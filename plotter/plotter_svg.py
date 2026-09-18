#!/usr/bin/env python3
"""Pen-plotter SVG exporter for simple symmetric Venn diagrams given as dual-map exports.

Input: {"n": n, "faces": [[4 labels], ...]} -- the dual (cubical sphere). The PRIMAL drawing
has one vertex per crossing (= per dual face) and one closed cycle of arcs per curve.

Layout: the label rotation (bit i -> i-1) is a graph automorphism whose orbits all have size n
(n prime), so the whole Tutte system collapses onto the orbit quotient. Writing positions as
complex numbers, the rotation is multiplication by lambda = exp(2*pi*i*s/n), which makes the
quotient system complex-linear in one unknown per orbit. The outer face (the n crossings around
label 0^n) is pinned to a regular n-gon. Solving that quotient gives an embedding that is
exactly n-fold symmetric by construction, not merely symmetric up to numerical noise.

Even spacing: any strictly positive per-vertex convex-combination weights keep the barycentric
embedding planar (Tutte/Floater), so we iterate weight = arc-length**p, a negative feedback that
equalises arc lengths. A monotone radial warp -- a homeomorphism of the plane, hence topology
preserving -- then redistributes the crossings toward equal areal density, with its local stretch
clamped so nothing is squashed into a sliver. Every stage is planar by construction and the
exported drawing is verified with an exact grid-bucketed segment sweep, plus a check that reads
all 2^n region labels back out of the drawn curves.

Output: one <path> per curve, closed, centripetal-Catmull-Rom smoothed, in millimetres.
"""
import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS',
           'VECLIB_MAXIMUM_THREADS', 'NUMEXPR_NUM_THREADS'):
    os.environ.setdefault(_v, '1')
import argparse, collections, json, math, resource, shutil, subprocess, sys, time
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'gks-scaffold'))
from interval_growth import oriented_faces  # noqa: E402


# ----------------------------------------------------------------------------- combinatorics
class Primal:
    """Crossing graph of the arrangement plus its rotational structure."""

    def __init__(self, path):
        d = json.load(open(path))
        self.n = n = int(d['n'])
        self.faces = faces = oriented_faces({frozenset(f) for f in d['faces']}, n)
        self.V = V = len(faces)
        assert V == (1 << n) - 2, (V, n)

        edge_faces = collections.defaultdict(list)
        for i, f in enumerate(faces):
            for a, b in zip(f, f[1:] + f[:1]):
                edge_faces[frozenset((a, b))].append(i)
        adj = [[] for _ in range(V)]
        curve_of = {}
        for e, fs in edge_faces.items():
            assert len(fs) == 2, 'dual edge not shared by exactly two squares'
            a, b = fs
            adj[a].append(b)
            adj[b].append(a)
            x, y = tuple(e)
            bit = next(i for i in range(n) if x[i] != y[i])
            curve_of[(a, b)] = curve_of[(b, a)] = bit
        assert all(len(a) == 4 for a in adj), 'crossing graph is not 4-regular'
        self.adj, self.curve_of = adj, curve_of

        # rotation bit i -> i-1 on labels, i.e. y[j] = x[(j+1) % n]
        face_id = {frozenset(f): i for i, f in enumerate(faces)}
        self.rho = rho = [face_id[frozenset(l[1:] + l[0] for l in faces[i])] for i in range(V)]
        assert len(set(rho)) == V

        # outer face of the primal = crossings around label 0^n, in cyclic order
        zero = '0' * n
        corners = collections.defaultdict(dict)
        for i, f in enumerate(faces):
            if zero in f:
                k = f.index(zero)
                corners[f[k - 1]][f[(k + 1) % 4]] = i
        outer, p = [], next(iter(corners))
        for _ in range(len(corners)):
            q, i = next(iter(corners[p].items()))
            outer.append(i)
            p = q
        assert len(set(outer)) == n, 'outer face is not an n-gon'
        self.outer = outer

        # orbits, with the outer-face representative first so that pinning is consistent
        orb = [-1] * V
        kof = [0] * V
        reps = []
        for seed in [outer[0]] + list(range(V)):
            if orb[seed] >= 0:
                continue
            r = len(reps)
            reps.append(seed)
            u, k = seed, 0
            while orb[u] < 0:
                orb[u], kof[u] = r, k
                u, k = rho[u], k + 1
            assert u == seed and k == n, 'orbit size is not n'
        self.orb, self.kof, self.reps = np.array(orb), np.array(kof), reps
        self.norb = len(reps)

        # rho shifts the outer cycle by a constant s; positions must rotate by lambda = w**s
        at = {v: t for t, v in enumerate(outer)}
        s = (at[rho[outer[0]]]) % n
        assert all((at[rho[v]] - at[v]) % n == s for v in outer)
        assert math.gcd(s, n) == 1
        self.shift = s
        self.lam = np.exp(2j * math.pi * s / n)

        # Level of a crossing = min weight of its four labels + 1. The four regions round a
        # crossing always have weights k, k+1, k+1, k+2, so the level runs 1 (the ring of
        # crossings touching the outside region 0^n) to n-1 (the ring round the centre 1^n),
        # and it coincides with the mean weight.
        self.level = np.array([min(l.count('1') for l in f) + 1 for f in faces])
        self.rank = np.array([sum(l.count('1') for l in f) / 4.0 for f in faces])
        assert np.allclose(self.level, self.rank), 'crossing weights are not k,k+1,k+1,k+2'

        # directed edge arrays, and an orbit id per undirected edge
        src = np.repeat(np.arange(V), 4)
        dst = np.array([w for v in range(V) for w in adj[v]])
        self.esrc, self.edst = src, dst
        key = {}
        n_eorb = 0
        eorb = np.empty(len(src), int)
        for idx, (a, b) in enumerate(zip(src, dst)):
            k = (a, b) if a < b else (b, a)
            if k not in key:
                x, y = k                       # walk the rotation orbit of this undirected edge
                for _ in range(n):
                    key[(x, y) if x < y else (y, x)] = n_eorb
                    x, y = rho[x], rho[y]
                n_eorb += 1
            eorb[idx] = key[k]
        self.eorb, self.n_eorb = eorb, n_eorb

        # regions: cyclic order of crossings around every label
        self.region_cycle = {}
        rc = collections.defaultdict(dict)
        for i, f in enumerate(faces):
            for k, x in enumerate(f):
                rc[x][f[k - 1]] = (f[(k + 1) % 4], i)
        for x, m in rc.items():
            cyc, p = [], next(iter(m))
            for _ in range(len(m)):
                q, i = m[p]
                cyc.append(i)
                p = q
            assert len(set(cyc)) == len(m), 'region boundary walk is not a simple cycle'
            self.region_cycle[x] = cyc

        # flat form of the region cycles, so areas and centroids are one reduceat, not 2^n loops
        self.reg_labels = labels = sorted(self.region_cycle)
        sizes = np.array([len(self.region_cycle[x]) for x in labels])
        self.reg_off = np.concatenate([[0], np.cumsum(sizes)[:-1]])
        self.reg_flat = np.fromiter((v for x in labels for v in self.region_cycle[x]),
                                    np.int64, int(sizes.sum()))
        nx = np.arange(len(self.reg_flat)) + 1
        nx[self.reg_off + sizes - 1] = self.reg_off
        self.reg_next = nx

        # quotient-system index arrays (one row per orbit, four entries per row)
        rep_edge = (4 * np.array(reps)[:, None] + np.arange(4)).ravel()
        self.qrow = np.repeat(np.arange(self.norb), 4)
        self.qedge = rep_edge
        self.qcol = self.orb[dst[rep_edge]]
        self.qlam = self.lam ** self.kof[dst[rep_edge]]

        # one closed cycle of crossings per curve
        # each crossing lies on exactly two curves, so the sorted four edge labels are (a,a,b,b)
        self.axes = np.sort(np.array([[curve_of[(v, w)] for w in adj[v]]
                                      for v in range(V)]), axis=1)[:, ::2]
        self.cycles = [self._curve_cycle(b) for b in range(n)]

    def _curve_cycle(self, bit):
        start = int(np.flatnonzero((self.axes == bit).any(1))[0])
        nxt = [w for w in self.adj[start] if self.curve_of[(start, w)] == bit]
        cyc = [start, nxt[0]]
        prev, cur = start, nxt[0]
        while True:
            w = [x for x in self.adj[cur] if self.curve_of[(cur, x)] == bit and x != prev][0]
            if w == start:
                break
            cyc.append(w)
            prev, cur = cur, w
        expect = 2 * self.V // self.n
        assert len(cyc) == expect and len(set(cyc)) == len(cyc), (
            f'curve {bit} is not a single cycle ({len(cyc)} vs {expect})')
        return cyc


# ----------------------------------------------------------------------------- layout
def solve_symmetric(P, w_edge, warm=None, tol=1e-13, maxit=20000):
    """Weighted barycentric (Tutte) solve on the rotation quotient.

    Never forms a matrix. The full system is the Dirichlet Laplacian (D - W) z = 0 with the
    outer orbit pinned; because the weights are symmetric and rotation-invariant, its quotient
    is Hermitian positive definite (the off-diagonal entry for an edge leaving orbit r carries
    lam**k, and the matching entry in the other row carries lam**-k = its conjugate). So it is
    solved with Jacobi-preconditioned conjugate gradient on four entries per orbit -- O(n_orb)
    memory and work per iteration instead of the O(n_orb**2) dense solve, which is 1 GB per
    factorisation at n=17. Warm-starting from the previous outer iterate keeps it a few dozen
    iterations once the weight sequence settles."""
    w = w_edge[P.qedge]
    D = np.bincount(P.qrow, w, minlength=P.norb)
    coef = -w * P.qlam
    free = P.qcol != 0                                  # orbit 0 is pinned at 1
    b = np.zeros(P.norb, complex)
    np.add.at(b, P.qrow[~free], -coef[~free])           # few entries: only rim neighbours
    b[0] = 0.0
    cf, cr, cc = coef[free], P.qrow[free], P.qcol[free]

    def A(x):
        y = D * x
        c = cf * x[cc]
        y += np.bincount(cr, c.real, minlength=P.norb) + \
            1j * np.bincount(cr, c.imag, minlength=P.norb)
        y[0] = 0.0
        return y
    x = np.zeros(P.norb, complex) if warm is None else warm.copy()
    x[0] = 0.0
    r = b - A(x)
    nb = float(np.linalg.norm(b)) or 1.0
    z = r / D
    p = z.copy()
    rz = float(np.vdot(r, z).real)
    for _ in range(maxit):
        if float(np.linalg.norm(r)) <= tol * nb:
            break
        Ap = A(p)
        alpha = rz / float(np.vdot(p, Ap).real)
        x += alpha * p
        r -= alpha * Ap
        z = r / D
        rz2 = float(np.vdot(r, z).real)
        p = z + (rz2 / rz) * p
        rz = rz2
    x[0] = 1.0
    return x[P.orb] * P.lam ** P.kof, x


def orbit_mean(P, vals):
    """Average a per-directed-edge quantity over each rotation orbit of edges (kills float noise)."""
    s = np.bincount(P.eorb, weights=vals, minlength=P.n_eorb)
    c = np.bincount(P.eorb, minlength=P.n_eorb)
    return (s / c)[P.eorb]


def region_areas(P, z):
    """Shoelace area of every region at once, aligned with P.reg_labels (one reduceat over the
    flattened region cycles rather than 2^n small numpy calls)."""
    a = z[P.reg_flat]
    b = z[P.reg_flat[P.reg_next]]
    return 0.5 * np.abs(np.add.reduceat(np.imag(np.conj(a) * b), P.reg_off))


def ideal_radius(P):
    """Equal-area rings: the disk of radius R(r) holds every crossing of rank >= r, so each
    ring's area is proportional to the number of crossings it contains."""
    ranks = np.array(sorted(set(P.rank)))
    cnt = np.array([(P.rank == r).sum() for r in ranks], float)
    N = np.cumsum(cnt[::-1])[::-1]
    R = np.sqrt(N / N[0])
    return np.interp(P.rank, ranks, R)


def level_radius(P, R=1.0):
    """Equal area per crossing: the disk holding every crossing of level >= l gets area
    proportional to how many crossings that is, so the annulus belonging to level l has area
    proportional to N_l. Level 1 lands on the rim R, level n-1 just off the centre."""
    ls = np.arange(int(P.level.min()), int(P.level.max()) + 1)
    N = np.array([(P.level == l).sum() for l in ls], float)
    C = np.cumsum(N[::-1])[::-1]
    return np.interp(P.level, ls, R * np.sqrt(C / C[0]))


def level_warp(P, z, aniso=8.0, blend=1.0, grid=800):
    """Carry each level to its equal-area radius with a monotone radial map.

    The Tutte layout already orders the levels radially and keeps each level radially narrow, so
    the correction the level targets ask for is almost purely radial: anchor the median radius of
    level l to its target r(l) and interpolate monotonically in log-log. Being a strictly
    increasing r -> g(r), this is a homeomorphism of the plane, so it moves everything without
    touching the topology -- no per-vertex planarity constraints needed. It is what unpacks the
    centre: at n=17 the innermost 171 regions hold 44% of the disk before the warp."""
    lev, r = P.level, np.abs(z)
    rmax = float(r.max())
    ls = np.arange(int(lev.min()), int(lev.max()) + 1)
    cur = np.array([np.median(r[lev == l]) for l in ls]) / rmax
    tgt = level_radius(P, 1.0)
    tg = np.array([np.median(tgt[lev == l]) for l in ls])
    u, G = np.log(cur)[::-1], np.log(tg)[::-1]          # increasing in u (outward)
    keep = np.concatenate([[True], np.diff(u) > 1e-9])
    u, G = u[keep], G[keep]
    G = (1 - blend) * u + blend * G
    lo = float(u[0]) - 0.6
    g = np.linspace(lo, 0.0, grid)
    slope = np.clip(np.gradient(np.interp(g, u, G, left=G[0] + (g[0] - u[0]), right=0.0), g),
                    1.0 / aniso, aniso)
    Gi = np.concatenate([[0.0], np.cumsum(0.5 * (slope[1:] + slope[:-1]) * np.diff(g))])
    Gi -= Gi[-1]

    def warp(w):
        rr = np.abs(w)
        uu = np.clip(np.log(np.maximum(rr, 1e-300) / rmax), g[0], 0.0)
        return w * np.exp(np.interp(uu, g, Gi)) * rmax / np.maximum(rr, 1e-300)
    return warp(z), warp


class LevelRelax:
    """Level-radial relaxation on the rotation quotient, with a hard planarity guard.

    Each orbit representative is pulled toward the barycentre of its neighbours blended with the
    point at its level's target radius on its own ray, and the whole orbit is moved together so
    the drawing stays exactly n-fold symmetric. The move is then clipped so that the crossing
    stays strictly on the interior side of every edge of every region it belongs to that it is
    not itself an endpoint of -- the kernel condition, which keeps each incident region a simple
    star-shaped polygon and so keeps the straight-line drawing planar. Constraints that the
    starting drawing already violates (a region can be simple without being star-shaped from one
    of its own corners) are recorded and left alone rather than enforced, and the final drawing
    is checked for real with the exact segment sweep."""

    def __init__(self, P, z):
        self.P = P
        n, V = P.n, P.V
        self.reps = reps = np.array(P.reps)
        self.nrep = len(reps)
        self.lamk = lamk = P.lam ** P.kof
        nb = np.array([P.adj[v] for v in reps])
        self.onb, self.lnb = P.orb[nb], lamk[nb]
        self.movable = P.level[reps] > 1              # the rim ring is the drawing's boundary
        self.tgt = level_radius(P, float(np.abs(z[P.outer[0]])))[reps]

        at = {x: {v: i for i, v in enumerate(c)} for x, c in P.region_cycle.items()}
        sgn = {}
        for x, c in P.region_cycle.items():
            p = z[c]
            sgn[x] = 1.0 if np.imag(np.sum(np.conj(p) * np.roll(p, -1))) > 0 else -1.0
        zero = '0' * n
        CV, EA, EB, SG, PV, NX = [], [], [], [], [], []
        for r, v in enumerate(reps):
            for x in P.faces[v]:
                if x == zero:                         # the outside region: its ring never moves
                    continue
                c, j = P.region_cycle[x], at[x][v]
                m = len(c)
                PV.append(c[(j - 1) % m])
                NX.append(c[(j + 1) % m])
                for i in range(m):
                    if i == j or i == (j - 1) % m:
                        continue
                    CV.append(r)
                    EA.append(c[i])
                    EB.append(c[(i + 1) % m])
                    SG.append(sgn[x])
        self.cv = np.array(CV, np.int64)
        self.oa, self.la = P.orb[np.array(EA, np.int64)], lamk[np.array(EA, np.int64)]
        self.ob, self.lb = P.orb[np.array(EB, np.int64)], lamk[np.array(EB, np.int64)]
        self.sg = np.array(SG)
        # area-gradient support: previous/next crossing of each (rep, incident region) pair
        pv, nx = np.array(PV, np.int64), np.array(NX, np.int64)
        self.opv, self.lpv = P.orb[pv], lamk[pv]
        self.onx, self.lnx = P.orb[nx], lamk[nx]
        self.face_rep = np.repeat(np.arange(self.nrep), 4)
        self.face_lab = [x for v in reps for x in P.faces[v]]
        self.face_sgn = np.array([0.0 if x == zero else sgn[x] for x in self.face_lab])
        lab_idx = {x: i for i, x in enumerate(P.reg_labels)}
        self.face_reg = np.array([lab_idx[x] for x in self.face_lab])
        self.active = self._ok(z[reps])

    def _ok(self, zr):
        pa = zr[self.oa] * self.la
        pb = zr[self.ob] * self.lb
        return np.imag(np.conj(pb - pa) * (zr[self.cv] - pa)) * self.sg > 0

    def step(self, zr, a, area_w=0.0, trials=30):
        P = self.P
        bary = (zr[self.onb] * self.lnb).mean(1)
        rad = self.tgt * zr / np.abs(zr)
        d = (1 - a) * bary + a * rad - zr
        if area_w:
            A = region_areas(P, zr[P.orb] * self.lamk)
            w = np.clip(np.log(np.median(A) / np.maximum(A, 1e-18)), -3, 3)[self.face_reg]
            g = -0.5j * (zr[self.onx] * self.lnx - zr[self.opv] * self.lpv) * self.face_sgn
            d = d + area_w * np.bincount(self.face_rep, (w * g).real, self.nrep) \
                + 1j * area_w * np.bincount(self.face_rep, (w * g).imag, self.nrep)
        d = np.where(self.movable, d, 0)
        s = np.ones(self.nrep)
        for _ in range(trials):
            cand = zr + s * d
            bad = self.active & ~self._ok(cand)
            if not bad.any():
                return cand, int(bad.sum())
            blame = np.unique(np.concatenate([self.cv[bad], self.oa[bad], self.ob[bad]]))
            blame = blame[self.movable[blame]]
            if len(blame) == 0:
                s *= 0.5
            else:
                s[blame] *= 0.5
        return zr, int(bad.sum())


def relax_levels(P, z, iters=300, a0=0.35, a1=0.05, area_w=0.0, every=50, log=None, note=None):
    """Iterate the level-radial step, easing the radial pull off as it settles."""
    R = LevelRelax(P, z)
    zr = z[R.reps].copy()
    hist = []
    for it in range(iters):
        a = a0 + (a1 - a0) * it / max(1, iters - 1)
        zr, bad = R.step(zr, a, area_w)
        if (it % every == 0 or it == iters - 1):
            s = layout_stats(P, zr[P.orb] * R.lamk)
            s.update(it=it, alpha=round(a, 4), blocked=bad)
            hist.append(s)
            if note:
                note('  it %3d a=%.3f feat %.4g  angle med %.1f  area %.3g/%.3g/%.3g  blocked %d'
                     % (it, a, s['feature'], s['angle_med'], s['area_min'], s['area_med'],
                        s['area_max'], bad))
    if log is not None:
        log.extend(hist)
    return zr[P.orb] * R.lamk


def layout_stats(P, z):
    """Cheap quality read-out on the straight-line drawing (unit coordinates)."""
    pts = np.stack([z.real, -z.imag], 1)
    segs = polyline_segments(P, pts)
    seglen = float(np.median(np.linalg.norm(segs[1] - segs[0], axis=1)))
    viol, feat, _, _ = sweep(segs, 0.5 * seglen, cell=1.5 * seglen)
    ang = crossing_angles(P, pts)
    a = np.sort(region_areas(P, z))[:-1]
    return dict(feature=float(feat), violations=int(viol), angle_min=float(ang.min()),
                angle_med=float(np.median(ang)), area_min=float(a.min()),
                area_med=float(np.median(a)), area_max=float(a.max()))


def polyline_segments(P, pts):
    """One straight segment per arc, tagged so the sweep can tell arcs that share a crossing."""
    a, b, ids = [], [], []
    for c in P.cycles:
        c = np.array(c)
        a.append(pts[c])
        b.append(pts[np.roll(c, -1)])
        ids.append(np.stack([c, np.roll(c, -1)], 1))
    A, B, I = np.concatenate(a), np.concatenate(b), np.concatenate(ids)
    return (A, B, I[:, 0], I[:, 1], I[:, 0], I[:, 1])


def crossing_angles(P, pts):
    """Angle between the two curves at every crossing, from the chord through it."""
    vid, tv = [], []
    for c in P.cycles:
        c = np.array(c)
        vid.append(c)
        tv.append(pts[np.roll(c, -1)] - pts[np.roll(c, 1)])
    vid, tv = np.concatenate(vid), np.concatenate(tv)
    o = np.argsort(vid, kind='stable')
    vid, tv = vid[o], tv[o]
    u = tv[::2] / np.maximum(np.linalg.norm(tv[::2], axis=1, keepdims=True), 1e-300)
    w = tv[1::2] / np.maximum(np.linalg.norm(tv[1::2], axis=1, keepdims=True), 1e-300)
    return np.degrees(np.arccos(np.clip(np.abs((u * w).sum(1)), 0, 1)))


def layout(P, iters=300, power=1.0, damp=0.5, log=None):
    """Iterated weighted symmetric Tutte. Weight ~ arc length is a negative feedback that
    equalises arc lengths, and any strictly positive weights leave the barycentric map planar
    (Tutte/Floater), so every iterate -- including the last -- is a valid embedding."""
    E = len(P.esrc)
    wl = np.ones(E)
    z, warm = solve_symmetric(P, wl)
    hist = []
    for it in range(iters):
        L = orbit_mean(P, np.abs(z[P.esrc] - z[P.edst]))
        wl = wl ** (1 - damp) * (L / L.mean()) ** (damp * power)
        wl = np.clip(wl / wl.mean(), 1e-12, 1e12)
        z, warm = solve_symmetric(P, wl, warm)
        if log is not None and (it % 25 == 0 or it == iters - 1):
            e = np.abs(z[P.esrc] - z[P.edst])
            a = np.sort(region_areas(P, z))[:-1]
            hist.append(dict(it=it, emin=float(e.min()), emed=float(np.median(e)),
                             amin=float(a.min()), amed=float(np.median(a)),
                             amax=float(a.max())))
    if log is not None:
        log.extend(hist)
    return z


def radial_warp(z, n, rim=0.78, aniso=2.2, grid=800):
    """Monotone radial remap: petal band outside, equal areal density of crossings inside.

    A strictly increasing r -> g(r) with g(0)=0 is a homeomorphism of the plane, so it cannot
    change the topology; the only risk is a long straight arc bulging across a neighbour, which
    the sweep afterwards checks. Two pieces: the n pinned outer crossings stay on the unit
    circle while the next ring in is carried to `rim`, which opens the petal band and turns the
    rim crossings from near-tangencies into clean X's; everything inside `rim` is redistributed
    toward equal area per crossing, with the local anisotropy r*g'(r)/g(r) clamped to
    [1/aniso, aniso] so no region is squashed into a sliver. Being purely radial the warp
    commutes with the rotation, so the drawing stays exactly n-fold symmetric."""
    r = np.abs(z)
    rmax = float(r.max())
    inner = np.sort(r)[:-n]                              # everything but the pinned outer ring
    r2 = float(inner[-1]) / rmax
    u = np.log(np.maximum(r, 1e-12) / rmax)
    u2, lo = math.log(r2), float(np.log(inner.min() / rmax)) - 0.30
    g = np.linspace(lo, u2, grid)
    h = np.histogram(np.log(inner / rmax), bins=grid, range=(lo, u2))[0].astype(float)
    sig = max(2.0, grid / 120.0)
    k = np.exp(-0.5 * (np.arange(-4 * int(sig), 4 * int(sig) + 1) / sig) ** 2)
    h = np.convolve(h, k / k.sum(), 'same')
    F = np.maximum(np.cumsum(h) / max(h.sum(), 1e-12), 1e-9)
    slope = np.clip(np.gradient(0.5 * np.log(F), g), 1.0 / aniso, aniso)
    G = np.concatenate([[0.0], np.cumsum(0.5 * (slope[1:] + slope[:-1]) * np.diff(g))])
    G += math.log(rim) - G[-1]                           # pin ring 2 at the rim radius
    g = np.concatenate([g, [0.0]])
    G = np.concatenate([G, [0.0]])                       # ... and the outer ring at radius 1

    def warp(w):
        rr = np.abs(w)
        uu = np.clip(np.log(np.maximum(rr, 1e-12) / rmax), g[0], 0.0)
        return w * np.exp(np.interp(uu, g, G)) * rmax / np.maximum(rr, 1e-12)
    return warp(z), warp


# ----------------------------------------------------------------------------- smoothing
def bezier_controls(pts, tension, cap=0.42):
    """Centripetal Catmull-Rom -> cubic Bezier control points for a closed polyline.

    pts: (m,2); tension: (m,) per-knot multiplier on the tangent. Returns (m,4,2) control nets.
    Control offsets are capped at `cap` times the chord, which kills the overshoot that a long
    span next to short ones would otherwise produce; capping only shortens the handles, so the
    tangent directions and hence the G1 smoothness and the crossing angles are untouched."""
    m = len(pts)
    P0 = pts
    P1 = np.roll(pts, -1, 0)
    Pm = np.roll(pts, 1, 0)
    P2 = np.roll(pts, -2, 0)
    d = lambda a, b: np.maximum(np.linalg.norm(b - a, axis=1), 1e-12) ** 0.5
    d0, d1, d2 = d(Pm, P0), d(P0, P1), d(P1, P2)     # knot spacings, alpha = 1/2
    # non-uniform Catmull-Rom tangents at the two knots of each span
    m0 = ((P0 - Pm) / d0[:, None] - (P1 - Pm) / (d0 + d1)[:, None] + (P1 - P0) / d1[:, None])
    m1 = ((P1 - P0) / d1[:, None] - (P2 - P0) / (d1 + d2)[:, None] + (P2 - P1) / d2[:, None])
    t0 = tension[:, None]
    t1 = np.roll(tension, -1)[:, None]
    h0 = t0 * m0 * d1[:, None] / 3.0
    h1 = t1 * m1 * d1[:, None] / 3.0
    chord = np.maximum(np.linalg.norm(P1 - P0, axis=1), 1e-12)[:, None]
    for h in (h0, h1):
        L = np.maximum(np.linalg.norm(h, axis=1), 1e-12)[:, None]
        np.multiply(h, np.minimum(1.0, cap * chord / L), out=h)
    # the second return is the tangent DIRECTION at each knot, deliberately free of the tension
    # factor: where a knot has been softened to zero the handles vanish but the curve still has a
    # well-defined incoming/outgoing chord pair, and the crossing angle must still be measurable
    return np.stack([P0, P0 + h0, P1 - h1, P1], 1), m0 / d1[:, None]


def sample_bezier(ctrl, k):
    t = np.linspace(0, 1, k + 1)[:-1][None, :, None]
    b0, b1, b2, b3 = ctrl[:, 0][:, None], ctrl[:, 1][:, None], ctrl[:, 2][:, None], ctrl[:, 3][:, None]
    return ((1 - t) ** 3 * b0 + 3 * (1 - t) ** 2 * t * b1 + 3 * (1 - t) * t ** 2 * b2 + t ** 3 * b3)


# ----------------------------------------------------------------------------- geometry checks
def _seg_pair_metrics(A0, A1, B0, B1):
    """Vectorised: (intersects?, distance) for segment pairs A and B."""
    def cr(o, a, b):
        return (a[:, 0] - o[:, 0]) * (b[:, 1] - o[:, 1]) - (a[:, 1] - o[:, 1]) * (b[:, 0] - o[:, 0])
    d1, d2 = cr(A0, A1, B0), cr(A0, A1, B1)
    d3, d4 = cr(B0, B1, A0), cr(B0, B1, A1)
    hit = ((d1 > 0) != (d2 > 0)) & ((d3 > 0) != (d4 > 0))

    def p2s(p, a, b):
        ab = b - a
        t = np.clip(((p - a) * ab).sum(1) / np.maximum((ab * ab).sum(1), 1e-30), 0, 1)
        return np.linalg.norm(p - (a + t[:, None] * ab), axis=1)
    dist = np.minimum.reduce([p2s(A0, B0, B1), p2s(A1, B0, B1), p2s(B0, A0, A1), p2s(B1, A0, A1)])
    return hit, np.where(hit, 0.0, dist)


def sweep(segs, delta, cell=None, maxpairs=1_000_000, note=None):
    """Grid-bucketed segment sweep: planarity violations, and the closest approach between two
    arcs that do not meet at a crossing.

    Each segment goes into every cell its bounding box, grown by delta/2, touches. Two segments
    closer than delta have overlapping grown boxes, so they land in a common cell -- the answer
    is exact for any separation below delta, and exact for intersections at any delta. A pair is
    evaluated in exactly one cell (the one holding the lower-left corner of the box overlap), so
    nothing is double counted and no pair list is ever materialised in full: candidates are
    streamed in blocks of at most `maxpairs`. Work and memory are O(segments), not O(segments^2).
    """
    P0, P1, i0, i1, a0, a1 = segs
    N = len(P0)
    if cell is None:
        cell = max(3.0 * float(np.median(np.linalg.norm(P1 - P0, axis=1))), delta)
    # Renumber the segments in grid order first. Every later gather (P0[ii], lo[jj], ...) then
    # reads neighbouring addresses instead of jumping over a 50 MB array, which is worth several
    # times the sort at n=17. Counts and distances do not depend on the numbering.
    mid = 0.5 * (P0 + P1)
    mc = np.floor((mid - mid.min(0)) / cell).astype(np.int64)
    sp = np.argsort(mc[:, 0] * np.int64(1 << 32) + mc[:, 1], kind='stable')
    P0, P1, i0, i1, a0, a1 = P0[sp], P1[sp], i0[sp], i1[sp], a0[sp], a1[sp]
    del mid, mc, sp
    lo = np.minimum(P0, P1) - 0.5 * delta
    hi = np.maximum(P0, P1) + 0.5 * delta
    org = lo.min(0)
    c0 = np.floor((lo - org) / cell).astype(np.int32)
    c1 = np.floor((hi - org) / cell).astype(np.int32)
    nx = (c1[:, 0] - c0[:, 0] + 1).astype(np.int64)
    ny = (c1[:, 1] - c0[:, 1] + 1).astype(np.int64)
    cnt = nx * ny
    tot = int(cnt.sum())
    seg = np.repeat(np.arange(N, dtype=np.int32), cnt)
    off = np.arange(tot, dtype=np.int64) - np.repeat(np.cumsum(cnt) - cnt, cnt)
    cx = c0[seg, 0] + (off % nx[seg]).astype(np.int32)
    cy = c0[seg, 1] + (off // nx[seg]).astype(np.int32)
    del off, nx, ny, cnt
    key = cx.astype(np.int64) * np.int64(1 << 32) + cy
    order = np.argsort(key, kind='stable')
    key, seg, cx, cy = key[order], seg[order], cx[order], cy[order]
    del order

    newg = np.empty(tot, bool)
    newg[0] = True
    np.not_equal(key[1:], key[:-1], out=newg[1:])
    del key
    gstart = np.flatnonzero(newg)
    gid = np.cumsum(newg) - 1
    del newg
    gsize = np.diff(np.append(gstart, tot))
    partners = (gsize[gid] - (np.arange(tot) - gstart[gid]) - 1).astype(np.int64)
    del gid, gstart, gsize

    best, bestpair, viol = np.inf, None, 0
    offenders = set()
    cum = np.cumsum(partners)
    if note:
        note(f'sweep: {N} segments, {tot} cell entries, {int(cum[-1])} candidate pairs, '
             f'cell {cell:.3f} mm')
    s = 0
    while s < tot:
        base = cum[s - 1] if s else 0
        e = int(np.searchsorted(cum, base + maxpairs, 'right'))
        e = max(e, s + 1)
        blk = partners[s:e]
        npair = int(blk.sum())
        if npair == 0:
            s = e
            continue
        ipos = np.repeat(np.arange(s, e, dtype=np.int64), blk)
        jpos = ipos + 1 + (np.arange(npair, dtype=np.int64) -
                           np.repeat(np.cumsum(blk) - blk, blk))
        ii, jj = seg[ipos], seg[jpos]
        # own the pair in the cell containing the lower-left corner of the box overlap
        ox = np.maximum(lo[ii, 0], lo[jj, 0])
        oy = np.maximum(lo[ii, 1], lo[jj, 1])
        own = ((np.floor((ox - org[0]) / cell).astype(np.int32) == cx[ipos]) &
               (np.floor((oy - org[1]) / cell).astype(np.int32) == cy[ipos]))
        ii, jj = ii[own], jj[own]
        del ipos, jpos, ox, oy, own
        if len(ii):
            share_pt = ((i0[ii] == i0[jj]) | (i0[ii] == i1[jj]) |
                        (i1[ii] == i0[jj]) | (i1[ii] == i1[jj]))
            share_an = ((a0[ii] == a0[jj]) | (a0[ii] == a1[jj]) |
                        (a1[ii] == a0[jj]) | (a1[ii] == a1[jj]))
            hit, dist = _seg_pair_metrics(P0[ii], P1[ii], P0[jj], P1[jj])
            bad = hit & ~share_pt
            viol += int(bad.sum())
            if bad.any():
                for arr in (a0, a1):
                    offenders.update(arr[ii[bad]].tolist())
                    offenders.update(arr[jj[bad]].tolist())
            m = ~share_an
            if m.any():
                d = np.where(m, dist, np.inf)
                k = int(np.argmin(d))
                if d[k] < best:
                    best = float(d[k])
                    bestpair = (int(ii[k]), int(jj[k]))
        s = e
    return viol, best, bestpair, offenders


# ----------------------------------------------------------------------------- colours
def oklch_to_hex(L, C, h_deg):
    h = math.radians(h_deg)
    a, b = C * math.cos(h), C * math.sin(h)
    l_ = L + 0.3963377774 * a + 0.2158037573 * b
    m_ = L - 0.1055613458 * a - 0.0638541728 * b
    s_ = L - 0.0894841775 * a - 1.2914855480 * b
    l, m, s = l_ ** 3, m_ ** 3, s_ ** 3
    rgb = (4.0767416621 * l - 3.3077115913 * m + 0.2309699292 * s,
           -1.2684380046 * l + 2.6097574011 * m - 0.3413193965 * s,
           -0.0041960863 * l - 0.7034186147 * m + 1.7076147010 * s)
    return rgb


def palette(n, L=0.58, Cmax=0.22, h0=25.0):
    out = []
    for i in range(n):
        h = h0 + 360.0 * i / n
        lo, hi = 0.0, Cmax
        for _ in range(28):                       # binary search the in-gamut chroma
            mid = 0.5 * (lo + hi)
            if all(-1e-6 <= c <= 1 + 1e-6 for c in oklch_to_hex(L, mid, h)):
                lo = mid
            else:
                hi = mid
        rgb = oklch_to_hex(L, lo, h)
        g = lambda c: 12.92 * c if c <= 0.0031308 else 1.055 * max(c, 0) ** (1 / 2.4) - 0.055
        out.append('#%02x%02x%02x' % tuple(int(round(255 * min(1, max(0, g(c))))) for c in rgb))
    return out


# ----------------------------------------------------------------------------- main
def fmt(x):
    return f'{x:.3f}'.rstrip('0').rstrip('.')


def write_svg(path, paths, colors, page, stroke=0.35):
    head = (f'<?xml version="1.0" encoding="UTF-8"?>\n'
            f'<svg xmlns="http://www.w3.org/2000/svg" version="1.1" '
            f'width="{fmt(page)}mm" height="{fmt(page)}mm" '
            f'viewBox="0 0 {fmt(page)} {fmt(page)}">\n')
    body = ''.join(f'<path id="curve-{i}" fill="none" stroke="{c}" stroke-width="{stroke}" '
                   f'stroke-linecap="round" stroke-linejoin="round" d="{d}"/>\n'
                   for i, (d, c) in enumerate(zip(paths, colors)))
    Path(path).write_text(head + body + '</svg>\n')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('input')
    ap.add_argument('-o', '--outdir', default=str(HERE))
    ap.add_argument('--name', default=None)
    ap.add_argument('--diameter', type=float, default=None, help='mm; default 400 (n<=11) / 500')
    ap.add_argument('--margin', type=float, default=6.0)
    ap.add_argument('--stroke', type=float, default=0.35)
    ap.add_argument('--mode', default='tutte', choices=['tutte', 'level'],
                    help='tutte: arc-length relaxation + radial warp. '
                         'level: same start, then level-radial relaxation with a kernel guard')
    ap.add_argument('--iters', type=int, default=300)
    ap.add_argument('--level-iters', type=int, default=300)
    ap.add_argument('--alpha0', type=float, default=0.35)
    ap.add_argument('--alpha1', type=float, default=0.05)
    ap.add_argument('--area-weight', type=float, default=0.0,
                    help='extra pull toward equal region areas during the level relaxation')
    ap.add_argument('--power', type=float, default=1.0)
    ap.add_argument('--damp', type=float, default=0.5)
    ap.add_argument('--anisotropy', type=float, default=1.8,
                    help='bound on the radial warp stretch')
    ap.add_argument('--rim', type=float, default=0.95,
                    help='radius (fraction) the second ring is carried to; 0 disables the warp')
    ap.add_argument('--tension', type=float, default=0.9)
    ap.add_argument('--rim-knots', type=int, default=5,
                    help='extra non-crossing knots per rim arc; 0 omits them')
    ap.add_argument('--bulge', type=float, default=1.04,
                    help='radius of those knots relative to the rim circle')
    ap.add_argument('--cap', type=float, default=0.42,
                    help='max Bezier handle length as a fraction of the arc chord')
    ap.add_argument('--samples', type=int, default=12, help='samples per arc for verification')
    ap.add_argument('--no-png', action='store_true')
    ap.add_argument('--progress', action='store_true', help='stage timings and RSS on stderr')
    ap.add_argument('--png-px', type=int, default=4000, help='preview raster size')
    ap.add_argument('--png-timeout', type=float, default=180.0,
                    help='seconds to give qlmanage before rasterising the preview directly')
    ap.add_argument('--verify-labels', default='auto', choices=['auto', 'yes', 'no'])
    ap.add_argument('--verify-sample', type=int, default=0,
                    help='check only this many randomly chosen regions (0 = all of them)')
    ap.add_argument('--maxpairs', type=int, default=1_000_000,
                    help='candidate segment pairs held in memory at once during the sweep')
    args = ap.parse_args()

    t_all = time.time()

    def note(msg):
        if args.progress:
            print(f'[{time.time() - t_all:7.1f}s {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024 ** 3:5.2f}GB] {msg}',
                  file=sys.stderr, flush=True)
    P = Primal(args.input)
    note(f'built crossing graph: {P.V} crossings, {P.norb} orbits')
    n = P.n
    diameter = args.diameter if args.diameter else (500.0 if n >= 13 else 400.0)
    name = args.name or f'venn-{n}'
    outdir = Path(args.outdir).resolve()
    outdir.mkdir(parents=True, exist_ok=True)

    t0 = time.time()
    hist = []
    z = layout(P, iters=args.iters, power=args.power, damp=args.damp, log=hist)
    if args.mode == 'level':
        note('tutte start done; level-radial relaxation')
        z = relax_levels(P, z, iters=args.level_iters, a0=args.alpha0, a1=args.alpha1,
                         area_w=args.area_weight, log=hist, note=note)
    elif args.rim > 0:
        z, _ = radial_warp(z, n, rim=args.rim, aniso=args.anisotropy)
    t_layout = time.time() - t0
    lay = layout_stats(P, z)
    note(f'straight-line drawing: {lay["violations"]} violations, feature {lay["feature"]:.4g}')
    assert lay['violations'] == 0, 'relaxation broke planarity of the straight-line drawing'
    note(f'layout done in {t_layout:.1f}s')

    # Knots of each drawn curve: its crossings in cycle order, plus -- on the one arc each curve
    # contributes to the rim -- a few extra points on a circular arc just outside the pinned
    # polygon. They are not crossings; they only bow the rim arc outward. Without them Tutte
    # leaves the two curves at a rim crossing nearly tangent (~2 degrees), because the straight
    # arc to the next rim crossing dominates both tangents; bowed out they meet at ~60 degrees
    # and the drawing gains its petals. The insertion is rotation-equivariant, so the exact
    # n-fold symmetry is untouched.
    outer_edges = {frozenset((P.outer[t], P.outer[(t + 1) % n])) for t in range(n)}
    K = args.rim_knots
    fr = [(j + 1) / (K + 1) for j in range(K)]
    knots, kvid = [], []
    for b in range(n):
        cyc = P.cycles[b]
        pk, vk = [], []
        for k, v in enumerate(cyc):
            pk.append(z[v])
            vk.append(v)
            w = cyc[(k + 1) % len(cyc)]
            if K and frozenset((v, w)) in outer_edges:
                a0, da = np.angle(z[v]), 2 * math.pi / n
                if abs((np.angle(z[w]) - a0 - da + math.pi) % (2 * math.pi) - math.pi) > 1e-9:
                    da = -da                                  # the rim arc runs the other way
                for f in fr:
                    pk.append(args.bulge * abs(z[v]) * np.exp(1j * (a0 + f * da)))
                    vk.append(-1)
        knots.append(np.stack([np.real(pk), -np.imag(pk)], 1))
        kvid.append(np.array(vk))

    # scale to millimetres so that the drawing -- splines included, not just the crossings --
    # spans exactly `diameter`; the spline construction is similarity-equivariant, so measuring
    # the unit-space paths once and then scaling the control nets is exact.
    page = diameter + 2 * args.margin
    probe = np.concatenate([sample_bezier(bezier_controls(
        knots[b], np.full(len(knots[b]), args.tension), args.cap)[0], 8).reshape(-1, 2)
        for b in range(n)])
    scale = diameter / (2.0 * float(np.linalg.norm(probe, axis=1).max()))
    knots = [k * scale + page / 2 for k in knots]
    pts = np.stack([z.real, -z.imag], 1) * scale + page / 2

    # --- spline, with per-crossing-orbit tension so the drawing stays exactly symmetric
    tens = np.full(P.V, args.tension)
    for attempt in range(8):
        ctrl, tang = [], []
        for b in range(n):
            t = np.where(kvid[b] >= 0, tens[np.maximum(kvid[b], 0)], args.tension)
            c, m0 = bezier_controls(knots[b], t, args.cap)
            ctrl.append(c)
            tang.append(m0)
        # sampled polylines for verification
        allp, alli, alla, starts = [], [], [], [0]
        for b in range(n):
            vid = kvid[b]
            m = len(vid)
            sp = args.samples
            flat = sample_bezier(ctrl[b], sp).reshape(-1, 2)
            pid = -(np.arange(m * sp, dtype=np.int64) + 1) - b * 10_000_000
            pid[::sp] = np.where(vid >= 0, vid, pid[::sp])
            # each span is anchored to the two crossings bounding the arc it belongs to
            ar = np.arange(m)
            a0 = vid[np.maximum.accumulate(np.where(vid >= 0, ar, -1))]
            nxt = np.minimum.accumulate(np.where(vid >= 0, ar, m)[::-1])[::-1]
            nxt = np.append(nxt[1:], m)
            a1 = vid[np.where(nxt < m, nxt, int(np.flatnonzero(vid >= 0)[0]))]
            allp.append(flat)
            alli.append(pid)
            alla.append(np.repeat(np.stack([a0, a1], 1), sp, 0))
            starts.append(starts[-1] + len(flat))
        Pt, Id, An = np.concatenate(allp), np.concatenate(alli), np.concatenate(alla)
        del allp, alli, alla
        nx = np.arange(len(Pt), dtype=np.int64) + 1
        for k in range(n):
            nx[starts[k + 1] - 1] = starts[k]
        segs = (Pt, Pt[nx], Id, Id[nx], An[:, 0], An[:, 1])
        note(f'sampled {len(Pt)} segments')
        seglen = float(np.median(np.linalg.norm(segs[1] - segs[0], axis=1)))

        def check(delta):
            """Exact for intersections at any delta, and exact for the closest approach as soon
            as the answer comes out below delta."""
            # cell = seglen + delta minimises (entries per segment) x (segments per cell), so
            # it minimises the candidate pair count; start the radius just above the sampling
            # step and widen only if the closest approach comes back at or above it. Violation
            # counts are exact at every radius, so the retry loop only ever pays the cheap pass.
            return sweep(segs, delta, cell=seglen + delta,
                         maxpairs=args.maxpairs, note=note)
        delta = 0.5 * seglen
        viol, feat, _, offenders = check(delta)
        note(f'sweep delta={delta:.3f}: {viol} violations, closest {feat:.4f} mm')
        if viol == 0:
            while feat >= delta and delta < diameter / 8:      # widen until the answer is exact
                delta *= 2.0
                viol, feat, _, offenders = check(delta)
            break
        # Local fallback: halve the tension at the crossings bounding the offending arcs, by
        # rotation orbit so the drawing stays symmetric; the last pass drops those arcs to
        # straight polylines, which is the pre-smoothing drawing and is planar by construction.
        hot = np.isin(P.orb, P.orb[sorted(o for o in offenders if o >= 0)])
        tens[hot] = 0.0 if attempt >= 2 else tens[hot] * 0.35
        print(f'  smoothing crossed {viol} times; softening {int(hot.sum())} crossings',
              file=sys.stderr)

    # --- metrics
    arc_len = np.zeros(0)
    total_len = {}
    for b in range(n):
        s = sample_bezier(ctrl[b], 64)
        s = np.concatenate([s, ctrl[b][:, 3][:, None]], 1)
        d = np.linalg.norm(np.diff(s, axis=1), axis=2).sum(1)
        arc_len = np.concatenate([arc_len, d])
        total_len[b] = float(d.sum())
    areas = np.sort(region_areas(P, z) * scale ** 2)[:-1]       # drop the unbounded outer region

    # crossing angles between the two curves through each vertex: every crossing appears in
    # exactly two curve knot lists, so sorting by vertex id puts the two tangents side by side
    vids = np.concatenate([kvid[b][kvid[b] >= 0] for b in range(n)])
    tvec = np.concatenate([tang[b][kvid[b] >= 0] for b in range(n)])
    o = np.argsort(vids, kind='stable')
    vids, tvec = vids[o], tvec[o]
    assert len(vids) == 2 * P.V and (vids[::2] == vids[1::2]).all()
    u = tvec[::2] / np.linalg.norm(tvec[::2], axis=1, keepdims=True)
    w = tvec[1::2] / np.linalg.norm(tvec[1::2], axis=1, keepdims=True)
    ang = np.degrees(np.arccos(np.clip(np.abs((u * w).sum(1)), 0, 1)))

    # --- SVG output
    def pathd(b):
        c = ctrl[b]
        out = [f'M{fmt(c[0,0,0])},{fmt(c[0,0,1])}']
        for k in range(len(c)):
            out.append(f'C{fmt(c[k,1,0])},{fmt(c[k,1,1])} {fmt(c[k,2,0])},{fmt(c[k,2,1])} '
                       f'{fmt(c[k,3,0])},{fmt(c[k,3,1])}')
        out.append('Z')
        return ' '.join(out)
    note('measuring lengths and angles done; writing paths')
    paths = [pathd(b) for b in range(n)]
    cols = palette(n)
    svg_c = outdir / f'{name}-color.svg'
    svg_k = outdir / f'{name}-black.svg'
    write_svg(svg_c, paths, cols, page, args.stroke)
    write_svg(svg_k, paths, ['#000000'] * n, page, args.stroke)

    # --- topology: re-derive the region labels from the exported geometry
    labels_ok = None
    note('svg written; verifying region labels')
    if args.verify_labels != 'no':
        labels_ok = verify_labels(P, pts, ctrl, args.samples, sample=args.verify_sample)

    res = dict(
        n=n, crossings=P.V, orbits=P.norb, rotation_shift=P.shift,
        diameter_mm=diameter, page_mm=page, layout_seconds=round(t_layout, 2),
        total_seconds=round(time.time() - t_all, 2),
        peak_rss_gb=round(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024 ** 3, 3),
        planarity_violations=viol, smallest_feature_mm=feat,
        length_m={b: total_len[b] / 1000.0 for b in range(n)},
        total_length_m=sum(total_len.values()) / 1000.0,
        arc_mm=dict(min=float(arc_len.min()), median=float(np.median(arc_len)),
                    max=float(arc_len.max())),
        region_mm2=dict(min=float(areas.min()), median=float(np.median(areas)),
                        max=float(areas.max())),
        crossing_angle_deg=dict(min=float(ang.min()), median=float(np.median(ang))),
        tension=float(tens.max()), labels_verified=labels_ok,
        svg_color=str(svg_c), svg_black=str(svg_k), history=hist)
    (outdir / f'{name}-metrics.json').write_text(json.dumps(res, indent=1) + '\n')

    pngs = []
    if not args.no_png:
        rsvg = shutil.which('rsvg-convert') or '/opt/homebrew/bin/rsvg-convert'
        for s, cs in ((svg_c, cols), (svg_k, ['#000000'] * n)):
            p = outdir / (s.name + '.png')
            if Path(rsvg).exists():
                subprocess.run([rsvg, '-w', str(args.png_px), '-h', str(args.png_px),
                                '-b', 'white', '-o', str(p), str(s)], capture_output=True,
                               timeout=args.png_timeout)
            else:                       # QuickLook gives up on multi-megabyte path data
                try:
                    subprocess.run(['qlmanage', '-t', '-s', str(args.png_px), '-o', str(outdir),
                                    str(s)], capture_output=True, timeout=args.png_timeout)
                except subprocess.TimeoutExpired:
                    note(f'qlmanage timed out on {s.name}')
            if not p.exists():
                raster_png(p, ctrl, cs, page, args.png_px, args.samples)
            if p.exists():
                pngs.append(p)
    res['png'] = [str(p) for p in pngs]
    print(json.dumps({k: v for k, v in res.items() if k != 'history'}, indent=1))
    for p in [svg_c, svg_k] + pngs:
        print(p)
    return res


def raster_png(path, ctrl, colors, page, px, samples):
    """Fallback preview: draw the sampled curves straight into a bitmap, one polyline per curve,
    at 2x and downsampled. QuickLook gives up on multi-megabyte path data; this does not."""
    try:
        from PIL import Image, ImageDraw
    except ImportError:
        return
    ss = 2
    im = Image.new('RGB', (px * ss, px * ss), 'white')
    d = ImageDraw.Draw(im)
    k = px * ss / page
    for c, col in zip(ctrl, colors):
        s = sample_bezier(c, max(3, samples // 2)).reshape(-1, 2) * k
        pts = [(float(x), float(y)) for x, y in s]
        d.line(pts + pts[:1], fill=col, width=ss)
    im.resize((px, px), Image.LANCZOS).save(path)


def points_inside(polys, q, budget=4_000_000):
    """Even-odd inside test of every query point against every sampled closed curve, by a
    horizontal band sweep: a query point can only be crossed by segments whose y-range meets its
    own, so each band compares its own points against its own segments. Cost is
    O(points * segments / bands) rather than O(points * segments)."""
    got = np.zeros((len(q), len(polys)), np.uint8)
    if len(q) == 0:
        return got
    ylo = min(float(p[:, 1].min()) for p in polys)
    yhi = max(float(p[:, 1].max()) for p in polys)
    nb = int(min(max(len(q) // 32, 16), 1 << 15))
    h = max((yhi - ylo) / nb, 1e-12)
    qb = np.clip(((q[:, 1] - ylo) / h).astype(np.int64), 0, nb - 1)
    qorder = np.argsort(qb, kind='stable')
    qstart = np.searchsorted(qb[qorder], np.arange(nb + 1), 'left')
    for b, p in enumerate(polys):
        a, c = p, np.roll(p, -1, 0)
        dy = np.where(c[:, 1] == a[:, 1], 1e-30, c[:, 1] - a[:, 1])
        b0 = np.clip(((np.minimum(a[:, 1], c[:, 1]) - ylo) / h).astype(np.int64), 0, nb - 1)
        b1 = np.clip(((np.maximum(a[:, 1], c[:, 1]) - ylo) / h).astype(np.int64), 0, nb - 1)
        span = b1 - b0 + 1
        sidx = np.repeat(np.arange(len(p), dtype=np.int64), span)
        band = b0[sidx] + (np.arange(int(span.sum()), dtype=np.int64) -
                           np.repeat(np.cumsum(span) - span, span))
        so = np.argsort(band, kind='stable')
        sidx, band = sidx[so], band[so]
        sstart = np.searchsorted(band, np.arange(nb + 1), 'left')
        inside = np.zeros(len(q), bool)
        for k in range(nb):
            qs, qe = qstart[k], qstart[k + 1]
            ss, se = sstart[k], sstart[k + 1]
            if qe == qs or se == ss:
                continue
            sel = sidx[ss:se]
            step = max(1, budget // max(1, len(sel)))
            for t in range(qs, qe, step):
                qi = qorder[t:min(t + step, qe)]
                Q = q[qi]
                A1, C1 = a[sel], c[sel]
                cond = (A1[None, :, 1] > Q[:, None, 1]) != (C1[None, :, 1] > Q[:, None, 1])
                xin = (C1[None, :, 0] - A1[None, :, 0]) * (Q[:, None, 1] - A1[None, :, 1]) / \
                    dy[sel][None, :] + A1[None, :, 0]
                inside[qi] ^= ((cond & (Q[:, None, 0] < xin)).sum(1) % 2).astype(bool)
        got[:, b] = inside
    return got


def region_centroids(P, pts):
    """Area centroid of every region polygon at once."""
    a = pts[P.reg_flat]
    b = pts[P.reg_flat[P.reg_next]]
    cr = a[:, 0] * b[:, 1] - b[:, 0] * a[:, 1]
    A = 0.5 * np.add.reduceat(cr, P.reg_off)
    cx = np.add.reduceat((a[:, 0] + b[:, 0]) * cr, P.reg_off)
    cy = np.add.reduceat((a[:, 1] + b[:, 1]) * cr, P.reg_off)
    d = np.where(np.abs(A) < 1e-12, np.nan, 6.0 * A)
    return np.stack([cx / d, cy / d], 1)


def interior_point(poly):
    """A point strictly inside a simple polygon: the centroid if it is inside, otherwise the
    midpoint of the first interior span of a horizontal line through the polygon."""
    a, b = poly, np.roll(poly, -1, 0)
    cr = a[:, 0] * b[:, 1] - b[:, 0] * a[:, 1]
    A = cr.sum() / 2.0
    if abs(A) > 1e-12:
        c = ((a + b) * cr[:, None]).sum(0) / (6.0 * A)
        hit = (a[:, 1] > c[1]) != (b[:, 1] > c[1])
        if hit.any():
            xs = (a[hit, 0] + (b[hit, 0] - a[hit, 0]) *
                  (c[1] - a[hit, 1]) / (b[hit, 1] - a[hit, 1]))
            if np.sum(xs < c[0]) % 2 == 1:
                return c
    ys = np.unique(poly[:, 1])
    y = float(np.median(poly[:, 1])) if len(ys) < 2 else float(0.5 * (ys[len(ys) // 2 - 1] +
                                                                     ys[len(ys) // 2]))
    hit = (a[:, 1] > y) != (b[:, 1] > y)
    xs = np.sort(a[hit, 0] + (b[hit, 0] - a[hit, 0]) * (y - a[hit, 1]) / (b[hit, 1] - a[hit, 1]))
    return np.array([0.5 * (xs[0] + xs[1]), y]) if len(xs) >= 2 else poly.mean(0)


def verify_labels(P, pts, ctrl, samples, sample=0, seed=0):
    """Check that the regions of the INPUT really are the regions of the exported drawing: take
    one interior point per region and read off, from the drawn closed curves alone, which of them
    contain it. That n-bit vector must be exactly the region's label. With `sample` > 0 only that
    many randomly chosen regions are checked (the outer one always included)."""
    n = P.n
    polys = [sample_bezier(c, max(4, samples)).reshape(-1, 2) for c in ctrl]
    labels = P.reg_labels
    zero = labels.index('0' * n)
    idx = np.arange(len(labels))
    if sample and sample < len(labels):
        rng = np.random.default_rng(seed)
        idx = np.unique(np.append(rng.choice(len(labels), sample, replace=False), zero))
    q = region_centroids(P, pts)[idx]
    far = float(np.abs(pts).max()) * 4.0
    q[np.isnan(q).any(1)] = far
    q[idx == zero] = far
    want = np.array([[int(c) for c in labels[i]] for i in idx], np.uint8)
    got = points_inside(polys, q)
    bad = np.flatnonzero((got != want).any(1))
    if len(bad):                       # centroid fell outside a non-convex region: retry properly
        q2 = np.array([interior_point(pts[P.region_cycle[labels[idx[i]]]]) for i in bad])
        got2 = points_inside(polys, q2)
        keep = (got2 != want[bad]).any(1)
        bad = bad[keep]
    ok = len(idx) - len(bad)
    return dict(regions=len(labels), checked=int(len(idx)), matched=int(ok),
                all_ok=bool(len(bad) == 0),
                mismatched_labels=[labels[idx[i]] for i in bad[:8]])


if __name__ == '__main__':
    main()

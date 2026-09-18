"""Combinatorial rebuild of the GKS symmetric Venn dual R(P(S_n)) and its KRSW first-child quadrangulation.
Sources: Griggs-Killian-Savage EJC 11 (2004) R2; Killian-Ruskey-Savage-Weston EJC 11 (2004) R86, Sections 2-3, 5.
Output: the plane dual graph as a list of faces (cyclic lists of region labels); each face is one vertex of the Venn diagram.
Independent verification: all 2^n labels, every edge a cube edge in exactly two faces, Euler 2, single rotation cycle at
every vertex, every curve's two sides connected (curve = bond = one Jordan curve), face bit words w.w (transversal crossings),
face set invariant under rotation. Not a 17-curve simple result: faces of size > 4 are non-simple vertices."""
import json, sys, math, collections
from hashlib import sha256
from pathlib import Path
from gks_chains import match, nodes, parent, chain

def build(n, quadrangulate=True):
    N = nodes(n); chains = {x: chain(x) for x in N}
    root = '1' + '0' * (n - 1)
    children = collections.defaultdict(list)
    for x in N:
        if x != root: children[parent(x)].append(x)
    for p in children: children[p].sort(key=lambda c: (len(chains[c]), c))   # shortest chain first (GKS Lemma 1)
    order = []
    def pre(x):
        order.append(x)
        for c in children[x]: pre(c)
    pre(root)
    col = {x: k + 1 for k, x in enumerate(order)}
    pos = {}   # rectangular coordinates within one copy: (column, weight)
    for x in N:
        for y in chains[x]: pos[y] = (col[x], y.count('1'))
    edges = set()
    def add(u, v):
        assert u != v and sum(a != b for a, b in zip(u, v)) == 1, (u, v)
        edges.add(frozenset((u, v)))
    for x in N:
        c = chains[x]
        for u, v in zip(c, c[1:]): add(u, v)
        if x != root:
            add(c[0], chains[parent(x)][0]); add(c[-1], chains[parent(x)][-1])
    added = 0
    if quadrangulate:
        for x in N:
            if not children[x]: continue
            w = children[x][0]
            b = w.rindex('1')
            # a = position of the 0 matched to the last 1 of w
            stack = []; a = None
            for i, ch in enumerate(w):
                if ch == '0': stack.append(i)
                else:
                    if stack:
                        j = stack.pop()
                        if i == b: a = j
            assert a is not None and a < b
            U = match(w)[0]; m = len(U)
            i0 = sum(1 for u in U if u < a)
            def I(bits, base):
                s = list(base)
                for t in bits: s[t] = '1'
                return ''.join(s)
            Cw = {j: I(U[:j], w) for j in range(0, m)}
            Cx = {}
            for j in range(0, m + 2):
                if j <= i0: Cx[j] = I(U[:j], x)
                elif j == i0 + 1: Cx[j] = I(U[:j - 1] + [a], x)
                else: Cx[j] = I(U[:j - 2] + [a, b], x)
            cw, cx = set(chains[w]), set(chains[x])
            for j in range(1, i0 + 1):
                if j in Cw and Cw[j] in cw and Cx[j] in cx: add(Cx[j], Cw[j]); added += 1
            for j in range(i0, m):
                if Cw[j] in cw and Cx[j + 2] in cx: add(Cx[j + 2], Cw[j]); added += 1
    return N, chains, pos, edges, col, added

def rotate(x, k):
    return x[k:] + x[:k]

def faces_of(n, pos, edges):
    """n rotated copies in pie slices plus 0^n (infinity) and 1^n (centre); faces via rotation system."""
    zero, one = '0' * n, '1' * n
    root_first = '1' + '0' * (n - 1); root_last = '1' * (n - 1) + '0'
    adj = collections.defaultdict(list)      # vertex -> list of (neighbour, direction angle)
    for k in range(n):
        base = 2 * math.pi * k / n
        def P(x):
            c, r = pos[x]; return (base + c * 1e-3, r)     # slice-local rectangular coords (angle-like, height)
        for e in edges:
            u, v = tuple(e); ru, rv = rotate(u, k), rotate(v, k)
            (xu, yu), (xv, yv) = P(u), P(v)
            adj[ru].append((rv, math.atan2(yv - yu, xv - xu)))
            adj[rv].append((ru, math.atan2(yu - yv, xu - xv)))
        s, t = rotate(root_first, k), rotate(root_last, k)
        adj[s].append((zero, -math.pi / 2)); adj[t].append((one, math.pi / 2))
        adj[zero].append((s, -base)); adj[one].append((t, base))   # reversed order at infinity
    rot = {}
    for v, lst in adj.items():
        lst.sort(key=lambda p: p[1]); nb = [p[0] for p in lst]
        assert len(set(nb)) == len(nb)
        rot[v] = {nb[i]: nb[(i + 1) % len(nb)] for i in range(len(nb))}
    seen = set(); faces = []
    for u in adj:
        for v in list(rot[u]):
            if (u, v) in seen: continue
            face = []; a, b = u, v
            while (a, b) not in seen:
                seen.add((a, b)); face.append(a)
                c = rot[b][a]; a, b = b, c
            faces.append(face)
    return faces

def check(n, faces):
    labels = set(); edges = collections.Counter(); bad = 0; sizes = collections.Counter(); pattern_bad = 0
    corners = collections.defaultdict(dict); repeated = 0
    for f in faces:
        k = len(f); sizes[k] += 1; bits = []
        if len(set(f)) != k: repeated += 1
        for i in range(k):
            a, b = f[i], f[(i + 1) % k]
            d = [t for t in range(n) if a[t] != b[t]]
            if len(d) != 1: bad += 1
            bits.append(d[0] if len(d) == 1 else -1)
            edges[frozenset((a, b))] += 1; labels.add(a); corners[a][f[i - 1]] = b
        h = k // 2
        if k % 2 or bits[:h] != bits[h:] or len(set(bits[:h])) != h: pattern_bad += 1
    single = sum(1 for v, m in corners.items() if _single_cycle(m))
    adj = collections.defaultdict(set)
    for e in edges:
        a, b = tuple(e); adj[a].add(b); adj[b].add(a)
    def connected(S):
        S = set(S); s = next(iter(S)); seen = {s}; st = [s]
        while st:
            x = st.pop()
            for y in adj[x]:
                if y in S and y not in seen: seen.add(y); st.append(y)
        return len(seen) == len(S)
    curves = all(connected({l for l in labels if l[i] == '1'}) and connected({l for l in labels if l[i] == '0'}) for i in range(n))
    fset = {frozenset(zip(f, f[1:] + f[:1])) for f in faces}
    sym = all(frozenset((rotate(a, 1), rotate(b, 1)) for a, b in fe) in fset for fe in fset)
    V, E, F = len(labels), len(edges), len(faces)
    return dict(V=V, E=E, F=F, euler=V - E + F, all_labels=(V == 2 ** n), edge_multiplicities=dict(collections.Counter(edges.values())),
                bad_edges=bad, face_sizes=dict(sorted(sizes.items())), non_transversal_faces=pattern_bad,
                vertices_single_rotation_cycle=(single == V), curves_two_sides_connected=curves, rotation_symmetric=sym,
                repeated_vertex_faces=repeated,
                venn_dual_valid=(V == 2 ** n and V - E + F == 2 and set(edges.values()) == {2} and bad == 0 and repeated == 0 and single == V and curves and sym),
                all_crossings_transversal=(pattern_bad == 0))

def _single_cycle(m):
    start = next(iter(m)); x = start; c = 0
    while True:
        x = m.get(x); c += 1
        if x is None or x == start or c > len(m) + 1: break
    return x == start and c == len(m) and len(set(m.values())) == len(m)

if __name__ == '__main__':
    here = Path(__file__).resolve().parent; report = {}
    for n in [int(a) for a in sys.argv[1:]] or [5, 7, 11, 13]:
        for quad in (False, True):
            N, chains, pos, edges, col, added = build(n, quad)
            faces = faces_of(n, pos, edges)
            r = check(n, faces)
            name = f'gks{n}-{"quadrangulated" if quad else "plain"}'
            report[name] = dict(chains=len(N), added_edges_per_copy=added, **r)
            print(name, json.dumps(report[name]), flush=True)
            out = here / (name + '-faces.json')
            out.write_text(json.dumps(dict(n=n, kind=name, faces=faces, verification=r, full17=False), separators=(',', ':')) + '\n')
    (here / 'gks-scaffold-report.json').write_text(json.dumps(report, indent=1) + '\n')

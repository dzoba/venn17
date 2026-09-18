"""Codex's growth construction (board 422), checked exactly: start from the symmetric simple arrangement whose regions are
the cyclic intervals (n(n-1)+2 labels); grow by cubical 2->4 moves (two squares of a 3-cube sharing an edge replaced by the
other four faces, adding the two absent labels), applied as full rotation orbits; verify with check() at every step
(all_labels only at the end). Depth-first search over move orbits for small n."""
import json, sys, collections, itertools, time
from pathlib import Path
from gks_scaffold import check, rotate
HERE = Path(__file__).resolve().parent

def lab(s, n): return ''.join('1' if i in s else '0' for i in range(n))
def flip(x, i): return x[:i] + ('1' if x[i] == '0' else '0') + x[i + 1:]

def interval_sphere(n):
    """faces of the dual of the cyclic-interval arrangement: square at interval [i..j] flipping (extend one end, shrink/extend the other)."""
    faces = set()
    def interval(i, L): return frozenset((i + t) % n for t in range(L))
    labels = {lab(frozenset(), n), lab(frozenset(range(n)), n)} | {lab(interval(i, L), n) for i in range(n) for L in range(1, n)}
    # squares: any 4-cycle of the cube on present labels
    for x in labels:
        for a, b in itertools.combinations(range(n), 2):
            y, z, w = flip(x, a), flip(flip(x, a), b), flip(x, b)
            if y in labels and z in labels and w in labels: faces.add(frozenset((x, y, z, w)))
    return labels, faces

def oriented_faces(face_sets, n):
    """orient squares consistently by BFS across shared edges (returns list of oriented 4-cycles or None)."""
    cyc = {}
    def square_cycle(sq):
        v = sorted(sq)[0]; nb = [x for x in sq if x != v and sum(a != b for a, b in zip(v, x)) == 1]; far = [x for x in sq if x != v and x not in nb][0]
        return [v, nb[0], far, nb[1]]
    sqs = [square_cycle(s) for s in face_sets]
    by_edge = collections.defaultdict(list)
    for i, c in enumerate(sqs):
        for j in range(4): by_edge[frozenset((c[j], c[(j + 1) % 4]))].append(i)
    oriented = {0: sqs[0]}; queue = collections.deque([0])
    while queue:
        i = queue.popleft(); c = oriented[i]
        for j in range(4):
            a, b = c[j], c[(j + 1) % 4]
            for i2 in by_edge[frozenset((a, b))]:
                if i2 in oriented or i2 == i: continue
                c2 = sqs[i2]; k2 = c2.index(a)
                oriented[i2] = c2 if c2[(k2 - 1) % 4] == b else c2[::-1]; queue.append(i2)
    if len(oriented) != len(sqs): return None
    return list(oriented.values())

def valid_sphere(face_sets, n, full=False):
    of = oriented_faces(face_sets, n)
    if of is None: return None
    r = check(n, of)
    ok = r['euler'] == 2 and set(r['edge_multiplicities']) == {2} and r['bad_edges'] == 0 and r['repeated_vertex_faces'] == 0 and r['vertices_single_rotation_cycle'] and r['curves_two_sides_connected'] and r['rotation_symmetric']
    if full: ok = ok and r['all_labels']
    return r if ok else None

def moves(labels, faces, n):
    """candidate 2->4 moves: (u, a, b, c) with squares ab and ac at u present and u^b^c, u^a^b^c absent."""
    out = []
    for x in labels:
        for a in range(n):
            xa = flip(x, a)
            if xa not in labels: continue
            for b, c in itertools.combinations([t for t in range(n) if t != a], 2):
                sab = frozenset((x, xa, flip(xa, b), flip(x, b))); sac = frozenset((x, xa, flip(xa, c), flip(x, c)))
                if sab in faces and sac in faces:
                    nb1, nb2 = flip(flip(x, b), c), flip(flip(xa, b), c)
                    if nb1 not in labels and nb2 not in labels: out.append((x, a, b, c))
    return out

def apply_move(labels, faces, n, mv):
    labels = set(labels); faces = set(faces)
    x, a, b, c = mv
    for k in range(n):
        u = rotate(x, k); A, B, C = (a - k) % n, (b - k) % n, (c - k) % n
        # careful: rotate(x,k) shifts string positions; axis index shifts consistently with rotate implementation
        ua = flip(u, A)
        sab = frozenset((u, ua, flip(ua, B), flip(u, B))); sac = frozenset((u, ua, flip(ua, C), flip(u, C)))
        if sab not in faces or sac not in faces: return None
        n1, n2 = flip(flip(u, B), C), flip(flip(ua, B), C)
        if n1 in labels or n2 in labels: return None
        faces.discard(sab); faces.discard(sac)
        faces |= {frozenset((u, flip(u, B), n1, flip(u, C))), frozenset((ua, flip(ua, B), n2, flip(ua, C))),
                  frozenset((flip(u, B), flip(ua, B), n2, n1)), frozenset((flip(u, C), flip(ua, C), n2, n1))}
        labels |= {n1, n2}
    return labels, faces

def grow(n, seconds):
    labels, faces = interval_sphere(n)
    assert valid_sphere(faces, n) is not None, 'interval start invalid'
    target = (1 << n); started = time.time(); best = [len(labels), None]; nodes = [0]
    def dfs(labels, faces, path):
        nodes[0] += 1
        if len(labels) > best[0]: best[0], best[1] = len(labels), list(path)
        if len(labels) == target: return (labels, faces, path)
        if time.time() - started > seconds: return None
        for mv in moves(labels, faces, n):
            res = apply_move(labels, faces, n, mv)
            if res is None: continue
            r = dfs(res[0], res[1], path + [mv])
            if r: return r
        return None
    res = dfs(labels, faces, [])
    out = dict(n=n, start_labels=len(labels), target=target, nodes=nodes[0], seconds=round(time.time() - started, 2), best_labels=best[0], moves=best[1])
    if res:
        r = valid_sphere(res[1], n, full=True); out['complete'] = r is not None; out['verification'] = r
        if r: (HERE / f'interval-growth-{n}-faces.json').write_text(json.dumps(dict(n=n, faces=oriented_faces(res[1], n), full17=False)) + '\n')
    else: out['complete'] = False
    return out

if __name__ == '__main__':
    for n in [int(a) for a in sys.argv[1:]] or [5, 7]:
        out = grow(n, float(__import__("os").environ.get("GROW_SECONDS", "120"))); print(json.dumps({k: v for k, v in out.items() if k != 'verification'}), flush=True)
        (HERE / f'interval-growth-{n}.json').write_text(json.dumps(out, indent=1) + '\n')

#!/usr/bin/env python3
"""Independent combinatorial audit. Metadata in the input is never trusted."""
import argparse
import collections
import hashlib
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError('Do not run this assertion-based independent audit with python -O')


def check(path):
    raw = Path(path).read_bytes()
    data = json.loads(raw)
    n = data['n']
    assert type(n) is int and n == 17, 'expected n = 17'
    assert isinstance(data['faces'], list) and data['faces'], 'expected a nonempty face list'
    faces = []
    edges = collections.defaultdict(list)
    vertices = set()
    for fi, face in enumerate(data['faces']):
        assert isinstance(face, list) and len(face) == 4, ('face length', fi)
        assert all(isinstance(s, str) and len(s) == n and set(s) <= {'0', '1'} for s in face), ('pattern', fi)
        # Character i is bit i, matching the input's curve numbering.
        vs = {int(s[::-1], 2) for s in face}
        assert len(vs) == 4, ('repeated vertex', fi)
        u = min(vs)
        bits = sorted(v ^ u for v in vs if v != u and (v ^ u) & ((v ^ u) - 1) == 0)
        assert len(bits) == 2, ('not a square', fi)
        a, b = bits
        assert vs == {u, u ^ a, u ^ b, u ^ a ^ b}, ('not a square', fi)
        cycle = [u, u ^ a, u ^ a ^ b, u ^ b]
        faces.append(cycle)
        vertices.update(vs)
        for x, y in zip(cycle, cycle[1:] + cycle[:1]):
            edges[min(x, y), max(x, y)].append((fi, x < y))
    assert all(len(fs) == 2 for fs in edges.values()), dict(collections.Counter(map(len, edges.values())))
    assert len({tuple(sorted(f)) for f in faces}) == len(faces), 'duplicate faces'
    adj = [[] for _ in faces]
    graph = collections.defaultdict(list)
    curve_graphs = [collections.defaultdict(list) for _ in range(n)]
    for (u, v), ((f, d), (g, e)) in edges.items():
        adj[f].append((g, d == e))
        adj[g].append((f, d == e))
        graph[u].append(v)
        graph[v].append(u)
        i = (u ^ v).bit_length() - 1
        curve_graphs[i][f].append(g)
        curve_graphs[i][g].append(f)
    orientation = {0: False}
    queue = [0]
    for f in queue:
        for g, flip in adj[f]:
            value = orientation[f] ^ flip
            if g in orientation:
                assert orientation[g] == value, ('nonorientable', f, g)
            else:
                orientation[g] = value
                queue.append(g)
    assert len(queue) == len(faces), 'disconnected face adjacency'
    oriented = [list(reversed(f)) if orientation[i] else f for i, f in enumerate(faces)]
    links = collections.defaultdict(dict)
    for f in oriented:
        for i, v in enumerate(f):
            prev, nxt = f[(i - 1) % 4], f[(i + 1) % 4]
            assert prev not in links[v], ('ambiguous link', v)
            links[v][prev] = nxt
    for v, link in links.items():
        assert set(link) == set(link.values()) == set(graph[v]), ('link not permutation', v)
        first = next(iter(link))
        seen, cur = set(), first
        while cur not in seen:
            seen.add(cur)
            cur = link[cur]
        assert cur == first and len(seen) == len(link), ('multiple vertex links', v)

    def component(g, start, allowed=lambda _: True):
        seen, todo = {start}, [start]
        for v in todo:
            for w in g[v]:
                if allowed(w) and w not in seen:
                    seen.add(w)
                    todo.append(w)
        return seen

    assert len(component(graph, next(iter(vertices)))) == len(vertices), 'disconnected map'
    chi = len(vertices) - len(edges) + len(faces)
    assert chi == 2, ('Euler characteristic', chi)
    curve_lengths, side_sizes = [], []
    for i, g in enumerate(curve_graphs):
        assert g and all(len(ns) == 2 for ns in g.values()), ('curve not 2-regular', i)
        assert len(component(g, next(iter(g)))) == len(g), ('curve disconnected', i)
        curve_lengths.append(len(g))
        sizes = []
        for side in (0, 1):
            target = {v for v in vertices if (v >> i) & 1 == side}
            assert target, ('empty side', i, side)
            seen = component(graph, next(iter(target)), lambda v: (v >> i) & 1 == side)
            assert seen == target, ('disconnected side', i, side)
            sizes.append(len(seen))
        side_sizes.append(sizes)
    assert vertices == set(range(1 << n)), 'missing patterns'
    assert len(faces) == (1 << n) - 2 and len(edges) == 2 * len(faces), 'counts'
    rotate = lambda v: (v >> 1) | ((v & 1) << (n - 1))
    canon = lambda f: min(tuple(f[k:] + f[:k]) for k in range(4))
    oriented_set = {canon(f) for f in oriented}
    assert all(canon([rotate(v) for v in f]) in oriented_set for f in oriented), 'symmetry reverses or misses faces'
    # At each fixed vertex the action is one step around the link, with opposite
    # steps at the two poles. This additionally identifies the rotation number.
    full = (1 << n) - 1
    pole_steps = []
    for pole in (0, full):
        assert len(links[pole]) == n, ('pole degree', pole)
        plus = all(links[pole][pole ^ (1 << i)] == pole ^ (1 << ((i + 1) % n)) for i in range(n))
        minus = all(links[pole][pole ^ (1 << i)] == pole ^ (1 << ((i - 1) % n)) for i in range(n))
        assert plus or minus, ('pole rotation not one step', pole)
        pole_steps.append(1 if plus else -1)
    assert pole_steps[0] == -pole_steps[1], 'inconsistent pole steps'
    result = dict(sha256=hashlib.sha256(raw).hexdigest(), n=n,
                  regions=len(vertices), arcs=len(edges), crossings=len(faces), euler=chi,
                  checks={name: True for name in ['square_crossings', 'two_faces_per_arc',
                      'connected_oriented_surface', 'single_vertex_links', 'euler_two',
                      'single_cycle_per_curve', 'connected_sides', 'all_patterns',
                      'simple_crossings', 'orientation_preserving_rotation']},
                  curve_lengths=curve_lengths, side_sizes=side_sizes, pole_steps=pole_steps,
                  verdict='PASS: finite combinatorial conditions; geometric realization is a separate theorem')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('input', nargs='?', default='venn17-local-c3-s2.json')
    parser.add_argument('--output')
    args = parser.parse_args()
    result = check(args.input)
    out = json.dumps(result, indent=2) + '\n'
    print(out, end='')
    if args.output:
        Path(args.output).write_text(out)

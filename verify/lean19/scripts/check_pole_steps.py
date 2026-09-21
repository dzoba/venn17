#!/usr/bin/env python3
"""Confirm the two oriented pole-link steps expected by PoleRotationData.lean."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
raw = json.loads((ROOT / "venn19-closure-s196002.json").read_text())
n = raw["n"]
full = (1 << n) - 1
faces = []
adj = []
pending = {}

for fi, face in enumerate(raw["faces"]):
    vs = sorted(int(s[::-1], 2) for s in face)
    u = vs[0]
    a, b = sorted(x ^ u for x in vs[1:] if (x ^ u) & ((x ^ u) - 1) == 0)
    cycle = (u, u ^ a, u ^ a ^ b, u ^ b)
    faces.append(cycle)
    adj.append([])
    for x, y in zip(cycle, cycle[1:] + cycle[:1]):
        key = (min(x, y), max(x, y))
        direction = x < y
        if key in pending:
            fj, other_direction = pending.pop(key)
            flip = other_direction == direction
            adj[fi].append((fj, flip))
            adj[fj].append((fi, flip))
        else:
            pending[key] = (fi, direction)

assert not pending
sign = [None] * len(faces)
sign[0] = False
queue = [0]
for fi in queue:
    for fj, flip in adj[fi]:
        expected = sign[fi] ^ flip
        if sign[fj] is None:
            sign[fj] = expected
            queue.append(fj)
        else:
            assert sign[fj] == expected
assert len(queue) == len(faces)

links = {0: {}, full: {}}
for fi, face in enumerate(faces):
    if sign[fi]:
        face = tuple(reversed(face))
    for pole in links:
        if pole in face:
            i = face.index(pole)
            links[pole][face[(i - 1) % 4]] = face[(i + 1) % 4]

steps = []
for pole in (0, full):
    assert len(links[pole]) == n
    step = next(step for step in (1, n - 1) if all(
        links[pole][pole ^ (1 << i)] == pole ^ (1 << ((i + step) % n))
        for i in range(n)))
    steps.append(step)

print(json.dumps({
    "curve_link_steps": steps,
    "triangulated_link_steps": [2 * steps[0], 2 * steps[1]],
    "expected_by_PoleRotationData": [2, 2 * n - 2],
    "passes": [2 * steps[0], 2 * steps[1]] == [2, 2 * n - 2],
}, indent=2))

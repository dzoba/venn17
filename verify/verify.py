#!/usr/bin/env python3
"""Standalone structural checker for a symmetric Venn certificate.

Usage:  python3 verify.py <certificate.json>

The certificate is a dual map: {"n": n, "faces": [[l0, l1, l2, l3], ...]} where each
label is an n-character LSB-first bit string naming one region of the arrangement and
each face is one vertex (crossing) of the Venn diagram.

verify.py re-orients the faces with interval_growth.oriented_faces and runs
gks_scaffold.check on the result, then prints every field of the report. The two
modules are the ones written for the scaffold work and share no code with the search
program that produced the certificates.

PASS requires all eight of:
    all_labels                        every one of the 2^n labels present exactly once
    euler == 2                        V - E + F = 2 (the map is a sphere)
    every edge multiplicity == 2      each edge borders exactly two faces
    vertices_single_rotation_cycle    the rotation at every vertex is one cycle
    curves_two_sides_connected        both sides of every curve are connected
    rotation_symmetric                the face set is invariant under the Z_n rotation
    non_transversal_faces == 0        every crossing is transversal (w.w bit pattern)
    repeated_vertex_faces == 0        no face repeats a vertex
"""
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from interval_growth import oriented_faces          # noqa: E402
from gks_scaffold import check                      # noqa: E402


def verify(path):
    t0 = time.time()
    d = json.load(open(path))
    n = d['n']
    faces = {frozenset(x) for x in d['faces']}
    print(f'file        {path}')
    print(f'n           {n}')
    print(f'faces       {len(d["faces"])} listed, {len(faces)} distinct')

    of = oriented_faces(faces, n)
    if of is None:
        print('oriented_faces: FAILED (faces do not orient consistently)')
        print('RESULT: FAIL')
        return False

    r = check(n, of)
    print('report:')
    for k in sorted(r):
        print(f'  {k:32} {r[k]}')

    criteria = [
        ('all_labels', bool(r['all_labels'])),
        ('euler == 2', r['euler'] == 2),
        ('edge multiplicities all 2', set(r['edge_multiplicities']) == {2}),
        ('vertices_single_rotation_cycle', bool(r['vertices_single_rotation_cycle'])),
        ('curves_two_sides_connected', bool(r['curves_two_sides_connected'])),
        ('rotation_symmetric', bool(r['rotation_symmetric'])),
        ('non_transversal_faces == 0', r['non_transversal_faces'] == 0),
        ('repeated_vertex_faces == 0', r['repeated_vertex_faces'] == 0),
    ]
    print('criteria:')
    for name, ok in criteria:
        print(f'  {"ok " if ok else "BAD"} {name}')

    passed = all(ok for _, ok in criteria)
    print(f'elapsed     {time.time() - t0:.1f} s')
    print(f'RESULT: {"PASS" if passed else "FAIL"}')
    return passed


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(2)
    ok = True
    for p in sys.argv[1:]:
        ok &= verify(p)
        print()
    sys.exit(0 if ok else 1)

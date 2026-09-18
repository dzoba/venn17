"""Monotonicity test on dual-map exports ({"n","faces":[[4 LSB-first label strings]...]}).
A Venn diagram is monotone (Bultena-Grunbaum-Ruskey) iff every k-region, 0<k<n, is adjacent to a (k-1)-region and a
(k+1)-region. In the dual: every label of weight k has a neighbour (Hamming distance 1 along a square edge) of weight k-1
and one of weight k+1. Prints, per file, the label count and the number of labels violating this (0 = monotone).
Usage: python3 monotone_test.py <files...>"""
import json, sys
def test(path):
    d = json.load(open(path)); n = d['n']; adj = {}
    for f in d['faces']:
        for i in range(4):
            for j in range(i + 1, 4):
                a, b = f[i], f[j]
                if sum(x != y for x, y in zip(a, b)) == 1: adj.setdefault(a, set()).add(b); adj.setdefault(b, set()).add(a)
    bad = [v for v, nb in adj.items() if 0 < v.count('1') < n and not (any(u.count('1') == v.count('1') + 1 for u in nb) and any(u.count('1') == v.count('1') - 1 for u in nb))]
    return n, len(adj), len(bad), sorted(bad)[:3]
out = {}
for p in sys.argv[1:]:
    n, V, bad, ex = test(p); out[p] = dict(n=n, labels=V, complete=(V == 2 ** n), non_monotone_labels=bad, examples=ex)
    print(f'{p}: n={n} labels={V} complete={V == 2**n} non_monotone_labels={bad} e.g. {ex}')
json.dump(out, open('monotone-results.json', 'w'), indent=1)

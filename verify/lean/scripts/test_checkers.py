#!/usr/bin/env python3
"""Adversarial regression tests; temporary mutations never alter the supplied file."""
import copy
import json
import subprocess
import tempfile
import unittest
from pathlib import Path

from check import check

ROOT = Path(__file__).resolve().parents[1]


class CheckerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original = json.loads((ROOT / 'venn17-local-c3-s2.json').read_text())
        cls.executable = ROOT / '.lake/build/bin/venn_check'

    def run_case(self, data, expected, python=True):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / 'input.json'
            path.write_text(json.dumps(data))
            result = subprocess.run([str(self.executable), str(path)], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0 if expected else 1, result.stdout + result.stderr)
            if python:
                if expected:
                    self.assertEqual(check(path)['regions'], 131072)
                else:
                    with self.assertRaises((AssertionError, KeyError, ValueError)):
                        check(path)
            return result.stdout + result.stderr

    def test_metadata_and_face_order_are_untrusted(self):
        data = copy.deepcopy(self.original)
        data.update(labels=1, energy=999, missing=999, duplicates=999, full=False)
        data['faces'] = [f[::-1] for f in reversed(data['faces'])]
        self.run_case(data, True)

    def test_removed_crossing(self):
        data = copy.deepcopy(self.original)
        data['faces'].pop()
        out = self.run_case(data, False)
        self.assertIn('twoFacesPerArc := false', out)

    def test_duplicate_crossing(self):
        data = copy.deepcopy(self.original)
        data['faces'].append(data['faces'][0])
        out = self.run_case(data, False)
        self.assertIn('twoFacesPerArc := false', out)

    def test_repeated_corner(self):
        data = {'n': 17, 'faces': [copy.deepcopy(self.original['faces'][0])]}
        data['faces'][0][1] = data['faces'][0][0]
        self.run_case(data, False)

    def test_non_square(self):
        self.run_case({'n': 17, 'faces': [['0'*17, '1'*17, '01'+'0'*15, '10'+'0'*15]]}, False)

    def test_bad_pattern_and_size(self):
        for s in ['x'*17, '0'*16, '0'*18]:
            self.run_case({'n': 17, 'faces': [[s]*4]}, False)
        self.run_case({'n': 16, 'faces': []}, False)

    def test_empty(self):
        self.run_case({'n': 17, 'faces': []}, False)


if __name__ == '__main__':
    unittest.main(verbosity=2)

import json
from math import comb, factorial
from pathlib import Path
import subprocess
import tempfile
import unittest

from oracles.cube_cycles import canonical_patterns, support_cycles, cube_total, support_defect

ROOT = Path(__file__).resolve().parents[1]


class CycleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.patterns = canonical_patterns(14)
        cls.support = support_cycles(cls.patterns, 14)
        cls.totals = [cube_total(n, cls.support) for n in range(8)]
        cls.tmp = tempfile.TemporaryDirectory()
        cls.binary = str(Path(cls.tmp.name) / 'labelled')
        subprocess.run(['g++', '-std=c++17', '-O3', '-Wall', '-Wextra', '-Werror',
                        str(ROOT / 'oracles/labelled_cube_cycles.cpp'), '-o', cls.binary], check=True)

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def labelled(self, n, length):
        lines = subprocess.check_output([self.binary, str(n), str(length)], text=True).splitlines()
        return [list(map(int, line.split())) for line in lines[:-1]], int(lines[-1].split()[1])

    def test_c14_patterns_and_counts(self):
        self.assertEqual(self.patterns, [0, 0, 0, 0, 392, 33530, 89782, 38232])
        self.assertEqual(self.support, [0, 0, 0, 0, 5376, 4598400, 147755520, 880865280])
        self.assertEqual(self.totals, [0, 0, 0, 0, 5376, 4652160, 203258880, 3337213440])

    def test_independent_labelled_dfs_all_four_cubes(self):
        for n in range(4, 8):
            with self.subTest(n=n):
                rows, total = self.labelled(n, 14)
                self.assertEqual(total, self.totals[n])
                for k, rooted, cycles in rows:
                    self.assertEqual(rooted, comb(n, k) * factorial(k) * self.patterns[k])
                    self.assertEqual(cycles, (1 << (n-k)) * comb(n, k) * self.support[k])

    def test_normalization_small_known_cases(self):
        # Q2 is one square; Q3 has six face squares and sixteen ordinary hexagons (including chorded ones).
        for length, n, expected in [(4, 2, 1), (4, 3, 6), (6, 3, 16), (8, 3, 6)]:
            with self.subTest(length=length, n=n):
                patterns = canonical_patterns(length)
                support = support_cycles(patterns, length)
                self.assertEqual(cube_total(n, support), expected)
                self.assertEqual(self.labelled(n, length)[1], expected)

    def test_inclusion_exclusion_and_negative_controls(self):
        for n in range(8):
            self.assertEqual(support_defect(n, self.totals), self.support[n])
        self.assertEqual(support_defect(7, self.totals), 880865280)
        old = self.totals[:]
        old[7] = 406517760
        self.assertEqual(support_defect(7, old), -2049830400)
        self.assertNotEqual(old[7], self.totals[7])
        self.assertGreater(support_defect(7, self.totals), 0)

    def test_receipt(self):
        receipt = json.loads((ROOT / 'conformance/receipts/c14-cubes.json').read_text())
        self.assertEqual(receipt['canonical_patterns'], self.patterns)
        self.assertEqual(receipt['support_cycles'], self.support)
        self.assertEqual(receipt['cube_totals'], self.totals)
        self.assertEqual(receipt['seventh_support_defect'], support_defect(7, self.totals))


if __name__ == '__main__':
    unittest.main()

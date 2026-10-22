from itertools import product
from math import factorial
import unittest

from oracles.cube_cycles import canonical_patterns, support_cycles
from oracles.pair_partition_cycles import full_support_pairings

EDGE = (2, [(0, 1)])
TRIANGLE = (3, [(0, 1), (1, 2), (0, 2)])
PATH = (3, [(0, 1), (1, 2)])


def ordinary_cycles(factors, length):
    """Direct unrooted subgraph enumeration, retaining coordinate support.

    Minimum vertex is the root; first-neighbor < last-neighbor removes reversal.
    Unlike the cube paths this does not divide a traversal count afterwards.
    """
    vertices = list(product(*(range(n) for n, _ in factors)))
    index = {v: i for i, v in enumerate(vertices)}
    adjacency = [[] for _ in vertices]
    for v, i in index.items():
        for axis, (_, edges) in enumerate(factors):
            for a, b in edges:
                if v[axis] in (a, b):
                    w = list(v)
                    w[axis] = b if v[axis] == a else a
                    adjacency[i].append((index[tuple(w)], 1 << axis))
    counts = [0] * (1 << len(factors))
    for root in range(len(vertices)):
        seen = {root}

        def walk(vertex, first, depth, mask):
            if depth == length - 1:
                for neighbor, axis in adjacency[vertex]:
                    if neighbor == root and first < vertex:
                        counts[mask | axis] += 1
                return
            for neighbor, axis in adjacency[vertex]:
                if neighbor > root and neighbor not in seen:
                    seen.add(neighbor)
                    walk(neighbor, neighbor if depth == 0 else first, depth+1, mask | axis)
                    seen.remove(neighbor)

        walk(root, -1, 0, 0)
    return counts


class SymbolProofTests(unittest.TestCase):
    def test_pair_partition_coefficients(self):
        expected_pairs = [1, 4, 27, 248, 2830, 38232]
        expected_coefficients = [1, 16, 648, 47616, 5433600, 880865280]
        for k, pairs, coefficient in zip(range(2, 8), expected_pairs, expected_coefficients):
            with self.subTest(k=k):
                self.assertEqual(full_support_pairings(k), pairs)
                words = canonical_patterns(2*k)
                self.assertEqual(words[k], pairs)
                self.assertEqual(support_cycles(words, 2*k)[k], coefficient)
                self.assertEqual(2**k * factorial(k) * pairs, 4*k * coefficient)

    def test_top_symbol_on_nonbipartite_factors(self):
        for factors, length, gamma in [([TRIANGLE, PATH], 4, 1),
                                        ([TRIANGLE, EDGE, EDGE], 6, 16),
                                        ([EDGE]*4, 8, 648)]:
            with self.subTest(length=length):
                counts = ordinary_cycles(factors, length)
                expected = gamma
                for _, edges in factors:
                    expected *= len(edges)
                self.assertEqual(counts[-1], expected)

    def test_support_defect_and_order_upper_bound(self):
        factors = [TRIANGLE, EDGE, EDGE]
        for length in (4, 6):
            counts = ordinary_cycles(factors, length)
            defect = 0
            for mask in range(8):
                selected = [g for i, g in enumerate(factors) if mask & (1 << i)]
                omitted_vertices = 1
                for i, (n, _) in enumerate(factors):
                    if not mask & (1 << i):
                        omitted_vertices *= n
                total = sum(ordinary_cycles(selected, length))
                defect += (-1)**(3-mask.bit_count()) * omitted_vertices * total
            self.assertEqual(defect, counts[-1])
            if length == 4:
                self.assertEqual(defect, 0)

    def test_centering_is_required(self):
        # f=c4, a=Q2, b=K1: uncentered delta_a f(b)=1, but D2(a,b)=0.
        c4_a = sum(ordinary_cycles([EDGE, EDGE], 4))
        c4_b = 0
        delta = c4_a - 4*c4_b
        centered = delta - 1*c4_a
        self.assertEqual(delta, 1)
        self.assertEqual(centered, 0)


if __name__ == '__main__':
    unittest.main()

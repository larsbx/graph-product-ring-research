#!/usr/bin/env python3
"""Independent finite checks for all-k NB/primitive coordinate-support proof.

No third-party packages. Hashimoto traces are computed on the directed
arc graph, not from cube words or the Chebyshev recurrence. Unlabelled
pairings are enumerated independently of the inclusion-exclusion formula.
Tests cannot replace mathematical proof or external acceptance.
"""
import itertools
import math
import unittest
from collections import defaultdict


def graph(vertices, edges):
    vertices = tuple(vertices)
    edges = frozenset(frozenset(e) for e in edges)
    assert all(len(e) == 2 for e in edges)
    return vertices, edges


def path_graph(n):
    return graph(range(n), ((i, i + 1) for i in range(n - 1)))


def cycle_graph(n):
    return graph(range(n), ((i, (i + 1) % n) for i in range(n)))


def complete_graph(n):
    return graph(range(n), itertools.combinations(range(n), 2))


def cartesian(g, h):
    vg, eg = g
    vh, eh = h
    verts = [(u, v) for u in vg for v in vh]
    edges = []
    for v in vh:
        for e in eg:
            u, w = tuple(e)
            edges.append(((u, v), (w, v)))
    for u in vg:
        for e in eh:
            v, w = tuple(e)
            edges.append(((u, v), (u, w)))
    return graph(verts, edges)


def cube(n):
    return graph(range(1 << n),
                 ((v, v ^ (1 << i))
                  for v in range(1 << n)
                  for i in range(n)
                  if v < (v ^ (1 << i))))


def epsilon(g):
    return len(g[0])


def edge_count(g):
    return len(g[1])


def hashimoto_trace(g, m):
    """Trace of the m-th power of the *arc* adjacency, using sparse DP."""
    if m < 1:
        raise ValueError("m must be positive")
    nbr = {v: set() for v in g[0]}
    for e in g[1]:
        u, v = tuple(e)
        nbr[u].add(v)
        nbr[v].add(u)
    arcs = [(u, v) for u in g[0] for v in nbr[u]]
    idx = {arc: i for i, arc in enumerate(arcs)}
    successors = []
    for u, v in arcs:
        successors.append([idx[(v, w)] for w in nbr[v] if w != u])
    answer = 0
    for root in range(len(arcs)):
        current = {root: 1}
        for _ in range(m):
            following = defaultdict(int)
            for a, count in current.items():
                for b in successors[a]:
                    following[b] += count
            current = following
            if not current:
                break
        answer += current.get(root, 0)
    return answer


def centered_defect(f, factors):
    total = 0
    n = len(factors)
    for mask in range(1, 1 << n):
        in_set = [i for i in range(n) if mask & (1 << i)]
        outside = [i for i in range(n) if not mask & (1 << i)]
        g = factors[in_set[0]]
        for i in in_set[1:]:
            g = cartesian(g, factors[i])
        weight = (-1) ** (n - len(in_set))
        for i in outside:
            weight *= epsilon(factors[i])
        total += weight * f(g)
    return total


def double_factorial_odd(n):
    result = 1
    for x in range(1, n + 1, 2):
        result *= x
    return result


def cycle_matchings(n, j):
    if j == 0:
        return 1
    return n * math.comb(n - j, j) // (n - j)


def pairing_ie(k):
    n = 2 * k
    return sum((-1) ** j * cycle_matchings(n, j)
               * double_factorial_odd(n - 2 * j - 1)
               for j in range(k + 1))


def chebyshev_lead(k):
    n = 2 * k
    return sum((-1) ** j
               * (n * math.comb(n - j, j) // (n - j))
               * double_factorial_odd(2 * (k - j) - 1)
               for j in range(k + 1))


def canonical_pairings(n):
    """All matchings of n labelled positions, with no cycle-word shortcuts."""
    if n == 0:
        yield ()
        return
    first = 0
    for other in range(1, n):
        remain = [v for v in range(n) if v not in (first, other)]
        for p in pairings_of(remain):
            yield ((first, other),) + p


def pairings_of(vertices):
    if not vertices:
        yield ()
        return
    a, *rest = vertices
    for b in rest:
        remaining = [v for v in rest if v != b]
        for p in pairings_of(remaining):
            yield ((a, b),) + p


def count_good_pairings(k):
    n = 2 * k
    return sum(1 for pairs in canonical_pairings(n)
               if all((a - b) % n not in (1, n - 1)
                      for a, b in pairs))


def count_simple_pairings(k):
    n = 2 * k
    answer = 0
    for pairs in canonical_pairings(n):
        match = {}
        for a, b in pairs:
            match[a] = b
            match[b] = a
        if all(not all(i0 <= match[pos] < j for pos in range(i0, j))
               for i0 in range(n)
               for j in range(i0 + 2, n + 1)
               if j - i0 < n):
            answer += 1
    return answer


def mobius(n):
    result = 1
    p = 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            result *= -1
            if n % p == 0:
                return 0
            while n % p == 0:
                n //= p
        p += 1
    return -result if n > 1 else result


def primitive_count(g, m):
    value = sum(mobius(m // r) * hashimoto_trace(g, r)
                for r in range(1, m + 1) if m % r == 0)
    assert value % m == 0
    return value // m


class NonbacktrackingSupportTests(unittest.TestCase):
    def test_cyclic_pairing_coefficients(self):
        expected_r = {2: 1, 3: 4, 4: 31, 5: 293, 6: 3326, 7: 44189}
        expected_beta = {2: 8, 3: 192, 4: 11904, 5: 1125120,
                         6: 153262080, 7: 28507207680}
        for k in expected_r:
            with self.subTest(k=k):
                self.assertEqual(pairing_ie(k), expected_r[k])
                self.assertEqual(chebyshev_lead(k), expected_r[k])
                self.assertEqual((1 << k) * math.factorial(k) * pairing_ie(k),
                                 expected_beta[k])
        for k in range(2, 7):
            self.assertEqual(count_good_pairings(k), expected_r[k])

    def test_connected_pairing_complement(self):
        # Independent finite connected-chord word check, k <= 6.
        expected_a = {2: 1, 3: 4, 4: 27, 5: 248, 6: 2830}
        for k, a in expected_a.items():
            self.assertEqual(count_simple_pairings(k), a)
            r = pairing_ie(k)
            gamma = (1 << k) * math.factorial(k) * a // (4 * k)
            beta = (1 << k) * math.factorial(k) * r
            eta = beta // (2 * k) - 2 * gamma
            known = {2: 0, 3: 0, 4: 192, 5: 17280, 6: 1904640}
            self.assertEqual(eta, known[k])

    def test_arc_trace_sanity_and_seam(self):
        self.assertEqual(hashimoto_trace(path_graph(3), 4), 0)
        self.assertEqual(hashimoto_trace(cycle_graph(4), 4), 8)
        self.assertEqual(hashimoto_trace(cycle_graph(4), 8), 8)
        self.assertEqual(hashimoto_trace(cycle_graph(5), 5), 10)
        self.assertEqual(hashimoto_trace(complete_graph(3), 3), 6)
        # Q2 is a 4-cycle. The same 4-cycle walked twice contributes
        # 8 cyclically NB roots at length 8 but zero primitive 8-classes.
        self.assertEqual(primitive_count(cube(2), 8), 0)

    def test_cube_defects_against_pair_words(self):
        for k in range(2, 5):
            expected = (1 << k) * math.factorial(k) * pairing_ie(k)
            actual = centered_defect(lambda g: hashimoto_trace(g, 2 * k),
                                     [path_graph(2)] * k)
            self.assertEqual(actual, expected)

    def test_mixed_factors_including_irregular_and_odd_cycles(self):
        fixtures = [
            [path_graph(3), complete_graph(3)],
            [path_graph(3), cycle_graph(4)],
            [path_graph(2), path_graph(3), complete_graph(3)],
            [path_graph(2), path_graph(3), cycle_graph(4)],
            [path_graph(2), path_graph(3), path_graph(2), complete_graph(3)],
        ]
        for factors in fixtures:
            k = len(factors)
            beta = (1 << k) * math.factorial(k) * pairing_ie(k)
            e_product = math.prod(edge_count(g) for g in factors)
            with self.subTest(k=k, degree_profile=tuple(edge_count(g) for g in factors)):
                self.assertEqual(
                    centered_defect(lambda g: hashimoto_trace(g, 2 * k), factors),
                    beta * e_product)

    def test_upper_order_on_full_ring_fixtures(self):
        for k, factors in [
            (2, [path_graph(2), path_graph(3), complete_graph(3)]),
            (3, [path_graph(2), path_graph(2), path_graph(3), complete_graph(3)]),
        ]:
            self.assertEqual(
                centered_defect(lambda g: hashimoto_trace(g, 2 * k), factors), 0)

    def test_primitive_mobius_symbol_mixed(self):
        for factors in [
            [path_graph(3), complete_graph(3)],
            [path_graph(2), path_graph(3), complete_graph(3)],
        ]:
            k = len(factors)
            beta = (1 << k) * math.factorial(k) * pairing_ie(k)
            expected = beta * math.prod(edge_count(g) for g in factors) // (2 * k)
            self.assertEqual(
                centered_defect(lambda g: primitive_count(g, 2 * k), factors),
                expected)


if __name__ == "__main__":
    unittest.main()

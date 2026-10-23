import random
import unittest
from math import comb
from oracles.mscs4 import count, cube_edges, auxiliary_cycles, validate
from oracles.cube_cycles import canonical_patterns, support_cycles


class MSCS4Tests(unittest.TestCase):
    def test_independent_fixtures(self):
        self.assertEqual(support_cycles(canonical_patterns(8), 8)[4], 648)
        for n, expected in [(3, 0), (4, 648), (5, 6480)]:
            self.assertEqual(count(n, cube_edges(n)), expected)

    def test_single_cycle_and_chords(self):
        word = [0,1,2,3,0,1,2,3]
        v = 0; edges = []
        for i in word:
            w = v ^ (1 << i); edges.append((v,w)); v = w
        self.assertEqual(count(4, edges), 1)
        self.assertEqual(count(4, edges[:-1]), 0)
        self.assertEqual(count(4, edges + edges), 1)

    def test_random_subgraphs_and_wedge_bound(self):
        rng = random.Random(18)
        full = sorted(cube_edges(4))
        for _ in range(30):
            edges = {e for e in full if rng.random() < .6}
            value = count(4, edges)
            self.assertLessEqual(auxiliary_cycles(4, edges), 16 * value)
            # independent face-template counting, no traversal in subgraph
            templates = cycle_templates()
            self.assertEqual(value, sum(t <= edges for t in templates))

    def test_invalid(self):
        for edges in [[(0,0)], [(0,3)], [(0,16)], [(-1,0)]]:
            with self.assertRaises(ValueError): validate(4, edges)


def cycle_templates():
    # Exhaustive 4-coordinate pair permutations, translated to every vertex.
    from itertools import permutations
    templates = set()
    for word in set(permutations([0,0,1,1,2,2,3,3])):
        for start in range(16):
            v=start; seen={v}; edges=[]
            for t,i in enumerate(word):
                w=v^(1<<i); edges.append(tuple(sorted((v,w))))
                if w in seen and not (t==7 and w==start): break
                seen.add(w); v=w
            else:
                templates.add(frozenset(edges))
    return templates

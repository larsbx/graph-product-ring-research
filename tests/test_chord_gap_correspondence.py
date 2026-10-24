"""Cyclic witness regressions independent of the C++ prefix oracle."""
from math import factorial
import unittest


def matchings(ps):
    if not ps:
        yield ()
    else:
        a = ps[0]
        for b in ps[1:]:
            for tail in matchings(tuple(x for x in ps[1:] if x != b)):
                yield ((a, b),) + tail


def components(pairs):
    def crosses(e, f):
        a, b = sorted(e)
        c, d = sorted(f)
        return (a < c < b) != (a < d < b)
    remaining = set(range(len(pairs)))
    result = []
    while remaining:
        found = {remaining.pop()}
        todo = list(found)
        while todo:
            i = todo.pop()
            new = {j for j in remaining if crosses(pairs[i], pairs[j])}
            remaining -= new
            found |= new
            todo.extend(new)
        result.append(found)
    return result


def closed(pairs, s):
    return all((a in s) == (b in s) for a, b in pairs)


def gaps(pairs, component):
    n = 2 * len(pairs)
    ends = sorted(p for i in component for p in pairs[i])
    for i, left in enumerate(ends):
        right = ends[(i + 1) % len(ends)]
        yield {(left + j) % n for j in range(1, (right - left) % n)}


def simple(pairs):
    colors = {p: i for i, e in enumerate(pairs) for p in e}
    x = 0
    seen = {0}
    for p in range(2 * len(pairs) - 1):
        x ^= 1 << colors[p]
        if x in seen:
            return False
        seen.add(x)
    return True


class ChordGapTests(unittest.TestCase):
    def check_matching(self, pairs):
        n = 2 * len(pairs)
        cs = components(pairs)
        intervals = [{(s + j) % n for j in range(length)}
                     for s in range(n) for length in range(1, n)]
        cyclic = [s for s in intervals if closed(pairs, s)]
        linear = [set(range(i, j)) for i in range(n) for j in range(i + 1, n + 1)
                  if j - i < n and closed(pairs, set(range(i, j)))]
        self.assertEqual(len(cs) == 1, not cyclic, pairs)
        self.assertEqual(bool(cyclic), bool(linear), pairs)
        self.assertEqual(simple(pairs), not cyclic, pairs)
        for s in cyclic:
            self.assertTrue(closed(pairs, set(range(n)) - s))
        if len(cs) > 1:
            for c in cs:
                gs = list(gaps(pairs, c))
                self.assertTrue(any(gs))
                for g in gs:
                    self.assertTrue(closed(pairs, g), (pairs, c, g))
                    self.assertLess(len(g), n)
                for i, e in enumerate(pairs):
                    if i not in c:
                        self.assertEqual(sum(set(e) <= g for g in gs), 1)

    def test_exhaustive_components_and_gaps(self):
        for k, expected in enumerate((1, 1, 4, 27, 248), 1):
            total = connected = 0
            for pairs in matchings(tuple(range(2 * k))):
                self.check_matching(pairs)
                total += 1
                connected += len(components(pairs)) == 1
            self.assertEqual(total, factorial(2*k) // (2**k * factorial(k)))
            self.assertEqual(connected, expected)

    def test_rotations_reflections_and_boundaries(self):
        fixtures = [((0, 2), (1, 3)), ((0, 1), (2, 3)), ((0, 3), (1, 2)),
                    ((0, 2), (1, 3), (4, 6), (5, 7)),
                    ((0, 7), (1, 3), (2, 4), (5, 6))]
        for pairs in fixtures:
            n = 2 * len(pairs)
            for sign in (1, -1):
                for shift in range(n):
                    self.check_matching(tuple(tuple((sign*p+shift) % n for p in e)
                                              for e in pairs))
        self.assertIn({0, 3}, list(gaps(((0, 3), (1, 2)), {1})))
        self.assertTrue(closed(((0, 3), (1, 2)), {1, 2}))

    def test_positive_witness(self):
        for k in range(2, 21):
            pairs = tuple((i, i+k) for i in range(k))
            self.assertEqual(len(components(pairs)), 1)
            self.assertTrue(simple(pairs))

    def test_merged_normalization(self):
        # k=9,10 are recurrence-derived predictions, not enumerated counts.
        counts = (1, 4, 27, 248, 2830, 38232, 593859, 10401712, 202601898)
        expected = (1, 16, 648, 47616, 5433600, 880865280,
                    191555159040, 53682819563520, 18821165247037440)
        for k, a, gamma in zip(range(2, 11), counts, expected):
            quotient, remainder = divmod(2**k * factorial(k) * a, 4*k)
            self.assertEqual(remainder, 0)
            self.assertEqual(quotient, gamma)
            self.assertEqual(2**(k-2) * factorial(k-1) * a, gamma)


if __name__ == '__main__':
    unittest.main()

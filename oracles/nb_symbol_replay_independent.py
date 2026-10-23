#!/usr/bin/env python3
"""Independent finite replay: cyclic pair matchings and Hashimoto traces.

No imports from graph-product-ring-research; no third-party packages.
"""
from itertools import combinations, product
from collections import defaultdict
from math import comb, factorial, prod


def odddouble(n):
    p = 1
    for i in range(1, n + 1, 2):
        p *= i
    return p


def matching_count(n, j):
    return n * comb(n - j, j) // (n - j) if j else 1


def R(k):
    return sum((-1)**j * matching_count(2*k, j) * odddouble(2*k-2*j-1)
               for j in range(k+1))


def graph(V, E):
    return tuple(V), frozenset(frozenset(e) for e in E)


def path(n):
    return graph(range(n), [(i, i+1) for i in range(n-1)])


def cycle(n):
    return graph(range(n), [(i, (i+1) % n) for i in range(n)])


def clique(n):
    return graph(range(n), combinations(range(n), 2))


def box(g, h):
    V, E = g
    W, F = h
    return graph(
        product(V, W),
        [((v, w), (x, w)) for e in E for v, x in [tuple(e)] for w in W] +
        [((v, w), (v, x)) for e in F for w, x in [tuple(e)] for v in V],
    )


def trace(g, m):
    """Directed-arc Hashimoto trace via sparse integer path dynamic programming."""
    V, E = g
    ne = {v: set() for v in V}
    for e in E:
        u, v = tuple(e)
        ne[u].add(v)
        ne[v].add(u)
    arc = [(u, v) for u in V for v in ne[u]]
    idx = {a: i for i, a in enumerate(arc)}
    succ = [[idx[(v, w)] for w in ne[v] if w != u] for u, v in arc]
    answer = 0
    for root in range(len(arc)):
        current = {root: 1}
        for _ in range(m):
            next_counts = defaultdict(int)
            for a, count in current.items():
                for b in succ[a]:
                    next_counts[b] += count
            current = next_counts
        answer += current.get(root, 0)
    return answer


def diff(f, factors):
    q = len(factors)
    value = 0
    for mask in range(1, 1 << q):
        included = [i for i in range(q) if (mask >> i) & 1]
        g = factors[included[0]]
        for i in included[1:]:
            g = box(g, factors[i])
        coef = (-1)**(q - len(included))
        for i in range(q):
            if i not in included:
                coef *= len(factors[i][0])
        value += coef * f(g)
    return value


def run():
    assert [R(k) for k in range(2, 8)] == [1, 4, 31, 293, 3326, 44189]
    beta = {k: (1 << k) * factorial(k) * R(k) for k in range(2, 8)}
    assert [beta[k] for k in range(2, 8)] == [
        8, 192, 11904, 1125120, 153262080, 28507207680
    ]
    for k in range(2, 8):
        print("coefficient", k, R(k), beta[k])

    fixtures = [
        ("P3,K3", [path(3), clique(3)]),
        ("P3,C4", [path(3), cycle(4)]),
        ("P3,K2,K3", [path(3), path(2), clique(3)]),
        ("P3,K2,C4", [path(3), path(2), cycle(4)]),
        ("P3,K2,K2,K3", [path(3), path(2), path(2), clique(3)]),
    ]
    for name, factors in fixtures:
        k = len(factors)
        expected = beta[k] * prod(len(g[1]) for g in factors)
        actual = diff(lambda g: trace(g, 2*k), factors)
        print("mixed", name, "actual", actual, "expected", expected)
        assert actual == expected

    for k, factors in [
        (2, [path(3), clique(3), path(2)]),
        (3, [path(2), path(3), clique(3), path(2)]),
    ]:
        actual = diff(lambda g: trace(g, 2*k), factors)
        print("upper-order", k, "actual", actual)
        assert actual == 0

    print("Independent finite replay PASS")


if __name__ == "__main__":
    run()

#!/usr/bin/env python3
"""Independent direct DFS of full-coordinate-support simple cycles in
mixed (non-hypercube) Cartesian products.

No flip-word/chord-diagram enumeration is used; adjacency is constructed
factor-by-factor. This exercises the claimed universality of the symbol
gamma_k * product(edge_count(factor)) rather than only its hypercube diagonal.
"""
from itertools import product
from math import factorial
from sys import argv


def adjacency_of_product(factors):
    vertices = list(product(*(range(n) for n, _ in factors)))
    idx = {v: i for i, v in enumerate(vertices)}
    adj = [[] for _ in vertices]
    for ix, v in enumerate(vertices):
        for axis, (n, edges) in enumerate(factors):
            for a, b in edges:
                if v[axis] in (a, b):
                    w = list(v)
                    w[axis] = b if v[axis] == a else a
                    adj[ix].append((idx[tuple(w)], axis))
    return adj


def full_support_cycles(factors):
    adj = adjacency_of_product(factors)
    k = len(factors)
    length = 2 * k
    count = 0

    def dfs(u, root, steps, seen, support):
        nonlocal count
        if steps == length - 1:
            for v, axis in adj[u]:
                if v == root and (support | (1 << axis)) == (1 << k) - 1:
                    count += 1
            return
        for v, axis in adj[u]:
            if not (seen >> v) & 1:
                dfs(v, root, steps + 1, seen | (1 << v), support | (1 << axis))

    for root in range(len(adj)):
        dfs(root, root, 0, 1 << root, 0)
    assert count % (4 * k) == 0
    return count // (4 * k)


K2 = (2, ((0, 1),))
K3 = (3, ((0, 1), (0, 2), (1, 2)))
P3 = (3, ((0, 1), (1, 2)))
a = [1, 1]
for k in range(2, 10):
    a.append((k - 1) * sum(a[i] * a[k - i] for i in range(1, k)))


def run(name, factors):
    k = len(factors)
    measured = full_support_cycles(factors)
    predicted = (2 ** (k - 2)) * factorial(k - 1) * a[k]
    for n, edges in factors:
        predicted *= len(edges)
    assert measured == predicted, (name, measured, predicted)
    print(f"PASS {name}: k={k}, full_supported_cycles={measured}")


def main():
    run("K2 x K2", (K2, K2))
    run("K3 x P3", (K3, P3))
    run("K3 x P3 x K2", (K3, P3, K2))
    run("P3 x K2 x K2 x K2", (P3, K2, K2, K2))
    if "--extended" in argv:
        run("K3 x K2 x K2 x K2 x K2", (K3, K2, K2, K2, K2))
    print("PASS: direct mixed-product graph DFS verifies gamma_k product(edge counts)")


if __name__ == "__main__":
    main()

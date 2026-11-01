#!/usr/bin/env python3
"""Exact, dependency-free audit of the P4 Cartesian-product law and its third jet.

Graphs are unlabeled isomorphism classes of simple undirected graphs on <=5
vertices, obtained by enumerating ALL labelled edge masks and minimizing over
all vertex permutations.  All arithmetic is integer-valued.  Python >=3.9.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, permutations
from math import prod


def graph_from_mask(n, mask):
    adj = [set() for _ in range(n)]
    for i, (u, v) in enumerate(combinations(range(n), 2)):
        if mask & (1 << i):
            adj[u].add(v)
            adj[v].add(u)
    return tuple(tuple(sorted(vs)) for vs in adj)


@lru_cache(None)
def permuted_edge_bit_positions(n):
    edges = tuple(combinations(range(n), 2))
    edge_ix = {e: i for i, e in enumerate(edges)}
    return tuple(tuple(edge_ix[tuple(sorted((perm[u], perm[v])))]
                       for u, v in edges)
                 for perm in permutations(range(n)))


def canonical_mask(n, mask):
    best = mask
    for bit_positions in permuted_edge_bit_positions(n):
        relabeled_mask = 0
        for i, j in enumerate(bit_positions):
            if mask & (1 << i):
                relabeled_mask |= 1 << j
        if relabeled_mask < best:
            best = relabeled_mask
    return best


def is_connected(G):
    if not G:
        return False
    reached = {0}
    queue = [0]
    for u in queue:
        for v in G[u]:
            if v not in reached:
                reached.add(v)
                queue.append(v)
    return len(reached) == len(G)


def all_unlabeled_through(max_n):
    graphs = []
    counts = {}
    for n in range(max_n + 1):
        representatives = set()
        for mask in range(1 << (n * (n - 1) // 2)):
            representatives.add(canonical_mask(n, mask))
        counts[n] = len(representatives)
        graphs.extend(graph_from_mask(n, mask) for mask in sorted(representatives))
    return graphs, counts


def cartesian(G, H):
    m, n = len(G), len(H)
    return tuple(tuple(sorted(
        [u * n + j for u in G[i]] + [i * n + k for k in H[j]]))
        for i in range(m) for j in range(n))


def edge_count(G):
    return sum(map(len, G)) // 2


def p3_count(G):
    return sum(len(ns) * (len(ns) - 1) // 2 for ns in G)


def triangle_count(G):
    return sum(1 for a, b, c in combinations(range(len(G)), 3)
               if b in G[a] and c in G[a] and c in G[b])


def p4_direct(G):
    # Counts injective oriented 3-edge walks; reverse orientation counts twice.
    oriented = 0
    for a, neighbors in enumerate(G):
        for b in neighbors:
            for c in G[b]:
                if c == a:
                    continue
                for d in G[c]:
                    if d != a and d != b:
                        oriented += 1
    assert oriented % 2 == 0
    return oriented // 2


def p4_edge_triangle(G):
    d = tuple(map(len, G))
    nonbacktracking = sum((d[u] - 1) * (d[v] - 1)
                          for u in range(len(G)) for v in G[u] if u < v)
    return nonbacktracking - 3 * triangle_count(G)


def p4_product_rhs(G, H):
    return (len(H) * p4_direct(G) + len(G) * p4_direct(H)
            + 6 * edge_count(H) * p3_count(G)
            + 6 * edge_count(G) * p3_count(H)
            + 4 * edge_count(G) * edge_count(H))


def cartesian_many(gs):
    result = ((),)  # adjacency of K1
    for G in gs:
        result = cartesian(result, G)
    return result


def epsilon_mixed_difference(gs):
    """Möbius-sum for D=P4, which has D(K1)=0."""
    k = len(gs)
    value = 0
    for mask in range(1 << k):
        selected = [gs[i] for i in range(k) if mask & (1 << i)]
        omitted_n = prod(len(gs[i]) for i in range(k) if not mask & (1 << i))
        value += (-1) ** (k - len(selected)) * p4_direct(cartesian_many(selected)) * omitted_n
    return value


def main():
    graphs, per_n = all_unlabeled_through(5)
    expected = {0: 1, 1: 1, 2: 2, 3: 4, 4: 11, 5: 34}
    assert per_n == expected, (per_n, expected)
    checked_single = 0
    for G in graphs:
        assert p4_direct(G) == p4_edge_triangle(G), (G, p4_direct(G), p4_edge_triangle(G))
        checked_single += 1
    checked_pairs = 0
    for G, H in combinations_with_replacement(graphs, 2):
        direct, predicted = p4_direct(cartesian(G, H)), p4_product_rhs(G, H)
        assert direct == predicted, (G, H, direct, predicted)
        checked_pairs += 1

    small_connected = [G for G in graphs if len(G) <= 4 and is_connected(G)]
    assert Counter(len(G) for G in small_connected) == {1: 1, 2: 1, 3: 2, 4: 6}
    checked_triples = 0
    for gs in combinations_with_replacement(small_connected, 3):
        got = epsilon_mixed_difference(gs)
        wanted = 24 * prod(edge_count(G) for G in gs)
        assert got == wanted, (gs, got, wanted)
        checked_triples += 1

    tiny_connected = [G for G in graphs if len(G) <= 3 and is_connected(G)]
    checked_fourth = 0
    for gs in combinations_with_replacement(tiny_connected, 4):
        assert epsilon_mixed_difference(gs) == 0, gs
        checked_fourth += 1

    k2 = graph_from_mask(2, 1)
    c4 = cartesian(k2, k2)
    q3 = cartesian(c4, k2)
    k3 = graph_from_mask(3, 7)
    prism = cartesian(k3, k2)
    print('Unlabeled counts at n=0,...,5:', per_n)
    print('Graph classes verified directly: ', checked_single)
    print('Unordered graph pairs checked:   ', checked_pairs)
    print('Connected triples checked (n<=4):', checked_triples)
    print('Connected fourth differences (n<=3):', checked_fourth)
    print('P4(C4) =', p4_direct(c4), '; P4(Q3) =', p4_direct(q3),
          '; P4(K3 square K2) =', p4_direct(prism))
    print('Third difference at (K2,K2,K2) =', epsilon_mixed_difference([k2]*3))
    print('All assertions passed.')


if __name__ == '__main__':
    main()
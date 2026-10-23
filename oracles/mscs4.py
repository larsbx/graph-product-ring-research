"""Exact non-induced, unrooted, unoriented four-direction C8 census.

CLI accepts JSON {"n": n, "edges": [[u,v], ...]} (integer bit vertices).
Enumeration visits each simple cycle only from its least vertex and in the
orientation with second vertex smaller than last; no symmetry division needed.
"""
import argparse
from fractions import Fraction
from itertools import combinations
import json
from math import comb


def cube_edges(n):
    return {(x, x ^ (1 << i)) for x in range(1 << n)
            for i in range(n) if not x & (1 << i)}


def validate(n, edges):
    if not isinstance(n, int) or isinstance(n, bool) or n < 0:
        raise ValueError('n must be a nonnegative integer')
    result = set()
    for u, v in edges:
        if any(not isinstance(x, int) or isinstance(x, bool) or not 0 <= x < 1 << n for x in (u, v)):
            raise ValueError('invalid vertex')
        d = u ^ v
        if not d or d & (d - 1):
            raise ValueError('edge must flip exactly one coordinate')
        result.add(tuple(sorted((u, v))))
    return result


def count(n, edges):
    edges = validate(n, edges)
    adj = [[] for _ in range(1 << n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    total = 0
    for start in range(1 << n):
        path = [start]
        seen = {start}
        def visit(v, support):
            nonlocal total
            if len(path) == 8:
                if start in adj[v] and path[1] < v and (support | (v ^ start)).bit_count() == 4:
                    total += 1
                return
            for w in adj[v]:
                mask = support | (v ^ w)
                if w <= start or w in seen or mask.bit_count() > 4:
                    continue
                # Remaining edges must be sufficient to return to start.
                if (w ^ start).bit_count() > 9 - len(path) - 1:
                    continue
                seen.add(w); path.append(w)
                visit(w, mask)
                path.pop(); seen.remove(w)
        visit(start, 0)
    return total


def auxiliary_cycles(n, edges):
    """Sum ordinary C4 counts in the wedge graphs H_x; independent lower test."""
    edges = validate(n, edges)
    def has(u, v):
        return tuple(sorted((u, v))) in edges
    total = 0
    for x in range(1 << n):
        adj = [set() for _ in range(n)]
        for i, j in combinations(range(n), 2):
            w = x ^ (1 << i) ^ (1 << j)
            if has(x ^ (1 << i), w) and has(x ^ (1 << j), w):
                adj[i].add(j); adj[j].add(i)
        total += sum(comb(len(adj[i] & adj[j]), 2) for i, j in combinations(range(n), 2)) // 2
    return total


def record(n, name, edges):
    edges = validate(n, edges)
    ambient = 648 * comb(n, 4) * 2 ** (n - 4) if n >= 4 else 0
    return dict(n=n, construction=name, edges=len(edges),
                edge_density=str(Fraction(len(edges), n * 2 ** (n-1))) if n else '0',
                M4=count(n, edges), ambient_M4=ambient,
                auxiliary_C4=auxiliary_cycles(n, edges))


def experiments():
    rows = []
    for n in range(4, 8):
        full = cube_edges(n)
        cases = {'full': full,
                 'even_lower_layer': {(u,v) for u,v in full if u.bit_count() % 2 == 0},
                 'middle_layer': {(u,v) for u,v in full if u.bit_count() == (n-1)//2},
                 'half_directions': {(u,v) for u,v in full if (u^v).bit_length() <= n//2},
                 'fixed_three_directions': {(u,v) for u,v in full if (u^v) < 8},
                 'parity_other_coordinates': {(u,v) for u,v in full if u.bit_count() % 2 == ((u^v).bit_length()-1) % 2}}
        rows.extend(record(n, name, edges) for name, edges in cases.items())
    return rows


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', nargs='?')
    args = parser.parse_args()
    if args.input:
        with open(args.input) as f:
            data = json.load(f)
        output = record(data['n'], 'input', data['edges'])
    else:
        output = experiments()
    print(json.dumps(output, indent=2))

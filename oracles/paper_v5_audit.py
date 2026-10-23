"""Fresh v5 audit: vertex DFS, explicit rotation orbits, prefix-XOR pairings.

No imports from existing repository tests/oracles. Run with Python 3.
"""
from itertools import product
from math import factorial, prod
import json


def pairings(items):
    if not items:
        yield ()
        return
    a, *tail = items
    for b in tail:
        for rest in pairings([x for x in tail if x != b]):
            yield ((a, b),) + rest


def coefficients(k):
    r = a = 0
    for pairs in pairings(list(range(2*k))):
        word = [0]*(2*k)
        for label, (i, j) in enumerate(pairs):
            word[i] = word[j] = label
        if any(word[i] == word[(i+1) % (2*k)] for i in range(2*k)):
            continue
        r += 1
        vertex = 0
        seen = {0}
        for label in word[:-1]:
            vertex ^= 1 << label
            if vertex in seen:
                break
            seen.add(vertex)
        else:
            a += 1
    scale = 2**k * factorial(k)
    return dict(k=k, R=r, A=a, beta=scale*r,
                primitive=scale*r//(2*k), gamma=scale*a//(4*k),
                eta=scale*(r-a)//(2*k))


def graph(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def box(factors):
    vertices = list(product(*(range(len(g)) for g in factors)))
    index = {v: i for i, v in enumerate(vertices)}
    adj = [set() for _ in vertices]
    for i, v in enumerate(vertices):
        for axis, g in enumerate(factors):
            for w in g[v[axis]]:
                dest = v[:axis] + (w,) + v[axis+1:]
                adj[i].add(index[dest])
    return adj


def counts(g, m):
    """Enumerate vertex sequences, checking closure and seam explicitly.

    Orbits retain direction. Periodicity tested on vertices, not labels:
    1212 has periodic labels but is a primitive square traversal.
    """
    rooted = 0
    primitive = set()
    simple = set()
    def rotation_key(seq):
        return min(seq[i:] + seq[:i] for i in range(len(seq)))
    def visit(seq):
        nonlocal rooted
        if len(seq) == m:
            if seq[0] not in g[seq[-1]] or seq[-2] == seq[0] or seq[-1] == seq[1]:
                return
            rooted += 1
            key = rotation_key(tuple(seq))
            if not any(m % r == 0 and tuple(seq) == tuple(seq[:r])*(m//r)
                       for r in range(1, m)):
                primitive.add(key)
            if len(set(seq)) == m:
                simple.add(min(key, rotation_key(tuple(reversed(seq)))))
            return
        for w in g[seq[-1]]:
            if len(seq) == 1 or w != seq[-2]:
                visit(seq + [w])
    for v in range(len(g)):
        visit([v])
    return rooted, len(primitive), len(simple)


def defect(factors, m):
    q = len(factors)
    result = [0, 0, 0]
    for mask in range(1 << q):
        subset = [g for i, g in enumerate(factors) if mask >> i & 1]
        weight = (-1)**(q-len(subset))*prod(len(g) for i, g in enumerate(factors)
                                                          if not (mask >> i & 1))
        value = counts(box(subset), m)
        for j in range(3):
            result[j] += weight*value[j]
    return result


def run():
    ledger = [coefficients(k) for k in range(2, 8)]
    assert [v['R'] for v in ledger] == [1, 4, 31, 293, 3326, 44189]
    assert [v['A'] for v in ledger] == [1, 4, 27, 248, 2830, 38232]
    p3 = graph(3, [(0, 1), (1, 2)])
    k2 = graph(2, [(0, 1)])
    k3 = graph(3, [(0, 1), (1, 2), (2, 0)])
    c4 = graph(4, [(0, 1), (1, 2), (2, 3), (3, 0)])
    isolated_edge = graph(3, [(0, 1)])
    fixtures = [('P3,K3', [p3, k3]), ('P3,K2,C4', [p3, k2, c4]),
                ('P3,K2,K2,K3', [p3, k2, k2, k3]),
                ('K2+K1,K3', [isolated_edge, k3]),
                ('empty,K3', [[], k3])]
    checks = []
    for name, factors in fixtures:
        k = len(factors)
        coeff = ledger[k-2]
        edges = prod(sum(map(len, g))//2 for g in factors)
        actual = defect(factors, 2*k)
        expected = [coeff[t]*edges for t in ('beta', 'primitive', 'gamma')]
        assert actual == expected, (name, actual, expected)
        checks.append(dict(factors=name, centered_b_p_c=actual))
    assert defect([p3, k2, k3], 4) == [0, 0, 0]
    assert counts(c4, 4) == (8, 2, 1)
    assert counts(c4, 8) == (8, 0, 0)
    # Two triangles sharing a vertex: primitive non-simple length-six walks.
    bowtie = graph(5, [(0,1),(1,2),(2,0),(0,3),(3,4),(4,0)])
    bow = counts(bowtie, 6)
    assert bow == (36, 4, 0), bow
    return dict(coefficients=ledger, mixed=checks, square4=[8,2,1],
                square8=[8,0,0], bowtie6=list(bow),
                upper_order_length4_three_factors=[0,0,0])


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))

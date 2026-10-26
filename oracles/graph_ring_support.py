"""Independent finite bridge replay: actual trajectories versus arc-matrix traces.

No imports from repository oracles. Exact integer arithmetic only. This is
bounded evidence, separate from Lean proofs and external acceptance.
"""
from collections import Counter
from itertools import product
from math import prod
import json


def graph(n, edges):
    g = [set() for _ in range(n)]
    for u, v in edges:
        assert u != v
        g[u].add(v)
        g[v].add(u)
    return g


def cartesian(factors):
    vertices = list(product(*(range(len(g)) for g in factors)))
    adjacent = {v: [] for v in vertices}
    for v in vertices:
        for a, g in enumerate(factors):
            for dest in g[v[a]]:
                w = v[:a] + (dest,) + v[a+1:]
                adjacent[v].append((w, a))
    return adjacent


def arc_trace(factors, m):
    """Sparse matrix trace on directed arcs, with no support annotations."""
    adj = cartesian(factors)
    arcs = [(v, w) for v in adj for w, _ in adj[v]]
    nxt = {(v, w): [(w, z) for z, _ in adj[w] if z != v] for v, w in arcs}
    total = 0
    for arc in arcs:
        state = {arc: 1}
        for _ in range(m):
            after = Counter()
            for a, c in state.items():
                for b in nxt[a]:
                    after[b] += c
            state = after
        total += state.get(arc, 0)
    return total


def trajectories(factors, m, seam=True):
    adj = cartesian(factors)
    for root in adj:
        def visit(path, word):
            if len(word) == m:
                if path[-1] == root and (not seam or path[-2] != path[1]):
                    yield tuple(path[:-1]), tuple(word)
                return
            for dest, axis in adj[path[-1]]:
                if len(path) < 2 or dest != path[-2]:
                    yield from visit(path+[dest], word+[axis])
        yield from visit([root], [])


def centered(factors, m):
    q = len(factors)
    return sum((-1)**len(removed) * prod(len(factors[a]) for a in removed)
               * arc_trace([g for a, g in enumerate(factors) if a not in removed], m)
               for mask in range(1 << q)
               for removed in [{a for a in range(q) if mask >> a & 1}])


def word_set(k):
    """Direct labeled-word enumeration, not matching or recurrence formulas."""
    return {w for w in product(range(k), repeat=2*k)
            if all(w.count(a) == 2 for a in range(k))
            and all(w[i] != w[(i+1) % (2*k)] for i in range(2*k))}


def check_case(name, factors, m):
    q = len(factors)
    walks = list(trajectories(factors, m))
    assert len(walks) == arc_trace(factors, m)
    full = [(p, w) for p, w in walks if len(set(w)) == q]
    defect = centered(factors, m)
    assert defect == len(full), (name, m, defect, len(full))
    for path, word in walks:
        assert 2*len(set(word)) <= m
        for a in set(word):
            assert word.count(a) >= 2
    recovery_count = None
    if m == 2*q and q >= 2:
        recovered = set()
        for path, word in full:
            oriented = []
            for a in range(q):
                steps = [i for i, axis in enumerate(word) if axis == a]
                assert len(steps) == 2
                i, j = steps
                u, v = path[i][a], path[(i+1) % m][a]
                assert v in factors[a][u]
                assert path[j][a] == v and path[(j+1) % m][a] == u
                assert {p[a] for p in path} == {u, v}
                start = path[0][a]
                other = v if start == u else u
                oriented.append((start, other))
            key = tuple(oriented), word
            assert key not in recovered  # no coordinate-witness overcount
            recovered.add(key)
            # Independently reconstruct the actual traversal from recovered data.
            state = [arc[0] for arc in oriented]
            restored = []
            for a in word:
                restored.append(tuple(state))
                u, v = oriented[a]
                state[a] = v if state[a] == u else u
            assert tuple(restored) == path and tuple(state) == path[0]
        arcs = [[(u, v) for u in range(len(g)) for v in sorted(g[u])] for g in factors]
        expected = {(tuple(a), w) for a in product(*arcs) for w in word_set(q)}
        assert recovered == expected  # surjection, including disconnected/empty cases
        recovery_count = len(recovered)
    return dict(case=name, length=m, rooted=len(walks), centered=defect,
                full_support=len(full), recovered_edge_word_tuples=recovery_count)


def run():
    k2 = graph(2, [(0,1)])
    p3 = graph(3, [(0,1),(1,2)])
    k3 = graph(3, [(0,1),(1,2),(2,0)])
    c4 = graph(4, [(0,1),(1,2),(2,3),(3,0)])
    irregular = graph(5, [(0,1),(1,2),(2,3),(3,0),(0,4)])
    disconnected = graph(6, [(0,1),(1,2),(2,3),(3,0),(4,5)])
    isolated = graph(3, [(0,1)])
    cases = [('P3,K3', [p3,k3], 4), ('irregular,K2', [irregular,k2], 4),
             ('disconnected,K2', [disconnected,k2], 4),
             ('K2+K1,P3,K3', [isolated,p3,k3], 6),
             ('empty,K3', [[],k3], 4), ('edgeless,K3', [graph(2,[]),k3], 4),
             ('P3,K2,K3-upper', [p3,k2,k3], 4),
             ('disconnected,K2-upper', [disconnected,k2], 3)]
    receipts = [check_case(*case) for case in cases]
    # Counterexample to dropping centered vertex weights: C4 x K2 = Q3.
    assert arc_trace([c4,k2], 4) == 48 and centered([c4,k2], 4) == 32
    # Counterexample to omitting the cyclic NB seam, at a leaf on a square.
    linear = len(list(trajectories([irregular], 6, seam=False)))
    cyclic = len(list(trajectories([irregular], 6)))
    assert linear > cyclic
    # Signed virtual factors exercise extension by multilinearity independently.
    def virtual_defect(virtuals, m):
        return sum(prod(c for c, _ in selection)
                   * centered([g for _, g in selection], m)
                   for selection in product(*virtuals))
    virtuals = [[(1,k2),(-2,p3)], [(1,k3),(-2,k2)]]
    edge_product = prod(sum(c * sum(map(len, g))//2 for c,g in terms)
                        for terms in virtuals)
    virtual_symbol = virtual_defect(virtuals, 4)
    assert virtual_symbol == 8*edge_product == -24
    virtual_upper = virtual_defect(virtuals + [[(1,k2),(-1,p3)]], 4)
    assert virtual_upper == 0
    return dict(cases=receipts,
                virtual_symbol=virtual_symbol, virtual_upper=virtual_upper,
                uncentered_counterexample=dict(rooted=48, centered=32),
                seam_counterexample=dict(linear_only=linear, cyclic=cyclic),
                status='bounded independent evidence; claim statuses unchanged')


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))

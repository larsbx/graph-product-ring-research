"""Independent, standard-library-only replay for the Lean finite component.

Restricted-growth word generation and involutive partner generation are separate
algorithms. Neither imports repository oracles or assumes the normalization.
"""
from itertools import product
from math import factorial
from pathlib import Path
import argparse
import json

ROOT = Path(__file__).resolve().parents[1]
VECTOR = ROOT / 'conformance/receipts/lean-word-vectors.json'


def words(k):
    def visit(w, counts):
        if len(w) == 2*k:
            if len(counts) == k and all(c == 2 for c in counts) and w[-1] != w[0]:
                yield tuple(w)
            return
        for a in range(min(len(counts)+1, k)):
            if w and a == w[-1]:
                continue
            if a == len(counts):
                yield from visit(w+[a], counts+[1])
            elif counts[a] < 2:
                cs = counts.copy()
                cs[a] += 1
                yield from visit(w+[a], cs)
    yield from visit([], [])


def matchings(k):
    def visit(partner):
        try:
            i = partner.index(-1)
        except ValueError:
            yield tuple(partner)
            return
        for j in range(i+1, 2*k):
            if partner[j] != -1 or j == i+1 or (i == 0 and j == 2*k-1):
                continue
            p = partner.copy()
            p[i], p[j] = j, i
            yield from visit(p)
    yield from visit([-1]*(2*k))


def partner(w):
    return tuple(next(j for j, b in enumerate(w) if b == a and j != i)
                 for i, a in enumerate(w))


def vertices(w, start=0):
    v = [start]
    for a in w:
        v.append(v[-1] ^ (1 << a))
    assert v[-1] == start
    return tuple(v[:-1])


def rotations(v):
    return {v[i:]+v[:i] for i in range(len(v))}


def run():
    rows = []
    for k, expected_r, expected_a in [(2,1,1), (3,4,4), (4,31,27), (5,293,248)]:
        ws = sorted(words(k))
        ps = set(matchings(k))
        assert len(ws) == expected_r
        assert {partner(w) for w in ws} == ps
        assert len(ps) == expected_r
        simple = sum(len(set(vertices(w))) == 2*k for w in ws)
        assert simple == expected_a
        # Independently enumerate all labeled words through k=4, rather than
        # manufacturing them by multiplying the matching cardinal by k!.
        if k <= 4:
            labeled = []
            for w in product(range(k), repeat=2*k):
                if all(w.count(a) == 2 for a in range(k)) and all(
                    w[i] != w[(i+1) % (2*k)] for i in range(2*k)):
                    labeled.append(w)
            assert len(labeled) == factorial(k)*expected_r
            rooted = {vertices(w, s) for w in labeled for s in range(1 << k)}
            assert len(rooted) == 2**k * len(labeled)
            primitive_classes = {min(rotations(v)) for v in rooted}
            assert all(len(rotations(v)) == 2*k for v in rooted)
            simple_rooted = {v for v in rooted if len(set(v)) == 2*k}
            unoriented = {min(rotations(v) | rotations(v[::-1])) for v in simple_rooted}
            assert len(rooted) == 2*k*len(primitive_classes)
            assert len(simple_rooted) == 4*k*len(unoriented)
        rows.append(dict(k=k, R=len(ps), A=simple, beta=2**k*factorial(k)*len(ps),
                         canonical_words=["".join(map(str, w)) for w in ws]))
    square = (0,1,0,1)
    assert square[:2]*2 == square
    assert len(rotations(vertices(square))) == 4
    nonsimple = (0,1,0,1,2,3,2,3)
    assert len(set(vertices(nonsimple))) < 8
    assert len(rotations(vertices(nonsimple))) == 8
    seam = (0,1,2,1,2,0)
    assert all(seam[i] != seam[i+1] for i in range(5)) and seam[-1] == seam[0]
    return dict(schema=1, scope='finite indexed words; no graph-ring acceptance',
                rows=rows, regressions=dict(square=list(square),
                primitive_nonsimple=list(nonsimple), seam_rejected=list(seam)))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = run()
    if args.write:
        VECTOR.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(VECTOR.read_text()) == result, 'stale or altered vectors'
    print('finite Lean companion vectors and independent orbit replay: PASS')

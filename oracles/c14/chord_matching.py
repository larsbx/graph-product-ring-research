#!/usr/bin/env python3
"""Independent oracle C: intersection-graph connectivity of chord matchings.

This never constructs a cube vertex or enumerates graph cycles. For each
pairing of 14 points on a circle it counts the diagram iff the graph whose
vertices are chords and whose edges join crossing chords is connected.
Every pairing corresponds to a canonical double-occurrence flip word.
"""

def connected(pairs):
    n = len(pairs)
    seen = {0}
    stack=[0]
    while stack:
        i=stack.pop()
        a,b=pairs[i]
        for j,(c,d) in enumerate(pairs):
            if j in seen: continue
            cross = (a<c<b<d) or (c<a<d<b)
            if cross:
                seen.add(j);stack.append(j)
    return len(seen)==n

counts={}
def recur(unpaired,pairs):
    if not unpaired:
        n=len(pairs)
        total,conn=counts.get(n,(0,0))
        counts[n]=(total+1,conn+int(connected(pairs)))
        return
    first=unpaired[0]
    for j in range(1,len(unpaired)):
        second=unpaired[j]
        recur(unpaired[1:j]+unpaired[j+1:], pairs+[(first,second)])

for n in range(2,8):
    recur(list(range(2*n)),[])
    total,conn=counts[n]
    print(f'k={n} perfect_matchings={(total):,} connected_chord_diagrams={conn:,}')
assert [counts[k][1] for k in range(2,8)]==[1,4,27,248,2830,38232]
print('PASS: independent chord-intersection connectivity')

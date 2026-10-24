#!/usr/bin/env python3
"""Exhaustively check crossing-connectivity iff no repeated cube-prefix on
all 135,135 matchings of 14 positions (independent predicates).
"""
from chord_matching import connected

checked=0
agree=0
mismatches=[]
def simple_by_prefix(pairs):
    label=[-1]*14
    for k,(a,b) in enumerate(pairs):
        label[a]=k; label[b]=k
    x=0; seen={0}
    for t in range(14):
        x^=1<<label[t]
        if t<13:
            if x in seen:return False
            seen.add(x)
    return x==0

def dfs(open_positions, pairs):
    global checked,agree
    if not open_positions:
        a=connected(pairs); b=simple_by_prefix(pairs)
        checked+=1
        if a==b:agree+=1
        elif len(mismatches)<4:mismatches.append((pairs,a,b))
        return
    p=open_positions[0]
    for i in range(1,len(open_positions)):
        dfs(open_positions[1:i]+open_positions[i+1:],pairs+[(p,open_positions[i])])

dfs(list(range(14)),[])
print('matchings',checked,'agreements',agree,'mismatches',mismatches)
assert checked==agree==135135
print('PASS: chord connectivity iff 14-cycle simple prefix')

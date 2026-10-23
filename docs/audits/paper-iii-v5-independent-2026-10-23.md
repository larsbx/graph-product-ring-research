# Independent mathematical audit of Paper III v5

Audited base: `392a7740ca5b68109c73986a6acd1a14b4d9f8f7` (merged PR #24).
Scope: a new AI-assisted mathematical inspection and independently written
finite replay, not external mathematical acceptance, formal verification,
publication acceptance, or a prior-art decision. All registry claims remain
**working**; issue #22 remains open.

## Verdict and correction

No counterexample or missing bipartite/regularity restriction was found in
the all-order support argument under its stated finite simple undirected
graph and centered augmentation conventions. The argument below establishes
why the full-ring extension follows from the combinatorics; finite tests
alone would not establish it.

One notation correction is needed: the draft defines a principal symbol at
exact order, but writes sigma_k(Delta_k) even when eta_k=0. Use the always
defined centered defect D_k Delta_k in the aggregate statement, with order
at most k. For k=2,3 there is no nonzero degree-k principal symbol. This
does not alter any coefficient or assert that the whole deficit vanishes.
The manuscript, support note, and claim statement are synchronized here.

## Centering and passage to the entire ring

The graph monoid under disjoint union is free on connected graph classes;
its additive completion consists of finite integer linear combinations.
If x=sum n_G G has epsilon(x)=0, then x=sum n_G u_G. Thus the u_G really
generate I additively, without a polynomial-ring or Cartesian unique-prime
factorization assumption. Products of q such generators additively span
I^q. This includes virtual graphs and disconnected factors, not only
positive connected products. Multilinearity is sufficient for extension.
Moreover u_(GH)=epsilon(G)u_H+epsilon(H)u_G+u_G u_H. For an
order-at-most-k invariant, substituting this into D_k kills the last
term in I^(k+1), proving the derivation rule in each argument. The
computed form really is a global tensor of epsilon-derivations.

Expand a product of centered factors over subsets T. Its scalar is
(-1)^(q-|T|) times the product of vertex counts outside T. In the full
Cartesian product these count exactly all fixed-coordinate fibers. A
particular walk with used set S consequently receives coefficient
sum_{T containing S}(-1)^(q-|T|), which is 1 precisely at full support.
An empty factor makes both sides zero. Isolated vertices need no special
assumption. For an invariant with nonzero value at K1 the empty-index term
must be retained; b_m, p_m, and the cycle counts here all vanish there.
In particular, the argument must not be transferred uncentered to tr(Q),
whose value at K1 is -1.

Each product step changes one coordinate. After deleting stationary steps,
a used projection is a nonconstant closed walk in a loopless graph and
has at least two traversals. Therefore 2|S|<=m for arbitrary factors,
including those with triangles. No projection is required to be NB.
Full-support defects vanish above floor(m/2); the preceding additive
generation argument proves actual ideal-power vanishing globally.

## Maximal-support bijection and cyclic seam

At length 2k in k used coordinates, every projection has exactly two
traversals. In a simple undirected graph these traverse the same unique
edge out and back. Recovering this edge in every factor is canonical.
There are product_i d(G_i) edge tuples, 2^k starting endpoint choices,
and |W_k| words of coordinate changes. This is a bijection, not merely
an injection or a count obtained by evaluation on cubes.

At maximal support only, consecutive equal labels are exactly inverse
edges; this equivalence includes the last/first seam. It is false as a
general statement about arbitrary factor walks with more than two steps
in a coordinate, but the proof does not use it there. Fiber inclusion
preserves the actual edge reversal condition at every seam.

Pairings have fixed indexed positions 0,...,2k-1. They are NOT quotiented
by rotation. Labelling their k blocks supplies k! words, with no hidden
stabilizer division. A trace term of B^m is an indexed closed arc sequence
of m transitions, equivalently a rooted vertex traversal of m edges.
This identification introduces neither an extra m nor a factor two.
Hence D_k b_(2k)=2^k k! R_k product_i d(G_i). The explicit word
1,...,k,1,...,k supplies positivity at all k>=2, including the seam.
Evaluation on k copies of K2 makes the ideal order exact.

Loops would invalidate the support bound; parallel edges would invalidate
the one-undirected-edge recovery argument. These objects are excluded.
There is no implicit infinite-product or completion step: every element
and every ideal-power expression uses finitely many graph classes.

## Primitive classes, reversal and simple cycles

Every actual cyclic arc sequence has a unique least period r. Its
primitive class contributes r distinct roots to b_m for each multiple m
of r, rather than m roots. Thus b_m=sum_{r|m} r p_r, and Mobius inversion
has denominator m. Proper divisors have order below k at m=2k, so they
do not contribute to D_k. Rational inversion causes no integrality gap:
the graph-by-graph orbit count is integral, and Z has no torsion.

A maximal-support 2k traversal cannot be a proper power. Any repetition
number divides the two occurrences in every coordinate, hence would have
to be two, but its closed half would use every coordinate once. That is
impossible. Consequently division by 2k acts freely on actual rooted
traversals. Coordinate-word periodicity is NOT actual walk periodicity:
1212 is a primitive square because the halfway vertex differs from its
start. The new replay explicitly tests periods of vertex sequences.

For simple cycles, equality of two prefix vertices is equivalent to the
intervening flips being whole pairs. A wrapping proper closed interval
exists exactly when its nonwrapping complement is closed, so checking
linear proper intervals suffices. Dividing simple rooted traversals by
2*(2k) accounts for rotations and both orientations. Primitive counts
retain orientation, hence the deficit subtracts 2c_(2k), not c_(2k).

## Reproducible independent finite evidence

Run `python3 oracles/paper_v5_audit.py`. No existing repository module is
imported. The new code enumerates perfect matchings, checks adjacent
pair avoidance and prefix-XOR vertex injectivity, and separately performs
vertex DFS on actual graph products. Primitive and simple classes use
explicit rotation/reversal orbit sets, without Mobius inversion or an
arc-matrix trace. Receipt: `conformance/receipts/paper-v5-audit.json`.

| k | R_k | A_k | beta_k | oriented primitive | gamma_k | eta_k |
|---|---:|---:|---:|---:|---:|---:|
|2|1|1|8|2|1|0|
|3|4|4|192|32|16|0|
|4|31|27|11904|1488|648|192|
|5|293|248|1125120|112512|47616|17280|
|6|3326|2830|153262080|12771840|5433600|1904640|
|7|44189|38232|28507207680|2036229120|880865280|274498560|

The matching enumeration includes all 135135 perfect matchings at k=7;
its simplicity test uses prefix vertices rather than interval closure.

| Factors | length | D_k b | D_k p | D_k c |
|---|---:|---:|---:|---:|
|P3,K3|4|48|12|6|
|P3,K2,C4|6|1536|256|128|
|P3,K2,K2,K3|8|71424|8928|3888|
|K2 disjoint union K1,K3|4|24|6|3|
|empty graph,K3|4|0|0|0|

The length-four three-factor defect on P3,K2,K3 vanishes for all three
invariants. A square at lengths four/eight has (b,p,c)=(8,2,1)/(8,0,0),
checking root periodicity and orientation. Two triangles sharing a vertex
give (b6,p6,c6)=(36,4,0): Delta_3 is nonzero on the full ring even though
its degree-three defect vanishes. This guards against overinterpreting
the zero coefficient. The existing 20-test suite also passes.

The all-order argument is finite combinatorics for each arbitrary k plus
additive generation, not extrapolation from this table. General junction
multiplicities, historical trace-induction repair, external acceptance,
and N6 novelty/prior-art requirements remain separate unresolved gates.

## Total C14 replay using the existing independent cube DFS

Separately compiled and ran the existing adjacency-based C++ oracle:

```sh
g++ -O3 -std=c++17 oracles/labelled_cube_cycles.cpp -o /tmp/gpr-cube-audit
/tmp/gpr-cube-audit 7 14
```

It returns support contributions 1505280, 386265600, 2068577280,
880865280 for supports 4,5,6,7, totaling **3337213440**. This is a
rerun of an existing implementation, not a newly written second total-C14
oracle. The new pairing replay independently verifies its maximal-support
contribution. Raw output: `conformance/receipts/paper-v5-c14-audit.txt`.

The revised TeX compiles with pdfLaTeX (three passes, five pages). The
claim registry parses as TOML and retains every prior status.

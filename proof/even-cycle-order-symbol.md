# Ordinary even cycles: support, augmented order, and principal symbol

Proof record, 2026-10-22. Repository mathematical derivation; not a recovered
manuscript. Acceptance/novelty review and manuscript synchronization remain
separate from the proofs below.

## 1. Exact conventions

All graphs are finite, undirected, and simple. Copies are ordinary, not
necessarily induced subgraphs. For connected H with at least one edge let
N_H(G)=inj(H,G)/|Aut(H)|, where inj means injective edge-preserving vertex
maps; nonedges need not be preserved. This counts copies with their selected
edge sets. In particular c_m=N_{C_m}, for m>=3, and |Aut(C_m)|=2m.

Let A be the Grothendieck ring of finite graphs with disjoint-union addition,
Cartesian multiplication, and unit 1=K1. The character epsilon(G)=|V(G)|
extends to A. Connectedness makes N_H additive, so it extends Z-linearly to
f:A->Z; f(1)=0. Put I=ker(epsilon). Regard Z as an A-module via epsilon.

For a in A define (delta_a f)(x)=f(ax)-epsilon(a)f(x).
Order at most r means delta_{a_0}...delta_{a_r}f=0 as a map on A for all
arguments. Equivalently f(I^{r+1})=0: delta_a amounts to multiplication by
u_a=a-epsilon(a)1, and I is generated additively by the u_G for actual graphs
G. Indeed any x=sum n_G G in I satisfies x=sum n_G u_G. Since I is an
ideal, testing the products of r+1 generators suffices even with a final x.
Order is the **least vanishing threshold**, not the smallest nonzero symbol.

For q>=1 define

D_q f(a_1,...,a_q)=f(product_i u_{a_i})
 = sum_{S subset [q]} (-1)^{q-|S|}
   (product_{i notin S} epsilon(a_i)) f(product_{i in S} a_i).

For order <=r, the principal symbol is sigma_r(f)=D_r f. It is a symmetric
Z-multilinear form, a derivation at epsilon in each slot: use
u_{ab}=epsilon(a)u_b+epsilon(b)u_a+u_a u_b; the final term lies in I^{r+1}
after multiplying by the other r-1 slots. This fixes the symbol normalization
without factorial division. Also
(delta_{a_1}...delta_{a_{q-1}} f)(a_q)=D_q f +
epsilon(a_q)D_{q-1} f, so the uncentered evaluation is NOT generally D_q.
For q=1 the corresponding identity is f(a)=D_1 f+epsilon(a)f(1).

## 2. Support-defect theorem

**Theorem 1.** D_q N_H(G_1,...,G_q) equals the number of H-copies in the
Cartesian product whose projection on every factor is nonconstant.

**Proof.** For S subset [q], copies constant on all coordinates outside S
are counted by (product_{i notin S}|V(G_i)|) N_H(product_{i in S}G_i).
A copy has a unique used-coordinate set T. It occurs in this expression
precisely when T subset S, once with its actual fixed coordinates. Its
coefficient in D_q is sum_{S superset T}(-1)^{q-|S|}, equal to one if
T=[q] and zero otherwise. The S=empty term is zero since H has an edge.
This proves the identity for copies, or first for injective maps and then
after division by Aut(H). Empty or disconnected factors cause no problem.
The identity concerns actual graphs; on virtual graphs it extends by
multilinearity, without asserting positivity there. QED.

Define r*(H) as the greatest number of nonconstant projections in an
injective edge-preserving embedding of H into a finite Cartesian product.
It is finite: each used coordinate labels some edge of H, so r*<=|E(H)|.
For H with an edge it is at least one, using H itself as a factor.

**Corollary 2.** ord_epsilon(N_H)=r*(H).

**Proof.** No product with r*+1 factors has a full-support copy; Theorem 1
and the additive generation of I imply f(I^{r*+1})=0. An embedding attaining
r* supplies actual factors with D_{r*}f>0, hence f(I^{r*}) is nonzero.
These give the upper and lower bounds under the order definition above. QED.

## 3. Even-cycle theorem on the full graph ring

Let d(G)=|E(G)|, extended additively. The Cartesian edge partition proves
d(G square H)=d(G)epsilon(H)+epsilon(G)d(H), so d is an epsilon-derivation.
For k>=2 set

a_k = # pair partitions of {1,...,2k} with no nonempty proper interval
      {i+1,...,j} (0<=i<j<=2k, j-i<2k) that is a union of pairs,
gamma_k = 2^k k! a_k / (4k).

**Theorem 3.** For ordinary simple cycles on the full ring A,

ord_epsilon(c_{2k})=k,
sigma_k(c_{2k})=gamma_k d^{tensor k}.

Here gamma_k is the integer full-support c_{2k}(Q_k) count. The statement
requires neither bipartite factors nor a restriction to a generated subring.

**Proof (upper order bound).** Every product edge changes exactly one
coordinate. The projection of a closed cycle on a used coordinate is a
nonconstant closed walk in a simple loopless graph. It cannot have length
one, so it uses at least two edges. A 2k-cycle therefore uses at most k
coordinates. Theorem 1 implies c_{2k}(I^{k+1})=0.

**Proof (top support classification).** In a full-support copy in k factors,
each coordinate changes exactly twice. A two-step closed walk in a simple
graph goes across one undirected edge and returns across the same edge.
Thus the copy determines one edge e_i in each G_i. Conversely, selecting
these edges gives a subgraph product isomorphic to Q_k. The cycle is a
full-support cube cycle in that product. Distinct edge selections cannot
count the same copy, since each projected edge is recovered from the cycle.
Extra edges of the factors impose no restrictions for ordinary subgraphs.
Consequently

D_k c_{2k}(G_1,...,G_k)=c_{2k}^{full}(Q_k) product_i |E(G_i)|.

This extends to A in each slot. It is the asserted pure principal symbol
once the constant and nonvanishing have been identified.

**Proof (constant and exactness).** A traversal from zero in Q_k using all k
coordinates in 2k steps uses each exactly twice. Identifying equal-coordinate
positions gives a pair partition. Canonical naming by first appearance gives
a bijection from pair partitions to canonical flip words. Two vertices at
times i<j coincide exactly when each coordinate occurs an even number of
times in that interval. With two occurrences per coordinate, this says the
interval is a union of whole pairs. Excluding all nonempty proper intervals
is therefore exactly the simple-cycle condition, including premature returns
to zero. Thus the canonical words number a_k.

There are k! labelled words for each canonical word, 2^k choices of starting
vertex, and 4k rooted directed traversals of every unoriented unrooted
2k-cycle. Hence c_{2k}^{full}(Q_k)=gamma_k. This also proves integrality of
the displayed quotient. The word 1,2,...,k,1,2,...,k has no repeated vertices
before its final return for k>=2 (its intermediate supports are distinct
prefixes followed by distinct nonempty proper suffixes). Thus gamma_k>0.
As d(K2)=1, D_k c_{2k}(K2,...,K2)>0, proving order at least k. QED.

## 4. Exact coefficients and the corrected c14 conclusion

Pair-partition enumeration (independent of the coordinate DFS) and the
checked-in cube paths give:

| k | a_k | gamma_k |
|---|---:|---:|
| 2 | 1 | 1 |
| 3 | 4 | 16 |
| 4 | 27 | 648 |
| 5 | 248 | 47,616 |
| 6 | 2,830 | 5,433,600 |
| 7 | 38,232 | 880,865,280 |

Thus c8 has order four with sigma_4(c8)=648 d^{tensor4}, and c14 has order
seven with sigma_7(c14)=880865280 d^{tensor7}, under precisely the conventions
above. This is a structural proof of purity and the upper bound, rather than
an inference from one diagonal evaluation. Numerical evaluation of a_7 is a
finite computation, cross-checked by perfect matchings and the two prior
cube enumerators; the all-k theorem keeps its exact finite combinatorial
formula and does not extrapolate the table.

## 5. Scope and remaining gates

The theorem is for ordinary non-induced counts on simple undirected graphs.
Induced copies, loops, directed graphs, and noninjective closed walks are not
covered. General connected-pattern order follows from Theorem 1, but other
patterns need not have a pure power of d as top symbol. No claim of novelty
or closed-form recurrence for a_k is made here.

Full c8 lower-order product corrections, exact imported theorem-label
reconciliation, external mathematical review, and literature comparison
remain separate tasks. The registry records this derivation as working
pending those acceptance steps, without promoting unrelated claims.

The #2 / PR #11 source-provenance gate remains: no v22 TeX is reconstructed,
v21 is not substituted, and no authoritative PDF/TeX bytes are replaced.
Paper III's lineage must be recovered before applying these corrections to
publication source. This proof record supersedes the earlier *conditional*
repository interpretation of the positive c14 coefficient, not historical
manuscript bytes.

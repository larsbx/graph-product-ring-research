# All-length ordinary even-cycle principal symbol — proof candidate (2026-10-22)

**Status:** **working proof note**, not yet promoted to `proved`. Depends on the exact graph-ring differential convention and the source provenance gate in issue #2. Independently executed finite checks are on draft PR #15. The connected-chord-diagram sequence and recurrence are prior art; no originality claim is made for them. New independent local C++ proof-obligation oracle checks **every perfect matching of 16 positions** (2,027,025 diagrams) and finds zero differences between chord-intersection connectivity and cube-prefix simplicity through k=8 (see oracles/c2k/verify_chord_prefix_all8.cpp).

## Statement

Let \(c_{2k}(G)\) be the number of **ordinary, non-induced, unoriented, unrooted** simple \(2k\)-cycle subgraphs of a finite simple graph \(G\), for \(k\ge2\). Let \(\varepsilon(G)=|V(G)|\), \(d(G)=|E(G)|\), and use exactly the centered augmentation-ideal convention of [PR #14](../../proof/even-cycle-order-symbol.md): put \(u_G=G-\varepsilon(G)1\), \(I=\ker\varepsilon\), and \(D_qf(G_1,\ldots,G_q)=f(\prod_i u_{G_i})\). Order at most r means \(f(I^{r+1})=0\); the principal symbol is \(D_r f\), with no factorial division. Authoritative manuscript indexing remains a separate provenance gate.

Write \(a_k\) for the number of **connected chord diagrams** with \(k\) chords, i.e. matchings of \(2k\) cyclically ordered marked points with connected chord-intersection graph (OEIS A000699).

> **Candidate theorem.** On the full Cartesian graph ring,
>
> \[
> \operatorname{ord}_\varepsilon(c_{2k})=k,\qquad
> \sigma_k(c_{2k})(G_1,\ldots,G_k)
> =2^{k-2}(k-1)!\,a_k\,\prod_{i=1}^k d(G_i)
> \quad(k\ge2).
> \]
>
> In particular \(\sigma_k(c_{2k})=\gamma_k d^{\otimes k}\) with
> \(\gamma_k=2^{k-2}(k-1)!a_k>0\) **for every** \(k\ge2\).

**Normalization:** if counting injective labeled maps \(C_{2k}\to G\) instead, multiply both \(c_{2k}\) and the symbol by \(|\mathrm{Aut}(C_{2k})|=4k\). Never mix this normalization with a value tabulated for unoriented cycle subgraphs.

## Inputs already established in PR #14

Theorems 1 and 3 of [the merged proof](../../proof/even-cycle-order-symbol.md)
establish that D_q N_F counts full-coordinate-support copies, a 2k-cycle
uses at most k coordinates, and each maximal-support copy determines a
unique selected edge in each factor. They give order k and

\[
\sigma_k(c_{2k})=\frac{2^k k! b_k}{4k}d^{\otimes k},
\]

where b_k counts pair partitions of the fixed positions 1,...,2k with no
nonempty proper **linear** pairing-closed interval. We reuse those results;
no new support-defect calculation is needed. The new combinatorial statement
below identifies b_k with the connected-chord count a_k.

In particular do not substitute an uncentered iterated delta evaluation:
PR #14 shows it has an additional epsilon times lower-defect term.

## Paired flip words and chord diagrams

Inside \(Q_k\), an oriented, vertex-rooted \(2k\)-cycle that changes all \(k\) coordinates is given by:

1. a chosen starting vertex (there are \(2^k\));
2. a sequence of \(2k\) coordinate flips, each of \(k\) named coordinates occurring exactly twice.

After forgetting the names of the coordinates, each such flip sequence is a perfect matching of the \(2k\) **ordered positions**; conversely the \(k!\) names can be assigned to its pairs.

Let \(s_t\in(\mathbb F_2)^k\) be the vector of parity counts among the first \(t\) flips. The cycle is simple iff \(s_a\ne s_b\) for all \(0\le a<b<2k\). Equality means exactly that some nonempty proper (linear, equivalently cyclic) interval of flip positions contains **both or neither endpoints of every chord**.

### Component-and-gap theorem (all k >= 2)

Positions are distinct fixed marked points on an oriented circle, indexed
modulo n=2k. A cyclic interval is a set of consecutive positions of length
1,...,n-1. It is pairing-closed if each pair has either zero or two
endpoints in it. Chords cross precisely when their endpoints alternate in
cyclic order; touching is impossible for a perfect matching.

**Theorem.** A matching has connected crossing graph if and only if it has
no nonempty proper pairing-closed cyclic interval.

**Proof, interval implies disconnection.** Let J be such an interval.
Pairing closure partitions the chords into those with both endpoints in J
and those with both endpoints in its complement. Both groups are nonempty:
each nonempty closed set contains at least one whole pair. Endpoints of a
chord from one group cannot alternate with endpoints of a chord from the
other, because J and its complement are consecutive arcs. There are no
crossing edges between these two nonempty groups.

**Proof, disconnection implies interval.** Choose any connected component C
of a disconnected crossing graph. C is nonempty and proper. Fix a chord e
outside C. Its endpoints divide the circle minus those endpoints into two
open arcs. Since e crosses no chord in C, each chord of C has both endpoints
in one of these arcs. Chords contained in different arcs cannot cross each
other. Connectedness of C therefore forces all its chords into the same
arc (also valid when C consists of a single chord). Thus the other open arc
contains no endpoint of C. Together with the two endpoints of e it is a
connected subset of the circle minus the endpoints of C. Consequently both
endpoints of e lie in the same open gap between consecutive endpoints of C.

This conclusion holds for **every** chord outside C. Select any such chord
and let J be the set of marked positions in its gap. J is nonempty, contains
no endpoint of C, and is proper because C has endpoints. Every position in J
belongs to a chord outside C, whose other endpoint lies in that same gap by
the preceding conclusion. Hence J is pairing-closed, as required. QED.

**Cyclic versus linear indexing.** The complement of a proper nonempty
cyclic pairing-closed interval is again proper, nonempty, and pairing-closed.
If the interval wraps across the cut between n and 1, its complement does
not. Thus existence of a cyclic interval is equivalent to existence of a
linear interval {i+1,...,j} with 0 <= i < j <= n and j-i < n, exactly the
criterion in PR #14. No rotation quotient is being taken.

**Prefix indexing.** For 0 <= i < j <= n, parity prefixes coincide precisely
when positions i+1,...,j are pairing-closed. If j=n and i>0, the complementary
prefix 1,...,i is closed, yielding a repetition among times 0,...,n-1.
The case (i,j)=(0,n) is the allowed final return. Hence excluding proper
closed intervals is exactly distinctness of the n pre-final vertices.
This proves b_k=a_k for every k>=2.

**Boundary cases.** For k=2, only the alternating matching is connected,
and it gives the square. Single-chord components and gaps spanning the
index cut are included in the proof. Closed intervals have even size at
least two, and so do their complements. For k=1 the combinatorial equivalence
still holds under the usual singleton-connected convention, but the flip
walk traverses one edge twice and is not an ordinary simple cycle: the graph
symbol formula is restricted to k>=2. The empty matching is excluded; a_0=1
below is only a recurrence convention. Diagrams are counted on **fixed ordered
positions**, not modulo rotation, reflection, or graph isomorphism.

An explicit positive witness for every \(k\ge2\) is the word
\(1,2,\ldots,k,1,2,\ldots,k\); the corresponding chord diagram has all chords crossing.

## Proof of the candidate theorem

The component-and-gap theorem identifies the pairing coefficient in PR #14
with a_k. Substitution into its already established ordinary-cycle formula
immediately gives

\[
\gamma_k=\frac{2^k k! a_k}{4k}=2^{k-2}(k-1)!a_k.
\]

For clarity, the factors are 2^k starting vertices, k! assignments of coordinate
names to the pairs, and 4k rooted directed traversals per ordinary unrooted
unoriented cycle. No additional dihedral quotient of a_k is allowed. This
matches PR #14 exactly, including gamma_2=1, gamma_4=648 and
gamma_7=880,865,280. Positivity and exact order k are already proved there.
The combinatorial proof here is self-contained; the graph-ring corollary
uses the explicitly cited merged theorem rather than duplicating it.

## Exact coefficients / consequences

| k | a_k (OEIS A000699) | gamma_k = 2^(k-2)(k-1)!a_k | status |
|--:|--:|--:|---|
| 2 | 1 | 1 | known / checked |
| 3 | 4 | 16 | known / checked |
| 4 | 27 | 648 | merged PR #14 / checked |
| 5 | 248 | 47,616 | merged PR #14 / checked |
| 6 | 2,830 | 5,433,600 | merged PR #14 / checked |
| 7 | 38,232 | **880,865,280** | two independent cycle oracles + chord matching / checked in PR #15 |
| 8 | 593,859 | **191,555,159,040** | analytic prediction; chord/prefix bijection checked independently on all 2,027,025 eight-chord matchings; no Q8 cycle enumeration |
| 9 | 10,401,712 | **53,682,819,563,520** | analytic prediction |
| 10 | 202,601,898 | **18,821,165,247,037,440** | analytic prediction |

The original Paper III table's \(c_{14}(Q_7)=406,517,760\) and \(\gamma_7=-2,049,830,400\) are contradicted. Independent exact enumeration in PR #15 gives \(c_{14}(Q_7)=3,337,213,440\) and \(\gamma_7=+880,865,280\).

The connected-chord recurrence
\(a_0=a_1=1\) and \(a_k=(k-1)\sum_{i=1}^{k-1}a_i a_{k-i}\)
is **established prior art**, not a project result: https://oeis.org/A000699 . The proposed novelty is only the precise graph-ring **full-support-symbol identification**, subject to a targeted comparison with product-graph cycle enumeration.

## Acceptance checklist

- [x] Independently scrutinize the all-k implication: the component-and-gap proof above supplies both directions and boundary cases. Separate acceptance review remains required. Exhaustive predicate agreement now checked independently through k=8 (2,027,025 matchings; zero mismatches), but a finite test does not replace a proof.
- [x] Confirm k=7 by two independent cycle enumerators and a 135,135-case chord/cube bijection check (PR #15).
- [ ] Replay with a properly installed Mojo SDK; the draft Mojo source in PR #15 remains **unexecuted** until its workflow succeeds.
- [x] Reconcile coefficient and centered-symbol normalization with merged PR #14.
- [ ] Reconcile authoritative manuscript notation and `Diff^n_epsilon` indexing after source recovery in issue #2.
- [ ] Consult novelty-lab issue #32 for exact literature precedence of the graph-ring symbol statement.
- [ ] Only then request promotion of a new claim in `proof/claims.toml`.


## Independent replay and evidence boundary

Local replay on 2026-10-22: the complete Python suite passes (13 tests);
the C++ oracle reports zero mismatches through k=8, including all 2,027,025
eight-chord matchings. The extended mixed-factor DFS also passes, with
counts 1, 6, 96, 1,296 and 142,848 on the five documented products.

`tests/test_chord_gap_correspondence.py` checks explicit nested/separated and
crossing examples, every component and every gap of all matchings through
k=5, rotations/reflections, wrap/complement and prefix boundaries, and exact
coefficient arithmetic through k=10. The separate C++ oracle exhausts all
matchings through k=8. These are finite regression evidence; the all-k result
rests on the argument above. The recurrence's literature provenance is not
re-proved here; k=9,10 values remain recurrence-derived predictions.

No claim-registry entry, publication source, acceptance status, or novelty
decision is promoted by this independent verification. Mojo execution remains
outside this change. The manuscript/source-lineage and novelty-lab gates above
remain open.

# Motivations for a nonbacktracking and primitive-cycle symbol calculus

**Research motivation | 2026-10-23 | Scope: finite simple undirected graphs**

This note explains *why* the Cartesian graph-ring program passes from ordinary
closed walks to nonbacktracking, primitive, and simple cycles, and what that
progression makes visible. It is motivation and research framing, **not** an
independent proof, a claim of priority, or an acceptance decision. The
mathematical statements summarized below are those in the repository's
[working nonbacktracking/primitive proof record](../../proof/nb-primitive-support-symbol.md),
[working ordinary-cycle proof record](../../proof/even-cycle-order-symbol.md)
and [corrected Paper III v5](../../paper/drafts/nb-cycles-v5-review.tex);
their review status is governed by [the claim registry](../../proof/claims.toml).

## 1. The problem with observing cycles only through adjacency traces

The classical identity for Cartesian products,
[
A_{G\square H}=A_G\otimes I_H+I_G\otimes A_H,
]
makes the ordinary closed-walk invariant
(w_m(G)=\operatorname{tr}(A_G^m)) exceptionally tractable. Its binomial
product convolution can be read directly from the commuting Kronecker
summands. That is a useful starting point, but a closed walk is not
necessarily a cycle in the graph-theoretic sense. It can reverse an edge,
repeat a shorter circuit, or revisit a vertex. Ordinary adjacency traces
combine all of these phenomena.

Even the smallest example makes the distinction concrete. On (C_4),
[
w_4(C_4)=32,qquad b_4(C_4)=8,qquad
p_4(C_4)=2,qquad c_4(C_4)=1.
]
The four numbers count different objects: closed walks with a chosen root;
rooted oriented *cyclically nonbacktracking* walks; oriented primitive
cyclic classes; and unoriented ordinary simple-cycle subgraphs,
respectively. The factor changes are not interchangeable normalizations.

**Motivation:** identify which parts of closed-walk behavior are forced by
Cartesian multiplication and which arise from reversing edges,
periodicity, or repeated vertices. A useful calculus must retain the
distinctions instead of calling every object a “cycle.”

## 2. Why a Cartesian differential symbol is the right measurement

Let (mathcal A) denote the Grothendieck ring with disjoint union as
addition and Cartesian product as multiplication. The vertex-count
character is (arepsilon(G)=|V(G)|); its augmentation ideal is
(I=kerarepsilon). Edge count (d(G)=|E(G)|) is an
(arepsilon)-derivation:
[
d(G\square H)=d(G)arepsilon(H)+arepsilon(G)d(H).
]

For an additive graph invariant (f), the **centered** (q)-factor
defect is
[
D_qf(G_1,ldots,G_q)
=fleft(\prod_{i=1}^q
[G_i-arepsilon(G_i)K_1]\right).
]
With (operatorname{ord}_arepsilon(f)le r) defined by
(f(I^{r+1})=0), its order-(r) principal symbol is (D_rf)
without factorial division.

The point of this formulation is not a new definition of differential
operators. It is a *support detector*: inclusion–exclusion cancels objects
confined to proper coordinate fibers and retains those that use every
chosen factor. For connected ordinary subgraph copies this is an
injective-embedding statement; for Hashimoto traces it remains valid even
when a nonbacktracking closed walk revisits a vertex. Cyclic
nonbacktracking must be checked at the **last/first** step as well as at
interior steps.

This turns an apparently spectral question into a finite structural one.
If a length-(m) closed walk uses a coordinate, it must change that
coordinate at least twice to return. Hence it can use at most
(lfloor m/2floor) product coordinates. At the maximal (k) factors
for length (2k), it uses each exactly twice and thus determines one
undirected edge of each factor. Its maximal-support data live in a
product of (k) edges—an embedded hypercube (Q_k)—regardless of
whether the ambient factors are regular, bipartite, or triangle-free.

**Motivation:** differential order measures maximal independent
Cartesian-coordinate participation, while the principal symbol records
the leading full-support combinatorics. That is more informative for
these questions than a diagonal computation on cubes alone.

## 3. A four-stage distinction, with a controlled correction

There are four related but genuinely different invariant families:

| Layer | Object | What remains or is removed |
| --- | --- | --- |
| Ordinary walks (w_m=operatorname{tr}(A^m)) | Rooted closed walks | All backtracks, repetitions, and revisits remain. |
| Hashimoto traces (b_m=operatorname{tr}(B^m)) | Rooted **oriented cyclically nonbacktracking** closed walks | Immediate reversals, including the cyclic seam, are removed; revisits and periodic powers remain. |
| Primitive counts (p_m) | **Oriented** primitive cyclic equivalence classes | Cyclic roots and proper powers are removed through Möbius inversion; a class may still visit a vertex more than once. |
| Simple counts (c_m=N_{C_m}) | Unoriented, non-induced simple-cycle subgraph copies | Repeated vertices are forbidden, including any premature return. |

The primitive extraction has the exact divisor relations
[
 b_m=sum_{rmid m}r,p_r,qquad
 p_m=rac1msum_{rmid m}mu(m/r)b_r.
]
For even lengths, the remaining gap between primitive and simple cycles
is the **oriented non-simple primitive deficit**
[
Delta_k=p_{2k}-2c_{2k}.
]
The factor (2) accounts for the two orientations of each simple
unoriented cycle. The deficit is a concrete combinatorial population,
not merely a residual scalar: its members are primitive
nonbacktracking closed walks whose vertices are not all distinct.

**Motivation:** the passage from (w) to (b) removes local
backtracking, the passage from (b) to (p) removes periodicity,
and (Delta_k) isolates genuinely repeated-vertex geometry. Each
stage asks a different question of the same Cartesian-product
structure.

## 4. Why the symbol tower is worth computing

The working proof records establish the following **all-order
candidate theorems** on the full finite-simple-graph ring
(not merely on bipartite-generated factors), for (kge2):
[
egin{aligned}
sigma_k(b_{2k})&=eta_k,d^{otimes k},
   &eta_k&=2^k k!R_k>0,\
sigma_k(p_{2k})&=rac{eta_k}{2k},d^{otimes k},\
sigma_k(c_{2k})&=gamma_k,d^{otimes k},
   &gamma_k&=rac{2^k k!A_k}{4k}>0,\
sigma_k(Delta_k)&=eta_k,d^{otimes k},
   &eta_k&=rac{2^k k!}{2k}(R_k-A_k)ge0.
end{aligned}
]

Here (R_k) counts pair partitions of (2k) cyclic positions with
**no block joining adjacent positions**, including the seam. In
contrast, (A_k) counts pair partitions with **no nonempty proper
contiguous interval** closed under the pairing—the simple cube-cycle
condition. The two numbers are different: nonbacktracking allows
nonconsecutive vertex revisits, whereas a simple cycle does not.

The finite identity
[
R_k=sum_{j=0}^k(-1)^j
rac{2k}{2k-j}inom{2k-j}{j}(2k-2j-1)!!
]
(with ((-1)!!=1)) ties the Hashimoto/Chebyshev coefficient to
ordinary matchings in the *cycle of positions*, not to an uncontrolled
asymptotic approximation. Positivity follows by constructing the
admissible word (1,2,ldots,k,1,2,ldots,k).

The striking structural feature is that all the **top** symbols point
in the single direction (d^{otimes k}), while their coefficients
retain the distinctions between the four counting problems. This
does **not** mean the underlying invariants agree, that their
lower-order corrections coincide, or that their full operator
algebras are one-dimensional.

For example, at (k=4):
[
eta_4=11,904,qquad
rac{eta_4}{8}=1,488,qquad
gamma_4=648,qquad
eta_4=1,488-2(648)=192.
]
The final (192) detects non-simple primitive eight-step behavior
that neither primitive normalization nor ordinary simple-cycle
counting alone expresses.

**Motivation:** the scalar tower is a finite, exact *comparison
instrument*. Once its top layer is established, attention can
shift to the lower layers, where graph-specific junction and overlap
geometry must occur.

## 5. Why the corrected seventh coefficient matters

A historical version of Paper III reported
[
c_{14}(Q_7)=406,517,760,qquad
gamma_7=-2,049,830,400
]
and interpreted the negative coefficient as a sign reversal. This is
**not a valid result** under ordinary non-induced simple-cycle
conventions. In a centered seven-factor defect, the seventh
simple-cycle symbol counts full-seven-coordinate cycles and cannot
be negative.

Independent enumerators and a unique-minimal-face decomposition give
the corrected values
[
c_{14}(Q_7)=3,337,213,440,qquad
gamma_7=880,865,280>0.
]
The matching counts are (R_7=44,189) and (A_7=38,232), yielding
[
eta_7=rac{2^7,7!}{14}(44,189-38,232)
=274,498,560.
]
The correction is more consequential than a changed table cell. It
demonstrates why a top symbol should have a **combinatorial meaning**
independent of finite-difference output: a counting interpretation
provides a falsification test for a numerically plausible but
mathematically impossible sign. The current all-(k) simple-cycle
proof candidate supplies that meaning and predicts (gamma_k>0)
at every order within its stated conventions.

See the [exact cube correction](c14-exact-cubes.md), the
[historical v4 audit](../audits/nb-v4-import-review-2026-10-23.md), and
the [corrected manuscript](../../paper/drafts/nb-cycles-v5-review.tex).

## 6. The real remaining combinatorics: local junction structure

The identity (Delta_k=p_{2k}-2c_{2k}) and its top coefficient
(eta_k) do **not** enumerate the different types of
repeated-vertex primitive walk. The proposed recursion over
partitions (lambdadash k) with parts at least two, and
multiplicities (mu_lambda), is still **conjectural**.
A length partition alone can forget which vertices and edges are
shared, how repeated visits are ordered, and how a cyclic traversal
passes through those junctions.

The immediate research task is therefore not to recompute another
hypercube scalar. It is to build an incidence-sensitive description
of primitive closed walks and derive a proven refinement of the
aggregate deficit. At (k=4), a figure-eight made of two four-cycles
is the first motivating configuration; at (k=6), proposed partition
types ((2,2,2)), ((2,4)), and ((3,3)) cannot be separated from
their aggregate coefficient without additional structural data.
A weighted oriented-edge transfer construction could be useful, but
an edge-local state **alone** cannot detect arbitrary vertex revisits:
such an approach must track junction incidence or an equivalent
exact finite memory and justify cyclic equivalence and primitivity.

**Motivation:** a successful correction algebra would explain not
only *how many* full-support primitive walks fail to be simple, but
*why*, by attaching mathematically defined coefficients to exact
overlap types. The existence of such a clean partition-indexed
presentation is an open question, not a premise.

## 7. Concrete research decisions and evidence required

1. **Separate counting conventions.** Preserve the distinction
   between closed walks, cyclically nonbacktracking rooted walks,
   oriented primitive classes, and unoriented ordinary simple copies.
   Induced cycles and directed/looped graphs are outside this note's
   theorem scope.
2. **Keep the finite proof replayable.** Use centered defects and
   independent direct-arc Hashimoto traces, coordinate-word
   enumeration, matching counts, and nonregular/nonbipartite
   Cartesian products. Preserve negative controls, especially the
   incorrect (c_{14}(Q_7)) count and the spurious negative symbol.
3. **Refine the deficit.** Build exact state definitions for
   repeated-vertex incidence; reproduce the (k=4) and (k=5)
   correction geometries before accepting any all-order formula
   for (mu_lambda). Do not infer a universal decomposition from
   matching a few aggregate scalars.
4. **Keep novelty separate from validity.** The Ihara/Hashimoto,
   Möbius, Cartesian adjacency and generic differential
   ingredients belong to established literatures. A new use of
   these tools is not automatically a new theorem. Send
   theorem-specific comparisons to the N6 / novelty-lab gate.
5. **Preserve manuscript provenance and claim status.** This note
   neither promotes entries in `proof/claims.toml` nor makes the
   corrected v5 a peer-reviewed publication. The separate parent
   `ring-graphs-v22` source-lineage gate remains open.

## 8. What the program is ultimately trying to explain

The long-term question is whether the topology of primitive
nonbacktracking cycles can be recovered through **finite,
compositional data** compatible with Cartesian products. The
highest-order symbol is unusually simple because maximal support
forces one edge per factor. Precisely for that reason, the
lower-order terms become the interesting part: they encode departures
from maximal support and the ways distinct simple cycles meet,
overlap, and form primitive but non-simple traversals.

That is the reason to develop the nonbacktracking/primitive tower,
rather than stopping at ordinary walk convolution or treating simple
cycle counts as isolated numerical sequences.

---

### Source and acceptance map

- [Corrected Paper III v5 manuscript](../../paper/drafts/nb-cycles-v5-review.tex) — theorem statements and review draft (merged PR #24).
- [Nonbacktracking/primitive support-word proof](../../proof/nb-primitive-support-symbol.md) — centered support, cyclic pair words, Möbius filtration (merged PR #23).
- [Ordinary even-cycle support proof](../../proof/even-cycle-order-symbol.md) — support-defect identity, all-even-cycle top symbols, corrected (c_{14}) (merged PR #14).
- [Exact cube-correction evidence](c14-exact-cubes.md) — independent enumeration and normalization.
- [Historical Paper III audit](../audits/nb-v4-import-review-2026-10-23.md) — provenance and withdrawn sign-change narrative.
- [Claim registry](../../proof/claims.toml) — `working` statuses and explicit acceptance boundary.
- [Issues #17](https://github.com/larsbx/graph-product-ring-research/issues/17) and [#22](https://github.com/larsbx/graph-product-ring-research/issues/22) — remaining review and proof-acceptance obligations.

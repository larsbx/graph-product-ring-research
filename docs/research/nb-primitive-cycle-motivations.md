# Motivations for a nonbacktracking and primitive-cycle symbol calculus

**Research motivation · 2026-10-23 · Finite simple undirected graphs**

This document explains *why* the Cartesian graph-ring program progresses from ordinary closed walks to nonbacktracking walks, primitive cyclic classes, and simple cycles. It is research framing, not a new proof, a novelty verdict, or a change in theorem-acceptance status. The results mentioned here have working mathematical records in the [nonbacktracking/primitive proof](../../proof/nb-primitive-support-symbol.md), the [ordinary even-cycle proof](../../proof/even-cycle-order-symbol.md), and the [corrected Paper III v5 manuscript](../../paper/drafts/nb-cycles-v5-review.tex). The [claim registry](../../proof/claims.toml) controls their status.

## 1. Why ordinary adjacency traces are not enough

The classical Cartesian-product identity

$$
A_{G\square H}=A_G\otimes I_H+I_G\otimes A_H
$$

makes the ordinary closed-walk count $w_m(G)=\operatorname{tr}(A_G^m)$ especially tractable. The commuting Kronecker summands give a binomial product convolution. Yet a *closed walk* need not be a simple cycle: it may immediately reverse an edge, traverse a shorter circuit several times, or revisit a vertex. Adjacency traces combine all these effects.

The four objects already differ on the four-cycle:

$$
w_4(C_4)=32,\qquad b_4(C_4)=8,\qquad
p_4(C_4)=2,\qquad c_4(C_4)=1.
$$

These count, respectively, rooted closed walks; rooted oriented **cyclically nonbacktracking** closed walks; oriented primitive cyclic classes; and unoriented ordinary simple-cycle subgraphs. Their conversion factors are not merely a choice of notation.

**Motivation.** Determine which features of closed walks arise from Cartesian multiplication and which arise from backtracking, periodicity, or vertex repetition. Treat those effects separately rather than calling each of them a "cycle."

## 2. Why Cartesian differential order is the natural measure

Let $\mathcal A$ denote the Grothendieck ring of finite simple graphs, with disjoint union as addition and Cartesian product as multiplication. Its vertex-count character is $\varepsilon(G)=|V(G)|$. Write $I=\ker\varepsilon$ and let $d(G)=|E(G)|$ be the edge-count derivation:

$$
d(G\square H)=d(G)\varepsilon(H)+\varepsilon(G)d(H).
$$

For an additive invariant $f$, its **centered** $q$-factor augmentation defect is

$$
D_q f(G_1,\ldots,G_q)=
f\left(\prod_{i=1}^q [G_i-\varepsilon(G_i)K_1]\right).
$$

The condition $\operatorname{ord}_{\varepsilon}(f)\le r$ means $f(I^{r+1})=0$; at exact order $r$, the undivided principal symbol is $D_r f$. The centering matters: historical formulas that evaluate uncentered iterated defects need not coincide with this expression for invariants that do not vanish at $K_1$.

Here the operator language has a precise combinatorial purpose. Inclusion–exclusion removes objects confined to a proper coordinate fiber and retains those using *every* selected Cartesian factor. This is a support detector. For ordinary connected subgraph copies, the objects are injective embeddings; for Hashimoto traces, they are cyclically nonbacktracking closed walks, which may revisit vertices. Their cyclic last/first seam must be checked explicitly.

Every coordinate changed by a closed walk must be traversed at least twice in order to return. Hence a length-$m$ walk uses at most $\lfloor m/2\rfloor$ factors. If a length-$2k$ walk uses all $k$ factors, it changes each exactly twice, moving across one uniquely recoverable undirected edge in each factor and back. The maximal-support object therefore lies in a $k$-fold product of edges, a copy of $Q_k$.

**Motivation.** Differential order records the greatest number of independent Cartesian coordinates the invariant can genuinely use. The top symbol records the structure at *maximal support*—not merely a numerical derivative along the family of hypercubes.

## 3. The four-stage counting tower

| Layer | Counted object | What is excluded |
| --- | --- | --- |
| $w_m=\operatorname{tr}(A^m)$ | Rooted ordinary closed walks | Nothing: backtracks, powers, and revisits remain. |
| $b_m=\operatorname{tr}(B^m)$ | Rooted oriented cyclically nonbacktracking closed walks | Immediate edge reversals, including the cyclic seam; periodic powers and nonconsecutive vertex revisits remain. |
| $p_m$ | Oriented *primitive* cyclic classes | Cyclic roots and proper powers; non-simple primitive walks remain. |
| $c_m=N_{C_m}$ | Unoriented, ordinary **non-induced** simple-cycle subgraph copies | Repeated vertices, including premature returns. |

The distinction between $b_m$ and $p_m$ is governed by Möbius inversion:

$$
b_m=\sum_{r\mid m} r\,p_r,\qquad
p_m=\frac1m\sum_{r\mid m}\mu(m/r)b_r.
$$

For even lengths, the residual difference between oriented primitive classes and unoriented simple cycles is a **concrete population of non-simple primitive cycles**:

$$
\Delta_k=p_{2k}-2c_{2k}.
$$

The coefficient $2$ accounts for two orientations of each unoriented simple cycle. The deficit counts primitive nonbacktracking closed walks which revisit vertices; it is not merely a formal subtraction.

**Motivation.** The transition $w\to b$ removes immediate reversals, $b\to p$ removes periodicity, and $\Delta$ isolates vertex-repetition geometry. These three corrections answer different mathematical questions.

## 4. Why the top symbols and their coefficients matter

The repository's **working all-order proof records** state, on the full finite-simple-graph ring and for every $k\ge2$,

$$
\begin{aligned}
\sigma_k(b_{2k})&=\beta_k d^{\otimes k},
  &\beta_k&=2^k k!R_k>0,\\
\sigma_k(p_{2k})&=\frac{\beta_k}{2k}d^{\otimes k},\\
\sigma_k(c_{2k})&=\gamma_k d^{\otimes k},
  &\gamma_k&=\frac{2^k k!A_k}{4k}>0,\\
\sigma_k(\Delta_k)&=\eta_k d^{\otimes k},
  &\eta_k&=\frac{2^k k!}{2k}(R_k-A_k)\ge0.
\end{aligned}
$$

The coefficients encode two distinct finite pairing restrictions. $R_k$ counts pair partitions of the $2k$ **cyclic** step positions with no pair joining adjacent positions, including across the last/first seam. $A_k$ counts pair partitions with no nonempty proper contiguous interval closed under pairing—the condition excluding repeated vertices in a full-support simple cube cycle.

In particular, a finite inclusion–exclusion calculation, using matchings in the *cycle of positions*, gives

$$
R_k=\sum_{j=0}^{k}(-1)^j
\frac{2k}{2k-j}\binom{2k-j}{j}(2k-2j-1)!!,
\qquad (-1)!!=1.
$$

This is the historical Chebyshev–moment leading coefficient in a purely finite combinatorial form. Positivity follows by constructing the cyclically admissible word $1,2,\ldots,k,1,2,\ldots,k$.

The structural observation is that **all four top symbols have the single direction $d^{\otimes k}$**. Their coefficients are nevertheless different. This does *not* imply that the invariants or their lower-order symbols coincide, nor that the entire graph trace algebra is generated by $d$.

At $k=4$, for example,

$$
\beta_4=11\,904,\qquad
\frac{\beta_4}{8}=1\,488,\qquad
\gamma_4=648,\qquad
\eta_4=1\,488-2(648)=192.
$$

The number $192$ detects primitive, non-simple, length-eight behavior that is invisible when only simple cycles are counted.

**Motivation.** The scalar tower is a finite comparison instrument. Once the maximal-support component is understood, the real geometry lies in the lower-order effects: joins, overlaps, and vertex revisits that the top symbol aggregates rather than classifies.

## 5. Why correcting the seventh symbol changes the research story

An earlier Paper III draft reported

$$
c_{14}(Q_7)=406\,517\,760,\qquad
\gamma_7=-2\,049\,830\,400
$$

and interpreted the negative coefficient as a sign reversal. That conclusion is **false** under the stated ordinary, non-induced simple-cycle counting convention. A centered seven-factor defect counts cycles using all seven coordinates; that number cannot be negative.

Independent cube enumeration and the unique-minimal-face decomposition yield

$$
c_{14}(Q_7)=3\,337\,213\,440,\qquad
\gamma_7=880\,865\,280>0.
$$

Moreover, $R_7=44\,189$ and $A_7=38\,232$, giving the aggregate repeated-vertex deficit

$$
\eta_7=\frac{2^7\,7!}{14}(44\,189-38\,232)
=274\,498\,560.
$$

The corrected all-order ordinary-cycle proof candidate predicts $\gamma_k>0$ at every $k\ge2$. The value is not a newly discovered sign flip: the sign flip was an enumeration and interpretation error.

**Motivation.** A combinatorial interpretation of an abstract symbol provides a *falsification criterion*. Nonnegativity of full-coordinate support caught a numerically derived but impossible claim, and independent counting repaired the numerical evidence. This is a reason to build theorem statements and computational oracles around exact objects, not just sequences of coefficients.

See the [exact cube correction](c14-exact-cubes.md), [historical v4 audit](../audits/nb-v4-import-review-2026-10-23.md), and [corrected v5 source](../../paper/drafts/nb-cycles-v5-review.tex).

## 6. The remaining problem is junction geometry, not another scalar

Although the top deficit coefficient $\eta_k$ is expressed at every order by the working proof records, it does not distinguish different kinds of non-simple primitive cycle. The proposed partition-indexed recursion, with $\lambda\vdash k$ and junction multiplicities $\mu_\lambda$, is still a **conjectural model**. A length partition can forget how cycles share vertices or edges, the ordering of repeated visits, and how orientation and cyclic primitivity constrain a traversal.

At length eight, the first illustrative obstruction is the figure-eight arrangement of two four-cycles sharing a vertex. At order $k=6$, the candidate types $(2,2,2)$, $(2,4)$ and $(3,3)$ are not determined individually by the single aggregate $\eta_6=1\,904\,640$.

A meaningful next step is an **incidence-sensitive** census or transfer object with precise state semantics: rooted vertex-repetition patterns, junction incidence, traversal order, orientation, and tests for cyclic periodicity. A line-digraph state that only knows the current directed edge cannot, by itself, identify arbitrary earlier vertex visits. Any quotient by partition type must be justified by an exact bijection or a proved invariant-preserving reduction.

**Motivation.** A genuine correction algebra should explain not only *how many* primitive nonbacktracking cycles are non-simple at top order, but *why*, by locating their contributions in independently defined overlap types. The existence of a compact partition-indexed presentation remains open.

## 7. Research and acceptance priorities

1. **Protect the counting conventions.** Ordinary versus non-induced simple cycles, rooted versus cyclic, oriented versus unoriented, primitive versus powered, and cyclic versus ordinary nonbacktracking must not be interchanged. The cited all-order results are scoped to finite simple graphs.
2. **Keep centered defects and reproducible oracles.** Independent arc-based Hashimoto traces, cyclic pairings, cube-coordinate words, and irregular/nonbipartite product tests check different failure modes. Retain the erroneous $Q_7$ value as a negative regression control, not as an alternative result.
3. **Separate aggregate and refined corrections.** Test explicit repeated-vertex incidence types at $k=4$ and $k=5$ before assigning universal meaning to $\mu_\lambda$; pursue the proposed $k=6$ types with independent geometric probes.
4. **Audit novelty at claim level.** Ihara–Bass/Hashimoto theory, Möbius inversion, Cartesian adjacency convolution, and generic differential-operator machinery are existing ingredients. A specialized synthesis does not automatically imply a new theorem; novelty judgments belong with the repository's N6/novelty-lab gates.
5. **Keep the source and proof authority distinct.** Corrected v5 is a manuscript artifact, not an acceptance certificate. The parent *ring-graphs-v22* source-lineage issue is separate. The proof records remain marked **working** in the claim registry pending independent mathematical and literature review.

## 8. Central motivation

The long-term problem is whether primitive nonbacktracking cycle topology can be represented by **finite compositional data compatible with Cartesian products**. The top symbol is remarkably simple because maximal support forces exactly one edge per factor. That simplicity does not trivialize the program; it points directly toward the lower-order strata where repetition and junction structure must live.

This is why the project should not stop with ordinary walk convolution, nor treat simple-cycle counts as disconnected numerical curiosities. The tower gives a shared algebraic measurement, while the differences between its layers isolate the geometry needing explanation.

---

### Primary repository sources and review obligations

- [Computer science implications and applied mathematics connections](cycle-calculus-cs-applied-connections.md) — application hypotheses, algorithmic research targets, and boundaries.
- [Corrected Paper III v5 manuscript](../../paper/drafts/nb-cycles-v5-review.tex), merged PR #24.
- [Nonbacktracking and primitive support-word proof](../../proof/nb-primitive-support-symbol.md), merged PR #23.
- [Ordinary even-cycle coordinate-support proof](../../proof/even-cycle-order-symbol.md), merged PR #14.
- [Cube correction and independent enumeration](c14-exact-cubes.md).
- [Historical Paper III v4 audit](../audits/nb-v4-import-review-2026-10-23.md).
- [Claim registry](../../proof/claims.toml) and [acceptance issues #17](https://github.com/larsbx/graph-product-ring-research/issues/17) and [#22](https://github.com/larsbx/graph-product-ring-research/issues/22).

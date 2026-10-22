# Branch 5A: nonbacktracking, primitive and simple-cycle symbols

Date: 2026-10-22. **Research memo / working proof candidate — not a manuscript or accepted theorem.**
Owner: graph-product-ring-research. Cross-reference: [ordinary even-cycle proof record](../../proof/even-cycle-order-symbol.md), [claim registry](../../proof/claims.toml), [draft chord identification PR #16](https://github.com/larsbx/graph-product-ring-research/pull/16), [novelty-lab #32](https://github.com/larsbx/novelty-lab/issues/32).

## Scope and exact definitions

All graphs are finite simple undirected. Cartesian product is denoted \(\square\), the graph-ring character is \(\varepsilon(G)=|V(G)|\), \(d(G)=|E(G)|\), and differential order/symbol use the **centered augmentation-ideal** convention of the proof record. Do not substitute uncentered iterated-delta evaluations.

Let \(w_m(G)=\operatorname{tr}(A_G^m)\). Let \(B_G\) be the Hashimoto matrix on oriented edges, with \((u,v)\to(v,z)\) allowed precisely when \(z\ne u\). Put \(b_m(G)=\operatorname{tr}(B_G^m)\): *cyclically* nonbacktracking, oriented, rooted closed walks. Write \(p_m(G)\) for oriented primitive cyclic equivalence classes (unrooted, but orientation retained); then
\[
b_m(G)=\sum_{r\mid m} r\,p_r(G),\qquad
p_m(G)=\frac1m\sum_{r\mid m}\mu(r)b_{m/r}(G).
\]
Define the primitive-but-not-simple deficit
\[
\Delta_k(G)=p_{2k}(G)-2c_{2k}(G).
\]
This normalizes every simple unoriented cycle to two oriented primitive cyclic classes. Verify the original nb draft uses exactly this normalization **before** transferring its coefficient notation.

## Ledger of the three prior gaps

| Gap | Previous state | Concrete next proof requirement |
| --- | --- | --- |
| Global proportionality of \(\sigma_k(b_{2k})\) | diagonal \(K_2\)-tuple computations did not establish a global symbol | apply the full-support coordinate-word argument below to all graph factors, then independently check the definition of cyclic nonbacktracking and the symbol normalization |
| \(a_k>0\) in the nb draft | finite evaluations/alternating sum placeholder | identify *which* \(a_k\) is meant; if it is a positive scalar multiple of \(b_{2k}(Q_k)\), exhibit a single permissible cyclic word; otherwise do not claim the original alternating-sum lemma is closed |
| \(\mu_\lambda\) junction recursion | conjectural partition bookkeeping | build a weighted oriented-edge automaton and cyclic-word/junction census; demonstrate exact recurrence and multiplicities for \(k=4,5\) before a general statement |

**Notation collision:** the connected-chord numbers \(a_k^{\rm chord}\) of the ordinary simple-cycle proof are positive by a constructive proof, whereas the nb note's alternating-sum \(a_k^{\rm nb}\) may be a *different* sequence. Do not conflate them.

## Candidate support-word theorem (new argument to review)

**Candidate theorem.** For every \(k\ge2\), on the **full** Cartesian graph ring,
\[
\operatorname{ord}_\varepsilon(b_{2k})=k,\qquad
\sigma_k(b_{2k})(G_1,\ldots,G_k)=\beta_k\prod_{i=1}^k d(G_i),
\]
where \(W_k\) is the set of labeled words \(w_1\cdots w_{2k}\) on \(\{1,\ldots,k\}\) in which every letter occurs twice and \(w_i\ne w_{i+1}\) cyclically, and
\[
\beta_k=2^k|W_k|=b_{2k}(Q_k)>0.
\]

**Proof outline, requiring independent audit.**
1. The centered \(k\)-factor defect of \(b_{2k}\) counts the cyclically nonbacktracking closed walks that change every Cartesian coordinate. This is ordinary inclusion-exclusion over constant coordinates. Unlike the connected-pattern proof, these walks need not be injective; justify the inclusion-exclusion directly for walk objects.
2. Every coordinate used by a closed walk changes at least twice (a nonconstant projected closed walk on a loopless graph cannot have length one). Hence no length-\(2k\) closed walk uses more than \(k\) factors, giving \(\operatorname{ord}\le k\).
3. In a full-support walk through exactly \(k\) factors, each coordinate changes exactly twice, along one undirected edge and then backwards. Choosing that edge independently in each factor produces \(Q_k\); every such walk is supported in exactly this uniquely recovered edge-tuple.
4. A step backtracks immediately precisely when two successive flips use the same coordinate; cyclic nonbacktracking imposes the same condition across the final/first step. Therefore the allowed flip words are exactly \(W_k\), independently of other edges in each ambient factor.
5. A chosen edge-tuple has \(2^k\) possible starting vertices and \(|W_k|\) rooted oriented flip sequences. The choice-to-walk map is bijective even if the walk revisits vertices. Thus its full-support defect equals \(2^k|W_k|\prod_i d(G_i)\).
6. The cyclic word \(1,2,\ldots,k,1,2,\ldots,k\) belongs to \(W_k\) for \(k\ge2\); so \(\beta_k>0\) and evaluation at \(G_i=K_2\) gives the lower order bound.

**Consequence, conditional only on checking the outline:** since proper divisors \(r>1\) have \(m/r<2k\), and the support bound gives \(\operatorname{ord}(b_m)\le\lfloor m/2\rfloor\), Möbius inversion yields
\[
\operatorname{ord}_\varepsilon(p_{2k})=k,\qquad
\sigma_k(p_{2k})=\frac{\beta_k}{2k}\,d^{\otimes k}.
\]
The deficit has candidate top symbol
\[
\sigma_k(\Delta_k)=\left(\frac{\beta_k}{2k}-2\gamma_k\right)d^{\otimes k},
\quad
\gamma_k=2^{k-2}(k-1)!\,a_k^{\rm chord}.
\]
The first *nonzero* deficit at \(k=4\) must be checked against the nb memo's exact convention. This proof candidate is **not** a proof of the lower-order junction recursion.

## Literature-backed alternate routes (not automatically valid theorems)

- **Regular-factor spectral transfer:** Bass–Ihara and Chebyshev polynomials express nonbacktracking counts using adjacency spectra on regular graphs. Useful for a second, independent proof of the candidate coefficient; does **not** justify extension from regular factors to all bipartite graphs. Rangarajan (FSTTCS 2017), https://doi.org/10.4230/LIPIcs.FSTTCS.2017.46.
- **Hamming-scheme/Krawtchouk analysis:** useful to simplify the original alternating sum on hypercubes; positivity of a generic Krawtchouk transform does **not** imply positivity of a particular scalar without checking the cone and normalization. Use only if the candidate word proof does not identify the nb coefficient.
- **Connection matrices:** Lovász/Freedman/Schrijver-inspired rank-one tests might characterize purity of a symbol after quotienting lower order, but the correspondence itself requires a theorem, not an analogy.
- **Lyndon words and Ihara primitive extraction:** primitive cyclic words separate via necklace/Möbius inversion; apply to the deficit \(\Delta_k\), not as a substitute for controlling repeated vertices. Foata–Zeilberger combinatorial Ihara proofs.
- **Bartholdi-type defect generating functions:** use an auxiliary variable for revisited vertices/junction types, *not* for backtracking alone. A naive finite oriented-edge state does not detect revisits; it needs vertex-memory or an exact partition state and quotient rules.

## Junction-recursion program (still conjectural)

Seek a weighted transfer object \(\mathcal B_G(u,t)\) and logarithmic/primitive extraction in which \(t\) records repeated-vertex junctions, not just bumps. Candidate connection-state partitions \(\lambda\) include \((2,2)\), \((2,3)\), \((2,2,2)\). Define \(\mu_\lambda\) only after proving a bijection between primitive cyclic walks and automaton objects carrying that junction type. Check automaton invariance under cyclic rotation/reversal and eliminate periodic words before claiming primitive multiplicities. First acceptance target: explain all terms in \(\Delta_4\) by explicit objects; second: \(\Delta_5\) independent oracle agreement.

## Reproducibility and promotion gates

1. Confirm the nb note's precise \(b,p,a_k\) definitions and avoid confusing \(a^{\rm nb}\) with \(a^{\rm chord}\).
2. Independently formalize the non-injective support inclusion-exclusion and cyclic seam condition; run fixtures \(K_2^k\) and mixed, irregular, nonbipartite factors.
3. Compare the \(\beta_k\) word count against direct Hashimoto matrix traces and the Möbius-derived primitive counts; negative controls must distinguish ordinary, cyclically nonbacktracking, primitive, and simple cycles.
4. Leave the junction recurrence **conjectural** until all its multiplicities are derived and independently reproduced.
5. Literature novelty decision belongs to [novelty-lab #32](https://github.com/larsbx/novelty-lab/issues/32). No acceptance authority or manuscript changes are claimed here. Preserve the source-provenance gate #2 / PR #11.

## References and context

- [Graph product research PR #14](https://github.com/larsbx/graph-product-ring-research/pull/14), merged working support/order theorem.
- [Graph product research PR #16](https://github.com/larsbx/graph-product-ring-research/pull/16), draft all-\(k\) connected-chord identification and acceptance gates.
- Rangarajan, *A Combinatorial Proof of Ihara-Bass's Formula for the Zeta Function of Regular Graphs*, FSTTCS 2017, https://doi.org/10.4230/LIPIcs.FSTTCS.2017.46.
- Foata–Zeilberger, combinatorial approach to Bass/Ihara, https://irma.math.unistra.fr/~foata/paper/pub78.pdf.
- Approximate/spectral transfer, graph-bundle zeta, and Krawtchouk references from the discussion are **research leads** pending precise locator verification, not imported proof.

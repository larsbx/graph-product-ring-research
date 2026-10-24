# Thread-to-repository audit — 2026-10-22

**Disposition:** partially portable as research notes; **NOT ready for mathematical claim promotion or a publication merge**.

**Targets:** `larsbx/graph-product-ring-research` (mathematics/evidence), `larsbx/novelty-lab#32` (literature novelty gate). This is a review record, not an acceptance certificate. The chat-generated v0.1.6 manuscripts and addenda have not been imported as an exact-source, hashed snapshot under issue #2. PR #11 currently records a separate v22-PDF / v21-TeX source gap.

## P0 — numerical contradiction in Paper III's ordinary `c14` principal symbol

The conversation's Paper III PDF, *Nonbacktracking Walks and Cycle Counts as Differential Operators on the Cartesian Graph Ring*, §7 Table 2 reports:

| Cube | `c14(Q_n)` |
|---|---:|
| `Q4` | 5,376 |
| `Q5` | 4,652,160 |
| `Q6` | 203,258,880 |
| `Q7` | 406,517,760 |

Its §7 Table 1 reports `gamma'_7 = -2,049,830,400`.

For the **ordinary non-induced subgraph count of a connected graph**, the 7-argument augmented defect evaluated at seven `K2` factors counts copies using all seven coordinates. It is a nonnegative integer, regardless of whether the counting convention is labeled embeddings or unlabeled subgraphs. The table implies instead

```
sigma_7(c14)(K2,...,K2)
  = 128 * sum_{j=0}^7 (-1)^(7-j) C(7,j) c14(Qj)/2^j
  = -2,049,830,400.
```

This is impossible under the stated semantics. Moreover, the printed `c14(Q7)` is **exactly twice** `c14(Q6)`, suspiciously suggesting a single-face lift rather than exhaustive enumeration. If the other listed counts are correct, nonnegativity alone requires `c14(Q7) >= 2,456,348,160`; full seven-coordinate copies exist (the 14-step cube cycle flipping axes 1..7 and then 1..7), so the true inequality is strict. These are consistency checks, not an independent replacement enumeration.

**Action:** isolate and reproduce the cycle enumerator; check symmetry factors, dimension traversal, generated counts, and whether the negative `gamma'_7` survives correction. Do not merge the negative-symbol theorem/sign-change narrative. Add this falsification case to issue #9 and the `c14` extension of #8.

## P1 — correct scope for the support-defect theorem

The thread's proposed identity is promising and admits a short proof **for connected pattern `Gamma` with at least two vertices**, additive ordinary-subgraph counting, vertex-count augmentation, and a fixed labeled/unlabeled convention:

```
(delta_{G1} ... delta_{G(q-1)} N_Gamma)(Gq)
  = # {copies of Gamma in G1 □ ... □ Gq with nonconstant projection on every factor}.
```

Möbius inversion on used coordinate sets proves it. Paired with the complement-component coordinate-coloring bridge, it yields the candidate `ord_epsilon(N_Gamma) = r*(Gamma)`, where `r*` is the maximum number of genuinely used coordinates. Unlike the disputed sign coefficient, this theorem is logically consistent and explains *why* negative ordinary-cycle top defects are impossible.

**Acceptance requirements:** exact `Diff_epsilon^n` convention, `q` versus `q-1` defect count, additive extension to the Grothendieck group, distinction between non-induced versus induced cycles and between labeled vs unlabeled copies, independent proof and oracle. Record as `working` until these are checked under issue #2/#4.

## P1 — uploaded multipartite proof contains a real nonexistent triangle

In `PATCH_2_K333_and_open_problems.md`, the propagation proof attempts the triangle `{u,u',w}` when `u,u'` belong to the same independent part. That is **not a triangle**. The claim `K_{n1,...,nr}` is S-prime for `r>=3` may still be valid, but this uploaded proof **must not** be merged verbatim.

A clean proof uses the triangle-edge adjacency graph: its vertices are edges of `Gamma`; two edge-vertices are adjacent if their original edges belong to one triangle. In a complete multipartite graph with >=3 nonempty parts, all edges incident to any fixed vertex lie in the same connected component of this adjacency graph: edges to two distinct parts form a triangle directly; edges to the same part connect through any vertex of a third part. Since `Gamma` is connected, all its edges are connected in triangle-edge adjacency. Every triangle must be monochromatic in any Cartesian-product embedding, so all edges change the same coordinate. Hence every embedding is fiber-confined. Record the result as a literature-checked corollary, not a novelty claim, pending the S-prime prior-art check.

## P1 — source-of-record mismatch

The GitHub repository's `main` has charter/roadmap/claim registry only; it has no imported `paper/`, kernel, or conformance suite. PR #11 is a **mergeable draft documentation-only inventory**, and explicitly states the latest located artifact is `ring-graphs-v22.pdf` without matching `v22.tex`, with the verification package at `ring_graphs_verify-0.4.0`. The chat has separately produced `fc_companion-0.1.5` and several patched `v0.1.6` local files. Their relationship to v22 and the verification package has **not** been established. Do not silently set the conversation artifacts as canonical.

**Action:** issue #2: import exact bytes/digests, identify manuscript lineage, then apply verified changes on the authoritative TeX source; retain historical drafts with retraction notes.

## P2 — conventions, literature attribution, and overclaims

- Use **Cartesian S-prime** as the literature name. Hellmuth's published article establishes NP-complete S-composite recognition and coNP-complete S-prime recognition on connected graphs, in its **Theorem 2.12**; a chat patch's `Theorem 3.4` locator appears wrong. Its connected-graph hypothesis matches the present FC setting.
- Cartesian factorization in polynomial time and S-prime recognition are different problems; no new hardness proof should be claimed.
- The complement-component bridge requires only: E_not_i paths **preserve** coordinate i. The converse, that equal i-th coordinates always imply such a path in the embedded graph, is generally false. The actual proof only needs the forward implication.
- The proposed `r*(G □ H)=r*(G)+r*(H)` is at present a candidate, not a theorem. Its lower bound follows from product embeddings; upper bound needs proof or falsification.
- Do **not** promote principal-symbol claims from a single hypercube diagonal evaluation. `sigma_k(N_Gamma)` need not be proportional to `d^tensor k`; order and top-symbol classification are separate.
- A previous chat statement `K_{m,n}` is FC except `K_{2,2}` was too broad: stars `K_{1,n}` (n>=2) are trees and have `r*=n`, hence are not FC. Classical S-prime bipartite families require proper part-size restrictions.
- Correct odd-cycle scope: `C5` has a mixed embedding in `K3 □ K3` on the *full ring*, although a different restriction may hold on the triangle-free-generated subring.

## Merge matrix

| Material | Placement | Verdict |
|---|---|---|
| Hellmuth/S-prime prior-art correction | #3, sourced bibliography | **Mergeable as literature correction**, after accurate locators |
| Historical manuscript & package inventory | #2 / PR #11 | **Draft documentation mergeable**; no theorem promotion |
| Triangle-monochromatic multipartite claim | theorem note / #3 | **Requires corrected proof** and prior-art check |
| Complement-component bridge | theorem note / #4 | **Working** pending exact count conventions / independent replay |
| Support-defect formula & order = r* | theorem note / #4 | **Working**; priority for formal review, no publication merge yet |
| Paper III c14 negative coefficient and sign reversal | #8/#9 | **Blocked / contradicted** |
| Product additivity of r* | experiments/open question | **Conjectural** |
| Chat v0.1.6 canonical manuscripts | paper/ | **Blocked** by provenance and consistency gates |

**Recommendation:** merge provenance/audit documentation only; do not merge the thread wholesale or mark any theorem `proved` in `proof/claims.toml` until sources are imported and the P0 `c14` contradiction resolved. This audit deliberately does not alter claims status or manuscript files.

### References
- Paper III (conversation upload), §7 Tables 1–2 and §9.
- Hellmuth, *On the Complexity of Recognizing S-composite and S-prime Graphs*, *Discrete Applied Mathematics* 161 (2013), 1006–1013; Theorem 2.12.
- `larsbx/graph-product-ring-research` README / ARCHITECTURE / `proof/claims.toml`, issue #2, PR #11.

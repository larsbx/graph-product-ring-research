# A third-order rooted-path jet on the finite Cartesian graph ring

**Repository claim status:** `working` pending independent mathematical and prior-art review. The combinatorial argument is complete and has a separate finite exhaustive audit; this is not a literature-novelty claim. This note is a contribution to the user's ring-theoretic program, not a claim of novelty relative to all published literature.

## Setting

Let \(A=K_0^{\square}(\mathrm{FinGraph})\), with addition induced by disjoint union and multiplication by the Cartesian product. Work with finite, undirected, simple graphs, allowing disconnected and empty graphs. Put \(\varepsilon(G)=|V(G)|\), \(d(G)=|E(G)|\), and \(U(G)=N_{P_3}(G)=\sum_v\binom{\deg v}{2}\).

Let \(F(G)=N_{P_4}(G)\) count **unrestricted, not necessarily induced** subgraph copies of the four-vertex, three-edge path. Thus an undirected path edge-set is counted once, even when the four vertices support additional chords. Define \(\widehat F(G)=4F(G)\) when any of the path's four vertices may be distinguished as a root, or \(F_{\mathrm{end}}(G)=2F(G)\) if the root must be one of the path's two endpoints.

## Proposition 1: exact Cartesian product law

For any finite simple graphs \(G,H\),

\[
F(G\square H)=\varepsilon(H)F(G)+\varepsilon(G)F(H)
+6d(H)U(G)+6d(G)U(H)+4d(G)d(H). \tag{1}
\]

**Proof.** Let \(t(G)\) denote the triangle count and define

\[
B(G)=\sum_{\{u,v\}\in E(G)}(\deg(u)-1)(\deg(v)-1).
\]

For each orientation of a middle edge \(u\to v\), choosing a predecessor different from \(v\) and a successor different from \(u\) gives \((\deg u-1)(\deg v-1)\) nonbacktracking walks of length three. Each genuine simple \(P_4\) is counted twice (opposite orientations). The only remaining collision is that the last vertex equals the first, making an oriented triangle. Every triangle contributes six such oriented closed walks. Hence

\[
F(G)=B(G)-3t(G). \tag{2}
\]

Write \(S(G)=\sum_v\deg(v)(\deg(v)-1)=2U(G)\); then \(\sum_v\deg(v)^2=S(G)+2d(G)\). Every \(G\)-parallel edge of \(G\square H\), indexed by \(uv\in E(G)\) and \(h\in V(H)\), contributes

\[
(\deg_G u+\deg_H h-1)(\deg_G v+\deg_H h-1).
\]

Summing gives

\[
\varepsilon(H)B(G)+2d(H)S(G)+d(G)\sum_h\deg_H(h)^2,
\]

because \(\sum_{uv\in E(G)}(\deg_Gu+\deg_Gv-2)=S(G)\). Adding the symmetric \(H\)-parallel edges yields

\[
B(G\square H)=\varepsilon(H)B(G)+\varepsilon(G)B(H)
+3d(H)S(G)+3d(G)S(H)+4d(G)d(H).
\]

Every triangle of a Cartesian product lies entirely in one coordinate fiber, so \(t(G\square H)=\varepsilon(H)t(G)+\varepsilon(G)t(H)\). Substitute equation (2) and \(S=2U\) to obtain (1). \(\square\)

## Proposition 2: exact order and integer-normalized cubic jet

Let \(\delta_x D(y)=D(xy)-D(x)\varepsilon(y)-\varepsilon(x)D(y)\), as in the existing graph-ring differential filtration. From (1),

\[
\delta_G F(H)=6d(G)U(H)+6U(G)d(H)+4d(G)d(H). \tag{3}
\]

The already established identities \(\delta_Gd=0\) and \(\delta_GU(H)=4d(G)d(H)\) imply

\[
\delta_K\delta_G F(H)=24d(K)d(G)d(H), \qquad
\delta_L\delta_K\delta_G F=0.
\]

Therefore \(F\in\mathrm{Diff}^3_\varepsilon(A,\mathbb Z)\) and its order is **exactly three**, since \(d(K_2)=1\) gives a nonzero third mixed difference:

\[
\sigma_3(F)=24\,d^{\otimes3}. \tag{4}
\]

The two natural rooted normalizations are

\[
\sigma_3(F_{\mathrm{end}})=48\,d^{\otimes3},\qquad
\sigma_3(\widehat F)=96\,d^{\otimes3}.
\]

This concerns unrestricted subgraph copies, not induced copies.

For the prime-factor polynomial presentation \(A\cong\mathbb Z[x_P]\), choose a finite set of prime variables and \(y_P=x_P-|V(P)|\). Define the integral constant-coefficient derivation

\[
E=\sum_P d(P)\frac{\partial}{\partial y_P}.
\]

As a statement about the degree-three graded jet at \(\varepsilon\),

\[
F\equiv 4\,(\varepsilon\circ E^3)\pmod{\mathrm{Diff}^2_\varepsilon}.
\]

Indeed on \(y_Py_Qy_R\) both give \(24d(P)d(Q)d(R)\), including repeated indices. The normalization is integral and does not require division by \(3!\) or an appeal to rational divided powers. The restriction to finite prime-variable sets is compatible under enlargement, since every polynomial uses finitely many variables.

## Audit: entirely independent finite enumeration

Run `python3 oracles/p4_cartesian_jet_audit.py` (Python standard library only, no third-party graph package). It enumerates all labeled simple graphs of order \(0\) through \(5\), canonically quotients by **every vertex permutation**, then directly enumerates injective three-edge walks in every representative and Cartesian product. It also evaluates (2), (1), the third mixed difference, and a fourth mixed difference.

Observed on the run accompanying this note:

| Check | Exact number | Result |
|---|---:|---|
| Nonisomorphic finite graphs on 0–5 vertices (1,1,2,4,11,34) | 53 | All passed (2) |
| Unordered graph pairs with repetition from those 53 graphs | 1,431 | All passed (1) |
| Unordered connected triples with repetition, factor orders ≤4 | 220 | Third difference = \(24d(G)d(H)d(K)\) |
| Unordered connected 4-tuples with repetition, factor orders ≤3 | 35 | Fourth mixed difference = 0 |

Calibration values: \(F(K_2\square K_2)=4\); \(F(K_2^{\square3})=48\); \(F(K_3\square K_2)=30\); \(\sigma_3(F)(K_2,K_2,K_2)=24\).

The independent program directly tests graph copies, so its correctness does **not** rely on the product formula being validated. The finite enumeration is evidence against implementation errors, not a substitute for the universal proof above.

## Limitations and next exact test

- This establishes one exact order-three subgraph-count operator on the **whole** graph ring; it does not claim the same law for *induced* \(P_4\) counts.
- It does not validate a universal subgraph-prime decomposition; mixed-coordinate paths are counted explicitly, avoiding the retracted universal projection factorization.
- A separate research question is to classify order and principal symbols of \(N_{P_m}\) for general \(m\), including whether the leading symbol is uniformly proportional to \(d^{\otimes(m-1)}\). No such general theorem is asserted here.
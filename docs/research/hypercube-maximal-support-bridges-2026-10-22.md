# Maximal-support cycles: hypercube Turán and Hamilton-profile bridges

Date: 2026-10-22. **Research proposal; no supersaturation or Hamilton-profile theorem asserted.**
Related: [nb/primitive symbol branch](nb-primitive-symbol-bridge-2026-10-22.md), [ordinary cycle support proof](../../proof/even-cycle-order-symbol.md), [open chord-diagram PR #16](https://github.com/larsbx/graph-product-ring-research/pull/16).

## Normalization (essential)

Let \(Q_n=K_2^{\square n}\). An ordinary \(C_{2k}\) means an *unoriented, unrooted, non-induced* simple cycle selected by its edges (not a closed walk). A coordinate direction is *used* when some cycle edge flips that bit. Put
\[
M_k(F)=\#\{C_{2k}\subseteq F:|\operatorname{supp}(C_{2k})|=k\},\qquad F\subseteq Q_n.
\]
Let \(a_k^{\rm chord}\) count pair partitions of \([2k]\) without a nonempty proper pairing-closed interval. The working GPR theorem gives
\[
\gamma_k=2^{k-2}(k-1)!a_k^{\rm chord}
=c_{2k}^{\rm full}(Q_k),\quad
\sigma_k(c_{2k})=\gamma_k d^{\otimes k}.
\]
Values (independent perfect-matching and cube oracles available in source repo):

| k | a_k^chord | gamma_k |
| -: | -: | -: |
| 2 | 1 | 1 |
| 3 | 4 | 16 |
| 4 | 27 | 648 |
| 5 | 248 | 47,616 |
| 6 | 2,830 | 5,433,600 |
| 7 | 38,232 | 880,865,280 |

**Literature bridge — candidate exact identification.** Axenovich–Benz–Offner–Tompkins, *Generalized Turán densities in the hypercube*, Discrete Mathematics 346 (2023), DOI https://doi.org/10.1016/j.disc.2022.113238, define \(z_{k,\ell}\) to count \(C_{2\ell}\) in \(Q_k\) using exactly \(k\) directions. Under matching ordinary-cycle conventions, their \(z_{k,k}\) equals our \(c_{2k}^{\rm full}(Q_k)=\gamma_k\). This follows by aligning the **definitions**; it is an identity of counts, not a newly proved extremal bound. Section 2 / Lemma 2 and Theorems 3, 5 and 7 are closest literature locators. Independently check potential induced/embedding normalizations before calling it an accepted bridge.

Theorem 3 supplies
\[
\mathbf d(Q_n,C_{2k},C_6)
\ge [4^{k+1}z_{k,k}(1+o(1))]^{-1}\quad(k\ge4).
\]
With this identification, it rewrites as
\[
\mathbf d(Q_n,C_{2k},C_6)
\ge \frac{1-o(1)}{2^{3k}(k-1)!a_k^{\rm chord}}.
\]
This is a **substitution into a known theorem**; novelty lies, if anywhere, in useful closed enumerations/recurrences, sharpening extremal arguments, or constructive applications.

The ambient number of maximal-support cycles is **exactly**
\[
M_k(Q_n)=\gamma_k \binom nk 2^{n-k};
\]
each full-support cycle is contained in a unique \(k\)-dimensional coordinate subcube.

## Candidate MSCS(k): maximal-support cycle supersaturation

For each fixed \(k\ge4\) with \(k\ne5\) and \(\delta>0\), do there exist \(\eta_k(\delta)>0\), \(n_0(k,\delta)\) such that every \(n\ge n_0\) and every spanning \(F\subseteq Q_n\) with \(|E(F)|\ge\delta|E(Q_n)|\) satisfies
\[
M_k(F)\ \ge\ \eta_k(\delta)\,\gamma_k\binom nk 2^{n-k}?
\]

**Status: conjectural formulation, not confirmed novel, potentially false.**
- The \(k=5\) exception is **mandatory**: Grebennikov–Marciano prove \(\operatorname{ex}(Q_n,C_{10})>0.036 |E(Q_n)|\) (arXiv:2402.19409, revision 2026-07-27). Such a graph has \(M_5(F)=0\).
- Check other \(k\) for positive-density \(C_{2k}\)-free or maximal-support-cycle-free constructions; a general \(C_{2k}\)-existence theorem does **not** automatically force a positive proportion of *maximal-support* cycles.
- It might follow from known hypercube supersaturation, counting/removal or density-increment results; literature audit must decide **before** making novelty claims.
- The original proposal begins at \(k=4\) as its first specific test: \(M_4(F)\stackrel?{\ge}\eta_4(\delta)\,648\binom n4 2^{n-4}\).

### First concrete proof/disproof route

1. Fix \(k=4\). Enumerate all full-four-direction \(C_8\)'s in \(Q_n\) for moderate \(n\) using the current centered support oracle. Confirm \(\gamma_4=648\) per \(Q_4\).
2. Evaluate exact \(M_4(F)\) and edge density for known layer-deletion, parity, level-modular, direction-restricted and \(C_{10}\)-free constructions, keeping each result as a *finite counterexample search*, not a proof.
3. Form the \(2k\)-uniform hypergraph \(\mathcal H_{n,k}\) whose vertices are edges of \(Q_n\) and whose hyperedges are maximal-support \(C_{2k}\)'s. Translate MSCS(k) into the supersaturation/density problem for this explicit hypergraph family. Check codegrees and link graphs before applying removal/regularity.
4. Seek a uniform density-to-count lemma for the *specified support type*, not merely all \(C_{2k}\). Compare with known cube hypergraph supersaturation and \(C_{2k}\)-Turán results. Prove a restricted class first (regular/layer-symmetric \(F\), if tractable).
5. Any high-density counterexample family should be published as an explicit falsification, with exact support convention and asymptotic density established.

### Role of the nb/primitive deficit

Let \(b_{2k}=\operatorname{tr}(B^{2k})\), \(p_{2k}\) the oriented primitive cyclic classes, \(\Delta_k=p_{2k}-2c_{2k}\). A possible attack would bound a *support-refined* primitive quantity from below and subtract a *support-refined* repeated-vertex defect. Merely proving a global top-symbol identity for \(\Delta_k\) does **not** control \(M_k(F)\) in arbitrary subgraphs: finite differences on a Cartesian graph ring and density restrictions on \(F\subseteq Q_n\) are different operations. A bridge lemma must explicitly couple them, e.g. through a positive localized counting identity or an inequality with verified signs.

## Hamilton-cycle direction-profile bridge (separate conjectural program)

For a cyclic coordinate-flip word let its profile be \((x_1,\dots,x_n)\), where \(x_i\) counts flips in coordinate \(i\). Necessary constraints for a Hamiltonian \(Q_n\)-cycle are
\[
\sum_i x_i=2^n,\quad x_i\equiv0\pmod2,\quad 2\le x_i\le 2^{n-1}.
\]
The **Hamilton-cycle profile conjecture** asks whether every tuple satisfying these conditions occurs (see Joshua Erde, *Matchings in the hypercube with specified edges*, arXiv:2404.03950; also MathDB problem reference https://mathdb.com/p/362623/hamilton-cycle-profile-conjecture-for-the-hypercube).

Our connected-chord certificate treats the **different** regime \(L=2k\) with all used \(x_i=2\). It does not solve Hamiltonian profile realization. An appropriate bridge conjecture would be an explicitly checkable **profile-preserving reroute lemma**: identify classes of paired-word local replacements that eliminate repeated prefix-parity states without changing the coordinate-use profile, and give necessary obstruction certificates when no such replacement exists. One must handle variable word length \(2^n\) separately from the minimal full-support length \(2k\). Do not claim every primitive nonbacktracking word admits such a reroute.

## Relation to important established/open questions

- Hypercube Turán densities for \(C_4\) and \(C_6\): established literature targets. Neither is solved by a count of ambient maximal-support configurations; compare only exact statements.
- Generalized Turán bounds for \(C_{2k}\) avoiding \(C_6\), and vice versa: the \(z_{k,k}\) identity is a **direct definitional bridge**, useful for exposing the connected-chord sequence in existing formulas.
- \(C_{10}\) positive density: known obstruction; do not relabel as conjectural.
- Hamilton direction profiles: a second **conditional route**, with a large length/profile gap needing its own proof.
- Ihara/Hashimoto primitive counts: potentially a mechanism via a quantitative repeated-vertex defect inequality, **not** a theorem transfer yet.

## Acceptance and novelty gates

1. Align \(z_{k,k}\), \(\gamma_k\) and \(M_k\) cycle normalization from the primary 2023 paper and repository proof; obtain a table of small-\(k\) direct matches.
2. Search existing maximal-support supersaturation/density theorems and counterexamples before novelty language, with locators and explicit hypotheses. Route literature authority to [novelty-lab #32](https://github.com/larsbx/novelty-lab/issues/32).
3. Reproduce \(k=4\) finite density/count fixtures and demonstrate a nontrivial restricted lower bound or a counterexample.
4. Do **not** promote conjectures to proved/accepted status in this bootstrap, non-accepting repository; keep manuscript/source recovery gate #2 / PR #11 and draft #16 separate.

## Primary references (verify the exact result/edition at use)

- Axenovich, Benz, Offner, Tompkins (2023), *Generalized Turán densities in the hypercube*: https://doi.org/10.1016/j.disc.2022.113238 ; preprint https://arxiv.org/abs/2201.04598.
- Grebennikov, Marciano, *C10 has positive Turán density in the hypercube*, arXiv v4 revised 2026-07-27: https://arxiv.org/abs/2402.19409.
- Erde, *Matchings in the hypercube with specified edges*: https://arxiv.org/abs/2404.03950.
- [GPR PR #14](https://github.com/larsbx/graph-product-ring-research/pull/14) and [draft PR #16](https://github.com/larsbx/graph-product-ring-research/pull/16).

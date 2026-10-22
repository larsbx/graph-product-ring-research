# All-length ordinary even-cycle principal symbol — proof candidate (2026-10-22)

**Status:** **working proof note**, not yet promoted to `proved`. Depends on the exact graph-ring differential convention and the source provenance gate in issue #2. Independently executed finite checks are on draft PR #15. The connected-chord-diagram sequence and recurrence are prior art; no originality claim is made for them.

## Statement

Let \(c_{2k}(G)\) be the number of **ordinary, non-induced, unoriented, unrooted** simple \(2k\)-cycle subgraphs of a finite simple graph \(G\), for \(k\ge2\). Let \(\varepsilon(G)=|V(G)|\), \(d(G)=|E(G)|\), and use the augmented graph-product differential-order convention in which a \(k\)-argument symbol is obtained by \(k-1\) iterated Leibniz defects.

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

## Lemma 1: support-defect identity

For a connected graph \(F\) with at least two vertices and \(q\ge1\), set \(N_F^{\rm full}(G_1,\ldots,G_q)\) to be the number of (ordinary, non-induced) copies of \(F\) in the Cartesian product whose projections to **all** \(q\) factors are nonconstant. Then

\[
(\widetilde\delta_{G_1}\cdots\widetilde\delta_{G_{q-1}}N_F)(G_q)
=N_F^{\rm full}(G_1,\ldots,G_q).
\]

*Proof.* Partition copies by their **unique** set \(T\subseteq[q]\) of nonconstant coordinates. Constants in the other factors can be chosen in \(\prod_{i\notin T}\varepsilon(G_i)\) ways. Expanding the \(q\)-argument iterated augmented defect by inclusion–exclusion, the multiplier attached to support \(T\) is
\(\prod_{i\notin T}\varepsilon(G_i)\sum_{T\subseteq S\subseteq[q]}(-1)^{q-|S|}\), which is 0 unless \(T=[q]\) and is 1 otherwise. No cancellation among distinct copies remains. This requires \(N_F(K_1)=0\), true for \(|V(F)|\ge2\). \(\square\)

## Lemma 2: at most k active directions

In a closed \(2k\)-step cycle of any Cartesian product, each nonconstant projected coordinate must change on at least **two** cycle edges: its projection is a closed walk with at least one non-loop move, and a single non-loop move cannot close. Every cycle edge changes exactly one coordinate. Thus a \(2k\)-cycle uses at most \(k\) coordinates.

If it uses **exactly \(k\)** coordinates, it changes every coordinate **exactly twice**. Its factor projection therefore walks along a single undirected edge and back. Hence each full-support copy lies in a **unique** subcube
\(e_1\square\cdots\square e_k\cong Q_k\), where \(e_i\) is a chosen undirected edge of \(G_i\). This uniqueness is why the cycle count factors through \(\prod_i d(G_i)\).

It follows from Lemma 1 that the \((k+1)\)-argument defect vanishes identically, so the differential order is at most \(k\).

## Lemma 3: paired flip words and chord diagrams

Inside \(Q_k\), an oriented, vertex-rooted \(2k\)-cycle that changes all \(k\) coordinates is given by:

1. a chosen starting vertex (there are \(2^k\));
2. a sequence of \(2k\) coordinate flips, each of \(k\) named coordinates occurring exactly twice.

After forgetting the names of the coordinates, each such flip sequence is a perfect matching of the \(2k\) **ordered positions**; conversely the \(k!\) names can be assigned to its pairs.

Let \(s_t\in(\mathbb F_2)^k\) be the vector of parity counts among the first \(t\) flips. The cycle is simple iff \(s_a\ne s_b\) for all \(0\le a<b<2k\). Equality means exactly that some nonempty proper (linear, equivalently cyclic) interval of flip positions contains **both or neither endpoints of every chord**.

For a chord matching \(M\), such a proper pairing-closed interval exists **iff** the chord-intersection graph of \(M\) is disconnected:

- A pairing-closed cyclic interval splits the matching into chords internal and external to the interval; no chord in one group crosses a chord in the other.
- Conversely, suppose the crossing graph is disconnected and choose one connected component \(C\) of chords. An induction that adds the chords of \(C\) along a spanning tree of crossings shows: any chord crossing **none** of \(C\) has both endpoints within one of the circular gaps between successive endpoints of \(C\). (For a single chord it is immediate; when a new chord crosses an existing component, any outside chord crossing none of the enlarged component must lie on one side of the newly inserted endpoint inside its old gap.) Because \(M\) has a chord outside \(C\), at least one such gap is nonempty. Its marked positions form a proper cyclic interval closed under pairing.

Thus **simple full-\(k\)-direction cube cycles correspond exactly to connected chord diagrams** on \(k\) chords. The number of acceptable unnamed flip-word matchings is \(a_k\).

An explicit positive witness for every \(k\ge2\) is the word
\(1,2,\ldots,k,1,2,\ldots,k\); the corresponding chord diagram has all chords crossing.

## Proof of the candidate theorem

By Lemmas 1–2 the \(k\)-argument defect counts all simple \(2k\)-cycles of full support in \(G_1\square\cdots\square G_k\), each residing in its unique selected edge-cube. For one selected cube, by Lemma 3 there are
\(2^k k!a_k\) **oriented vertex-rooted** cycles. Every undirected, unrooted simple \(2k\)-cycle has exactly \(2(2k)=4k\) such descriptions. Hence one cube contains

\[
\frac{2^k k! a_k}{4k}
=2^{k-2}(k-1)!a_k
\]

full-support simple cycle subgraphs. Multiplying by the \(\prod_i d(G_i)\) independent choices of factor edges gives the asserted \(k\)-argument symbol formula. Lemma 2 supplies the upper order bound. Positivity of \(a_k\), witnessed explicitly above, supplies a \(k\)-argument nonzero evaluation on \(K_2,\ldots,K_2\), hence the exact order \(k\). \(\square\)

## Exact coefficients / consequences

| k | a_k (OEIS A000699) | gamma_k = 2^(k-2)(k-1)!a_k | status |
|--:|--:|--:|---|
| 2 | 1 | 1 | known / checked |
| 3 | 4 | 16 | known / checked |
| 4 | 27 | 648 | previous paper / checked |
| 5 | 248 | 47,616 | previous paper / checked |
| 6 | 2,830 | 5,433,600 | previous paper / checked |
| 7 | 38,232 | **880,865,280** | two independent cycle oracles + chord matching / checked in PR #15 |
| 8 | 593,859 | **191,555,159,040** | analytic prediction from the candidate theorem |
| 9 | 10,401,712 | **53,682,819,563,520** | analytic prediction |
| 10 | 202,601,898 | **18,821,165,247,037,440** | analytic prediction |

The original Paper III table's \(c_{14}(Q_7)=406,517,760\) and \(\gamma_7=-2,049,830,400\) are contradicted. Independent exact enumeration in PR #15 gives \(c_{14}(Q_7)=3,337,213,440\) and \(\gamma_7=+880,865,280\).

The connected-chord recurrence
\(a_0=a_1=1\) and \(a_k=(k-1)\sum_{i=1}^{k-1}a_i a_{k-i}\)
is **established prior art**, not a project result: https://oeis.org/A000699 . The proposed novelty is only the precise graph-ring **full-support-symbol identification**, subject to a targeted comparison with product-graph cycle enumeration.

## Acceptance checklist

- [ ] Independently review the pairing-closed interval / connected-chord implication for **all k**, not just k=7 exhaustive predicate comparison.
- [x] Confirm k=7 by two independent cycle enumerators and a 135,135-case chord/cube bijection check (PR #15).
- [ ] Replay with a properly installed Mojo SDK; the draft Mojo source in PR #15 remains **unexecuted** until its workflow succeeds.
- [ ] Fix the counting convention and `Diff^n_epsilon` symbol indexing by importing the authoritative manuscript in issue #2.
- [ ] Consult novelty-lab issue #32 for exact literature precedence of the graph-ring symbol statement.
- [ ] Only then request promotion of a new claim in `proof/claims.toml`.

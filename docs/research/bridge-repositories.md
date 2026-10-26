# Research bridge repository map

Recorded 2026-10-26 from the user's selected repository names.

This is the coordination index in the source mathematics repository. It records
verified destinations and first obligations. Provisioning and bootstrap results
are recorded below; merging an initialization PR does not promote mathematical claims.

## Repository allocation

All names below are under the intended owner `larsbx`.

| Repository | Scope | First concrete obligation |
| --- | --- | --- |
| [even-cycle-calculus-research](https://github.com/larsbx/even-cycle-calculus-research) | Complete ordinary even-cycle product formulas below the known top symbol. | Derive the lower-support c8 terms, classify four-step and paired triangle projections, and validate injectivity/collision corrections against independent product enumeration. |
| [cartesian-support-rank-research](https://github.com/larsbx/cartesian-support-rank-research) | Coordinate-support rank r*(H), embedding certificates, and its relationship to augmented differential order. | Pin the embedding convention, build independently checkable support certificates, and test the project question r*(G square H)=r*(G)+r*(H) without assuming the upper bound. |
| [hypercube-cycle-extremal-research](https://github.com/larsbx/hypercube-cycle-extremal-research) | Coordinate-stratified cycle inventories, forbidden-cycle subgraphs, and candidate supersaturation bounds. | Validate support-stratum counts on edge-deleted cubes; seek an inequality relating retained edges to surviving cycles. The full-product symbol theorem alone supplies no such inequality. |
| [chord-diagram-symbols-research](https://github.com/larsbx/chord-diagram-symbols-research) | Transfer established connected-chord-diagram enumeration to graph-symbol coefficients, with exact normalizations and prior-art attribution. | Reuse the existing all-k component-and-gap proof and finite checks; reconcile recurrence/asymptotic sources and remaining acceptance obligations rather than redoing the already recorded bijection. |
| [vizing-coordinate-support-research](https://github.com/larsbx/vizing-coordinate-support-research) | Explore coordinate-support/overlap inequalities for domination witnesses. | Formulate and falsify a concrete candidate inequality relating support data to dominating-set size; no domination bound follows from additive cycle counts alone. |

## Current provisioning status

**Completed 2026-10-26:** all five destinations were created as public
repositories under `larsbx`, then confirmed through authenticated metadata reads
with admin, push and pull access. Each initialization PR #1 passed its hosted
`Pinned bootstrap replay` workflow and was merged with an expected-head check.
Local validation also checked pinned source digests, inherited claim statuses
and exact receipt reproduction. No repository-creation permission limitation
remains for this milestone.

| Repository | Bootstrap commit | Merged main commit | Initialization PR |
| --- | --- | --- | --- |
| [even-cycle-calculus-research](https://github.com/larsbx/even-cycle-calculus-research) | [b5228e0](https://github.com/larsbx/even-cycle-calculus-research/commit/b5228e00c8f6d4ece55153754ab4fa0fbf048460) | [42cfd84](https://github.com/larsbx/even-cycle-calculus-research/commit/42cfd84dfe4251bc6aef92683bd77144cc76a7e8) | [#1](https://github.com/larsbx/even-cycle-calculus-research/pull/1) |
| [cartesian-support-rank-research](https://github.com/larsbx/cartesian-support-rank-research) | [c2be9ca](https://github.com/larsbx/cartesian-support-rank-research/commit/c2be9ca2a885ea16dcac519ef1742fbabcae789f) | [59f28e5](https://github.com/larsbx/cartesian-support-rank-research/commit/59f28e51b061a0bba527787db7c97e40a0f7db0c) | [#1](https://github.com/larsbx/cartesian-support-rank-research/pull/1) |
| [hypercube-cycle-extremal-research](https://github.com/larsbx/hypercube-cycle-extremal-research) | [30e9c18](https://github.com/larsbx/hypercube-cycle-extremal-research/commit/30e9c1862453f893cb5986ea3990243f20e37ff8) | [c20cf12](https://github.com/larsbx/hypercube-cycle-extremal-research/commit/c20cf1244f597a6f4a896ddf3f61da7c91fe05b3) | [#1](https://github.com/larsbx/hypercube-cycle-extremal-research/pull/1) |
| [chord-diagram-symbols-research](https://github.com/larsbx/chord-diagram-symbols-research) | [a8c00d7](https://github.com/larsbx/chord-diagram-symbols-research/commit/a8c00d72a17c2024ca727dc4dafbbb07f7c2a5e5) | [1391205](https://github.com/larsbx/chord-diagram-symbols-research/commit/1391205162672cbdcc0a9db0ff839c16a685c140) | [#1](https://github.com/larsbx/chord-diagram-symbols-research/pull/1) |
| [vizing-coordinate-support-research](https://github.com/larsbx/vizing-coordinate-support-research) | [c387fd8](https://github.com/larsbx/vizing-coordinate-support-research/commit/c387fd8aeea0198add2632fd2119ad45f2f0c307) | [192f515](https://github.com/larsbx/vizing-coordinate-support-research/commit/192f515accc91fc51e70712b57d9225e8051acd7) | [#1](https://github.com/larsbx/vizing-coordinate-support-research/pull/1) |

The [machine-readable provisioning receipt](../../conformance/receipts/bridge-provisioning-2026-10-26.json)
records full commit hashes, repository IDs, permissions and successful PR-head
workflow run IDs. Each destination includes its own deterministic
`conformance/first.json`, `sources.lock.json`, claim registry and
`REPRODUCING.md`. Source pin remains `28d0224` throughout this bootstrap.

### First experiments delivered

- **Even cycles:** independent ordinary c8 vertex inventory on five products;
  Q4 has 696 copies, split into 648 full-support and 48 lower-support copies.
  K2 square K3 square K3 supplies 1,404 copies with step profile (2,3,3).
  The complete lower-support formula and collision classification remain open.
- **Support rank:** all edge partitions on six specified graphs, explicit
  injective embedding certificates and invalid-map controls. Small product
  maxima agree with additivity; reduction completeness and a general upper
  bound remain proof obligations, not assumptions of the search.
- **Hypercube extremal:** independent edge-subset cycle inventory over all
  4,096 spanning edge-deleted Q3 subgraphs, stratified by support. The full
  cube counts (c4,c6,c8)=(6,16,6); no dimension-uniform inequality is inferred.
- **Chord symbols:** replay of the existing pinned matching/prefix and
  recurrence oracles, including all 2,027,025 eight-chord matchings with zero
  mismatches. Existing component-and-gap proof authority is reused; remaining
  prior-art and acceptance obligations are explicit. No Q8 cycle enumeration.
- **Vizing support:** exhaustive domination subsets on Pn square Pm for
  2<=n,m<=4 falsify a projection-only bound. A size-three dominating set in
  P2 square P4 contradicts that candidate's bound four. The candidate is
  retracted; an overlap-sensitive replacement remains open. Vizing's usual
  conjecture and the existing independent program are not refuted or promoted.

Earlier authenticated 404s are historical observations of unverified
access/existence, not successful provisioning. They are superseded by the
successful creation, authenticated reads and merged bootstrap records above.

## Shared source and ownership

Source snapshot for this allocation:
[`graph-product-ring-research@28d0224`](https://github.com/larsbx/graph-product-ring-research/tree/28d022402037274a9fe85c1fd64ecda2532dceb9).

Pinned inputs:

- [Ordinary even-cycle support/order/symbol proof](https://github.com/larsbx/graph-product-ring-research/blob/28d022402037274a9fe85c1fd64ecda2532dceb9/proof/even-cycle-order-symbol.md).
- [All-k chord identification and coefficient record](https://github.com/larsbx/graph-product-ring-research/blob/28d022402037274a9fe85c1fd64ecda2532dceb9/docs/research/c2k-chord-symbol-all-k-proof-2026-10-22.md).
- [Claim registry](https://github.com/larsbx/graph-product-ring-research/blob/28d022402037274a9fe85c1fd64ecda2532dceb9/proof/claims.toml).

The source repository retains shared graph-ring foundations and existing proof
records. Destination repositories should cite immutable source revisions and
explicitly record any subsequent divergence, rather than silently forking theorem
authority. Shared executable kernels should be reused through pinned estate
dependencies where suitable; a language port or passing experiment is not a proof.

The Vizing bridge complements
[`larsbx/vizing-domination-conjecture-research`](https://github.com/larsbx/vizing-domination-conjecture-research),
which retains the existing domination research program, corpus provenance,
row-CSP evidence, and its own acceptance decisions. The bridge does not replace it.
Literature and novelty decisions remain coordinated with `larsbx/novelty-lab`.

## Bootstrap requirements for each destination

1. README with scope, non-goals, pinned inputs, and distinction between inherited
   evidence and new hypotheses.
2. Roadmap with a first reproducible experiment or proof obligation from the table.
3. Claim registry distinguishing imported results, working proofs, finite
   computations, conjectures, and retractions; preserve source claim status.
4. Independent replay instructions and provenance for any imported code/data.
5. Cross-link back to this index and to relevant sibling repositories after
   their existence/access is verified.

The manuscript source/lineage and mathematical/novelty review gates remain in
force. Repository allocation and merging this note change no theorem status.

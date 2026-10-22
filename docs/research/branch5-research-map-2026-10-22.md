# Branch 5 research map: cycle/walk symbols and adjacent open problems

Snapshot: 2026-10-22. **Non-authoritative map, not a manuscript or a promotion.**
This note captures the six future-direction areas and the subsequent nb / hypercube research conversations, without reviving superseded claims.

## Where each direction belongs

| Area from original future-work section | Correct estate treatment | Current boundary |
| --- | --- | --- |
| (1) Fiber-capture recognition | Existing [GPR-SPRIME](../../proof/claims.toml) and [novelty-lab N6 audit](https://github.com/larsbx/novelty-lab/issues/32) | unrestricted fiber-capture is established **Cartesian S-prime** prior art; do **not** present recognition as a newly open problem |
| (2) Approximate products / local certificates | background only; formulate a genuinely **restricted** new predicate before a new claim | no novelty transfer from approximate-product recognition by analogy |
| (3) Other multiplicative graph characters | existing research roadmap Phase 4C | separate derivation module at component-count or other characters; no claim currently closed |
| (4) Hopf/Tutte incidence compatibility | existing [GPR-HOPF-BRIDGE](../../proof/claims.toml) and [novelty-lab #33](https://github.com/larsbx/novelty-lab/issues/33) | require exact bialgebra compatibility or obstruction before a new Hopf claim |
| (5) Simple cycles / walk symbols | **primary branch here**: [nb/primitive](nb-primitive-symbol-bridge-2026-10-22.md) and [hypercube/extremal](hypercube-maximal-support-bridges-2026-10-22.md) | distinguish full-ring *working* ordinary-cycle symbol theorem from unaccepted nb proof candidate and open supersaturation conjectures |
| (6) Domination and Vizing | downstream [Vizing research repository](https://github.com/larsbx/vizing-domination-conjecture-research) | no domination consequence without a pinned, hypothesis-preserving transfer and an independent proof in its owning repo |

## New branch workstreams, in dependency order

**A. Simple even cycles (existing source of record).** [GPR support/order proof](../../proof/even-cycle-order-symbol.md) establishes a working all-\(k\) centered full-support theorem on the full Cartesian ring. [Draft #16](https://github.com/larsbx/graph-product-ring-research/pull/16) proposes the connected-chord identification and still has acceptance/novelty/manuscript gates. Earlier c14 negative-number claims are retracted; the corrected coefficient is +880,865,280.

**B. nb/primitive extension (new memo).** Three original blockers were global purity, an alternating coefficient positivity proof, and conjectural junction recursion. An exact support-word counting proof candidate may resolve the first blocker and prove positivity of the *nonbacktracking cube coefficient*. This must be checked against the nb manuscript's separate \(a_k\) notation before marking its original positivity lemma closed. The junction recursion remains conjectural.

**C. Extremal bridge (new memo).** Under aligned counting conventions, \(z_{k,k}=\gamma_k\) turns a full-support graph-ring coefficient into a parameter of published generalized hypercube Turán bounds. That is a definitional/synthetic bridge, **not** a new extremal theorem. Candidate maximal-support supersaturation MSCS(k) is open here and explicitly fails for \(k=5\) because of the published positive-density \(C_{10}\)-free construction.

**D. Hamiltonian direction profiles (separate, longer-term bridge).** Paired-coordinate connected-chord words suggest local reroutes, but the prescribed Hamilton-cycle profile problem needs \(2^n\) steps rather than \(2k\); preservation of every admissible profile has no present proof.

## Governance / handoff

- Repository/domain authority: `graph-product-ring-research` for mathematical working claims; `novelty-lab` for prior-art decisions; other repositories remain consumers only.
- Claims: entries in [proof/claims.toml](../../proof/claims.toml) are status-labeled and do not independently certify mathematical novelty.
- Experimental counts must land in `oracles/`, `experiments/` or `conformance/` with explicit provenance/negative controls; no empty language silos or premature kernel authority.
- Keep the current `ESTATE.toml` migration/bootstrap state and paper source-provenance gate intact; do not fake new registry membership or hand-edit the generated [estate registry](https://github.com/larsbx/estate-governance/blob/main/policy/estate-registry.toml).
- This is a branch memo package; publication, source reconstruction, claim promotion and merge are separately gated.

## Specific next checks

1. Formalize and independently test the global support-word proof for \(\sigma_k(b_{2k})\); compare \(K_2^k\), mixed nonregular factors and direct Hashimoto traces.
2. Recover the exact nb TeX definitions of \(a_k^{\rm nb}\); either prove its positivity from the word model or explicitly retain that open gap.
3. Build a repeated-vertex partition-state automaton; derive, rather than guess, junction coefficients at \(k=4\).
4. Check \(z_{k,k}\) convention against the Axenovich et al. text, plus locate any known MSCS-type supersaturation result/counterexample.
5. Use \(k=4\) as the first extremal falsification target; maintain the \(C_{10}\)/\(k=5\) obstruction as a negative control.

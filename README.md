# graph-product-ring-research

Research repository for the algebra and combinatorics of finite graphs under
**disjoint union** and **Cartesian product**.

The project studies:

- the graph semiring / Grothendieck-ring viewpoint for ((\sqcup,\square));
- multiplicative graph characters;
- derivations and higher-order differential operators at graph characters;
- ordinary cycle and closed-walk product identities;
- Cartesian S-prime structure where it is consumed as **prior art**, not renamed as a new graph class;
- exact computational verification of finite claims;
- possible compatibility with graph Hopf/Tutte/quantum-graph frameworks.

## Prior-art boundary

The October 2026 N6 literature audit in `larsbx/novelty-lab` materially
redirected this program:

- unrestricted “fiber-captured” = established Cartesian **S-prime** theory;
- unrestricted S-prime characterization and recognition complexity are prior art;
- the abstract polynomial/monoid-ring and generic differential-calculus layers
  are classical or routine consequences once Cartesian unique factorization is
  imported;
- residual research emphasis belongs on **exact invariant-specific theorems**:
  ordinary-cycle product formulas, restricted walk-symbol results, compatible
  algebraic bridges, and verified restricted consequences.

This repository must therefore distinguish **imported classical structure**,
**reformulation/synthesis**, **new theorem candidates**, **finite computation**,
and **open conjecture**.

## Authority model

- `proof/` — claim registry and proof records.
- `kernel/` — canonical executable verification only after promotion.
- `oracles/` — independent/non-authoritative cross-checks.
- `experiments/` — exploratory computation; never theorem authority.
- `paper/` — manuscript source and publication artifacts.
- `docs/research/` — roadmap, literature handoffs, theorem notes.
- `docs/audits/` — audits and review records.
- `conformance/receipts/` — replayable finite evidence.

See [ARCHITECTURE.md](ARCHITECTURE.md) and
[proof/claims.toml](proof/claims.toml).

## Immediate priorities

1. Import the current manuscript and verification package with provenance.
2. Reconcile manuscript terminology with Cartesian S-prime prior art.
3. Reproduce the exact (C_4), (P_3), and (C_6) product formulas.
4. Reproduce the bipartite and triangle-free walk-symbol theorem suite.
5. Audit the residual novelty of exact cycle/walk claims against
   `novelty-lab#32`.
6. Run the compatibility gate for a Cartesian-product/Hopf-Tutte bridge
   tracked in `novelty-lab#33`.
7. Open the next exact target: (c_8) / general (c_{2k}) order and symbol.

## Claim boundary

A clean build or passing numerical experiment does not establish novelty or a
general theorem. Search misses do not establish absence of prior art. Any
theorem-facing result must identify its imported hypotheses, exact statement,
proof/evidence path, and current claim status.

## Reproducible finite correction

The [exact c14 cube record](docs/research/c14-exact-cubes.md) supplies two
independent enumeration paths and regression tests. It gives
`c14(Q7)=3,337,213,440` and seven-factor support defect `+880,865,280`,
rejecting the old Q7 table and negative-symbol narrative. This is finite
evidence pending review; universal symbol classification and the manuscript
source-provenance gate remain separate. Replay with
`python3 -m unittest discover -s tests -v` (Python >=3.10 and g++ required).

# Architecture

Status: bootstrap architecture for a dedicated graph-product research repository.

## Domain

Primary domain: finite graph invariants under Cartesian product, with additive
completion under disjoint union.

The repository owns the **project-specific mathematics and evidence**. It does
not own classical Cartesian S-prime theory, generic commutative-algebra
differential operators, or standard Kronecker-sum spectral identities.

## Authority surfaces

### `proof/` — mathematical claim plane

Every project-facing claim has one status:

- `imported`: external theorem/fact used with an explicit locator;
- `conjectural`: open target;
- `working`: argument or computation exists but is not yet promoted;
- `computed`: exact finite statement reproduced by checked-in code/data;
- `proved`: repository proof record independent of exploratory scripts;
- `retracted`: retained for provenance but no longer asserted.

### `kernel/` — canonical executable plane

A future canonical kernel may replay:

- graph products and invariant values;
- exact cycle/walk product formulas on finite fixtures;
- iterated normalized commutators;
- certificate checks for bounded claims.

Bootstrap state: no acceptance authority.

### `oracles/`

Independent cross-checks: brute force, alternative graph libraries, symbolic
algebra, enumeration engines, and intentionally redundant implementations.

### `experiments/`

Exploration only. Regression discovery belongs here until the claim is promoted.

### `paper/`

Publication source. The paper is a projection of the claim state, not an
independent authority source.

### `docs/literature/`

Local copies/notes of literature decisions may point to the canonical N6
literature gate in `larsbx/novelty-lab`. Do not fork novelty decisions
silently.

## Prior-art boundary

The following are imported/classical unless a narrower theorem is separately
shown to be new:

- Cartesian unique prime factorization;
- the polynomial/monoid-ring specialization induced by that factorization;
- generic derivations/differential operators on polynomial rings;
- standard adjacency Kronecker-sum and closed-walk convolution;
- Cartesian S-prime characterization and unrestricted recognition complexity.

The descriptive alias “fiber-captured” may appear only as
**fiber-captured (Cartesian S-prime)** at first mention when historical
manuscript continuity requires it.

## Current research branches

1. **Exact ordinary-cycle formulas**
   - reproduce and audit (c_4), (P_3), (c_6);
   - determine (c_8);
   - formulate the general (c_{2k}) order/symbol problem.

2. **Restricted walk-symbol theorems**
   - bipartite even walks;
   - triangle-free corrections and odd-walk order;
   - exact prior-art comparison before novelty language.

3. **Other characters**
   - derivations/differential operators at characters other than vertex count.

4. **Algebraic compatibility**
   - Cartesian multiplication versus graph Hopf/Tutte/quantum-graph
     coproduct/gluing structures.

5. **Formalization**
   - import only stable theorem statements after provenance and scope are fixed.

6. **Vizing bridge**
   - export only exact restricted consequences; Vizing retains its own theorem
     authority.

## Acceptance boundary

No repository-local acceptance authority exists at bootstrap.

Promotion requires:

1. exact claim statement and status in `proof/claims.toml`;
2. checked-in proof or replayable finite certificate;
3. regression tests for the failure mode the artifact guards;
4. literature boundary recorded for theorem-facing novelty claims;
5. manuscript wording synchronized with claim status.

## Non-goals

- Do not rediscover/rebrand Cartesian S-prime theory.
- Do not infer a theorem from small-product testing.
- Do not call a routine algebraic reformulation novel.
- Do not conflate ordinary cycles, induced cycles, and closed walks.
- Do not infer Vizing-domination consequences from S-primality without a
  separate proof.

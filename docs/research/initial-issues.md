# Initial issue dependency graph

These are the first issues to instantiate in this repository after bootstrap.

## I1 — Import current manuscript and verification package

**Blocks:** I2, I3, I4, I5.

Deliver:
- current TeX/PDF;
- verification package;
- README/METHODS;
- exact version/provenance note;
- theorem-label ↔ claim-registry map.

## I2 — Reconcile Cartesian S-prime prior art

**Depends on:** I1.

Deliver:
- terminology patch;
- citations from the N6 audit;
- deletion/downgrade of superseded open questions;
- explicit distinction Cartesian-prime vs S-prime.

## I3 — Reproduce C4/P3/C6 formulas independently

**Depends on:** I1.

Deliver:
- exact graph definitions and counting conventions;
- independent implementation;
- deterministic fixtures;
- formula residual checks;
- iterated-commutator symbol checks;
- receipts.

## I4 — Reproduce bipartite / triangle-free walk theorem suite

**Depends on:** I1.

Deliver:
- exact theorem statements;
- spectral convolution oracle;
- operator-order checker;
- negative controls;
- finite fixtures;
- receipts.

## I5 — Close exact cycle/walk prior-art gate

**Depends on:** I1; external dependency `novelty-lab#32`.

Deliver:
- claim-level literature verdicts;
- manuscript wording changes.

## I6 — Cartesian/Hopf compatibility calculation

**External dependency:** `novelty-lab#33`.

Deliver one of:
- a compatible construction with checked axioms, or
- an explicit obstruction calculation ruling out the naïve bridge.

## I7 — c8 order and top symbol

**Depends on:** I3, I5.

Deliver:
- exact candidate statement;
- proof or replayable finite derivation sufficient to support the theorem;
- independent verification;
- no extrapolation to all k without a separate argument.

## I8 — General c2k conjecture

**Depends on:** I7.

Deliver:
- precise convention;
- best supported general statement;
- recurrence/structural mechanism or explicit obstruction family.

## I9 — Vizing bridge

**Depends on:** exact imported theorem worth consuming.

Deliver:
- pinned theorem locator;
- restricted VDC hypotheses;
- derived domination-specific consequence;
- regression evidence in the Vizing repo.

### Critical path

[
I1 \to \{I2,I3,I4,I5\},\quad
I3+I5 \to I7 \to I8.
]

I6 runs in parallel. I9 is consumer-driven and should not block the core.

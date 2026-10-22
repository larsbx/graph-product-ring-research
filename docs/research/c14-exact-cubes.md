# Exact ordinary 14-cycles in cubes — 2026-10-22

Status: reproducible finite computational evidence, pending repository review.
This corrects the numerical conclusions identified in PR #12, for issues #8/#9.
It does not promote a general differential-order or pure-symbol theorem.

## Convention and result

`Q_n` has vertices `{0,1}^n`, adjacent when exactly one bit differs. `c14`
counts unoriented, unrooted simple cycles of length 14, allowing chords.
Different cycle edge sets on the same vertex set are distinct. An oriented
rooted traversal has 14 distinct vertices before its final return.

| Used coordinates k | Canonical words P_k | Full-support cycles in Q_k, B_k | All cycles in Q_k |
|---|---:|---:|---:|
| 4 | 392 | 5,376 | 5,376 |
| 5 | 33,530 | 4,598,400 | 4,652,160 |
| 6 | 89,782 | 147,755,520 | 203,258,880 |
| 7 | 38,232 | 880,865,280 | **3,337,213,440** |

There are no 14-cycles in Q_0,...,Q_3. The seventh vertex-augmentation
support defect is **+880,865,280**, not -2,049,830,400. The previously
reported Q7 count 406,517,760 is rejected. Therefore the negative coefficient
and sign-reversal conclusion based on that table must not be asserted under
this ordinary-cycle convention.

## Counting and normalization proof

Represent a rooted traversal from zero by its coordinate-flip word. Every
coordinate occurs an even number of times because the walk closes; hence at
most seven coordinates occur. Replace coordinate names by 0,1,... in order of
first occurrence. This produces exactly one restricted-growth word per orbit
under coordinate permutations. For a word using all k coordinates the action
is free: every coordinate occurs, so only the identity permutation fixes it.
There are exactly k! labelled words per canonical word.

There are therefore k! P_k rooted oriented traversals starting at zero in Q_k
and using all coordinates. Translation supplies 2^k possible roots. Each
unrooted unoriented simple cycle has exactly 28 traversals (14 roots and two
orientations), even when the cycle has graph symmetries. Consequently

`B_k = 2^k k! P_k / 28`.

Each cycle in Q_n has one used-coordinate set S and one assignment of fixed
bits outside S. For |S|=k there are `C(n,k) 2^(n-k)` such faces. Restricting
to the face gives a full-support Q_k cycle; conversely every such cycle has
that unique minimal face. This proves, without double counting,

`c14(Q_n) = sum_k 2^(n-k) C(n,k) B_k`.

Binomial inversion gives the n-factor vertex-augmentation support defect

`D_n = sum_{j=0}^n (-2)^(n-j) C(n,j) c14(Q_j) = B_n`.

Indeed the coefficient of B_k is
`C(n,k) 2^(n-k) sum_{j=k}^n (-1)^(n-j) C(n-k,j-k)`, which vanishes
unless k=n, when it is one. This establishes the cube-specific support
identity, including its nonnegativity, independently of general graph-ring
order arguments.

## Two enumeration paths

1. `oracles/cube_cycles.py` enumerates restricted-growth coordinate words.
   Vertices are XOR bit masks. A set rejects any vertex repetition before the
   final return. The only search pruning uses Hamming distance to the origin;
   this cannot exceed the remaining number of flips. No expected counts are
   used by this enumerator.
2. `oracles/labelled_cube_cycles.cpp` directly traverses adjacent labelled
   cube vertices, using a boolean visited array. It fixes the first edge to
   `0 -> 1` and restores n possible first coordinates by cube symmetry. It
   uses no canonical relabelling, no support reconstruction, and no
   Hamming-distance pruning. After 13 edges, it tests adjacency to zero for
   the final edge. Counts are grouped by the actual used-coordinate mask.
   Multiplication by `n 2^n / 28` normalizes the fixed-first-edge tally.

The direct Q7 traversal's rooted oriented totals at zero are:

| Support size | Rooted traversals | Ordinary cycles in Q7 |
|---|---:|---:|
| 4 | 329,280 | 1,505,280 |
| 5 | 84,495,600 | 386,265,600 |
| 6 | 452,501,280 | 2,068,577,280 |
| 7 | 192,689,280 | 880,865,280 |

These sum to 3,337,213,440 ordinary cycles. Both implementations were
written and run in this change; independence means distinct algorithmic paths,
not an external human audit or a formal proof of their implementations.

## Replay and regression coverage

Requires Python >=3.10 and g++ with C++17; no Python packages or network access.
From the repository root run:

```sh
python3 -m unittest discover -s tests -v
```

The suite freshly enumerates all four cubes through both paths, checks each
support stratum against the face formula, verifies binomial inversion, and
rejects the old Q7 and negative defect. Small normalization controls include
Q2 squares, Q3 squares, ordinary hexagons (chords allowed), and Hamiltonian
8-cycles. The deterministic expected receipt is
`conformance/receipts/c14-cubes.json`; tests recompute it rather than trusting
it as an input to the enumerators. CI runs the same suite.

## Mathematical and provenance boundary

The verified value is `D_7(c14)(K2,...,K2)=880865280`. If the appropriate
order-seven and pure-symbol statement `sigma_7(c14)=gamma d^tensor7` is
separately established with `d(K2)=1`, then necessarily
`gamma=880865280`. A diagonal cube evaluation alone does **not** establish
that universal identity, its domain, or an upper bound on differential order.
It does give a nonzero seven-factor defect and thus rules out order below
seven under the corresponding augmented-defect convention.

Issue #8's c8 proof obligations and issue #9's general cycle-symbol problem
remain open. No extension from these counts to arbitrary Cartesian factors
is accepted here. No unrelated theorem in `proof/claims.toml` is promoted.

PR #11 / issue #2's source gate is preserved: exact v22 TeX is not recovered,
v21 is not equated with v22, and no TeX or PDF is reconstructed or replaced.
The Paper III lineage also still needs exact artifact import. This note is a
repository correction record, not a replacement authoritative manuscript.
Once authoritative sources are recovered, reconcile Paper III §7 Tables 1–2
and its dependent §9 sign narrative against this evidence; retain the old
numbers as historical errors, and only replace a universal coefficient after
its theorem's scope and normalization have been independently established.

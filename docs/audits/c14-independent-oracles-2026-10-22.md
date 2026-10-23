# Independent C14 enumeration and maximal-coordinate symbol audit — 2026-10-22

Status: exact local computational receipt; working mathematical consequence; **no proof-claim promotion**.

## Implementation order

Mojo-first executable draft in experiments/c14/c14_canonical.mojo follows the estate finite-math-kernels style, but **Mojo is not installed in the execution environment** and this Mojo file has not compiled or run. All figures below were actually reproduced by independent C++20 and Python oracles, with g++ 14.2.0 / Python 3.13.5. Replay with tools/replay_c14_independent.sh (not yet run on GitHub-hosted CI).

## Historical contradiction resolved

Paper III's original ordinary (non-induced, unoriented, unrooted) C14 table reports:

| Hypercube | Historical count | Independent corrected count |
| --- | ---: | ---: |
| Q4 | 5,376 | 5,376 |
| Q5 | 4,652,160 | 4,652,160 |
| Q6 | 203,258,880 | 203,258,880 |
| Q7 | 406,517,760 | **3,337,213,440** |

Two independent enumerators recover these corrected values:

- C++ oracle A: restricted-growth coordinate-flip sequences of length 14, returning to the origin after exactly 14 flips, with distinct intermediate vertices.
- C++ oracle B: independently constructs **all 4,373,461 even-block set partitions** of 14 flip positions and checks prefix self-avoidance only at completed partitions.

Both count the same canonical patterns P4=392, P5=33,530, P6=89,782, P7=38,232.

For each 4 <= n <= 7, set S_n = sum over k of binomial(n,k) k! Pk (number of origin-rooted oriented simple 14-cycle flip words). Then ordinary geometric cycle count c14(Qn) = 2^n S_n / 28; 28 is 14 cyclic starting points times two orientations. Specifically S7=730,015,440, hence c14(Q7)=3,337,213,440.

## Full-coordinate-support defect

The normalized seventh finite difference on seven K2 factors is

  sigma7(c14)(K2,...,K2) = 128 * sum[j=0..7] (-1)^(7-j) binomial(7,j) c14(Qj)/2^j.

The historical Q7 value yields -2,049,830,400 (mathematically impossible for a defect counting full-supported ordinary subgraph copies). The corrected Q7 value yields **+880,865,280**. Independently, exactly 38,232 maximal-coordinate patterns survive, giving 2^7 * 7! * 38,232 / 28 = **880,865,280**.

Therefore Paper III's first-negative-sign-at-k=7 claim **must be retracted**. Do not silently replace it without the exact manuscript source / counting convention provenance required by issue #2.

If the original primitive p14 symbol 2,036,229,120 is independently confirmed, the revised deficit symbol is conditionally 274,498,560 (not verified independently here).

## Third independent oracle / prior-art boundary

Python chord_matching.py enumerates all 135,135 pairings of 14 positions into seven chords and counts matchings whose chord crossing graph is connected: **38,232**. Python chord_bijection_check.py compares two independent predicates on every matching (chord-crossing connectivity vs cube-prefix self-avoidance) and finds **135,135 agreements, zero mismatches**.

The classical OEIS A000699 (connected/irreducible chord diagrams) already contains the sequence a2..a8 = 1,4,27,248,2830,38232,593859 and recurrence

  a(0)=a(1)=1, a(k)=(k-1) sum[i=1..k-1] a(i)*a(k-i).

This is prior art. See https://oeis.org/A000699 and Flajolet–Noy / Courtiel–Yeats–Zeilberger. The maximal-coordinate top-symbol candidate for ordinary simple 2k-cycles is

  gamma_k = 2^(k-2) * (k-1)! * a(k),

which agrees with the originally listed k<=6 values and yields +880,865,280 for k=7. A proof follows by noting that a full k-direction closed 2k-cycle changes each coordinate exactly twice, producing a connected chord diagram. The exact **novelty** and precise algebraic normalization of this graph-ring formulation still require separate proof/literature review under the repository authority process.

## Merge boundary

This PR is suitable for **independent verification/evidence review**, not for promoting Paper III or replacing an unimported publication source. Issue #2 controls manuscript provenance; issues #8/#9 control the cycle program and need the correction. The Mojo draft must be compiled on a Mojo-enabled estate runner before being labeled validated. Record the historical negative symbol as retracted when a future claim-registry promotion is authorized.

All executable local checks passed; no GitHub CI workflow result is claimed.

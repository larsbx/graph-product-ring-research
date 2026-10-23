# Historical nonbacktracking manuscript snapshot (Paper III)

**Status: archival / contradicted in part; not an accepted manuscript.**

- Original uploaded artifact: `nb-cycles-v4.tex`, 22,909 bytes, SHA-256
  `1f8125d5929ba2f55b950720267a2438f0dfe891e83d6e4ba791ff7256219055`.
- Companion PDF was provided in the conversation as `nb-cycles-v4.pdf`,
  288,186 bytes, SHA-256
  `267b3b93308f31486e8bbbf8b1a5b2d95a88dd23c78a21bacd56b4467cf8aadc`.
  Its binary bytes have **not** been imported in this PR; the hash is an
  identity/provenance locator, not a claim that the repository stores the PDF.
- The source was imported verbatim into `paper/historical/nb-cycles-v4.tex`,
  with its mathematical errors **unmodified** so that the correction trail can
  be audited. No claim is promoted on import.
- Distinct from the parent `ring-graphs-v22.pdf` source-of-record problem
  tracked under #2 / PR #11. This is **Paper III**, not a replacement
  `v22.tex`.

## Known invalid assertions in this historical source

- `c14(Q7)=406,517,760` is wrong for ordinary simple, non-induced cycles.
  The separately reproduced exact value is **3,337,213,440**.
- The claimed seventh symbol coefficient **−2,049,830,400** and the
  sign-change narrative are therefore wrong. Under the centered augmented
  symbol convention the correct coefficient is **+880,865,280**.
- The unrestricted all-`k` assertion `gamma'_k != 0` marked open is
  superseded by the all-`k` positive symbol formula in
  `proof/even-cycle-order-symbol.md` (currently marked working in the
  repository claim registry, pending external acceptance).
- The trace-algebra induction in the historical paper is not sufficient
  evidence to accept its all-`k` nonbacktracking symbol theorem: see
  `docs/audits/nb-v4-import-review-2026-10-23.md`.

## Authoritative locations for the verified/candidate correction

- `docs/research/c14-exact-cubes.md` — independent cube enumerators and
  exact finite correction.
- `proof/even-cycle-order-symbol.md` — support-defect theorem and all-`k`
  *working* ordinary-cycle pure-symbol proof.
- `proof/claims.toml` — claim statuses; no status promotion here.

The imported historical TeX must not be published as-is. New candidate paper
source requires an explicit corrected branch and proof review.

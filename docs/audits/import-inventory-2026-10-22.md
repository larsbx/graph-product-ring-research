# Import inventory — 2026-10-22

Status: issue #2 discovery record; no theorem promotion.

## Latest surfaced manuscript artifact

The latest manuscript artifact currently discoverable from the conversation/file
sources is:

- `ring-graphs-v22.pdf`
- native Library file
- size: 482,510 bytes
- Library file id: `libfile_ebb5f3dd10188191bcafa21ddad0f48e`
- file id: `file_00000000cd0871f7b9868fc884474905`
- created: 2026-04-24 21:19:06 UTC
- modified: 2026-04-24 21:19:11 UTC

The PDF identifies itself as **A Ring-Theoretic Framework for Graph Invariants
via Cartesian Products**, dated April 24, 2026.

Its front matter includes, among other things:

- the direct-product derivation-module correction;
- ordinary-cycle statements through (c_6);
- bipartite walk-symbol theorem;
- triangle-free all-(k) walk-symbol claims;
- the historical “fiber-captured” terminology that must now be reconciled with
  Cartesian S-prime prior art.

## Source-code gap

No `ring-graphs-v22.tex` is currently surfaced in the accessible conversation
or Library search.

The latest surfaced TeX source is:

- `ring-graphs-v21.tex`
- file id: `file_00000000b72471fb81dfb82172cb7ef1`
- uploaded: 2026-04-23 14:14:05 UTC

Therefore:

- do **not** reconstruct v22 TeX from the PDF;
- do **not** silently treat v21 TeX as byte-equivalent to v22;
- v22 PDF may be imported as a publication snapshot once its bytes are
  materialized;
- source-level manuscript work remains blocked on locating the exact v22 source
  or a later authoritative source.

## Latest surfaced verification package

The latest surfaced verification bundle is:

- `ring_graphs_verify-0.4.0.tar.gz`
- file id: `file_000000000d6071fb9319ac99a4375e79`
- uploaded: 2026-04-23 14:14:05 UTC

Companion documentation from the same upload turn:

- `ring_graphs_verify-METHODS.md`
  - file id: `file_00000000ad1871fb9efe3d4d5fb25e98`
- `ring_graphs_verify-README.md`
  - file id: `file_00000000381071fb996d54799b623968`

These are candidates for import after materialization and hashing.

## Prior-art warning

The v22 PDF predates the completed October 2026 N6 literature redirect now
recorded in `larsbx/novelty-lab`.

Accordingly, v22 is an **historical manuscript snapshot**, not a publication-ready
source-of-truth for novelty claims. In particular, unrestricted
“fiber-captured” characterization/recognition claims must be reconciled with
Cartesian S-prime prior art before publication.

## Next import steps

1. Materialize and hash `ring-graphs-v22.pdf`.
2. Materialize and hash `ring_graphs_verify-0.4.0.tar.gz` and companion docs.
3. Locate exact v22-or-later TeX source.
4. Import artifacts without status promotion.
5. Create a theorem-label ↔ `proof/claims.toml` map.
6. Run #3 prior-art reconciliation before treating the imported manuscript as
   current publication text.

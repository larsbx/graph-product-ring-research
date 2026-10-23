# Paper III v5 review candidate — build and proof-replay receipt

Date: **2026-10-23**. This is a *new candidate manuscript*; it does not
overwrite the exact historical source in \`paper/historical/nb-cycles-v4.tex\`.
The parent \`ring-graphs-v22\` source-of-record gate under issue #2 is separate.

## Rebuild

\`\`\`bash
pdflatex -interaction=nonstopmode -halt-on-error paper/drafts/nb-cycles-v5-review.tex
pdflatex -interaction=nonstopmode -halt-on-error paper/drafts/nb-cycles-v5-review.tex
python3 oracles/nb_symbol_replay_independent.py
python3 -m unittest discover -s tests -v
\`\`\`

LaTeX source was compiled locally with system \`pdflatex\` to a **5-page**
letter-size PDF and visually inspected (rendered at 110 DPI). The two-pass
compile was free of unresolved references, undefined citations and overfull
boxes. The repository does **not** store the binary PDF in this PR; the
user-facing PDF is provided separately alongside the source in the chat.

Exact source identity check: the Git blob SHA returned by the GitHub
connector for \`paper/drafts/nb-cycles-v5-review.tex\` was
\`b4ee40087f381662bbf15ba76ea934d1c345868e\`, **identical** to
\`git hash-object /mnt/data/nb-cycles-v5-review.tex\` on the compiled file.
The 15,498-byte TeX's SHA-256 was
\`a9b807827577e547b8b8ccbe6ce97e50e935c29ea09d17d325387263464248d0\`.
The locally built PDF's SHA-256 was
\`e9128cd2d4b68d0d5d31f465deba468d4bac5694db7ddfcd487c614ecfec3bf6\`.

## Show-your-work: coefficient \(k=4\)

A cycle \(C_8\) has matching numbers
\(m_0,m_1,m_2,m_3,m_4=(1,8,20,16,2)\). Thus
\[
 R_4=7!!-8(5!!)+20(3!!)-16(1!!)+2(-1)!!
    =105-120+60-16+2=31.
\]
The full-support Hashimoto coefficient is
\[
 \beta_4=2^4 4!R_4=16\cdot24\cdot31=11,904.
\]
Its oriented primitive top coefficient is \(\beta_4/8=1,488\).
The ordinary simple-cycle coefficient is \(\gamma_4=648\),
hence the aggregate repeated-vertex deficit is
\(\eta_4=1,488-2(648)=192\).

At \(k=7\), the *separate* connected-pairing and adjacency-avoiding
pairing counts are \(A_7=38,232\) and \(R_7=44,189\).
Their difference is 5,957, giving
\(\eta_7=2^7 7!(R_7-A_7)/14=274,498,560\).
The ordinary-cycle top coefficient is
\(\gamma_7=880,865,280>0\), with
\(c_{14}(Q_7)=3,337,213,440\).
This **retracts** the historically false negative-symbol claim.

## Independent finite checks

The standalone arc-DP oracle \`oracles/nb_symbol_replay_independent.py\`
does not import the canonical oracle or prior test modules. In a
separate local run it printed:

\`\`\`text
k   R_k    beta_k
2   1      8
3   4      192
4   31     11904
5   293    1125120
6   3326   153262080
7   44189  28507207680

D2 b4(P3,K3)          = 48       = 8*2*3
D2 b4(P3,C4)          = 64       = 8*2*4
D3 b6(P3,K2,K3)       = 1152     = 192*2*1*3
D3 b6(P3,K2,C4)       = 1536     = 192*2*1*4
D4 b8(P3,K2,K2,K3)    = 71424    = 11904*2*1*1*3
D3 b4(P3,K3,K2)       = 0        upper-order control
D4 b6(K2,P3,K3,K2)    = 0        upper-order control
Independent finite replay PASS
\`\`\`

Finite experiments test arithmetic and conventions; the all-order
claim is argued in the manuscript by centered support inclusion-exclusion,
the \(m\ge 2q\) support bound, and the maximal-support
one-edge-per-factor bijection. A green test does **not** independently
establish the mathematical theorem or originality.

## Repository relationships and boundaries

- Existing all-cycle candidate: \`proof/even-cycle-order-symbol.md\`.
- Existing NB/primitive working record: \`proof/nb-primitive-support-symbol.md\`
  (merged PR #23).
- Original erroneous v4 and audit: \`paper/historical/\`,
  \`docs/audits/nb-v4-import-review-2026-10-23.md\` (merged PR #21).
- Acceptance issues: #17 / #22. The nonbacktracking theorem remains
  registered as \`working\` in \`proof/claims.toml\`.
- The general junction multiplicity recursion is **not proved**.
- Novelty-lab's claim-specific and prior-art gates remain open.
- No \`proof/claims.toml\` promotion is requested by this PR.

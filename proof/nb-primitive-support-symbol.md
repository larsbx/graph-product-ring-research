# Nonbacktracking/primitive symbols by coordinate support (proof candidate)

Date: 2026-10-23. This note independently develops the Branch 5A
coordinate-word proposal previously recorded in the research memo behind
PR #19. It addresses issues #17 and #22. **Repository review status:
working**, not independently accepted/published. The result does not
depend on the invalid trace-algebra induction in historical Paper III v4.

## 1. Conventions and differential filtration

All graphs are finite simple undirected, possibly disconnected, including
the empty graph. Let \(A\) be their Grothendieck ring under disjoint union
and Cartesian product. The unit is \(K_1\), the character is
\(\varepsilon(G)=|V(G)|\), the augmentation ideal is \(I=\ker\varepsilon\),
and \(d(G)=|E(G)|\) is an \(\varepsilon\)-derivation. For \(f:A\to\mathbb Z\)
additive, let
\[
 u_G=G-\varepsilon(G)K_1,\quad
 D_q f(G_1,\ldots,G_q)=f(u_{G_1}\cdots u_{G_q}).
\]
Order at most \(r\) means \(f(I^{r+1})=0\); the principal symbol at exact
order \(r\) is \(D_r f\), *without factorial normalization*. This is the
**centered** convention of \`proof/even-cycle-order-symbol.md\`, not the
uncentered \(\widetilde\delta^{q-1}f(G_q)\) convention of historical drafts.

Let \(B_G\) be the Hashimoto matrix indexed by directed arcs \((v,w)\),
with \(B[(u,v),(v,w)]=1\) precisely if \(w\ne u\). Put
\[
 b_m(G)=\operatorname{tr}(B_G^m).
\]
It counts **rooted oriented cyclically nonbacktracking** closed walks
of length \(m\): in addition to ordinary adjacent steps, the final
and first steps cannot cancel. The length \(m\) and cyclic seam are
part of the convention. The function \(b_m\) is additive on disjoint
unions, extends to \(A\), and \(b_m(K_1)=0\).

Let \(p_m\) count oriented *primitive* cyclic nonbacktracking classes,
where the starting point is forgotten but the direction is retained.
For every \(m\ge1\), counting powers of primitive cyclic classes gives
\[
 b_m=\sum_{r\mid m}r p_r,\qquad
 p_m=\frac1m\sum_{r\mid m}\mu(m/r)b_r.
\]
This is an integral identity graph by graph; the rational linear
combination has integral values. No interpretation as unoriented
cycles is implicit.

## 2. A centered support lemma for cyclically NB closed walks

**Lemma 1 (full-support defect).** For actual graphs
\(G_1,\dots,G_q\), \(D_q b_m(G_1,\dots,G_q)\) equals the number of
rooted oriented cyclically nonbacktracking length-\(m\) closed walks
in \(G_1\square\cdots\square G_q\) which change **every** coordinate
at least once.

*Proof.* Every step of a Cartesian product changes exactly one factor.
Associate to a walk its unique set \(S\subseteq[q]\) of used factors.
For any \(T\subseteq[q]\), the contribution
\[
 \Bigl(\prod_{i\notin T}|V(G_i)|\Bigr)b_m(\square_{i\in T}G_i)
\]
counts exactly the walks with \(S\subseteq T\), with the unused
coordinates fixed. The cyclic nonbacktracking condition survives
inclusion into a fixed-coordinate fiber: immediate reversal and
the final/initial seam are properties of the same vertex sequence.
The coefficient of a fixed walk in the alternating centered sum is
\(\sum_{T\supseteq S}(-1)^{q-|T|}\), which is 1 for \(S=[q]\) and 0
otherwise. The empty term is zero because \(b_m(K_1)=0\).
Neither vertex injectivity nor bipartiteness is needed. QED.

**Lemma 2 (support upper bound).** Every length-\(m\) closed walk in a
Cartesian product of simple loopless graphs uses at most
\(\lfloor m/2\rfloor\) coordinates. Consequently,
\[
 b_m(I^{\lfloor m/2\rfloor+1})=0,\qquad
 \operatorname{ord}_\varepsilon(b_m)\le\lfloor m/2\rfloor.
\]

*Proof.* The projection to a used coordinate is a nonconstant closed
walk (after deleting stationary steps). It must contain at least two
edge traversals, since one edge cannot close in a loopless graph.
The \(m\) product steps are disjointly assigned to coordinates,
hence \(2|S|\le m\). Lemma 1 implies vanishing of every
\((\lfloor m/2\rfloor+1)\)-factor centered defect on actual graphs.
The \(u_G\) additively generate \(I\); multilinearity gives
the ideal-power vanishing on all of \(A\). QED.

## 3. Maximal support = one edge per factor

For \(k\ge2\), let \(\mathcal W_k\) be the set of **labelled**
words \(w_1\cdots w_{2k}\) over \(\{1,\ldots,k\}\) such that

1. every letter occurs exactly twice;
2. \(w_i\ne w_{i+1}\) for \(1\le i<2k\);
3. \(w_{2k}\ne w_1\) (the cyclic seam).

Let \(R_k=|\mathcal W_k|/k!\) be the number of unlabelled
pair partitions of \(2k\) cyclic positions whose blocks do not
contain adjacent positions *modulo \(2k\)*. Equivalently, label
the blocks by first occurrence; there are \(R_k\) canonical
restricted-growth words. Set
\[
 \boxed{\ \beta_k=2^k k!R_k=2^k|\mathcal W_k|\ }. 
\]

**Theorem 3 (global nonbacktracking order and symbol).**
For every integer \(k\ge2\), on the **full** finite simple graph ring
(not merely on bipartite factors),
\[
 \operatorname{ord}_\varepsilon(b_{2k})=k,\qquad
 \sigma_k(b_{2k})=\beta_k d^{\otimes k},\qquad \beta_k>0.
\]

*Proof.* Lemma 2 gives the order upper bound. In a walk of
length \(2k\) using all \(k\) product factors, every factor is
used **exactly twice**. Its projected two-step closed walk
crosses a unique undirected edge of that factor and returns.
Thus the walk determines a unique selected edge in each factor.
It lies in the Cartesian product of those edges, a \(Q_k\)
subgraph, and the chosen edge tuple can be recovered from the
walk.

Conversely, choose one edge from every \(G_i\). Choose the
starting endpoint of each edge (there are \(2^k\) vertex choices)
and a labelled word \(w\in\mathcal W_k\); flip the specified
coordinate in sequence. Each coordinate occurs twice, so the
walk closes. Since the selected factor contains just that one
edge, two *consecutive* flips of the same coordinate are
precisely immediate reversal; the cyclic seam gives the same
condition for the last and first flips. The word conditions are
therefore exactly the cyclic Hashimoto constraints.
Repeated vertices at nonconsecutive times are allowed.

This gives a bijection between full-support cyclically NB
rooted oriented walks and:
\[
 \Bigl(\prod_i E(G_i)\Bigr)
 \times\{0,1\}^{k}\times\mathcal W_k.
\]
By Lemma 1,
\[
 D_kb_{2k}(G_1,\ldots,G_k)
 =2^k|\mathcal W_k|\prod_i|E(G_i)|
 =\beta_k\prod_i d(G_i).
\]
As \(b_{2k}\) has order at most \(k\), this is its global
principal-symbol formula. The word
\((1,2,\ldots,k,1,2,\ldots,k)\) belongs to \(\mathcal W_k\)
for every \(k\ge2\), including its wraparound, so
\(\beta_k>0\). Evaluating on \((K_2,\ldots,K_2)\) proves the
order cannot be smaller than \(k\). QED.

## 4. Finite coefficient / Chebyshev identity

Let \(m_j(C_{2k})\) be the number of size-\(j\) matchings
in the **ordinary cycle** on \(2k\) position vertices. The
forbidden blocks are \(\{i,i+1\}\) for \(i\pmod{2k}\).
By inclusion-exclusion, a subset of \(j\) forbidden blocks
can occur in a pair partition only if they form a matching,
after which the remaining \(2(k-j)\) vertices can be paired in
\((2(k-j)-1)!!\) ways. Therefore
\[
 \boxed{\ 
 R_k=\sum_{j=0}^{k}(-1)^j
 m_j(C_{2k})\,(2k-2j-1)!!,\quad
 m_j(C_{2k})=\frac{2k}{2k-j}\binom{2k-j}{j}.
 \ }
\]
We set \((-1)!!=1\), and the displayed matching number is integral
(including \(m_k(C_{2k})=2\)). This is a *finite* all-order formula,
with no Gaussian integral or asymptotic assumption.

The historical regular-graph Ihara/Chebyshev calculation extracts
\[
 \beta_k^{\mathrm{Cheb}}=2^k k!
 \sum_{j=0}^k(-1)^j\,
 \frac{2k}{2k-j}\binom{2k-j}{j}
 (2(k-j)-1)!!.
\]
The expressions coincide term by term with \(R_k\). Thus the
historical \`a_k\` in \`nb-cycles-v4.tex\` is **\(R_k\)**, not the
separate connected-chord count of ordinary *simple* cycles. Its
positivity follows from the explicit allowed cyclic word
\((1,\ldots,k,1,\ldots,k)\), without the historical
Gaussian--Chebyshev positivity lemma.

For \(k=2,\dots,7\):
\[
\begin{array}{c|r|r}
 k&R_k&\beta_k\\\hline
 2&1&8\\
 3&4&192\\
 4&31&11\,904\\
 5&293&1\,125\,120\\
 6&3\,326&153\,262\,080\\
 7&44\,189&28\,507\,207\,680
\end{array}
\]
The bijection and finite formula hold for every \(k\); the table
values are finite checks rather than a proof extrapolation.

## 5. Primitive symbols and the deficit

**Corollary 4 (global primitive order and symbol).** For \(k\ge2\),
\[
 \operatorname{ord}_\varepsilon(p_{2k})=k,\qquad
 \sigma_k(p_{2k})=\frac{\beta_k}{2k}d^{\otimes k}.
\]

*Proof.* Every proper divisor \(r<2k\) has
\(\lfloor r/2\rfloor<k\). By Lemma 2, \(D_k b_r=0\), and each
\(b_r\) has order less than \(k\). Möbius inversion gives
\(D_k p_{2k}=(1/(2k))D_k b_{2k}\), while \(p_{2k}\) has order
at most \(k\). Theorem 3 shows the \(k\)-th defect is nonzero.
QED.

There is a second route to the top coefficient: any
full-\(k\)-coordinate nonbacktracking length-\(2k\) walk is
primitive. Indeed, if it were an \(h\ge2\)th power, every
coordinate would be used \(2/h\) times in the shorter closed
walk, requiring \(h=2\). But the purported shorter walk
would change every coordinate exactly once, impossible for a
closed walk in the selected edge product. Thus the \(2k\)
rootings of every oriented primitive cyclic class give
\(\beta_k/(2k)\) full-support classes.

Let \(c_{2k}\) be the ordinary non-induced simple \(2k\)-cycle
count, whose proof record is
\`proof/even-cycle-order-symbol.md\`. Write
\(\gamma_k=2^k k!a_k^{\mathrm{simple}}/(4k)\), where
\(a_k^{\mathrm{simple}}\) counts pair partitions with **no proper
closed interval**, the connected chord-diagram condition.
In particular \(\sigma_k(c_{2k})=\gamma_kd^{\otimes k}\)
under the working theorem in that separate proof record.

Define \(\Delta_k=p_{2k}-2c_{2k}\). Subtracting symbols gives the
**complete aggregate top-deficit coefficient**, for every \(k\ge2\):
\[
 \boxed{\ 
 \sigma_k(\Delta_k)=\eta_k d^{\otimes k},\quad
 \eta_k=\frac{\beta_k}{2k}-2\gamma_k
       =\frac{2^k k!}{2k}
          (R_k-a_k^{\mathrm{simple}})\ge0.
 \ }
\]
The last inequality follows directly: any full-support
*simple* cube cycle has no consecutive equal coordinate flips
(including across the cyclic seam), so its pair partition
belongs to the \(R_k\) set. This aggregate formula **does not**
establish the manuscript's partition-type junction recursion
or separate the \(\mu_\lambda\) multiplicities.

With \(a_k^{\mathrm{simple}}=(1,4,27,248,2830,38232)\) at
\(k=2,\ldots,7\), the aggregate values are
\[
(\eta_2,\eta_3,\eta_4,\eta_5,\eta_6,\eta_7)
=(0,0,192,17\,280,1\,904\,640,274\,498\,560).
\]

## 6. Validation and remaining boundaries

The separately committed \`tests/test_nb_support_words.py\` verifies
the exact coefficient identities, cyclic seam controls, a direct
Hashimoto trace on cubes, and centered defects on irregular as well
as nonbipartite factor tuples. Finite tests exercise the proof's
normalization; they do not independently prove the all-\(k\)
statements.

- This proof supersedes the *mathematical need* for historical
  Lemma 4.7/Proposition 4.8's incomplete trace-algebra induction.
  It does not claim that historical induction is now correct.
- No claim of novelty follows. Novelty-lab gates #32/#37 and the
  parent-v22 source-of-record gap remain.
- Historical \`paper/historical/nb-cycles-v4.tex\` is retained only
  in draft PR #21. Do not overwrite it with a rewritten paper
  in this proof PR.
- The \(\mu_\lambda\) junction/partition recursion requires a
  complete classification of repeated-vertex incidence, not merely
  the aggregate top-deficit formula.
- The exact all-\(k\) result is submitted as a **working proof**
  for independent review; this PR does not mark the claim registry
  \`proved\` or publish the manuscript.

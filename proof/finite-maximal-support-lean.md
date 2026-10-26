# Kernel-checked finite maximal-support words and cube walks

Scope: finite combinatorics only. This extends merged PR #27, on main at
`8c4e185fb2fd9ac987d07fa524f29d6d3949a22e`. The existing Paper III claim statuses
remain **working**, and issue #22 stays open. Kernel verification of these
statements is separate from independent mathematical acceptance, verification
of the graph-ring bridge, and prior-art assessment.

## Exact finite statements

Positions are `Pos k = Fin (k+k)`, with a fixed index zero and direction.
`Adjacent` includes integer neighbors in both directions and the last–first
seam. `Word k` consists of functions to `Fin k` whose coordinate fibers each
have cardinal two and which give different labels to adjacent positions.

`Matching k` is represented independently as a Boolean equivalence relation
on positions, all of whose classes have cardinal two, with adjacent positions
in different classes. These two-element classes are the unordered edges of a
perfect matching. The relation includes reflexivity; its off-diagonal pairs
are the matching, not graph loops. Rotation is not part of this definition.

The kernel-checked API is in namespace `GraphProductRing`:

| File | Main declarations | Statement |
|---|---|---|
| `Words.lean` | `Matching.card_blocks`, `matchingBijection`, `matching_iff_relabel` | There are k blocks; words modulo coordinate permutations biject with matchings. Equality of the forgotten matching is equivalent to existence of a label permutation. |
| `Words.lean` | `fiberEquiv`, `word_count` | Each matching has exactly k! labeled words, with no stabilizer divisor. Thus `card (Word k) = k! R k`. |
| `Words.lean` | `R_pos`, `beta_pos` | The explicit repeated word 0,…,k−1,0,…,k−1 proves Rₖ>0 and βₖ>0 for every k≥2, including the seam condition. |
| `Hypercube.lean` | `vertex_step`, `walk_closed`, `cyclic_word_no_backtrack` | Prefix-parity vertices follow the specified coordinate flip, close, and are nonbacktracking including the seam. |
| `Hypercube.lean` | `walkBijection`, `trajectory_injective`, `rooted_count` | A start vertex and word determine one actual vertex traversal, and its word is recoverable uniquely. Rooted count is βₖ=2^k k!Rₖ. |
| `Cycles.lean` | `maximal_support_primitive`, `rotationFiber`, `primitive_normalization` | Every such actual traversal has free rotation action; `(2k) card (PrimitiveClass k) = βₖ`. Direction is retained. |
| `SimpleCycles.lean` | `dihedralFiber`, `simple_normalization` | On injective cyclic vertex sequences, rotations and reversal give exactly 4k representatives; `(4k) card (UnorientedCycle k) = card (SimpleWalk k)`. |
| `MaximalSupport.lean` | `raw_closed_iff_even`, `maximal_support_twice`, `admitMaximalWord` | For arbitrary raw length-2k coordinate sequences, closure of the prefix-parity path and use of all k coordinates force every coordinate to occur twice. The cyclic adjacency hypothesis then admits exactly such a word. |

The cube is `Fin k → Bool`. Its vertices are labeled, and the starting vertex
is counted. Neither coordinate permutations nor cube translations are divided
out of actual walk counts. `CubeWalk` stores a coordinate witness and an
independently specified vertex trajectory with a checked flip at every step;
closure and uniqueness are derived. `trajectory_injective` proves that
retaining this witness does not inflate the vertex-traversal count.

The quotient used for `PrimitiveClass` is on actual vertex sequences, modulo
rotation alone. The square word 0101 repeats as a word, but its vertex sequence
0,1,3,2 has four distinct rotations. Dividing words alone by their rotation
orbits would give the wrong normalization. The proof of freeness uses the
two occurrences: a nonzero rotational symmetry would have to exchange each
pair and be a half turn; that half path flips the initial coordinate once,
so cannot return to the starting vertex.

`SimpleWalk` requires vertex injectivity before the duplicate endpoint. A
primitive walk can revisit vertices: 01012323 gives two squares sharing a
vertex and has eight distinct rotations. `UnorientedCycle` quotients only the
simple subset by both rotation and reversal. Thus the 4k divisor cannot be
applied to all rooted nonbacktracking walks as a simple-cycle count.

## Replay and small vectors

Run the commands in `formal/README.md`. The GitHub job
`lean-maximal-support` runs the same build, axiom audit, and companion replay
on pushes and pull requests. All local Lean modules build with warnings as
errors. The axiom audit permits only the three standard logical axioms
`propext`, `Classical.choice`, `Quot.sound`.

`conformance/receipts/lean-word-vectors.json` contains every canonical
restricted-growth word through k=5, rather than just aggregate constants.
`oracles/lean_word_vectors.py` independently generates restricted-growth words
and partner involutions, compares their exact sets, and directly enumerates
all labeled words and actual rotation/reversal orbits through k=4. It imports
no existing repository oracle. It compares replay output with the checked-in
vectors without modifying them; `--write` explicitly regenerates them.

| k | Rₖ | simple matching count Aₖ | βₖ |
|---|---:|---:|---:|
| 2 | 1 | 1 | 8 |
| 3 | 4 | 4 | 192 |
| 4 | 31 | 27 | 11,904 |
| 5 | 293 | 248 | 1,125,120 |

`Examples.lean` checks small finite word, seam, square-path and nonsimple-path
vectors by kernel reduction. The table's numeric Rₖ evaluations are independent
Python evidence; the general bijection, normalizations and positivity are Lean
proofs. The numeric table is not asserted to be a kernel evaluation of the
noncomputable cardinal `R`.

## Centered augmentation and exact-order boundary

No graph-ring theorem is imported as an axiom into these files. To consume the
finite coefficient in Paper III one still needs the graph-ring bridge with
vertex-count augmentation ε and centered generators
`u_G = [G] − ε(G)[K1]`, augmentation ideal I, and
`D_k f(G₁,…,Gₖ) = f(u_G₁ ⋯ u_Gₖ)`.

The finite rooted count supplies βₖ in the working proposed formula
`D_k b_(2k) = βₖ d^⊗k`. Exact order k additionally needs the global upper
bound `b_(2k)(I^(k+1))=0` and a nonzero centered degree-k evaluation.
The finite positivity theorem alone does not establish that bridge or that
upper bound on arbitrary graph-ring elements.

For the aggregate deficit Δₖ=p_(2k)−2c_(2k), retain
`D_k Δₖ = ηₖ d^⊗k`. A vanishing coefficient does not give exact order k,
nor does it imply that Δₖ is the zero function. In particular η₂=η₃=0
must not be described as a nonzero principal symbol at exact order k.
Nothing here changes the v5 correction or transfers an uncentered trace
identity to augmentation defects; `tr(Q)(K1)=−1` remains a separate warning
in the existing proof record.

## Remaining obligations, kept separate

1. **Graph-ring formal bridge.** Formalize the graph objects and additive
   completion; ε, I, centered generators, spanning of ideal powers; arbitrary
   factor coordinate-support cancellation and its upper-order bound;
   maximal-support factor-edge recovery and its edge-tuple multiplicity;
   extension to virtual/disconnected/empty graphs; primitive trace and Möbius
   filtration arguments. The cube component does not prove these steps.
2. **Mathematical review.** Independent reviewers must assess definitions,
   imported hypotheses, graph-ring scope and the interpretation of the Lean
   statements. Existing GPR-NB2K-SUPPORT, GPR-PRIMITIVE2K-SUPPORT,
   GPR-C2K and GPR-NB-DEFICIT-AGGREGATE remain working. Issue #22 is not
   closed or its acceptance checklist silently checked off by this work.
3. **Prior art.** Complete the claim-specific N6 comparison in novelty-lab
   (including #32/#37); a formal proof establishes neither originality nor
   publication priority. General junction recursion and lower-order deficit
   decomposition remain separate open work.

## Graph-ring bridge continuation

The subsequent checked Stages A–D are recorded in
[`graph-ring-lean-bridge.md`](graph-ring-lean-bridge.md). They construct the ring,
augmentation, ideal powers, actual-walk additive descent, coordinate masking and
cancellation, arbitrary-factor edge recovery and multiplicities, upper filtration,
global cyclic NB symbol on virtual factors, and separate exact order. The finite
Word/matching/orbit proofs above are reused. This continuation does not change any
Paper III claim classification or settle external acceptance or prior-art gates.

import GraphProductRing.WalkInvariant
import GraphProductRing.CartesianRing
import GraphProductRing.DiscreteGraphs
import GraphProductRing.CenteredSupport

namespace GraphProductRing
open scoped BigOperators
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2048

/-- Erasing uniquely recoverable coordinate witnesses is a bijection. -/
def productNBEquiv {q m} [NeZero m] (G : Fin q → FinGraph) :
    ProductWalk G m ≃ NBWalk (productGraph G) m := by
  apply Equiv.ofBijective (fun p => ⟨p.val.2, fun t => ⟨⟨p.val.1 t, p.property.1 t⟩, p.property.2 t⟩⟩)
  constructor
  · intro p r h
    exact product_trajectory_injective G (congrArg Subtype.val h)
  · intro w
    choose a ha using fun t => (w.property t).1
    exact ⟨⟨(a, w.val), ha, fun t => (w.property t).2⟩, rfl⟩

@[simp] theorem nb_product_count {q m} [NeZero m] (G : Fin q → FinGraph) :
    nbInvariant m (∏ a, graphClass (G a)) = (Fintype.card (ProductWalk G m) : ℤ) := by
  rw [← productGraph_class, nbInvariant_class]
  unfold nbGraphCount
  rw [← Fintype.card_congr (productNBEquiv G)]

/-- Remove edges, retaining every actual vertex and its multiplicity. -/
def maskedFactors {q} (G : Fin q → FinGraph) (T : Finset (Fin q)) : Fin q → FinGraph :=
  fun a => {G a with graph := if a ∈ T then ⊥ else (G a).graph}

@[simp] theorem masked_class {q} (G : Fin q → FinGraph) (T : Finset (Fin q)) (a) :
    graphClass (maskedFactors G T a) =
      if a ∈ T then ((G a).vertices : GraphRing) else graphClass (G a) := by
  by_cases h : a ∈ T
  · rw [if_pos h]
    change graphClass ⟨(G a).V, (G a).finiteV, if a ∈ T then ⊥ else (G a).graph⟩ = _
    rw [if_pos h]
    exact discrete_class (G a)
  · rw [if_neg h]
    simp [maskedFactors, h]

/-- The product-ring interpretation accounts for all fixed-coordinate vertex
choices; there is no implicit division by their number. -/
theorem masked_product_class {q} (G : Fin q → FinGraph) (T : Finset (Fin q)) :
    (∏ a, graphClass (maskedFactors G T a)) =
      (∏ a ∈ Finset.univ \ T, graphClass (G a)) *
        ∏ a ∈ T, ((G a).vertices : GraphRing) := by
  rw [← Finset.prod_sdiff (Finset.subset_univ T)]
  congr 1
  · apply Finset.prod_congr rfl
    intro a ha
    simp [Finset.mem_sdiff.mp ha |>.2]
  · apply Finset.prod_congr rfl
    intro a ha
    simp [ha]

theorem centered_mask_expansion {q} (G : Fin q → FinGraph) :
    centeredProduct G = ∑ T ∈ (Finset.univ : Finset (Fin q)).powerset,
      (-1 : GraphRing)^T.card * ∏ a, graphClass (maskedFactors G T a) := by
  rw [centered_expansion]
  apply Finset.sum_congr rfl
  intro T _
  rw [masked_product_class]
  rw [← Int.cast_prod]
  ring

/-- Masking is exactly walk restriction; all step and NB conditions survive,
including the cyclic seam. -/
def maskedWalkEquiv {q m} [NeZero m] (G : Fin q → FinGraph) (T : Finset (Fin q)) :
    ProductWalk (maskedFactors G T) m ≃
      {p : ProductWalk G m // ∀ t, p.val.1 t ∉ T} := by
  have hstep {x y : ProductVertex G} {a} :
      ProductStep (maskedFactors G T) x y a ↔ ProductStep G x y a ∧ a ∉ T := by
    unfold ProductStep maskedFactors
    by_cases h : a ∈ T <;> simp [h]
  refine ⟨fun p => ⟨⟨p.val, fun t => ((hstep.mp (p.property.1 t)).1), p.property.2⟩,
      fun t => (hstep.mp (p.property.1 t)).2⟩,
    fun p => ⟨p.val.val, fun t => hstep.mpr ⟨p.val.property.1 t, p.property t⟩, p.val.property.2⟩,
    ?_, ?_⟩
  · intro p; rfl
  · intro p; rfl

def usedCoordinates {q m} [NeZero m] {G : Fin q → FinGraph} (p : ProductWalk G m) : Finset (Fin q) :=
  Finset.univ.image p.val.1

private theorem mask_indicator {q m} [NeZero m] {G : Fin q → FinGraph}
    (p : ProductWalk G m) (T : Finset (Fin q)) :
    (∏ a ∈ T, if a ∈ usedCoordinates p then (0 : ℤ) else 1) =
      if ∀ t, p.val.1 t ∉ T then 1 else 0 := by
  classical
  by_cases h : ∀ t, p.val.1 t ∉ T
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro a ha
    have hn : a ∉ usedCoordinates p := by
      intro hu
      obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hu
      exact h t (ht ▸ ha)
    simp [hn]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨t, ht⟩ := h
    apply Finset.prod_eq_zero ht
    have hu : p.val.1 t ∈ usedCoordinates p := Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
    simp [hu]

/-- Each masked count is the sum of per-walk support indicators on the
unmasked actual Cartesian graph. -/
theorem masked_count {q m} [NeZero m] (G : Fin q → FinGraph) (T : Finset (Fin q)) :
    (Fintype.card (ProductWalk (maskedFactors G T) m) : ℤ) =
      ∑ p : ProductWalk G m, ∏ a ∈ T, if a ∈ usedCoordinates p then (0 : ℤ) else 1 := by
  classical
  rw [Fintype.card_congr (maskedWalkEquiv G T)]
  simp_rw [mask_indicator]
  simp [Fintype.card_subtype]

private theorem full_support_iff {q m} [NeZero m] {G : Fin q → FinGraph} (p : ProductWalk G m) :
    (Finset.univ : Finset (Fin q)) ⊆ usedCoordinates p ↔ Function.Surjective p.val.1 := by
  simp [usedCoordinates, Function.Surjective, Finset.subset_iff]

/-- The graph-ring centered NB defect equals the actual full-coordinate
support count. Every link is constructed, including the additive descent. -/
theorem nb_centered_full_support {q m} [NeZero m] (G : Fin q → FinGraph) :
    nbInvariant m (centeredProduct G) =
      (Fintype.card {p : ProductWalk G m // Function.Surjective p.val.1} : ℤ) := by
  classical
  rw [centered_mask_expansion, map_sum]
  have hterm (T : Finset (Fin q)) :
      nbInvariant m ((-1 : GraphRing)^T.card * ∏ a, graphClass (maskedFactors G T a)) =
      (-1 : ℤ)^T.card * (Fintype.card (ProductWalk (maskedFactors G T) m) : ℤ) := by
    have he : (-1 : GraphRing)^T.card * ∏ a, graphClass (maskedFactors G T a) =
        (-1 : ℤ)^T.card • ∏ a, graphClass (maskedFactors G T a) := by
      simp [zsmul_eq_mul]
    rw [he, map_smul, nb_product_count]
    rfl
  simp_rw [hterm, masked_count]
  rw [full_support_extraction]
  simp_rw [full_support_iff]
  simp [Fintype.card_subtype]

end
end GraphProductRing

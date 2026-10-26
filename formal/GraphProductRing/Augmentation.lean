import GraphProductRing.GraphRing
import Mathlib.RingTheory.Ideal.Operations

namespace GraphProductRing
open scoped BigOperators
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2048

private def graphSpan : Submodule ℤ GraphRing := Submodule.span ℤ (Set.range graphClass)

private theorem class_mem_span (G) : graphClass G ∈ graphSpan :=
  Submodule.subset_span ⟨G, rfl⟩

private theorem graphSpan_mul {x y : GraphRing} (hx : x ∈ graphSpan) (hy : y ∈ graphSpan) :
    x * y ∈ graphSpan := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨G, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨H, rfl⟩ := hy
      rw [← class_box]
      exact class_mem_span _
    | zero => simp [graphSpan]
    | add x y _ _ ihx ihy => simpa [mul_add] using graphSpan.add_mem ihx ihy
    | smul a x _ ih => simpa only [mul_smul_comm] using graphSpan.smul_mem a ih
  | zero => simp [graphSpan]
  | add x y _ _ ihx ihy => simpa [add_mul] using graphSpan.add_mem ihx ihy
  | smul a x _ ih => simpa only [smul_mul_assoc] using graphSpan.smul_mem a ih

/-- Actual graph classes generate the entire ring as an additive group,
not merely as an algebra. Product relations are used in the proof. -/
theorem graph_additive_span : Submodule.span ℤ (Set.range graphClass) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using FreeCommRing.induction_on with
  | neg_one =>
    have h : (1 : GraphRing) ∈ graphSpan := class_unit ▸ class_mem_span FinGraph.unit
    simpa using graphSpan.neg_mem h
  | of G => exact class_mem_span G
  | add p q hp hq => simpa only [map_add] using graphSpan.add_mem hp hq
  | mul p q hp hq => simpa only [map_mul] using graphSpan_mul hp hq

/-- Centering is ℤ-linear but deliberately is not a ring homomorphism. -/
def center : GraphRing →ₗ[ℤ] GraphRing where
  toFun x := x - (epsilon x : GraphRing)
  map_add' x y := by simp; ring
  map_smul' a x := by simp [zsmul_eq_mul]; ring

@[simp] theorem center_apply (x) : center x = x - (epsilon x : GraphRing) := rfl

def centered (G : FinGraph) : GraphRing := center (graphClass G)
def augmentationIdeal : Ideal GraphRing := RingHom.ker epsilon

@[simp] theorem centered_eq (G) : centered G = graphClass G - (G.vertices : GraphRing) := by
  simp [centered]
@[simp] theorem epsilon_center (x) : epsilon (center x) = 0 := by simp
@[simp] theorem center_of_mem {x} (hx : x ∈ augmentationIdeal) : center x = x := by
  have h : epsilon x = 0 := hx
  simp [h]

theorem centered_mem (G) : centered G ∈ augmentationIdeal := epsilon_center _

/-- The augmentation ideal is additively spanned by the actual centered graphs. -/
theorem augmentation_additive_span :
    Submodule.span ℤ (Set.range centered) = augmentationIdeal.restrictScalars ℤ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨G, rfl⟩
    exact centered_mem G
  · intro x hx
    rw [← center_of_mem hx]
    have hx' : x ∈ Submodule.span ℤ (Set.range graphClass) := by
      rw [graph_additive_span]; trivial
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨G, rfl⟩ := hy
      exact Submodule.subset_span ⟨G, rfl⟩
    | zero => simp
    | add x y _ _ ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
    | smul a x _ ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

/-- Length-q products, retaining order only as a convenient finite index. -/
def centeredProduct {q : ℕ} (G : Fin q → FinGraph) : GraphRing := ∏ i, centered (G i)

def centeredProducts (q : ℕ) : Set GraphRing := Set.range (@centeredProduct q)

/-- Positive ideal powers are additively spanned by products of exactly q
centered graph classes. This is stronger than ideal-generation. -/
theorem augmentation_power_span (q : ℕ) (hq : 0 < q) :
    (augmentationIdeal ^ q).restrictScalars ℤ = Submodule.span ℤ (centeredProducts q) := by
  induction q, hq using Nat.le_induction with
  | base =>
    rw [pow_one, ← augmentation_additive_span]
    congr 1
    ext x
    constructor
    · rintro ⟨G, rfl⟩
      exact ⟨fun _ => G, by simp [centeredProduct]⟩
    · rintro ⟨G, rfl⟩
      exact ⟨G 0, by simp [centeredProduct]⟩
  | succ q hq ih =>
    rw [pow_succ, Ideal.restrictScalars_mul, ih, ← augmentation_additive_span,
      Submodule.span_mul_span]
    congr 1
    ext z
    constructor
    · rintro ⟨x, ⟨G, rfl⟩, y, ⟨H, rfl⟩, rfl⟩
      exact ⟨Fin.snoc G H, by
        unfold centeredProduct
        rw [Fin.prod_univ_castSucc]
        simp⟩
    · rintro ⟨G, rfl⟩
      refine ⟨centeredProduct (fun i : Fin q => G i.castSucc), ⟨_, rfl⟩,
        centered (G (Fin.last q)), ⟨_, rfl⟩, ?_⟩
      simp [centeredProduct, Fin.prod_univ_castSucc]

/-- A centered identity on actual graph factors gives genuine ideal-power
vanishing on virtual elements. No graph-counting hypothesis is hidden here. -/
theorem vanishes_on_power_iff (f : GraphRing →ₗ[ℤ] ℤ) (q : ℕ) (hq : 0 < q) :
    (∀ x ∈ augmentationIdeal ^ q, f x = 0) ↔
      ∀ G : Fin q → FinGraph, f (centeredProduct G) = 0 := by
  have hspan := augmentation_power_span q hq
  constructor
  · intro h G
    apply h
    change centeredProduct G ∈ (augmentationIdeal ^ q).restrictScalars ℤ
    rw [hspan]
    exact Submodule.subset_span ⟨G, rfl⟩
  · intro h x hx
    have hx' : x ∈ Submodule.span ℤ (centeredProducts q) := by
      rw [← hspan]; exact hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy => obtain ⟨G, rfl⟩ := hy; exact h G
    | zero => simp
    | add x y _ _ ihx ihy => simp [ihx, ihy]
    | smul a x _ ih => rw [map_smul, ih, smul_zero]

end
end GraphProductRing

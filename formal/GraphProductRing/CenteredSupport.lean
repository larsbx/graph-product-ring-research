import GraphProductRing.Augmentation

namespace GraphProductRing
open scoped BigOperators
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2048

/-- Inclusion-exclusion in the constructed graph ring. T indexes removed
coordinates; its vertex weights are retained, including empty factors. -/
theorem centered_expansion {q : ℕ} (G : Fin q → FinGraph) :
    centeredProduct G = ∑ T ∈ (Finset.univ : Finset (Fin q)).powerset,
      (-1 : GraphRing)^T.card * (∏ i ∈ Finset.univ \ T, graphClass (G i)) *
        ∏ i ∈ T, ((G i).vertices : GraphRing) := by
  simpa only [centeredProduct, centered_eq] using
    Finset.prod_sub (fun i => graphClass (G i)) (fun i => ((G i).vertices : GraphRing)) Finset.univ

/-- Evaluating the centered expansion uses only ℤ-linearity, not a false
multiplicativity assumption on the walk-counting invariant. -/
theorem centered_evaluation {q : ℕ} (f : GraphRing →ₗ[ℤ] ℤ) (G : Fin q → FinGraph) :
    f (centeredProduct G) = ∑ T ∈ (Finset.univ : Finset (Fin q)).powerset,
      ((-1 : ℤ)^T.card * ∏ i ∈ T, (G i).vertices) *
        f (∏ i ∈ Finset.univ \ T, graphClass (G i)) := by
  rw [centered_expansion, map_sum]
  apply Finset.sum_congr rfl
  intro T _
  have he : (-1 : GraphRing)^T.card * (∏ i ∈ Finset.univ \ T, graphClass (G i)) *
      ∏ i ∈ T, ((G i).vertices : GraphRing) =
      ((-1 : ℤ)^T.card * ∏ i ∈ T, (G i).vertices) •
        (∏ i ∈ Finset.univ \ T, graphClass (G i)) := by
    simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_prod]
    ring
  rw [he, map_smul]
  rfl

/-- The coefficient of one fixed walk in centered inclusion-exclusion.
T is allowed precisely when it removes no used coordinate. -/
def supportKernel {α : Type*} [DecidableEq α] (s S : Finset α) : ℤ :=
  ∑ T ∈ s.powerset, (-1 : ℤ)^T.card * ∏ i ∈ T, if i ∈ S then (0 : ℤ) else 1

/-- Pointwise support cancellation, independent of graph regularity,
connectedness, path simplicity, or even the particular class of objects. -/
theorem support_cancellation {α : Type*} [DecidableEq α] (s S : Finset α) :
    supportKernel s S = if s ⊆ S then 1 else 0 := by
  have he : supportKernel s S = ∏ i ∈ s, (1 - (if i ∈ S then (0 : ℤ) else 1)) := by
    simp only [supportKernel, Finset.prod_sub, Finset.prod_const_one, mul_one]
  rw [he]
  by_cases h : s ⊆ S
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [h hi]
  · rw [if_neg h]
    obtain ⟨i, hi, hn⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hi (by simp [hn])

/-- A finite family of objects with independently assigned supports.
Applying cancellation object by object extracts exactly full support. -/
theorem full_support_extraction {α Ω : Type*} [DecidableEq α] [Fintype Ω]
    (s : Finset α) (used : Ω → Finset α) :
    (∑ T ∈ s.powerset, (-1 : ℤ)^T.card *
      ∑ w : Ω, ∏ i ∈ T, if i ∈ used w then (0 : ℤ) else 1) =
      ∑ w : Ω, if s ⊆ used w then (1 : ℤ) else 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  exact support_cancellation s (used w)

end
end GraphProductRing

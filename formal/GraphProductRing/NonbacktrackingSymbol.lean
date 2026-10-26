import GraphProductRing.MaskedSupport
import GraphProductRing.EdgeInvariant
import Mathlib.LinearAlgebra.Multilinear.Basic

namespace GraphProductRing
open scoped BigOperators
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2048

/-- Centered convention: no factorial normalization. Defined on every
virtual factor, not only graph classes. -/
def centeredSymbol (q : ℕ) (f : GraphRing →ₗ[ℤ] ℤ) :
    MultilinearMap ℤ (fun _ : Fin q => GraphRing) ℤ :=
  f.compMultilinearMap ((MultilinearMap.mkPiAlgebra ℤ (Fin q) GraphRing).compLinearMap (fun _ => center))

@[simp] theorem centeredSymbol_apply (q) (f : GraphRing →ₗ[ℤ] ℤ) (x : Fin q → GraphRing) :
    centeredSymbol q f x = f (∏ a, center (x a)) := rfl

def edgeTensor (q : ℕ) : MultilinearMap ℤ (fun _ : Fin q => GraphRing) ℤ :=
  (MultilinearMap.mkPiAlgebra ℤ (Fin q) ℤ).compLinearMap (fun _ => edgeInvariant)

@[simp] theorem edgeTensor_apply (q) (x : Fin q → GraphRing) : edgeTensor q x = ∏ a, edgeInvariant (x a) := rfl

/-- Multilinear equality is determined by independently proved additive graph
spanning in each factor. This includes arbitrary negative/virtual factors. -/
theorem multilinear_graph_ext {q} {f g : MultilinearMap ℤ (fun _ : Fin q => GraphRing) ℤ}
    (h : ∀ G : Fin q → FinGraph, f (fun a => graphClass (G a)) = g (fun a => graphClass (G a))) : f = g := by
  classical
  have hs (s : Finset (Fin q)) : ∀ x : Fin q → GraphRing,
      (∀ a, a ∉ s → ∃ G, x a = graphClass G) → f x = g x := by
    induction s using Finset.induction_on with
    | empty =>
      intro x hx
      choose G hG using fun a => hx a (by simp)
      have he : x = fun a => graphClass (G a) := funext hG
      rw [he]
      exact h G
    | @insert i s hi ih =>
      intro x hx
      have he : f.toLinearMap x i = g.toLinearMap x i := by
        apply additive_hom_ext
        intro G
        apply ih
        intro a ha
        by_cases hai : a = i
        · subst a
          exact ⟨G, by simp⟩
        · obtain ⟨H, hH⟩ := hx a (by simp [ha, hai])
          exact ⟨H, by simp [Function.update_of_ne hai, hH]⟩
      have hv := congrArg (fun l : GraphRing →ₗ[ℤ] ℤ => l (x i)) he
      simpa [MultilinearMap.toLinearMap] using hv
  apply MultilinearMap.ext
  intro x
  exact hs Finset.univ x (by simp)

/-- The support/filtration bound for arbitrary actual factors is transferred
to every virtual element of the ideal power by the checked spanning theorem. -/
theorem nb_upper_filtration {m q} [NeZero m] (hq : 0 < q) (hm : m < 2*q) :
    ∀ x ∈ augmentationIdeal ^ q, nbInvariant m x = 0 := by
  apply (vanishes_on_power_iff (nbInvariant m) q hq).mpr
  intro G
  rw [nb_centered_full_support]
  letI := full_support_empty G hm
  simp

/-- Full-support factor-edge recovery gives the actual-graph top defect. -/
theorem nb_graph_symbol {k} [NeZero (k+k)] (hk : 2 ≤ k) (G : Fin k → FinGraph) :
    nbInvariant (k+k) (centeredProduct G) = (beta k : ℤ) * ∏ a, ((G a).edges : ℤ) := by
  rw [nb_centered_full_support]
  have h := full_support_factor_count hk G
  exact_mod_cast h

/-- Global top-symbol purity on the full finite simple Cartesian graph ring.
This is derived from actual counts, masking, additive descent and spanning;
the identity itself is neither an axiom nor a presentation relation. -/
theorem nb_global_symbol {k} [NeZero (k+k)] (hk : 2 ≤ k) :
    centeredSymbol k (nbInvariant (k+k)) = (beta k : ℤ) • edgeTensor k := by
  apply multilinear_graph_ext
  intro G
  change nbInvariant (k+k) (centeredProduct G) = _
  rw [nb_graph_symbol hk]
  simp [edgeTensor_apply]

/-- Pointwise form of the global identity, on arbitrary virtual factors. -/
theorem nb_global_symbol_apply {k} [NeZero (k+k)] (hk : 2 ≤ k) (x : Fin k → GraphRing) :
    nbInvariant (k+k) (∏ a, center (x a)) = (beta k : ℤ) * ∏ a, edgeInvariant (x a) := by
  have h := congrArg (fun f : MultilinearMap ℤ (fun _ : Fin k => GraphRing) ℤ => f x) (nb_global_symbol hk)
  simpa using h

/-- Exact order is kept separate from a degree-k symbol formula. -/
def HasExactAugmentationOrder (f : GraphRing →ₗ[ℤ] ℤ) (k : ℕ) : Prop :=
  (∀ x ∈ augmentationIdeal^(k+1), f x = 0) ∧ ¬ ∀ x ∈ augmentationIdeal^k, f x = 0

private def edgeGraph : FinGraph := ⟨Bool, inferInstance, ⊤⟩

private theorem edgeGraph_edges : edgeGraph.edges = 1 := by
  classical
  unfold FinGraph.edges edgeGraph
  convert (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Bool)) using 1
  · congr 1
    ext e
    simp only [SimpleGraph.mem_edgeFinset]

/-- A nonzero K₂ centered evaluation, plus the global upper bound, proves
exact order k. Primitive normalization and aggregate deficits are not used. -/
theorem nb_exact_order {k} [NeZero (k+k)] (hk : 2 ≤ k) :
    HasExactAugmentationOrder (nbInvariant (k+k)) k := by
  constructor
  · exact nb_upper_filtration (by omega) (by omega)
  · intro h
    let G : Fin k → FinGraph := fun _ => edgeGraph
    have hm : centeredProduct G ∈ augmentationIdeal^k := by
      change centeredProduct G ∈ (augmentationIdeal^k).restrictScalars ℤ
      rw [augmentation_power_span k (by omega)]
      exact Submodule.subset_span ⟨G, rfl⟩
    have hz := h (centeredProduct G) hm
    rw [nb_graph_symbol hk] at hz
    have hp : (0 : ℤ) < beta k := by exact_mod_cast beta_pos hk
    simp only [G, edgeGraph_edges, Nat.cast_one, Finset.prod_const_one, mul_one] at hz
    omega

end
end GraphProductRing

import GraphProductRing.AdditiveLift
import GraphProductRing.FactorMultiplicity

namespace GraphProductRing
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2048

private def arcSum (G H : FinGraph) : FactorArc G ⊕ FactorArc H ≃ FactorArc (G.sum H) := by
  let f : FactorArc G ⊕ FactorArc H → FactorArc (G.sum H) :=
    Sum.elim (fun e => ⟨(Sum.inl e.val.1, Sum.inl e.val.2), e.property⟩)
      (fun e => ⟨(Sum.inr e.val.1, Sum.inr e.val.2), e.property⟩)
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        congr 1
        apply Subtype.ext
        have hp := congrArg Subtype.val h
        exact Prod.ext (Sum.inl.inj (congrArg Prod.fst hp)) (Sum.inl.inj (congrArg Prod.snd hp))
      | inr y => exact Sum.noConfusion (congrArg (fun e : FactorArc (G.sum H) => e.val.1) h)
    | inr x =>
      cases y with
      | inl y => exact Sum.noConfusion (congrArg (fun e : FactorArc (G.sum H) => e.val.1) h)
      | inr y =>
        congr 1
        apply Subtype.ext
        have hp := congrArg Subtype.val h
        exact Prod.ext (Sum.inr.inj (congrArg Prod.fst hp)) (Sum.inr.inj (congrArg Prod.snd hp))
  · rintro ⟨⟨u | u, v | v⟩, ha⟩
    · exact ⟨Sum.inl ⟨(u,v),ha⟩, rfl⟩
    · exact Bool.noConfusion ha
    · exact Bool.noConfusion ha
    · exact ⟨Sum.inr ⟨(u,v),ha⟩, rfl⟩

lemma edges_iso {G H : FinGraph} (e : G.graph ≃g H.graph) : G.edges = H.edges := by
  classical
  exact e.card_edgeFinset_eq

@[simp] theorem edges_sum (G H : FinGraph) : (G.sum H).edges = G.edges + H.edges := by
  have h := Fintype.card_congr (arcSum G H)
  rw [Fintype.card_sum, factor_arc_count, factor_arc_count, factor_arc_count] at h
  omega

@[simp] theorem edges_empty : FinGraph.empty.edges = 0 := by
  classical
  simp [FinGraph.edges, FinGraph.empty]

private def edgeRigCount : GraphRig →+ ℤ where
  toFun := Quotient.lift (fun G : FinGraph => (G.edges : ℤ)) (by
    intro G H ⟨e⟩
    change (G.edges : ℤ) = (H.edges : ℤ)
    exact_mod_cast edges_iso e)
  map_zero' := by change (FinGraph.empty.edges : ℤ) = 0; simp
  map_add' := by
    intro x y
    induction x using Quotient.inductionOn with | h G =>
      induction y using Quotient.inductionOn with | h H =>
        change ((G.sum H).edges : ℤ) = (G.edges : ℤ) + H.edges
        rw [edges_sum, Nat.cast_add]

/-- The additive edge invariant on all virtual graph-ring elements. -/
def edgeInvariant : GraphRing →ₗ[ℤ] ℤ := liftAdditive edgeRigCount

@[simp] theorem edgeInvariant_class (G) : edgeInvariant (graphClass G) = (G.edges : ℤ) := by
  rw [edgeInvariant, liftAdditive_class]
  rfl

@[simp] theorem edgeInvariant_one : edgeInvariant 1 = 0 := by
  rw [← class_unit, edgeInvariant_class]
  classical
  simp [FinGraph.edges, FinGraph.unit]

@[simp] theorem edgeInvariant_center (x) : edgeInvariant (center x) = edgeInvariant x := by
  have h (a : ℤ) : edgeInvariant (a : GraphRing) = 0 := by
    have he : (a : GraphRing) = a • (1 : GraphRing) := by simp [zsmul_eq_mul]
    rw [he, map_smul, edgeInvariant_one, smul_zero]
  rw [center_apply, map_sub, h, sub_zero]

end
end GraphProductRing

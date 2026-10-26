import GraphProductRing.WalkInvariant
import GraphProductRing.FactorMultiplicity

namespace GraphProductRing
noncomputable section

/-- The directed-arc Hashimoto transition, with no regularity hypothesis. -/
def HashimotoAdjacent {G : FinGraph} (a b : FactorArc G) : Prop :=
  a.val.2 = b.val.1 ∧ a.val.1 ≠ b.val.2

def HashimotoCycle (G : FinGraph) (m : ℕ) [NeZero m] :=
  {a : Fin m → FactorArc G // ∀ t, HashimotoAdjacent (a t) (a (t+1))}
instance (G) (m : ℕ) [NeZero m] : Fintype (HashimotoCycle G m) := by
  classical unfold HashimotoCycle; infer_instance

/-- Actual vertex trajectories and rooted closed cyclic Hashimoto arc
trajectories are equivalent, including the final/initial transition. -/
def nbHashimotoBijection (G : FinGraph) (m : ℕ) [NeZero m] : NBWalk G m ≃ HashimotoCycle G m where
  toFun w := ⟨fun t => ⟨(w.val t, w.val (t+1)), (w.property t).1⟩,
    fun t => ⟨rfl, Ne.symm (w.property t).2⟩⟩
  invFun a := ⟨fun t => (a.val t).val.1, fun t => by
    have h := (a.val t).property
    rw [(a.property t).1] at h
    refine ⟨h, ?_⟩
    have hn := (a.property t).2
    rw [(a.property (t+1)).1] at hn
    exact Ne.symm hn⟩
  left_inv w := rfl
  right_inv a := by
    apply Subtype.ext
    funext t
    apply Subtype.ext
    exact Prod.ext rfl (a.property t).1.symm

theorem nbGraphCount_hashimoto (G) (m : ℕ) [NeZero m] :
    nbGraphCount m G = (Fintype.card (HashimotoCycle G m) : ℤ) := by
  unfold nbGraphCount
  rw [Fintype.card_congr (nbHashimotoBijection G m)]

end
end GraphProductRing

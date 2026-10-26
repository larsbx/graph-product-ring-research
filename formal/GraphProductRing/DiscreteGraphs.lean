import GraphProductRing.GraphRing

namespace GraphProductRing
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2048

/-- Edgeless finite graphs, with the same actual vertices retained. -/
def discreteGraph (V : Type) [Fintype V] : FinGraph := ⟨V, inferInstance, ⊥⟩

def discreteIso {V W : Type} [Fintype V] [Fintype W] (e : V ≃ W) :
    (discreteGraph V).graph ≃g (discreteGraph W).graph := ⟨e, by intro x y; rfl⟩

def discreteSumIso (V W : Type) [Fintype V] [Fintype W] :
    (discreteGraph (V ⊕ W)).graph ≃g ((discreteGraph V).sum (discreteGraph W)).graph :=
  ⟨Equiv.refl _, by rintro (u | u) (v | v) <;> simp [FinGraph.sum, discreteGraph]⟩

private theorem discrete_fin_class (n : ℕ) : graphClass (discreteGraph (Fin n)) = (n : GraphRing) := by
  induction n with
  | zero =>
    have e : Fin 0 ≃ PEmpty := Fintype.equivOfCardEq (by simp)
    rw [class_iso (discreteIso e)]
    exact class_empty
  | succ n ih =>
    have e : Fin (n+1) ≃ Fin n ⊕ PUnit := Fintype.equivOfCardEq (by simp)
    rw [class_iso (discreteIso e), class_iso (discreteSumIso (Fin n) PUnit), class_sum, ih]
    change (n : GraphRing) + graphClass FinGraph.unit = _
    rw [class_unit, Nat.cast_add, Nat.cast_one]

/-- An edgeless graph is exactly |V| copies of K₁ in the additive completion. -/
theorem discrete_class (G : FinGraph) : graphClass (discreteGraph G.V) = (G.vertices : GraphRing) := by
  rw [class_iso (discreteIso (Fintype.equivFin G.V)), discrete_fin_class]
  simp [FinGraph.vertices]

end
end GraphProductRing

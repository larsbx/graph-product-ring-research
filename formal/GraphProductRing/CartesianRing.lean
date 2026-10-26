import GraphProductRing.CartesianWalks

namespace GraphProductRing
open scoped BigOperators
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2048

/-- Actual finite dependent Cartesian graph. The coordinate condition is the
same checked step relation used by ProductWalk, not an external axiom. -/
def productGraph {q : ℕ} (G : Fin q → FinGraph) : FinGraph where
  V := ProductVertex G
  finiteV := inferInstance
  graph := {
    Adj := fun x y => ∃ a, ProductStep G x y a
    symm := by
      intro x y ⟨a, h⟩
      exact ⟨a, h.1.symm, fun b hb => (h.2 b hb).symm⟩
    loopless := by
      intro x ⟨a,h⟩
      exact (G a).graph.irrefl h.1 }

private def splitLast {q : ℕ} (G : Fin (q+1) → FinGraph) :
    ProductVertex G ≃ (ProductVertex (fun a : Fin q => G a.castSucc) × (G (Fin.last q)).V) where
  toFun x := (fun a => x a.castSucc, x (Fin.last q))
  invFun y := Fin.snoc y.1 y.2
  left_inv x := Fin.snoc_init_self x
  right_inv y := by cases y; simp

/-- The dependent tuple construction is the binary Cartesian product in the
constructed ring, including the empty-index unit. -/
def productGraph_succIso {q : ℕ} (G : Fin (q+1) → FinGraph) :
    (productGraph G).graph ≃g
      ((productGraph (fun a : Fin q => G a.castSucc)).box (G (Fin.last q))).graph := by
  refine ⟨splitLast G, ?_⟩
  intro x y
  change ((∃ a : Fin q, ProductStep (fun i => G i.castSucc)
    (fun i => x i.castSucc) (fun i => y i.castSucc) a) ∧ x (Fin.last q) = y (Fin.last q) ∨
    (G (Fin.last q)).graph.Adj (x (Fin.last q)) (y (Fin.last q)) ∧
      (fun i : Fin q => x i.castSucc) = (fun i : Fin q => y i.castSucc)) ↔ ∃ a, ProductStep G x y a
  constructor
  · rintro (⟨⟨a, ha⟩, hl⟩ | ⟨ha, ht⟩)
    · refine ⟨a.castSucc, ha.1, ?_⟩
      intro b hb
      revert hb
      refine Fin.lastCases (fun _ => hl) (fun i hi => ?_) b
      exact ha.2 i (fun he => hi (congrArg Fin.castSucc he))
    · refine ⟨Fin.last q, ha, ?_⟩
      intro b hb
      revert hb
      refine Fin.lastCases (fun hb => (hb rfl).elim) (fun i _ => ?_) b
      exact congrFun ht i
  · rintro ⟨a, ha⟩
    revert ha
    refine Fin.lastCases ?_ (fun i => ?_) a
    · intro ha
      right
      refine ⟨ha.1, ?_⟩
      funext b
      exact ha.2 b.castSucc (Fin.castSucc_ne_last b)
    · intro ha
      left
      refine ⟨⟨i, ha.1, ?_⟩, ha.2 (Fin.last q) (Ne.symm (Fin.castSucc_ne_last i))⟩
      intro b hb
      exact ha.2 b.castSucc (fun he => hb (Fin.castSucc_injective _ he))

private def productGraph_zeroIso (G : Fin 0 → FinGraph) :
    (productGraph G).graph ≃g FinGraph.unit.graph :=
  ⟨Equiv.equivPUnit (∀ a : Fin 0, (G a).V), by
    intro x y
    change False ↔ ∃ a : Fin 0, _
    simp⟩

theorem productGraph_class {q} (G : Fin q → FinGraph) :
    graphClass (productGraph G) = ∏ a, graphClass (G a) := by
  induction q with
  | zero =>
    rw [class_iso (productGraph_zeroIso G), class_unit]
    simp
  | succ q ih =>
    rw [class_iso (productGraph_succIso G), class_box, ih, Fin.prod_univ_castSucc]

end
end GraphProductRing

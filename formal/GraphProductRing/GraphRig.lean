import GraphProductRing.GraphRing

/-! Finite graph isomorphism classes form a commutative rig. This intermediate
object supports additive (nonmultiplicative) invariant descent to GraphRing. -/
namespace GraphProductRing
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2048

namespace FinGraph

def isoSum {G H G' H' : FinGraph} (e : G.graph ≃g G'.graph) (f : H.graph ≃g H'.graph) :
    (G.sum H).graph ≃g (G'.sum H').graph :=
  ⟨Equiv.sumCongr e.toEquiv f.toEquiv, by
    rintro (u | u) (v | v) <;> simp [sum, e.map_adj_iff, f.map_adj_iff]⟩

def isoBox {G H G' H' : FinGraph} (e : G.graph ≃g G'.graph) (f : H.graph ≃g H'.graph) :
    (G.box H).graph ≃g (G'.box H').graph :=
  ⟨Equiv.prodCongr e.toEquiv f.toEquiv, by
    intro u v
    simp [box, e.map_adj_iff, f.map_adj_iff]⟩

def isoZeroSum (G : FinGraph) : (empty.sum G).graph ≃g G.graph :=
  ⟨Equiv.emptySum PEmpty G.V, by
    rintro (u | u) (v | v)
    · exact u.elim
    · exact u.elim
    · exact v.elim
    · rfl⟩

def isoUnitBox (G : FinGraph) : (unit.box G).graph ≃g G.graph :=
  ⟨Equiv.punitProd _, by
    intro u v
    have he : u.1 = v.1 := by
      cases u.1
      cases v.1
      rfl
    simp [box, unit, he]⟩

def isoEmptyBox (G : FinGraph) : (empty.box G).graph ≃g empty.graph :=
  ⟨Equiv.equivPEmpty (PEmpty × G.V), by intro u; exact u.1.elim⟩

def isoSumBox (G H K : FinGraph) : ((G.sum H).box K).graph ≃g ((G.box K).sum (H.box K)).graph :=
  ⟨Equiv.sumProdDistrib _ _ _, by
    rintro ⟨u | u, b⟩ ⟨v | v, c⟩ <;> simp [sum, box]⟩

end FinGraph

def graphIsoSetoid : Setoid FinGraph where
  r G H := Nonempty (G.graph ≃g H.graph)
  iseqv := ⟨fun _ => ⟨SimpleGraph.Iso.refl⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

abbrev GraphRig := Quotient graphIsoSetoid

def rigClass (G : FinGraph) : GraphRig := Quotient.mk graphIsoSetoid G

theorem rigClass_iso {G H : FinGraph} (e : G.graph ≃g H.graph) : rigClass G = rigClass H :=
  Quotient.sound ⟨e⟩

instance : Zero GraphRig := ⟨rigClass FinGraph.empty⟩
instance : One GraphRig := ⟨rigClass FinGraph.unit⟩
instance : Add GraphRig := ⟨Quotient.map₂ FinGraph.sum (by
  intro G G' ⟨e⟩ H H' ⟨f⟩
  exact ⟨FinGraph.isoSum e f⟩)⟩
instance : Mul GraphRig := ⟨Quotient.map₂ FinGraph.box (by
  intro G G' ⟨e⟩ H H' ⟨f⟩
  exact ⟨FinGraph.isoBox e f⟩)⟩

@[simp] theorem rigClass_empty : rigClass FinGraph.empty = 0 := rfl
@[simp] theorem rigClass_unit : rigClass FinGraph.unit = 1 := rfl
@[simp] theorem rigClass_sum (G H) : rigClass (G.sum H) = rigClass G + rigClass H := rfl
@[simp] theorem rigClass_box (G H) : rigClass (G.box H) = rigClass G * rigClass H := rfl

instance : CommSemiring GraphRig where
  add_assoc := by
    intro x y z
    induction x using Quotient.inductionOn with | h G =>
      induction y using Quotient.inductionOn with | h H =>
        induction z using Quotient.inductionOn with | h K =>
          exact rigClass_iso SimpleGraph.Iso.sumAssoc
  zero_add := by
    intro x
    induction x using Quotient.inductionOn with | h G =>
      exact rigClass_iso (FinGraph.isoZeroSum G)
  add_zero := by
    intro x
    induction x using Quotient.inductionOn with | h G =>
      exact rigClass_iso ((SimpleGraph.Iso.sumComm).trans (FinGraph.isoZeroSum G))
  add_comm := by
    intro x y
    induction x using Quotient.inductionOn with | h G =>
      induction y using Quotient.inductionOn with | h H =>
        exact rigClass_iso (SimpleGraph.Iso.sumComm)
  mul_assoc := by
    intro x y z
    induction x using Quotient.inductionOn with | h G =>
      induction y using Quotient.inductionOn with | h H =>
        induction z using Quotient.inductionOn with | h K =>
          exact rigClass_iso (SimpleGraph.boxProdAssoc _ _ _)
  one_mul := by
    intro x
    induction x using Quotient.inductionOn with | h G =>
      exact rigClass_iso (FinGraph.isoUnitBox G)
  mul_one := by
    intro x
    induction x using Quotient.inductionOn with | h G =>
      exact rigClass_iso ((SimpleGraph.boxProdComm _ _).trans (FinGraph.isoUnitBox G))
  mul_comm := by
    intro x y
    induction x using Quotient.inductionOn with | h G =>
      induction y using Quotient.inductionOn with | h H =>
        exact rigClass_iso (SimpleGraph.boxProdComm _ _)
  zero_mul := by
    intro x
    induction x using Quotient.inductionOn with | h G =>
      exact rigClass_iso (FinGraph.isoEmptyBox G)
  mul_zero := by
    intro x
    induction x using Quotient.inductionOn with | h G =>
      exact rigClass_iso ((SimpleGraph.boxProdComm _ _).trans (FinGraph.isoEmptyBox G))
  right_distrib := by
    intro x y z
    induction x using Quotient.inductionOn with | h G =>
      induction y using Quotient.inductionOn with | h H =>
        induction z using Quotient.inductionOn with | h K =>
          exact rigClass_iso (FinGraph.isoSumBox G H K)
  left_distrib := by
    intro x y z
    induction x using Quotient.inductionOn with | h G =>
      induction y using Quotient.inductionOn with | h H =>
        induction z using Quotient.inductionOn with | h K =>
          exact rigClass_iso ((SimpleGraph.boxProdComm _ _).trans
            ((FinGraph.isoSumBox H K G).trans
              (FinGraph.isoSum (SimpleGraph.boxProdComm _ _) (SimpleGraph.boxProdComm _ _))))
  nsmul := nsmulRec
  natCast := Nat.unaryCast
  natCast_zero := rfl
  natCast_succ := fun _ => rfl

end
end GraphProductRing

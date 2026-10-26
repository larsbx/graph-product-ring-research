import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.RingTheory.FreeCommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

/-! The universal Cartesian graph ring. Relations are imposed only for graph
isomorphism, disjoint union, Cartesian product, the empty graph and K₁.
No counting or support theorem is a relation of this construction. -/
namespace GraphProductRing
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2048

structure FinGraph where
  V : Type
  finiteV : Fintype V
  graph : SimpleGraph V

attribute [instance] FinGraph.finiteV

namespace FinGraph

def empty : FinGraph := ⟨PEmpty, inferInstance, ⊥⟩
def unit : FinGraph := ⟨PUnit, inferInstance, ⊥⟩
def sum (G H : FinGraph) : FinGraph :=
  ⟨G.V ⊕ H.V, inferInstance, G.graph.sum H.graph⟩
def box (G H : FinGraph) : FinGraph :=
  ⟨G.V × H.V, inferInstance, G.graph.boxProd H.graph⟩
def vertices (G : FinGraph) : ℤ := Fintype.card G.V

@[simp] theorem vertices_empty : vertices empty = 0 := by simp [vertices, empty]
@[simp] theorem vertices_unit : vertices unit = 1 := by simp [vertices, unit]
@[simp] theorem vertices_sum (G H) : vertices (sum G H) = vertices G + vertices H := by
  simp [vertices, sum]
@[simp] theorem vertices_box (G H) : vertices (box G H) = vertices G * vertices H := by
  simp [vertices, box]
theorem vertices_iso {G H : FinGraph} (e : G.graph ≃g H.graph) :
    vertices G = vertices H := by
  unfold vertices
  exact_mod_cast Fintype.card_congr e.toEquiv

end FinGraph

abbrev GraphPresentation := FreeCommRing FinGraph

inductive GraphRelation : GraphPresentation → Prop
  | empty : GraphRelation (FreeCommRing.of FinGraph.empty)
  | unit : GraphRelation (FreeCommRing.of FinGraph.unit - 1)
  | iso {G H : FinGraph} (e : G.graph ≃g H.graph) :
      GraphRelation (FreeCommRing.of G - FreeCommRing.of H)
  | sum (G H) : GraphRelation
      (FreeCommRing.of (G.sum H) - (FreeCommRing.of G + FreeCommRing.of H))
  | box (G H) : GraphRelation
      (FreeCommRing.of (G.box H) - FreeCommRing.of G * FreeCommRing.of H)

def graphRelations : Ideal GraphPresentation := Ideal.span {x | GraphRelation x}
abbrev GraphRing := GraphPresentation ⧸ graphRelations

def graphClass (G : FinGraph) : GraphRing :=
  Ideal.Quotient.mk graphRelations (FreeCommRing.of G)

private theorem relation_zero {x} (h : GraphRelation x) :
    Ideal.Quotient.mk graphRelations x = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span h)

@[simp] theorem class_empty : graphClass FinGraph.empty = 0 :=
  relation_zero GraphRelation.empty
@[simp] theorem class_unit : graphClass FinGraph.unit = 1 := by
  have h := relation_zero GraphRelation.unit
  rw [map_sub (Ideal.Quotient.mk graphRelations), map_one (Ideal.Quotient.mk graphRelations), sub_eq_zero] at h
  exact h
theorem class_iso {G H : FinGraph} (e : G.graph ≃g H.graph) :
    graphClass G = graphClass H := by
  have h := relation_zero (GraphRelation.iso e)
  rw [map_sub (Ideal.Quotient.mk graphRelations), sub_eq_zero] at h
  exact h
@[simp] theorem class_sum (G H) : graphClass (G.sum H) = graphClass G + graphClass H := by
  have h := relation_zero (GraphRelation.sum G H)
  rw [map_sub (Ideal.Quotient.mk graphRelations), map_add (Ideal.Quotient.mk graphRelations), sub_eq_zero] at h
  exact h
@[simp] theorem class_box (G H) : graphClass (G.box H) = graphClass G * graphClass H := by
  have h := relation_zero (GraphRelation.box G H)
  rw [map_sub (Ideal.Quotient.mk graphRelations), map_mul (Ideal.Quotient.mk graphRelations), sub_eq_zero] at h
  exact h

private theorem relations_le_vertex_ker :
    graphRelations ≤ RingHom.ker (FreeCommRing.lift FinGraph.vertices) := by
  apply Ideal.span_le.mpr
  intro x hx
  change FreeCommRing.lift FinGraph.vertices x = 0
  cases hx with
  | empty => simp
  | unit => simp
  | iso e => simp [FinGraph.vertices_iso e]
  | sum G H => simp
  | box G H => simp

/-- Vertex-count augmentation, descended through all presentation relations. -/
def epsilon : GraphRing →+* ℤ :=
  Ideal.Quotient.lift graphRelations (FreeCommRing.lift FinGraph.vertices)
    (fun _ h => relations_le_vertex_ker h)

@[simp] theorem epsilon_class (G) : epsilon (graphClass G) = G.vertices := by
  simp [epsilon, graphClass]

/-- Universal property: any isomorphism-invariant rig-valued invariant extends
uniquely to this ring. This also specifies the additive-completion meaning. -/
def liftInvariant {R : Type*} [CommRing R] (f : FinGraph → R)
    (h0 : f FinGraph.empty = 0) (h1 : f FinGraph.unit = 1)
    (hi : ∀ {G H : FinGraph}, (G.graph ≃g H.graph) → f G = f H)
    (ha : ∀ G H, f (G.sum H) = f G + f H)
    (hm : ∀ G H, f (G.box H) = f G * f H) : GraphRing →+* R :=
  Ideal.Quotient.lift graphRelations (FreeCommRing.lift f) (by
    intro x hx
    have hle : graphRelations ≤ RingHom.ker (FreeCommRing.lift f) := by
      apply Ideal.span_le.mpr
      intro y hy
      change FreeCommRing.lift f y = 0
      cases hy with
      | empty => simpa using h0
      | unit => simpa using sub_eq_zero.mpr h1
      | iso e => simpa using sub_eq_zero.mpr (hi e)
      | sum G H => simpa using sub_eq_zero.mpr (ha G H)
      | box G H => simpa using sub_eq_zero.mpr (hm G H)
    exact hle hx)

@[simp] theorem liftInvariant_class {R : Type*} [CommRing R] (f h0 h1 hi ha hm) (G) :
    liftInvariant (R := R) f h0 h1 hi ha hm (graphClass G) = f G := by
  simp [liftInvariant, graphClass]

theorem graphRing_hom_ext {R : Type*} [CommRing R] {f g : GraphRing →+* R}
    (h : ∀ G, f (graphClass G) = g (graphClass G)) : f = g := by
  apply RingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have he : f.comp (Ideal.Quotient.mk graphRelations) =
      g.comp (Ideal.Quotient.mk graphRelations) := FreeCommRing.hom_ext h
  exact DFunLike.congr_fun he p

end
end GraphProductRing

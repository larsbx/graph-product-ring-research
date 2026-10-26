import GraphProductRing.AdditiveLift
import GraphProductRing.CartesianWalks

namespace GraphProductRing
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2048

/-- Rooted oriented cyclic NB vertex trajectories. Every cyclic step and
last–first reversal is checked. Coordinate witnesses are absent. -/
def NBWalk (G : FinGraph) (m : ℕ) [NeZero m] :=
  {v : Fin m → G.V // ∀ t, G.graph.Adj (v t) (v (t+1)) ∧ v (t+1+1) ≠ v t}
instance (G m) [NeZero m] : Fintype (NBWalk G m) := by
  classical unfold NBWalk; infer_instance

def nbWalkMap {G H : FinGraph} {m} [NeZero m] (e : G.graph ↪g H.graph) (w : NBWalk G m) :
    NBWalk H m :=
  ⟨fun t => e (w.val t), fun t => ⟨e.map_adj_iff.mpr (w.property t).1,
    fun h => (w.property t).2 (e.injective h)⟩⟩

def nbWalkIso {G H : FinGraph} {m} [NeZero m] (e : G.graph ≃g H.graph) : NBWalk G m ≃ NBWalk H m :=
  ⟨nbWalkMap e.toEmbedding, nbWalkMap e.symm.toEmbedding,
    by intro w; apply Subtype.ext; funext t; exact e.symm_apply_apply _,
    by intro w; apply Subtype.ext; funext t; exact e.apply_symm_apply _⟩

def nbSumInl (G H : FinGraph) {m} [NeZero m] (w : NBWalk G m) : NBWalk (G.sum H) m :=
  ⟨fun t => Sum.inl (w.val t), fun t => ⟨(w.property t).1,
    fun h => (w.property t).2 (Sum.inl.inj h)⟩⟩
def nbSumInr (G H : FinGraph) {m} [NeZero m] (w : NBWalk H m) : NBWalk (G.sum H) m :=
  ⟨fun t => Sum.inr (w.val t), fun t => ⟨(w.property t).1,
    fun h => (w.property t).2 (Sum.inr.inj h)⟩⟩

/-- A cyclic walk in a disjoint union stays in one actual summand. -/
def nbWalkSum (G H : FinGraph) (m : ℕ) [NeZero m] : NBWalk (G.sum H) m ≃ NBWalk G m ⊕ NBWalk H m := by
  let f : NBWalk G m ⊕ NBWalk H m → NBWalk (G.sum H) m :=
    Sum.elim (nbSumInl G H) (nbSumInr G H)
  apply Equiv.symm
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        congr 1
        apply Subtype.ext
        funext t
        exact Sum.inl.inj (congrArg (fun w : NBWalk (G.sum H) m => w.val t) h)
      | inr y =>
        have he := congrArg (fun w : NBWalk (G.sum H) m => w.val 0) h
        exact (Sum.noConfusion he)
    | inr x =>
      cases y with
      | inl y =>
        have he := congrArg (fun w : NBWalk (G.sum H) m => w.val 0) h
        exact (Sum.noConfusion he)
      | inr y =>
        congr 1
        apply Subtype.ext
        funext t
        exact Sum.inr.inj (congrArg (fun w : NBWalk (G.sum H) m => w.val t) h)
  · intro w
    let tag : Fin m → Bool := fun t => (w.val t).isLeft
    have ht (t) : tag (t+1) = tag t := by
      have ha := (w.property t).1
      cases h0 : w.val t <;> cases h1 : w.val (t+1) <;> simp_all [tag, FinGraph.sum]
    have htag (t) : tag t = tag 0 := cyclic_constant tag ht t
    cases h0 : w.val 0 with
    | inl x =>
      have hv (t) : ∃ v : G.V, w.val t = Sum.inl v := by
        have h := htag t
        cases he : w.val t with
        | inl v => exact ⟨v, rfl⟩
        | inr v => simp [tag, he, h0] at h
      choose v hv using hv
      have hp : ∀ t, G.graph.Adj (v t) (v (t+1)) ∧ v (t+1+1) ≠ v t := by
        intro t
        have ha := (w.property t).1
        rw [hv t, hv (t+1)] at ha
        refine ⟨ha, ?_⟩
        intro he
        apply (w.property t).2
        rw [hv (t+1+1), hv t, he]
      refine ⟨Sum.inl ⟨v,hp⟩, ?_⟩
      apply Subtype.ext
      funext t
      exact (hv t).symm
    | inr x =>
      have hv (t) : ∃ v : H.V, w.val t = Sum.inr v := by
        have h := htag t
        cases he : w.val t with
        | inr v => exact ⟨v, rfl⟩
        | inl v => simp [tag, he, h0] at h
      choose v hv using hv
      have hp : ∀ t, H.graph.Adj (v t) (v (t+1)) ∧ v (t+1+1) ≠ v t := by
        intro t
        have ha := (w.property t).1
        rw [hv t, hv (t+1)] at ha
        refine ⟨ha, ?_⟩
        intro he
        apply (w.property t).2
        rw [hv (t+1+1), hv t, he]
      refine ⟨Sum.inr ⟨v,hp⟩, ?_⟩
      apply Subtype.ext
      funext t
      exact (hv t).symm

/-- The integer-valued actual graph count, prior to ring extension. -/
def nbGraphCount (m : ℕ) [NeZero m] (G : FinGraph) : ℤ := Fintype.card (NBWalk G m)

theorem nbGraphCount_iso {G H : FinGraph} {m} [NeZero m] (e : G.graph ≃g H.graph) :
    nbGraphCount m G = nbGraphCount m H := by
  unfold nbGraphCount
  exact_mod_cast Fintype.card_congr (nbWalkIso (m := m) e)

@[simp] theorem nbGraphCount_sum (G H) (m : ℕ) [NeZero m] :
    nbGraphCount m (G.sum H) = nbGraphCount m G + nbGraphCount m H := by
  unfold nbGraphCount
  rw [Fintype.card_congr (nbWalkSum G H m), Fintype.card_sum]
  simp

@[simp] theorem nbGraphCount_empty (m : ℕ) [NeZero m] : nbGraphCount m FinGraph.empty = 0 := by
  have hi : IsEmpty (NBWalk FinGraph.empty m) := ⟨fun w => (w.val 0).elim⟩
  simp [nbGraphCount, Fintype.card_eq_zero]

/-- Additivity is proved from actual trajectories before descent. -/
def nbRigCount (m : ℕ) [NeZero m] : GraphRig →+ ℤ where
  toFun := Quotient.lift (nbGraphCount m) (by
    intro G H ⟨e⟩
    exact nbGraphCount_iso e)
  map_zero' := nbGraphCount_empty m
  map_add' := by
    intro x y
    induction x using Quotient.inductionOn with | h G =>
      induction y using Quotient.inductionOn with | h H =>
        exact nbGraphCount_sum G H m

/-- The actual cyclic NB count on virtual graph-ring elements. -/
def nbInvariant (m : ℕ) [NeZero m] : GraphRing →ₗ[ℤ] ℤ := liftAdditive (nbRigCount m)

@[simp] theorem nbInvariant_class (m : ℕ) [NeZero m] (G) :
    nbInvariant m (graphClass G) = nbGraphCount m G := by
  rw [nbInvariant, liftAdditive_class]
  rfl

end
end GraphProductRing

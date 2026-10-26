import GraphProductRing.GraphRig
import GraphProductRing.Augmentation

namespace GraphProductRing
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2048

private def monomialValue (m : Multiplicative (Multiset FinGraph)) : GraphRig :=
  (m.toAdd.map rigClass).prod

private def rawAdditiveEval (f : GraphRig →+ ℤ) : GraphPresentation →+ ℤ :=
  FreeAbelianGroup.lift (fun m => f (monomialValue m))

private def rawMono (m : Multiplicative (Multiset FinGraph)) : GraphPresentation :=
  FreeAbelianGroup.of m

private theorem rawMono_mul (m n : Multiplicative (Multiset FinGraph)) :
    rawMono m * rawMono n = rawMono (m*n) := FreeAbelianGroup.of_mul_of m n

private theorem rawEval_mono (f : GraphRig →+ ℤ) (m : Multiplicative (Multiset FinGraph)) :
    rawAdditiveEval f (rawMono m) = f (monomialValue m) :=
  FreeAbelianGroup.lift_apply_of _ _

private theorem mono_value_mul (m n : Multiplicative (Multiset FinGraph)) :
    monomialValue (m*n) = monomialValue m * monomialValue n := by
  change (Multiset.map rigClass (m.toAdd + n.toAdd)).prod = _
  rw [Multiset.map_add, Multiset.prod_add]
  rfl

private theorem raw_relation_monomial (f : GraphRig →+ ℤ)
    (m : Multiplicative (Multiset FinGraph)) {x : GraphPresentation} (hx : GraphRelation x) :
    rawAdditiveEval f (rawMono m * x) = 0 := by
  have hg (G : FinGraph) : rawAdditiveEval f (rawMono m * FreeCommRing.of G) =
      f (monomialValue m * rigClass G) := by
    change rawAdditiveEval f (rawMono m * rawMono (Multiplicative.ofAdd {G})) = _
    rw [rawMono_mul, rawEval_mono, mono_value_mul]
    simp [monomialValue]
  have hgh (G H : FinGraph) : rawAdditiveEval f (rawMono m *
      (FreeCommRing.of G * FreeCommRing.of H)) =
      f (monomialValue m * (rigClass G * rigClass H)) := by
    change rawAdditiveEval f (rawMono m *
      (rawMono (Multiplicative.ofAdd {G}) * rawMono (Multiplicative.ofAdd {H}))) = _
    rw [rawMono_mul, rawMono_mul, rawEval_mono, mono_value_mul, mono_value_mul]
    simp [monomialValue]
  cases hx with
  | empty => simp [hg]
  | unit => simp [mul_sub, hg, rawEval_mono]
  | iso e => simp [mul_sub, hg, rigClass_iso e]
  | sum G H => simp [mul_sub, mul_add, hg]
  | box G H => simp [mul_sub, hg, hgh]

private def additiveAnnihilator (f : GraphRig →+ ℤ) : Ideal GraphPresentation where
  carrier := {x | ∀ r, rawAdditiveEval f (r*x) = 0}
  zero_mem' := by intro r; simp
  add_mem' := by intro x y hx hy r; simp [mul_add, hx r, hy r]
  smul_mem' := by
    intro r x hx s
    change rawAdditiveEval f (s * (r*x)) = 0
    rw [← mul_assoc]
    exact hx (s*r)

private theorem graphRelations_le_annihilator (f : GraphRig →+ ℤ) :
    graphRelations ≤ additiveAnnihilator f := by
  apply Ideal.span_le.mpr
  intro x hx r
  induction r using FreeAbelianGroup.induction_on with
  | C0 => simp
  | C1 m => exact raw_relation_monomial f m hx
  | Cn m ih => simpa using neg_eq_zero.mpr ih
  | Cp r s hr hs => simp [add_mul, hr, hs]

/-- Every additive invariant of finite graph isomorphism classes descends
through the ring presentation, without requiring multiplicativity. -/
def liftAdditive (f : GraphRig →+ ℤ) : GraphRing →ₗ[ℤ] ℤ :=
  ((graphRelations.restrictScalars ℤ).liftQ (rawAdditiveEval f).toIntLinearMap (by
    intro x hx
    change rawAdditiveEval f x = 0
    have h := graphRelations_le_annihilator f hx (1 : GraphPresentation)
    simpa using h))

@[simp] theorem liftAdditive_class (f : GraphRig →+ ℤ) (G : FinGraph) :
    liftAdditive f (graphClass G) = f (rigClass G) := by
  change (graphRelations.restrictScalars ℤ).liftQ _ _
    (Submodule.Quotient.mk (FreeCommRing.of G)) = _
  rw [Submodule.liftQ_apply]
  change rawAdditiveEval f (rawMono (Multiplicative.ofAdd {G})) = _
  rw [rawEval_mono]
  simp [monomialValue]

/-- Additive graph-class values determine the extension uniquely. -/
theorem additive_hom_ext {f g : GraphRing →ₗ[ℤ] ℤ}
    (h : ∀ G, f (graphClass G) = g (graphClass G)) : f = g := by
  apply LinearMap.ext
  intro x
  have hx : x ∈ Submodule.span ℤ (Set.range graphClass) := by
    rw [graph_additive_span]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨G, rfl⟩ := hy; exact h G
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul a x _ hx => rw [map_smul, map_smul, hx]

end
end GraphProductRing

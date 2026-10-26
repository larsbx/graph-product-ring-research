import GraphProductRing.MaximalSupport
import GraphProductRing.GraphRing

namespace GraphProductRing
open scoped BigOperators
noncomputable section

/-- A finite Cartesian product, using dependent tuples of actual vertices. -/
abbrev ProductVertex {q : ℕ} (G : Fin q → FinGraph) := ∀ a, (G a).V

/-- One step changes precisely one coordinate along an actual factor edge. -/
def ProductStep {q : ℕ} (G : Fin q → FinGraph) (x y : ProductVertex G) (a : Fin q) : Prop :=
  (G a).graph.Adj (x a) (y a) ∧ ∀ b, b ≠ a → x b = y b

/-- The coordinate witness is uniquely recoverable from a Cartesian step. -/
theorem step_axis_unique {q} {G : Fin q → FinGraph} {x y : ProductVertex G}
    {a b : Fin q} (ha : ProductStep G x y a) (hb : ProductStep G x y b) : a = b := by
  by_contra hn
  exact ha.1.ne (hb.2 a hn)

/-- Actual cyclic vertex sequences, with every step checked in its factor.
Using Fin m and t+1 includes the closing step. The NB condition includes
both the penultimate/final and final/initial seams. -/
def ProductWalk {q : ℕ} (G : Fin q → FinGraph) (m : ℕ) [NeZero m] :=
  {p : (Fin m → Fin q) × (Fin m → ProductVertex G) //
    (∀ t, ProductStep G (p.2 t) (p.2 (t+1)) (p.1 t)) ∧
    ∀ t, p.2 (t+1+1) ≠ p.2 t}

instance {q} (G : Fin q → FinGraph) (m) [NeZero m] : Fintype (ProductWalk G m) := by
  classical unfold ProductWalk; infer_instance

/-- Coordinate witnesses do not inflate the count of actual trajectories. -/
theorem product_trajectory_injective {q m} [NeZero m] (G : Fin q → FinGraph) :
    Function.Injective (fun p : ProductWalk G m => p.val.2) := by
  intro p r h
  change p.val.2 = r.val.2 at h
  apply Subtype.ext
  apply Prod.ext
  · funext t
    have hr := r.property.1 t
    rw [← h] at hr
    exact step_axis_unique (p.property.1 t) hr
  · exact h

/-- No function on a finite permutation can change at exactly one place.
The proof telescopes an integer indicator; no parity or bipartiteness is used. -/
theorem no_single_change {ι α : Type*} [Fintype ι] (e : ι ≃ ι) (f : ι → α) (i : ι)
    (h : ∀ j, j ≠ i → f (e j) = f j) : f (e i) = f i := by
  classical
  by_contra hn
  let v : ι → ℤ := fun j => if f j = f i then 1 else 0
  have hs : (∑ j, (v (e j) - v j)) = 0 := by
    rw [Finset.sum_sub_distrib, e.sum_comp]
    exact sub_self _
  have he : (∑ j, (v (e j) - v j)) = v (e i) - v i := by
    apply Finset.sum_eq_single i
    · intro j _ hj
      simp [v, h j hj]
    · simp
  rw [he] at hs
  simp [v, hn] at hs

def axisCount {q m} [NeZero m] {G : Fin q → FinGraph} (p : ProductWalk G m) (a : Fin q) : ℕ :=
  Fintype.card {t // p.val.1 t = a}

/-- Any used factor occurs at least twice, including in nonbipartite graphs. -/
theorem used_axis_at_least_two {q m} [NeZero m] {G : Fin q → FinGraph}
    (p : ProductWalk G m) (a : Fin q) (ha : ∃ t, p.val.1 t = a) : 2 ≤ axisCount p a := by
  classical
  have hp : 0 < axisCount p a := Fintype.card_pos_iff.mpr (by
    obtain ⟨t, ht⟩ := ha; exact ⟨t, ht⟩)
  by_contra hn
  have hc : axisCount p a = 1 := by omega
  have hc' : (Finset.univ.filter (fun t => p.val.1 t = a)).card = 1 := by
    simpa [axisCount, Fintype.card_subtype] using hc
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hc'
  have hwt : p.val.1 t = a := by
    have : t ∈ Finset.univ.filter (fun t => p.val.1 t = a) := by rw [ht]; simp
    simpa using this
  have hother (j : Fin m) (hj : j ≠ t) : p.val.1 j ≠ a := by
    intro he
    have : j ∈ Finset.univ.filter (fun t => p.val.1 t = a) := by simp [he]
    rw [ht] at this
    exact hj (Finset.mem_singleton.mp this)
  have he := no_single_change (Equiv.addRight (1 : Fin m)) (fun j => p.val.2 j a) t (by
    intro j hj
    exact ((p.property.1 j).2 a (Ne.symm (hother j hj))).symm)
  have hedge := (p.property.1 t).1
  rw [hwt] at hedge
  exact hedge.ne he.symm

lemma axis_count_sum {q m} [NeZero m] {G : Fin q → FinGraph} (p : ProductWalk G m) :
    ∑ a, axisCount p a = m := by
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv p.val.1)
  simpa [axisCount, Fintype.card_sigma] using h

/-- Arbitrary-factor support budget, without regularity or connectedness. -/
theorem full_support_budget {q m} [NeZero m] {G : Fin q → FinGraph}
    (p : ProductWalk G m) (hf : Function.Surjective p.val.1) : 2*q ≤ m := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ => used_axis_at_least_two p a (hf a))
  simpa [axis_count_sum, Nat.mul_comm] using h

/-- Maximal length forces double occurrence on arbitrary factors. This
reuses the same Word interface as the merged finite cube combinatorics. -/
theorem product_maximal_twice {k} [NeZero (k+k)] {G : Fin k → FinGraph}
    (p : ProductWalk G (k+k)) (hf : Function.Surjective p.val.1) :
    ∀ a, axisCount p a = 2 := by
  have hlo (a) : 2 ≤ axisCount p a := used_axis_at_least_two p a (hf a)
  have hall : (∑ a : Fin k, 2) = ∑ a, axisCount p a := by
    simp [axis_count_sum, Nat.mul_two]
  intro a
  exact ((Finset.sum_eq_sum_iff_of_le (fun b _ => hlo b)).mp hall a (Finset.mem_univ a)).symm

/-- A function constant across every cyclic successor is constant everywhere. -/
lemma cyclic_constant {m : ℕ} [NeZero m] {α : Type*} (f : Fin m → α)
    (h : ∀ t, f (t+1) = f t) (t : Fin m) : f t = f 0 := by
  obtain ⟨n, hn⟩ := t
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs := h ⟨n, by omega⟩
    have he : (⟨n, by omega⟩ : Fin m) + 1 = ⟨n+1, hn⟩ := by
      apply Fin.ext
      simp [Fin.val_add, Nat.mod_eq_of_lt hn]
    rw [he] at hs
    exact hs.trans (ih (by omega))

/-- With only two possible change sites, a cyclic coordinate remains on the
edge at either site. This recovers a factor edge from actual vertices. -/
theorem two_change_values {m : ℕ} [NeZero m] {α : Type*} (f : Fin m → α)
    (i j : Fin m) (_hij : i ≠ j)
    (h : ∀ t, t ≠ i → t ≠ j → f (t+1) = f t) (t : Fin m) :
    f t = f i ∨ f t = f (i+1) := by
  classical
  let inside (t : Fin m) : Prop := f t = f i ∨ f t = f (i+1)
  have hi : inside (i+1) = inside i := propext (by simp [inside])
  have hall : ∀ t, inside (t+1) = inside t := by
    have hj := no_single_change (Equiv.addRight (1 : Fin m)) inside j (by
      intro a haj
      by_cases hai : a = i
      · subst a; exact hi
      · dsimp [inside]
        rw [h a hai haj])
    intro a
    by_cases haj : a = j
    · subst a; exact hj
    · by_cases hai : a = i
      · subst a; exact hi
      · dsimp [inside]
        rw [h a hai haj]
  have he := (cyclic_constant inside hall t).trans (cyclic_constant inside hall i).symm
  change inside t
  rw [he]
  simp [inside]

/-- Every maximal-support factor projection uses one recoverable edge.
No orientation or label multiplicity is inferred from numerical counts. -/
theorem maximal_factor_edge {k} [NeZero (k+k)] {G : Fin k → FinGraph}
    (p : ProductWalk G (k+k)) (hf : Function.Surjective p.val.1) (a : Fin k) :
    ∃ i : Pos k, p.val.1 i = a ∧
      (G a).graph.Adj (p.val.2 i a) (p.val.2 (i+1) a) ∧
      ∀ t, p.val.2 t a = p.val.2 i a ∨ p.val.2 t a = p.val.2 (i+1) a := by
  classical
  have hc : (Finset.univ.filter (fun t => p.val.1 t = a)).card = 2 := by
    simpa [axisCount, Fintype.card_subtype] using product_maximal_twice p hf a
  obtain ⟨i,j,hij,he⟩ := Finset.card_eq_two.mp hc
  have hi : p.val.1 i = a := by
    have : i ∈ Finset.univ.filter (fun t => p.val.1 t = a) := by rw [he]; simp
    simpa using this
  refine ⟨i, hi, hi ▸ (p.property.1 i).1, ?_⟩
  apply two_change_values (fun t => p.val.2 t a) i j hij
  intro t hti htj
  have hn : p.val.1 t ≠ a := by
    intro ha
    have : t ∈ Finset.univ.filter (fun t => p.val.1 t = a) := by simp [ha]
    rw [he] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    exact this.elim hti htj
  exact ((p.property.1 t).2 a (Ne.symm hn)).symm

private lemma two_values_return {α : Type*} {u v x y z : α}
    (hx : x = u ∨ x = v) (hy : y = u ∨ y = v) (hz : z = u ∨ z = v)
    (hxy : x ≠ y) (hyz : y ≠ z) : z = x := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    rcases hz with rfl | rfl <;> simp_all

/-- At maximal support, equal adjacent coordinates would force an immediate
reversal. The cyclic indexing makes the last–first case part of this proof. -/
theorem maximal_axis_no_repeat {k} [NeZero (k+k)] {G : Fin k → FinGraph}
    (p : ProductWalk G (k+k)) (hf : Function.Surjective p.val.1) (t : Pos k) :
    p.val.1 t ≠ p.val.1 (t+1) := by
  intro he
  apply p.property.2 t
  funext a
  by_cases ha : a = p.val.1 t
  · obtain ⟨i, _, _, hv⟩ := maximal_factor_edge p hf a
    have h0 := (p.property.1 t).1
    have h1 := (p.property.1 (t+1)).1
    rw [← ha] at h0
    rw [← he, ← ha] at h1
    exact two_values_return (hv t) (hv (t+1)) (hv (t+1+1)) h0.ne h1.ne
  · have h0 := (p.property.1 t).2 a ha
    have h1 := (p.property.1 (t+1)).2 a (by rwa [← he])
    exact (h0.trans h1).symm

/-- Admission from actual arbitrary-factor trajectories to the merged Word
API. Neither double occurrence nor the seam restriction is assumed. -/
def productMaximalWord {k} [NeZero (k+k)] (hk : 2 ≤ k) {G : Fin k → FinGraph}
    (p : ProductWalk G (k+k)) (hf : Function.Surjective p.val.1) : Word k :=
  ⟨p.val.1, product_maximal_twice p hf, by
    intro i j hij
    rw [adjacent_next hk] at hij
    rcases hij with rfl | rfl
    · exact maximal_axis_no_repeat p hf i
    · exact Ne.symm (maximal_axis_no_repeat p hf j)⟩

@[simp] theorem productMaximalWord_val {k} [NeZero (k+k)] (hk : 2 ≤ k)
    {G : Fin k → FinGraph} (p : ProductWalk G (k+k)) (hf) :
    (productMaximalWord hk p hf).val = p.val.1 := rfl

/-- The actual full-support count vanishes above the length budget. -/
theorem full_support_empty {q m} [NeZero m] (G : Fin q → FinGraph) (hm : m < 2*q) :
    IsEmpty {p : ProductWalk G m // Function.Surjective p.val.1} :=
  ⟨fun p => (Nat.not_le_of_lt hm) (full_support_budget p.val p.property)⟩

end
end GraphProductRing

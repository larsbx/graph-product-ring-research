import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Setoid.Basic
import Mathlib.Tactic

/-! Finite indexed positions. No quotient by cyclic rotation is taken here. -/
namespace GraphProductRing
open scoped BigOperators
noncomputable section

abbrev Pos (k : ℕ) := Fin (k + k)

def Adjacent {k : ℕ} (i j : Pos k) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
  (i.val + 1 = k + k ∧ j.val = 0) ∨ (j.val + 1 = k + k ∧ i.val = 0)

instance {k} (i j : Pos k) : Decidable (Adjacent i j) := by
  unfold Adjacent
  infer_instance

/-- A coordinate word with every coordinate occurring exactly twice. -/
def Word (k : ℕ) := { w : Pos k → Fin k //
  (∀ a, Fintype.card {i // w i = a} = 2) ∧
  ∀ i j, Adjacent i j → w i ≠ w j }

instance (k) : Fintype (Word k) := by classical unfold Word; infer_instance

/-- A partition into two-element blocks is a perfect matching. The Bool
relation makes the finite ambient space explicit, independent of word labels. -/
def Matching (k : ℕ) := { r : Pos k → Pos k → Bool //
  Equivalence (fun i j => r i j = true) ∧
  (∀ i, Fintype.card {j // r j i = true} = 2) ∧
  ∀ i j, Adjacent i j → r i j = false }

instance (k) : Fintype (Matching k) := by classical unfold Matching; infer_instance

def Matching.setoid {k} (m : Matching k) : Setoid (Pos k) :=
  ⟨fun i j => m.val i j = true, m.property.1⟩

abbrev Matching.Block {k} (m : Matching k) := Quotient m.setoid
instance {k} (m : Matching k) : Fintype m.Block := Fintype.ofFinite _

def forget {k} (w : Word k) : Matching k := by
  classical
  refine ⟨fun i j => decide (w.val i = w.val j), ?_, ?_, ?_⟩
  · exact ⟨by simp, by simp_all [eq_comm], by simp_all⟩
  · intro i
    simpa using w.property.1 (w.val i)
  · intro i j h
    simpa using w.property.2 i j h

lemma forget_eq_iff {k} (w v : Word k) : forget w = forget v ↔
    ∀ i j, (w.val i = w.val j ↔ v.val i = v.val j) := by
  classical
  constructor
  · intro h i j
    have := congrArg (fun m : Matching k => m.val i j) h
    simpa [forget] using this
  · intro h
    apply Subtype.ext
    funext i j
    simp only [forget, Subtype.coe_mk]
    simp [h i j]

lemma word_surjective {k} (w : Word k) : Function.Surjective w.val := by
  intro a
  have h := w.property.1 a
  have : Nonempty {i // w.val i = a} := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨i, hi⟩ := this
  exact ⟨i, hi⟩

/-- Every matching has k blocks, derived from its two-element fibers. -/
theorem Matching.card_blocks {k} (m : Matching k) : Fintype.card m.Block = k := by
  classical
  have hc (b : m.Block) : Fintype.card {i // Quotient.mk m.setoid i = b} = 2 := by
    induction b using Quotient.inductionOn with
    | h j =>
      have e : {i // Quotient.mk m.setoid i = Quotient.mk m.setoid j} ≃
          {i // m.val i j = true} :=
        Equiv.subtypeEquivRight (fun i => Quotient.eq)
      rw [Fintype.card_congr e]
      exact m.property.2.1 j
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk m.setoid))
  simp only [Fintype.card_sigma, hc, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Fintype.card_fin] at h
  have heq : Fintype.card (Quotient m.setoid) = Fintype.card m.Block :=
    Fintype.card_congr (Equiv.refl _)
  omega

/-- Label the k blocks; no pair orientation is selected or counted. -/
def label {k} (m : Matching k) (e : m.Block ≃ Fin k) : Word k := by
  classical
  refine ⟨fun i => e (Quotient.mk m.setoid i), ?_, ?_⟩
  · intro a
    let j := (e.symm a).out
    have hj : Quotient.mk m.setoid j = e.symm a := Quotient.out_eq _
    have hf : ∀ i, e (Quotient.mk m.setoid i) = a ↔ m.val i j = true := by
      intro i
      rw [e.apply_eq_iff_eq_symm_apply, ← hj]
      exact Quotient.eq
    rw [Fintype.card_congr (Equiv.subtypeEquivRight hf)]
    exact m.property.2.1 j
  · intro i j hij he
    have hr : m.val i j = true := Quotient.exact (e.injective he)
    rw [m.property.2.2 i j hij] at hr
    contradiction

@[simp] theorem forget_label {k} (m : Matching k) (e : m.Block ≃ Fin k) :
    forget (label m e) = m := by
  classical
  apply Subtype.ext
  funext i j
  simp only [forget, label, Subtype.coe_mk]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, e.injective.eq_iff, Quotient.eq]
  rfl

lemma forget_surjective (k) : Function.Surjective (@forget k) := by
  intro m
  have h := m.card_blocks
  let e : m.Block ≃ Fin k := (Fintype.equivFin _).trans (finCongr h)
  exact ⟨label m e, forget_label m e⟩

/-- Kernel equality for surjections is precisely coordinate relabeling. -/
lemma relabel_of_kernel {α β : Type*} (f g : α → β)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : ∀ i j, (f i = f j ↔ g i = g j)) :
    ∃ e : β ≃ β, ∀ i, e (f i) = g i := by
  let t := Function.surjInv hf
  have ht : ∀ a, f (t a) = a := Function.rightInverse_surjInv hf
  have hs : ∀ i, g (t (f i)) = g i := fun i => (h _ _).mp (ht _)
  have hb : Function.Bijective (g ∘ t) := by
    constructor
    · intro a b hab
      have hab' := (h (t a) (t b)).mpr hab
      simpa only [ht] using hab'
    · intro b
      obtain ⟨i, rfl⟩ := hg b
      exact ⟨f i, hs i⟩
  exact ⟨Equiv.ofBijective (g ∘ t) hb, hs⟩

theorem matching_iff_relabel {k} (w v : Word k) : forget w = forget v ↔
    ∃ e : Equiv.Perm (Fin k), ∀ i, e (w.val i) = v.val i := by
  constructor
  · intro h
    exact relabel_of_kernel _ _ (word_surjective w) (word_surjective v)
      ((forget_eq_iff w v).mp h)
  · rintro ⟨e, he⟩
    apply (forget_eq_iff w v).mpr
    intro i j
    rw [← he i, ← he j, e.injective.eq_iff]

/-- Explicit relabeling action. -/
def relabel {k} (w : Word k) (e : Equiv.Perm (Fin k)) : Word k := by
  classical
  refine ⟨fun i => e (w.val i), ?_, ?_⟩
  · intro a
    rw [Fintype.card_congr (Equiv.subtypeEquivRight
      (fun i => e.apply_eq_iff_eq_symm_apply))]
    exact w.property.1 (e.symm a)
  · intro i j h he
    exact w.property.2 i j h (e.injective he)

lemma relabel_injective {k} (w : Word k) : Function.Injective (relabel w) := by
  intro e f h
  apply Equiv.ext
  intro a
  obtain ⟨i, rfl⟩ := word_surjective w a
  exact congrArg (fun v : Word k => v.val i) h

lemma forget_relabel {k} (w : Word k) (e : Equiv.Perm (Fin k)) :
    forget (relabel w e) = forget w :=
  (forget_eq_iff _ _).mpr (fun _ _ => e.injective.eq_iff)

/-- Each fiber of forgetting labels has exactly k! elements, with no
stabilizer division. -/
def fiberEquiv {k} (w : Word k) : Equiv.Perm (Fin k) ≃
    {v : Word k // forget v = forget w} := by
  classical
  refine Equiv.ofBijective (fun e => ⟨relabel w e, forget_relabel w e⟩) ⟨?_, ?_⟩
  · intro e f h
    exact relabel_injective w (congrArg Subtype.val h)
  · rintro ⟨v, hv⟩
    obtain ⟨e, he⟩ := (matching_iff_relabel w v).mp hv.symm
    refine ⟨e, Subtype.ext (Subtype.ext (funext he))⟩

def R (k : ℕ) : ℕ := Fintype.card (Matching k)

theorem word_count (k : ℕ) : Fintype.card (Word k) = k.factorial * R k := by
  classical
  have hc (m : Matching k) : Fintype.card {w : Word k // forget w = m} = k.factorial := by
    obtain ⟨w, rfl⟩ := forget_surjective k m
    rw [← Fintype.card_congr (fiberEquiv w), Fintype.card_perm, Fintype.card_fin]
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv (@forget k))
  simpa [Fintype.card_sigma, hc, R, Nat.mul_comm] using h.symm

/-- Quotient by coordinate relabeling; indexed positions remain fixed. -/
def relabelSetoid (k : ℕ) : Setoid (Word k) := Setoid.ker forget

def matchingBijection (k : ℕ) : Quotient (relabelSetoid k) ≃ Matching k :=
  Setoid.quotientKerEquivOfSurjective forget (forget_surjective k)

/-- The explicit word 0,...,k-1,0,...,k-1. -/
def repeatLabel {k} (i : Pos k) : Fin k :=
  if h : i.val < k then ⟨i.val, h⟩ else ⟨i.val - k, by omega⟩

def pairPos {k} (a : Fin k) (b : Bool) : Pos k :=
  ⟨if b then k + a.val else a.val, by split <;> omega⟩

lemma repeat_pair {k} (a : Fin k) (b : Bool) : repeatLabel (pairPos a b) = a := by
  cases b <;> apply Fin.ext <;> simp [repeatLabel, pairPos]

lemma repeat_fiber {k} (a : Fin k) : Fintype.card {i : Pos k // repeatLabel i = a} = 2 := by
  classical
  let f : Bool → {i : Pos k // repeatLabel i = a} := fun b => ⟨pairPos a b, repeat_pair a b⟩
  have hf : Function.Bijective f := by
    constructor
    · intro b c h
      have hv := congrArg (fun x => x.val.val) h
      change (if b then k + a.val else a.val) = (if c then k + a.val else a.val) at hv
      have hk : k ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt a.isLt)
      cases b <;> cases c <;> simp_all
    · rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      by_cases h : i.val < k
      · refine ⟨false, Subtype.ext (Fin.ext ?_)⟩
        simp [f, pairPos]
        simpa [repeatLabel, h] using hv.symm
      · refine ⟨true, Subtype.ext (Fin.ext ?_)⟩
        simp only [f, pairPos, ↓reduceIte, Fin.val_mk]
        simp only [repeatLabel, h, ↓reduceDIte, Fin.val_mk] at hv
        omega
  exact (Fintype.card_congr (Equiv.ofBijective f hf)).symm.trans Fintype.card_bool

lemma repeat_adjacent {k} (hk : 2 ≤ k) (i j : Pos k) (h : Adjacent i j) :
    repeatLabel i ≠ repeatLabel j := by
  intro he
  have hv := congrArg Fin.val he
  by_cases hi : i.val < k <;> by_cases hj : j.val < k <;>
    simp [repeatLabel, hi, hj] at hv <;>
    rcases h with h | h | ⟨h,h'⟩ | ⟨h,h'⟩ <;> omega

def repeatWord {k} (hk : 2 ≤ k) : Word k :=
  ⟨repeatLabel, repeat_fiber, fun i j h => repeat_adjacent hk i j h⟩

theorem R_pos {k} (hk : 2 ≤ k) : 0 < R k := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨forget (repeatWord hk)⟩

def beta (k : ℕ) := 2^k * k.factorial * R k

theorem beta_pos {k} (hk : 2 ≤ k) : 0 < beta k :=
  Nat.mul_pos (Nat.mul_pos (by positivity) (Nat.factorial_pos k)) (R_pos hk)

end
end GraphProductRing

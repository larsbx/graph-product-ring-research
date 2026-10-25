import GraphProductRing.Hypercube
import Mathlib.Algebra.Group.Fin.Basic

namespace GraphProductRing
noncomputable section

/-- The actual cyclic vertex sequence, without its duplicate endpoint. -/
def cycle {k} (p : CubeWalk k) (i : Pos k) : Cube k := p.val.2 ⟨i.val, by omega⟩

section Cyclic
variable {k : ℕ} [NeZero (k+k)]

lemma cycle_step (p : CubeWalk k) (i : Pos k) :
    cycle p (i+1) = flip (cycle p i) (p.val.1.val i) := by
  have hi := i.isLt
  have hn : 0 < k+k := NeZero.pos _
  by_cases h : i.val+1 < k+k
  · have he : (i+1 : Pos k).val = i.val+1 := by
      simp [Fin.val_add, Nat.mod_eq_of_lt h]
    unfold cycle
    have hf : (⟨(i+1 : Pos k).val, by omega⟩ : Fin (k+k+1)) = ⟨i.val+1, by omega⟩ := Fin.ext he
    rw [hf]
    exact p.property i
  · have hl : i.val+1 = k+k := by omega
    have he : i+1 = (0 : Pos k) := by
      apply Fin.ext
      simp [Fin.val_add, hl]
    rw [he]
    have hp := p.property i
    have hc := walk_closed p
    unfold cycle
    have hf : (⟨i.val+1, by omega⟩ : Fin (k+k+1)) = ⟨k+k, by omega⟩ := Fin.ext hl
    rw [hf, hc] at hp
    exact hp

omit [NeZero (k+k)] in
lemma two_occurrences {w : Word k} {i j l : Pos k} (hij : i ≠ j)
    (hw : w.val j = w.val i) (hl : w.val l = w.val i) : l = i ∨ l = j := by
  classical
  let s := Finset.univ.filter (fun t => w.val t = w.val i)
  have hc : s.card = 2 := by simpa [s, Fintype.card_subtype] using w.property.1 (w.val i)
  obtain ⟨a,b,hab,hs⟩ := Finset.card_eq_two.mp hc
  have hi : i ∈ s := by simp [s]
  have hj : j ∈ s := by simp [s, hw]
  have ht : l ∈ s := by simp [s, hl]
  rw [hs] at hi hj ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj ht
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> aesop

/-- Primitive means free under rotation of actual vertices, not of labels. -/
def Primitive (p : CubeWalk k) : Prop :=
  ∀ d : Pos k, (∀ i, cycle p (i+d) = cycle p i) → d = 0

theorem maximal_support_primitive (hk : 2 ≤ k) (p : CubeWalk k) : Primitive p := by
  intro d hd
  by_contra hdz
  have hw (i : Pos k) : p.val.1.val (i+d) = p.val.1.val i := by
    have h1 := cycle_step p (i+d)
    have h2 := cycle_step p i
    rw [show i+d+1 = (i+1)+d by abel, hd (i+1), hd i] at h1
    exact (flip_injective_axis _).mp (h1.symm.trans h2)
  have hw0 : p.val.1.val d = p.val.1.val 0 := by simpa using hw 0
  have hw2 : p.val.1.val (d+d) = p.val.1.val 0 := (hw d).trans hw0
  have hdd : d+d = 0 := by
    rcases two_occurrences (Ne.symm hdz) hw0 hw2 with h | h
    · exact h
    · have : d = 0 := by simpa using add_right_cancel (show d+d = 0+d by simpa using h)
      exact (hdz this).elim
  have hv := congrArg Fin.val hdd
  have hdv : d.val ≠ 0 := fun h => hdz (Fin.ext h)
  simp only [Fin.val_add, Fin.val_zero] at hv
  have hdhalf : d.val = k := by
    have hlt := d.isLt
    have hmod := Nat.mod_add_div (d.val+d.val) (k+k)
    have hdiv : (d.val+d.val) / (k+k) < 2 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
    have hnonzero : (d.val+d.val) / (k+k) ≠ 0 := by
      intro hz
      rw [hv, hz, Nat.mul_zero] at hmod
      omega
    have heq : (d.val+d.val) / (k+k) = 1 :=
      Nat.le_antisymm (Nat.le_of_lt_succ hdiv) (Nat.pos_of_ne_zero hnonzero)
    rw [heq] at hmod
    omega
  have hocc : occurrences p.val.1 k (p.val.1.val 0) = 1 := by
    unfold occurrences
    have he : Finset.univ.filter (fun i : Pos k => i.val < k ∧ p.val.1.val i = p.val.1.val 0) = {0} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hi, hwi⟩
        rcases two_occurrences (Ne.symm hdz) hw0 hwi with h | h
        · exact h
        · subst i; omega
      · rintro rfl
        exact ⟨by simp; omega, rfl⟩
    rw [he, Finset.card_singleton]
  have hstate := hd 0
  simp only [zero_add] at hstate
  have ht : cycle p d = vertex p.val.1 (p.val.2 0) k := by
    unfold cycle
    rw [walk_unique, hdhalf]
  rw [ht] at hstate
  have hb := congrFun hstate (p.val.1.val 0)
  change (p.val.2 0 (p.val.1.val 0) ^^ decide (occurrences p.val.1 k (p.val.1.val 0) % 2 = 1)) =
    p.val.2 0 (p.val.1.val 0) at hb
  rw [hocc] at hb
  cases h : p.val.2 0 (p.val.1.val 0) <;> simp [h] at hb

lemma adjacent_next (hk : 2 ≤ k) (i j : Pos k) :
    Adjacent i j ↔ j = i+1 ∨ i = j+1 := by
  have hn : 1 < k+k := by omega
  have hval (t : Pos k) : (t+1 : Pos k).val = (t.val+1) % (k+k) := by
    simp [Fin.val_add, Nat.mod_eq_of_lt hn]
  simp only [Fin.ext_iff, hval, Adjacent]
  have hi := i.isLt
  have hj := j.isLt
  by_cases hia : i.val+1 < k+k <;> by_cases hja : j.val+1 < k+k
  · rw [Nat.mod_eq_of_lt hia, Nat.mod_eq_of_lt hja]; omega
  · have hjl : j.val+1 = k+k := by omega
    rw [Nat.mod_eq_of_lt hia, hjl, Nat.mod_self]; omega
  · have hil : i.val+1 = k+k := by omega
    rw [hil, Nat.mod_self, Nat.mod_eq_of_lt hja]; omega
  · have hil : i.val+1 = k+k := by omega
    have hjl : j.val+1 = k+k := by omega
    rw [hil, hjl, Nat.mod_self]; omega

lemma adjacent_shift (hk : 2 ≤ k) {i j : Pos k} (h : Adjacent i j) (d : Pos k) :
    Adjacent (i+d) (j+d) := by
  rw [adjacent_next hk] at h ⊢
  rcases h with rfl | rfl <;> simp only [add_assoc, add_comm, add_left_comm] <;> simp

def shiftWord (hk : 2 ≤ k) (w : Word k) (d : Pos k) : Word k := by
  classical
  refine ⟨fun i => w.val (i+d), ?_, ?_⟩
  · intro a
    let e : {i : Pos k // w.val (i+d) = a} ≃ {j : Pos k // w.val j = a} :=
      Equiv.subtypeEquiv (Equiv.addRight d) (fun _ => Iff.rfl)
    exact (Fintype.card_congr e).trans (w.property.1 a)
  · intro i j h
    exact w.property.2 (i+d) (j+d) (adjacent_shift hk h d)

/-- Rotation of an actual walk, reconstructed from its shifted cyclic
vertices. No quotient of coordinate labels is used. -/
def rotateWalk (hk : 2 ≤ k) (p : CubeWalk k) (d : Pos k) : CubeWalk k := by
  refine ⟨(shiftWord hk p.val.1 d,
    fun t => cycle p (⟨t.val % (k+k), Nat.mod_lt _ (NeZero.pos _)⟩ + d)), ?_⟩
  intro i
  have hidx : (⟨(i.val+1) % (k+k), Nat.mod_lt _ (NeZero.pos _)⟩ : Pos k) = i+1 := by
    apply Fin.ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (show 1 < k+k by omega)]
  have hidx0 : (⟨i.val % (k+k), Nat.mod_lt _ (NeZero.pos _)⟩ : Pos k) = i := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  change cycle p (⟨(i.val+1) % (k+k), _⟩ + d) =
    flip (cycle p (⟨i.val % (k+k), _⟩ + d)) (p.val.1.val (i+d))
  rw [hidx, hidx0]
  convert cycle_step p (i+d) using 1; congr 1; abel

@[simp] theorem cycle_rotate (hk : 2 ≤ k) (p : CubeWalk k) (d i : Pos k) :
    cycle (rotateWalk hk p d) i = cycle p (i+d) := by
  simp [cycle, rotateWalk, Nat.mod_eq_of_lt i.isLt]

lemma cycle_injective : Function.Injective (@cycle k) := by
  intro p q he
  apply trajectory_injective
  change p.val.2 = q.val.2
  funext t
  by_cases ht : t.val < k+k
  · exact congrFun he ⟨t.val, ht⟩
  · have ht' : t = ⟨k+k, by omega⟩ := Fin.ext (by have htt := t.isLt; dsimp; omega)
    rw [ht', walk_closed, walk_closed]
    exact congrFun he 0

/-- Rotation classes retain orientation. -/
def rotationSetoid (_hk : 2 ≤ k) : Setoid (CubeWalk k) where
  r p q := ∃ d : Pos k, ∀ i, cycle q i = cycle p (i+d)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p; exact ⟨0, by simp⟩
    · rintro p q ⟨d,hd⟩
      exact ⟨-d, fun i => by rw [hd]; simp⟩
    · rintro p q r ⟨d,hd⟩ ⟨e,he⟩
      exact ⟨e+d, fun i => by rw [he,hd]; simp [add_assoc]⟩

abbrev PrimitiveClass (hk : 2 ≤ k) := Quotient (rotationSetoid hk)
instance (hk : 2 ≤ k) : Fintype (PrimitiveClass hk) := Fintype.ofFinite _

def rotationFiber (hk : 2 ≤ k) (p : CubeWalk k) : Pos k ≃
    {q : CubeWalk k // Quotient.mk (rotationSetoid hk) q = Quotient.mk (rotationSetoid hk) p} := by
  classical
  refine Equiv.ofBijective (fun d => ⟨rotateWalk hk p d, Quotient.sound ?_⟩) ⟨?_, ?_⟩
  · exact ⟨-d, fun i => by simp⟩
  · intro d e h
    have he : cycle (rotateWalk hk p d) = cycle (rotateWalk hk p e) :=
      congrArg (fun q => cycle q.val) h
    have hp : ∀ i, cycle p (i+(d-e)) = cycle p i := by
      intro i
      have := congrFun he (i-e)
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
    have := maximal_support_primitive hk p (d-e) hp
    exact sub_eq_zero.mp this
  · rintro ⟨q,hq⟩
    obtain ⟨d,hd⟩ := Quotient.exact hq
    refine ⟨-d, Subtype.ext (cycle_injective (funext ?_))⟩
    intro i
    simp only [cycle_rotate]
    rw [hd]
    simp

theorem primitive_normalization (hk : 2 ≤ k) :
    (k+k) * Fintype.card (PrimitiveClass hk) = beta k := by
  classical
  have hc (c : PrimitiveClass hk) :
      Fintype.card {p : CubeWalk k // Quotient.mk (rotationSetoid hk) p = c} = k+k := by
    induction c using Quotient.inductionOn with
    | h p => exact (Fintype.card_congr (rotationFiber hk p)).symm.trans (Fintype.card_fin _)
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk (rotationSetoid hk)))
  simp only [Fintype.card_sigma, hc, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  have he : Fintype.card (Quotient (rotationSetoid hk)) = Fintype.card (PrimitiveClass hk) :=
    Fintype.card_congr (Equiv.refl _)
  rw [rooted_count] at h
  rw [← he, Nat.mul_comm]
  exact h

/-- Simplicity is injectivity before the duplicate endpoint. It is strictly
stronger than primitive, as checked by the k=4 replay vector. -/
def Simple (p : CubeWalk k) : Prop := Function.Injective (cycle p)

end Cyclic
end
end GraphProductRing

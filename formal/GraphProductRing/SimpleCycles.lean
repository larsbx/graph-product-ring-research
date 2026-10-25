import GraphProductRing.Cycles

namespace GraphProductRing
noncomputable section
variable {k : ℕ} [NeZero (k+k)]

def reverseWord (hk : 2 ≤ k) (w : Word k) : Word k := by
  classical
  refine ⟨fun i => w.val (-i-1), ?_, ?_⟩
  · intro a
    let e : {i : Pos k // w.val (-i-1) = a} ≃ {j : Pos k // w.val j = a} :=
      Equiv.subtypeEquiv ((Equiv.neg _).trans (Equiv.addRight (-1))) (fun _ => by simp [sub_eq_add_neg])
    exact (Fintype.card_congr e).trans (w.property.1 a)
  · intro i j h
    apply w.property.2
    rw [adjacent_next hk] at h ⊢
    rcases h with rfl | rfl
    · right; abel
    · left; abel

def reverseWalk (hk : 2 ≤ k) (p : CubeWalk k) : CubeWalk k := by
  refine ⟨(reverseWord hk p.val.1,
    fun t => cycle p (-⟨t.val % (k+k), Nat.mod_lt _ (NeZero.pos _)⟩)), ?_⟩
  intro i
  have hidx : (⟨(i.val+1) % (k+k), Nat.mod_lt _ (NeZero.pos _)⟩ : Pos k) = i+1 := by
    apply Fin.ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (show 1 < k+k by omega)]
  have hidx0 : (⟨i.val % (k+k), Nat.mod_lt _ (NeZero.pos _)⟩ : Pos k) = i := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  change cycle p (-⟨(i.val+1) % (k+k), _⟩) =
    flip (cycle p (-⟨i.val % (k+k), _⟩)) (p.val.1.val (-i-1))
  rw [hidx, hidx0]
  have hs := cycle_step p (-i-1)
  have he : -i-1+1 = -i := by abel
  rw [he] at hs
  have hf := congrArg (fun x => flip x (p.val.1.val (-i-1))) hs
  dsimp only at hf
  rw [flip_flip] at hf
  convert hf.symm using 1; congr 1; abel

@[simp] theorem cycle_reverse (hk : 2 ≤ k) (p : CubeWalk k) (i : Pos k) :
    cycle (reverseWalk hk p) i = cycle p (-i) := by
  simp [cycle, reverseWalk, Nat.mod_eq_of_lt i.isLt]

def SimpleWalk (k : ℕ) [NeZero (k+k)] := {p : CubeWalk k // Simple p}
instance : Fintype (SimpleWalk k) := by classical unfold SimpleWalk; infer_instance

def dihedralIndex (b : Bool) (d i : Pos k) : Pos k := if b then d-i else i+d

def dihedralWalk (hk : 2 ≤ k) (p : SimpleWalk k) (b : Bool) (d : Pos k) : SimpleWalk k := by
  refine ⟨if b then rotateWalk hk (reverseWalk hk p.val) (-d) else rotateWalk hk p.val d, ?_⟩
  cases b
  · change Function.Injective (cycle (rotateWalk hk p.val d))
    intro i j h
    simp only [cycle_rotate] at h
    exact add_right_cancel (p.property h)
  · change Function.Injective (cycle (rotateWalk hk (reverseWalk hk p.val) (-d)))
    intro i j h
    simp only [cycle_rotate, cycle_reverse] at h
    exact add_right_cancel (neg_injective (p.property h))

@[simp] theorem cycle_dihedral (hk : 2 ≤ k) (p : SimpleWalk k) (b : Bool) (d i : Pos k) :
    cycle (dihedralWalk hk p b d).val i = cycle p.val (dihedralIndex b d i) := by
  cases b <;> simp [dihedralWalk, dihedralIndex, sub_eq_add_neg, add_comm]

/-- Ordinary unoriented simple cycles: both rotations and reversal. -/
def unorientedSetoid (_hk : 2 ≤ k) : Setoid (SimpleWalk k) where
  r p q := ∃ b d, ∀ i, cycle q.val i = cycle p.val (dihedralIndex b d i)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p; exact ⟨false, 0, by simp [dihedralIndex]⟩
    · rintro p q ⟨b,d,hd⟩
      cases b
      · exact ⟨false, -d, fun i => by rw [hd]; simp [dihedralIndex]⟩
      · exact ⟨true, d, fun i => by rw [hd]; simp [dihedralIndex]⟩
    · rintro p q r ⟨b,d,hd⟩ ⟨c,e,he⟩
      cases b <;> cases c
      · exact ⟨false,e+d, fun i => by rw [he,hd]; simp [dihedralIndex,add_assoc]⟩
      · exact ⟨true,e+d, fun i => by rw [he,hd]; simp [dihedralIndex]; congr 1; abel⟩
      · exact ⟨true,d-e, fun i => by rw [he,hd]; simp [dihedralIndex]; congr 1; abel⟩
      · exact ⟨false,d-e, fun i => by rw [he,hd]; simp [dihedralIndex]; congr 1; abel⟩

abbrev UnorientedCycle (hk : 2 ≤ k) := Quotient (unorientedSetoid hk)
instance (hk : 2 ≤ k) : Fintype (UnorientedCycle hk) := Fintype.ofFinite _

lemma one_ne_neg_one (hk : 2 ≤ k) : (1 : Pos k) ≠ -1 := by
  intro h
  have he : (1 : Pos k) + 1 = 0 := by
    calc (1 : Pos k)+1 = -1+1 := congrArg (fun x => x+1) h
         _ = 0 := neg_add_cancel _
  have hv := congrArg Fin.val he
  have hn : 2 < k+k := by omega
  simp [Fin.val_add, Nat.mod_eq_of_lt (show 1 < k+k by omega), Nat.mod_eq_of_lt hn] at hv

/-- A simple cycle has exactly 2(2k) distinct roots and orientations. -/
def dihedralFiber (hk : 2 ≤ k) (p : SimpleWalk k) : Bool × Pos k ≃
    {q : SimpleWalk k // Quotient.mk (unorientedSetoid hk) q = Quotient.mk (unorientedSetoid hk) p} := by
  classical
  refine Equiv.ofBijective (fun bd => ⟨dihedralWalk hk p bd.1 bd.2, Quotient.sound ?_⟩) ⟨?_, ?_⟩
  · rcases bd with ⟨b,d⟩
    cases b
    · exact ⟨false,-d, fun i => by simp [dihedralIndex]⟩
    · exact ⟨true,d, fun i => by simp [dihedralIndex]⟩
  · rintro ⟨b,d⟩ ⟨c,e⟩ h
    have heq : ∀ i, dihedralIndex b d i = dihedralIndex c e i := by
      intro i
      apply p.property
      have ht := congrArg (fun q => cycle q.val.val i) h
      simpa only [cycle_dihedral] using ht
    have hde : d = e := by simpa [dihedralIndex] using heq 0
    subst e
    have hone := heq 1
    cases b <;> cases c
    · rfl
    · exfalso
      apply one_ne_neg_one hk
      apply add_right_cancel (b := d)
      calc (1 : Pos k)+d = d-1 := by simpa [dihedralIndex] using hone
           _ = -1+d := by abel
    · exfalso
      apply one_ne_neg_one hk
      apply add_right_cancel (b := d)
      calc (1 : Pos k)+d = d-1 := by simpa [dihedralIndex] using hone.symm
           _ = -1+d := by abel
    · rfl

  · rintro ⟨q,hq⟩
    obtain ⟨b,d,hd⟩ := Quotient.exact hq
    cases b
    · refine ⟨(false,-d), Subtype.ext (Subtype.ext (cycle_injective (funext ?_)))⟩
      intro i
      simp only [cycle_dihedral]
      rw [hd]
      simp [dihedralIndex]
    · refine ⟨(true,d), Subtype.ext (Subtype.ext (cycle_injective (funext ?_)))⟩
      intro i
      simp only [cycle_dihedral]
      rw [hd]
      simp [dihedralIndex]

theorem simple_normalization (hk : 2 ≤ k) :
    (4*k) * Fintype.card (UnorientedCycle hk) = Fintype.card (SimpleWalk k) := by
  classical
  have hc (c : UnorientedCycle hk) :
      Fintype.card {p : SimpleWalk k // Quotient.mk (unorientedSetoid hk) p = c} = 4*k := by
    induction c using Quotient.inductionOn with
    | h p =>
      rw [← Fintype.card_congr (dihedralFiber hk p), Fintype.card_prod,
        Fintype.card_bool, Fintype.card_fin]
      omega
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk (unorientedSetoid hk)))
  simp only [Fintype.card_sigma, hc, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  have he : Fintype.card (Quotient (unorientedSetoid hk)) = Fintype.card (UnorientedCycle hk) :=
    Fintype.card_congr (Equiv.refl _)
  rw [← he, Nat.mul_comm]
  exact h

end
end GraphProductRing

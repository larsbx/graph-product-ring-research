import GraphProductRing.SimpleCycles

namespace GraphProductRing
open scoped BigOperators
noncomputable section

/-- Independent raw coordinate sequence, before assuming double occurrence. -/
def rawCount {k} (w : Pos k → Fin k) (a : Fin k) : ℕ := Fintype.card {i // w i = a}

def rawVertex {k} (w : Pos k → Fin k) (s : Cube k) (t : ℕ) : Cube k :=
  fun a => s a ^^ decide ((Finset.univ.filter (fun i : Pos k => i.val < t ∧ w i = a)).card % 2 = 1)

theorem raw_closed_iff_even {k} (w : Pos k → Fin k) (s : Cube k) :
    rawVertex w s (k+k) = s ↔ ∀ a, rawCount w a % 2 = 0 := by
  have hc (a) : (Finset.univ.filter (fun i : Pos k => i.val < k+k ∧ w i = a)).card = rawCount w a := by
    simp [rawCount, Fintype.card_subtype]
  constructor
  · intro h a
    have hb := congrFun h a
    simp only [rawVertex, hc] at hb
    by_contra hn
    have hm : rawCount w a % 2 = 1 := by omega
    rw [hm] at hb
    cases hs : s a <;> simp [hs] at hb
  · intro h
    funext a
    simp only [rawVertex, hc, h]
    simp

lemma raw_count_sum {k} (w : Pos k → Fin k) : ∑ a, rawCount w a = k+k := by
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv w)
  simpa [Fintype.card_sigma, rawCount] using h

/-- Closure gives even multiplicities, full support gives nonzero
multiplicities, and the exact length budget forces every one to be two. -/
theorem maximal_support_twice {k} (w : Pos k → Fin k) (s : Cube k)
    (hclosed : rawVertex w s (k+k) = s) (hfull : Function.Surjective w) :
    ∀ a, rawCount w a = 2 := by
  have heven := (raw_closed_iff_even w s).mp hclosed
  have hlo (a) : 2 ≤ rawCount w a := by
    obtain ⟨i, hi⟩ := hfull a
    have hp : 0 < rawCount w a := Fintype.card_pos_iff.mpr ⟨i, hi⟩
    have := heven a
    omega
  have hsum := raw_count_sum w
  intro a
  have hall : (∑ b : Fin k, 2) = ∑ b, rawCount w b := by simpa [Nat.mul_two] using hsum.symm
  exact ((Finset.sum_eq_sum_iff_of_le (fun b _ => hlo b)).mp hall a (Finset.mem_univ a)).symm

/-- This is the admission from arbitrary full-support closed raw words to
our finite word type; the cyclic seam restriction is an explicit hypothesis. -/
def admitMaximalWord {k} (w : Pos k → Fin k) (s : Cube k)
    (hclosed : rawVertex w s (k+k) = s) (hfull : Function.Surjective w)
    (hnb : ∀ i j, Adjacent i j → w i ≠ w j) : Word k :=
  ⟨w, maximal_support_twice w s hclosed hfull, hnb⟩

@[simp] theorem raw_vertex_word {k} (w : Word k) (s : Cube k) (t : ℕ) :
    rawVertex w.val s t = vertex w s t := rfl

/-- The admitted raw word yields precisely its original vertex sequence. -/
@[simp] theorem admitted_vertices {k} (w : Pos k → Fin k) (s : Cube k)
    (hc : rawVertex w s (k+k) = s) (hf : Function.Surjective w)
    (hn : ∀ i j, Adjacent i j → w i ≠ w j) (t) :
    vertex (admitMaximalWord w s hc hf hn) s t = rawVertex w s t := rfl

end
end GraphProductRing

import GraphProductRing.Words

namespace GraphProductRing
open scoped BigOperators
noncomputable section

abbrev Cube (k : ℕ) := Fin k → Bool

def flip {k} (x : Cube k) (a : Fin k) : Cube k :=
  fun b => if b = a then !(x b) else x b

@[simp] theorem flip_flip {k} (x : Cube k) (a : Fin k) : flip (flip x a) a = x := by
  funext b
  by_cases h : b = a <;> simp [flip, h]

theorem flip_injective_axis {k} (x : Cube k) {a b : Fin k} : flip x a = flip x b ↔ a = b := by
  constructor
  · intro h
    by_contra hn
    have := congrFun h a
    simp [flip, hn] at this
  · rintro rfl; rfl

def occurrences {k} (w : Word k) (t : ℕ) (a : Fin k) : ℕ :=
  (Finset.univ.filter (fun i : Pos k => i.val < t ∧ w.val i = a)).card

def vertex {k} (w : Word k) (s : Cube k) (t : ℕ) : Cube k :=
  fun a => s a ^^ decide (occurrences w t a % 2 = 1)

@[simp] theorem vertex_zero {k} (w : Word k) (s : Cube k) : vertex w s 0 = s := by
  funext a
  simp [vertex, occurrences]

lemma occurrences_full {k} (w : Word k) (a : Fin k) : occurrences w (k+k) a = 2 := by
  have h := w.property.1 a
  simpa [occurrences, Fintype.card_subtype] using h

@[simp] theorem vertex_closed {k} (w : Word k) (s : Cube k) : vertex w s (k+k) = s := by
  funext a
  simp [vertex, occurrences_full]

lemma occurrences_step {k} (w : Word k) (i : Pos k) (a : Fin k) :
    occurrences w (i.val+1) a = occurrences w i.val a + if w.val i = a then 1 else 0 := by
  classical
  have heq : Finset.univ.filter (fun j : Pos k => j.val < i.val+1 ∧ w.val j = a) =
      if w.val i = a then insert i (Finset.univ.filter (fun j => j.val < i.val ∧ w.val j = a))
      else Finset.univ.filter (fun j => j.val < i.val ∧ w.val j = a) := by
    ext j
    by_cases ha : w.val i = a <;> simp only [ha, ↓reduceIte, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_insert]
    · constructor
      · rintro ⟨hj, hw⟩
        by_cases he : j = i
        · exact Or.inl he
        · exact Or.inr ⟨by have : j.val ≠ i.val := fun h => he (Fin.ext h); omega, hw⟩
      · rintro (rfl | ⟨hj, hw⟩)
        · exact ⟨by omega, ha⟩
        · exact ⟨by omega, hw⟩
    · constructor
      · rintro ⟨hj, hw⟩
        refine ⟨?_, hw⟩
        by_contra hn
        have he : j = i := Fin.ext (by omega)
        exact ha (he ▸ hw)
      · rintro ⟨hj, hw⟩; exact ⟨by omega, hw⟩
  unfold occurrences
  rw [heq]
  by_cases ha : w.val i = a <;> simp [ha]

theorem vertex_step {k} (w : Word k) (s : Cube k) (i : Pos k) :
    vertex w s (i.val+1) = flip (vertex w s i.val) (w.val i) := by
  funext a
  rw [vertex, occurrences_step]
  by_cases h : a = w.val i
  · subst a
    simp only [↓reduceIte, flip, vertex]
    have hp : occurrences w i.val (w.val i) % 2 = 0 ∨ occurrences w i.val (w.val i) % 2 = 1 := by omega
    rcases hp with hp | hp <;> cases hs : s (w.val i) <;> simp [Nat.add_mod, hp]
  · simp [flip, vertex, h, Ne.symm h]

/-- Actual vertex traversals, with a coordinate witness checked at every
step. The word can be recovered uniquely from the vertex trajectory. -/
def CubeWalk (k : ℕ) := {p : Word k × (Fin (k+k+1) → Cube k) //
  ∀ i : Pos k, p.2 ⟨i.val+1, by omega⟩ = flip (p.2 ⟨i.val, by omega⟩) (p.1.val i)}
instance (k) : Fintype (CubeWalk k) := by classical unfold CubeWalk; infer_instance

def toWalk {k} (s : Cube k) (w : Word k) : CubeWalk k :=
  ⟨(w, fun t => vertex w s t.val), vertex_step w s⟩

lemma walk_unique {k} (p : CubeWalk k) (t : Fin (k+k+1)) :
    p.val.2 t = vertex p.val.1 (p.val.2 0) t.val := by
  obtain ⟨n, hn⟩ := t
  induction n with
  | zero => simp
  | succ n ih =>
    have h := p.property ⟨n, by omega⟩
    rw [h, ih (by omega), vertex_step p.val.1 (p.val.2 0) ⟨n, by omega⟩]

def walkBijection (k) : Cube k × Word k ≃ CubeWalk k := by
  refine ⟨fun p => toWalk p.1 p.2, fun p => (p.val.2 0, p.val.1), ?_, ?_⟩
  · rintro ⟨s,w⟩; simp [toWalk]
  · intro p
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext t
      exact (walk_unique p t).symm

theorem rooted_count (k) : Fintype.card (CubeWalk k) = beta k := by
  rw [← Fintype.card_congr (walkBijection k), Fintype.card_prod, word_count]
  simp [Cube, beta, Nat.mul_assoc]

/-- Erasing the coordinate witness loses no information. -/
theorem trajectory_injective {k} : Function.Injective (fun p : CubeWalk k => p.val.2) := by
  intro p q h
  change p.val.2 = q.val.2 at h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    funext i
    have hp := p.property i
    have hq := q.property i
    rw [h] at hp
    have hf := hp.symm.trans hq
    exact (flip_injective_axis _).mp hf
  · exact h

theorem walk_closed {k} (p : CubeWalk k) : p.val.2 ⟨k+k, by omega⟩ = p.val.2 0 := by
  rw [walk_unique, vertex_closed]

/-- At maximal support, equal consecutive coordinates are exactly a
backtrack. This equivalence also applies across the cyclic seam. -/
theorem no_backtrack {k} (x : Cube k) (a b : Fin k) :
    flip (flip x a) b = x ↔ a = b := by
  constructor
  · intro h
    have := congrArg (fun y => flip y b) h
    dsimp only at this
    rw [flip_flip] at this
    exact (flip_injective_axis x).mp this
  · rintro rfl; exact flip_flip x a

theorem cyclic_word_no_backtrack {k} (w : Word k) (x : Cube k) (i j : Pos k)
    (h : Adjacent i j) : flip (flip x (w.val i)) (w.val j) ≠ x := by
  exact fun he => w.property.2 i j h ((no_backtrack _ _ _).mp he)

end
end GraphProductRing

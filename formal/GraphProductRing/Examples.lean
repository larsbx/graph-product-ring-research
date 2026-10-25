import GraphProductRing.SimpleCycles

/-! Kernel-reduced finite vectors; no native_decide or external oracle axiom. -/
namespace GraphProductRing

example : (∀ a : Fin 2, Fintype.card {i : Fin 4 // (![0,1,0,1] : Fin 4 → Fin 2) i = a} = 2) := by
  decide

example : (∀ i j : Pos 2, Adjacent i j →
    (![0,1,0,1] : Fin 4 → Fin 2) i ≠ (![0,1,0,1] : Fin 4 → Fin 2) j) := by
  decide

/-- The last-first pair is adjacent even though its integer difference is 5. -/
example : Adjacent (k := 3) 5 0 := by decide

example : (![0,1,2,1,2,0] : Fin 6 → Fin 3) 5 =
    (![0,1,2,1,2,0] : Fin 6 → Fin 3) 0 := by decide

/-- A label-periodic square still has four distinct actual prefix vertices. -/
example : (List.scanl (fun x a : ℕ => Nat.xor x (2^a)) 0 [0,1,0,1]) =
    [0,1,3,2,0] := by decide

/-- Two squares joined at a vertex give a primitive, nonsimple traversal. -/
example : (List.scanl (fun x a : ℕ => Nat.xor x (2^a)) 0 [0,1,0,1,2,3,2,3]) =
    [0,1,3,2,0,4,12,8,0] := by decide

end GraphProductRing

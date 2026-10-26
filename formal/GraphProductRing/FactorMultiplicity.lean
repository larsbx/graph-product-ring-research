import GraphProductRing.CartesianWalks
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace GraphProductRing
open scoped BigOperators
noncomputable section

/-- Oriented factor edge: the first endpoint is the walk's initial coordinate.
This absorbs the 2^k start-vertex choices without another quotient. -/
def FactorArc (G : FinGraph) := {e : G.V × G.V // G.graph.Adj e.1 e.2}
instance (G) : Fintype (FactorArc G) := by classical unfold FactorArc; infer_instance

def arcEndpoint {G : FinGraph} (e : FactorArc G) (b : Bool) : G.V :=
  if b then e.val.2 else e.val.1

lemma arcEndpoint_injective {G : FinGraph} (e : FactorArc G) : Function.Injective (arcEndpoint e) := by
  intro b c h
  cases b <;> cases c <;> simp_all [arcEndpoint, e.property.ne, Ne.symm e.property.ne]

lemma arcEndpoint_adj {G : FinGraph} (e : FactorArc G) (b : Bool) :
    G.graph.Adj (arcEndpoint e b) (arcEndpoint e (!b)) := by
  cases b
  · exact e.property
  · exact e.property.symm

def arcState {k} {G : Fin k → FinGraph} (e : ∀ a, FactorArc (G a)) (x : Cube k) : ProductVertex G :=
  fun a => arcEndpoint (e a) (x a)

lemma arcState_injective {k} {G : Fin k → FinGraph} (e : ∀ a, FactorArc (G a)) :
    Function.Injective (arcState e) := by
  intro x y h
  funext a
  exact arcEndpoint_injective (e a) (congrFun h a)

/-- Realization of existing cube walks on selected actual factor edges. -/
def realizeEdgeWord {k} [NeZero (k+k)] (hk : 2 ≤ k) {G : Fin k → FinGraph}
    (e : ∀ a, FactorArc (G a)) (w : Word k) : ProductWalk G (k+k) := by
  let c := toWalk (fun _ => false) w
  refine ⟨(w.val, fun t => arcState e (cycle c t)), ?_, ?_⟩
  · intro t
    change ProductStep G (arcState e (cycle c t)) (arcState e (cycle c (t+1))) (w.val t)
    rw [cycle_step]
    constructor
    · simpa [arcState, flip, c, toWalk] using arcEndpoint_adj (e (w.val t)) (cycle c t (w.val t))
    · intro a ha
      simp [arcState, flip, c, toWalk, ha]
  · intro t he
    have hc := arcState_injective e he
    rw [cycle_step, cycle_step] at hc
    exact cyclic_word_no_backtrack w (cycle c t) t (t+1)
      ((adjacent_next hk t (t+1)).mpr (Or.inl rfl)) hc

@[simp] theorem realize_axes {k} [NeZero (k+k)] (hk : 2 ≤ k) {G : Fin k → FinGraph}
    (e : ∀ a, FactorArc (G a)) (w : Word k) : (realizeEdgeWord hk e w).val.1 = w.val := rfl

@[simp] theorem realize_start {k} [NeZero (k+k)] (hk : 2 ≤ k) {G : Fin k → FinGraph}
    (e : ∀ a, FactorArc (G a)) (w : Word k) (a) :
    (realizeEdgeWord hk e w).val.2 0 a = (e a).val.1 := by
  simp [realizeEdgeWord, arcState, cycle, toWalk, arcEndpoint]

/-- Edge recovery is stated on actual vertices, including the initial point. -/
def EdgeRecovery {k} [NeZero (k+k)] {G : Fin k → FinGraph}
    (p : ProductWalk G (k+k)) (e : ∀ a, FactorArc (G a)) : Prop :=
  (∀ a, (e a).val.1 = p.val.2 0 a) ∧
  ∀ a t, p.val.2 t a = (e a).val.1 ∨ p.val.2 t a = (e a).val.2

theorem edge_recovery_exists {k} [NeZero (k+k)] {G : Fin k → FinGraph}
    (p : ProductWalk G (k+k)) (hf : Function.Surjective p.val.1) :
    ∃ e, EdgeRecovery p e := by
  have hex (a) : ∃ e : FactorArc (G a), e.val.1 = p.val.2 0 a ∧
      ∀ t, p.val.2 t a = e.val.1 ∨ p.val.2 t a = e.val.2 := by
    obtain ⟨i, _, hedge, hv⟩ := maximal_factor_edge p hf a
    rcases hv 0 with h0 | h0
    · exact ⟨⟨(_, _), hedge⟩, h0.symm, hv⟩
    · refine ⟨⟨(_, _), hedge.symm⟩, h0.symm, ?_⟩
      intro t
      exact (hv t).symm
  choose e he using hex
  exact ⟨e, fun a => (he a).1, fun a => (he a).2⟩

private lemma pair_other_unique {α : Type*} {u v a b c : α} (huv : u ≠ v)
    (hu : u = a ∨ u = b) (hv : v = a ∨ v = b)
    (hu' : u = a ∨ u = c) (hv' : v = a ∨ v = c) : b = c := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
    rcases hu' with h | h <;> rcases hv' with h' | h' <;> aesop

/-- The edge tuple is recoverable uniquely; it is not merely chosen from a
cube containing the walk. This prevents edge-tuple overcount. -/
theorem edge_recovery_unique {k} [NeZero (k+k)] {G : Fin k → FinGraph}
    (p : ProductWalk G (k+k)) (hf : Function.Surjective p.val.1)
    {e f : ∀ a, FactorArc (G a)} (he : EdgeRecovery p e) (hf' : EdgeRecovery p f) : e = f := by
  funext a
  obtain ⟨t, ht⟩ := hf a
  have hedge := (p.property.1 t).1
  rw [ht] at hedge
  apply Subtype.ext
  apply Prod.ext
  · exact (he.1 a).trans (hf'.1 a).symm
  · apply pair_other_unique hedge.ne (he.2 a t) (he.2 a (t+1))
    · simpa only [hf'.1 a, ← he.1 a] using hf'.2 a t
    · simpa only [hf'.1 a, ← he.1 a] using hf'.2 a (t+1)

lemma edge_recovery_realize {k} [NeZero (k+k)] (hk : 2 ≤ k) {G : Fin k → FinGraph}
    (e : ∀ a, FactorArc (G a)) (w : Word k) : EdgeRecovery (realizeEdgeWord hk e w) e := by
  constructor
  · intro a
    exact (realize_start hk e w a).symm
  · intro a t
    change arcEndpoint (e a) (cycle (toWalk (fun _ => false) w) t a) = (e a).val.1 ∨
      arcEndpoint (e a) (cycle (toWalk (fun _ => false) w) t a) = (e a).val.2
    cases cycle (toWalk (fun _ => false) w) t a <;> simp [arcEndpoint]

private lemma edge_successor_unique {k} {G : Fin k → FinGraph}
    (e : ∀ a, FactorArc (G a)) {x y z : ProductVertex G} {a : Fin k}
    (hx : ∀ b, x b = (e b).val.1 ∨ x b = (e b).val.2)
    (hy : ∀ b, y b = (e b).val.1 ∨ y b = (e b).val.2)
    (hz : ∀ b, z b = (e b).val.1 ∨ z b = (e b).val.2)
    (hxy : ProductStep G x y a) (hxz : ProductStep G x z a) : y = z := by
  funext b
  by_cases hb : b = a
  · subst b
    have hne := hxy.1.ne
    have hne' := hxz.1.ne
    rcases hx a with h | h <;> rcases hy a with h' | h' <;>
      rcases hz a with h'' | h'' <;> aesop
  · exact (hxy.2 b hb).symm.trans (hxz.2 b hb)

/-- Fixed recoverable edges, axes and initial vertex determine the traversal. -/
theorem product_edge_walk_unique {k} [NeZero (k+k)] {G : Fin k → FinGraph}
    (e : ∀ a, FactorArc (G a)) {p r : ProductWalk G (k+k)}
    (hp : EdgeRecovery p e) (hr : EdgeRecovery r e) (hw : p.val.1 = r.val.1) : p = r := by
  apply product_trajectory_injective G
  change p.val.2 = r.val.2
  funext t
  obtain ⟨n, hn⟩ := t
  induction n with
  | zero => funext a; exact (hp.1 a).symm.trans (hr.1 a)
  | succ n ih =>
    let i : Pos k := ⟨n, by omega⟩
    have he : i+1 = (⟨n+1, hn⟩ : Pos k) := by
      apply Fin.ext
      simp [i, Fin.val_add, Nat.mod_eq_of_lt hn]
    have hpi := p.property.1 i
    have hri := r.property.1 i
    have hi : p.val.2 i = r.val.2 i := ih (by omega)
    rw [← hw, ← hi] at hri
    have hstep := edge_successor_unique e (fun a => hp.2 a i)
      (fun a => hp.2 a (i+1)) (fun a => hr.2 a (i+1)) hpi hri
    rw [he] at hstep
    exact hstep

def FullProductWalk {k} (G : Fin k → FinGraph) [NeZero (k+k)] :=
  {p : ProductWalk G (k+k) // Function.Surjective p.val.1}
instance {k} (G : Fin k → FinGraph) [NeZero (k+k)] : Fintype (FullProductWalk G) := by
  classical unfold FullProductWalk; infer_instance

def recoveredEdges {k} [NeZero (k+k)] {G : Fin k → FinGraph} (p : FullProductWalk G) :
    ∀ a, FactorArc (G a) := (edge_recovery_exists p.val p.property).choose

lemma recoveredEdges_spec {k} [NeZero (k+k)] {G : Fin k → FinGraph} (p : FullProductWalk G) :
    EdgeRecovery p.val (recoveredEdges p) := (edge_recovery_exists p.val p.property).choose_spec

/-- The full-support actual-factor correspondence consumes Word k from the
merged proof. Oriented edge choices include all factor start endpoints. -/
def fullSupportEdgeBijection {k} [NeZero (k+k)] (hk : 2 ≤ k) (G : Fin k → FinGraph) :
    FullProductWalk G ≃ (∀ a, FactorArc (G a)) × Word k where
  toFun p := (recoveredEdges p, productMaximalWord hk p.val p.property)
  invFun x := ⟨realizeEdgeWord hk x.1 x.2, word_surjective x.2⟩
  left_inv p := by
    apply Subtype.ext
    exact product_edge_walk_unique (recoveredEdges p)
      (edge_recovery_realize hk _ _) (recoveredEdges_spec p) rfl
  right_inv x := by
    apply Prod.ext
    · exact edge_recovery_unique _ (word_surjective x.2)
        (recoveredEdges_spec _) (edge_recovery_realize hk x.1 x.2)
    · apply Subtype.ext
      rfl

/-- Factor multiplicity before converting oriented arcs into unoriented edges.
The word-label factorial is reused from word_count, never assumed. -/
theorem full_support_arc_count {k} [NeZero (k+k)] (hk : 2 ≤ k) (G : Fin k → FinGraph) :
    Fintype.card (FullProductWalk G) = (∏ a, Fintype.card (FactorArc (G a))) *
      (k.factorial * R k) := by
  rw [Fintype.card_congr (fullSupportEdgeBijection hk G), Fintype.card_prod, word_count]
  simp [Fintype.card_pi]

/-- The ordinary unoriented edge count, not half a walk or cycle count. -/
def FinGraph.edges (G : FinGraph) : ℕ := by
  classical
  exact G.graph.edgeFinset.card

lemma factor_arc_count (G : FinGraph) : Fintype.card (FactorArc G) = 2 * G.edges := by
  classical
  let e : FactorArc G ≃ G.graph.Dart :=
    ⟨fun a => ⟨a.val, a.property⟩, fun a => ⟨a.toProd, a.adj⟩, by intro a; rfl, by intro a; rfl⟩
  rw [Fintype.card_congr e, SimpleGraph.dart_card_eq_twice_card_edges]
  rfl

/-- The finite maximal-support factor coefficient. This is an actual-walk
cardinality, not yet an assertion about a graph-ring differential operator. -/
theorem full_support_factor_count {k} [NeZero (k+k)] (hk : 2 ≤ k) (G : Fin k → FinGraph) :
    Fintype.card (FullProductWalk G) = beta k * ∏ a, (G a).edges := by
  rw [full_support_arc_count hk G]
  simp_rw [factor_arc_count]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold beta
  ring

end
end GraphProductRing

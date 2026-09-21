/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey
-/
module

public import LeanPool.GoemansFlow.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases

/-! # A counterexample to Goemans' cost conjecture

Jason Hickey directed Claude's formal verification of Dmitry Rybin's counterexample,
discovered with GPT-5.6 Pro. Upstream also acknowledges Katherine Schlitz.
Adapted from `jyh/dinitz-verify`, commit `ffba3523f0edd14be3460d039f22a6b98c02fd9e`.

The splittable flow costs 58; every unsplittable routing satisfying the additive
maximum-demand capacity bound costs at least 60, and this lower bound is attained.
Generic coefficient transfer gives refutations over all linearly ordered commutative rings.
-/

@[expose] public section

namespace GoemansFlow

/-! ## 1.  The counterexample instance -/

/-- The seven vertices. -/
inductive Vertex | s | u | v | w | t1 | t2 | t3
  deriving DecidableEq, Repr

instance : Fintype Vertex where
  elems := {.s, .u, .v, .w, .t1, .t2, .t3}
  complete := by intro vertex; cases vertex <;> decide

/-- The nine arcs. -/
inductive Arc | st1 | st2 | su | ut3 | uv | vt1 | vw | wt2 | wt3
  deriving DecidableEq, Repr

instance : Fintype Arc where
  elems := {.st1, .st2, .su, .ut3, .uv, .vt1, .vw, .wt2, .wt3}
  complete := by intro arc; cases arc <;> decide

/-- Tail vertex of each arc in the counterexample. -/
def tail : Arc → Vertex
  | .st1 => .s  | .st2 => .s  | .su  => .s
  | .ut3 => .u  | .uv  => .u
  | .vt1 => .v  | .vw  => .v
  | .wt2 => .w  | .wt3 => .w

/-- Head vertex of each arc in the counterexample. -/
def head : Arc → Vertex
  | .st1 => .t1 | .st2 => .t2 | .su  => .u
  | .ut3 => .t3 | .uv  => .v
  | .vt1 => .t1 | .vw  => .w
  | .wt2 => .t2 | .wt3 => .t3

/-- The fractional (splittable) flow `x`. -/
def fractionalFlow : Arc → ℤ
  | .st1 => 10 | .st2 => 6 | .su  => 24
  | .ut3 => 10 | .uv  => 14
  | .vt1 => 5  | .vw  => 9
  | .wt2 => 4  | .wt3 => 5

/-- The cost vector `c`. -/
def arcCost : Arc → ℤ
  | .st1 => 2 | .st2 => 3 | .su  => 0
  | .ut3 => 2 | .uv  => 0
  | .vt1 => 0 | .vw  => 0
  | .wt2 => 0 | .wt3 => 0

/-- Terminal of commodity `i`. -/
def terminal (i : Fin 3) : Vertex := if i = 0 then .t1 else if i = 1 then .t2 else .t3

/-- Demand of commodity `i`. -/
def demand (i : Fin 3) : ℤ := if i = 0 then 15 else if i = 1 then 10 else 15

/-- `d_max`, the largest demand. -/
def maximumDemand : ℤ := 15

theorem maximumDemand_is_max :
    (∀ i, demand i ≤ maximumDemand) ∧ (∃ i, demand i = maximumDemand) := by decide

theorem demand_pos : ∀ i, 0 < demand i := by decide

theorem arcCost_nonneg : ∀ a, 0 ≤ arcCost a := by decide

theorem fractionalFlow_nonneg : ∀ a, 0 ≤ fractionalFlow a := by decide

theorem terminal_injective : Function.Injective terminal := by decide

theorem terminal_ne_source : ∀ i, terminal i ≠ Vertex.s := by decide

/-- The instance is a *simple* digraph: no two arcs share both endpoints. -/
theorem arcs_simple : Function.Injective (fun a : Arc => (tail a, head a)) := by decide

/-- The instance has no self-loops. -/
theorem no_self_loops : ∀ a : Arc, tail a ≠ head a := by decide

/-- Flow conservation at every vertex other than the source: inflow − outflow = demand
absorbed there (which is `0` at non-terminals). -/
theorem flow_feasible : ∀ z : Vertex, z ≠ Vertex.s →
    (∑ a : Arc, if head a = z then fractionalFlow a else 0)
      - (∑ a : Arc, if tail a = z then fractionalFlow a else 0)
      = ∑ i : Fin 3, if terminal i = z then demand i else 0 := by decide

/-- Flow conservation at the source: net outflow = total demand. -/
theorem conservation_source :
    (∑ a : Arc, if tail a = Vertex.s then fractionalFlow a else 0)
      - (∑ a : Arc, if head a = Vertex.s then fractionalFlow a else 0)
      = ∑ i : Fin 3, demand i := by decide

/-! ## 2.  Loads and costs -/

/-- A routing: one walk from `s` to `t_i` per commodity `i`. -/
def IsRouting (p : Fin 3 → List Arc) : Prop :=
  ∀ i : Fin 3, IsWalk tail head Vertex.s (p i) (terminal i)

/-- Capacity-good: every arc load stays within `x(a) + d_max`. -/
def CapacityGood (p : Fin 3 → List Arc) : Prop :=
  ∀ a : Arc, unsplittableLoad demand p a ≤ fractionalFlow a + maximumDemand

/-- Cost of a routing. -/
def routingCost (p : Fin 3 → List Arc) : ℤ := ∑ a : Arc, arcCost a * unsplittableLoad demand p a

/-- The cost of the fractional flow. -/
theorem fractional_cost : (∑ a : Arc, arcCost a * fractionalFlow a) = 58 := by decide

/-! ## 3.  Path completeness: the digraph has exactly six s-t_i walks -/

/-- All nine arcs, in the order used for walk enumeration. -/
def allArcs : List Arc := [.st1, .st2, .su, .ut3, .uv, .vt1, .vw, .wt2, .wt3]

theorem mem_allArcs : ∀ e : Arc, e ∈ allArcs := by decide

/-- Arcs leaving `x`. -/
def outOf (x : Vertex) : List Arc := allArcs.filter (fun e => decide (tail e = x))

theorem mem_outOf {e : Arc} {x : Vertex} (h : tail e = x) : e ∈ outOf x :=
  List.mem_filter.mpr ⟨mem_allArcs e, by simp [h]⟩

/-- All walks of length at most `n` starting at `x`, paired with their endpoint. -/
def walksFrom : ℕ → Vertex → List (List Arc × Vertex)
  | 0, x => [([], x)]
  | n + 1, x => ([], x) :: (outOf x).flatMap (fun e =>
      (walksFrom n (head e)).map (fun q => (e :: q.1, q.2)))

theorem walksFrom_complete : ∀ (n : ℕ) (x : Vertex) (l : List Arc) (y : Vertex),
    l.length ≤ n → IsWalk tail head x l y → (l, y) ∈ walksFrom n x := by
  intro n
  induction n with
  | zero =>
    intro x l y hl hw
    cases l with
    | nil => obtain rfl : x = y := hw; simp [walksFrom]
    | cons e l => simp at hl
  | succ n ih =>
    intro x l y hl hw
    cases l with
    | nil => obtain rfl : x = y := hw; simp [walksFrom]
    | cons e l =>
      obtain ⟨he, hw'⟩ := hw
      have hl' : l.length ≤ n := by simp at hl; omega
      have hmem := ih (head e) l y hl' hw'
      simp only [walksFrom, List.mem_cons, List.mem_flatMap, List.mem_map]
      exact Or.inr ⟨e, mem_outOf he, (l, y), hmem, rfl⟩

/-- A topological rank certifying acyclicity. -/
def rank : Vertex → ℕ
  | .s => 0 | .u => 1 | .v => 2 | .w => 3 | .t1 => 4 | .t2 => 4 | .t3 => 4

theorem rank_arc : ∀ e : Arc, rank (tail e) < rank (head e) := by decide

theorem rank_le_four : ∀ z : Vertex, rank z ≤ 4 := by decide

theorem walk_len : ∀ (x : Vertex) (l : List Arc) (y : Vertex),
    IsWalk tail head x l y → l.length + rank x ≤ rank y := by
  intro x l
  induction l generalizing x with
  | nil => intro y hw; obtain rfl : x = y := hw; simp
  | cons e l ih =>
    intro y hw
    obtain ⟨he, hw'⟩ := hw
    have h1 := rank_arc e
    have h2 := ih (head e) y hw'
    subst he
    simp only [List.length_cons] at *
    omega

theorem walk_from_s_mem (l : List Arc) (y : Vertex) (h : IsWalk tail head Vertex.s l y) :
    (l, y) ∈ walksFrom 4 Vertex.s := by
  have hb := walk_len _ _ _ h
  have h4 := rank_le_four y
  have h0 : rank Vertex.s = 0 := rfl
  refine walksFrom_complete 4 _ _ _ ?_ h
  omega

/-- The explicit enumeration of all walks of length ≤ 4 out of the source. -/
theorem walksFrom_s_eq : walksFrom 4 Vertex.s =
    [([], Vertex.s),
     ([Arc.st1], Vertex.t1),
     ([Arc.st2], Vertex.t2),
     ([Arc.su], Vertex.u),
     ([Arc.su, Arc.ut3], Vertex.t3),
     ([Arc.su, Arc.uv], Vertex.v),
     ([Arc.su, Arc.uv, Arc.vt1], Vertex.t1),
     ([Arc.su, Arc.uv, Arc.vw], Vertex.w),
     ([Arc.su, Arc.uv, Arc.vw, Arc.wt2], Vertex.t2),
     ([Arc.su, Arc.uv, Arc.vw, Arc.wt3], Vertex.t3)] := by rfl

/-- The two s-t1 paths. -/
def expensivePathOne : List Arc := [.st1]
/-- The zero-cost path to the first terminal. -/
def zeroCostPathOne : List Arc := [.su, .uv, .vt1]
/-- The two s-t2 paths. -/
def expensivePathTwo : List Arc := [.st2]
/-- The zero-cost path to the second terminal. -/
def zeroCostPathTwo : List Arc := [.su, .uv, .vw, .wt2]
/-- The two s-t3 paths. -/
def expensivePathThree : List Arc := [.su, .ut3]
/-- The zero-cost path to the third terminal. -/
def zeroCostPathThree : List Arc := [.su, .uv, .vw, .wt3]

theorem paths_t1 (l : List Arc) (h : IsWalk tail head Vertex.s l Vertex.t1) :
    l = expensivePathOne ∨ l = zeroCostPathOne := by
  have hm := walk_from_s_mem l Vertex.t1 h
  rw [walksFrom_s_eq] at hm
  simpa [expensivePathOne, zeroCostPathOne] using hm

theorem paths_t2 (l : List Arc) (h : IsWalk tail head Vertex.s l Vertex.t2) :
    l = expensivePathTwo ∨ l = zeroCostPathTwo := by
  have hm := walk_from_s_mem l Vertex.t2 h
  rw [walksFrom_s_eq] at hm
  simpa [expensivePathTwo, zeroCostPathTwo] using hm

theorem paths_t3 (l : List Arc) (h : IsWalk tail head Vertex.s l Vertex.t3) :
    l = expensivePathThree ∨ l = zeroCostPathThree := by
  have hm := walk_from_s_mem l Vertex.t3 h
  rw [walksFrom_s_eq] at hm
  simpa [expensivePathThree, zeroCostPathThree] using hm

/-- The positive-cost path for commodity `i`. -/
def expensivePath (i : Fin 3) : List Arc :=
  if i = 0 then expensivePathOne else if i = 1 then expensivePathTwo else expensivePathThree
/-- The zero-cost path for commodity `i`. -/
def zeroCostPath (i : Fin 3) : List Arc :=
  if i = 0 then zeroCostPathOne else if i = 1 then zeroCostPathTwo else zeroCostPathThree

/-- **Path completeness.**  For each commodity `i`, the arc-lists forming a walk from the
source `s` to the terminal `t_i` are *exactly* the two listed paths.  This is derived from
the arc list — via the enumeration `walksFrom` together with the topological rank bounding
every walk by 4 arcs — and not assumed. -/
theorem path_complete (i : Fin 3) (l : List Arc) :
    IsWalk tail head Vertex.s l (terminal i) ↔ (l = expensivePath i ∨ l = zeroCostPath i) := by
  constructor
  · intro h
    fin_cases i
    · exact paths_t1 l h
    · exact paths_t2 l h
    · exact paths_t3 l h
  · intro h
    fin_cases i <;> rcases h with rfl | rfl <;> decide

/-- Conversely, all six really are walks. -/
theorem the_six_are_walks :
    IsWalk tail head Vertex.s expensivePathOne Vertex.t1 ∧
    IsWalk tail head Vertex.s zeroCostPathOne Vertex.t1 ∧
    IsWalk tail head Vertex.s expensivePathTwo Vertex.t2 ∧
    IsWalk tail head Vertex.s zeroCostPathTwo Vertex.t2 ∧
    IsWalk tail head Vertex.s expensivePathThree Vertex.t3 ∧
    IsWalk tail head Vertex.s zeroCostPathThree Vertex.t3 := by decide

/-- The vertex sequence visited by a walk. -/
def vertexSequence (x : Vertex) (l : List Arc) : List Vertex := x :: l.map head

/-- Each of the six s-t_i walks is a *simple path* (no repeated vertex), so restricting
Conjecture 1.3 to simple paths would not help. -/
theorem the_six_walks_are_simple :
    (vertexSequence Vertex.s expensivePathOne).Nodup ∧
    (vertexSequence Vertex.s zeroCostPathOne).Nodup ∧
    (vertexSequence Vertex.s expensivePathTwo).Nodup ∧
    (vertexSequence Vertex.s zeroCostPathTwo).Nodup ∧
    (vertexSequence Vertex.s expensivePathThree).Nodup ∧
    (vertexSequence Vertex.s zeroCostPathThree).Nodup := by decide

/-! ## 4.  Layer A: the eight-case check and the cost lower bound -/

/-- The load written as a function of the three chosen paths. -/
def loadThree (q0 q1 q2 : List Arc) (a : Arc) : ℤ :=
  (if a ∈ q0 then demand 0 else 0) + (if a ∈ q1 then demand 1 else 0) +
    (if a ∈ q2 then demand 2 else 0)

/-- Routing cost expressed in terms of the three chosen paths. -/
def routingCostThree (q0 q1 q2 : List Arc) : ℤ := ∑ a : Arc, arcCost a * loadThree q0 q1 q2 a

theorem unsplittableLoad_eq (p : Fin 3 → List Arc) (a : Arc) :
    unsplittableLoad demand p a = loadThree (p 0) (p 1) (p 2) a := by
  simp only [unsplittableLoad, loadThree, Fin.sum_univ_three]

theorem routingCost_eq (p : Fin 3 → List Arc) :
    routingCost p = routingCostThree (p 0) (p 1) (p 2) :=
  Finset.sum_congr rfl fun a _ => by rw [unsplittableLoad_eq]

/-- **The eight-case kernel check.**  Over the eight combinations of path choices, every
capacity-good one costs at least 60. -/
theorem enum_check :
    ∀ q0 ∈ [expensivePathOne, zeroCostPathOne],
    ∀ q1 ∈ [expensivePathTwo, zeroCostPathTwo],
    ∀ q2 ∈ [expensivePathThree, zeroCostPathThree],
    (∀ a : Arc, loadThree q0 q1 q2 a ≤ fractionalFlow a + maximumDemand) →
    60 ≤ routingCostThree q0 q1 q2 := by decide

/-- **Layer A (main).**  Every unsplittable routing of the three demands along arbitrary
walks out of `s` whose arc loads stay within `x(a) + d_max` costs at least 60 — strictly
more than the fractional cost 58. -/
theorem min_cost_capacity_good (p : Fin 3 → List Arc) (hr : IsRouting p) (hc : CapacityGood p) :
    60 ≤ routingCost p := by
  have h0 : p 0 ∈ [expensivePathOne, zeroCostPathOne] := by
    have := paths_t1 (p 0) (hr 0); simpa using this
  have h1 : p 1 ∈ [expensivePathTwo, zeroCostPathTwo] := by
    have := paths_t2 (p 1) (hr 1); simpa using this
  have h2 : p 2 ∈ [expensivePathThree, zeroCostPathThree] := by
    have := paths_t3 (p 2) (hr 2); simpa using this
  rw [routingCost_eq]
  refine enum_check _ h0 _ h1 _ h2 (fun a => ?_)
  have := hc a
  rwa [unsplittableLoad_eq] at this

/-! ### Non-vacuity and tightness -/

/-- Route every commodity on its "expensive" path. -/
def allExpensiveRoute : Fin 3 → List Arc := expensivePath

/-- Route `t1`, `t2` expensively and `t3` on the zero-cost path: cost exactly 60. -/
def optimalRoute : Fin 3 → List Arc :=
  fun i => if i = 0 then expensivePathOne else if i = 1 then expensivePathTwo else zeroCostPathThree

theorem exists_capacity_good : IsRouting allExpensiveRoute ∧ CapacityGood allExpensiveRoute := by
  constructor
  · intro i; revert i; decide
  · intro a; revert a; decide

theorem cost_sixty_attained :
    IsRouting optimalRoute ∧ CapacityGood optimalRoute ∧ routingCost optimalRoute = 60 := by
  refine ⟨?_, ?_, by decide⟩
  · intro i; revert i; decide
  · intro a; revert a; decide

/-- **Positive control.**  The instance *does* satisfy the conclusion of DGG Theorem 1.2
(the capacity clause (i) on its own): an unsplittable routing with
`flow_P(a) ≤ x(a) + d_max` for every arc `a` exists.  So the refutation isolates
clause (ii), the cost clause — it is not an artifact of an unsatisfiable capacity
requirement. -/
theorem dgg_theorem_holds_here :
    ∃ p : Fin 3 → List Arc, IsRouting p ∧
    ∀ a : Arc, unsplittableLoad demand p a ≤ fractionalFlow a + maximumDemand :=
  ⟨allExpensiveRoute, exists_capacity_good.1, exists_capacity_good.2⟩

/-- Route every commodity on its zero-cost path. -/
def allZeroCostRoute : Fin 3 → List Arc := zeroCostPath

/-- **Positive control for the other clause.**  Clause (ii) of Conjecture 1.3 -- the cost
clause -- is *also* satisfiable on its own here: the all-`Z` routing costs `0 ≤ 58 = c^T x`.
So neither clause is individually unsatisfiable at this instance; only their conjunction
fails, which is what makes the instance a counterexample to Conjecture 1.3 rather than to
either half of it. -/
theorem cost_clause_alone_satisfiable :
    IsRouting allZeroCostRoute ∧
    routingCost allZeroCostRoute ≤ ∑ a : Arc, arcCost a * fractionalFlow a := by
  refine ⟨?_, ?_⟩
  · intro i; revert i; decide
  · decide

/-- **No conflict with the primary source's planar theorems.**  Planarity is not formalized here.
The instance satisfies the numerical conclusion of the planar result in
arXiv:2308.02651.  Theorem 1.8 of that paper grants a two-sided violation of `2·d_max`
together with the cost bound, and its conclusion *is* satisfied here: the all-`Z` routing
keeps every arc load within `2·d_max = 30` of `x` on both sides and costs `0 ≤ 58`.  The
counterexample therefore refutes the `d_max` grade only, exactly as Conjecture 1.3 states
it. -/
theorem two_dmax_conclusion_holds_here :
    IsRouting allZeroCostRoute ∧
    (∀ a : Arc, fractionalFlow a - 2 * maximumDemand ≤ unsplittableLoad demand allZeroCostRoute a ∧
      unsplittableLoad demand allZeroCostRoute a ≤ fractionalFlow a + 2 * maximumDemand) ∧
    routingCost allZeroCostRoute ≤ ∑ a : Arc, arcCost a * fractionalFlow a := by
  refine ⟨?_, ?_, ?_⟩
  · intro i; revert i; decide
  · intro a; revert a; decide
  · decide

/-- 60 is exactly the optimum: it is a lower bound and it is attained. -/
theorem optimum_is_sixty :
    (∀ p : Fin 3 → List Arc, IsRouting p → CapacityGood p → 60 ≤ routingCost p) ∧
    (∃ p : Fin 3 → List Arc, IsRouting p ∧ CapacityGood p ∧ routingCost p = 60) :=
  ⟨min_cost_capacity_good, optimalRoute, cost_sixty_attained.1, cost_sixty_attained.2.1,
    cost_sixty_attained.2.2⟩

/-! ## 5.  Layer B: the conjecture, and its refutation -/

/-- **Goemans' cost conjecture** (Dinitz–Garg–Goemans / SSUF), Conjecture 1.3 of
arXiv:2308.02651, stated over a linearly ordered commutative ring `R`.

Read: for every finite digraph `(W, E)` with arc endpoints `tail`, `head`, every source
`src`, every finite family of commodities `K` with distinct terminals `term k ≠ src` and
positive demands `d k`, every `dmax` equal to the maximum demand, every nonnegative cost
vector `c` and every nonnegative feasible single-source flow `x` routing the demands,
there is an unsplittable routing `P` (one walk per commodity) with

* `flow_P(a) ≤ x(a) + dmax` for every arc `a`, and
* `c^T flow_P ≤ c^T x`.

This form ranges over arbitrary directed graphs and omits capacities. The refutation
of `GoemansCostConjectureFull` also supplies a simple, loopless, acyclic instance with
explicit capacities, avoiding dependence on these differences from the source. -/
def GoemansCostConjecture (R : Type) [CommRing R] [LinearOrder R] : Prop :=
  ∀ (W E K : Type) [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E] [Fintype K]
    (tail head : E → W) (src : W) (term : K → W) (d : K → R) (dmax : R) (x c : E → R),
    -- the terminals are distinct from each other and from the source
    Function.Injective term →
    (∀ k, term k ≠ src) →
    -- demands are positive and `dmax` is the maximum demand
    (∀ k, 0 < d k) →
    (∀ k, d k ≤ dmax) →
    (∃ k, d k = dmax) →
    -- nonnegative costs and a nonnegative flow
    (∀ a, 0 ≤ c a) →
    (∀ a, 0 ≤ x a) →
    -- `x` is a feasible single-source flow for the demands
    (∀ z : W, z ≠ src →
      (∑ a : E, if head a = z then x a else 0) - (∑ a : E, if tail a = z then x a else 0)
        = ∑ k : K, if term k = z then d k else 0) →
    ((∑ a : E, if tail a = src then x a else 0)
        - (∑ a : E, if head a = src then x a else 0) = ∑ k : K, d k) →
    -- conclusion
    ∃ P : K → List E,
      (∀ k, IsWalk tail head src (P k) (term k)) ∧
      (∀ a, unsplittableLoad d P a ≤ x a + dmax) ∧
      (∑ a : E, c a * unsplittableLoad d P a) ≤ ∑ a : E, c a * x a

/-- **The Full form is the weaker Prop.**  It is `GoemansCostConjecture` with four hypotheses
added (simple, loopless, acyclic, `x ≤ u`), so the bare conjecture implies it.  Hence
`¬ GoemansCostConjectureFull` is the stronger statement, and it implies
`¬ GoemansCostConjecture`. -/
theorem GoemansCostConjectureFull_of_GoemansCostConjecture
    (R : Type) [CommRing R] [LinearOrder R]
    (h : GoemansCostConjecture R) : GoemansCostConjectureFull R := by
  intro W E K _ _ _ _ _ tail head src term d dmax x c _u _hsimple _hloop _hacyc _hxu
    hinj hns hpos hle hex hc hx hcons hsrc
  exact h W E K tail head src term d dmax x c hinj hns hpos hle hex hc hx hcons hsrc

section Transfer

variable {R : Type} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

omit [LinearOrder R] [IsStrictOrderedRing R] in
private theorem cast_sum_ite {ι : Type} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (f : ι → ℤ) :
    (∑ i : ι, if P i then ((f i : R)) else 0) = (((∑ i : ι, if P i then f i else 0 : ℤ) : R)) := by
  rw [Int.cast_sum]
  exact Finset.sum_congr rfl fun i _ => by split <;> simp

omit [LinearOrder R] [IsStrictOrderedRing R] in
private theorem unsplittableLoad_cast {K E : Type} [Fintype K] [DecidableEq E]
    (d : K → ℤ) (P : K → List E) (a : E) :
    unsplittableLoad (fun k => ((d k : R))) P a = ((unsplittableLoad d P a : ℤ) : R) := by
  simp only [unsplittableLoad]
  exact cast_sum_ite (R := R) (fun k => a ∈ P k) d

/-- If the conjecture held over `R`, it would hold over `ℤ` (an integral instance is an
`R`-instance, and the conclusion pulls back along the order embedding `ℤ ↪ R`). -/
theorem GoemansCostConjecture_int_of (h : GoemansCostConjecture R) : GoemansCostConjecture ℤ := by
  intro W E K _ _ _ _ _ tail head src term d dmax x c hinj hns hpos hle hex hc hx hcons hsrc
  obtain ⟨P, hw, hcap, hcost⟩ :=
    h W E K tail head src term (fun k => ((d k : R))) ((dmax : R))
      (fun a => ((x a : R))) (fun a => ((c a : R)))
      hinj hns
      (fun k => by exact_mod_cast hpos k)
      (fun k => by exact_mod_cast hle k)
      (by obtain ⟨k, hk⟩ := hex; exact ⟨k, by exact_mod_cast hk⟩)
      (fun a => by exact_mod_cast hc a)
      (fun a => by exact_mod_cast hx a)
      (fun z hz => by
        rw [cast_sum_ite, cast_sum_ite, cast_sum_ite]
        exact_mod_cast congrArg (fun t : ℤ => ((t : R))) (hcons z hz))
      (by
        rw [cast_sum_ite, cast_sum_ite, ← Int.cast_sum]
        exact_mod_cast congrArg (fun t : ℤ => ((t : R))) hsrc)
  refine ⟨P, hw, fun a => ?_, ?_⟩
  · have := hcap a
    rw [unsplittableLoad_cast] at this
    exact_mod_cast this
  · have := hcost
    simp only [unsplittableLoad_cast] at this
    exact_mod_cast this

/-- The same transfer for the literature-faithful form: if the Full conjecture held over
`R`, it would hold over `ℤ`.  The four extra hypotheses (simple, loopless, acyclic,
`x ≤ u`) transfer verbatim -- the first three do not mention the ring at all, and `x ≤ u`
pushes forward along the order embedding `ℤ ↪ R`. -/
theorem GoemansCostConjectureFull_int_of (h : GoemansCostConjectureFull R) :
    GoemansCostConjectureFull ℤ := by
  intro W E K _ _ _ _ _ tail head src term d dmax x c u hsimple hloop hacyc hxu
    hinj hns hpos hle hex hc hx hcons hsrc
  obtain ⟨P, hw, hcap, hcost⟩ :=
    h W E K tail head src term (fun k => ((d k : R))) ((dmax : R))
      (fun a => ((x a : R))) (fun a => ((c a : R))) (fun a => ((u a : R)))
      hsimple hloop hacyc (fun a => by exact_mod_cast hxu a)
      hinj hns
      (fun k => by exact_mod_cast hpos k)
      (fun k => by exact_mod_cast hle k)
      (by obtain ⟨k, hk⟩ := hex; exact ⟨k, by exact_mod_cast hk⟩)
      (fun a => by exact_mod_cast hc a)
      (fun a => by exact_mod_cast hx a)
      (fun z hz => by
        rw [cast_sum_ite, cast_sum_ite, cast_sum_ite]
        exact_mod_cast congrArg (fun t : ℤ => ((t : R))) (hcons z hz))
      (by
        rw [cast_sum_ite, cast_sum_ite, ← Int.cast_sum]
        exact_mod_cast congrArg (fun t : ℤ => ((t : R))) hsrc)
  refine ⟨P, hw, fun a => ?_, ?_⟩
  · have := hcap a
    rw [unsplittableLoad_cast] at this
    exact_mod_cast this
  · have := hcost
    simp only [unsplittableLoad_cast] at this
    exact_mod_cast this

end Transfer

/-- **Layer B (main), literature-faithful form, over `ℤ`.**  The counterexample instance
discharges every hypothesis of `GoemansCostConjectureFull`: it is simple (`arcs_simple`),
loopless (`no_self_loops`), acyclic (`⟨rank, rank_arc⟩`), and takes `u := x` (the worst
case the primary source identifies), so `x ≤ u` holds by reflexivity. -/
theorem not_GoemansCostConjectureFull_int : ¬ GoemansCostConjectureFull ℤ := by
  intro h
  obtain ⟨P, hw, hcap, hcost⟩ :=
    h Vertex Arc (Fin 3) tail head Vertex.s terminal demand maximumDemand
      fractionalFlow arcCost fractionalFlow
      arcs_simple no_self_loops ⟨rank, rank_arc⟩ (fun a => le_refl _)
      terminal_injective terminal_ne_source demand_pos maximumDemand_is_max.1 maximumDemand_is_max.2
      arcCost_nonneg fractionalFlow_nonneg flow_feasible conservation_source
  have hlow : (60 : ℤ) ≤ ∑ a : Arc, arcCost a * unsplittableLoad demand P a :=
    min_cost_capacity_good P hw hcap
  rw [fractional_cost] at hcost
  omega

/-- **Layer B (main), literature-faithful form, general coefficient ring.**  Goemans' cost
conjecture -- capacities restored, digraph simple, loopless and acyclic -- is false over
every linearly ordered commutative ring. -/
theorem not_GoemansCostConjectureFull (R : Type) [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] : ¬ GoemansCostConjectureFull R :=
  fun h => not_GoemansCostConjectureFull_int (GoemansCostConjectureFull_int_of h)

/-- The literature-faithful form over `ℚ`, the setting of Conjecture 1.3. -/
theorem not_GoemansCostConjectureFull_rat : ¬ GoemansCostConjectureFull ℚ :=
  not_GoemansCostConjectureFull ℚ

/-- **THE HEADLINE.**  Goemans' cost conjecture for single-source unsplittable flow
(Conjecture 1.3 of arXiv:2308.02651, the cost version of the Dinitz–Garg–Goemans theorem)
is **false** over `ℚ`, in the form that keeps every piece of the literature's data: arc
capacities `u` with `x ≤ u`, and a simple, loopless, acyclic digraph.

`dgg_cost_conjecture_false` below is the same refutation for the bare form
`GoemansCostConjecture` and is kept as the searchable alias. -/
theorem goemans_cost_conjecture_false : ¬ GoemansCostConjectureFull ℚ :=
  not_GoemansCostConjectureFull ℚ

/-- The headline over the reals. -/
theorem goemans_cost_conjecture_false_real : ¬ GoemansCostConjectureFull ℝ :=
  not_GoemansCostConjectureFull ℝ

/-- **Layer B, bare form.**  Goemans' cost conjecture is false over `ℤ`. -/
theorem not_GoemansCostConjecture_int : ¬ GoemansCostConjecture ℤ :=
  fun h => not_GoemansCostConjectureFull_int
    (GoemansCostConjectureFull_of_GoemansCostConjecture ℤ h)

/-- **Layer B, bare form, general coefficient ring.**  Goemans' cost conjecture is false
over every linearly ordered commutative ring — in particular over `ℚ`, the setting of
Conjecture 1.3 of arXiv:2308.02651, and over `ℝ`. -/
theorem not_GoemansCostConjecture (R : Type) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] :
    ¬ GoemansCostConjecture R :=
  fun h => not_GoemansCostConjecture_int (GoemansCostConjecture_int_of h)

/-- The bare form over `ℚ`; the searchable alias of the headline
`goemans_cost_conjecture_false`.  (It also follows from the headline without re-running the
instance, via `GoemansCostConjectureFull_of_GoemansCostConjecture` — see
`dgg_cost_conjecture_false_of_headline` — since the Full form is the weaker Prop.) -/
theorem dgg_cost_conjecture_false : ¬ GoemansCostConjecture ℚ := not_GoemansCostConjecture ℚ

/-- The same over the reals. -/
theorem dgg_cost_conjecture_false_real : ¬ GoemansCostConjecture ℝ := not_GoemansCostConjecture ℝ

/-- The headline implies the bare-form refutation, with no second appeal to the instance:
the Full form is the weaker Prop, so refuting it refutes the bare one. -/
theorem dgg_cost_conjecture_false_of_headline : ¬ GoemansCostConjecture ℚ :=
  fun h => goemans_cost_conjecture_false (GoemansCostConjectureFull_of_GoemansCostConjecture ℚ h)

end GoemansFlow

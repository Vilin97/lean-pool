/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/

import Mathlib.Tactic.Linarith
import LeanPool.PebblingLean.Basic

/-!
# Direct delivery along paths

This file formalizes the elementary deterministic fact used inside the upper
bound: a pile of size `T * 2^d` at one end of a length-`d` path can deliver `T`
pebbles to the other end.
-/

namespace PebblingLean

universe u

namespace Graph

variable {V : Type u} (G : Graph V)

/-- Walks in the custom graph structure used by this project. -/
inductive Walk : V → V → Type u where
  | nil (v : V) : Walk v v
  | cons {u v w : V} : G.Adj u v → Walk v w → Walk u w

namespace Walk

/-- Length of a walk. -/
def length {u v : V} : G.Walk u v → ℕ
  | nil _ => 0
  | cons _ tail => tail.length + 1

/-- Concatenate two walks. -/
def append {u v w : V} : G.Walk u v → G.Walk v w → G.Walk u w
  | nil _, tail => tail
  | cons h headTail, tail => cons h (append headTail tail)

@[simp]
theorem length_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (Graph.Walk.append G p q).length = p.length + q.length := by
  induction p generalizing w with
  | nil _ =>
      simp [append, length]
  | cons _ tail ih =>
      simp [append, length, ih, Nat.add_assoc, Nat.add_comm]

/-- Reverse a walk in an undirected graph. -/
def reverse {u v : V} : G.Walk u v → G.Walk v u
  | nil u => nil u
  | cons h tail => Graph.Walk.append G (reverse tail) (cons (G.symm h) (nil _))

@[simp]
theorem length_reverse {u v : V} (p : G.Walk u v) :
    p.reverse.length = p.length := by
  induction p with
  | nil _ =>
      rfl
  | cons _ tail ih =>
      simp [reverse, length, ih]

end Walk

end Graph

namespace Pebbling

variable {V : Type u}

/-- A distribution with `k` pebbles at one vertex and none elsewhere. -/
def single [DecidableEq V] (v : V) (k : ℕ) : Pebbling V :=
  fun x => if x = v then k else 0

@[simp]
theorem single_apply_self [DecidableEq V] (v : V) (k : ℕ) :
    single v k v = k := by
  simp [single]

@[simp]
theorem single_apply_ne [DecidableEq V] {u v : V} (k : ℕ) (h : u ≠ v) :
    single v k u = 0 := by
  simp [single, h]

@[simp]
theorem size_single [Fintype V] [DecidableEq V] (v : V) (k : ℕ) :
    size (single v k) = k := by
  classical
  simp [size, single]

/-- A distribution supported on two distinct vertices.  If the vertices are not
distinct, the first branch takes precedence; the lemmas below use adjacent
vertices, so they are distinct. -/
def twoPoint [DecidableEq V] (u v : V) (ku kv : ℕ) : Pebbling V :=
  fun x => if x = u then ku else if x = v then kv else 0

@[simp]
theorem twoPoint_apply_left [DecidableEq V] (u v : V) (ku kv : ℕ) :
    twoPoint u v ku kv u = ku := by
  simp [twoPoint]

@[simp]
theorem twoPoint_apply_right [DecidableEq V] {u v : V} (ku kv : ℕ) (hvu : v ≠ u) :
    twoPoint u v ku kv v = kv := by
  simp [twoPoint, hvu]

@[simp]
theorem twoPoint_apply_ne [DecidableEq V] {u v x : V} (ku kv : ℕ)
    (hxu : x ≠ u) (hxv : x ≠ v) :
    twoPoint u v ku kv x = 0 := by
  simp [twoPoint, hxu, hxv]

theorem single_eq_twoPoint_right_zero [DecidableEq V] {u v : V} (k : ℕ) (huv : u ≠ v) :
    single u k = twoPoint u v k 0 := by
  funext x
  by_cases hxu : x = u
  · subst x
    simp [single, twoPoint]
  · by_cases hxv : x = v
    · subst x
      have hvu : v ≠ u := fun h => huv h.symm
      simp [single, twoPoint, hvu]
    · simp [single, twoPoint, hxu, hxv]

theorem single_eq_twoPoint_left_zero [DecidableEq V] {u v : V} (k : ℕ) (huv : u ≠ v) :
    single v k = twoPoint u v 0 k := by
  funext x
  by_cases hxu : x = u
  · subst x
    simp [single, twoPoint, huv]
  · by_cases hxv : x = v
    · subst x
      have hvu : v ≠ u := fun h => huv h.symm
      simp [single, twoPoint, hvu]
    · simp [single, twoPoint, hxu, hxv]

/-- One edge move transfers one pebble from the left support vertex to the
right support vertex, consuming two pebbles on the left. -/
theorem twoPoint_edge_move [DecidableEq V] {G : Graph V} {u v : V}
    (huv_adj : G.Adj u v) (k a : ℕ) :
    Move G (twoPoint u v (2 * (k + 1)) a) (twoPoint u v (2 * k) (a + 1)) := by
  have huv : u ≠ v := by
    intro h
    subst v
    exact (G.loopless u) huv_adj
  refine ⟨u, v, huv_adj, ?_, ?_⟩
  · simp [twoPoint]
  · funext x
    by_cases hxu : x = u
    · subst x
      simp [moveDistribution, twoPoint]
      omega
    · by_cases hxv : x = v
      · subst x
        have hvu : v ≠ u := fun h => huv h.symm
        simp [moveDistribution, twoPoint, hvu]
      · simp [moveDistribution, twoPoint, hxu, hxv]

/-- Repeating the same edge move sends `k` pebbles across an edge from a pile
of size `2*k`, preserving any accumulator already present at the destination. -/
theorem reaches_twoPoint_edge [DecidableEq V] {G : Graph V} {u v : V}
    (huv_adj : G.Adj u v) (k a : ℕ) :
    Reaches G (twoPoint u v (2 * k) a) (twoPoint u v 0 (a + k)) := by
  induction k generalizing a with
  | zero =>
      exact Relation.ReflTransGen.refl
  | succ k ih =>
      have hmove := twoPoint_edge_move (G := G) huv_adj k a
      have htail : Reaches G (twoPoint u v (2 * k) (a + 1))
          (twoPoint u v 0 (a + (k + 1))) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (a + 1)
      exact Relation.ReflTransGen.head hmove htail

/-- A pile of `2*k` pebbles at one endpoint of an edge can deliver `k` pebbles
to the other endpoint. -/
theorem reaches_single_edge [DecidableEq V] {G : Graph V} {u v : V}
    (huv_adj : G.Adj u v) (k : ℕ) :
    Reaches G (single u (2 * k)) (single v k) := by
  have huv : u ≠ v := by
    intro h
    subst v
    exact (G.loopless u) huv_adj
  have hreach := reaches_twoPoint_edge (G := G) huv_adj k 0
  have hstart : single u (2 * k) = twoPoint u v (2 * k) 0 :=
    single_eq_twoPoint_right_zero (v := v) (2 * k) huv
  have hfinish : single v k = twoPoint u v 0 k :=
    single_eq_twoPoint_left_zero (u := u) k huv
  rw [hstart, hfinish]
  simpa [Nat.zero_add] using hreach

/-- Direct delivery along a walk. -/
theorem canReachAtLeast_single_of_walk [DecidableEq V] {G : Graph V} {u target : V}
    (walk : G.Walk u target) (T : ℕ) :
    CanReachAtLeast G (single u (T * 2 ^ walk.length)) target T := by
  induction walk with
  | nil v =>
      refine ⟨single v T, ?_, ?_⟩
      · simpa [Graph.Walk.length, Reaches] using
          (Relation.ReflTransGen.refl : Reaches G (single v T) (single v T))
      · simp
  | cons huv tail ih =>
      dsimp [Graph.Walk.length]
      let k := T * 2 ^ tail.length
      have hfirst : Reaches G (single _ (2 * k)) (single _ k) :=
        reaches_single_edge (G := G) huv k
      have hpow : T * 2 ^ (tail.length + 1) = 2 * k := by
        dsimp [k]
        rw [Nat.pow_succ]
        ac_rfl
      rcases ih with ⟨Dfinish, htail, htarget⟩
      exact ⟨Dfinish, by
        simpa [hpow, Reaches] using Relation.ReflTransGen.trans hfirst htail, htarget⟩

/-- Direct delivery is monotone in the initial distribution: extra pebbles
away from the chosen starting pile cannot hurt. -/
theorem canReachAtLeast_of_walk_of_single_dominated [DecidableEq V] {G : Graph V}
    {D : Pebbling V} {u target : V} (walk : G.Walk u target) {T : ℕ}
    (hdom : Dominates D (single u (T * 2 ^ walk.length))) :
    CanReachAtLeast G D target T :=
  canReachAtLeast_of_dominates (canReachAtLeast_single_of_walk walk T) hdom

/-- Moving from `D` to `E` can be done with an untouched extra distribution
added everywhere. -/
theorem move_add_right [DecidableEq V] {G : Graph V} {D E A : Pebbling V}
    (hmove : Move G D E) :
    Move G (D + A) (E + A) := by
  rcases hmove with ⟨u, v, huv_adj, hD, rfl⟩
  have huv : u ≠ v := by
    intro h
    subst v
    exact (G.loopless u) huv_adj
  have hdist :
      moveDistribution (D + A) u v = moveDistribution D u v + A := by
    funext x
    by_cases hxu : x = u
    · subst x
      simp only [moveDistribution_apply_from, Pi.add_apply]
      calc
        D u + A u - 2 = A u + D u - 2 := by rw [Nat.add_comm]
        _ = A u + (D u - 2) := Nat.add_sub_assoc hD (A u)
        _ = D u - 2 + A u := by rw [Nat.add_comm]
    · by_cases hxv : x = v
      · subst x
        have hvu : v ≠ u := fun h => huv h.symm
        simp [moveDistribution, hvu]
        omega
      · simp [moveDistribution, hxu, hxv]
  refine ⟨u, v, huv_adj, ?_, hdist.symm⟩
  exact hD.trans (Nat.le_add_right (D u) (A u))

/-- A whole pebbling sequence can be replayed with an untouched extra
distribution added everywhere. -/
theorem reaches_add_right [DecidableEq V] {G : Graph V} {D E A : Pebbling V}
    (hreach : Reaches G D E) :
    Reaches G (D + A) (E + A) := by
  unfold Reaches at hreach ⊢
  refine hreach.head_induction_on ?refl ?head
  · exact Relation.ReflTransGen.refl
  · intro B C hmove _ ih
    exact Relation.ReflTransGen.head (move_add_right hmove) ih

/-- If two distributions can independently deliver `T₁` and `T₂` pebbles to
the same target, their sum can deliver `T₁ + T₂`. -/
theorem canReachAtLeast_add [DecidableEq V] {G : Graph V} {D₁ D₂ : Pebbling V}
    {target : V} {T₁ T₂ : ℕ}
    (h₁ : CanReachAtLeast G D₁ target T₁)
    (h₂ : CanReachAtLeast G D₂ target T₂) :
    CanReachAtLeast G (D₁ + D₂) target (T₁ + T₂) := by
  rcases h₁ with ⟨E₁, hreach₁, htarget₁⟩
  rcases h₂ with ⟨E₂, hreach₂, htarget₂⟩
  have hfirst : Reaches G (D₁ + D₂) (E₁ + D₂) :=
    reaches_add_right hreach₁
  have hsecond₀ : Reaches G (D₂ + E₁) (E₂ + E₁) :=
    reaches_add_right hreach₂
  have hstart : D₂ + E₁ = E₁ + D₂ := by
    funext v
    exact Nat.add_comm (D₂ v) (E₁ v)
  have hfinish : E₂ + E₁ = E₁ + E₂ := by
    funext v
    exact Nat.add_comm (E₂ v) (E₁ v)
  have hsecond : Reaches G (E₁ + D₂) (E₁ + E₂) := by
    simpa [hstart, hfinish] using hsecond₀
  refine ⟨E₁ + E₂, Relation.ReflTransGen.trans hfirst hsecond, ?_⟩
  exact add_le_add htarget₁ htarget₂

end Pebbling

end PebblingLean

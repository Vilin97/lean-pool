/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Basic definitions for graph pebbling

This file sets up the objects that should remain stable throughout the
formalization: simple undirected graphs, pebbling distributions, legal pebbling
moves, reachability, solvability, and optimality.
-/

namespace PebblingLean

universe u

/-- A simple undirected graph, kept intentionally small for the pebbling
formalization. -/
structure Graph (V : Type u) where
  /-- The adjacency relation between vertices. -/
  Adj : V → V → Prop
  /-- Adjacency is symmetric. -/
  symm : ∀ {u v : V}, Adj u v → Adj v u
  /-- The graph has no self-loops. -/
  loopless : ∀ v : V, ¬ Adj v v

namespace Graph

variable {V : Type u} (G : Graph V)

theorem adj_comm {u v : V} : G.Adj u v ↔ G.Adj v u :=
  ⟨G.symm, G.symm⟩

end Graph

/-- A pebbling distribution assigns a nonnegative number of pebbles to each
vertex. -/
abbrev Pebbling (V : Type u) := V → ℕ

namespace Pebbling

variable {V : Type u}

/-- The total number of pebbles in a finite distribution. -/
def size [Fintype V] (D : Pebbling V) : ℕ :=
  ∑ v, D v

/-- Pointwise domination of pebbling distributions. -/
def Dominates (D E : Pebbling V) : Prop :=
  ∀ v : V, E v ≤ D v

@[simp]
theorem size_zero [Fintype V] : size (fun _ : V => 0) = 0 := by
  simp [size]

/-- A single vertex count is bounded by the total size of a finite
distribution. -/
theorem le_size [Fintype V] (D : Pebbling V) (v : V) :
    D v ≤ size D := by
  classical
  rw [size]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)

/-- The distribution obtained by moving two pebbles from `u` to one pebble at
`v`. Legality of this operation is recorded separately in `Move`. -/
def moveDistribution [DecidableEq V] (D : Pebbling V) (u v : V) : Pebbling V :=
  fun x =>
    if x = u then D x - 2
    else if x = v then D x + 1
    else D x

@[simp]
theorem moveDistribution_apply_from [DecidableEq V] (D : Pebbling V) {u v : V} :
    moveDistribution D u v u = D u - 2 := by
  simp [moveDistribution]

@[simp]
theorem moveDistribution_apply_to [DecidableEq V] (D : Pebbling V) {u v : V} (h : v ≠ u) :
    moveDistribution D u v v = D v + 1 := by
  simp [moveDistribution, h]

@[simp]
theorem moveDistribution_apply_of_ne [DecidableEq V] (D : Pebbling V) {u v x : V}
    (hxu : x ≠ u) (hxv : x ≠ v) :
    moveDistribution D u v x = D x := by
  simp [moveDistribution, hxu, hxv]

/-- Performing the same move from a larger distribution gives a larger result. -/
theorem moveDistribution_mono [DecidableEq V] {D D' : Pebbling V} {u v : V}
    (huv : u ≠ v) (hdom : Dominates D' D) :
    Dominates (moveDistribution D' u v) (moveDistribution D u v) := by
  intro x
  by_cases hxu : x = u
  · subst x
    simpa [moveDistribution] using Nat.sub_le_sub_right (hdom u) 2
  · by_cases hxv : x = v
    · subst x
      have hvu : v ≠ u := fun h => huv h.symm
      simpa [moveDistribution, hvu] using hdom v
    · simpa [moveDistribution, hxu, hxv] using hdom x

/-- One legal pebbling move: remove two pebbles from `u` and add one pebble to
an adjacent vertex `v`. -/
def Move [DecidableEq V] (G : Graph V) (D E : Pebbling V) : Prop :=
  ∃ u v : V,
    G.Adj u v ∧
      2 ≤ D u ∧
        E = moveDistribution D u v

/-- `E` is reachable from `D` by zero or more pebbling moves. -/
def Reaches [DecidableEq V] (G : Graph V) (D E : Pebbling V) : Prop :=
  Relation.ReflTransGen (Move G) D E

/-- Reach a target with at least `T` pebbles. -/
def CanReachAtLeast [DecidableEq V] (G : Graph V) (D : Pebbling V) (target : V) (T : ℕ) :
    Prop :=
  ∃ E : Pebbling V, Reaches G D E ∧ T ≤ E target

/-- A distribution can reach a target if some reachable distribution has at
least one pebble on that target. -/
def CanReach [DecidableEq V] (G : Graph V) (D : Pebbling V) (target : V) : Prop :=
  CanReachAtLeast G D target 1

/-- A distribution is `T`-solvable if it can move at least `T` pebbles to every
target. -/
def SolvableAtLeast [DecidableEq V] (G : Graph V) (D : Pebbling V) (T : ℕ) : Prop :=
  ∀ target : V, CanReachAtLeast G D target T

/-- A distribution is solvable if it can reach every target vertex. -/
def Solvable [DecidableEq V] (G : Graph V) (D : Pebbling V) : Prop :=
  SolvableAtLeast G D 1

/-- Reaching demand zero is automatic. -/
theorem canReachAtLeast_zero [DecidableEq V] (G : Graph V) (D : Pebbling V) (target : V) :
    CanReachAtLeast G D target 0 :=
  ⟨D, Relation.ReflTransGen.refl, Nat.zero_le _⟩

/-- Every distribution is zero-demand solvable. -/
theorem solvableAtLeast_zero [DecidableEq V] (G : Graph V) (D : Pebbling V) :
    SolvableAtLeast G D 0 := by
  intro target
  exact canReachAtLeast_zero G D target

/-- There is a solvable distribution of total size `k`. -/
def HasSolvableSize [Fintype V] [DecidableEq V] (G : Graph V) (k : ℕ) : Prop :=
  ∃ D : Pebbling V, size D = k ∧ Solvable G D

/-- There is a `T`-solvable distribution of total size `k`. -/
def HasSolvableAtLeastSize [Fintype V] [DecidableEq V] (G : Graph V) (T k : ℕ) : Prop :=
  ∃ D : Pebbling V, size D = k ∧ SolvableAtLeast G D T

/-- There is a `T`-solvable distribution of total size at most `k`.  This is
the natural form for upper-bound constructions. -/
def HasSolvableAtMostSize [Fintype V] [DecidableEq V] (G : Graph V) (T k : ℕ) : Prop :=
  ∃ D : Pebbling V, size D ≤ k ∧ SolvableAtLeast G D T

/-- Every occupied pile in `D` has size at least `S`. -/
def MinOccupiedPileSize (D : Pebbling V) (S : ℕ) : Prop :=
  ∀ v : V, D v ≠ 0 → S ≤ D v

/-- Number of occupied vertices in a finite pebbling distribution. -/
def supportSize [Fintype V] (D : Pebbling V) : ℕ :=
  (Finset.univ.filter fun v => D v ≠ 0).card

/-- A relational form of the optimal pebbling number: `k` is optimal if there is
a solvable distribution with `k` pebbles, and none with fewer. This avoids
choosing a numerical value before proving existence for the graph family under
study. -/
def IsOptimalNumber [Fintype V] [DecidableEq V] (G : Graph V) (k : ℕ) : Prop :=
  HasSolvableSize G k ∧ ∀ l : ℕ, l < k → ¬ HasSolvableSize G l

/-- A relational form of the optimal `T`-pebbling number. -/
def IsOptimalDemandNumber [Fintype V] [DecidableEq V] (G : Graph V) (T k : ℕ) : Prop :=
  HasSolvableAtLeastSize G T k ∧ ∀ l : ℕ, l < k → ¬ HasSolvableAtLeastSize G T l

/-- A single move can be replayed from a dominating distribution. -/
theorem move_of_dominates [DecidableEq V] {G : Graph V} {D E D' : Pebbling V}
    (hmove : Move G D E) (hdom : Dominates D' D) :
    ∃ E' : Pebbling V, Move G D' E' ∧ Dominates E' E := by
  rcases hmove with ⟨u, v, huv_adj, hD, rfl⟩
  have huv : u ≠ v := by
    intro huv_eq
    subst v
    exact (G.loopless u) huv_adj
  refine ⟨moveDistribution D' u v, ?_, moveDistribution_mono huv hdom⟩
  exact ⟨u, v, huv_adj, (hD.trans (hdom u)), rfl⟩

/-- Any sequence of moves can be replayed from a dominating distribution. -/
theorem reaches_of_dominates [DecidableEq V] {G : Graph V} {D E D' : Pebbling V}
    (hreach : Reaches G D E) (hdom : Dominates D' D) :
    ∃ E' : Pebbling V, Reaches G D' E' ∧ Dominates E' E := by
  unfold Reaches at hreach
  refine hreach.head_induction_on
    (motive := fun A _ => ∀ D0 : Pebbling V, Dominates D0 A →
      ∃ E' : Pebbling V, Reaches G D0 E' ∧ Dominates E' E) ?refl ?head D' hdom
  · intro D0 hdom_E
    exact ⟨D0, Relation.ReflTransGen.refl, hdom_E⟩
  · intro A B hmove hreach_B _ih D0 hdom_A
    rcases move_of_dominates hmove hdom_A with ⟨B', hmove', hdom_B⟩
    rcases _ih B' hdom_B with ⟨E', hreach', hdom_E⟩
    exact ⟨E', Relation.ReflTransGen.head hmove' hreach', hdom_E⟩

/-- Extra pebbles cannot hurt target reachability. -/
theorem canReachAtLeast_of_dominates [DecidableEq V] {G : Graph V} {D D' : Pebbling V}
    {target : V} {T : ℕ} (hcan : CanReachAtLeast G D target T) (hdom : Dominates D' D) :
    CanReachAtLeast G D' target T := by
  rcases hcan with ⟨E, hreach, htarget⟩
  rcases reaches_of_dominates hreach hdom with ⟨E', hreach', hdom_E⟩
  exact ⟨E', hreach', htarget.trans (hdom_E target)⟩

/-- If a distribution can reach a larger demand, it can reach any smaller
demand. -/
theorem canReachAtLeast_mono [DecidableEq V] {G : Graph V} {D : Pebbling V}
    {target : V} {T T' : ℕ} (hTT' : T' ≤ T)
    (hcan : CanReachAtLeast G D target T) :
    CanReachAtLeast G D target T' := by
  rcases hcan with ⟨E, hreach, htarget⟩
  exact ⟨E, hreach, hTT'.trans htarget⟩

/-- Extra pebbles cannot hurt `T`-solvability. -/
theorem solvableAtLeast_of_dominates [DecidableEq V] {G : Graph V} {D D' : Pebbling V}
    {T : ℕ} (hsolv : SolvableAtLeast G D T) (hdom : Dominates D' D) :
    SolvableAtLeast G D' T := by
  intro target
  exact canReachAtLeast_of_dominates (hsolv target) hdom

/-- `T`-solvability implies any smaller demand. -/
theorem solvableAtLeast_mono [DecidableEq V] {G : Graph V} {D : Pebbling V}
    {T T' : ℕ} (hTT' : T' ≤ T) (hsolv : SolvableAtLeast G D T) :
    SolvableAtLeast G D T' := by
  intro target
  exact canReachAtLeast_mono hTT' (hsolv target)

/-- A distribution that is `T`-solvable for `T ≥ 1` is solvable in the usual
one-pebble sense. -/
theorem solvable_of_solvableAtLeast [DecidableEq V] {G : Graph V} {D : Pebbling V}
    {T : ℕ} (hT : 1 ≤ T) (hsolv : SolvableAtLeast G D T) :
    Solvable G D :=
  solvableAtLeast_mono hT hsolv

/-- A bounded-size construction for a larger demand also works for any smaller
demand. -/
theorem hasSolvableAtMostSize_mono_demand [Fintype V] [DecidableEq V]
    {G : Graph V} {T T' k : ℕ} (hTT' : T' ≤ T)
    (h : HasSolvableAtMostSize G T k) :
    HasSolvableAtMostSize G T' k := by
  rcases h with ⟨D, hsize, hsolv⟩
  exact ⟨D, hsize, solvableAtLeast_mono hTT' hsolv⟩

/-- A construction with size at most `k` is also a construction with any larger
size bound. -/
theorem hasSolvableAtMostSize_mono_size [Fintype V] [DecidableEq V]
    {G : Graph V} {T k k' : ℕ} (hkk' : k ≤ k')
    (h : HasSolvableAtMostSize G T k) :
    HasSolvableAtMostSize G T k' := by
  rcases h with ⟨D, hsize, hsolv⟩
  exact ⟨D, hsize.trans hkk', hsolv⟩

/-- The size of a sum of two finite distributions is the sum of their sizes. -/
theorem size_add [Fintype V] (D E : Pebbling V) :
    size (D + E) = size D + size E := by
  classical
  simp [size, Finset.sum_add_distrib]

theorem sum_ite_nonzero_const [Fintype V] (D : Pebbling V) (K : ℕ) :
    (∑ v : V, if D v = 0 then 0 else K) = supportSize D * K := by
  classical
  calc
    (∑ v : V, if D v = 0 then 0 else K)
        = ∑ v : V, if D v ≠ 0 then K else 0 := by
          refine Finset.sum_congr rfl ?_
          intro v _hv
          by_cases hv0 : D v = 0
          · simp [hv0]
          · simp [hv0]
    _ = ∑ v ∈ (Finset.univ.filter fun v : V => D v ≠ 0), K := by
          rw [Finset.sum_filter]
    _ = supportSize D * K := by
          simp [supportSize, Finset.sum_const]

/-- If each occupied pile has at least `S` pebbles, then the number of occupied
vertices times `S` is at most the total size. -/
theorem supportSize_mul_le_size_of_minOccupiedPileSize [Fintype V]
    {D : Pebbling V} {S : ℕ} (hmin : MinOccupiedPileSize D S) :
    supportSize D * S ≤ size D := by
  classical
  have hsum :
      (∑ v : V, if D v = 0 then 0 else S) ≤ ∑ v : V, D v := by
    refine Finset.sum_le_sum ?_
    intro v _hv
    by_cases hv0 : D v = 0
    · simp [hv0]
    · simpa [hv0] using hmin v hv0
  simpa [sum_ite_nonzero_const, size] using hsum

/-- Multiplicative form of the occupied-pile count bound, used in product
recurrences. -/
theorem supportSize_mul_minPileCost_le_size_mul [Fintype V]
    {D : Pebbling V} {S K : ℕ} (hmin : MinOccupiedPileSize D S) :
    supportSize D * (S * K) ≤ size D * K := by
  rw [← Nat.mul_assoc]
  exact Nat.mul_le_mul_right K
    (supportSize_mul_le_size_of_minOccupiedPileSize hmin)

end Pebbling

end PebblingLean

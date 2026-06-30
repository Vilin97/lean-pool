/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/

import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import LeanPool.PebblingLean.Basic

/-!
# Weight functions

The lower-bound argument is organized around the standard pebbling weight
function: a pebble at distance `d` from a target contributes `2^{-d}`.
-/

namespace PebblingLean

universe u

namespace Pebbling

variable {V : Type u}

/-- Contribution of a single pebble at `u` to the weight with target `target`. -/
noncomputable def unitWeight (dist : V → V → ℕ) (target u : V) : ℚ :=
  (1 : ℚ) / (2 : ℚ) ^ dist u target

/-- Weight of a pebbling distribution with respect to a target, using a supplied
distance function. -/
noncomputable def weight [Fintype V] (dist : V → V → ℕ) (D : Pebbling V) (target : V) : ℚ :=
  ∑ u, (D u : ℚ) * unitWeight dist target u

@[simp]
theorem weight_zero [Fintype V] (dist : V → V → ℕ) (target : V) :
    weight dist (fun _ : V => 0) target = 0 := by
  simp [weight]

/-- Algebraic effect of one legal move on a weighted sum. -/
theorem sum_moveDistribution_mul [Fintype V] [DecidableEq V] (D : Pebbling V)
    (w : V → ℚ) {u v : V} (huv : u ≠ v) (hD : 2 ≤ D u) :
    (∑ x, ((moveDistribution D u v x : ℕ) : ℚ) * w x)
      = (∑ x, (D x : ℚ) * w x) - 2 * w u + w v := by
  classical
  have hcast : ((D u - 2 : ℕ) : ℚ) = (D u : ℚ) - 2 := by
    rw [Nat.cast_sub hD]
    norm_num
  have hpoint :
      ∀ x : V,
        ((moveDistribution D u v x : ℕ) : ℚ) * w x =
          (D x : ℚ) * w x +
            (if u = x then -2 * w u else if v = x then w v else 0) := by
    intro x
    by_cases hux : u = x
    · subst x
      simp [moveDistribution, hcast]
      ring
    · by_cases hvx : v = x
      · subst x
        have hvu : v ≠ u := fun h => hux h.symm
        simp [moveDistribution, hvu]
        simp [hux]
        ring_nf
      · have hxu : x ≠ u := fun h => hux h.symm
        have hxv : x ≠ v := fun h => hvx h.symm
        simp [moveDistribution, hxu, hxv]
        simp [hux, hvx]
  calc
    (∑ x, ((moveDistribution D u v x : ℕ) : ℚ) * w x)
        = ∑ x, ((D x : ℚ) * w x +
            (if u = x then -2 * w u else if v = x then w v else 0)) := by
          exact Finset.sum_congr rfl (fun x _ => hpoint x)
    _ = (∑ x, (D x : ℚ) * w x) +
          (∑ x, (if u = x then -2 * w u else if v = x then w v else 0)) := by
          exact Finset.sum_add_distrib
    _ = (∑ x, (D x : ℚ) * w x) - 2 * w u + w v := by
          have hdelta :
              (∑ x : V, if u = x then -2 * w u else if v = x then w v else 0)
                = -2 * w u + w v := by
            calc
              (∑ x : V, if u = x then -2 * w u else if v = x then w v else 0)
                  = ∑ x : V, ((if u = x then -2 * w u else 0) +
                      (if v = x then w v else 0)) := by
                    apply Finset.sum_congr rfl
                    intro x _
                    by_cases hux : u = x
                    · have hvx_false : ¬ v = x := fun hvx => huv (hux.trans hvx.symm)
                      simp [hux, hvx_false]
                    · by_cases hvx : v = x
                      · simp [hux, hvx]
                      · simp [hux, hvx]
              _ = (∑ x : V, if u = x then -2 * w u else 0) +
                    (∑ x : V, if v = x then w v else 0) := by
                    exact Finset.sum_add_distrib
              _ = -2 * w u + w v := by
                    have hu_sum :
                        (∑ x : V, if u = x then -2 * w u else 0) = -2 * w u := by
                      simp
                    have hv_sum :
                        (∑ x : V, if v = x then w v else 0) = w v := by
                      simp
                    rw [hu_sum, hv_sum]
          rw [hdelta]
          ring_nf

/-- Exact change in target weight under one legal move. -/
theorem weight_moveDistribution [Fintype V] [DecidableEq V] (dist : V → V → ℕ)
    (D : Pebbling V) {u v target : V} (huv : u ≠ v) (hD : 2 ≤ D u) :
    weight dist (moveDistribution D u v) target
      = weight dist D target - 2 * unitWeight dist target u + unitWeight dist target v := by
  simpa [weight] using
    sum_moveDistribution_mul (D := D) (w := unitWeight dist target) (u := u) (v := v) huv hD

/-- If moving from `u` to `v` moves at most one step closer to the target, then
the new pebble at `v` contributes no more weight than the two pebbles removed
from `u`. -/
theorem unitWeight_le_two_mul_of_dist_le_succ (dist : V → V → ℕ) {u v target : V}
    (h : dist u target ≤ dist v target + 1) :
    unitWeight dist target v ≤ 2 * unitWeight dist target u := by
  unfold unitWeight
  have hbase_one : (1 : ℚ) ≤ 2 := by norm_num
  have hpow : (2 : ℚ) ^ dist u target ≤ (2 : ℚ) ^ (dist v target + 1) := by
    exact pow_le_pow_right₀ hbase_one h
  rw [pow_succ] at hpow
  have hpu : 0 < (2 : ℚ) ^ dist u target := by positivity
  have hpv : 0 < (2 : ℚ) ^ dist v target := by positivity
  field_simp [hpu.ne', hpv.ne']
  linarith

/-- A single legal move cannot increase target weight, provided the supplied
distance function changes by at most one along graph edges. -/
theorem weight_moveDistribution_le [Fintype V] [DecidableEq V] (dist : V → V → ℕ)
    (D : Pebbling V) {u v target : V} (huv : u ≠ v) (hD : 2 ≤ D u)
    (hdist : dist u target ≤ dist v target + 1) :
    weight dist (moveDistribution D u v) target ≤ weight dist D target := by
  have hw := unitWeight_le_two_mul_of_dist_le_succ (dist := dist)
    (u := u) (v := v) (target := target) hdist
  rw [weight_moveDistribution (dist := dist) (D := D) (u := u) (v := v)
    (target := target) huv hD]
  linarith

/-- Relational version of `weight_moveDistribution_le` for `Move`. -/
theorem weight_move_le_of_dist [Fintype V] [DecidableEq V] (G : Graph V)
    (dist : V → V → ℕ) {D E : Pebbling V} {target : V}
    (hmove : Move G D E)
    (hdist : ∀ {u v : V}, G.Adj u v → dist u target ≤ dist v target + 1) :
    weight dist E target ≤ weight dist D target := by
  rcases hmove with ⟨u, v, huv_adj, hD, rfl⟩
  have huv : u ≠ v := by
    intro huv_eq
    subst v
    exact (G.loopless u) huv_adj
  exact weight_moveDistribution_le (dist := dist) (D := D) (u := u) (v := v)
    (target := target) huv hD (hdist huv_adj)

/-- A sequence of legal moves cannot increase target weight. -/
theorem weight_reaches_le_of_dist [Fintype V] [DecidableEq V] (G : Graph V)
    (dist : V → V → ℕ) {D E : Pebbling V} {target : V}
    (hreach : Reaches G D E)
    (hdist : ∀ {u v : V}, G.Adj u v → dist u target ≤ dist v target + 1) :
    weight dist E target ≤ weight dist D target := by
  unfold Reaches at hreach
  refine hreach.head_induction_on ?refl ?head
  · rfl
  · intro A B hmove _ ih
    exact ih.trans (weight_move_le_of_dist (G := G) (dist := dist)
      (target := target) hmove hdist)

/-- If a reachable distribution has a pebble on the target, then its target
weight is at least one. -/
theorem one_le_weight_of_canReach [Fintype V] [DecidableEq V] (G : Graph V)
    (dist : V → V → ℕ) {D : Pebbling V} {target : V}
    (hcan : CanReach G D target)
    (hdist_self : dist target target = 0)
    (hdist_edge : ∀ {u v : V}, G.Adj u v → dist u target ≤ dist v target + 1) :
    1 ≤ weight dist D target := by
  rcases hcan with ⟨E, hreach, htarget⟩
  have hmono := weight_reaches_le_of_dist (G := G) (dist := dist)
    (D := D) (E := E) (target := target) hreach hdist_edge
  have hterm : 1 ≤ (E target : ℚ) * unitWeight dist target target := by
    have htarget_rat : (1 : ℚ) ≤ (E target : ℚ) := by
      exact_mod_cast htarget
    simpa [unitWeight, hdist_self] using htarget_rat
  have hnonneg :
      ∀ x ∈ (Finset.univ : Finset V), 0 ≤ (E x : ℚ) * unitWeight dist target x := by
    intro x _
    have hpow_pos : 0 < (2 : ℚ) ^ dist x target := by positivity
    have hunit_nonneg : 0 ≤ unitWeight dist target x := by
      unfold unitWeight
      exact div_nonneg zero_le_one hpow_pos.le
    exact mul_nonneg (Nat.cast_nonneg _) hunit_nonneg
  have hEweight : 1 ≤ weight dist E target := by
    exact hterm.trans (Finset.single_le_sum hnonneg (Finset.mem_univ target))
  exact hEweight.trans hmono

end Pebbling

end PebblingLean

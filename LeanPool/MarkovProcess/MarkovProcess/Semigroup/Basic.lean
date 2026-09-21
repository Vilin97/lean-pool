/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Strongly continuous contraction semigroups

This file provides a small reusable interface for strongly continuous contraction
semigroups on real normed spaces, parametrized by nonnegative real time.
-/

open Filter Topology

namespace MarkovProcess.Semigroup

/-- A strongly continuous contraction semigroup on a real normed space. -/
structure StronglyContinuousContractionSemigroup (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The continuous linear time-evolution operator. -/
  operator : NNReal → E →L[ℝ] E
  operator_zero : operator 0 = ContinuousLinearMap.id ℝ E
  operator_add : ∀ s t, operator (s + t) = (operator s).comp (operator t)
  opNorm_le_one : ∀ t, ‖operator t‖ ≤ 1
  continuous_orbit : ∀ x, Continuous (fun t ↦ operator t x)

namespace StronglyContinuousContractionSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

instance : CoeFun (StronglyContinuousContractionSemigroup E)
    (fun _ ↦ NNReal → E →L[ℝ] E) where
  coe S := S.operator

@[ext]
theorem ext {S T : StronglyContinuousContractionSemigroup E}
    (h : ∀ t, S t = T t) : S = T := by
  cases S with
  | mk S _ _ _ _ =>
    cases T with
    | mk T _ _ _ _ =>
      have : S = T := funext h
      cases this
      rfl

variable (S : StronglyContinuousContractionSemigroup E)

@[simp]
theorem zero : S 0 = ContinuousLinearMap.id ℝ E :=
  S.operator_zero

@[simp]
theorem zero_apply (x : E) : S 0 x = x := by
  rw [S.zero]
  rfl

@[simp]
theorem add (s t : NNReal) : S (s + t) = (S s).comp (S t) :=
  S.operator_add s t

@[simp]
theorem add_apply (s t : NNReal) (x : E) : S (s + t) x = S s (S t x) := by
  rw [S.add]
  rfl

theorem norm_operator_le_one (t : NNReal) : ‖S t‖ ≤ 1 :=
  S.opNorm_le_one t

theorem norm_apply_le (t : NNReal) (x : E) : ‖S t x‖ ≤ ‖x‖ := by
  calc
    ‖S t x‖ ≤ ‖S t‖ * ‖x‖ := (S t).le_opNorm x
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (S.norm_operator_le_one t) (norm_nonneg x)
    _ = ‖x‖ := one_mul _

theorem dist_apply_le (t : NNReal) (x y : E) : dist (S t x) (S t y) ≤ dist x y := by
  calc
    dist (S t x) (S t y) ≤ ‖S t‖ * dist x y := (S t).dist_le_opNorm x y
    _ ≤ 1 * dist x y :=
      mul_le_mul_of_nonneg_right (S.norm_operator_le_one t) dist_nonneg
    _ = dist x y := one_mul _

theorem continuous (x : E) : Continuous (fun t ↦ S t x) :=
  S.continuous_orbit x

theorem continuousAt (t : NNReal) (x : E) : ContinuousAt (fun s ↦ S s x) t :=
  (S.continuous x).continuousAt

theorem tendsto (t : NNReal) (x : E) :
    Tendsto (fun s ↦ S s x) (nhds t) (nhds (S t x)) :=
  S.continuousAt t x

theorem commute (s t : NNReal) : (S s).comp (S t) = (S t).comp (S s) := by
  rw [← S.add, ← S.add, add_comm]

theorem commute_apply (s t : NNReal) (x : E) : S s (S t x) = S t (S s x) := by
  change ((S s).comp (S t)) x = ((S t).comp (S s)) x
  rw [S.commute]

end StronglyContinuousContractionSemigroup

end MarkovProcess.Semigroup

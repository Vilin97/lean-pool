/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalSpace
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

@[expose] public section

/-! Continuous matrix fields act as genuine bounded operators on ordinary R³ L². -/

noncomputable section

namespace EulerMeanCoefficients

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerLiftedPressure
open scoped NNReal BoundedContinuousFunction

abbrev Field := Space →ᵇ (Space →L[ℝ] Space)

def multiplier (A : Field) : L2 →L[ℝ] L2 :=
  coefficientOperator A A.continuous.aestronglyMeasurable ‖A‖₊ A.norm_coe_le_norm

theorem multiplier_ae (A : Field) (u : L2) :
    multiplier A u =ᵐ[volume] fun x => A x (u x) :=
  coefficientOperator_ae A A.continuous.aestronglyMeasurable ‖A‖₊ A.norm_coe_le_norm u

theorem multiplier_norm_le (A : Field) : ‖multiplier A‖ ≤ ‖A‖ :=
  coefficientOperator_norm_le A A.continuous.aestronglyMeasurable ‖A‖₊ A.norm_coe_le_norm

theorem multiplier_add (A B : Field) : multiplier (A+B) = multiplier A + multiplier B := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [multiplier_ae (A+B) u, multiplier_ae A u, multiplier_ae B u,
    Lp.coeFn_add (multiplier A u) (multiplier B u)] with x hab ha hb hs
  change (multiplier (A+B) u) x = (multiplier A u + multiplier B u) x
  rw [hab, hs]
  simp only [Pi.add_apply]
  rw [ha, hb]
  rfl

theorem multiplier_smul (c : ℝ) (A : Field) : multiplier (c • A) = c • multiplier A := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [multiplier_ae (c • A) u, multiplier_ae A u,
    Lp.coeFn_smul c (multiplier A u)] with x hca ha hs
  change (multiplier (c • A) u) x = (c • multiplier A u) x
  rw [hca, hs]
  simp only [Pi.smul_apply]
  rw [ha]
  rfl

def multiplierLinear : Field →ₗ[ℝ] (L2 →L[ℝ] L2) where
  toFun := multiplier
  map_add' := multiplier_add
  map_smul' := multiplier_smul

/-- Uniform coefficient convergence implies operator-norm convergence by this CLM. -/
def multiplierMap : Field →L[ℝ] (L2 →L[ℝ] L2) where
  toLinearMap := multiplierLinear
  cont := AddMonoidHomClass.continuous_of_bound multiplierLinear 1 (fun A => by
    change ‖multiplier A‖ ≤ 1 * ‖A‖
    simpa only [one_mul] using multiplier_norm_le A)

@[simp] theorem multiplierMap_apply (A : Field) : multiplierMap A = multiplier A := rfl

theorem multiplier_one : multiplier (1 : Field) = ContinuousLinearMap.id ℝ L2 := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [multiplier_ae (1 : Field) u] with x hx
  exact hx

theorem multiplier_mul (A B : Field) :
    multiplier (A*B) = (multiplier A).comp (multiplier B) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [multiplier_ae (A*B) u, multiplier_ae A (multiplier B u),
    multiplier_ae B u] with x hab ha hb
  change (multiplier (A*B) u) x = (multiplier A (multiplier B u)) x
  rw [hab, ha, hb]
  rfl

theorem multiplier_inverse (A B : Field) (hAB : ∀ x v, A x (B x v) = v) (u : L2) :
    multiplier A (multiplier B u) = u := by
  apply Lp.ext
  filter_upwards [multiplier_ae A (multiplier B u), multiplier_ae B u] with x ha hb
  rw [ha, hb, hAB]

theorem multiplier_adjoint (A B : Field) (hB : ∀ x, B x = (A x).adjoint) :
    multiplier B = (multiplier A).adjoint := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left, MeasureTheory.L2.inner_def,
    MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplier_ae B u, multiplier_ae A v] with x hb ha
  rw [hb, ha, hB, ContinuousLinearMap.adjoint_inner_left]

theorem multiplier_eq_coefficientOperator (A : Field) (C : ℝ≥0)
    (hC : ∀ x, ‖A x‖ ≤ C) :
    multiplier A = coefficientOperator A A.continuous.aestronglyMeasurable C hC := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  exact (multiplier_ae A u).trans
    (coefficientOperator_ae A A.continuous.aestronglyMeasurable C hC u).symm

theorem multiplier_quadratic_upper (A : Field) (K : ℝ)
    (hA : ∀ x v, ⟪A x v, v⟫_ℝ ≤ K * ‖v‖^2) (u : L2) :
    ⟪multiplier A u, u⟫_ℝ ≤ K * ‖u‖^2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def,
    ← integral_const_mul]
  apply integral_mono_ae (MeasureTheory.L2.integrable_inner (multiplier A u) u)
    ((MeasureTheory.L2.integrable_inner u u).const_mul K)
  filter_upwards [multiplier_ae A u] with x hx
  rw [hx, real_inner_self_eq_norm_sq]
  exact hA x (u x)

end EulerMeanCoefficients

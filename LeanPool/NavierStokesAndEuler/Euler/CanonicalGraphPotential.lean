/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedGradientSpace
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Radial reconstruction of a canonically normalized scalar potential. -/

@[expose] public section


noncomputable section

namespace EulerCanonicalGraphPotential

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace
open scoped ContDiff

/-- The scalar radial integral of a spatial vector field, based at the origin. -/
def radialPotential (V : Vector3 → Vector3) (x : Vector3) : ℝ :=
  ∫ s in (0 : ℝ)..1, ⟪V (s • x), x⟫_ℝ

/-- The radial integral is normalized to vanish at the origin. -/
theorem radialPotential_zero (V : Vector3 → Vector3) : radialPotential V 0 = 0 := by
  simp [radialPotential]

/-- The fundamental theorem of calculus identifies the radial integral with a normalized genuine
potential. -/
theorem radialPotential_eq_sub (V : Vector3 → Vector3) (hV : Continuous V)
    (q : Vector3 → ℝ) (hq : ContDiff ℝ ∞ q) (hgrad : ∀ x, gradient q x = V x)
    (x : Vector3) : radialPotential V x = q x - q 0 := by
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => q (r • x)) ⟪V (s • x), x⟫_ℝ s := by
    have h := ((hq.differentiable (by simp)) (s • x)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).smul_const x)
    simpa only [Function.comp_def, id_eq, one_smul, ← inner_gradient_left, hgrad] using h
  have hi : IntervalIntegrable (fun s : ℝ => ⟪V (s • x), x⟫_ℝ) volume 0 1 :=
    ((hV.comp (continuous_id.smul continuous_const)).inner continuous_const).intervalIntegrable 0 1
  simpa only [radialPotential, one_smul, zero_smul] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi

/-- A radial reconstruction of a genuine smooth gradient is itself spatially smooth. -/
theorem radialPotential_smooth (V : Vector3 → Vector3) (hV : Continuous V)
    (q : Vector3 → ℝ) (hq : ContDiff ℝ ∞ q) (hgrad : ∀ x, gradient q x = V x) :
    ContDiff ℝ ∞ (radialPotential V) := by
  have he : radialPotential V = fun x => q x - q 0 :=
    funext (radialPotential_eq_sub V hV q hq hgrad)
  rw [he]
  exact hq.sub contDiff_const

/-- Radial normalization preserves the actual gradient. -/
theorem radialPotential_gradient (V : Vector3 → Vector3) (hV : Continuous V)
    (q : Vector3 → ℝ) (hq : ContDiff ℝ ∞ q) (hgrad : ∀ x, gradient q x = V x)
    (x : Vector3) : gradient (radialPotential V) x = V x := by
  have he : radialPotential V = fun x => q x - q 0 :=
    funext (radialPotential_eq_sub V hV q hq hgrad)
  rw [he, gradient, fderiv_sub_const]
  exact hgrad x

/-- A jointly continuous vector field has a jointly continuous radial scalar potential. -/
theorem radialPotential_joint_continuous {T : Type*} [TopologicalSpace T]
    [FirstCountableTopology T] [LocallyCompactSpace T]
    (V : T → Vector3 → Vector3) (hV : Continuous V.uncurry) :
    Continuous (fun p : T × Vector3 => radialPotential (V p.1) p.2) := by
  have hc : Continuous (fun p : (T × Vector3) × ℝ =>
      ⟪V p.1.1 (p.2 • p.1.2), p.1.2⟫_ℝ) := by
    exact (hV.comp ((continuous_fst.fst).prodMk
      (continuous_snd.smul continuous_fst.snd))).inner continuous_fst.snd
  have hi := continuous_parametric_integral_of_continuous
    (μ := volume)
    (f := fun p : T × Vector3 => fun s : ℝ => ⟪V p.1 (s • p.2), p.2⟫_ℝ)
    hc (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  simpa only [radialPotential, intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc] using hi

end EulerCanonicalGraphPotential

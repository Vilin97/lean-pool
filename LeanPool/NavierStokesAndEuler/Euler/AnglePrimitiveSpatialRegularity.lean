/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AngleMeanZeroPrimitive
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import LeanPool.NavierStokesAndEuler.Euler.CompactParameterIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The actual angular primitive is jointly smooth in spatial labels and angle. -/

@[expose] public section


noncomputable section

universe u

namespace EulerAngleMeanZeroPrimitive

open Set MeasureTheory EulerCompactParameterIntegral
open scoped ContDiff

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem rawPrimitive_fixed_interval (f : ℝ → E) (θ : ℝ) :
    rawPrimitive f θ = θ • (∫ s in (0 : ℝ)..1, f (θ*s)) := by
  simpa only [rawPrimitive, mul_zero, mul_one] using
    (intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1) f θ).symm

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

theorem rawPrimitive_joint_contDiff (F : X × ℝ → E) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : X × ℝ => rawPrimitive (fun θ => F (p.1,θ)) p.2) := by
  have hG : ContDiff ℝ ∞ (fun z : (X × ℝ) × ℝ => F (z.1.1,z.1.2*z.2)) :=
    hF.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.mul contDiff_snd))
  have hi := integral_contDiff 0 1 zero_le_one _ hG
  simpa only [rawPrimitive_fixed_interval, Pi.smul_def'] using contDiff_snd.smul hi

theorem primitive_joint_contDiff (P : ℝ) (hP : 0 ≤ P) (F : X × ℝ → E)
    (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : X × ℝ => primitive P (fun θ => F (p.1,θ)) p.2) := by
  have hr := rawPrimitive_joint_contDiff F hF
  have hm := integral_contDiff 0 P hP _ hr
  exact hr.sub (contDiff_const.smul (hm.comp contDiff_fst))

section Continuous

variable {Y : Type*} [TopologicalSpace Y] [FirstCountableTopology Y] [LocallyCompactSpace Y]

omit [CompleteSpace E] in
theorem rawPrimitive_joint_continuous (F : Y × ℝ → E) (hF : Continuous F) :
    Continuous (fun p : Y × ℝ => rawPrimitive (fun θ => F (p.1,θ)) p.2) := by
  have hG : Continuous (fun z : (Y × ℝ) × ℝ => F (z.1.1,z.1.2*z.2)) :=
    hF.comp (continuous_fst.fst.prodMk (continuous_fst.snd.mul continuous_snd))
  have hi := continuous_parametric_integral_of_continuous
    (μ := volume) (f := fun p : Y × ℝ => fun s : ℝ => F (p.1,p.2*s)) hG
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  have hi' : Continuous (fun p : Y × ℝ => ∫ s in (0 : ℝ)..1, F (p.1,p.2*s)) := by
    simpa only [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
      integral_Icc_eq_integral_Ioc] using hi
  simpa only [rawPrimitive_fixed_interval, Pi.smul_def'] using continuous_snd.smul hi'

omit [CompleteSpace E] in
theorem primitive_joint_continuous (P : ℝ) (hP : 0 ≤ P) (F : Y × ℝ → E)
    (hF : Continuous F) :
    Continuous (fun p : Y × ℝ => primitive P (fun θ => F (p.1,θ)) p.2) := by
  have hr := rawPrimitive_joint_continuous F hF
  have hm := continuous_parametric_integral_of_continuous
    (μ := volume) (f := fun y : Y => fun s : ℝ => rawPrimitive (fun θ => F (y,θ)) s)
    hr (isCompact_Icc : IsCompact (Icc (0 : ℝ) P))
  have hm' : Continuous (fun y : Y => ∫ s in (0 : ℝ)..P, rawPrimitive (fun θ => F (y,θ)) s) := by
    simpa only [intervalIntegral.integral_of_le hP, integral_Icc_eq_integral_Ioc] using hm
  exact hr.sub (continuous_const.smul (hm'.comp continuous_fst))

end Continuous
end EulerAngleMeanZeroPrimitive

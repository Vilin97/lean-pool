/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketLabelData
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2GevreyCalculus

@[expose] public section

/-! Keeping the physical label scale in the coefficient bounds gives one
factor ell for each normalized spatial derivative. This factor is needed
in the neighboring-label estimates of the induction. -/

noncomputable section

namespace EulerOperatorGevreyCalculus

open EulerGevrey
open scoped ContDiff

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem scalar_precomp_bound (f : E → V) (hf : ContDiff ℝ ∞ f)
    (C R ell : ℝ) (hell : 0 ≤ ell)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ C*majorant R 0 n) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => f (ell • y)) x‖ ≤ C*majorant (ell*R) 0 n := by
  rw [iteratedFDeriv_comp_const_smul ell (hf.of_le (by simp)),norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hell n)]
  calc
    _ ≤ ell^n*(C*majorant R 0 n) := mul_le_mul_of_nonneg_left (hb n (ell • x)) (pow_nonneg hell n)
    _ = _ := by simp only [majorant,Nat.add_zero,mul_pow]; ring

end EulerOperatorGevreyCalculus

namespace EulerParentPacketFrames.LabelData

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerLpTranslation
  EulerPacketParentLabelBounds EulerPacketCofactor EulerGevrey EulerOperatorGevreyCalculus
open scoped ContDiff BoundedContinuousFunction

variable {G : Parent} (L : LabelData G)

def scaledRadius : ℝ := G.ell*coefficientRadius L.K

theorem scaledRadius_nonneg : 0 ≤ L.scaledRadius :=
  mul_nonneg G.ell_pos.le (coefficientRadius_nonneg L.K)

theorem scaled_gradient_bound (A : SmoothL2Field Space) (hA : HasLabelBound L.K A)
    (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ A.field (G.ell • y)) x‖ ≤
      gradientAmplitude L.K*majorant L.scaledRadius 0 n := by
  apply scalar_precomp_bound (fderiv ℝ A.field) (A.smooth.fderiv_right (m := ∞) (by simp))
    (gradientAmplitude L.K) (coefficientRadius L.K) G.ell G.ell_pos.le
  intro j y
  have h := source_gradient_bound A.toLp A.translation_contDiff A.field A.smooth A.toLp_ae
    L.K (zero_le_one.trans L.K_one) hA (ContinuousLinearMap.id ℝ Space) norm_id_le j y
  simpa only [ContinuousLinearMap.id_apply] using h

theorem frame_scaled_bound (n : ℕ) (t : Icc (0 : ℝ) G.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (G.frame.field t : Space → EndSpace) x‖ ≤
      frameAmplitude L.K*majorant L.scaledRadius 0 n := by
  have he : (G.frame.field t : Space → EndSpace)=
      fun y => ContinuousLinearMap.id ℝ Space+fderiv ℝ (L.displacement t).field (G.ell • y) :=
    funext (L.frame_match t)
  rw [he]
  apply scalar_precomp_bound (fun y => ContinuousLinearMap.id ℝ Space+fderiv ℝ (L.displacement
    t).field y)
    (contDiff_const.add ((L.displacement t).smooth.fderiv_right (m := ∞) (by simp)))
    (frameAmplitude L.K) (coefficientRadius L.K) G.ell G.ell_pos.le
  intro j y
  have h := source_deformation_bound (L.displacement t).toLp (L.displacement t).translation_contDiff
    (L.displacement t).field (L.displacement t).smooth (L.displacement t).toLp_ae
    L.K (zero_le_one.trans L.K_one) (L.displacement_bound t)
    (ContinuousLinearMap.id ℝ Space) norm_id_le j y
  simpa only [ContinuousLinearMap.id_apply] using h

theorem first_scaled_bound (n : ℕ) (t : Icc (0 : ℝ) G.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (G.first.field t : Space → EndSpace) x‖ ≤
      gradientAmplitude L.K*majorant L.scaledRadius 0 n := by
  have he : (G.first.field t : Space → EndSpace)=
      fun y => fderiv ℝ (L.velocity t).field (G.ell • y) := funext (L.first_match t)
  rw [he]
  exact L.scaled_gradient_bound (L.velocity t) (L.velocity_bound t) n x

theorem second_scaled_bound (n : ℕ) (t : Icc (0 : ℝ) G.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (G.second.field t : Space → EndSpace) x‖ ≤
      gradientAmplitude L.K*majorant L.scaledRadius 0 n := by
  have he : (G.second.field t : Space → EndSpace)=
      fun y => fderiv ℝ (L.acceleration t).field (G.ell • y) := funext (L.second_match t)
  rw [he]
  exact L.scaled_gradient_bound (L.acceleration t) (L.acceleration_bound t) n x

theorem inverse_scaled_bound (n : ℕ) (t : Icc (0 : ℝ) G.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (G.inverse.field t : Space → EndSpace) x‖ ≤
      (9*(frameAmplitude L.K)^2)*majorant L.scaledRadius 0 n :=
  coefficientInverse_bound G.frame.toSmoothCoefficientPath G.inverse.field G.frame_det
    G.inverse_left
    L.scaledRadius (frameAmplitude L.K) L.scaledRadius_nonneg (frameAmplitude_nonneg L.K)
    L.frame_scaled_bound n t x

theorem strain_scaled_bound (n : ℕ) (t : Icc (0 : ℝ) G.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (G.strain.field t : Space → EndSpace) x‖ ≤
      (27*(frameAmplitude L.K)^2*gradientAmplitude L.K)*majorant L.scaledRadius 0 n :=
  coefficientStrain_bound G.frame.toSmoothCoefficientPath G.first.toSmoothCoefficientPath
    G.strain.toSmoothCoefficientPath G.frame_det G.strain_equation L.scaledRadius
    (frameAmplitude L.K) (gradientAmplitude L.K) L.scaledRadius_nonneg
    (frameAmplitude_nonneg L.K) (gradientAmplitude_nonneg L.K)
    L.frame_scaled_bound L.first_scaled_bound n t x

theorem curvature_scaled_bound (n : ℕ) (t : Icc (0 : ℝ) G.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (G.curvature.field t : Space → EndSpace) x‖ ≤
      (27*(frameAmplitude L.K)^2*gradientAmplitude L.K)*majorant L.scaledRadius 0 n :=
  coefficientCurvature_bound G.frame.toSmoothCoefficientPath G.second.toSmoothCoefficientPath
    G.curvature.toSmoothCoefficientPath G.frame_det G.second_equation L.scaledRadius
    (frameAmplitude L.K) (gradientAmplitude L.K) L.scaledRadius_nonneg
    (frameAmplitude_nonneg L.K) (gradientAmplitude_nonneg L.K)
    L.frame_scaled_bound L.second_scaled_bound n t x

end EulerParentPacketFrames.LabelData

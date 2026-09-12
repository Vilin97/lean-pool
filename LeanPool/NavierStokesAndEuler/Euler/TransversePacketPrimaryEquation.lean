/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryPaths

/-!
The actual joined primary solves the homogeneous transverse equation.
The physical normal field is pointwise; it is never treated as one L²
vector. All equations below are for genuine cylinder representatives.
-/

@[expose] public section


noncomputable section

namespace EulerTransversePacketPrimary

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerTransversePacketProvider EulerTimeIntervalRestriction

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D)

theorem balance_ae (t : Icc (0 : ℝ) D.T) :
    ∀ᵐ x ∂liftMeasure P,
      derivativePath τ hτ hτT B Y t x+D.M.field t x.1 (velocityPath τ hτ hτT B Y t x) +
        (-(2*⟪D.normal.field t x.1,D.M.field t x.1 (velocityPath τ hτ hτT B Y t x)⟫_ℝ)/
          ‖D.normal.field t x.1‖^2) • D.normal.field t x.1 = 0 := by
  by_cases ht : (t : ℝ) ≤ τ
  · let th : Icc (0 : ℝ) τ := ⟨t,t.property.1,ht⟩
    have hv : velocityPath τ hτ hτT B Y t = pastVelocity τ hτ hτT B Y th :=
      velocityPath_left τ hτ hτT B Y th
    have hd : derivativePath τ hτ hτT B Y t = pastDerivative τ hτ hτT B Y th :=
      derivativePath_left τ hτ hτT B Y th
    rw [hv,hd]
    exact past_balance_ae τ hτ hτT B Y th
  · let tr : Icc τ D.T := ⟨t,(not_le.mp ht).le,t.property.2⟩
    let tf : Icc (0 : ℝ) (D.T-τ) :=
      ⟨(t : ℝ)-τ,sub_nonneg.mpr tr.property.1,sub_le_sub_right t.property.2 τ⟩
    have hv : velocityPath τ hτ hτT B Y t = futureVelocity τ hτ hτT B Y tf :=
      velocityPath_right τ hτ hτT B Y tr
    have hd : derivativePath τ hτ hτT B Y t = futureDerivative τ hτ hτT B Y tf :=
      derivativePath_right τ hτ hτT B Y tr
    have hidx : tailInclusion D.T τ hτ.le tf = t := by
      apply Subtype.ext
      change τ+((t : ℝ)-τ) = (t : ℝ)
      ring
    have hM : (D.tail τ hτ.le hτT).M.field tf = D.M.field t := by
      change D.M.field (tailInclusion D.T τ hτ.le tf) = D.M.field t
      rw [hidx]
    have hm : (D.tail τ hτ.le hτT).normal.field tf = D.normal.field t := by
      change D.normal.field (tailInclusion D.T τ hτ.le tf) = D.normal.field t
      rw [hidx]
    have he := future_balance_ae τ hτ hτT B Y tf
    rw [hM,hm,← hv,← hd] at he
    exact he

theorem tangent_ae (t : Icc (0 : ℝ) D.T) :
    ∀ᵐ x ∂liftMeasure P,
      ⟪D.normal.field t x.1,velocityPath τ hτ hτT B Y t x⟫_ℝ = 0 := by
  by_cases ht : (t : ℝ) ≤ τ
  · let th : Icc (0 : ℝ) τ := ⟨t,t.property.1,ht⟩
    have hv : velocityPath τ hτ hτT B Y t = pastVelocity τ hτ hτT B Y th :=
      velocityPath_left τ hτ hτT B Y th
    rw [hv]
    filter_upwards [EulerTransversePacketEndpoint.velocityPath_ae B (endpointData τ hτ hτT Y) th]
      with x hx
    change pastVelocity τ hτ hτT B Y th x = _ at hx
    rw [hx]
    exact (D.initial τ hτ hτT.le).frame_tangent th x.1 _
  · let tr : Icc τ D.T := ⟨t,(not_le.mp ht).le,t.property.2⟩
    let tf : Icc (0 : ℝ) (D.T-τ) :=
      ⟨(t : ℝ)-τ,sub_nonneg.mpr tr.property.1,sub_le_sub_right t.property.2 τ⟩
    let Df := D.tail τ hτ.le hτT
    have hv : velocityPath τ hτ hτT B Y t = futureVelocity τ hτ hτT B Y tf :=
      velocityPath_right τ hτ hτT B Y tr
    have hidx : tailInclusion D.T τ hτ.le tf = t := by
      apply Subtype.ext
      change τ+((t : ℝ)-τ) = (t : ℝ)
      ring
    have hm : Df.normal.field tf = D.normal.field t := by
      change D.normal.field (tailInclusion D.T τ hτ.le tf) = D.normal.field t
      rw [hidx]
    rw [hv,← hm]
    filter_upwards [EulerSourceCylinderEquation.velocity_ae P D.support D.support_measurable
      Df.T Df.T_pos.le Df.frame Df.frameDerivative Df.frameLower Df.frameLower_pos Df.frame_lower
      (zeroForcing Df).path (forwardInitial τ hτ hτT B Y).value tf] with x hx
    change futureVelocity τ hτ hτT B Y tf x = _ at hx
    rw [hx]
    exact Df.frame_tangent tf x.1 _

end EulerTransversePacketPrimary

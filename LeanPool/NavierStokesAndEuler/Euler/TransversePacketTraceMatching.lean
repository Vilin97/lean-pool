/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketMatching

@[expose] public section

/-! The actual time derivative and normalized pressure also match at the history/forward junction.
  -/

noncomputable section

namespace EulerTransversePacketJoin

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerTimeIntervalRestriction EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerLpCylinderPaths EulerLpCylinderRectangular EulerCylinderScalarPrimitive
    EulerSourceNormalCoefficient
  EulerPacketProfileRecursion EulerTransversePacketProvider
open scoped ContDiff BoundedContinuousFunction

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) {raw : VectorField} (G : Forcing P D raw)

omit [Fact (0 < P)] [CompleteSpace U] in
theorem source_coefficient_match {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : SmoothCoefficientPath (Icc (0 : ℝ) D.T) V) :
    (A.comp (initialInclusion D.T τ hτT.le)).field ⟨τ,hτ.le,le_rfl⟩ =
      (A.comp (tailInclusion D.T τ hτ.le)).field ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ := by
  change A.field ⟨τ,hτ.le,hτT.le⟩ = A.field ⟨τ+0,by linarith,by linarith⟩
  simp only [add_zero]

omit [Fact (0 < P)] [CompleteSpace U] in
theorem normal_match :
    (D.initial τ hτ hτT.le).normal.field ⟨τ,hτ.le,le_rfl⟩ =
      (D.tail τ hτ.le hτT).normal.field ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ :=
  source_coefficient_match τ hτ hτT D.normal

omit [CompleteSpace U] in
theorem forcing_match :
    ((G.initial τ hτ hτT.le).path ⟨τ,hτ.le,le_rfl⟩ : CylinderL2 P Space) =
      ((G.tail τ hτ.le hτT).path ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ : CylinderL2 P Space) := by
  change (G.path ⟨τ,hτ.le,hτT.le⟩ : CylinderL2 P Space) =
    (G.path ⟨τ+0,by linarith,by linarith⟩ : CylinderL2 P Space)
  simp only [add_zero]

/-- The same physical first-order equation determines the same derivative
from the matching velocity and forcing. -/
theorem derivative_match : pastDerivative τ hτ hτT B G ⟨τ,hτ.le,le_rfl⟩ =
    futureDerivative τ hτ hτT B G ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ := by
  let Dh := D.initial τ hτ hτT.le
  let Df := D.tail τ hτ.le hτT
  let Gh := G.initial τ hτ hτT.le
  let Gf := G.tail τ hτ.le hτT
  let Bh := B
  let I := forwardInitial τ hτ hτT B G
  let th : Icc (0 : ℝ) τ := ⟨τ,hτ.le,le_rfl⟩
  let tf : Icc (0 : ℝ) (D.T-τ) := ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩
  have hM : Dh.M.field th = Df.M.field tf := source_coefficient_match τ hτ hτT D.M
  have hm : Dh.normal.field th = Df.normal.field tf := normal_match τ hτ hτT
  have hforce : (Gh.path th : CylinderL2 P Space) = (Gf.path tf : CylinderL2 P Space) :=
    forcing_match τ hτ hτT G
  have hv := velocity_match τ hτ hτT B G
  have hh := Bh.balance_ae Gh th
  have hf := EulerSourceCylinderEquation.velocity_balance_ae P D.support D.support_measurable
    Df.T Df.T_pos.le Df.frame Df.frameDerivative Df.frameLower Df.frameLower_pos Df.frame_lower
    Gf.path I.value (fun t x => Df.M.field t x) (fun t x => Df.normal.field t x)
    (HistoryData.normal_ne_zero (D := Df)) Df.frame_tangent Df.frame_range Df.frame_strain tf
  change ∀ᵐ x ∂liftMeasure P,
    pastDerivative τ hτ hτT B G th x+Dh.M.field th x.1 (pastVelocity τ hτ hτT B G th x)+
      ((⟪Dh.normal.field th x.1,(Gh.path th : CylinderL2 P Space) x⟫_ℝ-
        2*⟪Dh.normal.field th x.1,Dh.M.field th x.1 (pastVelocity τ hτ hτT B G th x)⟫_ℝ)/
        ‖Dh.normal.field th x.1‖^2) • Dh.normal.field th x.1 = (Gh.path th : CylinderL2 P Space) x
          at hh
  change ∀ᵐ x ∂liftMeasure P,
    futureDerivative τ hτ hτT B G tf x+Df.M.field tf x.1 (futureVelocity τ hτ hτT B G tf x)+
      ((⟪Df.normal.field tf x.1,(Gf.path tf : CylinderL2 P Space) x⟫_ℝ-
        2*⟪Df.normal.field tf x.1,Df.M.field tf x.1 (futureVelocity τ hτ hτT B G tf x)⟫_ℝ)/
        ‖Df.normal.field tf x.1‖^2) • Df.normal.field tf x.1 = (Gf.path tf : CylinderL2 P Space) x
          at hf
  rw [hM,hm,hforce,hv] at hh
  apply Lp.ext
  filter_upwards [hh,hf] with x hx hy
  exact add_right_cancel (add_right_cancel (hx.trans hy.symm))

/-- The normalized pressure integral has the same input scalar L² class on
both sides of the junction. -/
theorem pressure_match : pastPressure τ hτ hτT B G ⟨τ,hτ.le,le_rfl⟩ =
    futurePressure τ hτ hτT B G ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ := by
  let Dh := D.initial τ hτ hτT.le
  let Df := D.tail τ hτ.le hτT
  let th : Icc (0 : ℝ) τ := ⟨τ,hτ.le,le_rfl⟩
  let tf : Icc (0 : ℝ) (D.T-τ) := ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩
  have hM : Dh.M.field th = Df.M.field tf := source_coefficient_match τ hτ hτT D.M
  have hm : Dh.normal.field th = Df.normal.field tf := normal_match τ hτ hτT
  have hN : normalFunctional Dh.normal Dh.normalLower Dh.normalLower_pos Dh.normal_lower th =
      normalFunctional Df.normal Df.normalLower Df.normalLower_pos Df.normal_lower tf := by
    apply BoundedContinuousFunction.ext
    intro x
    apply ContinuousLinearMap.ext
    intro v
    erw [normalFunctional_apply,normalFunctional_apply,hm]
  change primitive P (fullOperatorMap P
      (normalFunctional Dh.normal Dh.normalLower Dh.normalLower_pos Dh.normal_lower th)
      (((G.initial τ hτ hτT.le).path th : CylinderL2 P Space)-(2 : ℝ) •
        fullOperatorMap P (Dh.M.field th) (pastVelocity τ hτ hτT B G th))) =
    primitive P (fullOperatorMap P
      (normalFunctional Df.normal Df.normalLower Df.normalLower_pos Df.normal_lower tf)
      (((G.tail τ hτ.le hτT).path tf : CylinderL2 P Space)-(2 : ℝ) •
        fullOperatorMap P (Df.M.field tf) (futureVelocity τ hτ hτT B G tf)))
  have hforce : ((G.initial τ hτ hτT.le).path th : CylinderL2 P Space) =
      ((G.tail τ hτ.le hτT).path tf : CylinderL2 P Space) := forcing_match τ hτ hτT G
  have hv : pastVelocity τ hτ hτT B G th = futureVelocity τ hτ hτT B G tf :=
    velocity_match τ hτ hτT B G
  rw [hN,hM,hforce,hv]

end EulerTransversePacketJoin

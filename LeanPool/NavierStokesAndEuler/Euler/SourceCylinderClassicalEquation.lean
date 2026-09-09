/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderClassical

@[expose] public section

/-!
# The actual pointwise forward equation

The L² coordinate equation and normal balance hold for the reconstructed
smooth field at every cylinder point. The scalar normal residual is the
literal source expression; its angular primitive will supply the pressure.
-/

noncomputable section

namespace EulerSourceCylinderClassical

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace
  EulerMetricTransport EulerMeanCoefficients EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerSourceCylinderEquation EulerCylinderSmoothOrbit EulerVolterraConvolution
open scoped ContDiff BoundedContinuousFunction

variable (period : ℝ) [Fact (0 < period)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (S : Set Space) (hS : MeasurableSet S) (hSc : IsCompact S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] Space))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c*‖v‖^2 ≤ ‖Q.field t x v‖^2)
  (f : C(Icc (0 : ℝ) T,Supported period Space S hS)) (a₀ : Supported period U S hS)
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS f)))
  (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate period a (a₀ : CylinderL2 period U)))
  (M : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (m : SmoothCoefficientPath (Icc (0 : ℝ) T) Space)

/-- The source's literal scalar normal pressure residual. -/
def normalResidual (t : Icc (0 : ℝ) T) (x : LiftDomain period) : ℝ :=
  (⟪m.field t x.1,pointField period (includePath period S hS f) hf t x⟫_ℝ -
    2*⟪m.field t x.1,M.field t x.1 (field period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t x)⟫_ℝ) /
      ‖m.field t x.1‖^2

theorem normalResidual_continuous (hm : ∀ t x, m.field t x ≠ 0) (t : Icc (0 : ℝ) T) :
    Continuous (normalResidual period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m t) := by
  have hA := smoothField_continuous period _ (field_smooth period S hS hSc T hT Q Q₁ c hc hQ f a₀
    hf ha₀ t)
  have hF := smoothField_continuous period _ (pointField_smooth period (includePath period S hS f)
    hf t)
  have hM : Continuous (fun x : LiftDomain period => M.field t x.1) := (M.field t).continuous.comp
    continuous_fst
  have hm' : Continuous (fun x : LiftDomain period => m.field t x.1) := (m.field t).continuous.comp
    continuous_fst
  exact ((hm'.inner hF).sub (continuous_const.mul (hm'.inner (hM.clm_apply hA)))).div
    (hm'.norm.pow 2) (fun x => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hm t x.1)))

/-- The literal scalar pressure source is smooth in every spatial and angular variable. -/
theorem normalResidual_smooth (hm : ∀ t x, m.field t x ≠ 0)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period
      (normalResidual period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m t) x) := by
  have hp : ContDiff ℝ ∞ (fun h : LiftTangent => x.1+h.1) := contDiff_const.add contDiff_fst
  have hm' : ContDiff ℝ ∞ (fun h : LiftTangent => m.field t (x.1+h.1)) := (m.smooth t).comp hp
  have hM : ContDiff ℝ ∞ (fun h : LiftTangent => M.field t (x.1+h.1)) := (M.smooth t).comp hp
  have hA := field_smooth period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t x
  have hF := pointField_smooth period (includePath period S hS f) hf t x
  have hd : ∀ h : LiftTangent, ⟪m.field t (x.1+h.1),m.field t (x.1+h.1)⟫_ℝ ≠ 0 := by
    intro h
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hm t (x.1+h.1)))
  have h := ((hm'.inner ℝ hF).sub ((contDiff_const (c := (2 : ℝ))).mul
    (hm'.inner ℝ (hM.clm_apply hA)))).div (hm'.inner ℝ hm') hd
  convert h using 1 <;> first
    | rfl
    | (funext z; simp only [localFieldLift,normalResidual,real_inner_self_eq_norm_sq,Pi.div_apply])

/-- Pointwise tangency follows from the actual frame representation and continuity. -/
theorem field_tangent
    (hTangent : ∀ t x v, ⟪m.field t x,Q.field t x v⟫_ℝ = 0)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    ⟪m.field t x.1,field period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t x⟫_ℝ = 0 := by
  have hae : (fun y : LiftDomain period => ⟪m.field t y.1,
      field period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t y⟫_ℝ) =ᵐ[liftMeasure period] (fun _ =>
        0) := by
    filter_upwards [velocity_ae period S hS T hT Q Q₁ c hc hQ f a₀ t,
      field_ae period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t] with y hq ha
    rw [← ha,hq]
    exact hTangent t y.1 _
  exact congrFun (Measure.eq_of_ae_eq hae
    (((m.field t).continuous.comp continuous_fst).inner (smoothField_continuous period _
      (field_smooth period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t))) continuous_const) x

/-- Equation (11) before angular integration holds at every cylinder point. -/
theorem field_balance (hm : ∀ t x, m.field t x ≠ 0)
    (hTangent : ∀ t x v, ⟪m.field t x,Q.field t x v⟫_ℝ = 0)
    (hRange : ∀ t x η, ⟪m.field t x,η⟫_ℝ = 0 → ∃ v, Q.field t x v = η)
    (hFlow : ∀ t x, Q₁.field t x = (M.field t x).comp (Q.field t x))
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    derivativeField period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t x +
      M.field t x.1 (field period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t x) +
      normalResidual period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m t x • m.field t x.1 =
        pointField period (includePath period S hS f) hf t x := by
  have hae : (fun y : LiftDomain period =>
      derivativeField period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t y +
      M.field t y.1 (field period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t y) +
      normalResidual period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m t y • m.field t y.1)
        =ᵐ[liftMeasure period]
        pointField period (includePath period S hS f) hf t := by
    filter_upwards [velocity_balance_ae period S hS T hT Q Q₁ c hc hQ f a₀
        (fun s y => M.field s y) (fun s y => m.field s y) hm hTangent hRange hFlow t,
      field_ae period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t,
      derivativeField_ae period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t,
      pointField_ae period (includePath period S hS f) hf t] with y he ha hd hforce
    change (f t : CylinderL2 period Space) y = pointField period (includePath period S hS f) hf t y
      at hforce
    rw [ha,hd,hforce] at he
    exact he
  have hA := smoothField_continuous period _ (field_smooth period S hS hSc T hT Q Q₁ c hc hQ f a₀
    hf ha₀ t)
  have hD := smoothField_continuous period _ (derivativeField_smooth period S hS hSc T hT Q Q₁ c hc
    hQ f a₀ hf ha₀ t)
  have hF := smoothField_continuous period _ (pointField_smooth period (includePath period S hS f)
    hf t)
  have hM : Continuous (fun y : LiftDomain period => M.field t y.1) := (M.field t).continuous.comp
    continuous_fst
  have hm' : Continuous (fun y : LiftDomain period => m.field t y.1) := (m.field t).continuous.comp
    continuous_fst
  exact congrFun (Measure.eq_of_ae_eq hae ((hD.add (hM.clm_apply hA)).add
    ((normalResidual_continuous period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m hm t).smul hm'))
      hF) x

end EulerSourceCylinderClassical

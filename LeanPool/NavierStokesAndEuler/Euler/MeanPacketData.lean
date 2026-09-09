/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanSourceStrongInverse
public import LeanPool.NavierStokesAndEuler.Euler.MeanSourceSpatialRegularity
public import LeanPool.NavierStokesAndEuler.Euler.MeanPressureRepresentative
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousForcingTimeLp
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpLinearity

@[expose] public section

/-!
# Concrete source data for the mean packet provider

This record contains only the given matrix coefficients and the manuscript's
pointwise inequalities and time identities. Its solver and strong evolution
are the previously constructed actual variational inverse, not input fields.
-/

noncomputable section

namespace EulerMeanPacketProvider

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerMeanCoefficients EulerMeanBoundary EulerMeanHarmonic
  EulerMeanSourceInverse EulerMeanVariationalInverse EulerLiftedPressure EulerTimeLp
    EulerVolterraConvolution
open scoped ContDiff NNReal

/-- Literal coefficient data and source smallness hypotheses. -/
structure Data where
  T : ℝ
  T_pos : 0 < T
  ℓ : ℝ
  ℓ_pos : 0 < ℓ
  ℓ_le_one : ℓ ≤ 1
  F : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)
  F₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)
  F₂ : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)
  M : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)
  H : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)
  FInv : C(Icc (0 : ℝ) T,Field)
  M0 : BoundedSmoothField (Space →L[ℝ] Space)
  Be : ℝ
  Bc : ℝ
  L : ℝ
  r : ℝ
  K : ℝ
  Be_nonneg : 0 ≤ Be
  Bc_nonneg : 0 ≤ Bc
  L_lower : boundaryLocalizationC1*Bc ≤ L
  r_nonneg : 0 ≤ r
  r_le_quarter : r ≤ 1/4
  K_nonneg : 0 ≤ K
  exterior_lower : ∀ x, r ≤ ‖ℓ • x‖ → ∀ v : Space, -Be*‖v‖^2 ≤ ⟪M0.field x v,v⟫_ℝ
  core_lower : ∀ x, ‖ℓ • x‖ < r → ∀ v : Space, -Bc*‖v‖^2 ≤ ⟪M0.field x v,v⟫_ℝ
  inverse_left : ∀ t x v, FInv t x (F.field t x v) = v
  inverse_right : ∀ t x v, F.field t x (FInv t x v) = v
  inverse_initial : ∀ x v, FInv ⟨0, le_rfl, T_pos.le⟩ x v = v
  derivative_initial : ∀ x, F₁.field ⟨0, le_rfl, T_pos.le⟩ x = M0.field x
  frame_time : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
    HasDerivWithinAt (fun s => extendPath (Y := Field) T T_pos.le F.field s x)
      (extendPath (Y := Field) T T_pos.le F₁.field t x) (Icc (0 : ℝ) T) t
  derivative_time : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
    HasDerivWithinAt (fun s => extendPath (Y := Field) T T_pos.le F₁.field s x)
      (extendPath (Y := Field) T T_pos.le F₂.field t x) (Icc (0 : ℝ) T) t
  second_equation : ∀ t x v, F₂.field t x v = -(H.field t x (F.field t x v))
  strain_equation : ∀ t x v, F₁.field t x v = M.field t x (F.field t x v)
  curvature_upper : ∀ t x v, ⟪H.field t x v,v⟫_ℝ ≤ K*‖v‖^2
  small : K*(T^2/2)+Be*T+boundaryLocalizationC2*Bc*r^3*T ≤ 1/2

namespace Data

variable (D : Data)

abbrev opF := operatorPath D.T D.F.field
abbrev opF₁ := operatorPath D.T D.F₁.field
abbrev opF₂ := operatorPath D.T D.F₂.field
abbrev opM := operatorPath D.T D.M.field
abbrev opH := operatorPath D.T D.H.field
abbrev opInv := operatorPath D.T D.FInv

theorem opInv_left : ∀ t v, D.opInv t (D.opF t v) = v :=
  operatorPath_inverse D.T D.FInv D.F.field D.inverse_left

theorem opInv_right : ∀ t v, D.opF t (D.opInv t v) = v :=
  operatorPath_inverse D.T D.F.field D.FInv D.inverse_right

theorem opInv_initial : D.opInv ⟨0, le_rfl, D.T_pos.le⟩ = ContinuousLinearMap.id ℝ L2 :=
  operatorPath_identity_at D.T D.FInv ⟨0, le_rfl, D.T_pos.le⟩ D.inverse_initial

theorem opF_time : ∀ t : Icc (0 : ℝ) D.T,
    HasDerivWithinAt (extendPath D.T D.T_pos.le D.opF) (D.opF₁ t) (Icc (0 : ℝ) D.T) t :=
  operatorPath_hasDerivWithinAt D.T D.T_pos.le D.F.field D.F₁.field D.frame_time

theorem opF₁_time : ∀ t : Icc (0 : ℝ) D.T,
    HasDerivWithinAt (extendPath D.T D.T_pos.le D.opF₁) (D.opF₂ t) (Icc (0 : ℝ) D.T) t :=
  operatorPath_hasDerivWithinAt D.T D.T_pos.le D.F₁.field D.F₂.field D.derivative_time

theorem opF₁_initial : D.opF₁ ⟨0, le_rfl, D.T_pos.le⟩ =
    coefficientOperator D.M0.field D.M0.field.continuous.aestronglyMeasurable
      ‖D.M0.field‖₊ D.M0.field.norm_coe_le_norm :=
  operatorPath_initial_coefficient D.T D.T_pos.le D.F₁.field D.M0.field
    D.derivative_initial ‖D.M0.field‖₊ D.M0.field.norm_coe_le_norm

theorem opF₂_eq : ∀ t, D.opF₂ t = -(D.opH t).comp (D.opF t) := by
  intro t
  apply ContinuousLinearMap.ext
  intro v
  exact operatorPath_neg_comp D.T D.H.field D.F.field D.F₂.field D.second_equation t v

theorem opStrain_eq : ∀ t v, D.opF₁ t v = D.opM t (D.opF t v) :=
  operatorPath_comp D.T D.M.field D.F.field D.F₁.field D.strain_equation

theorem opCurvature_upper : ∀ t v, ⟪D.opH t v,v⟫_ℝ ≤ D.K*‖v‖^2 :=
  operatorPath_quadratic_upper D.T D.H.field D.K D.curvature_upper

/-- The actual source weak inverse with the harmonic boundary estimate discharged. -/
def solver : TimeLp D.T L2 →L[ℝ] meanDerivatives D.T D.T_pos.le D.opInv :=
  sourceMeanSolver D.T D.T_pos.le D.ℓ D.ℓ_pos D.M0.field D.M0.field.continuous.aestronglyMeasurable
    ‖D.M0.field‖₊ D.M0.field.norm_coe_le_norm D.Be D.Bc D.L D.r D.Be_nonneg D.Bc_nonneg
    D.L_lower D.r_nonneg D.r_le_quarter D.exterior_lower D.core_lower
    D.opInv D.opH D.K D.K_nonneg D.opInv_initial D.opCurvature_upper D.small

/-- The source strong evolution is obtained from the constructed inverse. -/
def evolution (f : TimeLp D.T L2) :
    StrongMeanEvolution D.T D.T_pos.le D.opInv D.opF D.opF₁
      (boundaryOperator (scaledCutoff D.ℓ D.ℓ_pos)) D.L (D.solver f) f :=
  Classical.choice (sourceMeanSolver_strong D.T D.T_pos.le D.ℓ D.ℓ_pos
    D.M0.field D.M0.field.continuous.aestronglyMeasurable ‖D.M0.field‖₊ D.M0.field.norm_coe_le_norm
    D.Be D.Bc D.L D.r D.Be_nonneg D.Bc_nonneg D.L_lower D.r_nonneg D.r_le_quarter
    D.exterior_lower D.core_lower D.opInv D.opF D.opF₁ D.opF₂ D.opH D.K D.K_nonneg
    D.opInv_initial D.opCurvature_upper D.small D.opF_time D.opF₁_time
    D.opInv_left D.opInv_right D.opF₁_initial D.opF₂_eq f)

abbrev frameLower : ℝ := meanFrameCoercivity D.T D.opInv

theorem frameLower_pos : 0 < D.frameLower := meanFrameCoercivity_pos D.T D.opInv

theorem frame_lower : ∀ t v, D.frameLower*‖v‖^2 ≤ ‖solenoidalFrame D.T D.opF t v‖^2 :=
  solenoidalFrame_lower D.T D.opInv D.opF D.opInv_left

end Data

end EulerMeanPacketProvider

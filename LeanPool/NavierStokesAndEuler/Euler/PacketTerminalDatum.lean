/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderCompactTranslation
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PeriodicProfile
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SpatialCutoffs

/-!
The literal compact terminal datum χ₁(y) fδ(θ) ξT.  The periodic variable
has period 2π.  The constant vector is multiplied by the spatial cutoff
before it is placed in the genuine cylinder L² space.
-/

@[expose] public section


noncomputable section

namespace EulerPacketTerminalDatum

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerTransportDerivatives EulerSpatialCutoffs EulerPeriodicProfile
  EulerCylinderCompact EulerLpCylinderTranslation
open scoped ContDiff

/-- Period: an abbreviation for `2 * Real.pi`. -/
abbrev period : ℝ := 2 * Real.pi

instance period_pos : Fact (0 < period) := ⟨mul_pos (by norm_num) Real.pi_pos⟩

/-- Scalar field, given by `innerCutoff x.1 * (profile_periodic δ).lift x.2`. -/
def scalarField (δ : ℝ) (x : LiftDomain period) : ℝ :=
  innerCutoff x.1 * (profile_periodic δ).lift x.2

/-- Field, given by `scalarField δ x • ξ`. -/
def field {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (δ : ℝ) (ξ : U) (x : LiftDomain period) : U := scalarField δ x • ξ

@[simp] theorem scalarField_coe (δ : ℝ) (y : Space) (θ : ℝ) :
    scalarField δ (y,(θ : AddCircle period)) = innerCutoff y * profile δ θ := by
  simp only [scalarField,Function.Periodic.lift_coe]

@[simp] theorem field_coe {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (δ : ℝ) (ξ : U) (y : Space) (θ : ℝ) :
    field δ ξ (y,(θ : AddCircle period)) = (innerCutoff y * profile δ θ) • ξ := by
  rw [field,scalarField_coe]

theorem local_scalarField (δ : ℝ) (y : Space) (θ : ℝ) :
    localFieldLift period (scalarField δ) (y,(θ : AddCircle period)) =
      fun a : LiftTangent => innerCutoff (y+a.1) * profile δ (θ+a.2) := by
  funext a
  change scalarField δ (y+a.1,(θ : AddCircle period)+(a.2 : AddCircle period)) = _
  rw [← AddCircle.coe_add,scalarField_coe]

theorem scalarField_smooth (δ : ℝ) (hδ : 0 < δ) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (scalarField δ) x) := by
  rcases x with ⟨y,θ⟩
  obtain ⟨s,hs⟩ := QuotientAddGroup.mk_surjective θ
  rw [← hs,local_scalarField]
  exact (innerCutoff_contDiff.comp (contDiff_const.add contDiff_fst)).mul
    ((profile_contDiff δ hδ).comp (contDiff_const.add contDiff_snd))

theorem field_smooth {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (δ : ℝ) (hδ : 0 < δ) (ξ : U) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (field δ ξ) x) :=
  (scalarField_smooth δ hδ x).smul contDiff_const

/-- Support set, given by `tsupport innerCutoff ×ˢ Set.univ`. -/
def supportSet : Set (LiftDomain period) := tsupport innerCutoff ×ˢ Set.univ

theorem supportSet_compact : IsCompact supportSet :=
  innerCutoff_compactSupport.prod isCompact_univ

theorem field_zero_outside {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (δ : ℝ) (ξ : U) (x : LiftDomain period) (hx : x.1 ∉ tsupport innerCutoff) :
    field δ ξ x = 0 := by
  simp only [field,scalarField,image_eq_zero_of_notMem_tsupport hx,zero_mul,zero_smul]

theorem field_support {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (δ : ℝ) (ξ : U) : tsupport (field δ ξ) ⊆ supportSet := by
  apply closure_minimal _ supportSet_compact.isClosed
  intro x hx
  refine ⟨?_,Set.mem_univ _⟩
  by_contra hn
  exact hx (field_zero_outside δ ξ x hn)

theorem field_compact {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (δ : ℝ) (ξ : U) : HasCompactSupport (field δ ξ) :=
  supportSet_compact.of_isClosed_subset (isClosed_tsupport _) (field_support δ ξ)

/-- Compact field, bundling `field`, `compact`, `smooth`. -/
def compactField {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (δ : ℝ) (hδ : 0 < δ) (ξ : U) : CompactField period U where
  field := field δ ξ
  compact := field_compact δ ξ
  smooth := field_smooth δ hδ ξ

/-- Terminal, given by `(compactField δ hδ ξ).toLp`. -/
def terminal {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (δ : ℝ) (hδ : 0 < δ) (ξ : U) : CylinderL2 period U := (compactField δ hδ ξ).toLp

theorem terminal_ae {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (δ : ℝ) (hδ : 0 < δ) (ξ : U) : terminal δ hδ ξ =ᵐ[liftMeasure period] field δ ξ :=
  (compactField δ hδ ξ).toLp_ae

theorem terminal_orbit_contDiff {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (δ : ℝ) (hδ : 0 < δ) (ξ : U) :
    ContDiff ℝ ∞ (fun a : LiftTangent => translate period a (terminal δ hδ ξ)) :=
  (compactField δ hδ ξ).translation_contDiff

theorem field_odd {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (δ : ℝ) (ξ : U) (x : LiftDomain period) : field δ ξ (-x) = -field δ ξ x := by
  rcases x with ⟨y,θ⟩
  obtain ⟨s,hs⟩ := QuotientAddGroup.mk_surjective θ
  rw [← hs]
  change field δ ξ (-y,-(s : AddCircle period)) = -field δ ξ (y,(s : AddCircle period))
  rw [← AddCircle.coe_neg,field_coe,field_coe,innerCutoff_even,profile_odd,mul_neg,neg_smul]

theorem profile_integral_zero (δ : ℝ) :
    (∫ θ in (0 : ℝ)..period, profile δ θ) = 0 := by
  have h := (profile_periodic δ).intervalIntegral_add_eq 0 (-Real.pi)
  have he : -Real.pi + period = Real.pi := by ring
  simpa only [zero_add,he,profile_mean_zero] using h

theorem field_integral_zero {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    (δ : ℝ) (ξ : U) (y : Space) :
    (∫ θ in (0 : ℝ)..period, field δ ξ (y,(θ : AddCircle period))) = 0 := by
  simp only [field_coe,intervalIntegral.integral_smul_const,
    intervalIntegral.integral_const_mul,profile_integral_zero,mul_zero,zero_smul]

end EulerPacketTerminalDatum

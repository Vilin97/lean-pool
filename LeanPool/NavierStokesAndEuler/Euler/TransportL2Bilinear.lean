/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevTransportCommutator
public import LeanPool.NavierStokesAndEuler.Euler.SobolevMetricTransport

@[expose] public section

/-! Genuine transport as a bounded bilinear map from Sobolev velocity and an H¹ transported field
  into L². -/

noncomputable section

namespace EulerTransportL2Bilinear

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerMetricTransport EulerTransportDerivatives EulerSobolevL2Product EulerSobolevTransport
  EulerFunctionalVelocity EulerH6Nonlinear EulerSobolevMetricTransport
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual product of a bounded Sobolev velocity with the genuine first derivatives of an H¹ field. -/
def transportL2Bilinear {q : ℕ} (hq : 3 ≤ q) (L : Fin 4 → Vector3 →L[ℝ] ℝ) :
    SobolevSpace period q →L[ℝ] SobolevSpace period 1 →L[ℝ] LiftL2 period :=
  ∑ i : Fin 4, (scalarProductBilinear period hq (L i)).bilinearComp
    (ContinuousLinearMap.id ℝ (SobolevSpace period q)) ((valueOperator period 0).comp
      (derivativeOperator period 0 i))

/-- Transport is the sum of its four literal scalar-times-derivative L² products. -/
theorem transportL2Bilinear_apply {q : ℕ} (hq : 3 ≤ q) (L : Fin 4 → Vector3 →L[ℝ] ℝ)
    (u : SobolevSpace period q) (e : SobolevSpace period 1) :
    transportL2Bilinear period hq L u e = ∑ i : Fin 4,
      scalarProduct period hq (L i) u (value period (derivativeOperator period 0 i e)) := by
  simp only [transportL2Bilinear, sum_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, scalarProductBilinear_apply]
  rfl

/-- On the actual lifted velocity coefficients, this is exactly the operator used in metric transport cancellation. -/
theorem transportL2Bilinear_eq_metric {q : ℕ} (hq : 3 ≤ q) (κ : ℝ) (m : Vector3)
    (u : SobolevSpace period q) (e : SobolevSpace period 1) :
    transportL2Bilinear period hq (velocityComponents κ m) u e = transportOperator period hq κ m u
      e := by
  rw [transportL2Bilinear_apply, transportOperator_apply]

/-- The bilinear L² transport agrees almost everywhere with the actual classical directional transport. -/
theorem transportL2Bilinear_ae {q : ℕ} (hq : 3 ≤ q) (L : Fin 4 → Vector3 →L[ℝ] ℝ)
    (u : SobolevSpace period q) (e : SobolevSpace period 1) (f g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (he : (value period e : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    (transportL2Bilinear period hq L u e : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      transportField period 3 (velocityMap L ∘ f) g := by
  rw [transportL2Bilinear_apply]
  have hi (i : Fin 4) :
      (scalarProduct period hq (L i) u (value period (derivativeOperator period 0 i e)) :
        LiftDomain period → Vector3) =ᵐ[liftMeasure period]
        (fun x => L i (f x) • fieldDerivative period (standardDirection i) g x) := by
    have hd := EulerStrongSmoothJet.translation_derivative_ae period (standardDirection i)
      (value period e) (value period (derivativeOperator period 0 i e)) g he hg
      (derivativeOperator_hasDerivAt period i e)
    filter_upwards [scalarProduct_ae period hq (L i) u (value period (derivativeOperator period 0 i
      e)), hu, hd]
      with x hx hux hdx
    exact hx.trans (by rw [hux,hdx])
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin 4 =>
    scalarProduct period hq (L i) u (value period (derivativeOperator period 0 i e))),
      ae_all_iff.mpr hi]
    with x hx hall
  simp only [Finset.sum_apply] at hx
  change _ = ∑ i : Fin 4, L i (f x) • fieldDerivative period (standardDirection i) g x
  exact hx.trans (Finset.sum_congr rfl (fun i _ => hall i))

end EulerTransportL2Bilinear

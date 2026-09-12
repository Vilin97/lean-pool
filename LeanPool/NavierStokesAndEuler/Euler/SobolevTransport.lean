/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevProduct
import LeanPool.NavierStokesAndEuler.Euler.Foundations.StrongSmoothJet

/-! Actual one-derivative-losing nonlinear transport on the complete cylinder Sobolev spaces. -/

@[expose] public section


noncomputable section

namespace EulerSobolevTransport

open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
  EulerCylinderSobolevSpace EulerSobolevL2Product EulerMetricTransport EulerTransportDerivatives
open scoped Topology ContDiff ENNReal

variable (period : ℝ) [Fact (0 < period)]

/-- Cache the standard `NormedAddCommGroup (SobolevSpace period q)` instance to shorten
typeclass synthesis. -/
local instance sobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
/-- Cache the standard `NormedSpace ℝ (SobolevSpace period q)` instance to shorten typeclass
synthesis. -/
local instance sobolevRealSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The genuine transport bilinear map, with one actual coordinate derivative on its second input.
-/
def transportBilinear {q : ℕ} (hq : 6 ≤ q)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) :
    SobolevSpace period (q+1) →L[ℝ] SobolevSpace period (q+1) →L[ℝ] SobolevSpace period q :=
  ∑ i : Fin 4, (productHqBilinear period hq (L i) (hL i)).bilinearComp
    (truncateOperator period q) (derivativeOperator period q i)

/-- Transport is the finite sum of the actual Sobolev products and strong coordinate derivatives. -/
theorem transportBilinear_apply {q : ℕ} (hq : 6 ≤ q)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (q + 1)) :
    transportBilinear period hq L hL u v = ∑ i : Fin 4,
      productHq period hq (L i) (hL i) (truncateOperator period q u) (derivativeOperator period q i
          v) := by
  simp only [transportBilinear, sum_apply, ContinuousLinearMap.bilinearComp_apply,
    productHqBilinear_apply]

/-- The actual transport loses exactly one derivative, with an explicit fixed-order constant. -/
theorem transportBilinear_bound {q : ℕ} (hq : 6 ≤ q)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (q + 1)) :
    ‖transportBilinear period hq L hL u v‖ ≤ (4 * sobolevProductConstant period q) * ‖u‖ * ‖v‖ := by
  rw [transportBilinear_apply]
  have hi (i : Fin 4) : ‖productHq period hq (L i) (hL i)
      (truncateOperator period q u) (derivativeOperator period q i v)‖ ≤
      sobolevProductConstant period q * ‖u‖ * ‖v‖ :=
    (productHq_norm period hq (L i) (hL i) _ _).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (truncateOperator_bound period u)
        (sobolevProductConstant_nonneg period q)) (derivativeOperator_bound period i v)
        (norm_nonneg _) (mul_nonneg (sobolevProductConstant_nonneg period q) (norm_nonneg u)))
  have h := (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin
      4))) => hi i))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
    mul_assoc] using h

/-- The transport norm in the derivative-losing operator topology. -/
theorem transportBilinear_norm {q : ℕ} (hq : 6 ≤ q)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) :
    ‖transportBilinear period hq L hL‖ ≤ 4 * sobolevProductConstant period q := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by
      norm_num) (sobolevProductConstant_nonneg period q))
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg (by norm_num)
    (sobolevProductConstant_nonneg period q)) (norm_nonneg u))
  intro v
  exact transportBilinear_bound period hq L hL u v

/-- The genuine transport is represented by the literal sum of pointwise directional products. -/
theorem transportBilinear_value {q : ℕ} (hq : 6 ≤ q)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (q + 1)) :
    value period (transportBilinear period hq L hL u v) =
      ∑ i : Fin 4, scalarProduct period (by omega : 3 ≤ q) (L i)
        (truncateOperator period q u) (value period (derivativeOperator period q i v)) := by
  rw [transportBilinear_apply]
  change (valueOperator period q) (∑ i : Fin 4, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact productHq_value period hq (L i) (hL i) _ _

/-- On smooth representatives the nonlinear transport is exactly the classical cylinder differential
operator. -/
theorem transportBilinear_ae {q : ℕ} (hq : 6 ≤ q)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (q + 1)) (f g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hv : (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    (value period (transportBilinear period hq L hL u v) : LiftDomain period → Vector3)
        =ᵐ[liftMeasure period]
      (fun x => ∑ i : Fin 4, L i (f x) • fieldDerivative period (standardDirection i) g x) := by
  rw [transportBilinear_value]
  have hprod (i : Fin 4) :
      (scalarProduct period (by omega : 3 ≤ q) (L i) (truncateOperator period q u)
        (value period (derivativeOperator period q i v)) : LiftDomain period → Vector3)
            =ᵐ[liftMeasure period]
        (fun x => L i (f x) • fieldDerivative period (standardDirection i) g x) := by
    have hd := EulerStrongSmoothJet.translation_derivative_ae period (standardDirection i)
      (value period v) (value period (derivativeOperator period q i v)) g hv hg
      (derivativeOperator_hasDerivAt period i v)
    filter_upwards [scalarProduct_ae period (by omega : 3 ≤ q) (L i) (truncateOperator period q u)
      (value period (derivativeOperator period q i v)), hu, hd] with x h1 h2 h3
    exact h1.trans (by rw [value_truncateOperator, h2, h3])
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin 4 =>
    scalarProduct period (by omega : 3 ≤ q) (L i) (truncateOperator period q u)
      (value period (derivativeOperator period q i v))), ae_all_iff.mpr hprod] with x hx hall
  simp only [Finset.sum_apply] at hx
  exact hx.trans (Finset.sum_congr rfl (fun i _ => hall i))

end EulerSobolevTransport

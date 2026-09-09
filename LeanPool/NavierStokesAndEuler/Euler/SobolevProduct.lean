/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevProductApproximation

/-! Actual pointwise multiplication on the complete cylinder Sobolev spaces Hq, q≥6. -/

@[expose] public section


noncomputable section

namespace EulerSobolevL2Product

open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
  EulerCylinderSobolevSpace EulerSpatialSobolevInverse EulerMetricTransport
open scoped Topology ContDiff ENNReal

variable (period : ℝ) [Fact (0 < period)]

/-- The L² values of the genuine approximating products converge to the actual pointwise product. -/
theorem productApprox_value_tendsto {q : ℕ} (hq : 6 ≤ q)
    (L : Vector3 →L[ℝ] ℝ) (u v : SobolevSpace period q) :
    Filter.Tendsto (fun n => value period (productApprox period q n L u v)) Filter.atTop
      (𝓝 (scalarProduct period (by omega : 3 ≤ q) L u (value period v))) := by
  let U := fun n => restrictOperator period (by omega : q ≤ q+3) (smoothApprox period q n u)
  have hU : Filter.Tendsto U Filter.atTop (𝓝 u) := smoothApprox_tendsto period u
  have hV : Filter.Tendsto (fun n => value period (sobolevMollifier period q n v)) Filter.atTop (𝓝
      (value period v)) :=
    (valueOperator period q).continuous.tendsto v |>.comp (sobolevMollifier_tendsto period v)
  have h := (scalarProductBilinear period (by
      omega : 3 ≤ q) L).continuous₂.tendsto (u, value period v) |>.comp (hU.prodMk_nhds hV)
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro n
  change scalarProduct period (by
      omega : 3 ≤ q) L (U n) (value period (sobolevMollifier period q n v)) =
    value period (productApprox period q n L u v)
  rw [productApprox, productHighLow_value]
  exact scalarProduct_of_value_eq period (by omega : 3 ≤ q) (le_refl 3) L _ _ rfl _

/-- The actual pointwise product lies in Hq and satisfies the proved fixed-order algebra bound. -/
theorem exists_sobolev_product {q : ℕ} (hq : 6 ≤ q)
    (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (u v : SobolevSpace period q) :
    ∃ p : SobolevSpace period q,
      value period p = scalarProduct period (by omega : 3 ≤ q) L u (value period v) ∧
      ‖p‖ ≤ sobolevProductConstant period q * ‖u‖ * ‖v‖ := by
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete (productApprox_cauchy period hq L hL u v)
  refine ⟨p, ?_, ?_⟩
  · exact tendsto_nhds_unique ((valueOperator period q).continuous.tendsto p |>.comp hp)
      (productApprox_value_tendsto period hq L u v)
  · exact le_of_tendsto hp.norm (Filter.Eventually.of_forall (fun n => productApprox_bound period
      hq n L hL u v))

/-- The genuine product in the complete Sobolev space, uniquely determined by its L² value. -/
def productHq {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u v : SobolevSpace period q) : SobolevSpace period q :=
  Classical.choose (exists_sobolev_product period hq L hL u v)

@[simp] theorem productHq_value {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u v : SobolevSpace period q) :
    value period (productHq period hq L hL u v) = scalarProduct period (by
        omega : 3 ≤ q) L u (value period v) :=
  (Classical.choose_spec (exists_sobolev_product period hq L hL u v)).1

/-- The algebra bound for the genuine Sobolev product. -/
theorem productHq_norm {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u v : SobolevSpace period q) :
    ‖productHq period hq L hL u v‖ ≤ sobolevProductConstant period q * ‖u‖ * ‖v‖ :=
  (Classical.choose_spec (exists_sobolev_product period hq L hL u v)).2

/-- The product is exactly pointwise multiplication almost everywhere. -/
theorem productHq_ae {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u v : SobolevSpace period q) :
    (value period (productHq period hq L hL u v) : LiftDomain period → Vector3) =ᵐ[liftMeasure
        period]
      (fun x => L (value period u x) • value period v x) := by
  rw [productHq_value]
  exact scalarProduct_ae period (by omega : 3 ≤ q) L u (value period v)

theorem productHq_add_left {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u w v : SobolevSpace period q) :
    productHq period hq L hL (u+w) v = productHq period hq L hL u v + productHq period hq L hL w v
        := by
  apply value_injective period
  change value period (productHq period hq L hL (u+w) v) = value period (productHq period hq L hL u
      v) + value period (productHq period hq L hL w v)
  simp only [productHq_value, scalarProduct_add_left]

theorem productHq_smul_left {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (r : ℝ) (u v : SobolevSpace period q) :
    productHq period hq L hL (r • u) v = r • productHq period hq L hL u v := by
  apply value_injective period
  change value period (productHq period hq L hL (r • u) v) = r • value period (productHq period hq
      L hL u v)
  simp only [productHq_value, scalarProduct_smul_left]

theorem productHq_add_right {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u v w : SobolevSpace period q) :
    productHq period hq L hL u (v+w) = productHq period hq L hL u v + productHq period hq L hL u w
        := by
  apply value_injective period
  change value period (productHq period hq L hL u (v+w)) = value period (productHq period hq L hL u
      v) + value period (productHq period hq L hL u w)
  simp only [productHq_value]
  exact scalarProduct_add_right period (by omega : 3 ≤ q) L u (value period v) (value period w)

theorem productHq_smul_right {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u : SobolevSpace period q) (r : ℝ) (v : SobolevSpace period q) :
    productHq period hq L hL u (r • v) = r • productHq period hq L hL u v := by
  apply value_injective period
  change value period (productHq period hq L hL u (r • v)) = r • value period (productHq period hq
      L hL u v)
  simp only [productHq_value]
  exact scalarProduct_smul_right period (by omega : 3 ≤ q) L u r (value period v)

/-- Multiplication by a Sobolev scalar component, as an actual bounded Sobolev operator. -/
def productHqRight {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u : SobolevSpace period q) : SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  LinearMap.mkContinuous
    { toFun := productHq period hq L hL u
      map_add' := productHq_add_right period hq L hL u
      map_smul' := productHq_smul_right period hq L hL u }
    (sobolevProductConstant period q * ‖u‖) (productHq_norm period hq L hL u)

theorem productHqRight_norm {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u : SobolevSpace period q) : ‖productHqRight period hq L hL u‖ ≤ sobolevProductConstant period
        q * ‖u‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (sobolevProductConstant_nonneg period q)
      (norm_nonneg u))
    (productHq_norm period hq L hL u)

/-- The actual complete Sobolev algebra multiplication is a continuous bilinear map. -/
def productHqBilinear {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) :
    SobolevSpace period q →L[ℝ] SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  LinearMap.mkContinuous
    { toFun := productHqRight period hq L hL
      map_add' := by
        intro u w
        apply ContinuousLinearMap.ext
        intro v
        exact productHq_add_left period hq L hL u w v
      map_smul' := by
        intro r u
        apply ContinuousLinearMap.ext
        intro v
        exact productHq_smul_left period hq L hL r u v }
    (sobolevProductConstant period q) (productHqRight_norm period hq L hL)

@[simp] theorem productHqBilinear_apply {q : ℕ} (hq : 6 ≤ q)
    (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (u v : SobolevSpace period q) :
    productHqBilinear period hq L hL u v = productHq period hq L hL u v := rfl

end EulerSobolevL2Product

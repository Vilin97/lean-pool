/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevProductJet
public import LeanPool.NavierStokesAndEuler.Euler.GeneralRealCylinderAlgebra

@[expose] public section

/-! The genuine smooth product bound expressed in the complete cylinder Sobolev norm. -/

noncomputable section

namespace EulerSobolevL2Product

open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
  EulerCylinderSobolevSpace EulerSpatialSobolevInverse EulerStrongSmoothJet EulerVectorCylinder
  EulerMetricTransport EulerGeneralCylinderAlgebra
open scoped Topology ContDiff ENNReal

variable (period : ℝ) [Fact (0 < period)]

/-- The derivative sum of a complete Sobolev element agrees with its smooth representative. -/
theorem sumNorm_eq_classical {q : ℕ} (u : SobolevSpace period q)
    (f : LiftDomain period → Vector3)
    (hrep : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    sumNorm period u = liftSobolevNorm period q f := by
  rw [sumNorm_eq_jet]
  exact jet_sobolevNorm_eq period (value period u) (toJet period u) f hrep hf

/-- Actual pointwise multiplication has the same representative at every Sobolev order. -/
theorem scalarProduct_of_value_eq {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q)
    (L : Vector3 →L[ℝ] ℝ) (u : SobolevSpace period p) (w : SobolevSpace period q)
    (he : value period u = value period w) (v : LiftL2 period) :
    scalarProduct period hp L u v = scalarProduct period hq L w v := by
  apply Lp.ext
  filter_upwards [scalarProduct_ae period hp L u v, scalarProduct_ae period hq L w v] with x h1 h2
  rw [h1, h2, he]

/-- A fixed Sobolev-order algebra constant for the complete-array norm. -/
def sobolevProductConstant (q : ℕ) : ℝ :=
  (3 * algebraConstant period q) * (Fintype.card (SobolevWord q) : ℝ)^2

theorem sobolevProductConstant_nonneg (q : ℕ) : 0 ≤ sobolevProductConstant period q :=
  mul_nonneg (mul_nonneg (by norm_num) (algebraConstant_nonneg period q)) (sq_nonneg _)

/-- Exact smooth product representative of the actual strong product jet. -/
theorem productHighLow_representative {q : ℕ} (L : Vector3 →L[ℝ] ℝ)
    (u : SobolevSpace period (q+3)) (v : SobolevSpace period q)
    (f g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hv : (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g) :
    (value period (productHighLow period L u v) : LiftDomain period → Vector3) =ᵐ[liftMeasure
      period]
      (fun x => L (f x) • g x) := by
  rw [productHighLow_value]
  filter_upwards [scalarProduct_ae period (le_refl 3) L
    (restrictOperator period (by omega : 3 ≤ q+3) u) (value period v), hu, hv] with x h1 h2 h3
  exact h1.trans (by rw [value_restrictOperator, h2, h3])

/-- The actual product jet satisfies the low-order algebra bound whenever the inputs are smooth. -/
theorem productHighLow_bound_smooth {q : ℕ} (hq : 6 ≤ q)
    (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u : SobolevSpace period (q+3)) (v : SobolevSpace period q)
    (f g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hv : (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    ‖productHighLow period L u v‖ ≤ sobolevProductConstant period q *
      ‖restrictOperator period (by omega : q ≤ q+3) u‖ * ‖v‖ := by
  let U : SobolevSpace period q := restrictOperator period (by omega : q ≤ q+3) u
  have hU : (value period U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f := hu
  have hfL : ∀ j ≤ q, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2
    (liftMeasure period) :=
    fun j hj w => jet_classical_memLp period hj (value period U) (toJet period U) w f hU hf
  have hgL : ∀ j ≤ q, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w g) 2
    (liftMeasure period) :=
    fun j hj w => jet_classical_memLp period hj (value period v) (toJet period v) w g hv hg
  have hP := cylinder_Hq_scalar_vector_product period hq 3 (L ∘ f) g
    (postcomp_smooth period L f hf) hg (fun j hj w => postcomp_word_memLp period hj L f hf hfL w)
      hgL
  have hPs : ∀ x, ContDiff ℝ ∞ (localFieldLift period (fun x => L (f x) • g x) x) :=
    fun x => (postcomp_smooth period L f hf x).smul (hg x)
  have hpr := productHighLow_representative period L u v f g hu hv
  have hN := norm_le_sumNorm period (productHighLow period L u v)
  rw [sumNorm_eq_classical period _ _ hpr hPs] at hN
  have hLF := postcomp_sobolevNorm_le period q L hL f hf hfL
  have hFn : liftSobolevNorm period q f ≤ (Fintype.card (SobolevWord q) : ℝ) * ‖U‖ := by
    rw [← sumNorm_eq_classical period U f hU hf]
    exact sumNorm_le_card_norm period U
  have hGn : liftSobolevNorm period q g ≤ (Fintype.card (SobolevWord q) : ℝ) * ‖v‖ := by
    rw [← sumNorm_eq_classical period v g hv hg]
    exact sumNorm_le_card_norm period v
  have hpos : 0 ≤ 3 * algebraConstant period q := mul_nonneg (by norm_num) (algebraConstant_nonneg
    period q)
  calc
    ‖productHighLow period L u v‖ ≤ liftSobolevNorm period q (fun x => L (f x) • g x) := hN
    _ ≤ (3 * algebraConstant period q) * liftSobolevNorm period q (L ∘ f) * liftSobolevNorm period
      q g := hP
    _ ≤ (3 * algebraConstant period q) * liftSobolevNorm period q f * liftSobolevNorm period q g :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLF hpos) (liftSobolevNorm_nonneg
        period q g)
    _ ≤ (3 * algebraConstant period q) * ((Fintype.card (SobolevWord q) : ℝ) * ‖U‖) *
        ((Fintype.card (SobolevWord q) : ℝ) * ‖v‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hFn hpos) hGn (liftSobolevNorm_nonneg period q g)
        (mul_nonneg hpos (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg U)))
    _ = sobolevProductConstant period q * ‖U‖ * ‖v‖ := by unfold sobolevProductConstant; ring

/-- The high-low product is additive in its first argument. -/
theorem productHighLow_add_left {q : ℕ} (L : Vector3 →L[ℝ] ℝ)
    (u w : SobolevSpace period (q+3)) (v : SobolevSpace period q) :
    productHighLow period L (u+w) v = productHighLow period L u v + productHighLow period L w v :=
      by
  apply value_injective period
  change value period (productHighLow period L (u+w) v) = value period (productHighLow period L u
    v) + value period (productHighLow period L w v)
  simp only [productHighLow_value, map_add, scalarProduct_add_left]

/-- The high-low product is additive in its second argument. -/
theorem productHighLow_add_right {q : ℕ} (L : Vector3 →L[ℝ] ℝ)
    (u : SobolevSpace period (q+3)) (v w : SobolevSpace period q) :
    productHighLow period L u (v+w) = productHighLow period L u v + productHighLow period L u w :=
      by
  apply value_injective period
  change value period (productHighLow period L u (v+w)) = value period (productHighLow period L u
    v) + value period (productHighLow period L u w)
  simp only [productHighLow_value]
  exact scalarProduct_add_right period (le_refl 3) L _ _ _

/-- Exact product difference decomposition. -/
theorem productHighLow_sub {q : ℕ} (L : Vector3 →L[ℝ] ℝ)
    (u w : SobolevSpace period (q+3)) (v z : SobolevSpace period q) :
    productHighLow period L u v - productHighLow period L w z =
      productHighLow period L (u-w) v + productHighLow period L w (v-z) := by
  apply value_injective period
  change value period (productHighLow period L u v) - value period (productHighLow period L w z) =
    value period (productHighLow period L (u-w) v) + value period (productHighLow period L w (v-z))
  simp only [productHighLow_value, map_sub]
  rw [show value period (v-z) = value period v - value period z from map_sub (valueOperator period
    q) v z]
  change scalarProductBilinear period (le_refl 3) L _ _ - scalarProductBilinear period (le_refl 3)
    L _ _ =
    scalarProductBilinear period (le_refl 3) L _ _ + scalarProductBilinear period (le_refl 3) L _ _
  simp only [map_sub, sub_apply]
  abel

end EulerSobolevL2Product

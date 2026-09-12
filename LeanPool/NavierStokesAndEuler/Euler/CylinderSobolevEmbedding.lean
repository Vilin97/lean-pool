/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevSpace
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.MollifierRepresentative
import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevDensity
import LeanPool.NavierStokesAndEuler.Euler.Foundations.StrongSmoothJet
import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCylinder

/-! Genuine L∞ control of finite-order cylinder Sobolev fields, obtained by smooth density. -/

@[expose] public section


noncomputable section

namespace EulerCylinderSobolevSpace

open MeasureTheory EulerLiftedGradientSpace EulerMetricTransport EulerSpatialSobolevInverse
  EulerCylinderSobolev EulerCylinderMollifier EulerMollifierRepresentative EulerStrongSmoothJet
  EulerVectorCylinder
open scoped Topology ContDiff ENNReal

variable (period : ℝ) [Fact (0 < period)]

/-- A fixed-order embedding constant for the complete finite-array Sobolev norm. -/
def sobolevEmbeddingConstant (q : ℕ) : ℝ :=
  (3 * cylinderEmbeddingConstant period) * (Fintype.card (SobolevWord q) : ℝ)

theorem sobolevEmbeddingConstant_nonneg (q : ℕ) : 0 ≤ sobolevEmbeddingConstant period q :=
  mul_nonneg (mul_nonneg (by
      norm_num) (cylinderEmbeddingConstant_nonneg period)) (Nat.cast_nonneg _)

/-- Every actual smooth mollification has the same uniform pointwise Sobolev bound. -/
theorem mollifier_pointwise_bound {q : ℕ} (hq : 3 ≤ q) (n : ℕ) (u : SobolevSpace period q)
    (x : LiftDomain period) :
    ‖smoothMollifier period n (value period u) x‖ ≤ sobolevEmbeddingConstant period q * ‖u‖ := by
  let un := sobolevMollifier period q n u
  let f := smoothMollifier period n (value period u)
  have hf := smoothMollifier_smooth period n (value period u)
  have hrep : (value period un : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f :=
    sobolevMollifier_representative period n u
  have hL2 : ∀ j ≤ 3, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period) :=
    fun j hj w => jet_classical_memLp period (by
        omega) (value period un) (toJet period un) w f hrep hf
  have hnorm : liftSobolevNorm period q f = sumNorm period un := by
    rw [sumNorm_eq_jet]
    exact (jet_sobolevNorm_eq period (value period un) (toJet period un) f hrep hf).symm
  calc
    _ ≤ (3 * cylinderEmbeddingConstant period) * liftSobolevNorm period 3 f := by
      simpa only [Nat.cast_ofNat] using vector_cylinder_pointwise_le_H3 period 3 f hf hL2 x
    _ ≤ (3 * cylinderEmbeddingConstant period) * liftSobolevNorm period q f :=
      mul_le_mul_of_nonneg_left (liftSobolevNorm_mono period hq f)
        (mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period))
    _ = (3 * cylinderEmbeddingConstant period) * sumNorm period un := by rw [hnorm]
    _ ≤ (3 * cylinderEmbeddingConstant period) * ((Fintype.card (SobolevWord q) : ℝ) * ‖un‖) :=
      mul_le_mul_of_nonneg_left (sumNorm_le_card_norm period un)
        (mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period))
    _ ≤ (3 * cylinderEmbeddingConstant period) * ((Fintype.card (SobolevWord q) : ℝ) * ‖u‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sobolevMollifier_bound period n u)
          (Nat.cast_nonneg _))
        (mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period))
    _ = _ := (mul_assoc ..).symm

/-- Every actual Hq field, q≥3, has an almost-everywhere bounded L² representative. -/
theorem value_ae_bound {q : ℕ} (hq : 3 ≤ q) (u : SobolevSpace period q) :
    ∀ᵐ x ∂liftMeasure period, ‖value period u x‖ ≤ sobolevEmbeddingConstant period q * ‖u‖ := by
  obtain ⟨ns, _hns, hlim⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (mollify_tendsto period (value period
        u))).exists_seq_tendsto_ae'
  have hreps : ∀ᵐ x ∂liftMeasure period, ∀ n : ℕ,
      mollify period (ns n) (value period u) x = smoothMollifier period (ns n) (value period u) x :=
    ae_all_iff.mpr (fun n => mollify_ae_smoothMollifier period (ns n) (value period u))
  filter_upwards [hlim, hreps] with x hx hrep
  apply le_of_tendsto hx.norm
  exact Filter.Eventually.of_forall (fun n => by
    rw [hrep n]
    exact mollifier_pointwise_bound period hq (ns n) u x)

end EulerCylinderSobolevSpace

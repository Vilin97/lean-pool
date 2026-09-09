/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevSmoothProduct
public import LeanPool.NavierStokesAndEuler.Euler.SobolevSmoothApproximation

@[expose] public section

/-! Cauchy convergence of actual smooth cylinder products in the complete Sobolev space. -/

noncomputable section

namespace EulerSobolevL2Product

open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
  EulerCylinderSobolevSpace EulerSpatialSobolevInverse EulerStrongSmoothJet EulerVectorCylinder
  EulerMetricTransport EulerCylinderMollifier EulerMollifierRepresentative
open scoped Topology ContDiff ENNReal

variable (period : ℝ) [Fact (0 < period)]

/-- Differences of actual smooth representatives remain actual smooth representatives. -/
theorem smooth_representative_sub {q : ℕ} (u v : SobolevSpace period q)
    (hu : ∃ f : LiftDomain period → Vector3,
      (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hv : ∃ g : LiftDomain period → Vector3,
      (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    ∃ f : LiftDomain period → Vector3,
      (value period (u-v) : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period f x) := by
  obtain ⟨f, hfu, hf⟩ := hu
  obtain ⟨g, hgv, hg⟩ := hv
  refine ⟨f-g, ?_, fun x => (hf x).sub (hg x)⟩
  filter_upwards [Lp.coeFn_sub (value period u) (value period v), hfu, hgv] with x h1 h2 h3
  exact h1.trans (by simp only [Pi.sub_apply, h2, h3])

/-- The smooth product bound only needs the existence of the actual smooth representatives. -/
theorem productHighLow_bound_of_smooth {q : ℕ} (hq : 6 ≤ q)
    (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u : SobolevSpace period (q+3)) (v : SobolevSpace period q)
    (hu : ∃ f : LiftDomain period → Vector3,
      (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hv : ∃ g : LiftDomain period → Vector3,
      (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    ‖productHighLow period L u v‖ ≤ sobolevProductConstant period q *
      ‖restrictOperator period (by omega : q ≤ q+3) u‖ * ‖v‖ := by
  obtain ⟨f, hfu, hf⟩ := hu
  obtain ⟨g, hgv, hg⟩ := hv
  exact productHighLow_bound_smooth period hq L hL u v f g hfu hgv hf hg

/-- The genuine product difference is controlled solely in the original Sobolev topology. -/
theorem productHighLow_dist_of_smooth {q : ℕ} (hq : 6 ≤ q)
    (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u w : SobolevSpace period (q+3)) (v z : SobolevSpace period q)
    (hu : ∃ f : LiftDomain period → Vector3, (value period u : LiftDomain period → Vector3)
      =ᵐ[liftMeasure period] f ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hw : ∃ f : LiftDomain period → Vector3, (value period w : LiftDomain period → Vector3)
      =ᵐ[liftMeasure period] f ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hv : ∃ f : LiftDomain period → Vector3, (value period v : LiftDomain period → Vector3)
      =ᵐ[liftMeasure period] f ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hz : ∃ f : LiftDomain period → Vector3, (value period z : LiftDomain period → Vector3)
      =ᵐ[liftMeasure period] f ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    dist (productHighLow period L u v) (productHighLow period L w z) ≤
      sobolevProductConstant period q * dist (restrictOperator period (by omega : q ≤ q+3) u)
        (restrictOperator period (by omega : q ≤ q+3) w) * ‖v‖ +
      sobolevProductConstant period q * ‖restrictOperator period (by omega : q ≤ q+3) w‖ * dist v z
        := by
  rw [dist_eq_norm, productHighLow_sub]
  have h1 := productHighLow_bound_of_smooth period hq L hL (u-w) v
    (smooth_representative_sub period u w hu hw) hv
  have h2 := productHighLow_bound_of_smooth period hq L hL w (v-z) hw
    (smooth_representative_sub period v z hv hz)
  simpa only [map_sub, ← dist_eq_norm] using (norm_add_le _ _).trans (add_le_add h1 h2)

/-- A quantitative difference estimate transfers Cauchy convergence through a bilinear operation. -/
theorem cauchySeq_of_product_control {X Y Z : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [PseudoMetricSpace Z] (u : ℕ → X) (v : ℕ → Y) (p : ℕ → Z) (A B : ℝ)
    (hu : CauchySeq u) (hv : CauchySeq v)
    (h : ∀ n m, dist (p n) (p m) ≤ A * dist (u n) (u m) + B * dist (v n) (v m)) :
    CauchySeq p := by
  rw [cauchySeq_iff_tendsto_dist_atTop_0] at hu hv ⊢
  apply squeeze_zero (fun nm : ℕ × ℕ => (dist_nonneg : 0 ≤ dist (p nm.1) (p nm.2))) (fun nm => h
    nm.1 nm.2)
  simpa only [mul_zero, add_zero] using (hu.const_mul A).add (hv.const_mul B)

/-- Smooth products of the concrete approximations. -/
def productApprox (q n : ℕ) (L : Vector3 →L[ℝ] ℝ) (u v : SobolevSpace period q) : SobolevSpace
  period q :=
  productHighLow period L (smoothApprox period q n u) (sobolevMollifier period q n v)

/-- The actual product approximations satisfy a bound independent of the smoothing scale. -/
theorem productApprox_bound {q : ℕ} (hq : 6 ≤ q) (n : ℕ)
    (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (u v : SobolevSpace period q) :
    ‖productApprox period q n L u v‖ ≤ sobolevProductConstant period q * ‖u‖ * ‖v‖ := by
  have hv : ∃ g : LiftDomain period → Vector3,
      (value period (sobolevMollifier period q n v) : LiftDomain period → Vector3) =ᵐ[liftMeasure
        period] g ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period g x) := ⟨smoothMollifier period n (value period v),
        sobolevMollifier_representative period n v,
    smoothMollifier_smooth period n (value period v)⟩
  have h := productHighLow_bound_of_smooth period hq L hL _ _ (smoothApprox_representative period n
    u) hv
  exact h.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (smoothApprox_bound period n u) (sobolevProductConstant_nonneg
      period q))
    (sobolevMollifier_bound period n v) (norm_nonneg _) (mul_nonneg (sobolevProductConstant_nonneg
      period q) (norm_nonneg u)))

/-- Actual smooth products converge in the complete Hq topology. -/
theorem productApprox_cauchy {q : ℕ} (hq : 6 ≤ q)
    (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (u v : SobolevSpace period q) :
    CauchySeq (fun n => productApprox period q n L u v) := by
  let U := fun n => restrictOperator period (by omega : q ≤ q+3) (smoothApprox period q n u)
  let V := fun n => sobolevMollifier period q n v
  have hU : CauchySeq U := (smoothApprox_tendsto period u).cauchySeq
  have hV : CauchySeq V := (sobolevMollifier_tendsto period v).cauchySeq
  apply cauchySeq_of_product_control U V _ (sobolevProductConstant period q * ‖v‖)
    (sobolevProductConstant period q * ‖u‖) hU hV
  intro n m
  have hsm (k : ℕ) : ∃ g : LiftDomain period → Vector3,
      (value period (sobolevMollifier period q k v) : LiftDomain period → Vector3) =ᵐ[liftMeasure
        period] g ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period g x) := ⟨smoothMollifier period k (value period v),
        sobolevMollifier_representative period k v,
    smoothMollifier_smooth period k (value period v)⟩
  have h := productHighLow_dist_of_smooth period hq L hL _ _ _ _
    (smoothApprox_representative period n u) (smoothApprox_representative period m u) (hsm n) (hsm
      m)
  have h1 := mul_le_mul_of_nonneg_left (sobolevMollifier_bound period n v)
    (mul_nonneg (sobolevProductConstant_nonneg period q) (dist_nonneg : 0 ≤ dist (U n) (U m)))
  have h2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (smoothApprox_bound period m u) (sobolevProductConstant_nonneg
      period q))
    (dist_nonneg : 0 ≤ dist (V n) (V m))
  exact h.trans ((add_le_add h1 h2).trans_eq (by dsimp [U, V]; ring))

end EulerSobolevL2Product

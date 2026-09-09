/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.TransportDerivatives
import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedCurl
import LeanPool.NavierStokesAndEuler.Euler.Foundations.NoncompactTransport
import Mathlib.Algebra.Order.Star.Real

/-! Classical lifted closedness of actual smooth representatives of the closed L² gradient space. -/

@[expose] public section


noncomputable section

namespace EulerClassicalPressureCurl

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerLiftedWeakDerivative EulerNoncompactTransport EulerLiftedCurl
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Product cylinder volume assigns positive measure to every nonempty open set. -/
instance liftMeasure_openPos : MeasureTheory.Measure.IsOpenPosMeasure (liftMeasure period) := by
  unfold liftMeasure
  infer_instance

omit [Fact (0 < period)] in
/-- The scalar directional product rule in the genuine cylinder covering coordinates. -/
theorem fieldDerivative_mul (a : LiftTangent) (f g : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) (x : LiftDomain period) :
    fieldDerivative period a (fun y => f y * g y) x =
      fieldDerivative period a f x * g x + f x * fieldDerivative period a g x := by
  have h := ((((hf x).differentiable (by simp)) 0).hasFDerivAt.mul
    (((hg x).differentiable (by simp)) 0).hasFDerivAt).fderiv
  have he := congrArg (fun L : LiftTangent →L[ℝ] ℝ => L a) h
  simpa +unfoldPartialApp [fieldDerivative, localFieldLift, Pi.mul_def, mul_comm, add_comm] using he

/-- A smooth scalar field times a compact smooth scalar field is integrable. -/
theorem scalar_product_integrable (f g : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hgc : HasCompactSupport g) :
    Integrable (fun x => f x * g x) (liftMeasure period) :=
  ((smoothField_continuous period f hf).mul (smoothField_continuous period g
      hg)).integrable_of_hasCompactSupport hgc.mul_left

/-- Scalar integration by parts with only the test factor compactly supported. -/
theorem scalar_integration_by_parts_test (a : LiftTangent) (f ψ : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x))
    (hψc : HasCompactSupport ψ) :
    (∫ x, fieldDerivative period a f x * ψ x ∂liftMeasure period) =
      -(∫ x, f x * fieldDerivative period a ψ x ∂liftMeasure period) := by
  let Df := fieldDerivative period a f
  let Dψ := fieldDerivative period a ψ
  let F := fun n x => fieldDerivative period a (fun y => spatialCutoff period n y * f y) x * ψ x
  let G := fun n x => spatialCutoff period n x * (f x * Dψ x)
  have hDf := fieldDerivative_smooth period a f hf
  have hDψ := fieldDerivative_smooth period a ψ hψ
  have hI := scalar_product_integrable period Df ψ hDf hψ hψc
  have hJ := scalar_product_integrable period f ψ hf hψ hψc
  have hR := scalar_product_integrable period f Dψ hf hDψ (fieldDerivative_compact period a ψ hψc)
  have hs (n : ℕ) (x : LiftDomain period) :
      ContDiff ℝ ∞ (localFieldLift period (fun y => spatialCutoff period n y * f y) x) :=
    (spatialCutoff_smooth period n x).mul (hf x)
  have hFG (n : ℕ) : (∫ x, F n x ∂liftMeasure period) = -(∫ x, G n x ∂liftMeasure period) := by
    have h := scalar_integration_by_parts period a
      (fun y => spatialCutoff period n y * f y) ψ
      (spatialCutoff_compact period n).mul_right hψc (hs n) hψ
    simpa only [F, G, Dψ, mul_assoc] using h
  obtain ⟨M, hM, hMb⟩ := spatialCutoff_derivative_bound period
  have hDc (n : ℕ) (x : LiftDomain period) :
      ‖fieldDerivative period a (spatialCutoff period n) x‖ ≤ M * ‖a‖ := by
    calc
      _ ≤ M * cutoffScale n * ‖a‖ := hMb n x a
      _ ≤ M * 1 * ‖a‖ := by gcongr; exact cutoffScale_le_one n
      _ = _ := by ring
  have hFm (n : ℕ) : AEStronglyMeasurable (F n) (liftMeasure period) :=
    ((smoothField_continuous period _ (fieldDerivative_smooth period a _ (hs n))).mul
      (smoothField_continuous period ψ hψ)).aestronglyMeasurable
  have hFb (n : ℕ) : ∀ᵐ x ∂liftMeasure period,
      ‖F n x‖ ≤ ‖Df x * ψ x‖ + (M * ‖a‖) * ‖f x * ψ x‖ := by
    apply Filter.Eventually.of_forall
    intro x
    have hc := spatialCutoff_bounds period n x
    have hcn : ‖spatialCutoff period n x‖ ≤ 1 := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hc.1] using hc.2
    have he : F n x = fieldDerivative period a (spatialCutoff period n) x * (f x * ψ x) +
        spatialCutoff period n x * (Df x * ψ x) := by
      dsimp [F, Df]
      rw [fieldDerivative_mul period a _ f (spatialCutoff_smooth period n) hf]
      ring
    rw [he]
    calc
      _ ≤ ‖fieldDerivative period a (spatialCutoff period n) x‖ * ‖f x * ψ x‖ +
          ‖spatialCutoff period n x‖ * ‖Df x * ψ x‖ := by
        simpa only [norm_mul] using norm_add_le
          (fieldDerivative period a (spatialCutoff period n) x * (f x * ψ x))
          (spatialCutoff period n x * (Df x * ψ x))
      _ ≤ (M * ‖a‖) * ‖f x * ψ x‖ + 1 * ‖Df x * ψ x‖ := by gcongr; exact hDc n x
      _ = _ := by ring
  have hFl : ∀ᵐ x ∂liftMeasure period, Filter.Tendsto (fun n => F n x) Filter.atTop (𝓝 (Df x * ψ
      x)) := by
    apply Filter.Eventually.of_forall
    intro x
    have hdc : Filter.Tendsto (fun n => fieldDerivative period a (spatialCutoff period n) x)
        Filter.atTop (𝓝 0) := spatialCutoff_derivative_tendsto period x a
    simp_rw [F, fieldDerivative_mul period a _ f (spatialCutoff_smooth period _) hf]
    simpa only [zero_mul, one_mul, zero_add] using ((hdc.mul_const (f x)).add
      ((spatialCutoff_tendsto period x).mul_const (Df x))).mul_const (ψ x)
  have hFt := tendsto_integral_of_dominated_convergence
    (fun x => ‖Df x * ψ x‖ + (M * ‖a‖) * ‖f x * ψ x‖)
    hFm (hI.norm.add (hJ.norm.const_mul (M * ‖a‖))) hFb hFl
  have hGm (n : ℕ) : AEStronglyMeasurable (G n) (liftMeasure period) :=
    ((smoothField_continuous period _ (spatialCutoff_smooth period n)).mul
      ((smoothField_continuous period f hf).mul (smoothField_continuous period Dψ
          hDψ))).aestronglyMeasurable
  have hGb (n : ℕ) : ∀ᵐ x ∂liftMeasure period, ‖G n x‖ ≤ ‖f x * Dψ x‖ := by
    apply Filter.Eventually.of_forall
    intro x
    have hc := spatialCutoff_bounds period n x
    have hcn : ‖spatialCutoff period n x‖ ≤ 1 := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hc.1] using hc.2
    change ‖spatialCutoff period n x * (f x * Dψ x)‖ ≤ ‖f x * Dψ x‖
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcn (norm_nonneg (f x * Dψ x))
  have hGl : ∀ᵐ x ∂liftMeasure period, Filter.Tendsto (fun n => G n x) Filter.atTop (𝓝 (f x * Dψ
      x)) :=
    Filter.Eventually.of_forall (fun x => by
      simpa only [G, one_mul] using (spatialCutoff_tendsto period x).mul_const (f x * Dψ x))
  have hGt := tendsto_integral_of_dominated_convergence (fun x => ‖f x * Dψ x‖)
    hGm hR.norm hGb hGl
  have hseq : (fun n => ∫ x, F n x ∂liftMeasure period) = fun n => -(∫ x, G n x ∂liftMeasure
      period) := funext hFG
  rw [hseq] at hFt
  exact tendsto_nhds_unique hFt hGt.neg

/-- A smooth scalar cylinder field annihilating every compact smooth test is pointwise zero. -/
theorem smooth_eq_zero_of_compact_test_integrals (q : LiftDomain period → ℝ)
    (hq : ∀ x, ContDiff ℝ ∞ (localFieldLift period q x))
    (htest : ∀ ψ : LiftDomain period → ℝ, HasCompactSupport ψ →
      (∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x)) →
      (∫ x, q x * ψ x ∂liftMeasure period) = 0) :
    ∀ x, q x = 0 := by
  have hzero (n : ℕ) (x : LiftDomain period) : spatialCutoff period n x * (q x) ^ 2 = 0 := by
    have hcont : Continuous (fun y => spatialCutoff period n y * (q y) ^ 2) :=
      (smoothField_continuous period _ (spatialCutoff_smooth period n)).mul
        ((smoothField_continuous period q hq).pow 2)
    have hcomp : HasCompactSupport (fun y => spatialCutoff period n y * (q y) ^ 2) :=
      (spatialCutoff_compact period n).mul_right
    have hInt : (∫ y, spatialCutoff period n y * (q y) ^ 2 ∂liftMeasure period) = 0 := by
      have hh := htest (fun y => spatialCutoff period n y * q y)
        (spatialCutoff_compact period n).mul_right
        (fun y => (spatialCutoff_smooth period n y).mul (hq y))
      rw [← hh]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by ring)
    have hAE : (fun y => spatialCutoff period n y * (q y) ^ 2) =ᵐ[liftMeasure period] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun y => mul_nonneg (spatialCutoff_bounds period n y).1 (sq_nonneg (q y)))
        (hcont.integrable_of_hasCompactSupport hcomp)).mp hInt
    exact congrFun (MeasureTheory.Measure.eq_of_ae_eq hAE hcont continuous_const) x
  intro x
  have ht := (spatialCutoff_tendsto period x).mul_const ((q x) ^ 2)
  have hseq : (fun n => spatialCutoff period n x * (q x) ^ 2) = fun _ : ℕ => 0 :=
    funext (fun n => hzero n x)
  rw [hseq] at ht
  have hh : (q x) ^ 2 = 0 := by
    simpa only [one_mul] using tendsto_nhds_unique ht tendsto_const_nhds
  exact sq_eq_zero_iff.mp hh

/-- Every smooth representative of an element of the closed lifted gradient space is classically
closed. -/
theorem gradientSpace_classical_curl_zero (κ : ℝ) (m : Vector3)
    (p : LiftL2 period) (hp : p ∈ gradientSpace period κ m)
    (g : LiftDomain period → Vector3)
    (hrep : (p : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    ∀ x i j, (fieldDerivative period (coordinateDirection κ m i) g x) j =
      (fieldDerivative period (coordinateDirection κ m j) g x) i := by
  intro x i j
  let φ : LiftDomain period → ℝ := fun y => g y i
  let χ : LiftDomain period → ℝ := fun y => g y j
  let a := coordinateDirection κ m j
  let b := coordinateDirection κ m i
  have hφ : ∀ y, ContDiff ℝ ∞ (localFieldLift period φ y) :=
    fun y => (EuclideanSpace.proj i : Vector3 →L[ℝ] ℝ).contDiff.comp (hg y)
  have hχ : ∀ y, ContDiff ℝ ∞ (localFieldLift period χ y) :=
    fun y => (EuclideanSpace.proj j : Vector3 →L[ℝ] ℝ).contDiff.comp (hg y)
  let q := fun y => fieldDerivative period a φ y - fieldDerivative period b χ y
  have hqa := fieldDerivative_smooth period a φ hφ
  have hqb := fieldDerivative_smooth period b χ hχ
  have hq : ∀ y, ContDiff ℝ ∞ (localFieldLift period q y) := fun y => (hqa y).sub (hqb y)
  have hzero := smooth_eq_zero_of_compact_test_integrals period q hq (fun ψ hψc hψ => by
    have hw := gradientSpace_weak_curl_zero period κ m hp i j ψ hψc hψ
    have hw' : (∫ y, φ y * fieldDerivative period a ψ y - χ y * fieldDerivative period b ψ y
        ∂liftMeasure period) = 0 := by
      rw [← hw]
      apply integral_congr_ae
      filter_upwards [hrep] with y hy
      rw [hy]
    have hDaψ := fieldDerivative_smooth period a ψ hψ
    have hDbψ := fieldDerivative_smooth period b ψ hψ
    have hIa := scalar_product_integrable period φ (fieldDerivative period a ψ) hφ hDaψ
      (fieldDerivative_compact period a ψ hψc)
    have hIb := scalar_product_integrable period χ (fieldDerivative period b ψ) hχ hDbψ
      (fieldDerivative_compact period b ψ hψc)
    rw [integral_sub hIa hIb] at hw'
    have ha := scalar_integration_by_parts_test period a φ ψ hφ hψ hψc
    have hb := scalar_integration_by_parts_test period b χ ψ hχ hψ hψc
    have hJa := scalar_product_integrable period (fieldDerivative period a φ) ψ hqa hψ hψc
    have hJb := scalar_product_integrable period (fieldDerivative period b χ) ψ hqb hψ hψc
    change (∫ y, (fieldDerivative period a φ y - fieldDerivative period b χ y) * ψ y
      ∂liftMeasure period) = 0
    simp_rw [sub_mul]
    rw [integral_sub hJa hJb]
    linarith)
  have ha : fieldDerivative period a φ x = (fieldDerivative period a g x) i :=
    fieldDerivative_linear period (EuclideanSpace.proj i) g hg a x
  have hb : fieldDerivative period b χ x = (fieldDerivative period b g x) j :=
    fieldDerivative_linear period (EuclideanSpace.proj j) g hg b x
  have hz := hzero x
  change fieldDerivative period a φ x - fieldDerivative period b χ x = 0 at hz
  rw [ha, hb] at hz
  exact (sub_eq_zero.mp hz).symm

end EulerClassicalPressureCurl

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.UnshiftedPressure
public import LeanPool.NavierStokesAndEuler.Euler.LowerTransportSource

@[expose] public section

/-! Actual unshifted Gevrey product and lower-pressure estimates with constants independent of
  truncation. -/

noncomputable section

namespace EulerWeightedConvolution

open Finset EulerPacketWeights EulerJetProductBounds

/-- The ordinary Gevrey-two product weight is submultiplicative after paying the binomial coefficient. -/
theorem unshifted_product_term (ρ : ℝ) (hρ : 0 < ρ) (j l : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    weight ρ (j+l) * ((j+l).choose l : ℝ) * a*b ≤ (weight ρ l*a)*(weight ρ j*b) := by
  have he : weight ρ (j+l) * ((j+l).choose l : ℝ) * a*b =
      ((weight ρ l*a)*(weight ρ j*b))/((j+l).choose l : ℝ) := by
    rw [Nat.cast_choose ℝ (Nat.le_add_left l j)]
    simp only [Nat.add_sub_cancel_right]
    unfold weight
    rw [pow_add]
    field_simp [factorial_cast_ne_zero]
  have hc : (1 : ℝ) ≤ ((j+l).choose l : ℝ) := by exact_mod_cast Nat.choose_pos (Nat.le_add_left l j)
  rw [he]
  exact div_le_self (mul_nonneg (mul_nonneg (weight_pos hρ l).le ha) (mul_nonneg (weight_pos hρ
    j).le hb)) hc

/-- The actual binomial product convolution is bounded in unshifted Gevrey sums with constant one. -/
theorem unshifted_product_sum (ρ : ℝ) (hρ : 0 < ρ) (N : ℕ) (A B : ℕ → ℝ)
    (hA : ∀ n, 0 ≤ A n) (hB : ∀ n, 0 ≤ B n) :
    (∑ n ∈ range (N+1), weight ρ n * leibnizConvolution A B n) ≤
      (∑ l ∈ range (N+1), weight ρ l*A l)*(∑ j ∈ range (N+1), weight ρ j*B j) := by
  calc
    _ = ∑ n ∈ range (N+1), ∑ l ∈ range (n+1), weight ρ n*(n.choose l : ℝ)*A l*B (n-l) := by
      simp only [leibnizConvolution, mul_sum, mul_assoc]
    _ ≤ ∑ n ∈ range (N+1), ∑ l ∈ range (n+1), (weight ρ l*A l)*(weight ρ (n-l)*B (n-l)) := by
      apply sum_le_sum
      intro n _
      apply sum_le_sum
      intro l hl
      have he : n-l+l = n := by have := mem_range.mp hl; omega
      simpa only [he] using unshifted_product_term ρ hρ (n-l) l (A l) (B (n-l)) (hA l) (hB (n-l))
    _ ≤ _ := EulerH6Pressure.triangle_sum_le_product N _ _
      (fun l => mul_nonneg (weight_pos hρ l).le (hA l)) (fun j => mul_nonneg (weight_pos hρ j).le
        (hB j))

end EulerWeightedConvolution

namespace EulerH6Nonlinear

open MeasureTheory InnerProductSpace EulerSobolev EulerCylinderSobolev EulerLiftedGradientSpace
  EulerMetricTransport
  EulerSpatialSobolevInverse EulerJetProductBounds EulerPacketWeights EulerH6Pressure
    EulerWeightedConvolution
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual scalar-vector product is bounded in every finite unshifted H⁶ Gevrey sum. -/
theorem product_unshifted_weighted_bound (d N : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (f : LiftDomain period → ℝ) (g : LiftDomain period → Domain d)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure
      period))
    (hgL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure
      period)) :
    (∑ n ∈ Finset.range (N+1), weight ρ n * wordSobolevNorm period 6 n (fun x => f x • g x)) ≤
      productConstant period d * (∑ l ∈ Finset.range (N+1), weight ρ l*wordSobolevNorm period 6 l
        f)*
        (∑ j ∈ Finset.range (N+1), weight ρ j*wordSobolevNorm period 6 j g) := by
  have h := Finset.sum_le_sum (s := Finset.range (N+1)) (fun n _ => mul_le_mul_of_nonneg_left
    (product_wordSobolevNorm_bound period d n f g hf hg hfL hgL) (weight_pos hρ n).le)
  have he : (∑ n ∈ Finset.range (N+1), weight ρ n*(productConstant period d*leibnizConvolution
      (fun l => wordSobolevNorm period 6 l f) (fun l => wordSobolevNorm period 6 l g) n)) =
      productConstant period d * ∑ n ∈ Finset.range (N+1), weight ρ n*leibnizConvolution
        (fun l => wordSobolevNorm period 6 l f) (fun l => wordSobolevNorm period 6 l g) n := by
    simp only [Finset.mul_sum, mul_left_comm]
  rw [he] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (unshifted_product_sum ρ hρ N _ _
    (fun l => wordSobolevNorm_nonneg period 6 l f) (fun l => wordSobolevNorm_nonneg period 6 l g))
    (productConstant_nonneg period d)).trans_eq (mul_assoc _ _ _).symm)

/-- The actual transport source in H⁵ is bounded by H⁶ energies at the same external cutoff. -/
theorem transport_lower_weighted_bound (N : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (b : LiftDomain period → Domain 4) (e : LiftDomain period → Vector3)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hbL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w b) 2 (liftMeasure
      period))
    (heL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w e) 2 (liftMeasure
      period)) :
    (∑ n ∈ Finset.range (N+1), weight ρ n*wordSobolevNorm period 5 n (transportField period 3 b e))
      ≤
      (5460*lowerProductConstant period 3)*
        (∑ l ∈ Finset.range (N+1), weight ρ l*wordSobolevNorm period 6 l b)*
        (∑ j ∈ Finset.range (N+1), weight ρ j*wordSobolevNorm period 6 j e) := by
  have h := Finset.sum_le_sum (s := Finset.range (N+1)) (fun n _ => mul_le_mul_of_nonneg_left
    (transport_lower_no_loss period n b e hb he hbL heL) (weight_pos hρ n).le)
  have hfac : (∑ n ∈ Finset.range (N+1), weight ρ n*((5460*lowerProductConstant period
    3)*leibnizConvolution
      (fun l => wordSobolevNorm period 6 l b) (fun l => wordSobolevNorm period 6 l e) n)) =
      (5460*lowerProductConstant period 3)* ∑ n ∈ Finset.range (N+1), weight ρ n*leibnizConvolution
        (fun l => wordSobolevNorm period 6 l b) (fun l => wordSobolevNorm period 6 l e) n := by
    simp only [Finset.mul_sum, mul_left_comm]
  rw [hfac] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (unshifted_product_sum ρ hρ N _ _
    (fun l => wordSobolevNorm_nonneg period 6 l b) (fun l => wordSobolevNorm_nonneg period 6 l e))
    (mul_nonneg (by norm_num) (lowerProductConstant_nonneg period 3))).trans_eq (mul_assoc _ _
      _).symm)

end EulerH6Nonlinear

namespace EulerH6Pressure

open MeasureTheory EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerJetProductBounds
  EulerPacketWeights

variable (period : ℝ) [Fact (0 < period)] {directions : Fin 4 → LiftTangent}

/-- Actual coefficient multiplication has its unshifted weighted fixed-Sobolev bound. -/
theorem multiply_block_weighted_bound {s q : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period directions s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (N : ℕ) (hN : N+q ≤ s) (ρ : ℝ) (hρ : 0 < ρ) :
    (∑ n ∈ Finset.range (N+1), weight ρ n * blockNorm period
      (EulerSpatialSobolevInverse.SpatialJet.multiply K J) q n) ≤
      (∑ l ∈ Finset.range (N+1), weight ρ l*coefficientBlock period K q l)*
        (∑ j ∈ Finset.range (N+1), weight ρ j*blockNorm period J q j) := by
  have h := Finset.sum_le_sum (s := Finset.range (N+1)) (fun n hn => mul_le_mul_of_nonneg_left
    (multiply_blockNorm_bound K J (by have := Finset.mem_range.mp hn; omega : n+q ≤ s)) (weight_pos
      hρ n).le)
  exact h.trans (EulerWeightedConvolution.unshifted_product_sum ρ hρ N _ _
    (fun _ => coefficientBlock_nonneg K) (fun _ => blockNorm_nonneg J))

end EulerH6Pressure

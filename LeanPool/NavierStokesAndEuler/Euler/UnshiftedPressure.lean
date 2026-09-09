/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.H6PressureConstants

@[expose] public section

/-! The actual pressure inverse in unshifted Gevrey-weighted fixed Sobolev blocks. -/

noncomputable section

namespace EulerWeightedPressure

open Finset EulerPacketWeights EulerWeightedConvolution EulerGevrey

/-- The ordinary Gevrey product weight gains the reciprocal binomial coefficient. -/
theorem unshifted_weight_kernel (ρ Rc : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc)
    (j l : ℕ) (Z : ℝ) (hZ : 0 ≤ Z) :
    weight ρ (j+l) * ((j+l).choose l : ℝ) * (Rc^l * (l.factorial : ℝ)^2) * Z ≤
      (ρ*Rc)^l * (weight ρ j * Z) := by
  have he : weight ρ (j+l) * ((j+l).choose l : ℝ) * (Rc^l * (l.factorial : ℝ)^2) * Z =
      ((ρ*Rc)^l * (weight ρ j * Z)) / ((j+l).choose l : ℝ) := by
    rw [Nat.cast_choose ℝ (Nat.le_add_left l j)]
    simp only [Nat.add_sub_cancel_right]
    unfold weight
    rw [pow_add, mul_pow]
    field_simp [factorial_cast_ne_zero]
  have hc : (1 : ℝ) ≤ ((j+l).choose l : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_left l j)
  rw [he]
  exact div_le_self (mul_nonneg (pow_nonneg (mul_nonneg hρ.le hRc) l)
    (mul_nonneg (weight_pos hρ j).le hZ)) hc

/-- Positive-order coefficient terms are absorbed in the unshifted Gevrey sum with a constant independent of the cutoff. -/
theorem unshifted_weighted_inverse (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc)
    (hM : 1 ≤ M) (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (N : ℕ) (A F Z : ℕ → ℝ) (_hF : ∀ n, 0 ≤ F n) (hZ : ∀ n, 0 ≤ Z n)
    (hA : ∀ l, 1 ≤ l → l ≤ N → A l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2)
    (hrec : ∀ n ≤ N, Z n ≤ M * (F n + ∑ l ∈ range n,
      (n.choose (l + 1) : ℝ) * A (l + 1) * Z (n - (l + 1)))) :
    (∑ n ∈ range (N + 1), weight ρ n * Z n) ≤
      2 * M * ∑ n ∈ range (N + 1), weight ρ n * F n := by
  let v : ℕ → ℝ := fun n => weight ρ n
  have hv : ∀ n, 0 ≤ v n := fun n => (weight_pos hρ _).le
  have hq : 0 ≤ ρ * Rc := mul_nonneg hρ.le hRc
  have hhalf : ρ * Rc ≤ 1 / 2 := by nlinarith
  have hcomm : (∑ n ∈ range (N + 1), v n * ∑ l ∈ range n,
      (n.choose (l + 1) : ℝ) * A (l + 1) * Z (n - (l + 1))) ≤
      (2 * (ρ * Rc)) * ∑ j ∈ range (N + 1), v j * Z j := by
    calc
      _ = ∑ n ∈ range (N + 1), ∑ l ∈ range n,
          v n * (n.choose (l + 1) : ℝ) * A (l + 1) * Z (n - (l + 1)) := by
        simp only [mul_sum, mul_assoc]
      _ ≤ ∑ n ∈ range (N + 1), ∑ l ∈ range n,
          (ρ * Rc) ^ (l + 1) * (v (n - (l + 1)) * Z (n - (l + 1))) := by
        apply sum_le_sum
        intro n hn
        apply sum_le_sum
        intro l hl
        have hln := mem_range.mp hl
        have hnN : n ≤ N := by have := mem_range.mp hn; omega
        have hcoeff := hA (l + 1) (by omega) (by omega)
        have h1 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcoeff
            (mul_nonneg (hv n) (Nat.cast_nonneg (n.choose (l + 1))))) (hZ (n - (l + 1)))
        have h2 := unshifted_weight_kernel ρ Rc hρ hRc (n - (l + 1)) (l + 1)
          (Z (n - (l + 1))) (hZ _)
        have he : n - (l + 1) + (l + 1) = n := by omega
        dsimp [v] at h1 ⊢
        exact h1.trans (by simpa only [he] using h2)
      _ ≤ _ := geometric_lower_triangle (ρ * Rc) hq hhalf N
        (fun j => v j * Z j) (fun j => mul_nonneg (hv j) (hZ j))
  have hs := sum_le_sum (s := range (N + 1)) (fun n hn =>
    mul_le_mul_of_nonneg_left (hrec n (by have := mem_range.mp hn; omega)) (hv n))
  have hsumid : (∑ n ∈ range (N + 1), v n * (M * (F n + ∑ l ∈ range n,
      (n.choose (l + 1) : ℝ) * A (l + 1) * Z (n - (l + 1))))) =
      M * ((∑ n ∈ range (N + 1), v n * F n) +
        ∑ n ∈ range (N + 1), v n * ∑ l ∈ range n,
          (n.choose (l + 1) : ℝ) * A (l + 1) * Z (n - (l + 1))) := by
    simp only [mul_add, sum_add_distrib, mul_sum, mul_left_comm, mul_comm]
  rw [hsumid] at hs
  have hzsum : 0 ≤ ∑ n ∈ range (N + 1), v n * Z n :=
    sum_nonneg (fun n _ => mul_nonneg (hv n) (hZ n))
  have hsmall' := mul_le_mul_of_nonneg_right hsmall hzsum
  have hcomm' := mul_le_mul_of_nonneg_left hcomm (show 0 ≤ M by linarith)
  change (∑ n ∈ range (N + 1), v n * Z n) ≤ 2 * M * ∑ n ∈ range (N + 1), v n * F n
  nlinarith

end EulerWeightedPressure

namespace EulerH6Pressure

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerSpatialSobolevInverse
  EulerJetProductBounds EulerPressureJetIdentities EulerPressureSpatialRegularity
open scoped Topology

variable (period : ℝ) [Fact (0 < period)] {directions : Fin 4 → LiftTangent}

theorem pressure_unshifted_Hq_bound {s q : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period directions s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (N : ℕ) (hN : N + q ≤ s) (hq : q ≤ s)
    (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase : (CoefficientJet.restrict K q hq).pressureConstant c ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N →
      coefficientBlock period K q l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2) :
    (∑ n ∈ Finset.range (N + 1), EulerPacketWeights.weight ρ n *
      blockNorm period (J.solvePressure K κ m c hc hpos) q n) ≤
      2 * M * ∑ n ∈ Finset.range (N + 1), EulerPacketWeights.weight ρ n *
        blockNorm period J q n := by
  apply EulerWeightedPressure.unshifted_weighted_inverse ρ Rc M hρ hRc hM hsmall N
    (coefficientBlock period K q) (blockNorm period J q)
    (blockNorm period (J.solvePressure K κ m c hc hpos) q)
    (fun _ => blockNorm_nonneg J) (fun _ => blockNorm_nonneg _) hcoeff
  intro n hn
  exact pressure_block_recurrence K J κ m c hc hpos hq (by omega) M hbase

end EulerH6Pressure

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderSobolev
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketWeights
public import LeanPool.NavierStokesAndEuler.Euler.H6PressureCommutator

/-! The actual base-order pressure commutator needs only one fewer pressure derivative. -/

@[expose] public section


noncomputable section

namespace EulerBasePressureCommutator

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolev EulerSpatialSobolevInverse
  EulerH6Pressure EulerJetProductBounds EulerPacketWeights
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Sum of the strictly positive coefficient derivative bounds at the fixed base index six. -/
def baseCoefficientSum {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A) : ℝ :=
  ∑ l ∈ Finset.range 6, boundLevel period K (l+1)

omit [Fact (0 < period)] in
theorem baseCoefficientSum_nonneg {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A) : 0 ≤
        baseCoefficientSum period K :=
  Finset.sum_nonneg fun _ _ => boundLevel_nonneg K

/-- Every pressure derivative of order at most five is controlled by its genuine H⁵ norm. -/
theorem pressure_level_le_five {p : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period standardDirection 6 p) {j : ℕ} (hj : j ≤ 5) :
    levelNorm period J j ≤ sobolevSize period (directions := standardDirection) 5 p := by
  rw [← blockNorm_zero_eq_size J (by norm_num : 5 ≤ 6)]
  change levelNorm period J j ≤ ∑ r ∈ Finset.range 6, levelNorm period J r
  have hmem : j ∈ Finset.range 6 := Finset.mem_range.mpr (by omega)
  exact Finset.single_le_sum (fun r _ => (levelNorm_nonneg J : 0 ≤ levelNorm period J r)) hmem

/-- At each base derivative order, the actual coefficient commutator uses only H⁵ pressure. -/
theorem base_order_bound {A : SmoothCoefficient period} {p : LiftL2 period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (J : EulerSpatialSobolevInverse.SpatialJet period standardDirection 6 p) (r : ℕ) (hr : r ≤ 6) :
    commutatorBlock K J 0 r ≤ 64 * baseCoefficientSum period K * sobolevSize period (directions :=
        standardDirection) 5 p := by
  apply (commutatorBlock_bound K J (by omega : r+0 ≤ 6)).trans
  rw [commutatorConvolution_eq_sum]
  have hs : (∑ l ∈ Finset.range r, (r.choose (l+1) : ℝ)*coefficientBlock period K 0 (l+1)*blockNorm
      period J 0 (r-(l+1))) ≤
      64 * (∑ l ∈ Finset.range r, boundLevel period K (l+1)) * sobolevSize period (directions :=
          standardDirection) 5 p := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro l hl
    have hj : r-(l+1) ≤ 5 := by have := Finset.mem_range.mp hl; omega
    have hc : (r.choose (l+1) : ℝ) ≤ 64 := by
      have h1 : (r.choose (l+1) : ℝ) ≤ (2 : ℝ)^r := by exact_mod_cast Nat.choose_le_two_pow r (l+1)
      exact h1.trans ((pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr).trans_eq (by norm_num))
    simpa [coefficientBlock, blockNorm] using
      (mul_le_mul (mul_le_mul_of_nonneg_right hc (boundLevel_nonneg K))
        (pressure_level_le_five period J hj) (levelNorm_nonneg J)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64) (boundLevel_nonneg K)))
  apply hs.trans
  apply mul_le_mul_of_nonneg_right _ (sobolevSize_nonneg 5 p)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 64)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hr) (fun _ _ _ =>
      boundLevel_nonneg K)

/-- Summing all base orders through six leaves a fixed constant and only H⁵ pressure. -/
theorem base_sum_bound {A : SmoothCoefficient period} {p : LiftL2 period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (J : EulerSpatialSobolevInverse.SpatialJet period standardDirection 6 p) :
    (∑ r ∈ Finset.range 7, commutatorBlock K J 0 r) ≤
      448 * baseCoefficientSum period K * sobolevSize period (directions := standardDirection) 5 p
          := by
  have h := Finset.sum_le_sum (s := Finset.range 7) (fun r hr => base_order_bound period K J r (by
      have := Finset.mem_range.mp hr; omega))
  exact h.trans_eq (by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring)

/-- The actual base pressure commutators after an external derivative word. -/
def basePressureBlock {s : ℕ} {A : SmoothCoefficient period} {p : LiftL2 period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (J : EulerSpatialSobolevInverse.SpatialJet period standardDirection s p) (n : ℕ) (hn : n + 6 ≤
        s)
        : ℝ :=
  ∑ w : Fin n → Fin 4, ∑ r ∈ Finset.range 7,
    commutatorBlock K (EulerH6Pressure.SpatialJet.derivativeJet (q := 6) J w hn) 0 r

/-- At every external order, the base commutator loses no external derivative. -/
theorem basePressureBlock_bound {s : ℕ} {A : SmoothCoefficient period} {p : LiftL2 period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (J : EulerSpatialSobolevInverse.SpatialJet period standardDirection s p) (n : ℕ) (hn : n + 6 ≤
        s)
        :
    basePressureBlock period K J n hn ≤ 448 * baseCoefficientSum period K * blockNorm period J 5 n
        := by
  rw [blockNorm_eq_word_sizes J (by omega : n+5 ≤ s), Finset.mul_sum]
  exact Finset.sum_le_sum fun w _ => base_sum_bound period K
      (EulerH6Pressure.SpatialJet.derivativeJet J w hn)

/-- The complete finite weighted base pressure commutator is controlled by the unshifted H⁵ pressure
sum. -/
theorem basePressure_weighted_bound {s : ℕ} {A : SmoothCoefficient period} {p : LiftL2 period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (J : EulerSpatialSobolevInverse.SpatialJet period standardDirection s p) (N : ℕ) (hN : N + 6 ≤
        s)
    (ρ : ℝ) (hρ : 0 < ρ) :
    (∑ n : Fin (N+1), weight ρ n.val * basePressureBlock period K J n.val (by
        have := n.isLt; omega)) ≤
      448 * baseCoefficientSum period K * ∑ n ∈ Finset.range (N+1), weight ρ n * blockNorm period J
          5 n := by
  rw [← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  exact Finset.sum_le_sum fun n _ =>
    (mul_le_mul_of_nonneg_left (basePressureBlock_bound period K J n.val (by have := n.isLt; omega))
      (weight_pos hρ n.val).le).trans_eq (by ring)

end EulerBasePressureCommutator

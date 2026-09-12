/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketWeights
public import LeanPool.NavierStokesAndEuler.Euler.H6PressureCommutator
import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
import LeanPool.NavierStokesAndEuler.Euler.Foundations.WeightedConvolution

/-! Actual external pressure commutators controlled by the shifted pressure sum below the velocity
cutoff. -/

@[expose] public section


noncomputable section

namespace EulerPressureCommutatorWeights

open Finset EulerPacketWeights EulerWeightedConvolution EulerGevrey
  EulerJetProductBounds

/-- Remove the coefficient's zeroth order, which is absent from every commutator. -/
def positivePart (A : ℕ → ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else A n

/-- Delay a pressure sequence by one order so the external radius-loss convolution has the source's
exact index. -/
def delayed (P : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => P n

/-- The positive coefficient sum is a geometric tail, uniformly in its cutoff. -/
theorem positiveCoefficientSum_bound (ρ Rc : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc)
    (hsmall : ρ * Rc ≤ 1 / 2) (N : ℕ) (A : ℕ → ℝ)
    (hA : ∀ l, 1 ≤ l → l ≤ N → A l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2) :
    (∑ l ∈ range (N+1), weight ρ l * positivePart A l) ≤ 2*(ρ*Rc) := by
  rw [sum_range_succ']
  simp only [positivePart, Nat.add_one_ne_zero, ite_false, ite_true, mul_zero, add_zero]
  calc
    _ ≤ ∑ l ∈ range N, (ρ*Rc)^(l+1) := by
      apply sum_le_sum
      intro l hl
      have h := mul_le_mul_of_nonneg_left (hA (l+1) (by
          omega) (by have := mem_range.mp hl; omega)) (weight_pos hρ (l+1)).le
      have he : weight ρ (l+1) * (Rc^(l+1)*((l+1).factorial : ℝ)^2) = (ρ*Rc)^(l+1) := by
        unfold weight
        rw [mul_pow]
        field_simp [factorial_cast_ne_zero]
      exact h.trans_eq he
    _ ≤ _ := geometric_tail_le_two_mul (ρ*Rc) (mul_nonneg hρ.le hRc) hsmall N

/-- The delayed pressure sum is exactly the shifted sum strictly below the cutoff. -/
theorem delayed_weighted_sum (ρ : ℝ) (N : ℕ) (P : ℕ → ℝ) :
    (∑ j ∈ range (N+1), (j : ℝ)*weight ρ j*delayed P j) =
      ∑ j ∈ range N, ((j+1 : ℕ) : ℝ)*weight ρ (j+1)*P j := by
  rw [sum_range_succ']
  simp only [delayed, Nat.cast_zero, zero_mul, add_zero]

/-- The external commutator is controlled by the shifted lower-order pressure sum, without pressure
order N. -/
theorem commutator_weighted_shifted (ρ Rc : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc)
    (hsmall : ρ * Rc ≤ 1 / 2) (N : ℕ) (A P : ℕ → ℝ)
    (hA0 : ∀ l, 0 ≤ A l) (hP : ∀ l, 0 ≤ P l)
    (hA : ∀ l, 1 ≤ l → l ≤ N → A l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2) :
    (∑ n ∈ range (N+1), weight ρ n * commutatorConvolution A P n) ≤
      2*Rc * ∑ j ∈ range N, ((j+1 : ℕ) : ℝ)*weight ρ (j+1)*P j := by
  have ha : ∀ l, 0 ≤ positivePart A l := fun l => by
      unfold positivePart; split <;> first | exact le_rfl | exact hA0 l
  have hp : ∀ l, 0 ≤ delayed P l := by
      intro l; cases l with | zero => exact le_rfl | succ l => exact hP l
  have he : (∑ n ∈ range (N+1), weight ρ n * commutatorConvolution A P n) =
      ∑ n ∈ range (N+1), ∑ l ∈ range n,
        weight ρ n * (n.choose (l+1) : ℝ) * positivePart A (l+1) * delayed P (n-l) := by
    simp only [commutatorConvolution_eq_sum, mul_sum]
    apply sum_congr rfl
    intro n _
    apply sum_congr rfl
    intro l hl
    have hn : n-l = (n-(l+1))+1 := by have := mem_range.mp hl; omega
    rw [hn]
    simp only [positivePart, Nat.add_one_ne_zero, ite_false, delayed]
    ring
  rw [he]
  have h := external_commutator_sum ρ hρ N (positivePart A) (delayed P) ha hp
  rw [delayed_weighted_sum] at h
  have hs : 0 ≤ ∑ j ∈ range N, ((j+1 : ℕ) : ℝ)*weight ρ (j+1)*P j :=
    sum_nonneg fun j _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (weight_pos hρ _).le) (hP j)
  exact h.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (positiveCoefficientSum_bound ρ Rc hρ hRc hsmall N A hA)
      (inv_nonneg.mpr hρ.le)) hs).trans_eq (by field_simp [hρ.ne']))

end EulerPressureCommutatorWeights

namespace EulerH6Pressure

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerSpatialSobolevInverse
  EulerJetProductBounds  EulerPressureSpatialRegularity EulerPacketWeights

variable (period : ℝ) [Fact (0 < period)] {directions : Fin 4 → LiftTangent}

/-- The actual fixed-Sobolev external coefficient commutator has a bound using only the shifted
pressure below the cutoff. -/
theorem commutatorBlock_weighted_shifted {s q : ℕ} {A : SmoothCoefficient period} {p : LiftL2
    period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period directions s A)
    (P : EulerSpatialSobolevInverse.SpatialJet period directions s p)
    (N : ℕ) (hN : N + q ≤ s) (ρ Rc : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hsmall : ρ * Rc ≤ 1 / 2)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K q l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2) :
    (∑ n ∈ Finset.range (N+1), weight ρ n * commutatorBlock K P q n) ≤
      2*Rc * ∑ j ∈ Finset.range N, ((j+1 : ℕ) : ℝ)*weight ρ (j+1)*blockNorm period P q j := by
  have h := Finset.sum_le_sum (s := Finset.range (N+1)) (fun n hn =>
    mul_le_mul_of_nonneg_left (commutatorBlock_bound K P (by
        have := Finset.mem_range.mp hn; omega : n+q ≤ s))
      (weight_pos hρ n).le)
  exact h.trans (EulerPressureCommutatorWeights.commutator_weighted_shifted ρ Rc hρ hRc hsmall N
    (coefficientBlock period K q) (blockNorm period P q)
    (fun _ => coefficientBlock_nonneg K) (fun _ => blockNorm_nonneg P) hcoeff)

end EulerH6Pressure

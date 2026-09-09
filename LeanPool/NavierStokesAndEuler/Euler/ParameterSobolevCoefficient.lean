/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks
public import LeanPool.NavierStokesAndEuler.Euler.PacketMajorantShift

@[expose] public section

/-!
# Absorbing a fixed Sobolev coefficient order once

The actual coefficient blocks are finite sums of ordinary coefficient jets.
Their alphabet count and fixed base derivative order enlarge only the
coefficient radius, once. No forcing or solution radius is changed.
-/

noncomputable section

namespace EulerParameterWordGevrey

open ContinuousLinearMap Finset EulerGevrey
open scoped ContDiff

variable {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- The actual fixed-base block is the finite sum of the higher word levels. -/
theorem block_eq_sum_levels (directions : ι → P) (q : ℕ) (f : P → E)
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : P) :
    block directions q f n x = ∑ k ∈ range (q+1), wordSum directions f (n+k) x := by
  induction n generalizing f with
  | zero => simp only [block_zero, baseSize, Nat.zero_add]
  | succ n ih =>
    rw [block_succ directions q f hf n x]
    simp_rw [ih _ (directional_contDiff directions f hf _)]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    simpa only [show n+1+k=n+k+1 by omega] using
      (wordSum_succ directions f hf (n+k) x).symm

/-- The enlarged radius is a property only of the coefficient alphabet. -/
def sobolevCoefficientRadius (ι : Type*) [Fintype ι] (Rc : ℝ) : ℝ :=
  4*(max 1 (Fintype.card ι : ℝ)*Rc)

/-- For fixed q this is a literal polynomial in the original coefficient
radius and amplitude, with numerical factorial coefficients. -/
def sobolevCoefficientAmplitude (ι : Type*) [Fintype ι] (q : ℕ) (Rc C : ℝ) : ℝ :=
  (2 : ℝ)^q*C*∑ k ∈ range (q+1), sobolevCoefficientRadius ι Rc^k*(k.factorial : ℝ)^2

theorem sobolevCoefficientRadius_nonneg (Rc : ℝ) (hRc : 0 ≤ Rc) :
    0 ≤ sobolevCoefficientRadius ι Rc := by
  unfold sobolevCoefficientRadius
  positivity

theorem sobolevCoefficientAmplitude_nonneg (q : ℕ) (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) :
    0 ≤ sobolevCoefficientAmplitude ι q Rc C := by
  have hr := sobolevCoefficientRadius_nonneg (ι := ι) Rc hRc
  unfold sobolevCoefficientAmplitude
  positivity

/-- All actual fixed-Sobolev coefficient blocks have an unshifted factorial
bound after a single coefficient-radius enlargement. -/
theorem coefficientBlock_of_tensor_bound (directions : ι → P)
    (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ) (A : P → E) (hA : ContDiff ℝ ∞ A)
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hAb : ∀ n x, ‖iteratedFDeriv ℝ n A x‖ ≤ C*majorant Rc 0 n) (n : ℕ) (x : P) :
    coefficientBlock directions q A n x ≤
      sobolevCoefficientAmplitude ι q Rc C*majorant (sobolevCoefficientRadius ι Rc) 0 n := by
  let r₀ : ℝ := max 1 (Fintype.card ι : ℝ)*Rc
  have hr₀ : 0 ≤ r₀ := mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hRc
  have hk (k : ℕ) : wordSum directions A (n+k) x ≤
      C*(sobolevCoefficientRadius ι Rc^k*(k.factorial : ℝ)^2)*
        majorant (sobolevCoefficientRadius ι Rc) 0 n := by
    have hword := wordSum_gevrey directions hd A Rc C hRc hC 0 hAb (n+k) x
    have hword' : wordSum directions A (n+k) x ≤ C*majorant r₀ k n := by
      simpa only [majorant, Nat.add_zero, r₀] using hword
    have hs := mul_le_mul_of_nonneg_left (majorant_coarse_split r₀ hr₀ k n) hC
    exact hword'.trans (hs.trans_eq (by
      change C*((4*r₀)^k*(k.factorial : ℝ)^2*majorant (4*r₀) 0 n) =
        C*((4*r₀)^k*(k.factorial : ℝ)^2)*majorant (4*r₀) 0 n
      ring))
  change (2 : ℝ)^q*block directions q A n x ≤ _
  rw [block_eq_sum_levels directions q A hA n x]
  calc
    _ ≤ (2 : ℝ)^q*∑ k ∈ range (q+1),
        C*(sobolevCoefficientRadius ι Rc^k*(k.factorial : ℝ)^2)*
          majorant (sobolevCoefficientRadius ι Rc) 0 n :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun k _ => hk k)) (by positivity)
    _ = _ := by
      unfold sobolevCoefficientAmplitude
      rw [← sum_mul, ← mul_sum]
      ring

theorem baseSize_le_coefficientBlock_zero (directions : ι → P) (q : ℕ) (A : P → E) (x : P) :
    baseSize directions q A x ≤ coefficientBlock directions q A 0 x := by
  change _ ≤ (2 : ℝ)^q*block directions q A 0 x
  rw [block_zero]
  have hp : (1 : ℝ) ≤ (2 : ℝ)^q := one_le_pow₀ (by norm_num)
  exact (one_mul _).symm.trans_le (mul_le_mul_of_nonneg_right hp (baseSize_nonneg directions q A x))

theorem baseSize_of_tensor_bound (directions : ι → P)
    (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ) (A : P → E) (hA : ContDiff ℝ ∞ A)
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hAb : ∀ n x, ‖iteratedFDeriv ℝ n A x‖ ≤ C*majorant Rc 0 n) (x : P) :
    baseSize directions q A x ≤ sobolevCoefficientAmplitude ι q Rc C := by
  have h := (baseSize_le_coefficientBlock_zero directions q A x).trans
    (coefficientBlock_of_tensor_bound directions hd q A hA Rc C hRc hC hAb 0 x)
  simpa only [majorant, Nat.zero_add, pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, mul_one]
    using h

end EulerParameterWordGevrey

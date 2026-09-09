/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2Gevrey
import Mathlib.Algebra.Order.Star.Real

/-! The fixed physical Sobolev order costs a polynomial in the Gevrey
radius. Explicit coarse powers leave room for the source exponent
C*=10(s+2), including the sum of all three particle-map fields. -/

@[expose] public section


noncomputable section

namespace EulerSobolevSourceExponent

open Finset EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerParameterWordGevrey EulerMeanClassicalWordBounds EulerPacketParentLabelBounds

/-- Fixed cost, given by `(2 : ℝ)^q*∑ j ∈ range (q+1), (j.factorial : ℝ)^2`. -/
def fixedCost (q : ℕ) : ℝ := (2 : ℝ)^q*∑ j ∈ range (q+1), (j.factorial : ℝ)^2

theorem fixedCost_nonneg (q : ℕ) : 0 ≤ fixedCost q := by unfold fixedCost; positivity

theorem coefficient_radius_le (k R : ℝ) (hk : 12 ≤ k) (hR : R ≤ k ^ 5) :
    sobolevCoefficientRadius (Fin 3) R ≤ k^6 := by
  have he : sobolevCoefficientRadius (Fin 3) R = 12*R := by
    norm_num [sobolevCoefficientRadius]
    ring
  rw [he]
  calc
    12*R ≤ 12*k^5 := mul_le_mul_of_nonneg_left hR (by norm_num)
    _ ≤ k*k^5 := mul_le_mul_of_nonneg_right hk (pow_nonneg (by linarith) 5)
    _ = k^6 := by ring

theorem coefficient_amplitude_le (q : ℕ) (k C R : ℝ) (hk : 12 ≤ k)
    (hcost : fixedCost q ≤ k) (_hC : 0 ≤ C) (hR : 0 ≤ R) (hCb : C ≤ k ^ 6) (hRb : R ≤ k ^ 5) :
    sobolevCoefficientAmplitude (Fin 3) q R C ≤ k^(6*q+7) := by
  have hk0 : 0 ≤ k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hr0 := sobolevCoefficientRadius_nonneg (ι := Fin 3) R hR
  have hr := coefficient_radius_le k R hk hRb
  have hj (j : ℕ) (hj : j ∈ range (q+1)) :
      sobolevCoefficientRadius (Fin 3) R^j ≤ k^(6*q) := by
    have hjq : j ≤ q := by simpa using Nat.le_of_lt_succ (mem_range.mp hj)
    calc
      _ ≤ (k^6)^j := pow_le_pow_left₀ hr0 hr j
      _ = k^(6*j) := (pow_mul k 6 j).symm
      _ ≤ k^(6*q) := pow_le_pow_right₀ hk1 (Nat.mul_le_mul_left 6 hjq)
  have hsum : (∑ j ∈ range (q+1), sobolevCoefficientRadius (Fin 3) R^j*(j.factorial : ℝ)^2) ≤
      k^(6*q)*(∑ j ∈ range (q+1), (j.factorial : ℝ)^2) := by
    rw [mul_sum]
    exact sum_le_sum (fun j hj' => mul_le_mul_of_nonneg_right (hj j hj') (sq_nonneg _))
  calc
    _ ≤ (2 : ℝ)^q*k^6*(k^(6*q)*∑ j ∈ range (q+1), (j.factorial : ℝ)^2) := by
      unfold sobolevCoefficientAmplitude
      exact mul_le_mul (mul_le_mul_of_nonneg_left hCb (by positivity)) hsum
        (by positivity) (by positivity)
    _ = fixedCost q*k^(6*q+6) := by
      rw [show 6*q+6 = 6+6*q by omega,pow_add]
      unfold fixedCost
      ring
    _ ≤ k*k^(6*q+6) := mul_le_mul_of_nonneg_right hcost (pow_nonneg hk0 _)
    _ = k^(6*q+7) := by
      rw [show 6*q+7 = (6*q+6)+1 by omega,pow_succ]
      ring

theorem source_cost_bounds (q : ℕ) (k C R : ℝ) (hk : 12 ≤ k)
    (hcost : fixedCost q ≤ k) (hC : 0 ≤ C) (hR : 0 ≤ R) (hCb : C ≤ k ^ 6) (hRb : R ≤ k ^ 5) :
    3*sobolevCoefficientAmplitude (Fin 3) q R C ≤ k^(10*(q+2)) ∧
      sobolevCoefficientRadius (Fin 3) R ≤ k^(10*(q+2)) := by
  have hk0 : 0 ≤ k := by linarith
  have hk1 : 1 ≤ k := by linarith
  constructor
  · calc
      _ ≤ 3*k^(6*q+7) := mul_le_mul_of_nonneg_left
        (coefficient_amplitude_le q k C R hk hcost hC hR hCb hRb) (by norm_num)
      _ ≤ k*k^(6*q+7) := mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hk0 _)
      _ = k^(6*q+8) := by rw [show 6*q+8=(6*q+7)+1 by omega,pow_succ]; ring
      _ ≤ k^(10*(q+2)) := pow_le_pow_right₀ hk1 (by omega)
  · exact (coefficient_radius_le k R hk hRb).trans (pow_le_pow_right₀ hk1 (by omega))

theorem triple_classical_bound (q : ℕ) (A B C : SmoothL2Field Space) (M R J : ℝ)
    (hM : 0 ≤ M) (hR : 0 ≤ R) (hA : A.HasJetBound M R) (hB : B.HasJetBound M R) (hC : C.HasJetBound
        M R)
    (hcost : 3 * sobolevCoefficientAmplitude (Fin 3) q R M ≤ J)
    (hrad : sobolevCoefficientRadius (Fin 3) R ≤ J) (n : ℕ) :
    classicalBlockSize direction q A.toLp A.translation_contDiff n +
      classicalBlockSize direction q B.toLp B.translation_contDiff n +
      classicalBlockSize direction q C.toLp C.translation_contDiff n ≤ J^(n+1)*(n.factorial : ℝ)^2
          := by
  have hd (i : Fin 3) : ‖direction i‖ ≤ 1 := by simp [direction]
  have h₀ := classicalBlockSize_of_jet_bound direction hd q A M R hM hR hA n
  have h₁ := classicalBlockSize_of_jet_bound direction hd q B M R hM hR hB n
  have h₂ := classicalBlockSize_of_jet_bound direction hd q C M R hM hR hC n
  have hr0 := sobolevCoefficientRadius_nonneg (ι := Fin 3) R hR
  have hj0 : 0 ≤ J := hr0.trans hrad
  calc
    _ ≤ (3*sobolevCoefficientAmplitude (Fin 3) q R M) *
        sobolevCoefficientRadius (Fin 3) R^n*(n.factorial : ℝ)^2 :=
      (add_le_add (add_le_add h₀ h₁) h₂).trans_eq (by ring)
    _ ≤ J*J^n*(n.factorial : ℝ)^2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hcost (pow_le_pow_left₀ hr0 hrad n) (pow_nonneg hr0 n) hj0) (sq_nonneg _)
    _ = _ := by rw [pow_succ]; ring

theorem source_triple_classical_bound (q : ℕ) (A B C : SmoothL2Field Space) (k M R : ℝ)
    (hk : 12 ≤ k) (hcost : fixedCost q ≤ k) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hMb : M ≤ k ^ 6) (hRb : R ≤ k ^ 5)
    (hA : A.HasJetBound M R) (hB : B.HasJetBound M R) (hC : C.HasJetBound M R) (n : ℕ) :
    classicalBlockSize direction q A.toLp A.translation_contDiff n +
      classicalBlockSize direction q B.toLp B.translation_contDiff n +
      classicalBlockSize direction q C.toLp C.translation_contDiff n ≤
        (k^(10*(q+2)))^(n+1)*(n.factorial : ℝ)^2 := by
  have h := source_cost_bounds q k M R hk hcost hM hR hMb hRb
  exact triple_classical_bound q A B C M R _ hM hR hA hB hC h.1 h.2 n

end EulerSobolevSourceExponent

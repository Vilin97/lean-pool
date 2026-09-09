/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CoefficientJetPressureBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient
import Mathlib.Algebra.Order.Star.Real

/-! Joint monotonicity and genuine polynomial formulas for fixed-order
coefficient and pressure constants. These give uniform parent-scale bounds. -/

@[expose] public section


noncomputable section

namespace EulerParameterWordGevrey

open Finset

theorem sobolevCoefficientAmplitude_mono_all {ι : Type*} [Fintype ι]
    (q : ℕ) {R C S D : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C) (hRS : R ≤ S) (hCD : C ≤ D) :
    sobolevCoefficientAmplitude ι q R C ≤ sobolevCoefficientAmplitude ι q S D := by
  have hS : 0 ≤ S := hR.trans hRS
  have hD : 0 ≤ D := hC.trans hCD
  have hr := sobolevCoefficientRadius_nonneg (ι := ι) R hR
  have hrs : sobolevCoefficientRadius ι R ≤ sobolevCoefficientRadius ι S := by
    unfold sobolevCoefficientRadius
    gcongr
  unfold sobolevCoefficientAmplitude
  apply mul_le_mul
  · gcongr
  · apply sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr hrs k) (sq_nonneg _)
  · exact sum_nonneg (fun k _ => mul_nonneg (pow_nonneg hr k) (sq_nonneg _))
  · positivity

/-- Coefficient polynomial, given by `(2 : Polynomial ℝ)^q*C*∑ k ∈ range (q+1),
(16*R)^k*Polynomial.C ((k.factorial : ℝ)^2)`. -/
def coefficientPolynomial (q : ℕ) (R C : Polynomial ℝ) : Polynomial ℝ :=
  (2 : Polynomial ℝ)^q*C*∑ k ∈ range (q+1), (16*R)^k*Polynomial.C ((k.factorial : ℝ)^2)

theorem coefficientPolynomial_eval (q : ℕ) (R C : Polynomial ℝ) (x : ℝ) :
    (coefficientPolynomial q R C).eval x =
      sobolevCoefficientAmplitude (Fin 4) q (R.eval x) (C.eval x) := by
  simp only [coefficientPolynomial,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,
    Polynomial.eval_finsetSum, Polynomial.eval_C, sobolevCoefficientAmplitude,
        sobolevCoefficientRadius,
    Fintype.card_fin,Nat.cast_ofNat,max_eq_right (by norm_num : (1 : ℝ) ≤ 4)]
  congr 2
  funext k
  rw [show 16*R.eval x=4*(4*R.eval x) by ring]

end EulerParameterWordGevrey

namespace EulerCoefficientJetPressureBounds

theorem productCost_mono {B C : ℝ} (hBC : B ≤ C) (q : ℕ) : productCost B q ≤ productCost C q := by
  induction q with
  | zero => exact hBC
  | succ q ih =>
      simp only [productCost]
      gcongr

theorem pressureCost_mono {c d B C : ℝ} (hc : 0 < c) (hd : 0 < d) (hB : 0 ≤ B)
    (hci : c⁻¹ ≤ d⁻¹) (hBC : B ≤ C) (q : ℕ) : pressureCost c B q ≤ pressureCost d C q := by
  have hC : 0 ≤ C := hB.trans hBC
  induction q with
  | zero => exact hci
  | succ q ih =>
      have hp := productCost_nonneg B hB q
      have hP := productCost_nonneg C hC q
      have hv := pressureCost_nonneg c B hc hB q
      have hV := pressureCost_nonneg d C hd hC q
      have hb := productCost_mono hBC q
      simp only [pressureCost]
      gcongr

/-- Product polynomial as an element of `ℕ → Polynomial ℝ | 0 => B | q+1 =>
B+8*productPolynomial B q`. -/
def productPolynomial (B : Polynomial ℝ) : ℕ → Polynomial ℝ
  | 0 => B
  | q+1 => B+8*productPolynomial B q

/-- Pressure polynomial as an element of `ℕ → Polynomial ℝ | 0 => i | q+1 =>
i+4*(pressurePolynomial i B q*(1+productPolynomial B q*pressurePolynomial i B q))`. -/
def pressurePolynomial (i B : Polynomial ℝ) : ℕ → Polynomial ℝ
  | 0 => i
  | q+1 => i+4*(pressurePolynomial i B q*(1+productPolynomial B q*pressurePolynomial i B q))

theorem productPolynomial_eval (B : Polynomial ℝ) (q : ℕ) (x : ℝ) :
    (productPolynomial B q).eval x=productCost (B.eval x) q := by
  induction q with
  | zero => rfl
  | succ q ih => simp only [productPolynomial,productCost,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_ofNat,ih]

theorem pressurePolynomial_eval (i B : Polynomial ℝ) (q : ℕ) (x : ℝ) :
    (pressurePolynomial i B q).eval x=pressureCost (i.eval x)⁻¹ (B.eval x) q := by
  induction q with
  | zero => simp only [pressurePolynomial,pressureCost,inv_inv]
  | succ q ih => simp only [pressurePolynomial,pressureCost,Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, ih, productPolynomial_eval,
          inv_inv]

end EulerCoefficientJetPressureBounds

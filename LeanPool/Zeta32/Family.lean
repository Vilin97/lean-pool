/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.NumberTheory.Bernoulli

/-! Zeta32 — Family. -/

public section

open Polynomial
open scoped BigOperators

namespace Zeta32
noncomputable section

/-- The rational polynomial with roots `-1`, …, `-m`. -/
@[expose]
def D (m : ℕ) : ℚ[X] := ∏ j ∈ Finset.Icc 1 m, (X + C (j : ℚ))
/-- Numerator of the rational function used to construct the polynomial family. -/
@[expose]
def numerator (n k : ℕ) : ℚ[X] := X^k * (D n)^4
/-- Polynomial quotient of the numerator by the denominator polynomial. -/
@[expose]
def polynomialPart (n k : ℕ) : ℚ[X] := numerator n k /ₘ D (5*n)
/-- Residue coefficient at the simple pole indexed by `j`. -/
@[expose]
def residue (n k j : ℕ) : ℚ :=
  (numerator n k).eval (-(j : ℚ)) /
    ∏ l ∈ (Finset.Icc 1 (5*n)).erase j, ((l : ℚ)-(j : ℚ))
/-- Bernoulli moment of the polynomial functional at rational parameter `r`. -/
@[expose]
def moment (r : ℚ) (e : ℕ) : ℚ :=
  ((e+1 : ℕ) : ℚ) * bernoulli' e + 2*r*bernoulli' (e+1)
/-- Finite generalized harmonic sum of order `e` through index `j`. -/
@[expose]
def H (e j : ℕ) : ℚ := ∑ a ∈ Finset.Icc 1 j, 1 / (a : ℚ)^e
/-- Constant contribution of the pole indexed by `j` to the moment functional. -/
@[expose]
def beta (r : ℚ) (j : ℕ) : ℚ := 2*r - 2*j*H 3 j + 2*r*j*H 2 j
/-- Linear extension of the Bernoulli moments to a polynomial. -/
@[expose]
def polynomialMoment (r : ℚ) (p : ℚ[X]) : ℚ := p.sum fun e a => a * moment r e
/-- Coefficient of the target zeta value in the rational-function moment. -/
@[expose]
def slope (n k : ℕ) : ℚ := ∑ j ∈ Finset.Icc 1 (5*n), residue n k j * (2*j)
/-- Constant coefficient in the rational-function moment. -/
@[expose]
def intercept (r : ℚ) (n k : ℕ) : ℚ :=
  polynomialMoment r (polynomialPart n k) +
    ∑ j ∈ Finset.Icc 1 (5*n), residue n k j * beta r j
/-- Hankel matrix of the constant moment coefficients. -/
@[expose]
def A (r : ℚ) (n : ℕ) : Matrix (Fin (3*n)) (Fin (3*n)) ℚ :=
  fun i k => intercept r n (i.val+k.val)
/-- Hankel matrix of the target-value moment coefficients. -/
@[expose]
def B (n : ℕ) : Matrix (Fin (3*n)) (Fin (3*n)) ℚ :=
  fun i k => slope n (i.val+k.val)
/-- Determinant polynomial of the moment pencil `X • B + A`. -/
@[expose]
def Q (r : ℚ) (n : ℕ) : ℚ[X] :=
  Matrix.det ((X : ℚ[X]) • (B n).map C + (A r n).map C)

theorem Q_natDegree_le (r : ℚ) (n : ℕ) : (Q r n).natDegree ≤ 3*n := by
  simpa [Q] using Polynomial.natDegree_det_X_add_C_le (B n) (A r n)

/-- Primitive integral normalization of the determinant polynomial, with zero preserved. -/
def primitiveQ (r : ℚ) (n : ℕ) : ℤ[X] :=
  if Q r n = 0 then 0 else
    (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (Q r n)).primPart

theorem primitiveQ_isPrimitive (r : ℚ) (n : ℕ) (hn : Q r n ≠ 0) :
    (primitiveQ r n).IsPrimitive := by
  simp only [primitiveQ, ite_eq_right hn]
  exact Polynomial.isPrimitive_primPart _

theorem primitiveQ_natDegree_le (r : ℚ) (n : ℕ) : (primitiveQ r n).natDegree ≤ 3*n := by
  unfold primitiveQ
  split_ifs with hn
  · simp
  rw [Polynomial.natDegree_primPart]
  apply le_trans _ (Q_natDegree_le r n)
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  apply Polynomial.notMem_support_iff.mp
  intro h
  have hs := IsLocalization.integerNormalization_support (nonZeroDivisors ℤ) (Q r n)
  exact (Polynomial.notMem_support_iff.mpr (Polynomial.coeff_eq_zero_of_natDegree_lt hk)) (hs h)

theorem primitiveQ_proportional (r : ℚ) (n : ℕ) :
    ∃ a : ℚ, a ≠ 0 ∧ (primitiveQ r n).map (algebraMap ℤ ℚ) = C a * Q r n := by
  by_cases hn : Q r n = 0
  · exact ⟨1, one_ne_zero, by simp [primitiveQ, hn]⟩
  let R := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (Q r n)
  have hR : R ≠ 0 := fun hz => hn (IsFractionRing.integerNormalization_eq_zero_iff.mp hz)
  have hcont : R.content ≠ 0 := fun hz => hR (Polynomial.content_eq_zero_iff.mp hz)
  have hcontQ : (R.content : ℚ) ≠ 0 := by exact_mod_cast hcont
  obtain ⟨b, hb, hmap⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (Q r n)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
  refine ⟨(b : ℚ)/(R.content : ℚ), div_ne_zero hbQ hcontQ, ?_⟩
  apply Polynomial.ext
  intro k
  have hfac := congrArg (fun f : ℤ[X] => (f.map (algebraMap ℤ ℚ)).coeff k)
    R.eq_C_content_mul_primPart
  have hco : (b : ℚ) * (Q r n).coeff k = (R.content : ℚ) * (R.primPart.coeff k : ℚ) := by
    rw [show R.map (algebraMap ℤ ℚ) = b • Q r n from hmap] at hfac
    simpa using hfac
  simp only [primitiveQ, ite_eq_right hn, coeff_map, coeff_C_mul]
  change (R.primPart.coeff k : ℚ) = (b : ℚ)/(R.content : ℚ) * (Q r n).coeff k
  apply (mul_left_cancel₀ hcontQ)
  field_simp
  nlinarith [hco]

/-- Factorial quotient used to normalize the rational-function determinant. -/
@[expose]
def Sn (n : ℕ) : ℚ := ((5*n).factorial : ℚ) / ((n.factorial : ℚ)^4)
/-- Product of squared factorials used to normalize the Hankel determinant. -/
@[expose]
def Fn (n : ℕ) : ℚ := ∏ i ∈ Finset.range (3*n), ((i.factorial : ℚ))^2
/-- Positive scalar converting the determinant to its arithmetic normalization. -/
@[expose]
def scale (n : ℕ) : ℚ := Sn n ^ (3*n) / Fn n
/-- The determinant polynomial after multiplication by the arithmetic normalization. -/
@[expose]
def Qtilde (r : ℚ) (n : ℕ) : ℚ[X] := C (scale n) * Q r n

theorem Sn_pos (n : ℕ) : 0 < Sn n := by
  unfold Sn
  positivity

theorem Fn_pos (n : ℕ) : 0 < Fn n := by
  unfold Fn
  exact Finset.prod_pos fun i hi => by positivity

theorem scale_pos (n : ℕ) : 0 < scale n := by
  unfold scale
  exact div_pos (pow_pos (Sn_pos n) _) (Fn_pos n)

/-- Negative minimum valuation among the nonzero coefficients of the normalized polynomial. -/
@[expose]
def cost (r : ℚ) (n p : ℕ) : ℝ := -sInf
  {v : ℝ | ∃ k, (Qtilde r n).coeff k ≠ 0 ∧
    v = (padicValRat p ((Qtilde r n).coeff k) : ℝ)}

/-- A nonzero proportionality factor for the primitive integral normalization. -/
def primitiveScale (r : ℚ) (n : ℕ) : ℚ := (primitiveQ_proportional r n).choose
theorem primitiveScale_ne_zero (r : ℚ) (n : ℕ) : primitiveScale r n ≠ 0 :=
  (primitiveQ_proportional r n).choose_spec.1
theorem primitiveScale_spec (r : ℚ) (n : ℕ) :
    (primitiveQ r n).map (algebraMap ℤ ℚ) = C (primitiveScale r n) * Q r n :=
  (primitiveQ_proportional r n).choose_spec.2
/-- Primitive integral determinant polynomial with a positive proportionality factor. -/
@[expose]
def P (r : ℚ) (n : ℕ) : ℤ[X] :=
  if 0 < primitiveScale r n then primitiveQ r n else -primitiveQ r n

theorem P_natDegree_le (r : ℚ) (n : ℕ) : (P r n).natDegree ≤ 3*n := by
  unfold P
  split_ifs
  · exact primitiveQ_natDegree_le r n
  · simpa [Polynomial.natDegree_neg] using primitiveQ_natDegree_le r n

/-- Positive proportionality factor for the primitive determinant polynomial. -/
def d (r : ℚ) (n : ℕ) : ℚ := |primitiveScale r n|
/-- Positive proportionality factor relative to the arithmetically normalized polynomial. -/
def dtilde (r : ℚ) (n : ℕ) : ℚ := d r n / scale n

theorem d_pos (r : ℚ) (n : ℕ) : 0 < d r n := abs_pos.mpr (primitiveScale_ne_zero r n)
theorem dtilde_pos (r : ℚ) (n : ℕ) : 0 < dtilde r n := by
  exact div_pos (d_pos r n) (scale_pos n)

theorem P_eq_dtilde_Qtilde (r : ℚ) (n : ℕ) :
    (P r n).map (algebraMap ℤ ℚ) = C (dtilde r n) * Qtilde r n := by
  have hbase : (primitiveQ r n).map (algebraMap ℤ ℚ) = C (primitiveScale r n) * Q r n :=
    primitiveScale_spec r n
  have hP : (P r n).map (algebraMap ℤ ℚ) = C (d r n) * Q r n := by
    by_cases h : 0 < primitiveScale r n
    · simpa [P, h, d, abs_of_pos h] using hbase
    · have hn : primitiveScale r n < 0 :=
        lt_of_le_of_ne (le_of_not_gt h) (primitiveScale_ne_zero r n)
      have hneg : (-primitiveQ r n).map (algebraMap ℤ ℚ) =
          C (-primitiveScale r n) * Q r n := by
        rw [Polynomial.map_neg, hbase, C_neg, neg_mul]
      simpa [P, h, d, abs_of_neg hn] using hneg
  rw [Qtilde, dtilde]
  calc
    (P r n).map (algebraMap ℤ ℚ) = C (d r n) * Q r n := hP
    _ = C (d r n / scale n) * (C (scale n) * Q r n) := by
      rw [← mul_assoc, ← C_mul]
      congr 1
      field_simp [scale_pos n |>.ne']

/-- Real zeta value at three, expressed as a convergent series. -/
def zeta3val : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1)^3
/-- Real zeta value at two, expressed as a convergent series. -/
def zeta2val : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1)^2
/-- The real target value `ζ(3) - r * ζ(2)`. -/
def Cr (r : ℚ) : ℝ := zeta3val - (r : ℝ) * zeta2val

end
end Zeta32

end

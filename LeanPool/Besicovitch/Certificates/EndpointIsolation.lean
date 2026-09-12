/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Certificates.Krawczyk
public import LeanPool.Besicovitch.Certificates.DensePolynomial
public import LeanPool.Besicovitch.SixPoint.AlgebraicBasic

/-!
# Isolation of the six-point endpoint

This file encodes the two polynomial equations in centered coordinates. All numbers in the
preconditioner are rational, and the coefficient-norm estimates are checked by the kernel.
-/

@[expose] public section

noncomputable section

open Function NNReal Set

namespace LeanPool.Besicovitch

namespace DenseEndpoint

open DenseBivariatePolynomial

/-- The centered half-coordinate as a transparent dense polynomial. -/
def scaledS : DenseBivariatePolynomial :=
  add (constant (6933064218259049 / 10 ^ 16)) (scale (1 / 10 ^ 16) first)

/-- The centered distance coordinate as a transparent dense polynomial. -/
def scaledB : DenseBivariatePolynomial :=
  add (constant (5747488323603321 / (2 * 10 ^ 15)))
    (scale (3 / (2 * 10 ^ 15)) second)

/-- The cleared balance polynomial in transparent dense form. -/
def balance : DenseBivariatePolynomial :=
  let s := scaledS
  let B := scaledB
  let q := add (scale 2 s) (constant 1)
  let p := add (add (add (scale 2 B) (neg (scale 12 (pow s 2)))) (scale 4 s))
    (constant (-1))
  let D := add (add (scale 16 (pow s 2)) (neg (scale 4 s))) (neg B)
  let A2 := scale (1 / 2) (add (pow B 2) (constant (-1)))
  let C2 := add (scale (1 / 2) (add (pow B 2) (pow D 2))) (neg (scale 4 (pow s 2)))
  let K := add (scale 6 (mul s p)) (mul (add (scale 4 (pow s 2)) (constant (-1))) q)
  add (pow (add (pow K 2) (neg (mul (add A2 C2) (pow q 2)))) 2)
    (neg (scale 4 (mul (mul A2 C2) (pow q 4))))

/-- The cleared Gram polynomial in transparent dense form. -/
def gram : DenseBivariatePolynomial :=
  let s := scaledS
  let B := scaledB
  let q := add (scale 2 s) (constant 1)
  let p := add (add (add (scale 2 B) (neg (scale 12 (pow s 2)))) (scale 4 s))
    (constant (-1))
  let D := add (add (scale 16 (pow s 2)) (neg (scale 4 s))) (neg B)
  let x := add (constant 5) (neg (pow B 2))
  let z := add (add (pow q 2) (scale 4 (pow p 2))) (neg (mul (pow D 2) (pow q 2)))
  let k := add (mul (add (constant 1) (neg (scale 4 (pow s 2)))) (pow q 2)) (pow p 2)
  scale (1 / 64) <|
    add (pow (add (scale 8 k) (neg (mul x z))) 2)
      (neg (mul (add (constant 16) (neg (pow x 2)))
        (add (scale 16 (mul (pow p 2) (pow q 2))) (neg (pow z 2)))))

/-- The preconditioned fixed-point map in transparent dense form. -/
def fixedMap : Fin 2 → DenseBivariatePolynomial :=
  ![add first (neg (add (scale 68748375835 balance) (scale 4033169260133 gram))),
    add second (neg (add (scale 104924796527 balance) (scale 2365005784960 gram)))]

end DenseEndpoint

/-- Each coordinate of the fixed-point map is strictly inside the unit interval. -/
private theorem endpointMapPolynomial_coefficientL1Norm_lt_one_0 (j : Fin 2) (hj : j = 0) :
    DenseBivariatePolynomial.coefficientL1Norm (DenseEndpoint.fixedMap j) < 1 := by
  fin_cases j <;> cases hj
  all_goals norm_num [DenseBivariatePolynomial.coefficientL1Norm, DenseEndpoint.fixedMap,
      DenseEndpoint.balance, DenseEndpoint.gram, DenseEndpoint.scaledS, DenseEndpoint.scaledB,
      DenseBivariatePolynomial.add, DenseBivariatePolynomial.neg, DenseBivariatePolynomial.scale,
      DenseBivariatePolynomial.mul, DenseBivariatePolynomial.scaleRow, DenseBivariatePolynomial.pow,
      DenseBivariatePolynomial.constant, DenseBivariatePolynomial.first,
      DenseBivariatePolynomial.second, DenseUnivariate.add, DenseUnivariate.neg,
      DenseUnivariate.scale, DenseUnivariate.mul, DenseUnivariate.coefficientL1Norm]

private theorem endpointMapPolynomial_coefficientL1Norm_lt_one_1 (j : Fin 2) (hj : j = 1) :
    DenseBivariatePolynomial.coefficientL1Norm (DenseEndpoint.fixedMap j) < 1 := by
  fin_cases j <;> cases hj
  all_goals norm_num [DenseBivariatePolynomial.coefficientL1Norm, DenseEndpoint.fixedMap,
      DenseEndpoint.balance, DenseEndpoint.gram, DenseEndpoint.scaledS, DenseEndpoint.scaledB,
      DenseBivariatePolynomial.add, DenseBivariatePolynomial.neg, DenseBivariatePolynomial.scale,
      DenseBivariatePolynomial.mul, DenseBivariatePolynomial.scaleRow, DenseBivariatePolynomial.pow,
      DenseBivariatePolynomial.constant, DenseBivariatePolynomial.first,
      DenseBivariatePolynomial.second, DenseUnivariate.add, DenseUnivariate.neg,
      DenseUnivariate.scale, DenseUnivariate.mul, DenseUnivariate.coefficientL1Norm]

theorem endpointMapPolynomial_coefficientL1Norm_lt_one (i : Fin 2) :
    DenseBivariatePolynomial.coefficientL1Norm (DenseEndpoint.fixedMap i) < 1 := by
  fin_cases i
  · exact endpointMapPolynomial_coefficientL1Norm_lt_one_0 _ rfl
  · exact endpointMapPolynomial_coefficientL1Norm_lt_one_1 _ rfl

/-- The exact derivative certificate makes the fixed-point map a strict contraction. -/
private theorem endpointMapPolynomial_derivative_coefficientL1Norm_lt_0 (j : Fin 2) (hj : j = 0) :
    DenseBivariatePolynomial.coefficientL1Norm (DenseBivariatePolynomial.derivFirst (DenseEndpoint.fixedMap j)) +
      DenseBivariatePolynomial.coefficientL1Norm (DenseBivariatePolynomial.derivSecond (DenseEndpoint.fixedMap j)) <
      1 / 10 ^ 9 := by
  fin_cases j <;> cases hj
  all_goals norm_num [DenseBivariatePolynomial.coefficientL1Norm, DenseEndpoint.fixedMap,
      DenseEndpoint.balance, DenseEndpoint.gram, DenseEndpoint.scaledS, DenseEndpoint.scaledB,
      DenseBivariatePolynomial.add, DenseBivariatePolynomial.neg, DenseBivariatePolynomial.scale,
      DenseBivariatePolynomial.mul, DenseBivariatePolynomial.scaleRow, DenseBivariatePolynomial.pow,
      DenseBivariatePolynomial.constant, DenseBivariatePolynomial.first,
      DenseBivariatePolynomial.second, DenseBivariatePolynomial.derivFirst,
      DenseBivariatePolynomial.derivSecond, DenseUnivariate.add, DenseUnivariate.neg,
      DenseUnivariate.scale, DenseUnivariate.mul, DenseUnivariate.deriv,
      DenseUnivariate.coefficientL1Norm]

private theorem endpointMapPolynomial_derivative_coefficientL1Norm_lt_1 (j : Fin 2) (hj : j = 1) :
    DenseBivariatePolynomial.coefficientL1Norm (DenseBivariatePolynomial.derivFirst (DenseEndpoint.fixedMap j)) +
      DenseBivariatePolynomial.coefficientL1Norm (DenseBivariatePolynomial.derivSecond (DenseEndpoint.fixedMap j)) <
      1 / 10 ^ 9 := by
  fin_cases j <;> cases hj
  all_goals norm_num [DenseBivariatePolynomial.coefficientL1Norm, DenseEndpoint.fixedMap,
      DenseEndpoint.balance, DenseEndpoint.gram, DenseEndpoint.scaledS, DenseEndpoint.scaledB,
      DenseBivariatePolynomial.add, DenseBivariatePolynomial.neg, DenseBivariatePolynomial.scale,
      DenseBivariatePolynomial.mul, DenseBivariatePolynomial.scaleRow, DenseBivariatePolynomial.pow,
      DenseBivariatePolynomial.constant, DenseBivariatePolynomial.first,
      DenseBivariatePolynomial.second, DenseBivariatePolynomial.derivFirst,
      DenseBivariatePolynomial.derivSecond, DenseUnivariate.add, DenseUnivariate.neg,
      DenseUnivariate.scale, DenseUnivariate.mul, DenseUnivariate.deriv,
      DenseUnivariate.coefficientL1Norm]

theorem endpointMapPolynomial_derivative_coefficientL1Norm_lt (i : Fin 2) :
    DenseBivariatePolynomial.coefficientL1Norm
        (DenseBivariatePolynomial.derivFirst (DenseEndpoint.fixedMap i)) +
      DenseBivariatePolynomial.coefficientL1Norm
        (DenseBivariatePolynomial.derivSecond (DenseEndpoint.fixedMap i)) <
      1 / 10 ^ 9 := by
  fin_cases i
  · exact endpointMapPolynomial_derivative_coefficientL1Norm_lt_0 _ rfl
  · exact endpointMapPolynomial_derivative_coefficientL1Norm_lt_1 _ rfl

/-- The two normalized coordinates used by the endpoint certificate. -/
abbrev EndpointCertificateSpace := Fin 2 → ℝ

/-- The cleared endpoint equations evaluated in normalized coordinates. -/
def endpointCertificateSystem (x : EndpointCertificateSpace) : EndpointCertificateSpace :=
  ![DenseBivariatePolynomial.eval DenseEndpoint.balance (x 0) (x 1),
    DenseBivariatePolynomial.eval DenseEndpoint.gram (x 0) (x 1)]

/-- The preconditioned endpoint fixed-point map in normalized coordinates. -/
def endpointCertificateMap (x : EndpointCertificateSpace) : EndpointCertificateSpace := fun i ↦
  DenseBivariatePolynomial.eval (DenseEndpoint.fixedMap i) (x 0) (x 1)

/-- The closed unit box in the normalized coordinates. -/
def endpointCertificateBox : Set EndpointCertificateSpace := Metric.closedBall 0 1

/-- Decode the normalized first coordinate into the half-coordinate `s`. -/
def endpointCertificateS (u : EndpointCertificateSpace) : ℝ :=
  6933064218259049 / 10 ^ 16 + (1 / 10 ^ 16) * u 0

/-- Decode the normalized second coordinate into the distance coordinate `B`. -/
def endpointCertificateB (u : EndpointCertificateSpace) : ℝ :=
  5747488323603321 / (2 * 10 ^ 15) + (3 / (2 * 10 ^ 15)) * u 1

/-- The endpoint balance residual with its denominator cleared in half-coordinates. -/
def endpointBalanceCleared (s B : ℝ) : ℝ :=
  let q := 2 * s + 1
  let p := 2 * B - 12 * s ^ 2 + 4 * s - 1
  let D := 16 * s ^ 2 - 4 * s - B
  let A2 := (B ^ 2 - 1) / 2
  let C2 := (B ^ 2 + D ^ 2) / 2 - 4 * s ^ 2
  let K := 6 * s * p + (4 * s ^ 2 - 1) * q
  (K ^ 2 - (A2 + C2) * q ^ 2) ^ 2 - 4 * A2 * C2 * q ^ 4

/-- The endpoint Gram residual with its denominator cleared in half-coordinates. -/
def endpointGramCleared (s B : ℝ) : ℝ :=
  let q := 2 * s + 1
  let p := 2 * B - 12 * s ^ 2 + 4 * s - 1
  let D := 16 * s ^ 2 - 4 * s - B
  let x := 5 - B ^ 2
  let z := q ^ 2 + 4 * p ^ 2 - D ^ 2 * q ^ 2
  let k := (1 - 4 * s ^ 2) * q ^ 2 + p ^ 2
  ((8 * k - x * z) ^ 2 - (16 - x ^ 2) * (16 * p ^ 2 * q ^ 2 - z ^ 2)) / 64

theorem DenseEndpoint.eval_scaledS (u : EndpointCertificateSpace) :
    DenseBivariatePolynomial.eval DenseEndpoint.scaledS (u 0) (u 1) =
      endpointCertificateS u := by
  simp [DenseEndpoint.scaledS, endpointCertificateS, DenseBivariatePolynomial.eval_add,
    DenseBivariatePolynomial.eval_scale, DenseBivariatePolynomial.eval_constant,
    DenseBivariatePolynomial.eval_first]

theorem DenseEndpoint.eval_scaledB (u : EndpointCertificateSpace) :
    DenseBivariatePolynomial.eval DenseEndpoint.scaledB (u 0) (u 1) =
      endpointCertificateB u := by
  simp [DenseEndpoint.scaledB, endpointCertificateB, DenseBivariatePolynomial.eval_add,
    DenseBivariatePolynomial.eval_scale, DenseBivariatePolynomial.eval_constant,
    DenseBivariatePolynomial.eval_second]

theorem DenseEndpoint.eval_balance (u : EndpointCertificateSpace) :
    DenseBivariatePolynomial.eval DenseEndpoint.balance (u 0) (u 1) =
      endpointBalanceCleared (endpointCertificateS u) (endpointCertificateB u) := by
  simp only [DenseEndpoint.balance, DenseBivariatePolynomial.eval_add,
    DenseBivariatePolynomial.eval_neg, DenseBivariatePolynomial.eval_scale,
    DenseBivariatePolynomial.eval_mul, DenseBivariatePolynomial.eval_pow,
    DenseBivariatePolynomial.eval_constant, DenseEndpoint.eval_scaledS,
    DenseEndpoint.eval_scaledB, endpointBalanceCleared]
  ring

theorem DenseEndpoint.eval_gram (u : EndpointCertificateSpace) :
    DenseBivariatePolynomial.eval DenseEndpoint.gram (u 0) (u 1) =
      endpointGramCleared (endpointCertificateS u) (endpointCertificateB u) := by
  simp only [DenseEndpoint.gram, DenseBivariatePolynomial.eval_add,
    DenseBivariatePolynomial.eval_neg, DenseBivariatePolynomial.eval_scale,
    DenseBivariatePolynomial.eval_mul, DenseBivariatePolynomial.eval_pow,
    DenseBivariatePolynomial.eval_constant, DenseEndpoint.eval_scaledS,
    DenseEndpoint.eval_scaledB, endpointGramCleared]
  ring

private theorem balance_clear_denominator (q K A C : ℝ) (hq : q ≠ 0) :
    q ^ 4 * (((K / q) ^ 2 - A - C) ^ 2 - 4 * A * C) =
      (K ^ 2 - (A + C) * q ^ 2) ^ 2 - 4 * A * C * q ^ 4 := by
  field_simp [hq]
  ring

theorem endpointBalanceCleared_eq (s B : ℝ) (hq : 2 * s + 1 ≠ 0) :
    endpointBalanceCleared s B =
      (2 * s + 1) ^ 4 * endpointBalanceResidual (2 * s) B := by
  let q := 2 * s + 1
  let p := 2 * B - 12 * s ^ 2 + 4 * s - 1
  let D := 16 * s ^ 2 - 4 * s - B
  let A2 := (B ^ 2 - 1) / 2
  let C2 := (B ^ 2 + D ^ 2) / 2 - 4 * s ^ 2
  let K := 6 * s * p + (4 * s ^ 2 - 1) * q
  have hR : 6 * s * (p / q) + 4 * s ^ 2 - 1 = K / q := by
    field_simp [q, hq]
    simp only [K, p]
    ring
  have hb₀ : 2 * B - 3 * (2 * s) ^ 2 + 2 * (2 * s) - 1 = p := by
    simp only [p]
    ring
  have hD₀ : 4 * (2 * s) ^ 2 - 2 * (2 * s) - B = D := by
    simp only [D]
    ring
  have hc₀ : (2 * s) ^ 2 = 4 * s ^ 2 := by ring
  rw [endpointBalanceResidual, hb₀, hD₀, hc₀]
  rw [show 3 * (2 * s) * (p / (2 * s + 1)) + 4 * s ^ 2 - 1 =
    6 * s * (p / q) + 4 * s ^ 2 - 1 by simp only [q]; ring]
  change endpointBalanceCleared s B = q ^ 4 *
    (((6 * s * (p / q) + 4 * s ^ 2 - 1) ^ 2 - A2 - C2) ^ 2 - 4 * A2 * C2)
  rw [hR, endpointBalanceCleared]
  exact (balance_clear_denominator q K A2 C2 hq).symm

private theorem gram_clear_denominator (q p x z k : ℝ) (hq : q ≠ 0) :
    4 * q ^ 4 * ((k / (2 * q ^ 2) - x / 4 * (z / (4 * q ^ 2))) ^ 2 -
      (1 - (x / 4) ^ 2) * ((p / q) ^ 2 - (z / (4 * q ^ 2)) ^ 2)) =
      ((8 * k - x * z) ^ 2 - (16 - x ^ 2) * (16 * p ^ 2 * q ^ 2 - z ^ 2)) / 64 := by
  field_simp [hq]
  ring

theorem endpointGramCleared_eq (s B : ℝ) (hq : 2 * s + 1 ≠ 0) :
    endpointGramCleared s B = 4 * (2 * s + 1) ^ 4 * endpointGramResidual (2 * s) B := by
  let q := 2 * s + 1
  let p := 2 * B - 12 * s ^ 2 + 4 * s - 1
  let D := 16 * s ^ 2 - 4 * s - B
  let x := 5 - B ^ 2
  let z := q ^ 2 + 4 * p ^ 2 - D ^ 2 * q ^ 2
  let k := (1 - 4 * s ^ 2) * q ^ 2 + p ^ 2
  have hz : (1 + 4 * (p / q) ^ 2 - D ^ 2) / 4 = z / (4 * q ^ 2) := by
    field_simp [q, hq]
    simp only [z]
    ring
  have hk : (1 + (p / q) ^ 2 - 4 * s ^ 2) / 2 = k / (2 * q ^ 2) := by
    field_simp [q, hq]
    simp only [k]
    ring
  have hb₀ : 2 * B - 3 * (2 * s) ^ 2 + 2 * (2 * s) - 1 = p := by
    simp only [p]
    ring
  have hD₀ : 4 * (2 * s) ^ 2 - 2 * (2 * s) - B = D := by
    simp only [D]
    ring
  have hc₀ : (2 * s) ^ 2 = 4 * s ^ 2 := by ring
  rw [endpointGramResidual, hb₀, hD₀, hc₀]
  change endpointGramCleared s B = 4 * q ^ 4 *
    (((1 + (p / q) ^ 2 - 4 * s ^ 2) / 2 - (x / 4) *
      ((1 + 4 * (p / q) ^ 2 - D ^ 2) / 4)) ^ 2 -
      (1 - (x / 4) ^ 2) * ((p / q) ^ 2 -
        ((1 + 4 * (p / q) ^ 2 - D ^ 2) / 4) ^ 2))
  rw [hz, hk, endpointGramCleared]
  exact (gram_clear_denominator q p x z k hq).symm

private theorem endpoint_auxiliary_bounds {s B : ℝ} (hsL : (6933 / 10000 : ℝ) < s)
    (hsU : s < (6934 / 10000 : ℝ)) (hBL : (28737 / 10000 : ℝ) < B)
    (hBU : B < (28738 / 10000 : ℝ)) :
    let D := 16 * s ^ 2 - 4 * s - B
    let b := (2 * B - 12 * s ^ 2 + 4 * s - 1) / (2 * s + 1)
    (73 / 100 : ℝ) < b ∧ b < 74 / 100 ∧ 2 < D ∧ D < 21 / 10 := by
  let q := 2 * s + 1
  let p := 2 * B - 12 * s ^ 2 + 4 * s - 1
  let D := 16 * s ^ 2 - 4 * s - B
  let b := p / q
  have hq : 0 < q := by dsimp [q]; linarith
  have hpL : (73 / 100 : ℝ) * q < p := by
    dsimp [p, q]
    nlinarith [sq_nonneg (s - 6934 / 10000)]
  have hpU : p < (74 / 100 : ℝ) * q := by
    dsimp [p, q]
    nlinarith [sq_nonneg (s - 6933 / 10000)]
  have hbL : (73 / 100 : ℝ) < b := (lt_div_iff₀ hq).2 hpL
  have hbU : b < (74 / 100 : ℝ) := (div_lt_iff₀ hq).2 hpU
  have hDL : (2 : ℝ) < D := by
    dsimp [D]
    nlinarith [sq_nonneg (s - 6933 / 10000)]
  have hDU : D < (21 / 10 : ℝ) := by
    dsimp [D]
    nlinarith [sq_nonneg (s - 6934 / 10000)]
  exact ⟨hbL, hbU, hDL, hDU⟩

private theorem endpoint_signs {s B : ℝ} (hsL : (6933 / 10000 : ℝ) < s)
    (hsU : s < (6934 / 10000 : ℝ)) (hBL : (28737 / 10000 : ℝ) < B)
    (hBU : B < (28738 / 10000 : ℝ)) :
    let D := 16 * s ^ 2 - 4 * s - B
    let b := (2 * B - 12 * s ^ 2 + 4 * s - 1) / (2 * s + 1)
    let A2 := (B ^ 2 - 1) / 2
    let C2 := (B ^ 2 + D ^ 2) / 2 - 4 * s ^ 2
    let R := 6 * s * b + 4 * s ^ 2 - 1
    let x := (5 - B ^ 2) / 4
    let z := (1 + 4 * b ^ 2 - D ^ 2) / 4
    let k := (1 + b ^ 2 - 4 * s ^ 2) / 2
    0 < A2 ∧ 0 < C2 ∧ 0 < R ∧ 0 < R ^ 2 - A2 - C2 ∧
      x < 0 ∧ z < 0 ∧ k - x * z < 0 := by
  let q := 2 * s + 1
  let p := 2 * B - 12 * s ^ 2 + 4 * s - 1
  let D := 16 * s ^ 2 - 4 * s - B
  let b := p / q
  let A2 := (B ^ 2 - 1) / 2
  let C2 := (B ^ 2 + D ^ 2) / 2 - 4 * s ^ 2
  let R := 6 * s * b + 4 * s ^ 2 - 1
  let x := (5 - B ^ 2) / 4
  let z := (1 + 4 * b ^ 2 - D ^ 2) / 4
  let k := (1 + b ^ 2 - 4 * s ^ 2) / 2
  have hbounds := endpoint_auxiliary_bounds hsL hsU hBL hBU
  change (73 / 100 : ℝ) < b ∧ b < 74 / 100 ∧ 2 < D ∧ D < 21 / 10 at hbounds
  rcases hbounds with ⟨hbL, hbU, hDL, hDU⟩
  have hA : 0 < A2 := by
    dsimp [A2]
    nlinarith [sq_nonneg (B - 28737 / 10000)]
  have hC : 0 < C2 := by
    dsimp [C2]
    nlinarith [sq_nonneg B, sq_nonneg D, sq_nonneg s]
  have hR : (19 / 5 : ℝ) < R := by
    dsimp [R]
    nlinarith [mul_pos (sub_pos.mpr hsL) (sub_pos.mpr hbL), sq_nonneg s]
  have hAupper : A2 < 4 := by
    dsimp [A2]
    nlinarith [sq_nonneg (B - 28738 / 10000)]
  have hCupper : C2 < (9 / 2 : ℝ) := by
    dsimp [C2]
    nlinarith [sq_nonneg (B - 28738 / 10000), sq_nonneg (D - 21 / 10),
      sq_nonneg (s - 6933 / 10000)]
  have hQ : 0 < R ^ 2 - A2 - C2 := by
    nlinarith [sq_nonneg (R - 19 / 5)]
  have hx : x < 0 := by
    dsimp [x]
    nlinarith [sq_nonneg (B - 28737 / 10000)]
  have hz : z < 0 := by
    dsimp [z]
    nlinarith [sq_nonneg (b - 74 / 100), sq_nonneg (D - 2)]
  have hk : k < 0 := by
    dsimp [k]
    nlinarith [sq_nonneg (b - 74 / 100), sq_nonneg (s - 6933 / 10000)]
  have hkxz : k - x * z < 0 := by
    nlinarith [mul_pos (neg_pos.mpr hx) (neg_pos.mpr hz)]
  dsimp only [D, b, A2, C2, R, x, z, k]
  exact ⟨hA, hC, (by norm_num : (0 : ℝ) < 19 / 5).trans hR, hQ, hx, hz, hkxz⟩

private theorem abs_apply_le_one_of_mem_endpointCertificateBox {x : EndpointCertificateSpace}
    (hx : x ∈ endpointCertificateBox) (i : Fin 2) : |x i| ≤ 1 := by
  rw [← Real.norm_eq_abs]
  exact (norm_le_pi_norm x i).trans (by simpa [endpointCertificateBox] using hx)

/-- The exact coefficient enclosure makes the certificate map preserve its unit box. -/
theorem endpointCertificateMap_mapsTo :
    MapsTo endpointCertificateMap endpointCertificateBox endpointCertificateBox := by
  intro x hx
  have hx₀ := abs_apply_le_one_of_mem_endpointCertificateBox hx 0
  have hx₁ := abs_apply_le_one_of_mem_endpointCertificateBox hx 1
  rw [endpointCertificateBox, Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs]
  refine (DenseBivariatePolynomial.abs_eval_le_coefficientL1Norm
    (DenseEndpoint.fixedMap i) hx₀ hx₁).trans ?_
  exact_mod_cast (endpointMapPolynomial_coefficientL1Norm_lt_one i).le

private theorem endpointCertificateMap_coordinate_sub_le (i : Fin 2)
    {x y : EndpointCertificateSpace} (hx : x ∈ endpointCertificateBox)
    (hy : y ∈ endpointCertificateBox) :
    |endpointCertificateMap y i - endpointCertificateMap x i| ≤
      (1 / 10 ^ 9 : ℝ) * ‖y - x‖ := by
  let p := DenseEndpoint.fixedMap i
  let a : ℝ := DenseBivariatePolynomial.coefficientL1Norm
    (DenseBivariatePolynomial.derivFirst p)
  let b : ℝ := DenseBivariatePolynomial.coefficientL1Norm
    (DenseBivariatePolynomial.derivSecond p)
  have hx₀ := abs_apply_le_one_of_mem_endpointCertificateBox hx 0
  have hx₁ := abs_apply_le_one_of_mem_endpointCertificateBox hx 1
  have hy₀ := abs_apply_le_one_of_mem_endpointCertificateBox hy 0
  have hy₁ := abs_apply_le_one_of_mem_endpointCertificateBox hy 1
  have h₀ : |y 0 - x 0| ≤ ‖y - x‖ := by
    rw [← Real.norm_eq_abs]
    simpa only [Pi.sub_apply] using norm_le_pi_norm (y - x) 0
  have h₁ : |y 1 - x 1| ≤ ‖y - x‖ := by
    rw [← Real.norm_eq_abs]
    simpa only [Pi.sub_apply] using norm_le_pi_norm (y - x) 1
  have ha : |DenseBivariatePolynomial.eval p (y 0) (y 1) -
      DenseBivariatePolynomial.eval p (x 0) (y 1)| ≤ a * |y 0 - x 0| :=
    DenseBivariatePolynomial.abs_eval_sub_le_derivFirst p hx₀ hy₀ hy₁
  have hb : |DenseBivariatePolynomial.eval p (x 0) (y 1) -
      DenseBivariatePolynomial.eval p (x 0) (x 1)| ≤ b * |y 1 - x 1| :=
    DenseBivariatePolynomial.abs_eval_sub_le_derivSecond p hx₀ hx₁ hy₁
  have hab : a + b < (1 / 10 ^ 9 : ℝ) := by
    dsimp [a, b, p]
    have h := endpointMapPolynomial_derivative_coefficientL1Norm_lt i
    have h' := (Rat.cast_lt (K := ℝ)).mpr h
    norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] at h'
    norm_num at h' ⊢
    exact h'
  have ha₀ : 0 ≤ a := by
    dsimp [a]
    exact_mod_cast DenseBivariatePolynomial.coefficientL1Norm_nonneg
      (DenseBivariatePolynomial.derivFirst p)
  have hb₀ : 0 ≤ b := by
    dsimp [b]
    exact_mod_cast DenseBivariatePolynomial.coefficientL1Norm_nonneg
      (DenseBivariatePolynomial.derivSecond p)
  rw [endpointCertificateMap]
  change |DenseBivariatePolynomial.eval p (y 0) (y 1) -
    DenseBivariatePolynomial.eval p (x 0) (x 1)| ≤ _
  calc
    _ = |(DenseBivariatePolynomial.eval p (y 0) (y 1) -
          DenseBivariatePolynomial.eval p (x 0) (y 1)) +
        (DenseBivariatePolynomial.eval p (x 0) (y 1) -
          DenseBivariatePolynomial.eval p (x 0) (x 1))| := by ring_nf
    _ ≤ |DenseBivariatePolynomial.eval p (y 0) (y 1) -
          DenseBivariatePolynomial.eval p (x 0) (y 1)| +
        |DenseBivariatePolynomial.eval p (x 0) (y 1) -
          DenseBivariatePolynomial.eval p (x 0) (x 1)| := abs_add_le _ _
    _ ≤ a * |y 0 - x 0| + b * |y 1 - x 1| := add_le_add ha hb
    _ ≤ a * ‖y - x‖ + b * ‖y - x‖ := add_le_add
      (mul_le_mul_of_nonneg_left h₀ ha₀) (mul_le_mul_of_nonneg_left h₁ hb₀)
    _ = (a + b) * ‖y - x‖ := by ring
    _ ≤ (1 / 10 ^ 9 : ℝ) * ‖y - x‖ :=
      mul_le_mul_of_nonneg_right hab.le (norm_nonneg _)

/-- The normalized fixed-point map is Lipschitz with exact constant `10⁻⁹`. -/
theorem endpointCertificateMap_lipschitzOn :
    LipschitzOnWith (1 / 10 ^ 9 : ℝ≥0) endpointCertificateMap endpointCertificateBox := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [dist_eq_norm, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs, Pi.sub_apply]
  exact endpointCertificateMap_coordinate_sub_le i hy hx

/-- The normalized fixed-point map is a certified strict contraction. -/
theorem endpointCertificateMap_contracting :
    ContractingWith (1 / 10 ^ 9 : ℝ≥0)
      (endpointCertificateMap_mapsTo.restrict endpointCertificateMap
        endpointCertificateBox endpointCertificateBox) := by
  exact ⟨by norm_num, endpointCertificateMap_lipschitzOn.mapsToRestrict
    endpointCertificateMap_mapsTo⟩

/-- The rational preconditioner as a real linear map. -/
def endpointCertificatePreconditioner :
    EndpointCertificateSpace →ₗ[ℝ] EndpointCertificateSpace where
  toFun y := ![68748375835 * y 0 + 4033169260133 * y 1,
    104924796527 * y 0 + 2365005784960 * y 1]
  map_add' := by
    intro x y
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' := by
    intro a x
    funext i
    fin_cases i <;> simp <;> ring

theorem endpointCertificateMap_eq_update (x : EndpointCertificateSpace) :
    endpointCertificateMap x =
      x - endpointCertificatePreconditioner (endpointCertificateSystem x) := by
  funext i
  fin_cases i <;>
    simp [endpointCertificateMap, endpointCertificateSystem, endpointCertificatePreconditioner,
      DenseEndpoint.fixedMap, DenseBivariatePolynomial.eval_add,
      DenseBivariatePolynomial.eval_neg, DenseBivariatePolynomial.eval_scale,
      DenseBivariatePolynomial.eval_first, DenseBivariatePolynomial.eval_second] <;> ring

theorem endpointCertificatePreconditioner_injective :
    Function.Injective endpointCertificatePreconditioner := by
  intro x y h
  have h₀ := congrFun h 0
  have h₁ := congrFun h 1
  change 68748375835 * x 0 + 4033169260133 * x 1 =
    68748375835 * y 0 + 4033169260133 * y 1 at h₀
  change 104924796527 * x 0 + 2365005784960 * x 1 =
    104924796527 * y 0 + 2365005784960 * y 1 at h₁
  funext i
  fin_cases i
  · change x 0 = y 0
    linarith [h₀, h₁]
  · change x 1 = y 1
    linarith [h₀, h₁]

/-- The exact contraction certificate isolates a unique normalized fixed point. -/
theorem existsUnique_endpointCertificate_fixedPoint :
    ∃! x, x ∈ endpointCertificateBox ∧ IsFixedPt endpointCertificateMap x := by
  refine existsUnique_fixedPoint_mem (K := (1 / 10 ^ 9 : ℝ≥0))
    ⟨0, by simp [endpointCertificateBox]⟩
    Metric.isClosed_closedBall.isComplete endpointCertificateMap_mapsTo ?_
  simpa only using endpointCertificateMap_contracting

/-- The exact certificate isolates a unique zero of the cleared endpoint system. -/
theorem existsUnique_endpointCertificate_zero :
    ∃! x, x ∈ endpointCertificateBox ∧ endpointCertificateSystem x = 0 := by
  refine existsUnique_zero_of_contracting_preconditioner
    (K := (1 / 10 ^ 9 : ℝ≥0)) ⟨0, by simp [endpointCertificateBox]⟩
      Metric.isClosed_closedBall.isComplete endpointCertificateMap_mapsTo ?_
      (fun x _ ↦ endpointCertificateMap_eq_update x)
      endpointCertificatePreconditioner_injective
  simpa only using endpointCertificateMap_contracting

private theorem endpointCertificate_coordinate_lt_one {u : EndpointCertificateSpace}
    (hu : u ∈ endpointCertificateBox) (hfixed : endpointCertificateMap u = u) (i : Fin 2) :
    |u i| < 1 := by
  rw [← congrFun hfixed i]
  exact (DenseBivariatePolynomial.abs_eval_le_coefficientL1Norm
    (DenseEndpoint.fixedMap i) (abs_apply_le_one_of_mem_endpointCertificateBox hu 0)
    (abs_apply_le_one_of_mem_endpointCertificateBox hu 1)).trans_lt
      (by exact_mod_cast endpointMapPolynomial_coefficientL1Norm_lt_one i)

private theorem isEndpointPolynomialPair_of_endpointCertificate_zero
    {u : EndpointCertificateSpace} (hu : u ∈ endpointCertificateBox)
    (hzero : endpointCertificateSystem u = 0) :
    IsEndpointPolynomialPair (2 * endpointCertificateS u) (endpointCertificateB u) := by
  let s := endpointCertificateS u
  let B := endpointCertificateB u
  have hfixed : endpointCertificateMap u = u := by
    rw [endpointCertificateMap_eq_update, hzero, map_zero, sub_zero]
  have hu₀ := abs_lt.mp (endpointCertificate_coordinate_lt_one hu hfixed 0)
  have hu₁ := abs_lt.mp (endpointCertificate_coordinate_lt_one hu hfixed 1)
  have hsL : 6933064218259048 / 10 ^ 16 < s := by
    dsimp [s, endpointCertificateS]
    norm_num at hu₀ ⊢
    linarith
  have hsU : s < 6933064218259050 / 10 ^ 16 := by
    dsimp [s, endpointCertificateS]
    norm_num at hu₀ ⊢
    linarith
  have hBL : 2873744161801659 / 10 ^ 15 < B := by
    dsimp [B, endpointCertificateB]
    norm_num at hu₁ ⊢
    linarith
  have hBU : B < 2873744161801662 / 10 ^ 15 := by
    dsimp [B, endpointCertificateB]
    norm_num at hu₁ ⊢
    linarith
  have hq : 2 * s + 1 ≠ 0 := by
    have : 0 < s := by norm_num at hsL ⊢; linarith
    positivity
  have hbalance := congrFun hzero 0
  have hgram := congrFun hzero 1
  change DenseBivariatePolynomial.eval DenseEndpoint.balance (u 0) (u 1) = 0 at hbalance
  change DenseBivariatePolynomial.eval DenseEndpoint.gram (u 0) (u 1) = 0 at hgram
  rw [DenseEndpoint.eval_balance, endpointBalanceCleared_eq _ _ hq] at hbalance
  rw [DenseEndpoint.eval_gram, endpointGramCleared_eq _ _ hq] at hgram
  have hbalance' : endpointBalanceResidual (2 * s) B = 0 := by
    exact (mul_eq_zero.mp hbalance).resolve_left (pow_ne_zero 4 hq)
  have hgram' : endpointGramResidual (2 * s) B = 0 := by
    rcases mul_eq_zero.mp hgram with hcoeff | hres
    · have hpow := (mul_eq_zero.mp hcoeff).resolve_left (by norm_num : (4 : ℝ) ≠ 0)
      exact (pow_ne_zero 4 hq hpow).elim
    · exact hres
  have hsigns := endpoint_signs (s := s) (B := B)
    (by norm_num at hsL ⊢; linarith) (by norm_num at hsU ⊢; linarith)
    (by norm_num at hBL ⊢; linarith) (by norm_num at hBU ⊢; linarith)
  dsimp only [IsEndpointPolynomialPair]
  refine ⟨by nlinarith [hsL], by nlinarith [hsU], hBL, hBU, ?_, ?_, ?_, ?_,
    hbalance', hgram', ?_, ?_, ?_⟩
  · exact hsigns.1
  · convert hsigns.2.1 using 1; ring
  · convert hsigns.2.2.1 using 1; ring
  · convert hsigns.2.2.2.1 using 1; ring
  · exact hsigns.2.2.2.2.1
  · convert hsigns.2.2.2.2.2.1 using 1; ring
  · convert hsigns.2.2.2.2.2.2 using 1; ring

/-- There exists an endpoint polynomial pair in the stated strict rational box. -/
theorem exists_isEndpointPolynomialPair : ∃ c B : ℝ, IsEndpointPolynomialPair c B := by
  obtain ⟨u, hu, -⟩ := existsUnique_endpointCertificate_zero
  exact ⟨2 * endpointCertificateS u, endpointCertificateB u,
    isEndpointPolynomialPair_of_endpointCertificate_zero hu.1 hu.2⟩

/-- Normalize a pair `(c, B)` into the centered certificate coordinates. -/
def endpointCertificateCoordinates (c B : ℝ) : EndpointCertificateSpace :=
  ![10 ^ 16 * (c / 2 - 6933064218259049 / 10 ^ 16),
    (2 * 10 ^ 15 / 3) * (B - 5747488323603321 / (2 * 10 ^ 15))]

@[simp]
theorem endpointCertificateS_coordinates (c B : ℝ) :
    endpointCertificateS (endpointCertificateCoordinates c B) = c / 2 := by
  simp [endpointCertificateS, endpointCertificateCoordinates]

@[simp]
theorem endpointCertificateB_coordinates (c B : ℝ) :
    endpointCertificateB (endpointCertificateCoordinates c B) = B := by
  simp [endpointCertificateB, endpointCertificateCoordinates]
  ring

private theorem endpointCertificateCoordinates_mem_box {c B : ℝ}
    (hcL : 13866128436518096 / 10 ^ 16 < c)
    (hcU : c < 13866128436518100 / 10 ^ 16)
    (hBL : 2873744161801659 / 10 ^ 15 < B)
    (hBU : B < 2873744161801662 / 10 ^ 15) :
    endpointCertificateCoordinates c B ∈ endpointCertificateBox := by
  rw [endpointCertificateBox, Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  fin_cases i <;> rw [Real.norm_eq_abs, abs_le] <;>
    constructor <;> simp only [endpointCertificateCoordinates] <;>
      norm_num at hcL hcU hBL hBU ⊢ <;> linarith

private theorem endpointCertificateSystem_coordinates_eq_zero {c B : ℝ} (hc : 0 < c)
    (hbalance : endpointBalanceResidual c B = 0)
    (hgram : endpointGramResidual c B = 0) :
    endpointCertificateSystem (endpointCertificateCoordinates c B) = 0 := by
  have hq : 2 * (c / 2) + 1 ≠ 0 := by nlinarith
  have hc₂ : 2 * (c / 2) = c := by ring
  funext i
  fin_cases i
  · change DenseBivariatePolynomial.eval DenseEndpoint.balance
      (endpointCertificateCoordinates c B 0) (endpointCertificateCoordinates c B 1) = 0
    rw [DenseEndpoint.eval_balance, endpointCertificateS_coordinates,
      endpointCertificateB_coordinates, endpointBalanceCleared_eq _ _ hq, hc₂, hbalance,
      mul_zero]
  · change DenseBivariatePolynomial.eval DenseEndpoint.gram
      (endpointCertificateCoordinates c B 0) (endpointCertificateCoordinates c B 1) = 0
    rw [DenseEndpoint.eval_gram, endpointCertificateS_coordinates,
      endpointCertificateB_coordinates, endpointGramCleared_eq _ _ hq, hc₂, hgram, mul_zero]

private theorem endpointCertificate_of_isEndpointPolynomialPair {c B : ℝ}
    (h : IsEndpointPolynomialPair c B) :
    endpointCertificateCoordinates c B ∈ endpointCertificateBox ∧
      endpointCertificateSystem (endpointCertificateCoordinates c B) = 0 := by
  simp only [IsEndpointPolynomialPair] at h
  rcases h with ⟨hcL, hcU, hBL, hBU, -, -, -, -, hbalance, hgram, -, -, -⟩
  exact ⟨endpointCertificateCoordinates_mem_box hcL hcU hBL hBU,
    endpointCertificateSystem_coordinates_eq_zero
      (by norm_num at hcL ⊢; linarith) hbalance hgram⟩

/-- The signed polynomial endpoint system has exactly one solution in its stated box. -/
theorem existsUnique_isEndpointPolynomialPair :
    ∃! p : ℝ × ℝ, IsEndpointPolynomialPair p.1 p.2 := by
  obtain ⟨u, hu, hunique⟩ := existsUnique_endpointCertificate_zero
  let p : ℝ × ℝ := (2 * endpointCertificateS u, endpointCertificateB u)
  have hp : IsEndpointPolynomialPair p.1 p.2 :=
    isEndpointPolynomialPair_of_endpointCertificate_zero hu.1 hu.2
  refine ⟨p, hp, ?_⟩
  intro q hq
  have heq := hunique (endpointCertificateCoordinates q.1 q.2)
    (endpointCertificate_of_isEndpointPolynomialPair hq)
  apply Prod.ext
  · have hs := congrArg endpointCertificateS heq
    rw [endpointCertificateS_coordinates] at hs
    change q.1 = 2 * endpointCertificateS u
    nlinarith
  · have hB := congrArg endpointCertificateB heq
    rw [endpointCertificateB_coordinates] at hB
    exact hB

end LeanPool.Besicovitch

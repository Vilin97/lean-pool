/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.RPolynomial.Basic
public import LeanPool.CarlsonFunctions.Carlson.RPolynomial.Transform
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-! # Two-variable Carlson R-polynomials -/

open Complex
@[expose] public noncomputable section CarlsonTwoVariable
namespace DirichletTransform.TwoVariable

/-- The explicit Pochhammer numerator of a two-variable Carlson R-polynomial. This form is
well-defined at all parameter values, including zeros of the usual normalizing Pochhammer
symbol. -/
def carlsonRPolynomialNumerator₂ (n : ℕ) (b₀ b₁ x y : ℂ) : ℂ :=
  ∑ ij ∈ Finset.antidiagonal n,
    (Nat.choose n ij.1 : ℂ) *
      (ascPochhammer ℂ ij.1).eval b₀ *
      (ascPochhammer ℂ ij.2).eval b₁ * x ^ ij.1 * y ^ ij.2

/-- The affine polynomial for a pair is the expected two-term linear polynomial. -/
theorem carlsonAffinePolynomial_pair (x y : ℂ) :
    carlsonAffinePolynomial (pair x y) =
      MvPolynomial.C x * MvPolynomial.X 0 + MvPolynomial.C y * MvPolynomial.X 1 := by
  simp [carlsonAffinePolynomial, pair, Fin.sum_univ_two]

/-- The explicit two-variable Pochhammer numerator agrees with the specialization of the
general multivariate numerator to `Fin 2`. -/
theorem carlsonRPolynomialNumerator_pair (n : ℕ) (b₀ b₁ x y : ℂ) :
    carlsonRPolynomialNumerator n (pair b₀ b₁) (pair x y) =
      carlsonRPolynomialNumerator₂ n b₀ b₁ x y := by
  unfold carlsonRPolynomialNumerator carlsonRPolynomialNumerator₂
  let p := carlsonPowerPolynomial n (pair x y)
  calc
    ∑ m ∈ p.support,
        (m.multinomial : ℂ) * m.prod (fun i e ↦ pair x y i ^ e) *
          ∏ i, (ascPochhammer ℂ (m i)).eval (pair b₀ b₁ i) =
      ∑ m ∈ p.support, p.coeff m *
          ∏ i, (ascPochhammer ℂ (m i)).eval (pair b₀ b₁ i) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hmdeg : m.sum (fun _ e ↦ e) = n := by
          by_contra hne
          exact (MvPolynomial.mem_support_iff.mp hm)
            (coeff_carlsonPowerPolynomial_eq_zero_of_sum_ne n (pair x y) m hne)
        rw [coeff_carlsonPowerPolynomial]
        simp [hmdeg]
    _ = (AddMonoidAlgebra.coeff p).sum (fun m c ↦ c *
          ∏ i, (ascPochhammer ℂ (m i)).eval (pair b₀ b₁ i)) := by
      rw [MvPolynomial.sum_def]
    _ = _ := by
      let weight : (Fin 2 →₀ ℕ) → ℂ := fun m ↦
        ∏ i, (ascPochhammer ℂ (m i)).eval (pair b₀ b₁ i)
      let L : ((Fin 2 →₀ ℕ) →₀ ℂ) →ₗ[ℂ] ℂ :=
        Finsupp.lsum ℂ (fun m ↦ LinearMap.mulRight ℂ (weight m))
      change L (AddMonoidAlgebra.coeff p) = _
      dsimp [p]
      rw [carlsonPowerPolynomial, carlsonAffinePolynomial_pair, add_pow]
      have hcoeff : AddMonoidAlgebra.coeff
          (∑ m ∈ Finset.range (n + 1),
            (MvPolynomial.C x * MvPolynomial.X 0) ^ m *
              (MvPolynomial.C y * MvPolynomial.X 1) ^ (n - m) *
                (n.choose m : MvPolynomial (Fin 2) ℂ)) =
          ∑ m ∈ Finset.range (n + 1), AddMonoidAlgebra.coeff
            ((MvPolynomial.C x * MvPolynomial.X 0) ^ m *
              (MvPolynomial.C y * MvPolynomial.X 1) ^ (n - m) *
                (n.choose m : MvPolynomial (Fin 2) ℂ)) := by
        ext d
        simp
      rw [hcoeff, map_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      apply Finset.sum_congr rfl
      intro m hm
      rw [MvPolynomial.C_mul_X_eq_monomial, MvPolynomial.C_mul_X_eq_monomial,
        MvPolynomial.monomial_pow, MvPolynomial.monomial_pow,
        MvPolynomial.monomial_mul_monomial]
      rw [show (n.choose m : MvPolynomial (Fin 2) ℂ) = MvPolynomial.C (n.choose m : ℂ) by rfl,
        mul_comm, MvPolynomial.C_mul_monomial]
      change L (Finsupp.single _ _) = _
      rw [Finsupp.lsum_single]
      have hi0 : ((m • Finsupp.single (0 : Fin 2) 1 +
          (n - m) • Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ)) 0 = m := by simp
      have hi1 : ((m • Finsupp.single (0 : Fin 2) 1 +
          (n - m) • Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ)) 1 = n - m := by simp
      simp only [LinearMap.mulRight_apply, weight, pair, Fin.prod_univ_two,
        Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hi0, hi1]
      ring

/-- Simultaneously exchanging the two parameters and variables leaves the two-variable
Pochhammer numerator unchanged. -/
theorem carlsonRPolynomialNumerator₂_swap (n : ℕ) (b₀ b₁ x y : ℂ) :
    carlsonRPolynomialNumerator₂ n b₁ b₀ y x =
      carlsonRPolynomialNumerator₂ n b₀ b₁ x y := by
  unfold carlsonRPolynomialNumerator₂
  rw [← Finset.Nat.sum_antidiagonal_swap]
  apply Finset.sum_congr rfl
  intro ij hij
  have hs : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  rw [Nat.choose_symm_of_eq_add hs.symm]
  change (Nat.choose n ij.2 : ℂ) *
      (ascPochhammer ℂ ij.2).eval b₁ * (ascPochhammer ℂ ij.1).eval b₀ *
        y ^ ij.2 * x ^ ij.1 = _
  ring

/-- Negating both variables multiplies the two-variable numerator by its degree parity. -/
theorem carlsonRPolynomialNumerator₂_neg (n : ℕ) (b₀ b₁ x y : ℂ) :
    carlsonRPolynomialNumerator₂ n b₀ b₁ (-x) (-y) =
      (-1 : ℂ) ^ n * carlsonRPolynomialNumerator₂ n b₀ b₁ x y := by
  unfold carlsonRPolynomialNumerator₂
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have hs : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  rw [neg_pow, neg_pow, ← hs, pow_add]
  ring

/-- On a pair of opposite variables, homogeneity reduces the numerator to its value at
`(1, -1)`. This isolates the scalar coefficient evaluated in [Carl77, Theorem 6.9-1]. -/
theorem carlsonRPolynomialNumerator₂_opposite (n : ℕ) (b₀ b₁ x : ℂ) :
    carlsonRPolynomialNumerator₂ n b₀ b₁ x (-x) =
      x ^ n * carlsonRPolynomialNumerator₂ n b₀ b₁ 1 (-1) := by
  unfold carlsonRPolynomialNumerator₂
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have hs : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  simp only [one_pow]
  rw [neg_pow, ← hs, pow_add]
  ring

/-- The odd-degree equal-parameter Carlson numerator vanishes at opposite variables.
This is the exceptional-parameter-free polynomial content of [Carl77, Theorem 6.9-1]. -/
theorem carlsonRPolynomialNumerator₂_eq_zero_of_odd
    (n : ℕ) (hn : Odd n) (b x : ℂ) :
    carlsonRPolynomialNumerator₂ n b b x (-x) = 0 := by
  have hswap := carlsonRPolynomialNumerator₂_swap n b b x (-x)
  have hneg := carlsonRPolynomialNumerator₂_neg n b b x (-x)
  simp only [neg_neg] at hneg
  rw [hswap] at hneg
  have hsign : (-1 : ℂ) ^ n = -1 := by simpa using hn.neg_one_pow
  rw [hsign, neg_one_mul] at hneg
  apply (mul_eq_zero.mp (show (2 : ℂ) * carlsonRPolynomialNumerator₂ n b b x (-x) = 0 by
    calc
      (2 : ℂ) * carlsonRPolynomialNumerator₂ n b b x (-x) =
          carlsonRPolynomialNumerator₂ n b b x (-x) +
            carlsonRPolynomialNumerator₂ n b b x (-x) := two_mul _
      _ = -carlsonRPolynomialNumerator₂ n b b x (-x) +
            carlsonRPolynomialNumerator₂ n b b x (-x) :=
        congrArg (fun q ↦ q + carlsonRPolynomialNumerator₂ n b b x (-x)) hneg
      _ = 0 := neg_add_cancel _)).resolve_left
  norm_num

/-- The two-variable regularized Carlson polynomial in terms of its explicit Pochhammer
numerator. -/
theorem regRPolynomial_eq_numerator₂_mul_one_div_Gamma
    (n : ℕ) (b₀ b₁ x y : ℂ) :
    regRPolynomial n b₀ b₁ x y =
      carlsonRPolynomialNumerator₂ n b₀ b₁ x y *
        (Gamma (b₀ + b₁ + n))⁻¹ := by
  change regCarlsonRPolynomial n (pair b₀ b₁) (pair x y) = _
  rw [regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma,
    carlsonRPolynomialNumerator_pair, sum_pair]

/-- Simultaneously exchanging the two parameters and variables leaves the regularized
two-variable R-polynomial unchanged. -/
theorem regRPolynomial_swap (n : ℕ) (b₀ b₁ x y : ℂ) :
    regRPolynomial n b₁ b₀ y x = regRPolynomial n b₀ b₁ x y := by
  rw [regRPolynomial_eq_numerator₂_mul_one_div_Gamma,
    regRPolynomial_eq_numerator₂_mul_one_div_Gamma,
    carlsonRPolynomialNumerator₂_swap]
  congr 2
  ring_nf

/-- The regularized equal-parameter Carlson polynomial of odd degree vanishes at opposite
variables. This is the regularized form of [Carl77, Theorem 6.9-1]. -/
theorem regRPolynomial_eq_zero_of_odd (n : ℕ) (hn : Odd n) (b x : ℂ) :
    regRPolynomial n b b x (-x) = 0 := by
  rw [regRPolynomial_eq_numerator₂_mul_one_div_Gamma,
    carlsonRPolynomialNumerator₂_eq_zero_of_odd n hn b x, zero_mul]

/-- The two-variable Carlson power kernel is homogeneous of degree `n`. -/
theorem carlsonPowerPolynomial_pair_smul (n : ℕ) (a x y : ℂ) :
    carlsonPowerPolynomial n (pair (a * x) (a * y)) =
      MvPolynomial.C (a ^ n) * carlsonPowerPolynomial n (pair x y) := by
  have h : pair (a * x) (a * y) = fun i ↦ a * pair x y i := by
    funext i
    fin_cases i <;> rfl
  rw [h]
  exact carlsonPowerPolynomial_smul n a (pair x y)

end DirichletTransform.TwoVariable
end CarlsonTwoVariable

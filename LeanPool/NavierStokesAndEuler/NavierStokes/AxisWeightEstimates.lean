/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Concrete coefficient estimates for the natural-axis norm

Products are actual
finite coefficient convolutions with the Leibniz binomial factors. In particular,
the mixed derivative estimate is proved after the radial inverse; no boundedness
of either differentiation operator on its own is assumed.
-/

namespace NavierStokes.AxisWeightEstimates

open scoped BigOperators
open Finset Finset.Nat

noncomputable section

/-- The exact coefficient weight printed in the candidate manuscript. -/
def weight (ε : ℝ) (n m : ℕ) : ℝ :=
  (1 / 20 : ℝ) ^ n * (ε⁻¹) ^ m * (m.factorial : ℝ) * ((n + m).choose m : ℝ) /
    (((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2)

/-- The analytic part of the weight, before the two square-decay factors. -/
def coreWeight (ε : ℝ) (n m : ℕ) : ℝ :=
  (1 / 20 : ℝ) ^ n * (ε⁻¹) ^ m * (m.factorial : ℝ) * ((n + m).choose m : ℝ)

def squareDecay (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1) ^ 2

theorem weight_eq_core_decay (ε : ℝ) (n m : ℕ) :
    weight ε n m = coreWeight ε n m * squareDecay n * squareDecay m := by
  unfold weight coreWeight squareDecay
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem squareDecay_pos (n : ℕ) : 0 < squareDecay n := by
  unfold squareDecay
  positivity

theorem coreWeight_pos {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    0 < coreWeight ε n m := by
  unfold coreWeight
  have hc : 0 < ((n + m).choose m : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : m ≤ n + m)
  positivity

theorem weight_pos {ε : ℝ} (hε : 0 < ε) (n m : ℕ) : 0 < weight ε n m := by
  rw [weight_eq_core_decay]
  exact mul_pos (mul_pos (coreWeight_pos hε n m) (squareDecay_pos n)) (squareDecay_pos m)

theorem squareDecay_succ_le (n : ℕ) : squareDecay (n + 1) ≤ squareDecay n := by
  unfold squareDecay
  apply one_div_le_one_div_of_le (by positivity)
  push_cast
  nlinarith [show (0 : ℝ) ≤ n by positivity]

theorem squareDecay_le_four_succ (n : ℕ) : squareDecay n ≤ 4 * squareDecay (n + 1) := by
  unfold squareDecay
  have hn : (0 : ℝ) ≤ n := by positivity
  have h₁ : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h₂ : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) + 1 := by positivity
  rw [show 4 * (1 / (((n + 1 : ℕ) : ℝ) + 1) ^ 2) =
    4 / (((n + 1 : ℕ) : ℝ) + 1) ^ 2 by ring]
  rw [div_le_div_iff₀ (sq_pos_of_pos h₁) (sq_pos_of_pos h₂)]
  push_cast
  nlinarith

/-- Elementary telescoping majorant for the square summability estimate. -/
theorem reciprocal_square_telescope (x : ℝ) (hx : 1 ≤ x) :
    1 / x ^ 2 ≤ 2 / x - 2 / (x + 1) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have hid : 2 / x - 2 / (x + 1) = 2 / (x * (x + 1)) := by
    field_simp; ring
  rw [hid, div_le_div_iff₀ (sq_pos_of_pos hx0) (mul_pos hx0 hx1)]
  nlinarith

theorem sum_squareDecay_le (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), squareDecay i) ≤ 2 - 2 / ((n : ℝ) + 2) := by
  induction n with
  | zero => norm_num [squareDecay]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hn : (0 : ℝ) ≤ n := by positivity
      have htel := reciprocal_square_telescope ((n : ℝ) + 2) (by linarith)
      have hid : squareDecay (n + 1) = 1 / ((n : ℝ) + 2) ^ 2 := by
        simp [squareDecay, Nat.cast_add, Nat.cast_one]
        ring
      rw [hid]
      push_cast
      ring_nf at ih htel ⊢
      linarith

theorem sum_squareDecay_le_two (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), squareDecay i) ≤ 2 := by
  have h := sum_squareDecay_le n
  have hp : 0 ≤ 2 / ((n : ℝ) + 2) := by positivity
  linarith

theorem squareDecay_product_le (i j : ℕ) :
    squareDecay i * squareDecay j ≤
      2 * squareDecay (i + j) * (squareDecay i + squareDecay j) := by
  have hi : 0 < (i : ℝ) + 1 := by positivity
  have hj : 0 < (j : ℝ) + 1 := by positivity
  have hij : 0 < ((i + j : ℕ) : ℝ) + 1 := by positivity
  have hpoly : (((i + j : ℕ) : ℝ) + 1) ^ 2 ≤
      2 * (((i : ℝ) + 1) ^ 2 + ((j : ℝ) + 1) ^ 2) := by
    push_cast
    nlinarith [sq_nonneg ((i : ℝ) - (j : ℝ))]
  have hh := div_le_div_of_nonneg_right hpoly (le_of_lt
    (mul_pos (mul_pos (sq_pos_of_pos hi) (sq_pos_of_pos hj)) (sq_pos_of_pos hij)))
  convert! hh using 1 <;> unfold squareDecay <;>
    field_simp [ne_of_gt hi, ne_of_gt hj, ne_of_gt hij]
  ring

/-- The one-dimensional convolution constant is at most eight. -/
theorem squareDecay_convolution_le (n : ℕ) :
    (∑ ij ∈ antidiagonal n, squareDecay ij.1 * squareDecay ij.2) ≤ 8 * squareDecay n := by
  have hsum : (∑ ij ∈ antidiagonal n, squareDecay ij.1 * squareDecay ij.2) ≤
      ∑ ij ∈ antidiagonal n, 2 * squareDecay n * (squareDecay ij.1 + squareDecay ij.2) := by
    apply Finset.sum_le_sum
    intro ij hij
    have h := squareDecay_product_le ij.1 ij.2
    rw [mem_antidiagonal.mp hij] at h
    exact h
  have hfirst : (∑ ij ∈ antidiagonal n, squareDecay ij.1) ≤ 2 := by
    rw [sum_antidiagonal_eq_sum_range_succ_mk]
    exact sum_squareDecay_le_two n
  have hsecond : (∑ ij ∈ antidiagonal n, squareDecay ij.2) ≤ 2 := by
    have heq : (∑ ij ∈ antidiagonal n, squareDecay ij.2) =
        ∑ ij ∈ antidiagonal n, squareDecay ij.1 := by
      simpa only [Prod.fst_swap] using
        (sum_antidiagonal_swap (n := n) (f := fun ij => squareDecay ij.1))
    rw [heq]
    exact hfirst
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hd := (squareDecay_pos n).le
  nlinarith

/-- A term of Vandermonde's sum gives the binomial estimate used in the norm. -/
theorem choose_product_le (i j k l : ℕ) :
    (i + k).choose k * (j + l).choose l ≤ ((i + j) + (k + l)).choose (k + l) := by
  have h := Finset.single_le_sum (fun p (_ : p ∈ antidiagonal (k + l)) =>
    Nat.zero_le ((i + k).choose p.1 * (j + l).choose p.2))
    (show (k, l) ∈ antidiagonal (k + l) from mem_antidiagonal.mpr rfl)
  rw [← Nat.add_choose_eq] at h
  have hindex : i + k + (j + l) = i + j + (k + l) := by omega
  rw [hindex] at h
  exact h

theorem choose_factorials (k l : ℕ) :
    ((k + l).choose k : ℝ) * (k.factorial : ℝ) * (l.factorial : ℝ) =
      ((k + l).factorial : ℝ) := by
  have h := Nat.add_choose_mul_factorial_mul_factorial l k
  rw [Nat.add_comm l k, Nat.mul_right_comm] at h
  exact_mod_cast h

/-- The analytic factors respect the Leibniz convolution with constant one. -/
theorem coreWeight_product_le {ε : ℝ} (hε : 0 < ε) (i j k l : ℕ) :
    ((k + l).choose k : ℝ) * coreWeight ε i k * coreWeight ε j l ≤
      coreWeight ε (i + j) (k + l) := by
  have hc : ((i + k).choose k : ℝ) * ((j + l).choose l : ℝ) ≤
      (((i + j) + (k + l)).choose (k + l) : ℝ) := by
    exact_mod_cast choose_product_le i j k l
  have hfac := choose_factorials k l
  have hnonneg : 0 ≤ (1 / 20 : ℝ) ^ (i + j) * (ε⁻¹) ^ (k + l) *
      ((k + l).factorial : ℝ) := by positivity
  calc
    _ = ((1 / 20 : ℝ) ^ (i + j) * (ε⁻¹) ^ (k + l) * ((k + l).factorial : ℝ)) *
        (((i + k).choose k : ℝ) * ((j + l).choose l : ℝ)) := by
      rw [← hfac]
      unfold coreWeight
      rw [pow_add, pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc hnonneg

/-- Factorial form used only to prove the exact shift identities. -/
theorem coreWeight_factorial (ε : ℝ) (n m : ℕ) :
    coreWeight ε n m =
      (1 / 20 : ℝ) ^ n * (ε⁻¹) ^ m * ((n + m).factorial : ℝ) / (n.factorial : ℝ) := by
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hf : (m.factorial : ℝ) * ((n + m).choose m : ℝ) * (n.factorial : ℝ) =
      ((n + m).factorial : ℝ) := by
    have h := Nat.add_choose_mul_factorial_mul_factorial n m
    exact_mod_cast (by simpa only [mul_comm, mul_left_comm, mul_assoc] using h)
  apply (eq_div_iff hn).2
  unfold coreWeight
  calc
    _ = (1 / 20 : ℝ) ^ n * (ε⁻¹) ^ m *
        ((m.factorial : ℝ) * ((n + m).choose m : ℝ) * (n.factorial : ℝ)) := by ring
    _ = _ := by rw [hf]

theorem coreWeight_radial_identity {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    coreWeight ε n m * ((n : ℝ) + m + 1) =
      20 * ((n : ℝ) + 1) * coreWeight ε (n + 1) m := by
  rw [coreWeight_factorial, coreWeight_factorial]
  have hindex : n + 1 + m = (n + m) + 1 := by omega
  rw [hindex, Nat.factorial_succ, Nat.factorial_succ, pow_succ]
  push_cast
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [ne_of_gt hε, hn, hn1]

theorem coreWeight_radial_le {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    coreWeight ε n m ≤ 20 * coreWeight ε (n + 1) m := by
  have hp : 0 < (n : ℝ) + 1 := by positivity
  apply (mul_le_mul_iff_left₀ hp).mp
  calc
    coreWeight ε n m * ((n : ℝ) + 1) ≤
        coreWeight ε n m * ((n : ℝ) + m + 1) := by
      exact mul_le_mul_of_nonneg_left (by
        have hm : (0 : ℝ) ≤ m := by positivity
        linarith)
        (coreWeight_pos hε n m).le
    _ = 20 * coreWeight ε (n + 1) m * ((n : ℝ) + 1) := by
      rw [coreWeight_radial_identity hε]
      ring

theorem coreWeight_parameter_shift {ε : ℝ} (hε : 0 < ε) (i k : ℕ) :
    coreWeight ε i (k + 1) =
      (20 / ε) * ((i : ℝ) + 1) * coreWeight ε (i + 1) k := by
  rw [coreWeight_factorial, coreWeight_factorial]
  have hindex : i + 1 + k = i + (k + 1) := by omega
  rw [hindex, Nat.factorial_succ, pow_succ, pow_succ]
  push_cast
  have hi : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hi1 : (i : ℝ) + 1 ≠ 0 := by positivity
  have he := ne_of_gt hε
  field_simp

/-- A radial shift costs at most the printed factor `4 * 20 = 80`. -/
theorem weight_radial_shift {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    weight ε n m ≤ 80 * weight ε (n + 1) m := by
  rw [weight_eq_core_decay, weight_eq_core_decay]
  calc
    _ ≤ (20 * coreWeight ε (n + 1) m) * (4 * squareDecay (n + 1)) * squareDecay m := by
      apply mul_le_mul_of_nonneg_right _ (squareDecay_pos m).le
      exact mul_le_mul (coreWeight_radial_le hε n m) (squareDecay_le_four_succ n)
        (squareDecay_pos n).le (mul_nonneg (by norm_num) (coreWeight_pos hε (n + 1) m).le)
    _ = _ := by ring

theorem weight_radial_shift_ratio {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    weight ε n m / weight ε (n + 1) m ≤ 80 := by
  exact (div_le_iff₀ (weight_pos hε (n + 1) m)).2 (weight_radial_shift hε n m)

/-- Assigning the output radial shift to a parameter-differentiated factor. -/
theorem weight_parameter_radial_shift {ε : ℝ} (hε : 0 < ε) (i k : ℕ) :
    weight ε i (k + 1) ≤ (80 / ε) * ((i : ℝ) + 1) * weight ε (i + 1) k := by
  have hc : 0 ≤ (20 / ε) * ((i : ℝ) + 1) * coreWeight ε (i + 1) k := by
    have hcpos := coreWeight_pos hε (i + 1) k
    positivity
  have hd := mul_le_mul (squareDecay_le_four_succ i) (squareDecay_succ_le k)
    (squareDecay_pos (k + 1)).le (mul_nonneg (by norm_num) (squareDecay_pos (i + 1)).le)
  rw [weight_eq_core_decay, coreWeight_parameter_shift hε, weight_eq_core_decay]
  calc
    _ = ((20 / ε) * ((i : ℝ) + 1) * coreWeight ε (i + 1) k) *
        (squareDecay i * squareDecay (k + 1)) := by ring
    _ ≤ ((20 / ε) * ((i : ℝ) + 1) * coreWeight ε (i + 1) k) *
        (4 * squareDecay (i + 1) * squareDecay k) := mul_le_mul_of_nonneg_left hd hc
    _ = _ := by ring

theorem weight_parameter_radial_shift_ratio {ε : ℝ} (hε : 0 < ε) (i k : ℕ) :
    weight ε i (k + 1) / weight ε (i + 1) k ≤ (80 / ε) * ((i : ℝ) + 1) := by
  exact (div_le_iff₀ (weight_pos hε (i + 1) k)).2 (weight_parameter_radial_shift hε i k)

/-- The finite weight convolution associated with radial multiplication and
the parameter Leibniz rule. -/
def productWeightSum (ε : ℝ) (n m : ℕ) : ℝ :=
  ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
    (m.choose kl.1 : ℝ) * weight ε ij.1 kl.1 * weight ε ij.2 kl.2

theorem weight_product_term_le {ε : ℝ} (hε : 0 < ε) (i j k l : ℕ) :
    ((k + l).choose k : ℝ) * weight ε i k * weight ε j l ≤
      coreWeight ε (i + j) (k + l) * (squareDecay i * squareDecay j) *
        (squareDecay k * squareDecay l) := by
  have hd : 0 ≤ squareDecay i * squareDecay j * squareDecay k * squareDecay l := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (squareDecay_pos i).le
      (squareDecay_pos j).le) (squareDecay_pos k).le) (squareDecay_pos l).le
  calc
    _ = (((k + l).choose k : ℝ) * coreWeight ε i k * coreWeight ε j l) *
        (squareDecay i * squareDecay j * squareDecay k * squareDecay l) := by
      rw [weight_eq_core_decay, weight_eq_core_decay]
      ring
    _ ≤ coreWeight ε (i + j) (k + l) *
        (squareDecay i * squareDecay j * squareDecay k * squareDecay l) :=
      mul_le_mul_of_nonneg_right (coreWeight_product_le hε i j k l) hd
    _ = _ := by ring

/-- The manuscript's uniform algebra constant `64`, with actual finite sums. -/
theorem productWeightSum_le {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    productWeightSum ε n m ≤ 64 * weight ε n m := by
  have hsum : productWeightSum ε n m ≤
      ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        coreWeight ε n m * (squareDecay ij.1 * squareDecay ij.2) *
          (squareDecay kl.1 * squareDecay kl.2) := by
    apply Finset.sum_le_sum
    intro ij hij
    apply Finset.sum_le_sum
    intro kl hkl
    have h := weight_product_term_le hε ij.1 ij.2 kl.1 kl.2
    rw [mem_antidiagonal.mp hij, mem_antidiagonal.mp hkl] at h
    exact h
  have hfactor :
      (∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        coreWeight ε n m * (squareDecay ij.1 * squareDecay ij.2) *
          (squareDecay kl.1 * squareDecay kl.2)) =
      coreWeight ε n m *
        (∑ ij ∈ antidiagonal n, squareDecay ij.1 * squareDecay ij.2) *
        (∑ kl ∈ antidiagonal m, squareDecay kl.1 * squareDecay kl.2) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hfactor] at hsum
  have hn0 : 0 ≤ ∑ ij ∈ antidiagonal n, squareDecay ij.1 * squareDecay ij.2 :=
    Finset.sum_nonneg (fun ij _ => mul_nonneg (squareDecay_pos _).le (squareDecay_pos _).le)
  have hm0 : 0 ≤ ∑ kl ∈ antidiagonal m, squareDecay kl.1 * squareDecay kl.2 :=
    Finset.sum_nonneg (fun kl _ => mul_nonneg (squareDecay_pos _).le (squareDecay_pos _).le)
  have hprod := mul_le_mul (squareDecay_convolution_le n) (squareDecay_convolution_le m)
    hm0 (mul_nonneg (by norm_num) (squareDecay_pos n).le)
  calc
    _ ≤ coreWeight ε n m *
        ((∑ ij ∈ antidiagonal n, squareDecay ij.1 * squareDecay ij.2) *
        (∑ kl ∈ antidiagonal m, squareDecay kl.1 * squareDecay kl.2)) := by
      simpa only [mul_assoc] using hsum
    _ ≤ coreWeight ε n m * ((8 * squareDecay n) * (8 * squareDecay m)) :=
      mul_le_mul_of_nonneg_left hprod (coreWeight_pos hε n m).le
    _ = _ := by rw [weight_eq_core_decay]; ring

/-- Actual radial convolution with the parameter Leibniz coefficients. -/
def jetProduct (f g : ℕ → ℕ → ℝ) (n m : ℕ) : ℝ :=
  ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
    (m.choose kl.1 : ℝ) * f ij.1 kl.1 * g ij.2 kl.2

theorem abs_bilinear_term_le (a x y wx wy F G : ℝ)
    (ha : 0 ≤ a) (hF : 0 ≤ F) (_hG : 0 ≤ G) (hwx : 0 ≤ wx) (_hwy : 0 ≤ wy)
    (hx : |x| ≤ F * wx) (hy : |y| ≤ G * wy) :
    |a * x * y| ≤ (F * G) * (a * wx * wy) := by
  rw [abs_mul, abs_mul, abs_of_nonneg ha]
  calc
    a * |x| * |y| = a * (|x| * |y|) := by ring
    _ ≤ a * ((F * wx) * (G * wy)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hx hy (abs_nonneg y) (mul_nonneg hF hwx)) ha
    _ = _ := by ring

theorem abs_double_sum_le {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (f M : ι → κ → ℝ) (h : ∀ i ∈ s, ∀ k ∈ t, |f i k| ≤ M i k) :
    |∑ i ∈ s, ∑ k ∈ t, f i k| ≤ ∑ i ∈ s, ∑ k ∈ t, M i k := by
  calc
    _ ≤ ∑ i ∈ s, |∑ k ∈ t, f i k| := abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      exact (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (h i hi))

/-- Uniform coefficient product bound, requiring only the actual coefficient
bounds on the two input arrays. -/
theorem jetProduct_bound {ε F G : ℝ} (hε : 0 < ε) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (f g : ℕ → ℕ → ℝ)
    (hf : ∀ n m, |f n m| ≤ F * weight ε n m)
    (hg : ∀ n m, |g n m| ≤ G * weight ε n m) (n m : ℕ) :
    |jetProduct f g n m| ≤ 64 * F * G * weight ε n m := by
  have hsum : |jetProduct f g n m| ≤
      ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        (F * G) * ((m.choose kl.1 : ℝ) * weight ε ij.1 kl.1 * weight ε ij.2 kl.2) := by
    apply abs_double_sum_le
    intro ij hij kl hkl
    exact abs_bilinear_term_le _ _ _ _ _ _ _ (Nat.cast_nonneg _) hF hG
      (weight_pos hε _ _).le (weight_pos hε _ _).le (hf _ _) (hg _ _)
  have hfactor :
      (∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        (F * G) * ((m.choose kl.1 : ℝ) * weight ε ij.1 kl.1 * weight ε ij.2 kl.2)) =
      (F * G) * productWeightSum ε n m := by
    simp only [productWeightSum, Finset.mul_sum]
  rw [hfactor] at hsum
  calc
    _ ≤ (F * G) * productWeightSum ε n m := hsum
    _ ≤ (F * G) * (64 * weight ε n m) :=
      mul_le_mul_of_nonneg_left (productWeightSum_le hε n m) (mul_nonneg hF hG)
    _ = _ := by ring

def radialDivisor (r n : ℕ) : ℝ := ((n : ℝ) + 1) * ((n : ℝ) + r)

theorem radialDivisor_pos {r : ℕ} (hr : 1 ≤ r) (n : ℕ) : 0 < radialDivisor r n := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  unfold radialDivisor
  positivity

/-- The extra parameter and dot factors fit inside the regular radial divisor. -/
theorem mixed_factors_le_divisor {r n i j : ℕ} (hr : 1 ≤ r) (hij : i + j = n) :
    ((i : ℝ) + 1) * (j : ℝ) ≤ radialDivisor r n := by
  have hi : i + 1 ≤ n + 1 := by omega
  have hj : j ≤ n + r := by omega
  unfold radialDivisor
  exact_mod_cast Nat.mul_le_mul hi hj

def shiftedProductWeightSum (ε : ℝ) (n m : ℕ) : ℝ :=
  ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
    (m.choose kl.1 : ℝ) * weight ε (ij.1 + 1) kl.1 * weight ε ij.2 kl.2

theorem shiftedProductWeightSum_le {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    shiftedProductWeightSum ε n m ≤ 64 * weight ε (n + 1) m := by
  have hsub : shiftedProductWeightSum ε n m ≤ productWeightSum ε (n + 1) m := by
    unfold productWeightSum
    rw [sum_antidiagonal_succ]
    change shiftedProductWeightSum ε n m ≤ _ + shiftedProductWeightSum ε n m
    apply le_add_of_nonneg_left
    apply Finset.sum_nonneg
    intro kl hkl
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (weight_pos hε _ _).le)
      (weight_pos hε _ _).le
  exact hsub.trans (productWeightSum_le hε (n + 1) m)

/-- A single mixed term after applying the inverse radial divisor. -/
theorem mixed_weight_term_le {ε : ℝ} (hε : 0 < ε) {r n i j : ℕ}
    (hr : 1 ≤ r) (hij : i + j = n) (m k l : ℕ) :
    (((m.choose k : ℝ) * j) / radialDivisor r n) * weight ε i (k + 1) * weight ε j l ≤
      (80 / ε) * ((m.choose k : ℝ) * weight ε (i + 1) k * weight ε j l) := by
  have hD := radialDivisor_pos hr n
  have hcoef : 0 ≤ ((m.choose k : ℝ) * j) / radialDivisor r n := by positivity
  have hfactor : (((i : ℝ) + 1) * j) / radialDivisor r n ≤ 1 := by
    apply (div_le_iff₀ hD).2
    simpa only [one_mul] using mixed_factors_le_divisor hr hij
  have hnonneg : 0 ≤ (80 / ε) *
      ((m.choose k : ℝ) * weight ε (i + 1) k * weight ε j l) := by
    exact mul_nonneg (by positivity)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (weight_pos hε _ _).le) (weight_pos hε _ _).le)
  calc
    _ ≤ (((m.choose k : ℝ) * j) / radialDivisor r n) *
        ((80 / ε) * ((i : ℝ) + 1) * weight ε (i + 1) k) * weight ε j l := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (weight_parameter_radial_shift hε i k) hcoef)
        (weight_pos hε _ _).le
    _ = ((80 / ε) * ((m.choose k : ℝ) * weight ε (i + 1) k * weight ε j l)) *
        ((((i : ℝ) + 1) * j) / radialDivisor r n) := by ring
    _ ≤ ((80 / ε) * ((m.choose k : ℝ) * weight ε (i + 1) k * weight ε j l)) * 1 :=
      mul_le_mul_of_nonneg_left hfactor hnonneg
    _ = _ := mul_one _

def mixedWeightSum (ε : ℝ) (r n m : ℕ) : ℝ :=
  ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
    (((m.choose kl.1 : ℝ) * ij.2) / radialDivisor r n) *
      weight ε ij.1 (kl.1 + 1) * weight ε ij.2 kl.2

theorem mixedWeightSum_le {ε : ℝ} (hε : 0 < ε) {r : ℕ} (hr : 1 ≤ r) (n m : ℕ) :
    mixedWeightSum ε r n m ≤ (5120 / ε) * weight ε (n + 1) m := by
  have hsum : mixedWeightSum ε r n m ≤
      ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        (80 / ε) * ((m.choose kl.1 : ℝ) * weight ε (ij.1 + 1) kl.1 * weight ε ij.2 kl.2) := by
    apply Finset.sum_le_sum
    intro ij hij
    apply Finset.sum_le_sum
    intro kl hkl
    exact mixed_weight_term_le hε hr (mem_antidiagonal.mp hij) m kl.1 kl.2
  have hfactor :
      (∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        (80 / ε) * ((m.choose kl.1 : ℝ) * weight ε (ij.1 + 1) kl.1 * weight ε ij.2 kl.2)) =
      (80 / ε) * shiftedProductWeightSum ε n m := by
    simp only [shiftedProductWeightSum, Finset.mul_sum]
  rw [hfactor] at hsum
  calc
    _ ≤ (80 / ε) * shiftedProductWeightSum ε n m := hsum
    _ ≤ (80 / ε) * (64 * weight ε (n + 1) m) :=
      mul_le_mul_of_nonneg_left (shiftedProductWeightSum_le hε n m) (by positivity)
    _ = _ := by ring

/-- The coefficient at radial degree n+1 of J_r((∂η f) D_Y g).
The radial divisor is distributed over its finite convolution sum. -/
def inverseMixedJet (r : ℕ) (f g : ℕ → ℕ → ℝ) (n m : ℕ) : ℝ :=
  ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
    (((m.choose kl.1 : ℝ) * ij.2) / radialDivisor r n) *
      f ij.1 (kl.1 + 1) * g ij.2 kl.2

/-- The mixed derivative is bounded after radial inversion, with explicit
constant 5120/ε. Neither individual derivative is assumed bounded. -/
theorem inverseMixedJet_bound {ε F G : ℝ} (hε : 0 < ε) (hF : 0 ≤ F) (hG : 0 ≤ G)
    {r : ℕ} (hr : 1 ≤ r) (f g : ℕ → ℕ → ℝ)
    (hf : ∀ n m, |f n m| ≤ F * weight ε n m)
    (hg : ∀ n m, |g n m| ≤ G * weight ε n m) (n m : ℕ) :
    |inverseMixedJet r f g n m| ≤ (5120 / ε) * F * G * weight ε (n + 1) m := by
  have hD := radialDivisor_pos hr n
  have hsum : |inverseMixedJet r f g n m| ≤
      ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        (F * G) * ((((m.choose kl.1 : ℝ) * ij.2) / radialDivisor r n) *
          weight ε ij.1 (kl.1 + 1) * weight ε ij.2 kl.2) := by
    apply abs_double_sum_le
    intro ij hij kl hkl
    exact abs_bilinear_term_le _ _ _ _ _ _ _ (by positivity) hF hG
      (weight_pos hε _ _).le (weight_pos hε _ _).le (hf _ _) (hg _ _)
  have hfactor :
      (∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        (F * G) * ((((m.choose kl.1 : ℝ) * ij.2) / radialDivisor r n) *
          weight ε ij.1 (kl.1 + 1) * weight ε ij.2 kl.2)) =
      (F * G) * mixedWeightSum ε r n m := by
    simp only [mixedWeightSum, Finset.mul_sum]
  rw [hfactor] at hsum
  calc
    _ ≤ (F * G) * mixedWeightSum ε r n m := hsum
    _ ≤ (F * G) * ((5120 / ε) * weight ε (n + 1) m) :=
      mul_le_mul_of_nonneg_left (mixedWeightSum_le hε hr n m) (mul_nonneg hF hG)
    _ = _ := by ring

/-- Coefficients of the radial averaging operator `Bf(Y)=∫₀¹ f(tY)dt`. -/
def averageJet (f : ℕ → ℕ → ℝ) (n m : ℕ) : ℝ := f n m / ((n : ℝ) + 1)

/-- Coefficients of the zero-datum primitive. -/
def primitiveJet (f : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | n + 1, m => f n m / ((n : ℝ) + 1)

/-- Coefficients of the regular zero-datum inverse of `Y f'' + r f'`. -/
def regularInverseJet (r : ℕ) (f : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | n + 1, m => f n m / radialDivisor r n

/-- The primitive is applied together with the parameter derivative. -/
def parameterPrimitiveJet (f : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | n + 1, m => f n (m + 1) / ((n : ℝ) + 1)

theorem averageJet_bound {ε F : ℝ} (_hε : 0 < ε) (_hF : 0 ≤ F)
    (f : ℕ → ℕ → ℝ) (hf : ∀ n m, |f n m| ≤ F * weight ε n m) (n m : ℕ) :
    |averageJet f n m| ≤ F * weight ε n m := by
  unfold averageJet
  rw [abs_div, abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]
  exact (div_le_self (abs_nonneg _) (by
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith)).trans (hf n m)

theorem primitiveJet_bound {ε F : ℝ} (hε : 0 < ε) (hF : 0 ≤ F)
    (f : ℕ → ℕ → ℝ) (hf : ∀ n m, |f n m| ≤ F * weight ε n m) (n m : ℕ) :
    |primitiveJet f n m| ≤ 80 * F * weight ε n m := by
  cases n with
  | zero =>
      simpa only [primitiveJet, abs_zero] using
        (mul_nonneg (mul_nonneg (by norm_num) hF) (weight_pos hε 0 m).le)
  | succ n =>
      calc
        |primitiveJet f (n + 1) m| = |averageJet f n m| := rfl
        _ ≤ F * weight ε n m := averageJet_bound hε hF f hf n m
        _ ≤ F * (80 * weight ε (n + 1) m) :=
          mul_le_mul_of_nonneg_left (weight_radial_shift hε n m) hF
        _ = _ := by ring

theorem radialDivisor_ge_one {r : ℕ} (hr : 1 ≤ r) (n : ℕ) : 1 ≤ radialDivisor r n := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have ha : (1 : ℝ) ≤ n + 1 := by linarith
  have hb : (1 : ℝ) ≤ n + r := by linarith
  simpa only [one_mul, radialDivisor] using
    (mul_le_mul ha hb (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ (n : ℝ) + 1))

theorem regularInverseJet_bound {ε F : ℝ} (hε : 0 < ε) (hF : 0 ≤ F)
    {r : ℕ} (hr : 1 ≤ r) (f : ℕ → ℕ → ℝ)
    (hf : ∀ n m, |f n m| ≤ F * weight ε n m) (n m : ℕ) :
    |regularInverseJet r f n m| ≤ 80 * F * weight ε n m := by
  cases n with
  | zero =>
      simpa only [regularInverseJet, abs_zero] using
        (mul_nonneg (mul_nonneg (by norm_num) hF) (weight_pos hε 0 m).le)
  | succ n =>
      rw [regularInverseJet, abs_div, abs_of_pos (radialDivisor_pos hr n)]
      calc
        |f n m| / radialDivisor r n ≤ |f n m| :=
          div_le_self (abs_nonneg _) (radialDivisor_ge_one hr n)
        _ ≤ F * weight ε n m := hf n m
        _ ≤ F * (80 * weight ε (n + 1) m) :=
          mul_le_mul_of_nonneg_left (weight_radial_shift hε n m) hF
        _ = _ := by ring

theorem parameterPrimitiveJet_bound {ε F : ℝ} (hε : 0 < ε) (hF : 0 ≤ F)
    (f : ℕ → ℕ → ℝ) (hf : ∀ n m, |f n m| ≤ F * weight ε n m) (n m : ℕ) :
    |parameterPrimitiveJet f n m| ≤ (80 / ε) * F * weight ε n m := by
  cases n with
  | zero =>
      simpa only [parameterPrimitiveJet, abs_zero] using
        (mul_nonneg (mul_nonneg (show 0 ≤ 80 / ε by positivity) hF) (weight_pos hε 0 m).le)
  | succ n =>
      rw [parameterPrimitiveJet, abs_div, abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]
      apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
      calc
        |f n (m + 1)| ≤ F * weight ε n (m + 1) := hf n (m + 1)
        _ ≤ F * ((80 / ε) * ((n : ℝ) + 1) * weight ε (n + 1) m) :=
          mul_le_mul_of_nonneg_left (weight_parameter_radial_shift hε n m) hF
        _ = _ := by ring

/-- Put the already estimated mixed coefficient in its output radial degree. -/
def regularInverseMixedJet (r : ℕ) (f g : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | n + 1, m => inverseMixedJet r f g n m

theorem regularInverseMixedJet_bound {ε F G : ℝ}
    (hε : 0 < ε) (hF : 0 ≤ F) (hG : 0 ≤ G) {r : ℕ} (hr : 1 ≤ r)
    (f g : ℕ → ℕ → ℝ)
    (hf : ∀ n m, |f n m| ≤ F * weight ε n m)
    (hg : ∀ n m, |g n m| ≤ G * weight ε n m) (n m : ℕ) :
    |regularInverseMixedJet r f g n m| ≤ (5120 / ε) * F * G * weight ε n m := by
  cases n with
  | zero =>
      simpa only [regularInverseMixedJet, abs_zero] using
        (mul_nonneg (mul_nonneg (mul_nonneg (show 0 ≤ 5120 / ε by positivity) hF) hG)
          (weight_pos hε 0 m).le)
  | succ n => exact inverseMixedJet_bound hε hF hG hr f g hf hg n m

end

end NavierStokes.AxisWeightEstimates

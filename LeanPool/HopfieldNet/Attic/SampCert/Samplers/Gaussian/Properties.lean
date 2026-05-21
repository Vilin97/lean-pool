/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.Attic.SampCert.Foundations.Basic
import LeanPool.HopfieldNet.Attic.SampCert.Samplers.Uniform.Basic
import LeanPool.HopfieldNet.Attic.SampCert.Samplers.Bernoulli.Basic
import LeanPool.HopfieldNet.Attic.SampCert.Samplers.BernoulliNegativeExponential.Basic
import LeanPool.HopfieldNet.Attic.SampCert.Samplers.Laplace.Basic
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import LeanPool.HopfieldNet.Attic.SampCert.Util.UtilMathlib
import LeanPool.HopfieldNet.Attic.SampCert.Samplers.Gaussian.Code
import LeanPool.HopfieldNet.Attic.SampCert.Util.Gaussian.DiscreteGaussian

/-!
# ``DiscreteGaussianSample`` Properties

This file proves evaluation and normalization properties of ``DiscreteGaussianSample``.
-/

noncomputable section

open Classical PMF Nat Real

namespace SLang

lemma ite_simpl_gaussian_1 (num den t: ℕ+) (x a : ℤ) :
  @ite ENNReal (x = a) (propDecidable (x = a)) 0
  (if a = x then
    DiscreteLaplaceSample t 1 x *
      BernoulliExpNegSample (Int.natAbs (Int.sub (|x| * ↑↑t * ↑↑den) ↑↑num) ^ 2) (2 * num * t ^ 2 * den) false
  else 0) = 0 := by
  split
  · simp
  · split
    · rename_i h1 h2
      subst h2
      contradiction
    · simp

lemma ite_simpl_gaussian_2 (num den t: ℕ+) (x a : ℤ) :
  @ite ENNReal (x = a) (propDecidable (x = a)) 0
  (if a = x then
    DiscreteLaplaceSample t 1 x *
      BernoulliExpNegSample (Int.natAbs (Int.sub (|x| * ↑↑t * ↑↑den) ↑↑num) ^ 2) (2 * num * t ^ 2 * den) true
  else 0) = 0 := by
  split
  · simp
  · split
    · rename_i h1 h2
      subst h2
      contradiction
    · simp

/--
Gaussian sampling attempt is a proper distribution.
-/
@[simp]
theorem DiscreteGaussianSampleLoop_normalizes (num den t : ℕ+) (mix : ℕ) :
  ∑' x, (DiscreteGaussianSampleLoop num den t mix) x = 1 := by
  simp only [DiscreteGaussianSampleLoop, Bind.bind, Int.natCast_natAbs, Pure.pure, SLang.bind_apply,
    SLang.pure_apply, tsum_bool, ENNReal.tsum_prod', Prod.mk.injEq, mul_ite, mul_one, mul_zero,
    and_true, and_false, ↓reduceIte, add_zero, zero_add]
  rw [DiscreteLaplaceSampleMixed_equiv]
  conv =>
    left
    right
    intro a
    congr
    . rw [ENNReal.tsum_eq_add_tsum_ite a]
      right
      right
      intro x
      rw [ite_simpl_gaussian_1]
    . rw [ENNReal.tsum_eq_add_tsum_ite a]
      right
      right
      intro x
      rw [ite_simpl_gaussian_2]
  simp only [↓reduceIte, tsum_zero, add_zero]
  conv =>
    left
    right
    intro a
    rw [← mul_add]
    rw [← tsum_bool]
    rw [BernoulliExpNegSample_normalizes]
  simp only [mul_one]
  rw [DiscreteLaplaceSample_normalizes]

@[simp]
lemma ite_simpl_1' (num den t : PNat) (x : ℤ) (n : ℤ) :
  (@ite ENNReal (x = n) (propDecidable (x = n)) 0
  (@ite ENNReal (n = x) (n.instDecidableEq x)
  (ENNReal.ofReal (((t : ℝ)⁻¹.exp - 1) / ((t : ℝ)⁻¹.exp + 1) * (-(@abs ℝ DistribLattice.toLattice AddGroupWithOne.toAddGroup ↑x / (t : ℝ))).exp) *
    ENNReal.ofReal (-(((|x| * t * den).sub num).natAbs ^ 2 / ((2 : ℕ+) * num * (t : ℝ) ^ 2 * den))).exp)
  0)) = 0 := by
  split
  · simp
  · rename_i h
    simp [h]
    intro h
    subst h
    contradiction

/--
Evaluation of the discrete Gaussian sample loop distribution when the termination flag is ``true``.
-/
@[simp]
theorem DiscreteGaussianSampleLoop_apply_true (num den t : ℕ+) (n : ℤ) (mix : ℕ) :
  (DiscreteGaussianSampleLoop num den t mix) (n, true)
    = ENNReal.ofReal ((rexp (t)⁻¹ - 1) / (rexp (t)⁻¹ + 1)) * ENNReal.ofReal (rexp (-(Int.natAbs n / t)) *
    rexp (-((Int.natAbs (Int.sub (|n| * t * den) ↑↑num)) ^ 2 / ((2 : ℕ+) * num * ↑↑t ^ 2 * den)))) := by
  simp only [DiscreteGaussianSampleLoop, DiscreteLaplaceSampleMixed_equiv, Bind.bind, Int.natCast_natAbs, Pure.pure, SLang.bind_apply,
    DiscreteLaplaceSample_apply, NNReal.coe_natCast, PNat.one_coe, cast_one, NNReal.coe_one,
    div_one, one_div, Int.cast_abs, SLang.pure_apply, Prod.mk.injEq, mul_ite,
    mul_one, mul_zero, tsum_bool, and_false, ↓reduceIte, and_true, BernoulliExpNegSample_apply_true,
    cast_pow, NNReal.coe_pow, PNat.mul_coe, PNat.pow_coe, cast_mul, NNReal.coe_mul, zero_add]
  rw [ENNReal.tsum_eq_add_tsum_ite (n : ℤ)]
  simp (config := { contextual := true }) only [↓reduceIte, ite_simpl_1', tsum_zero, add_zero]
  rw [ENNReal.ofReal_mul]
  have A : 0 ≤ rexp (-(|↑n| / ↑↑t)) := by apply exp_nonneg
  · conv =>
      left
      rw [mul_assoc]
      right
      rw [← ENNReal.ofReal_mul A]
    congr
    rw [cast_natAbs]
    simp only [Int.cast_abs]
  · rw [div_nonneg_iff] -- always the same
    left
    simp only [sub_nonneg, one_le_exp_iff, inv_nonneg, cast_nonneg, true_and]
    apply Right.add_nonneg
    · apply exp_nonneg
    · simp only [zero_le_one]

lemma if_simpl_2' (x_1 x : ℤ) (a : ENNReal) :
  @ite ENNReal (x_1 = x) (propDecidable (x_1 = x)) 0 (a * (@ite ENNReal (x = x_1) (propDecidable (x = (x_1, true).1))) 1 0) = 0 := by
  split
  · simp
  · split
    · rename_i h1 h2
      subst h2
      contradiction
    · simp

lemma alg_auto (num den : ℕ+) (x : ℤ) :
  ENNReal.ofReal (
  rexp (-((Int.natAbs x) / ((@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + 1))) *
    rexp (-((Int.natAbs (Int.sub (|x| * (@HDiv.hDiv ℤ ℤ ℤ instHDiv num den + 1) * den ^ 2) (num ^ 2))) ^ 2 /
          ((2 : ℕ+) * num ^ 2 * ((@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + 1) ^ 2 * den ^ 2))))
  = ENNReal.ofReal (rexp (-((num ^ 2) / (2 * den ^ 2 * ((@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + 1) ^ 2)))) *
      ENNReal.ofReal (rexp (- ((x ^ 2 * den ^ 2) /(2 * num ^ 2)))) := by
  let τ := (@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + (1 : ℝ)
  have Tau : (@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + (1 : ℝ) = τ := rfl
  rw [Tau]

  have Tau_ne0 : τ ≠ 0 := by
    rw [ne_iff_lt_or_gt]
    right
    apply cast_add_one_pos

  rw [← ENNReal.ofReal_mul]
  · congr 1
    simp [← exp_add]
    simp [division_def]
    rw [(neg_add _ _).symm]
    rw [(neg_add _ _).symm]
    congr 1
    have A : ∀ x : ℤ, (Int.natAbs x)^2 = (x : ℝ)^2 := by
      intro x
      rw [cast_natAbs]
      rw [sq_eq_sq_iff_abs_eq_abs]
      simp
    rw [A]
    clear A
    have A : ∀ x y : ℤ, ((Int.sub x y) : ℝ) = (x : ℝ) - (y : ℝ) := by
      intro x y
      rw [← @Int.cast_sub]
      rfl
    rw [A]
    clear A

    rw [pow_two]
    rw [sub_mul]
    rw [mul_sub]
    rw [mul_sub]
    rw [sub_mul]
    rw [sub_mul]
    rw [sub_mul]
    simp

    have X : (@HDiv.hDiv ℤ ℤ ℤ instHDiv num den) + (1 : ℝ) = (@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + (1 : ℝ) := by
      rfl
    rw [X]
    clear X

    have X : ((Int.natAbs x) : ℝ) = Complex.abs (x : ℂ) := by
      rw [cast_natAbs]
      simp
    rw [X]
    clear X
    rw [Tau]

    let α := (num : ℝ) ^ 2
    have Alpha : ((num : ℕ+) : ℝ) ^ 2 = α := rfl
    rw [Alpha]

    let β := (den : ℝ) ^ 2
    have Beta : ((den : ℕ+) : ℝ) ^ 2  = β := rfl
    rw [Beta]

    let y := Complex.abs (x : ℂ)
    have Y : Complex.abs (x : ℂ)  = y := rfl
    rw [← Complex.abs_ofReal]
    have Cast : ∀ x : ℤ, @Int.cast ℂ Ring.toIntCast x = Complex.ofReal' (@Int.cast ℝ Ring.toIntCast x) := by
      simp
    rw [← Cast]
    rw [Y]

    have Alpha_ne0 : α ≠ 0 := by
      unfold_let
      simp

    have Beta_ne0 : β ≠ 0 := by
      unfold_let
      simp

    field_simp [Alpha_ne0, Beta_ne0, Tau_ne0]
    have xsq_eq_ysq : (x : ℝ) ^ 2 = y ^ 2 := by
      rw [← Y]
      simp
    rw [xsq_eq_ysq]
    ring


  · simp [exp_nonneg]

lemma alg_auto' (num den : ℕ+) (x : ℤ) :
  -((x : ℝ) ^ 2 * (den : ℝ) ^ 2 / ((2 : ℝ) * (num : ℝ) ^ 2)) = -(x : ℝ) ^ 2 / ((2 : ℝ) * ((num : ℝ) ^ 2 / (den : ℝ) ^ 2)) := by
  ring_nf ; simp ; ring_nf

lemma Add1 (n : Nat) : 0 < n + 1 := by
  simp only [add_pos_iff, zero_lt_one, or_true]

/--
Closed form evaluation of the discrete Gaussian sampler
-/
@[simp]
theorem DiscreteGaussianSample_apply (num : PNat) (den : PNat) (mix : ℕ) (x : ℤ) :
  (DiscreteGaussianSample num den mix) x =
  ENNReal.ofReal (discrete_gaussian ((num : ℝ) / (den : ℝ)) 0 x) := by
  unfold discrete_gaussian
  unfold gauss_term_ℝ
  simp
  simp only [DiscreteGaussianSample, Bind.bind, Pure.pure, SLang.bind_apply]
  have A := DiscreteGaussianSampleLoop_normalizes (num ^ 2) (den ^ 2) { val := ↑num / ↑den + 1, property := (Add1 (↑num / ↑den)  : 0 < ↑num / ↑den + 1) } mix

  conv =>
    left
    right
    intro a
    left
    rw [probUntil_apply_norm _ _ _ A]
  clear A

  simp only [ENNReal.tsum_prod', tsum_bool, ↓reduceIte, DiscreteGaussianSampleLoop_apply_true,
    PNat.mk_coe, cast_add, cast_one, Int.ofNat_ediv, PNat.pow_coe, cast_pow, zero_add, ite_mul,
    zero_mul, SLang.pure_apply, NNReal.coe_natCast, div_pow]
  rw [ENNReal.tsum_eq_add_tsum_ite x]
  conv =>
    left
    right
    right
    intro x_1
    rw [if_simpl_2']
  simp only [↓reduceIte, mul_one, tsum_zero, add_zero]

  rw [ENNReal.tsum_mul_left]
  rw [ENNReal.mul_inv]
  · rw [mul_assoc]
    conv =>
      left
      right
      rw [mul_comm]
      rw [mul_assoc]
    rw [← mul_assoc]
    rw [ENNReal.mul_inv_cancel]
    · simp only [one_mul]
      rw [mul_comm]
      rw [← division_def]
      rw [ENNReal.ofReal_div_of_pos]
      · simp only [alg_auto]
        rw [ENNReal.tsum_mul_left]
        rw [ENNReal.div_eq_inv_mul]
        rw [← mul_assoc]
        rw [ENNReal.mul_inv]
        have A : ENNReal.ofReal (rexp (-(↑↑num ^ 2 / (2 * ↑↑den ^ 2 * (↑(@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + 1) ^ 2)))) ≠ 0 := by
          refine zero_lt_iff.mp ?ha.h.a
          simp only [ENNReal.ofReal_pos]
          simp only [exp_pos]
        have B  : ENNReal.ofReal (rexp (-(↑↑num ^ 2 / (2 * ↑↑den ^ 2 * (↑(@HDiv.hDiv ℕ ℕ ℕ instHDiv ↑num ↑den) + 1) ^ 2)))) ≠ ⊤ := by
          exact ENNReal.ofReal_ne_top
        · conv =>
            left
            left
            rw [mul_comm]
            rw [← mul_assoc]
            rw [ENNReal.mul_inv_cancel A B]
          clear A B
          simp only [one_mul]
          rw [mul_comm]
          rw [← division_def]
          congr
          · simp only [alg_auto']
          · conv =>
              left
              right
              intro i
              rw [alg_auto']
            rw [← ENNReal.ofReal_tsum_of_nonneg]
            · intro n
              simp only [exp_nonneg]
            · have A : ((num : ℝ) / (den : ℝ)) ≠ 0 := by
                simp
              have Y := @summable_gauss_term' ((num : ℝ) / (den : ℝ)) A 0
              unfold gauss_term_ℝ at Y
              simp at Y
              exact Y
        · left
          simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
          simp only [exp_pos]
        · left
          exact ENNReal.ofReal_ne_top
      · apply tsum_pos
        · have A : ((num : ℝ) / (den : ℝ)) ≠ 0 := by
            simp
          have Y := @summable_gauss_term' ((num : ℝ) / (den : ℝ)) A 0
          unfold gauss_term_ℝ at Y
          simp at Y
          exact Y
        · intro i
          simp only [exp_nonneg]
        · simp only [exp_pos]
        · exact 0
    · refine pos_iff_ne_zero.mp ?h0.a
      simp only [ENNReal.ofReal_pos]
      rw [div_pos_iff]
      left
      simp only [sub_pos, one_lt_exp_iff, inv_pos]
      constructor
      · apply cast_add_one_pos
      · apply Right.add_pos_of_pos_of_nonneg
        · simp only [exp_pos]
        · simp only [zero_le_one]
    · exact ENNReal.ofReal_ne_top
  · left
    apply zero_lt_iff.mp
    simp only [ENNReal.ofReal_pos]
    rw [div_pos_iff]
    left
    simp only [sub_pos, one_lt_exp_iff, inv_pos]
    constructor
    · apply cast_add_one_pos
    · apply Right.add_pos_of_pos_of_nonneg
      · simp only [exp_pos]
      · simp only [zero_le_one]
  · left
    exact ENNReal.ofReal_ne_top

/--
Discrete Gaussian is a proper distribution
-/
@[simp]
theorem DiscreteGaussianSample_normalizes (num : PNat) (den : PNat) (mix : ℕ) :
  ∑' x : ℤ, (DiscreteGaussianSample num den mix) x = 1 := by
  have A : (num : ℝ) / (den : ℝ) ≠ 0 := by
    simp only [ne_eq, div_eq_zero_iff, cast_eq_zero, PNat.ne_zero, or_self, not_false_eq_true]
  conv =>
    left
    right
    intro x
    rw [DiscreteGaussianSample_apply]
  rw [← ENNReal.ofReal_tsum_of_nonneg]
  · rw [ENNReal.ofReal_one.symm]
    congr 1
    apply discrete_gaussian_normalizes A
  · intro n
    apply discrete_gaussian_nonneg A 0 n
  · apply discrete_gaussian_summable A

theorem DiscreteGaussianSample_HasSum1 (num : PNat) (den : PNat) (mix : ℕ) :
  HasSum (DiscreteGaussianSample num den mix) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  apply DiscreteGaussianSample_normalizes

def DiscreteGaussianPMF (num : PNat) (den : PNat) (mix : ℕ) : PMF ℤ :=
  ⟨ DiscreteGaussianSample num den mix , DiscreteGaussianSample_HasSum1 num den mix ⟩

end SLang

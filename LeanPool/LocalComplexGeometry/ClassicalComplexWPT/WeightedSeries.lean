/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight

/-!
# Weighted `ℓ¹` coefficient infrastructure

The ordinary complex norm is not ultrametric.  We therefore work with honest
`ℓ¹` coefficient estimates: antidiagonal convolution is submultiplicative,
high shifts and low cuts have operator norm at most one, and evaluation on the
unit polydisc is bounded by the `ℓ¹` norm.
-/

open Finset
open scoped ENNReal NNReal Topology

noncomputable section


namespace ClassicalComplexWPT

/-- Complex `ℓ¹` coefficients indexed by `I`. -/
abbrev L1Coeff (I : Type*) := lp (fun _ : I ↦ ℂ) 1

namespace L1Coeff

lemma summable_norm {I : Type*} (f : L1Coeff I) : Summable (fun i ↦ ‖f i‖) := by
  simpa using (lp.memℓp f).summable (p := (1 : ℝ≥0∞)) (by norm_num)

lemma norm_eq_tsum_norm {I : Type*} (f : L1Coeff I) : ‖f‖ = ∑' i, ‖f i‖ := by
  simpa using lp.norm_eq_tsum_rpow (p := (1 : ℝ≥0∞)) (by norm_num) f

end L1Coeff

section Convolution

variable {A : Type*} [AddCommMonoid A] [Finset.HasAntidiagonal A]

/-- Antidiagonal Cauchy product of two `ℓ¹` coefficient families. -/
def convolutionFun (f g : L1Coeff A) (n : A) : ℂ :=
  ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2

lemma summable_antidiagonal_norm_product (f g : L1Coeff A) :
    Summable (fun n : A ↦ ∑ kl ∈ Finset.antidiagonal n, ‖f kl.1‖ * ‖g kl.2‖) := by
  apply summable_sum_mul_antidiagonal_of_summable_mul
    (A := A) (α := ℝ) (f := fun a ↦ ‖f a‖) (g := fun a ↦ ‖g a‖)
  exact (L1Coeff.summable_norm f).mul_of_nonneg (L1Coeff.summable_norm g)
      (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)

lemma summable_norm_convolutionFun (f g : L1Coeff A) :
    Summable (fun n ↦ ‖convolutionFun f g n‖) := by
  refine (summable_antidiagonal_norm_product f g).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
  calc
    ‖convolutionFun f g n‖ ≤
        ∑ kl ∈ Finset.antidiagonal n, ‖f kl.1 * g kl.2‖ := norm_sum_le _ _
    _ ≤ ∑ kl ∈ Finset.antidiagonal n, ‖f kl.1‖ * ‖g kl.2‖ := by
      gcongr with kl hkl
      exact norm_mul_le _ _

/-- Antidiagonal convolution as an `ℓ¹` coefficient family. -/
def convolution (f g : L1Coeff A) : L1Coeff A :=
  ⟨convolutionFun f g, by
    apply memℓp_gen
    simpa using summable_norm_convolutionFun f g⟩

@[simp]
lemma convolution_apply (f g : L1Coeff A) (n : A) :
    convolution f g n = ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2 := rfl

/-- The ordinary `ℓ¹` Cauchy-product estimate. -/
theorem norm_convolution_le (f g : L1Coeff A) : ‖convolution f g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [L1Coeff.norm_eq_tsum_norm, L1Coeff.norm_eq_tsum_norm, L1Coeff.norm_eq_tsum_norm]
  have hf := L1Coeff.summable_norm f
  have hg := L1Coeff.summable_norm g
  have hprod : Summable (fun x : A × A ↦ ‖f x.1‖ * ‖g x.2‖) :=
    hf.mul_of_nonneg hg (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
  have hant := summable_antidiagonal_norm_product f g
  have hconv := summable_norm_convolutionFun f g
  calc
    (∑' n, ‖convolution f g n‖) ≤
        ∑' n, ∑ kl ∈ Finset.antidiagonal n, ‖f kl.1‖ * ‖g kl.2‖ := by
      apply hconv.tsum_le_tsum
      · intro n
        exact calc
          ‖convolution f g n‖ ≤
              ∑ kl ∈ Finset.antidiagonal n, ‖f kl.1 * g kl.2‖ := norm_sum_le _ _
          _ ≤ ∑ kl ∈ Finset.antidiagonal n, ‖f kl.1‖ * ‖g kl.2‖ := by
            gcongr with kl hkl
            exact norm_mul_le _ _
      · exact hant
    _ = (∑' a, ‖f a‖) * ∑' a, ‖g a‖ := by
      symm
      exact hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hprod

lemma convolution_add_left (f₁ f₂ g : L1Coeff A) :
    convolution (f₁ + f₂) g = convolution f₁ g + convolution f₂ g := by
  apply lp.ext
  funext n
  simp only [convolution_apply, lp.coeFn_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma convolution_smul_left (c : ℂ) (f g : L1Coeff A) :
    convolution (c • f) g = c • convolution f g := by
  apply lp.ext
  funext n
  simp only [convolution_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc,
    Finset.mul_sum]

/-- Right convolution as a linear map. -/
def convolutionRightLinear (g : L1Coeff A) : L1Coeff A →ₗ[ℂ] L1Coeff A where
  toFun f := convolution f g
  map_add' f₁ f₂ := convolution_add_left f₁ f₂ g
  map_smul' c f := convolution_smul_left c f g

/-- Right convolution as a continuous linear map. -/
def convolutionRight (g : L1Coeff A) : L1Coeff A →L[ℂ] L1Coeff A :=
  (convolutionRightLinear g).mkContinuous ‖g‖ (fun f ↦ by
    change ‖convolution f g‖ ≤ ‖g‖ * ‖f‖
    simpa [mul_comm] using norm_convolution_le f g)

@[simp]
lemma convolutionRight_apply (g f : L1Coeff A) : convolutionRight g f = convolution f g := rfl

theorem norm_convolutionRight_le (g : L1Coeff A) : ‖convolutionRight g‖ ≤ ‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  change ‖convolution f g‖ ≤ ‖g‖ * ‖f‖
  simpa [mul_comm] using norm_convolution_le f g

end Convolution

section DistinguishedShift

variable {A : Type*}

/-- Index map which discards the first `d` distinguished-variable coefficients. -/
def highIndex (d : ℕ) : A × ℕ → A × ℕ := fun x ↦ (x.1, x.2 + d)

lemma highIndex_injective (d : ℕ) : Function.Injective (highIndex (A := A) d) := by
  rintro ⟨a, n⟩ ⟨b, m⟩ h
  simp only [highIndex, Prod.mk.injEq] at h ⊢
  exact ⟨h.1, Nat.add_right_cancel h.2⟩

/-- Delete the first `d` distinguished-variable coefficient layers. -/
def highShift (d : ℕ) (f : L1Coeff (A × ℕ)) : L1Coeff (A × ℕ) :=
  ⟨fun x ↦ f (highIndex d x), by
    apply memℓp_gen
    simpa [Function.comp_def] using
      (L1Coeff.summable_norm f).comp_injective (highIndex_injective (A := A) d)⟩

@[simp]
lemma highShift_apply (d : ℕ) (f : L1Coeff (A × ℕ)) (a : A) (n : ℕ) :
    highShift d f (a, n) = f (a, n + d) := rfl

theorem norm_highShift_le (d : ℕ) (f : L1Coeff (A × ℕ)) :
    ‖highShift d f‖ ≤ ‖f‖ := by
  rw [L1Coeff.norm_eq_tsum_norm, L1Coeff.norm_eq_tsum_norm]
  let e := highIndex (A := A) d
  apply (L1Coeff.summable_norm (highShift d f)).tsum_le_tsum_of_inj e
    (highIndex_injective (A := A) d)
  · intro c hc
    exact norm_nonneg _
  · intro i
    exact le_rfl
  · exact L1Coeff.summable_norm f

lemma highShift_add (d : ℕ) (f g : L1Coeff (A × ℕ)) :
    highShift d (f + g) = highShift d f + highShift d g := by
  apply lp.ext
  funext x
  rfl

lemma highShift_smul (d : ℕ) (c : ℂ) (f : L1Coeff (A × ℕ)) :
    highShift d (c • f) = c • highShift d f := by
  apply lp.ext
  funext x
  rfl

/-- High shift as a complex-linear map. -/
def highShiftLinear (d : ℕ) : L1Coeff (A × ℕ) →ₗ[ℂ] L1Coeff (A × ℕ) where
  toFun := highShift d
  map_add' := highShift_add d
  map_smul' := highShift_smul d

/-- High shift as a contraction. -/
def highShiftCLM (d : ℕ) : L1Coeff (A × ℕ) →L[ℂ] L1Coeff (A × ℕ) :=
  (highShiftLinear d).mkContinuous 1 (by
    intro f
    change ‖highShift d f‖ ≤ 1 * ‖f‖
    simpa using norm_highShift_le (A := A) d f)

theorem norm_highShiftCLM_le (d : ℕ) : ‖highShiftCLM (A := A) d‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖highShift d f‖ ≤ 1 * ‖f‖
  simpa using norm_highShift_le (A := A) d f

/-- Keep exactly the distinguished-variable coefficient layers below `d`. -/
def lowCut (d : ℕ) (f : L1Coeff (A × ℕ)) : L1Coeff (A × ℕ) :=
  ⟨fun x ↦ if x.2 < d then f x else 0, by
    apply memℓp_gen
    simpa using (L1Coeff.summable_norm f).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) (fun x ↦ by split_ifs <;> simp)⟩

@[simp]
lemma lowCut_apply_of_lt (d : ℕ) (f : L1Coeff (A × ℕ)) (a : A) {n : ℕ}
    (hn : n < d) : lowCut d f (a, n) = f (a, n) := by simp [lowCut, hn]

@[simp]
lemma lowCut_apply_of_le (d : ℕ) (f : L1Coeff (A × ℕ)) (a : A) {n : ℕ}
    (hn : d ≤ n) : lowCut d f (a, n) = 0 := by simp [lowCut, Nat.not_lt.mpr hn]

theorem norm_lowCut_le (d : ℕ) (f : L1Coeff (A × ℕ)) : ‖lowCut d f‖ ≤ ‖f‖ := by
  rw [L1Coeff.norm_eq_tsum_norm, L1Coeff.norm_eq_tsum_norm]
  apply (L1Coeff.summable_norm (lowCut d f)).tsum_le_tsum
  · intro x
    change ‖if x.2 < d then f x else 0‖ ≤ ‖f x‖
    split_ifs <;> simp
  · exact L1Coeff.summable_norm f

lemma lowCut_add (d : ℕ) (f g : L1Coeff (A × ℕ)) :
    lowCut d (f + g) = lowCut d f + lowCut d g := by
  apply lp.ext
  funext x
  simp only [lowCut, lp.coeFn_add, Pi.add_apply]
  split_ifs <;> simp

lemma lowCut_smul (d : ℕ) (c : ℂ) (f : L1Coeff (A × ℕ)) :
    lowCut d (c • f) = c • lowCut d f := by
  apply lp.ext
  funext x
  simp only [lowCut, lp.coeFn_smul, Pi.smul_apply]
  split_ifs <;> simp

/-- Low-degree cutoff as a complex-linear map. -/
def lowCutLinear (d : ℕ) : L1Coeff (A × ℕ) →ₗ[ℂ] L1Coeff (A × ℕ) where
  toFun := lowCut d
  map_add' := lowCut_add d
  map_smul' := lowCut_smul d

/-- Low cutoff as a contraction. -/
def lowCutCLM (d : ℕ) : L1Coeff (A × ℕ) →L[ℂ] L1Coeff (A × ℕ) :=
  (lowCutLinear d).mkContinuous 1 (by
    intro f
    change ‖lowCut d f‖ ≤ 1 * ‖f‖
    simpa using norm_lowCut_le (A := A) d f)

theorem norm_lowCutCLM_le (d : ℕ) : ‖lowCutCLM (A := A) d‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖lowCut d f‖ ≤ 1 * ‖f‖
  simpa using norm_lowCut_le (A := A) d f

end DistinguishedShift

section Evaluation

variable {S : Type*}

/-- A multivariate monomial indexed by a finitely-supported exponent vector. -/
def monomial (y : S → ℂ) (a : S →₀ ℕ) : ℂ :=
  a.prod fun i n ↦ y i ^ n

@[simp]
lemma monomial_zero (y : S → ℂ) : monomial y 0 = 1 := by simp [monomial]

lemma monomial_add (y : S → ℂ) (a b : S →₀ ℕ) :
    monomial y (a + b) = monomial y a * monomial y b := by
  classical
  exact Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ m n ↦ pow_add _ m n)

lemma norm_monomial_le_one (y : S → ℂ) (hy : ∀ i, ‖y i‖ ≤ 1) (a : S →₀ ℕ) :
    ‖monomial y a‖ ≤ 1 := by
  classical
  change ‖∏ i ∈ a.support, y i ^ a i‖ ≤ 1
  rw [norm_prod]
  simp only [norm_pow]
  apply Finset.prod_le_one
  · intro i hi
    exact pow_nonneg (norm_nonneg _) _
  · intro i hi
    exact pow_le_one₀ (norm_nonneg _) (hy i)

/-- Multiplicative real polyradius weight. -/
def monomialWeight (r : S → ℝ) (a : S →₀ ℕ) : ℝ :=
  a.prod fun i n ↦ r i ^ n

lemma monomialWeight_add (r : S → ℝ) (a b : S →₀ ℕ) :
    monomialWeight r (a + b) = monomialWeight r a * monomialWeight r b := by
  classical
  exact Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ m n ↦ pow_add _ m n)

/-- Evaluate an `ℓ¹` coefficient family on the unit polydisc. -/
def evalL1 (f : L1Coeff (S →₀ ℕ)) (y : S → ℂ) : ℂ :=
  ∑' a, f a * monomial y a

lemma summable_norm_evalL1_terms (f : L1Coeff (S →₀ ℕ)) (y : S → ℂ)
    (hy : ∀ i, ‖y i‖ ≤ 1) :
    Summable (fun a ↦ ‖f a * monomial y a‖) := by
  refine (L1Coeff.summable_norm f).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun a ↦ ?_)
  calc
    ‖f a * monomial y a‖ ≤ ‖f a‖ * ‖monomial y a‖ := norm_mul_le _ _
    _ ≤ ‖f a‖ * 1 :=
      mul_le_mul_of_nonneg_left (norm_monomial_le_one y hy a) (norm_nonneg _)
    _ = ‖f a‖ := mul_one _

lemma summable_evalL1_terms (f : L1Coeff (S →₀ ℕ)) (y : S → ℂ)
    (hy : ∀ i, ‖y i‖ ≤ 1) :
    Summable (fun a ↦ f a * monomial y a) :=
  Summable.of_norm (summable_norm_evalL1_terms f y hy)

/-- Evaluation on the unit polydisc is bounded by the coefficient `ℓ¹` norm. -/
lemma norm_evalL1_le (f : L1Coeff (S →₀ ℕ)) (y : S → ℂ)
    (hy : ∀ i, ‖y i‖ ≤ 1) : ‖evalL1 f y‖ ≤ ‖f‖ := by
  rw [L1Coeff.norm_eq_tsum_norm]
  exact (norm_tsum_le_tsum_norm (summable_norm_evalL1_terms f y hy)).trans <| by
    apply (summable_norm_evalL1_terms f y hy).tsum_le_tsum
    · intro a
      calc
        ‖f a * monomial y a‖ ≤ ‖f a‖ * ‖monomial y a‖ := norm_mul_le _ _
        _ ≤ ‖f a‖ := by
          simpa using
            mul_le_mul_of_nonneg_left (norm_monomial_le_one y hy a) (norm_nonneg (f a))
    · exact L1Coeff.summable_norm f

end Evaluation

end ClassicalComplexWPT

/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module



public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

import LeanPool.CarlsonFunctions.Pochhammer.Gamma

/-! # The complex multivariate beta function -/

open Fintype

@[expose] public noncomputable section MvBeta

namespace Complex

variable {ι : Type*} [Fintype ι]

/-- The multivariate Beta function. -/
def mvBeta (b : ι → ℂ) : ℂ :=
    (∏ i, Gamma (b i)) / Gamma (∑ i, b i)

/-- The domain on which the usual simplex integral representation of `mvBeta` converges
absolutely. -/
def mvBetaConvergent : Set (ι → ℂ) :=
  {b | ∀ i, 0 < (b i).re}

/-- The ordinary Dirichlet convergence region is open. -/
theorem isOpen_mvBetaConvergent : IsOpen (mvBetaConvergent : Set (ι → ℂ)) := by
  rw [show (mvBetaConvergent : Set (ι → ℂ)) =
      ⋂ i, {b : ι → ℂ | 0 < (b i).re} by
    ext b
    simp [mvBetaConvergent]]
  exact isOpen_iInter_of_finite fun i ↦
    isOpen_lt continuous_const
      (Complex.continuous_re.comp (continuous_apply i))

/-- The sum of parameters in `mvBetaConvergent` has positive real part. -/
theorem sum_re_pos_of_mem_mvBetaConvergent [Nonempty ι] {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) : 0 < (∑ i, b i).re := by
  simpa using Finset.sum_pos (fun i _ ↦ hb i) Finset.univ_nonempty

/-- The multivariate Beta function does not vanish on its convergence domain. -/
theorem mvBeta_ne_zero [Nonempty ι] {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    mvBeta b ≠ 0 := by
  apply div_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ Gamma_ne_zero_of_re_pos (hb i)
  · exact Gamma_ne_zero_of_re_pos (sum_re_pos_of_mem_mvBetaConvergent hb)

omit [Fintype ι] in
/-- Adding nonnegative integers coordinatewise preserves `mvBetaConvergent`. -/
theorem addNat_mem_mvBetaConvergent {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (m : ι → ℕ) : (fun i ↦ b i + (m i : ℂ)) ∈ mvBetaConvergent := by
  intro i
  norm_num
  exact add_pos_of_pos_of_nonneg (hb i) (Nat.cast_nonneg _)

omit [Fintype ι] in
/-- Simultaneously permuting the parameters preserves the convergence domain. -/
theorem comp_perm_mem_mvBetaConvergent {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent)
    (σ : Equiv.Perm ι) : b ∘ σ ∈ mvBetaConvergent :=
  fun i ↦ hb (σ i)

/-- `mvBeta` is symmetric in its arguments. -/
theorem mvBeta_perm (b : ι → ℂ) (σ : Equiv.Perm ι) :
    mvBeta (b ∘ σ) = mvBeta b := by
  change (∏ i, Gamma (b (σ i))) / Gamma (∑ i, b (σ i)) =
    (∏ i, Gamma (b i)) / Gamma (∑ i, b i)
  have hp : (∏ i, Gamma (b (σ i))) = ∏ i, Gamma (b i) :=
    Equiv.prod_comp σ (fun i => Gamma (b i))
  have hs : (∑ i, b (σ i)) = ∑ i, b i :=
    Equiv.sum_comp σ b
  rw [hp, hs]

/-- On a singleton index type, `mvBeta` equals one throughout its convergence domain. -/
theorem mvBeta_eq_one_of_unique [Unique ι] {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    mvBeta b = 1 := by
  have hG : Gamma (b default) ≠ 0 := Gamma_ne_zero_of_re_pos (hb default)
  simp [mvBeta, hG]

/-- Positive integer translates of `mvBeta`, assuming only that the coordinate parameters avoid
the poles of the Gamma function. This hypothesis is substantially weaker than
membership in `mvBetaConvergent`.

Some pole-avoidance hypothesis is necessary: because Mathlib totalizes `Gamma` to be zero at its
poles, the displayed identity is not valid for arbitrary complex parameters. -/
theorem mvBeta_addNat_of_ne_neg_nat {b : ι → ℂ}
    (hb : ∀ i (k : ℕ), b i ≠ -(k : ℂ))
    (m : ι → ℕ) :
    mvBeta (fun i : ι => b i + (m i : ℂ)) * (ascPochhammer ℂ (∑ i, m i)).eval (∑ i, b i) =
    mvBeta b * ∏ i, (ascPochhammer ℂ (m i)).eval (b i) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      simp [mvBeta]
  | inr hι =>
      let _ := hι
      have hcoord (i : ι) :
          Gamma (b i + (m i : ℂ)) =
            (ascPochhammer ℂ (m i)).eval (b i) * Gamma (b i) := by
        apply (div_eq_iff (Gamma_ne_zero (hb i))).mp
        exact Gamma_add_nat_div_Gamma_eq (b i) (hb i)
      have hsum_add :
          ∑ i, (b i + (m i : ℂ)) = (∑ i, b i) + (∑ i, m i : ℕ) := by
        simp [Finset.sum_add_distrib]
      have hprod :
          ∏ i, Gamma (b i + (m i : ℂ)) =
            (∏ i, (ascPochhammer ℂ (m i)).eval (b i)) * ∏ i, Gamma (b i) := by
        simp_rw [hcoord, Finset.prod_mul_distrib]
      have hrec := one_div_Gamma_eq_ascPochhammer_mul_one_div_Gamma_add_nat
        (∑ i, b i) (∑ i, m i)
      simp only [mvBeta, hsum_add, hprod, div_eq_mul_inv]
      calc
        ((∏ i, (ascPochhammer ℂ (m i)).eval (b i)) * ∏ i, Gamma (b i)) *
              (Gamma ((∑ i, b i) + (∑ i, m i : ℕ)))⁻¹ *
              (ascPochhammer ℂ (∑ i, m i)).eval (∑ i, b i) =
            (∏ i, (ascPochhammer ℂ (m i)).eval (b i)) * (∏ i, Gamma (b i)) *
              ((ascPochhammer ℂ (∑ i, m i)).eval (∑ i, b i) *
                (Gamma ((∑ i, b i) + (∑ i, m i : ℕ)))⁻¹) := by ring
        _ = (∏ i, (ascPochhammer ℂ (m i)).eval (b i)) * (∏ i, Gamma (b i)) *
              (Gamma (∑ i, b i))⁻¹ := by rw [← hrec]
        _ = (∏ i, Gamma (b i)) * (Gamma (∑ i, b i))⁻¹ *
              ∏ i, (ascPochhammer ℂ (m i)).eval (b i) := by ring

/-- Positive integer translates of `mvBeta` on its absolutely convergent domain. -/
theorem mvBeta_addNat {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (m : ι → ℕ) :
    mvBeta (fun i : ι => b i + (m i : ℂ)) * (ascPochhammer ℂ (∑ i, m i)).eval (∑ i, b i) =
    mvBeta b * ∏ i, (ascPochhammer ℂ (m i)).eval (b i) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      simp [mvBeta]
  | inr hι =>
      let _ := hι
      apply mvBeta_addNat_of_ne_neg_nat (m := m)
      intro i k hik
      have hi : 0 < (b i).re := hb i
      rw [hik] at hi
      norm_num at hi
      linarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k]

end Complex

end MvBeta

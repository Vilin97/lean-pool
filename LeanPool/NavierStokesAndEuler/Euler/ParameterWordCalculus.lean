/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import Mathlib.Analysis.Calculus.ContDiff.Operations
public import LeanPool.NavierStokesAndEuler.Euler.ParameterWordGevrey
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder

/-!
# Actual directional word calculus without changing radius

The word derivative and word sum are the existing ordered evaluations of
the genuine iterated Fréchet derivative. Fixed bounded maps commute with
every word and act boundedly on the same sum, without a dimension factor.
-/

@[expose] public section


noncomputable section

namespace EulerParameterWordGevrey

open ContinuousLinearMap Finset
open scoped ContDiff

variable {P E F ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A genuine derivative in one prescribed constant direction. -/
def directional (directions : ι → P) (f : P → E) (i : ι) : P → E :=
  fun x => fderiv ℝ f x (directions i)

theorem directional_contDiff (directions : ι → P) (f : P → E) (hf : ContDiff ℝ ∞ f) (i : ι) :
    ContDiff ℝ ∞ (directional directions f i) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem wordDerivative_zero (directions : ι → P) (f : P → E)
    (w : Fin 0 → ι) (x : P) : wordDerivative directions f w x = f x :=
  iteratedFDeriv_zero_apply _

/-- Every bounded linear map commutes with the actual ordered spatial derivative. -/
theorem wordDerivative_comp_clm (directions : ι → P) (L : E →L[ℝ] F)
    (f : P → E) (hf : ContDiff ℝ ∞ f) {n : ℕ} (w : Fin n → ι) (x : P) :
    wordDerivative directions (L ∘ f) w x = L (wordDerivative directions f w x) :=
  congrArg (fun D : P [×n]→L[ℝ] F => D (fun j => directions (w j)))
    (L.iteratedFDeriv_comp_left (x := x) hf.contDiffAt (by simp))

theorem wordDerivative_add (directions : ι → P) (f g : P → E)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {n : ℕ} (w : Fin n → ι) (x : P) :
    wordDerivative directions (f+g) w x =
      wordDerivative directions f w x+wordDerivative directions g w x :=
  congrArg (fun D : P [×n]→L[ℝ] E => D (fun j => directions (w j)))
    (iteratedFDeriv_add_apply (x := x) (hf.contDiffAt.of_le (by
        simp)) (hg.contDiffAt.of_le (by simp)))

theorem wordDerivative_sub (directions : ι → P) (f g : P → E)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {n : ℕ} (w : Fin n → ι) (x : P) :
    wordDerivative directions (f-g) w x =
      wordDerivative directions f w x-wordDerivative directions g w x :=
  congrArg (fun D : P [×n]→L[ℝ] E => D (fun j => directions (w j)))
    (iteratedFDeriv_sub_apply (x := x) (hf.contDiffAt.of_le (by
        simp)) (hg.contDiffAt.of_le (by simp)))

/-- Removing the last word letter differentiates the function in that direction first. -/
theorem wordDerivative_snoc (directions : ι → P) (f : P → E) (hf : ContDiff ℝ ∞ f)
    {n : ℕ} (w : Fin n → ι) (i : ι) (x : P) :
    wordDerivative directions f (Fin.snoc w i) x =
      wordDerivative directions (directional directions f i) w x := by
  change iteratedFDeriv ℝ (n+1) f x (directions ∘ Fin.snoc w i) = _
  rw [Fin.comp_snoc, iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
  exact (wordDerivative_comp_clm directions (ContinuousLinearMap.apply ℝ E (directions i))
    (fderiv ℝ f) (hf.fderiv_right (m := ∞) (by simp)) w x).symm

variable [Fintype ι]

theorem wordSum_zero (directions : ι → P) (f : P → E) (x : P) :
    wordSum directions f 0 x = ‖f x‖ := by
  simp only [wordSum, wordDerivative_zero, sum_const, card_univ, Fintype.card_fun,
    Fintype.card_fin, pow_zero, one_smul]

theorem wordSum_nonneg (directions : ι → P) (f : P → E) (n : ℕ) (x : P) :
    0 ≤ wordSum directions f n x := sum_nonneg (fun _ _ => norm_nonneg _)

/-- The genuine word sum decomposes as the sum of its first directional derivatives. -/
theorem wordSum_succ (directions : ι → P) (f : P → E) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (x : P) :
    wordSum directions f (n+1) x = ∑ i, wordSum directions (directional directions f i) n x := by
  calc
    _ = ∑ z : ι × (Fin n → ι), ‖wordDerivative directions (directional directions f z.1) z.2 x‖ :=
      Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n+1) => ι)).symm
        (fun w => ‖wordDerivative directions f w x‖)
        (fun z => ‖wordDerivative directions (directional directions f z.1) z.2 x‖)
        (fun w => by
          change ‖wordDerivative directions f w x‖ =
            ‖wordDerivative directions (directional directions f (w (Fin.last n))) (Fin.init w) x‖
          have h := wordDerivative_snoc directions f hf (Fin.init w) (w (Fin.last n)) x
          simpa only [Fin.snoc_init_self] using congrArg norm h)
    _ = _ := Fintype.sum_prod_type _

/-- A fixed bounded map preserves the radius and factorial shift in the actual word sum. -/
theorem wordSum_comp_clm_le (directions : ι → P) (L : E →L[ℝ] F)
    (f : P → E) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : P) :
    wordSum directions (L ∘ f) n x ≤ ‖L‖*wordSum directions f n x := by
  unfold wordSum
  rw [mul_sum]
  apply sum_le_sum
  intro w _
  rw [wordDerivative_comp_clm directions L f hf w x]
  exact L.le_opNorm _

theorem wordSum_add_le (directions : ι → P) (f g : P → E)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (n : ℕ) (x : P) :
    wordSum directions (f+g) n x ≤ wordSum directions f n x+wordSum directions g n x := by
  unfold wordSum
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro w _
  rw [wordDerivative_add directions f g hf hg w x]
  exact norm_add_le _ _

theorem wordSum_sub_le (directions : ι → P) (f g : P → E)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (n : ℕ) (x : P) :
    wordSum directions (f-g) n x ≤ wordSum directions f n x+wordSum directions g n x := by
  unfold wordSum
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro w _
  rw [wordDerivative_sub directions f g hf hg w x]
  exact norm_sub_le _ _

/-- Subtracting a frozen coefficient has no positive-order derivative. -/
theorem wordSum_sub_const_succ (directions : ι → P) (f : P → E)
    (hf : ContDiff ℝ ∞ f) (c : E) (n : ℕ) (x : P) :
    wordSum directions (f-fun _ => c) (n+1) x = wordSum directions f (n+1) x := by
  unfold wordSum wordDerivative
  rw [iteratedFDeriv_sub_apply (hf.contDiffAt.of_le (by simp)) contDiffAt_const]
  simp only [iteratedFDeriv_succ_const, Pi.zero_apply, sub_zero]

end EulerParameterWordGevrey

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.GaussDigammaSeries
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Gamma Seq Log Deriv

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex

namespace NumberField.Odlyzko

theorem logDeriv_natCast_cpow
    {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    logDeriv (fun z : ℂ ↦ (n : ℂ) ^ z) s =
      Complex.log (n : ℂ) := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hderiv :=
    (hasDerivAt_id s).const_cpow (c := (n : ℂ)) (Or.inl hnC)
  have hderiv' :
      HasDerivAt (fun z : ℂ ↦ (n : ℂ) ^ z)
        ((n : ℂ) ^ s * Complex.log (n : ℂ)) s := by grind
  rw [logDeriv_apply, hderiv'.deriv]
  simp_all

private theorem logDeriv_add_nat (s : ℂ) (j : ℕ) :
    logDeriv (fun z : ℂ ↦ z + j) s = (s + j)⁻¹ := by
  rw [logDeriv_apply, deriv_add_const]
  simp only [deriv_id'', one_div]

theorem logDeriv_GammaSeq
    {s : ℂ} {n : ℕ} (hn : n ≠ 0)
    (hs : ∀ j ∈ Finset.range (n + 1), s + j ≠ 0) :
    logDeriv (fun z : ℂ ↦ Complex.GammaSeq z n) s =
      Complex.log (n : ℂ) -
        ∑ j ∈ Finset.range (n + 1), (s + j)⁻¹ := by
  let numerator : ℂ → ℂ := fun z ↦ (n : ℂ) ^ z * (n.factorial : ℂ)
  let denominator : ℂ → ℂ := fun z ↦
    ∏ j ∈ Finset.range (n + 1), (z + j)
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hfac : (n.factorial : ℂ) ≠ 0 := by
    norm_cast
    exact Nat.factorial_ne_zero n
  have hnum : numerator s ≠ 0 := by
    unfold numerator
    simp_all
  have hden : denominator s ≠ 0 := by
    unfold denominator
    exact Finset.prod_ne_zero_iff.mpr hs
  have hdnum : DifferentiableAt ℂ numerator s := by
    unfold numerator
    exact
      ((hasDerivAt_id s).const_cpow (c := (n : ℂ)) (Or.inl hnC))
        |>.differentiableAt.mul (differentiableAt_const _)
  have hdden : DifferentiableAt ℂ denominator s := by
    unfold denominator
    fun_prop
  change logDeriv (fun z : ℂ ↦ numerator z / denominator z) s = _
  rw [logDeriv_div s hnum hden hdnum hdden]
  have hnumFormula :
      logDeriv numerator s = Complex.log (n : ℂ) := by
    unfold numerator
    rw [logDeriv_mul_const s (n.factorial : ℂ) hfac]
    exact logDeriv_natCast_cpow hn s
  have hdenFormula :
      logDeriv denominator s =
        ∑ j ∈ Finset.range (n + 1), (s + j)⁻¹ := by
    unfold denominator
    rw [logDeriv_prod hs]
    · apply Finset.sum_congr rfl
      intro j hj
      exact logDeriv_add_nat s j
    · simp
  simp_all

end NumberField.Odlyzko

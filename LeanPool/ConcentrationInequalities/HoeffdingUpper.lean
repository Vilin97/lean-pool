/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Measurability

/-!
# Hoeffding's upper-tail inequality for a sum of bounded independent variables

A packaged, optimized Chernoff/Hoeffding upper tail: for finitely many independent random variables
`X i` on a probability space, each valued in `[0,1]`, the sum exceeds its mean by `t ≥ 0` with
probability at most `exp(−2t²/n)`.

Mathlib provides the single-variable Hoeffding lemma (`hasSubgaussianMGF_of_mem_Icc`) and the
sub-Gaussian sum machinery (`HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`), but not the
packaged `exp(−2t²/n)` upper tail for a sum of `[0,1]`-variables. This file assembles it: center
each summand, obtain sub-Gaussian parameter `1/4` per variable, combine by independence, and apply
the optimized Chernoff bound.

* `Contrib.Hoeffding.hoeffding_upper` — the upper-tail bound.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace Contrib.Hoeffding

/-- Centering a finite family moves the sum of expectations to the threshold. -/
private lemma centered_sum_event {Ω : Type*} [MeasureSpace Ω] {n : ℕ}
    (X : Fin n → Ω → ℝ) (t : ℝ) :
    {ω | (∑ i, X i ω) ≥ (∑ i, ∫ ω, X i ω ∂ℙ) + t} =
      {ω | t ≤ ∑ i, (X i ω - ∫ ω, X i ω ∂ℙ)} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Finset.sum_sub_distrib]
  constructor <;> intro h <;> linarith

/-- The variance sum for `n` unit-interval summands gives Hoeffding's exponent. -/
private lemma hoeffding_exponent (n : ℕ) (t : ℝ) :
    -t ^ 2 / (2 * ∑ _i : Fin n, (((2 : NNReal) ^ 2)⁻¹)) = -2 * t ^ 2 / (n : ℝ) := by
  simp
  by_cases hn : n = 0
  · simp [hn]
  · field_simp

/-- **Hoeffding upper tail.** For finitely many independent random variables `X i` on a probability
space, each valued in `[0,1]`, the sum exceeds its mean by `t ≥ 0` with probability at most
`exp(−2t²/n)`.

The proof centers each summand, applies Mathlib's Hoeffding lemma to obtain sub-Gaussian parameter
`1/4`, combines these bounds using independence, and then applies the optimized Chernoff bound.
Measurability and boundedness imply the integrability needed for the expectations. -/
theorem hoeffding_upper {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {n : ℕ}
    (X : Fin n → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X ℙ)
    (h01 : ∀ i, ∀ᵐ ω ∂(ℙ : Measure Ω), X i ω ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ) (ht : 0 ≤ t) :
    (ℙ {ω | (∑ i, X i ω) ≥ (∑ i, ∫ ω, X i ω ∂ℙ) + t})
      ≤ ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (n : ℝ))) := by
  let Y : Fin n → Ω → ℝ := fun i ω ↦ X i ω - ∫ ω, X i ω ∂ℙ
  have hY_indep : iIndepFun Y ℙ := by
    have h := hindep.comp (fun i x ↦ x - ∫ ω, X i ω ∂ℙ)
      (fun _ ↦ measurable_id.sub measurable_const)
    simpa [Y, Function.comp_def] using h
  have hY_subG : ∀ i : Fin n,
      HasSubgaussianMGF (Y i) (((2 : NNReal) ^ 2)⁻¹) ℙ := by
    intro i
    simpa [Y] using
      (hasSubgaussianMGF_of_mem_Icc (X := X i) (a := (0 : ℝ)) (b := 1)
        (hmeas i).aemeasurable (h01 i))
  have hbound := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hY_indep
    (s := Finset.univ) (fun i _ ↦ hY_subG i) ht
  have hreal :
      (ℙ : Measure Ω).real {ω | (∑ i, X i ω) ≥ (∑ i, ∫ ω, X i ω ∂ℙ) + t}
        ≤ Real.exp (-2 * t ^ 2 / (n : ℝ)) := by
    calc
      (ℙ : Measure Ω).real {ω | (∑ i, X i ω) ≥ (∑ i, ∫ ω, X i ω ∂ℙ) + t}
          = (ℙ : Measure Ω).real {ω | t ≤ ∑ i, Y i ω} := by
              rw [centered_sum_event]
      _ ≤ Real.exp (-t ^ 2 / (2 * ∑ i : Fin n, (((2 : NNReal) ^ 2)⁻¹))) := hbound
      _ = Real.exp (-2 * t ^ 2 / (n : ℝ)) := by
        rw [hoeffding_exponent]
  rw [← ENNReal.ofReal_toReal (measure_ne_top ℙ _)]
  exact ENNReal.ofReal_le_ofReal hreal

end Contrib.Hoeffding

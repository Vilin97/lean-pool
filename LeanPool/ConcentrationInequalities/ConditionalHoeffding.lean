/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Conditional Hoeffding lemma (conditionally sub-Gaussian martingale increment)

The conditional analogue of Mathlib's `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`: a random
variable a.s. bounded in `[a,b]` whose conditional expectation given a sub-σ-algebra `m` is `0` is
*conditionally* sub-Gaussian with parameter `(b−a)²/4`. This is the martingale-increment bound that
feeds Azuma (`measure_sum_ge_le_of_hasCondSubgaussianMGF`) to yield McDiarmid's bounded-differences
inequality. Mathlib has the unconditional version but not this conditional one.

* `Contrib.ConditionalHoeffding.hasCondSubgaussianMGF_of_mem_Icc`.

The proof lifts the unconditional Hoeffding bound through the conditional-expectation kernel
`condExpKernel μ m`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Contrib.ConditionalHoeffding

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {hm : m ≤ mΩ} {μ : Measure Ω}

/-- **Conditional Hoeffding.** A variable a.s. in `[a,b]` with conditional expectation `0` given `m`
is conditionally sub-Gaussian with parameter `(b−a)²/4`. -/
theorem hasCondSubgaussianMGF_of_mem_Icc [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    {a b : ℝ} {X : Ω → ℝ} (hXm : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hmean : μ[X | m] =ᵐ[μ] 0) :
    HasCondSubgaussianMGF m hm X ⟨(b - a) ^ 2 / 4, by positivity⟩ μ := by
  let c : NNReal := ⟨(b - a) ^ 2 / 4, by positivity⟩
  have hXint : Integrable X μ := Integrable.of_mem_Icc a b hXm.aemeasurable hb
  have hb_kernel : ∀ᵐ ω ∂(μ.trim hm), ∀ᵐ y ∂condExpKernel μ m ω, X y ∈ Set.Icc a b := by
    apply Measure.ae_ae_of_ae_comp
    rwa [condExpKernel_comp_trim]
  have hmean_trim : μ[X | m] =ᵐ[μ.trim hm] 0 :=
    StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm stronglyMeasurable_condExp
      stronglyMeasurable_zero hmean
  have hint := condExp_ae_eq_trim_integral_condExpKernel hm hXint
  change Kernel.HasSubgaussianMGF X c (condExpKernel μ m) (μ.trim hm)
  refine ⟨?_, ?_⟩
  · intro t
    rw [condExpKernel_comp_trim]
    exact integrable_exp_mul_of_mem_Icc hXm.aemeasurable hb
  · filter_upwards [hb_kernel, hmean_trim, hint] with ω hbound hzero hintegral
    have hmgf := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      hXm.aemeasurable hbound (hintegral ▸ hzero)
    intro t
    convert hmgf.mgf_le t using 1
    apply congrArg (fun z : ℝ => Real.exp (z * t ^ 2 / 2))
    norm_cast
    apply NNReal.eq
    change (b - a) ^ 2 / 4 = (|b - a| / 2) ^ 2
    rw [div_pow, sq_abs]
    norm_num

end Contrib.ConditionalHoeffding

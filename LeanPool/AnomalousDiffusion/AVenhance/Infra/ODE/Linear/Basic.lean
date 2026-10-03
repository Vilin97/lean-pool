/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Integral-form linear ODEs

This file records the integral formulation used for linear equations with measurable
coefficients, together with the continuity and almost-everywhere derivative consequences of the
Lebesgue differentiation theorem.  The coefficient and forcing are deliberately abstract: the
file is reusable for finite-dimensional spaces and for other complete real normed spaces.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace AVenhance.Infra.ODE

open AbsolutelyContinuousOnInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The right-hand side of a time-dependent linear equation. -/
def linearRhs (A : ℝ → E →L[ℝ] E) (f y : ℝ → E) (t : ℝ) : E :=
  A t (y t) + f t

/-- Integral form of `y' = A(t)y + f(t)` on the oriented interval `a..b`. -/
def IsLinearIntegralSolution (A : ℝ → E →L[ℝ] E) (f : ℝ → E) (y₀ : E)
    (a b : ℝ) (y : ℝ → E) : Prop :=
  ∀ t ∈ Icc a b, y t = y₀ + ∫ s in a..t, linearRhs A f y s

/-- A vector-valued integral primitive is continuous on the interval of integrability. -/
theorem continuousOn_intervalPrimitive {g : ℝ → E} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) :
    ContinuousOn (fun t => ∫ s in a..t, g s) (uIcc a b) := by
  exact intervalIntegral.continuousOn_primitive_interval' hg (by simp)

/-- Lebesgue differentiation for the vector-valued interval primitive, with basepoint `a`. -/
theorem ae_hasDerivAt_intervalPrimitive {g : ℝ → E} {a b : ℝ}
    [CompleteSpace E]
    (hg : IntervalIntegrable g volume a b) :
    ∀ᵐ t ∂volume, t ∈ uIcc a b →
      HasDerivAt (fun x => ∫ s in a..x, g s) (g t) t := by
  filter_upwards [hg.ae_hasDerivAt_integral] with t ht
  intro hmem
  exact ht hmem a (by simp)

/-- The interval primitive of a Banach-valued integrable function is absolutely continuous. -/
theorem IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_vector
    {g : ℝ → E} {a b c : ℝ}
    (hg : IntervalIntegrable g volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in c..x, g t) a b := by
  let s := fun (J : ℕ × (ℕ → ℝ × ℝ)) =>
    ⋃ i ∈ Finset.range J.1, uIoc (J.2 i).1 (J.2 i).2
  have h_tendsto :
      Tendsto (fun J => ∫⁻ (x : ℝ) in s J, ‖g x‖ₑ ∂volume.restrict (uIoc a b))
        (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
          𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (𝓝 0) := by
    apply tendsto_setLIntegral_zero
    · exact ne_of_lt (intervalIntegrable_iff.mp hg).hasFiniteIntegral
    · exact tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero
        a b
  have h_tendsto' := ENNReal.toReal_zero ▸
    (ENNReal.continuousAt_toReal (by simp)).tendsto.comp h_tendsto
  refine squeeze_zero' ?_ ?_ h_tendsto'
  · filter_upwards with J
    exact Finset.sum_nonneg (fun _ _ => dist_nonneg)
  have h_disj : ∀ᶠ J in AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
      𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b),
      J ∈ AbsolutelyContinuousOnInterval.disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [h_disj] with J hJ
  obtain ⟨hJ₁, hJ₂⟩ := mem_ofPred_eq ▸ hJ
  simp only [Function.comp_apply, s]
  rw [← integral_norm_eq_lintegral_enorm
      (hg.aestronglyMeasurable_restrict_uIoc.restrict),
    integral_biUnion_finset _ (by simp +contextual [uIoc]) hJ₂]
  · refine Finset.sum_le_sum (fun i hi => ?_)
    have hsubset := AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin hJ
      (Finset.mem_range.mp hi)
    rw [dist_eq_norm,
      intervalIntegral.integral_interval_sub_left
        (by apply IntervalIntegrable.mono_set' hg; grind [uIoc, uIcc])
        (by apply IntervalIntegrable.mono_set' hg; grind [uIoc, uIcc]),
      Measure.restrict_restrict_of_subset hsubset,
      intervalIntegral.integral_symm]
    simpa [norm_neg] using
      intervalIntegral.norm_integral_le_integral_norm_uIoc (f := g)
  · intro i hi
    have hsubset := AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin hJ
      (Finset.mem_range.mp hi)
    unfold IntegrableOn
    rw [Measure.restrict_restrict_of_subset hsubset]
    exact (IntegrableOn.mono_set hg.def'.norm hsubset).integrable

/-- Integral-form solutions are absolutely continuous whenever their right-hand side is L¹. -/
theorem IsLinearIntegralSolution.absolutelyContinuousOnInterval
    {A : ℝ → E →L[ℝ] E} {f y : ℝ → E} {y₀ : E} {a b : ℝ}
    (hab : a ≤ b)
    (hy : IsLinearIntegralSolution A f y₀ a b y)
    (h_rhs : IntervalIntegrable (linearRhs A f y) volume a b) :
    AbsolutelyContinuousOnInterval y a b := by
  have hprim :=
    AVenhance.Infra.ODE.IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_vector
      h_rhs left_mem_uIcc
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => y₀) a b := by
    rw [absolutelyContinuousOnInterval_iff]
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro J hJ hlen
    simpa using hε
  apply (hconst.add hprim).congr
  intro t ht
  exact (hy t (by simpa [uIcc_of_le hab] using ht)).symm

/-- Integral-form solutions have the ordinary derivative almost everywhere in the interval. -/
theorem IsLinearIntegralSolution.ae_hasDerivAt {A : ℝ → E →L[ℝ] E} {f y : ℝ → E}
    {y₀ : E} {a b : ℝ}
    [CompleteSpace E]
    (hab : a ≤ b)
    (hy : IsLinearIntegralSolution A f y₀ a b y)
    (h_rhs : IntervalIntegrable (linearRhs A f y) volume a b) :
    ∀ᵐ t ∂volume, t ∈ Icc a b →
      HasDerivAt y (linearRhs A f y t) t := by
  have hend : ∀ᵐ t ∂volume, t ≠ a ∧ t ≠ b := by
    filter_upwards
      [show ∀ᵐ t ∂volume, t ≠ a by simp [ae_iff, measure_singleton],
       show ∀ᵐ t ∂volume, t ≠ b by simp [ae_iff, measure_singleton]] with t ha' hb'
    exact ⟨ha', hb'⟩
  filter_upwards [ae_hasDerivAt_intervalPrimitive h_rhs, hend] with t ht ⟨hta, htb⟩
  intro htmem
  have htU : t ∈ uIcc a b := by simpa [uIcc_of_le hab] using htmem
  have htIoo : t ∈ Ioo a b := by
    rcases htmem with ⟨hat, htb'⟩
    exact ⟨lt_of_le_of_ne hat hta.symm, lt_of_le_of_ne htb' htb⟩
  have hderiv := ht htU
  have hderiv' : HasDerivAt
      (fun x => y₀ + ∫ s in a..x, linearRhs A f y s)
      (linearRhs A f y t) t := by
    convert (hasDerivAt_const t y₀).add hderiv using 1
    simp
  have heq : (fun x => y x) =ᶠ[𝓝 t]
      (fun x => y₀ + ∫ s in a..x, linearRhs A f y s) := by
    filter_upwards [Ioo_mem_nhds htIoo.1 htIoo.2] with x hx
    exact hy x (Ioo_subset_Icc_self hx)
  exact hderiv'.congr_of_eventuallyEq heq

end AVenhance.Infra.ODE

/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# A fundamental lemma for scalar weak tests

A continuous function on the closed unit time interval is determined by its pairings with smooth
tests supported in the open interval. This is the separation step used after subtracting the
integral primitive of a Fourier coefficient's forcing.
-/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff

namespace AVenhance.Infra.Parabolic.WeakUniqueness

/-- A continuous time function that pairs to zero with every smooth compactly supported interior
test vanishes at every time, including the endpoints. -/
theorem continuous_eq_zero_of_smooth_interior_tests {f : ℝ → ℝ}
    (hf : Continuous f)
    (hzero : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Set.Ioo (0 : ℝ) 1 →
      ∫ t in (0 : ℝ)..1, f t * g t = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, f t = 0 := by
  have hlocal : LocallyIntegrableOn f (Set.Ioo (0 : ℝ) 1) volume :=
    hf.continuousOn.locallyIntegrableOn (IsOpen.measurableSet isOpen_Ioo)
  have hAE := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero isOpen_Ioo hlocal
    (fun g hg hcompact hts => by
      have hsupport : Function.support (fun t => f t * g t) ⊆ Set.Ioc (0 : ℝ) 1 := by
        intro t ht
        have hgt : g t ≠ 0 := by
          intro hgt
          exact ht (by simp [hgt])
        exact Ioo_subset_Ioc_self (hts (subset_closure hgt))
      have hinterval := intervalIntegral.integral_eq_integral_of_support_subset
        (μ := volume) hsupport
      calc
        ∫ t, g t • f t = ∫ t, f t * g t := by
          apply integral_congr_ae
          filter_upwards with t
          simp [smul_eq_mul, mul_comm]
        _ = ∫ t in (0 : ℝ)..1, f t * g t := hinterval.symm
        _ = 0 := hzero g hg hcompact hts)
  have hpoint : ∀ t ∈ Set.Ioo (0 : ℝ) 1, f t = 0 := by
    intro t ht
    by_contra hne
    let U : Set ℝ := Set.Ioo (0 : ℝ) 1 ∩ {s | f s ≠ 0}
    have hUopen : IsOpen U := isOpen_Ioo.inter (isOpen_ne_fun hf continuous_const)
    have htU : t ∈ U := ⟨ht, hne⟩
    have hUpos : 0 < volume U := IsOpen.measure_pos volume hUopen ⟨t, htU⟩
    have hnotU : ∀ᵐ s ∂volume, s ∉ U := by
      filter_upwards [hAE] with s hs
      intro hsU
      exact hsU.2 (hs hsU.1)
    have hUzero : volume U = 0 := by
      simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hnotU
    exact (ne_of_gt hUpos) hUzero
  have hclosed : IsClosed {t : ℝ | f t = 0} := isClosed_singleton.preimage hf
  have hclosure : closure (Set.Ioo (0 : ℝ) 1) ⊆ {t : ℝ | f t = 0} :=
    closure_minimal hpoint hclosed
  intro t ht
  have htClosure : t ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ht
  exact hclosure htClosure

end AVenhance.Infra.Parabolic.WeakUniqueness

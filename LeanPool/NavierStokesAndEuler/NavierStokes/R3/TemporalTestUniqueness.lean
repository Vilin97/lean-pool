/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-! # Pointwise recovery from compact temporal tests -/


noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace NavierStokesR3.TemporalTestUniqueness

/-- Continuity turns the distributional fundamental lemma into equality at
every time of the open interval. The tests are real, and values may be complex. -/
theorem eq_zero_on_open_of_tests {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℂ}
    (hf : ContinuousOn f U)
    (htest : ∀ a : ℝ → ℝ, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ U →
      (∫ t : ℝ, a t • f t) = 0) :
    ∀ t ∈ U, f t = 0 := by
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hf.locallyIntegrableOn hU.measurableSet) htest
  have hrestr : f =ᵐ[volume.restrict U] (fun _ => (0 : ℂ)) := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hU.measurableSet] with t ht htU
    exact ht htU
  exact Measure.eqOn_open_of_ae_eq hrestr hU hf continuousOn_const

/-- A compact temporal test supported in `(0,T)` has the same integral over
`[0,T]` as over the line. No integrability of the untested function is needed. -/
theorem integral_eq_setIntegral {T : ℝ} {a : ℝ → ℝ} {f : ℝ → ℂ}
    (hs : tsupport a ⊆ Ioo (0 : ℝ) T) :
    (∫ t : ℝ, a t • f t) = ∫ t in Icc (0 : ℝ) T, a t • f t := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have ha : a t = 0 := image_eq_zero_of_notMem_tsupport fun h =>
    ht (Ioo_subset_Icc_self (hs h))
  simp only [ha, zero_smul]

theorem eq_zero_on_Ioo_of_setIntegral_tests {T : ℝ} {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ioo (0 : ℝ) T))
    (htest : ∀ a : ℝ → ℝ, ContDiff ℝ ∞ a → HasCompactSupport a →
      tsupport a ⊆ Ioo (0 : ℝ) T →
      (∫ t in Icc (0 : ℝ) T, a t • f t) = 0) :
    ∀ t ∈ Ioo (0 : ℝ) T, f t = 0 := by
  apply eq_zero_on_open_of_tests isOpen_Ioo hf
  intro a ha hc hs
  rw [integral_eq_setIntegral hs]
  exact htest a ha hc hs

end NavierStokesR3.TemporalTestUniqueness

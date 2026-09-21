/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.L0LacunaryOperator

/-!
# Bounded compactly supported almost-everywhere measurable inputs

The core test domain uses Borel-measurable representatives. Every bounded,
compactly supported a.e.-measurable input has a representative in that domain.
This does not change any operator definition or its original test class.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace QuadraticCarleson.L0InfinityAERepresentative


/-- The Borel representative can retain both the pointwise bound and compact support. -/
theorem exists_L0Infinity_ae_eq {f : ℝ → ℂ} (hf : AEMeasurable f volume)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (hc : HasCompactSupport f) :
    ∃ g : L0Infinity, f =ᵐ[volume] (g : ℝ → ℂ) := by
  classical
  obtain ⟨C, hC⟩ := hb
  have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  obtain ⟨g, hgm, hgb, hfg⟩ := hf.exists_ae_eq_range_subset
    (t := {z : ℂ | ‖z‖ ≤ C}) (Eventually.of_forall hC) ⟨f 0, hC 0⟩
  let u : ℝ → ℂ := (tsupport f).indicator g
  have hum : Measurable u := hgm.indicator (isClosed_tsupport f).measurableSet
  have hub : ∀ x, ‖u x‖ ≤ C := by
    intro x
    by_cases hx : x ∈ tsupport f
    · have hgx : ‖g x‖ ≤ C := hgb (mem_range_self x)
      simpa only [u, indicator_of_mem hx] using hgx
    · simpa only [u, indicator_of_notMem hx, norm_zero] using hC0
  have huc : HasCompactSupport u :=
    HasCompactSupport.of_support_subset_isCompact hc
      support_indicator_subset
  refine ⟨⟨u, hum, ⟨C, hub⟩, huc⟩, ?_⟩
  filter_upwards [hfg] with x hx
  by_cases hs : x ∈ tsupport f
  · simpa only [u, indicator_of_mem hs] using hx
  · rw [show u x = 0 by simp only [u, indicator_of_notMem hs]]
    exact image_eq_zero_of_notMem_tsupport hs

/-- Changing an input on a null set changes none of its translated truncation
integrals, for any evaluation point or modulation. -/
theorem quadraticHilbertTrunc_congr_ae {f g : ℝ → ℂ}
    (hfg : f =ᵐ[volume] g) (lam ε x : ℝ) :
    quadraticHilbertTrunc lam ε f x = quadraticHilbertTrunc lam ε g x := by
  have hshift : (fun t ↦ f (x - t)) =ᵐ[volume] (fun t ↦ g (x - t)) :=
    (quasiMeasurePreserving_sub_left_of_right_invariant volume x).ae hfg
  unfold quadraticHilbertTrunc
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hshift] with t ht
  rw [ht]

/-- Principal-value existence and its value are independent of the chosen representative. -/
theorem hasQuadraticPrincipalValue_congr_ae {f g : ℝ → ℂ}
    (hfg : f =ᵐ[volume] g) (lam x : ℝ) (z : ℂ) :
    HasQuadraticPrincipalValue lam f x z ↔ HasQuadraticPrincipalValue lam g x z := by
  simp only [HasQuadraticPrincipalValue, quadraticHilbertTrunc_congr_ae hfg]


end QuadraticCarleson.L0InfinityAERepresentative

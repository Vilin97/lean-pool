/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.L0InfinityAERepresentative
import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryEndpointDirectResolved

/-!
# Endpoint bounds for arbitrary almost-everywhere measurable representatives

The paper's bounded compact-support input convention is insensitive to null
sets. These statements supply actual principal values for raw inputs and the
same modular bounds, without requiring the input itself to be Borel measurable.
-/

open MeasureTheory
open scoped ENNReal

namespace QuadraticCarleson.PositiveEndpointsAERepresentative

open L0InfinityAERepresentative PositivePrincipalValueEndpoints


/-- The full endpoint also holds for Lebesgue-measurable representatives of
the paper's test functions. The supplied values are genuine PVs on a common
conull set, so their supremum is the paper's operator there. -/
theorem full_principalValue_endpoint_aemeasurable :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ (f : ℝ → ℂ), AEMeasurable f volume →
      (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) → HasCompactSupport f →
      ∃ P : ℝ → ℝ → ℂ,
        (∀ᵐ x, ∀ lam : ℝ, HasQuadraticPrincipalValue lam f x (P lam x)) ∧
        ∀ α : ℝ, 0 < α →
          volume {x | ENNReal.ofReal α < ⨆ lam : ℝ, ‖P lam x‖ₑ} ≤
            K * ∫⁻ x, ENNReal.ofReal ((‖f x‖ / α) * paperLog 1 (‖f x‖ / α)) := by
  obtain ⟨K, hK, hbound⟩ := HilbertMaximalWeakResolved.full_principalValue_endpoint
  refine ⟨K, hK, ?_⟩
  intro f hf hb hc
  obtain ⟨g, hfg⟩ := exists_L0Infinity_ae_eq hf hb hc
  refine ⟨fun lam x ↦ principalValueRepresentative lam g x, ?_, ?_⟩
  · filter_upwards [(hbound g).1] with x hx
    intro lam
    exact (hasQuadraticPrincipalValue_congr_ae hfg lam x _).mpr (hx lam)
  · intro α hα
    have h := (hbound g).2 α hα
    have hmass : (∫⁻ x, ENNReal.ofReal ((‖g x‖ / α) * paperLog 1 (‖g x‖ / α))) =
        ∫⁻ x, ENNReal.ofReal ((‖f x‖ / α) * paperLog 1 (‖f x‖ / α)) := by
      apply lintegral_congr_ae
      filter_upwards [hfg] with x hx
      rw [hx]
    simpa only [fullPrincipalValueMaximal, ofReal_norm, hmass] using h

/-- The sharper lacunary endpoint has the same a.e.-representative invariance. -/
theorem lacunary_principalValue_endpoint_aemeasurable :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ (f : ℝ → ℂ), AEMeasurable f volume →
      (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) → HasCompactSupport f →
      ∃ P : ℤ → ℝ → ℂ,
        (∀ᵐ x, ∀ m : ℤ, HasQuadraticPrincipalValue (dyadicModulation m) f x (P m x)) ∧
        ∀ α : ℝ, 0 < α →
          volume {x | ENNReal.ofReal α < ⨆ m : ℤ, ‖P m x‖ₑ} ≤
            K * ∫⁻ x, ENNReal.ofReal ((‖f x‖ / α) *
              paperLog 2 (‖f x‖ / α) ^ 2 * paperLog 4 (‖f x‖ / α)) := by
  obtain ⟨K, hK, hbound⟩ := LacunaryEndpointDirectResolved.lacunary_principalValue_endpoint
  refine ⟨K, hK, ?_⟩
  intro f hf hb hc
  obtain ⟨g, hfg⟩ := exists_L0Infinity_ae_eq hf hb hc
  refine ⟨fun m x ↦ principalValueRepresentative (dyadicModulation m) g x, ?_, ?_⟩
  · filter_upwards [(hbound g).1] with x hx
    intro m
    exact (hasQuadraticPrincipalValue_congr_ae hfg (dyadicModulation m) x _).mpr (hx m)
  · intro α hα
    have h := (hbound g).2 α hα
    have hmass : (∫⁻ x, ENNReal.ofReal ((‖g x‖ / α) *
        paperLog 2 (‖g x‖ / α) ^ 2 * paperLog 4 (‖g x‖ / α))) =
        ∫⁻ x, ENNReal.ofReal ((‖f x‖ / α) *
          paperLog 2 (‖f x‖ / α) ^ 2 * paperLog 4 (‖f x‖ / α)) := by
      apply lintegral_congr_ae
      filter_upwards [hfg] with x hx
      rw [hx]
    simpa only [lacunaryPrincipalValueMaximal, ofReal_norm, hmass] using h


end QuadraticCarleson.PositiveEndpointsAERepresentative

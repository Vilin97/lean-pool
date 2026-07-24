/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.L2LocBridge

/-!
# Weak-gradient bridge

This module gives the integration-by-parts weak-gradient relation a
distributional name.  The test functions are bundled with their `C¹`, compact
support, and support-in-domain data, so future mathlib distribution/test-function
work has a single interface to refine.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- Bundled compactly supported `C¹` test functions with topological support
contained in the domain. -/
structure CompactlySupportedC1In {n : ℕ} (Ω : Set (Domain n)) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  /-- The underlying function of a compactly supported `C¹` test map. -/
  toFun : Domain n → F
  contDiff : ContDiff ℝ 1 toFun
  hasCompactSupport : HasCompactSupport toFun
  tsupport_subset : tsupport toFun ⊆ Ω

namespace CompactlySupportedC1In

instance {n : ℕ} {Ω : Set (Domain n)} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    CoeFun (CompactlySupportedC1In Ω F) (fun _ => Domain n → F) where
  coe ψ := ψ.toFun

theorem coe_mk {n : ℕ} {Ω : Set (Domain n)} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ψ : Domain n → F) (hψ : ContDiff ℝ 1 ψ)
    (hψ_compact : HasCompactSupport ψ) (hψ_support : tsupport ψ ⊆ Ω) :
    ((CompactlySupportedC1In.mk ψ hψ hψ_compact hψ_support :
        CompactlySupportedC1In Ω F) : Domain n → F) = ψ := rfl

end CompactlySupportedC1In

/-- Distributional weak-gradient relation for a chosen gradient field. -/
structure DistributionalWeakGradientIn {n m : ℕ}
    (u : Domain n → Target m) (Du : Domain n → Gradient n m)
    (Ω : Set (Domain n)) : Prop where
  integration_by_parts :
    ∀ i : Fin n, ∀ ψ : CompactlySupportedC1In Ω (Target m),
      (∫ x in Ω, inner ℝ (u x) (partialDerivative ψ i x))
        =
      -∫ x in Ω, inner ℝ (Du x i) (ψ x)

/-- The distributional weak-gradient bridge implies the custom weak-gradient
interface used by the monotonicity proof. -/
theorem DistributionalWeakGradientIn.toHasWeakGradientIn {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)}
    (h : DistributionalWeakGradientIn u Du Ω) :
    HasWeakGradientIn u Du Ω := by
  intro i ψ hψ hψ_compact hψ_support
  exact
    h.integration_by_parts i
      { toFun := ψ
        contDiff := hψ
        hasCompactSupport := hψ_compact
        tsupport_subset := hψ_support }

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end

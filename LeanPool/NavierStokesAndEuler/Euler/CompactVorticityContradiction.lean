/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerMaximal
public import LeanPool.NavierStokesAndEuler.Euler.SolutionDefinitions
import LeanPool.NavierStokesAndEuler.Euler.CompactCurlBounds
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerBKM

/-! A classical comparison field with uniformly confined vorticity cannot
agree with the maximal ordinary solution throughout a finite lifespan.
The contradiction uses the proved Beale--Kato--Majda integral criterion. -/

@[expose] public section


noncomputable section

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerOrdinarySobolev EulerVectorCalculus EulerMeanBoundary EulerMeanCutoffCurl

namespace Euler.ComparatorBridge

variable {A : SmoothL2Field Space} (L : FiniteLifespan A)
  {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}

theorem finiteLifespan_contradiction_of_compact_vorticity
    (h : EulerExistenceAndSmoothnessR3 A.field v p)
    (K : Set Space) (hK : IsCompact K)
    (hmatch : ∀ t : L.Time, L.maximalVelocity t = (v · (t : ℝ)))
    (hsupport : ∀ (t : L.Time) x, x ∉ K →
      vectorCurl (L.maximalVelocity t) x = 0) : False := by
  obtain ⟨M, hM, hbound⟩ := h.vorticity_bounded_on_compact K hK L.duration
  have hcurl : ∀ (t : L.Time) x, ‖vectorCurl (L.maximalVelocity t) x‖ ≤ M := by
    intro t x
    by_cases hx : x ∈ K
    · rw [hmatch t]
      exact hbound t ⟨t.property.1, t.property.2.le⟩ x hx
    · rw [hsupport t x hx, norm_zero]
      exact hM
  obtain ⟨S, hS, hSL, t, hlarge⟩ := L.vorticityIntegral_unbounded (M * L.duration)
  have hbound : ∀ s x, ‖vectorCurl ((L.evolution S hS hSL).velocity s).field x‖ ≤ M := by
    intro s x
    rw [← L.maximalVelocity_eq_evolution S hS hSL s]
    exact hcurl _ x
  have hupper := (L.evolution S hS hSL).vorticityIntegral_le_const M hbound t
  have ht : (t : ℝ) ≤ L.duration := t.property.2.trans hSL.le
  exact (not_lt_of_ge (hupper.trans (mul_le_mul_of_nonneg_left ht hM))) hlarge

end Euler.ComparatorBridge

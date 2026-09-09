/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ComparatorEvolutionIdentification
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerMaximal

@[expose] public section

/-! Local recovery and ordinary uniqueness identify the canonical maximal
velocity with every global Comparator solution. -/

noncomputable section


open Set EulerSmoothLimit EulerLpTranslation EulerOrdinarySobolev EulerMeanCutoffCurl

namespace Euler.ComparatorBridge

variable {A : SmoothL2Field Space} (L : FiniteLifespan A)
  {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}

theorem maximalVelocity_eq_of_local_evolution
    (h : EulerExistenceAndSmoothnessR3 A.field v p)
    (hcompact : ∀ t : L.Time, HasCompactSupport (vectorCurl (L.maximalVelocity t)))
    (hlocal : HasLocalEvolutionAtCompactCurl v) :
    ∀ t : L.Time, L.maximalVelocity t = (v · (t : ℝ)) := by
  intro t
  let S := L.intermediateHorizon t
  have hS : 0 < S := L.intermediateHorizon_pos t
  have hSL : S < L.duration := L.intermediateHorizon_lt t
  have hc : ∀ s, HasCompactSupport
      (vectorCurl ((L.evolution S hS hSL).velocity s).field) := by
    intro s
    rw [← L.maximalVelocity_eq_evolution S hS hSL s]
    exact hcompact _
  have he := evolution_field_eq_of_local_evolution (L.evolution S hS hSL) h
    (L.evolution_initial S hS hSL) hc hlocal (L.intermediateTime t)
  rw [← L.maximalVelocity_eq_evolution S hS hSL (L.intermediateTime t)] at he
  exact he

/-- The local analytic bridge suffices to identify the Comparator with the
canonical maximal solution, without additional time or space assumptions. -/
theorem maximalVelocity_eq_of_compactCurlLocalUpgrade
    (h : EulerExistenceAndSmoothnessR3 A.field v p)
    (hcompact : ∀ t : L.Time, HasCompactSupport (vectorCurl (L.maximalVelocity t)))
    (hupgrade : CompactCurlLocalUpgrade) :
    ∀ t : L.Time, L.maximalVelocity t = (v · (t : ℝ)) :=
  maximalVelocity_eq_of_local_evolution L h hcompact
    (hasLocalEvolutionAtCompactCurl_of_upgrade h hupgrade)

end Euler.ComparatorBridge

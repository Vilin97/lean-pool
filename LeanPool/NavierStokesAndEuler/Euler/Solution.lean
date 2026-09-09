/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SolutionDefinitions
import LeanPool.NavierStokesAndEuler.Euler.CanonicalVorticityConfinement
import LeanPool.NavierStokesAndEuler.Euler.CompactVorticityContradiction
import LeanPool.NavierStokesAndEuler.Euler.ComparatorIdentification
import LeanPool.NavierStokesAndEuler.Euler.ComparatorLocalEvolution
import LeanPool.NavierStokesAndEuler.Euler.ComparatorMaximalSolution
import LeanPool.NavierStokesAndEuler.Euler.EulerSingularity
import LeanPool.NavierStokesAndEuler.Euler.InitialDataBridge

/-!
The independent solution to the unforced Euler Comparator challenge.
Its definitions come from `SolutionDefinitions`, never from the reference
module or its placeholder theorem.
-/

@[expose] public section


noncomputable section

namespace Euler

open ComparatorBridge EulerPacketInduction Set MeasureTheory
open scoped ENNReal Topology

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

private theorem initialDatum_no_global_solution :
    ¬ (∃ v p, EulerExistenceAndSmoothnessR3 initialDatum.field v p) := by
  rintro ⟨v, p, h⟩
  exact finiteLifespan_contradiction_of_compact_vorticity lifespan h
    canonicalVorticityBall canonicalVorticityBall_compact
    (maximalVelocity_eq_of_compactCurlLocalUpgrade lifespan h
      canonical_vorticity_hasCompactSupport compactCurlLocalUpgrade)
    canonical_vorticity_eq_zero_outside

/-- Smooth, rapidly decaying, divergence-free Euler data admitting no global smooth solution
with uniformly bounded kinetic energy. -/
theorem euler_breakdown_R3 :
    ∃ u₀ : ℝ³ → ℝ³, InitialVelocityConditionDecay u₀ ∧
      ¬ (∃ v p, EulerExistenceAndSmoothnessR3 u₀ v p) := by
  exact ⟨initialDatum.field,
    initialVelocityConditionDecay_of_compact initialDatum.field initialDatum.smooth
      initialDatum_compact initialDatum_divergence, initialDatum_no_global_solution⟩

-- Match the reference's elaboration of ENNReal suprema independently of import order.
attribute [local instance] CompletePartialOrder.toSupSet

/-- Compactly supported smooth Euler data with a finite maximal Sobolev lifespan.
At the terminal time, the velocity C¹ norm has infinite left limsup and the time integral
of the vorticity supremum diverges. The solution has uniformly bounded kinetic energy
throughout its lifespan and admits no global smooth continuation with that energy bound. -/
theorem exists_compact_smooth_euler_singularity :
    ∃ (u₀ : ℝ³ → ℝ³) (Tstar : ℝ) (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
      InitialVelocityConditionDecay u₀ ∧ HasCompactSupport u₀ ∧ u₀ ≠ 0 ∧
      0 < Tstar ∧ Tstar ≤ 1 ∧
      EulerSobolevExistenceAndSmoothnessR3On (Ico 0 Tstar) u₀ v p ∧
      (∃ E : ℝ, ∀ t ∈ Ico (0 : ℝ) Tstar, (∫ x : ℝ³, ‖v x t‖ ^ 2) < E) ∧
      (∀ T : ℝ, 0 < T →
        ((∃ w q, EulerSobolevExistenceAndSmoothnessR3On (Icc 0 T) u₀ w q) ↔ T < Tstar)) ∧
      (∀ T ∈ Ioo 0 Tstar,
        (⨆ t ∈ Icc (0 : ℝ) T, velocityC1Norm (v · t)) < ⊤ ∧
        (∫⁻ t in Ico (0 : ℝ) T, vorticityNorm (v · t)) < ⊤) ∧
      Filter.limsup (fun t : ℝ => velocityC1Norm (v · t)) (𝓝[<] Tstar) = ⊤ ∧
      (∫⁻ t in Ico (0 : ℝ) Tstar, vorticityNorm (v · t)) = ⊤ ∧
      ¬ (∃ w q, EulerExistenceAndSmoothnessR3 u₀ w q) := by
  refine ⟨initialDatum.field, lifespan.duration, maximalVelocityExtension lifespan,
    maximalPressureExtension lifespan, ?_, initialDatum_compact, initialDatum_nonzero,
    lifespan.duration_pos, lifespan_le_one, maximal_sobolevSolution lifespan,
    maximalVelocityExtension_bounded_energy lifespan, ?_, ?_,
    maximalVelocityExtension_c1_limsup lifespan,
    maximalVelocityExtension_vorticity_integral lifespan, initialDatum_no_global_solution⟩
  · exact initialVelocityConditionDecay_of_compact initialDatum.field initialDatum.smooth
      initialDatum_compact initialDatum_divergence
  · intro T hT
    exact maximal_sobolev_existence_iff lifespan T hT
  · intro T hT
    exact ⟨maximalVelocityExtension_c1_locally_bounded lifespan T hT.1 hT.2,
      maximalVelocityExtension_vorticity_locally_integrable lifespan T hT.1 hT.2⟩

end Euler

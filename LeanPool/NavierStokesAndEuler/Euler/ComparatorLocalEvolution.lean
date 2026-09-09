/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ComparatorEvolutionIdentification
public import LeanPool.NavierStokesAndEuler.Euler.DivCurlTensorRecovery
public import LeanPool.NavierStokesAndEuler.Euler.ClassicalBridge
import LeanPool.NavierStokesAndEuler.Euler.CompactProjectedEulerLaw
import LeanPool.NavierStokesAndEuler.Euler.CompactVorticityTimeUpgrade
import LeanPool.NavierStokesAndEuler.Euler.ComparatorLocalCompactVorticity
import LeanPool.NavierStokesAndEuler.Euler.ComparatorTruncationFamily
import LeanPool.NavierStokesAndEuler.Euler.ComparatorUniformSpatialJets

/-!
# The concrete local Comparator-to-development conversion

Compact initial vorticity remains in one compact set for a positive time.
Elliptic recovery gives all spatial L² derivatives on that interval, and
the genuine Euler pairings against dense compact solenoidal tests provide
the time regularity needed for an ordinary Euler evolution.
-/

@[expose] public section


noncomputable section


namespace Euler.ComparatorBridge

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerOrdinarySobolev
  EulerMeanSolenoidal EulerMeanHarmonic EulerMeanCutoffCurl EulerComparatorRecovery
open scoped ContDiff Topology

variable {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}

/-- Actual ordinary smooth-L² velocity slices recovered from a common compact
vorticity support. The fields are definitionally the Comparator velocity. -/
def recoveredVelocity (h : EulerExistenceAndSmoothnessR3 u₀ v p)
    (T : ℝ) (K : Set Space) (hK : IsCompact K)
    (hsupport : ∀ t ∈ Icc (0 : ℝ) T, tsupport (vectorCurl (v · t)) ⊆ K) :
    Icc (0 : ℝ) T → SmoothL2Field Space := fun t =>
  smoothL2FieldOfCurlCompact (v · (t : ℝ))
    (h.velocity_contDiff t t.property.1)
    (h.velocity_memLp t t.property.1)
    (fun x => h.div_free x t t.property.1)
    (hK.of_isClosed_subset (isClosed_tsupport _) (hsupport t t.property))

@[simp] theorem recoveredVelocity_field (h : EulerExistenceAndSmoothnessR3 u₀ v p)
    (T : ℝ) (K : Set Space) (hK : IsCompact K)
    (hsupport : ∀ t ∈ Icc (0 : ℝ) T, tsupport (vectorCurl (v · t)) ⊆ K)
    (t : Icc (0 : ℝ) T) :
    (recoveredVelocity h T K hK hsupport t).field = (v · (t : ℝ)) := rfl

/-- All genuine spatial L² tensor norms are uniformly bounded on the common
compact-vorticity interval. No time regularity of these norms is assumed. -/
theorem recoveredVelocity_jetLp_uniform (h : EulerExistenceAndSmoothnessR3 u₀ v p)
    (T : ℝ) (K : Set Space) (hK : IsCompact K)
    (hsupport : ∀ t ∈ Icc (0 : ℝ) T, tsupport (vectorCurl (v · t)) ⊆ K) :
    ∀ n : ℕ, ∃ M : ℝ, ∀ t,
      ‖(recoveredVelocity h T K hK hsupport t).jetLp n‖ ≤ M := by
  intro n
  refine jetLp_norm_uniform_of_coordinate_energy
    (recoveredVelocity h T K hK hsupport) ?_ n
  intro j word
  obtain ⟨B, hB⟩ := h.component_word_energy_uniform_of_commonCompactCurl
    T K hK hsupport j word
  exact ⟨B, fun t => hB t t.property⟩

/-- A Comparator Euler solution with a common compact vorticity support is
represented by an actual ordinary evolution throughout that interval. -/
theorem exists_evolution_of_commonCompactCurl
    (h : EulerExistenceAndSmoothnessR3 u₀ v p)
    (T : ℝ) (hT : 0 < T) (K : Set Space) (hK : IsCompact K)
    (hsupport : ∀ t ∈ Icc (0 : ℝ) T, tsupport (vectorCurl (v · t)) ⊆ K) :
    ∃ U : Evolution T hT.le,
      ∀ t : Icc (0 : ℝ) T, (U.velocity t).field = (v · (t : ℝ)) := by
  let A := recoveredVelocity h T K hK hsupport
  have hA (t : Icc (0 : ℝ) T) : (A t).field = (v · (t : ℝ)) := rfl
  have hscalar : IsSmoothScalarEuler (hT := hT.le) A := by
    apply isSmoothScalarEuler_of_weak_projectedEquation hT A
      (comparator_velocity_mem_solenoidal h A hA)
      (tensorNorm_uniform_of_jetLp_uniform A
        (recoveredVelocity_jetLp_uniform h T K hK hsupport))
      compactSolenoidalTests compactSolenoidalTests_dense
    · intro φ _
      exact comparator_weak_pairings_continuous h A hA φ
    · intro φ hφ t ht
      exact comparator_projected_pairing_hasDerivAt h hT A hA φ hφ t ht
  obtain ⟨U, hU⟩ := (exists_evolution_iff_scalar (hT := hT.le) hT A).mpr hscalar
  refine ⟨U, ?_⟩
  intro t
  rw [hU]
  exact hA t

/-- Compact initial vorticity alone supplies the complete local conversion:
the truncations, support propagation, spatial recovery, and time regularity
are all obtained from the actual Comparator solution assumptions. -/
theorem compactCurlLocalUpgrade : CompactCurlLocalUpgrade := by
  intro u₀ v p h hc
  obtain ⟨δ, B, hδ, hsupport⟩ :=
    h.local_compact_vorticity_of_truncationFamily h.finiteEnergyTruncationFamily hc
  obtain ⟨U, hU⟩ := exists_evolution_of_commonCompactCurl h δ hδ
    (Metric.closedBall (0 : Space) B) (isCompact_closedBall _ _) hsupport
  exact ⟨δ, hδ, U, hU⟩

end Euler.ComparatorBridge

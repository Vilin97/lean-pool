/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.SafeAverageAnalytic
import LeanPool.PoincareThreeBody.PoincareSet

/-!
# Separation of resonant disturbing averages in the collision band

The safe average stays finite at the boundary, while the aligned average tends to negative
infinity.  Hence the two orientation phases separate at an admissible eccentricity.
-/

namespace LeanPool.PoincareThreeBody

open Filter Set Topology

theorem exists_separating_resonantDisturbingAverages_of_collision_band
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (haxisHalf : 1 / 2 < resonantSemimajorAxis p q)
    (haxisOne : resonantSemimajorAxis p q < 1) :
    ∃ phaseA phaseB : ℝ, ∃ witness ∈ admissibleResonantEccentricitySet p q,
      resonantDisturbingAverage p q witness phaseA -
        resonantDisturbingAverage p q witness phaseB ≠ 0 := by
  let collisionEccentricity := resonantCollisionEccentricity p q
  let safeAverage : ℝ → ℝ := fun eccentricity ↦
    resonantDisturbingAverage p q eccentricity (resonantSafeOrientation p q)
  have hsafeContinuous : ContinuousAt safeAverage collisionEccentricity :=
    (analyticAt_resonantDisturbingAverage_safe_collisionBoundary
      hp hq haxisHalf haxisOne).continuousAt
  have hsafeEventually : ∀ᶠ eccentricity in 𝓝 collisionEccentricity,
      safeAverage collisionEccentricity - 1 < safeAverage eccentricity := by
    exact hsafeContinuous.eventually
      (isOpen_Ioi.mem_nhds (by linarith :
        safeAverage collisionEccentricity - 1 < safeAverage collisionEccentricity))
  rcases Metric.eventually_nhds_iff.mp hsafeEventually with
    ⟨radius, hradius, hsafeLocal⟩
  let lowerEccentricity := collisionEccentricity - radius / 2
  have hlower : lowerEccentricity < resonantCollisionEccentricity p q := by
    dsimp [lowerEccentricity, collisionEccentricity]
    linarith
  rcases exists_collisionAligned_resonantDisturbingAverage_between hp hq
      haxisHalf haxisOne hlower (safeAverage collisionEccentricity - 1) with
    ⟨witness, hwitnessLower, hwitnessNonnegative, hwitnessBoundary,
      hwitnessOne, haligned⟩
  have hwitnessNear : dist witness collisionEccentricity < radius := by
    rw [Real.dist_eq, abs_of_nonpos]
    · dsimp [lowerEccentricity] at hwitnessLower
      linarith
    · exact sub_nonpos.mpr hwitnessBoundary.le
  have hsafe := hsafeLocal hwitnessNear
  have hseparated :
      resonantDisturbingAverage p q witness (resonantCollisionOrientation p q) <
        resonantDisturbingAverage p q witness (resonantSafeOrientation p q) := by
    exact haligned.trans hsafe
  have hapoapsis := resonant_apoapsis_lt_one_of_eccentricity_lt_collision
    hp hq hwitnessBoundary
  refine ⟨resonantCollisionOrientation p q, resonantSafeOrientation p q,
    witness, ?_, ?_⟩
  · exact ⟨hwitnessNonnegative, hwitnessOne, by
      simpa [resonantSemimajorAxis] using hapoapsis⟩
  · linarith

/-- For every rational resonance in the collision band, nondegenerate eccentricities are dense
in the whole admissible fiber. -/
theorem dense_nondegenerateResonantEccentricities_of_collision_band
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (haxisHalf : 1 / 2 < resonantSemimajorAxis p q)
    (haxisOne : resonantSemimajorAxis p q < 1) :
    Dense (nondegenerateResonantEccentricities p q) := by
  rcases exists_separating_resonantDisturbingAverages_of_collision_band
      hp hq haxisHalf haxisOne with
    ⟨phaseA, phaseB, witness, hwitness, hvalues⟩
  let difference : ℝ → ℝ := fun eccentricity ↦
    resonantDisturbingAverage p q eccentricity phaseA -
      resonantDisturbingAverage p q eccentricity phaseB
  have hnonempty : (admissibleResonantEccentricitySet p q).Nonempty :=
    ⟨witness, hwitness⟩
  have hanalytic : AnalyticOnNhd ℝ difference
      (admissibleResonantEccentricitySet p q) :=
    (analyticOnNhd_resonantDisturbingAverage_eccentricity hp hq phaseA).sub
      (analyticOnNhd_resonantDisturbingAverage_eccentricity hp hq phaseB)
  have hdense : Dense
      {eccentricity : AdmissibleResonantEccentricity p q |
        difference eccentricity.1 ≠ 0} := by
    apply dense_nonzero_of_analyticOnNhd
      (isOpen_admissibleResonantEccentricitySet p q)
      (isConnected_admissibleResonantEccentricitySet hnonempty)
      (f := difference) (witness := witness)
    · exact hanalytic
    · exact hwitness
    · exact hvalues
  apply hdense.mono
  intro eccentricity heccentricity
  apply exists_deriv_resonantDisturbingAverage_ne_zero_of_values_ne
    hp hq eccentricity.2.1.le eccentricity.2.2.1 eccentricity.2.2.2
  exact sub_ne_zero.mp heccentricity

end LeanPool.PoincareThreeBody

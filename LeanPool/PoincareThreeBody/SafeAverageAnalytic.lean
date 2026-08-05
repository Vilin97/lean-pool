/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.SafeCollisionPhase
import LeanPool.PoincareThreeBody.AnalyticCompactParameterIntegral

/-!
# Analyticity of the collision-avoiding average at the boundary

Compactness of one resonant period upgrades pointwise collision avoidance to a uniform parameter
neighborhood.  The compact parameter-integral theorem then gives analyticity of the safe average
through the collision eccentricity.
-/

namespace LeanPool.PoincareThreeBody

open Filter MeasureTheory Set Topology

/-- Squared distance from the primary along the collision-avoiding resonant orientation. -/
noncomputable def safePrimaryDistanceSq
    (p q : ℕ) (parameters : ℝ × ℝ) : ℝ :=
  (orientedResonantEllipsePosition p q parameters.1
      (resonantSafeOrientation p q) parameters.2 0 - 1) ^ 2 +
    orientedResonantEllipsePosition p q parameters.1
      (resonantSafeOrientation p q) parameters.2 1 ^ 2

theorem analyticAt_safePrimaryDistanceSq
    (p q : ℕ) {eccentricity time : ℝ}
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1) :
    AnalyticAt ℝ (safePrimaryDistanceSq p q) (eccentricity, time) := by
  have hx := analyticAt_orientedResonantEllipsePosition_eccentricity_time_coordinate
    p q (orientation := resonantSafeOrientation p q) (time := time)
      heccentricity heccentricityOne 0
  have hy := analyticAt_orientedResonantEllipsePosition_eccentricity_time_coordinate
    p q (orientation := resonantSafeOrientation p q) (time := time)
      heccentricity heccentricityOne 1
  exact (((hx.sub analyticAt_const).pow 2).add (hy.pow 2)).congr (by
    filter_upwards [] with parameters
    rfl)

theorem isOpen_safeCollisionFreeParameters (p q : ℕ) :
    IsOpen {parameters : ℝ × ℝ |
      0 < parameters.1 ∧ parameters.1 < 1 ∧ safePrimaryDistanceSq p q parameters ≠ 0} := by
  rw [isOpen_iff_mem_nhds]
  intro parameters hparameters
  have hdistance := (analyticAt_safePrimaryDistanceSq p q
    hparameters.1 hparameters.2.1).continuousAt
      (isOpen_compl_singleton.mem_nhds hparameters.2.2)
  filter_upwards [
    (isOpen_lt continuous_const continuous_fst).mem_nhds hparameters.1,
    (isOpen_lt continuous_fst continuous_const).mem_nhds hparameters.2.1,
    hdistance] with candidate hpositive hone hne
  exact ⟨hpositive, hone, hne⟩

/-- The safe disturbing average extends analytically through the aligned collision boundary. -/
theorem analyticAt_resonantDisturbingAverage_safe_collisionBoundary
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (haxisHalf : 1 / 2 < resonantSemimajorAxis p q)
    (haxisOne : resonantSemimajorAxis p q < 1) :
    AnalyticAt ℝ (fun eccentricity ↦
      resonantDisturbingAverage p q eccentricity (resonantSafeOrientation p q))
      (resonantCollisionEccentricity p q) := by
  let collisionEccentricity := resonantCollisionEccentricity p q
  let timeSet := Icc 0 (resonantOrbitPeriod p)
  let collisionFreeParameters : Set (ℝ × ℝ) := {parameters |
    0 < parameters.1 ∧ parameters.1 < 1 ∧ safePrimaryDistanceSq p q parameters ≠ 0}
  have hcollisionEccentricity : 0 < collisionEccentricity :=
    resonantCollisionEccentricity_pos hp hq haxisOne
  have hcollisionEccentricityOne : collisionEccentricity < 1 :=
    resonantCollisionEccentricity_lt_one hp hq haxisHalf
  have htimeCompact : IsCompact timeSet := isCompact_Icc
  have hcollisionFreeOpen : IsOpen collisionFreeParameters :=
    isOpen_safeCollisionFreeParameters p q
  have hboundarySubset : {collisionEccentricity} ×ˢ timeSet ⊆ collisionFreeParameters := by
    rintro ⟨eccentricity, time⟩ ⟨heccentricity, htime⟩
    have heccentricityEq : eccentricity = collisionEccentricity := by
      simpa only [mem_singleton_iff] using heccentricity
    subst eccentricity
    exact ⟨hcollisionEccentricity, hcollisionEccentricityOne,
      safeOrientation_primaryDistance_ne_zero_at_collisionBoundary
        hp hq haxisHalf haxisOne time⟩
  obtain ⟨parameterNeighborhood, timeNeighborhood, hparameterOpen, htimeOpen,
      hparameterContains, htimeContains, hproductSubset⟩ :=
    generalized_tube_lemma isCompact_singleton htimeCompact
      hcollisionFreeOpen hboundarySubset
  have hparameterNeighborhood : parameterNeighborhood ∈ 𝓝 collisionEccentricity :=
    hparameterOpen.mem_nhds (hparameterContains (mem_singleton collisionEccentricity))
  have hintegrable : ∀ᶠ eccentricity in 𝓝 collisionEccentricity,
      IntegrableOn (fun time ↦ resonantDisturbingFunction p q eccentricity
        (resonantSafeOrientation p q) time) timeSet := by
    filter_upwards [hparameterNeighborhood] with eccentricity heccentricity
    have hparameters : ∀ time ∈ timeSet,
        0 < eccentricity ∧ eccentricity < 1 ∧
          safePrimaryDistanceSq p q (eccentricity, time) ≠ 0 := by
      intro time htime
      have htimeNeighborhoodMem : time ∈ timeNeighborhood := htimeContains htime
      have hpair : (eccentricity, time) ∈
          parameterNeighborhood ×ˢ timeNeighborhood :=
        ⟨heccentricity, htimeNeighborhoodMem⟩
      exact hproductSubset hpair
    have hcontinuous : ContinuousOn
        (resonantDisturbingFunction p q eccentricity (resonantSafeOrientation p q))
        timeSet := by
      intro time htime
      have hjoint :=
        analyticAt_resonantDisturbingFunction_eccentricity_time_of_primaryDistance_ne_zero
          hp hq (hparameters time htime).1 (hparameters time htime).2.1
            (hparameters time htime).2.2
      have hinclusion : AnalyticAt ℝ (fun candidate : ℝ ↦ (eccentricity, candidate)) time :=
        analyticAt_const.prod analyticAt_id
      exact (hjoint.comp hinclusion).continuousAt.continuousWithinAt
    exact hcontinuous.integrableOn_compact htimeCompact
  have hsetIntegral : AnalyticAt ℝ (fun eccentricity ↦
      ∫ time in timeSet,
        resonantDisturbingFunction p q eccentricity
          (resonantSafeOrientation p q) time) collisionEccentricity := by
    apply analyticAt_setIntegral_of_joint_analytic
      (function := fun parameters : ℝ × ℝ ↦
        resonantDisturbingFunction p q parameters.1
          (resonantSafeOrientation p q) parameters.2)
      (centerParameter := collisionEccentricity) (timeSet := timeSet)
      htimeCompact
    · intro time htime
      apply analyticAt_resonantDisturbingFunction_eccentricity_time_of_primaryDistance_ne_zero
        hp hq hcollisionEccentricity hcollisionEccentricityOne
      exact safeOrientation_primaryDistance_ne_zero_at_collisionBoundary
        hp hq haxisHalf haxisOne time
    · exact hintegrable
  have hperiod : 0 ≤ resonantOrbitPeriod p := by
    unfold resonantOrbitPeriod
    positivity
  apply hsetIntegral.congr
  filter_upwards [] with eccentricity
  unfold resonantDisturbingAverage
  dsimp [timeSet]
  rw [intervalIntegral.integral_of_le hperiod, ← integral_Icc_eq_integral_Ioc]

end LeanPool.PoincareThreeBody

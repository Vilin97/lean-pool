/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteLifespan
import LeanPool.NavierStokesAndEuler.Euler.PacketFirstStageSupport
import LeanPool.NavierStokesAndEuler.Euler.PacketInitialDatumSupport

/-! A compactly supported, smooth, divergence-free initial velocity
whose ordinary smooth Euler solutions have a finite maximal horizon.
The separate continuation and vorticity criteria are not asserted here. -/

@[expose] public section


noncomputable section

namespace EulerPacketInduction

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerOrdinarySobolev EulerPacketBaseGuardScales
open scoped ContDiff

theorem initialDatum_support : tsupport initialDatum.field ⊆ Metric.closedBall 0 2 :=
  Stage.initialDataLimit_support_of_physical packets le_rfl le_rfl
    (constructionScales.firstForwardStage_initial_support le_rfl le_rfl)

theorem initialDatum_compact : HasCompactSupport initialDatum.field :=
  (isCompact_closedBall (0 : Space) 2).of_isClosed_subset (isClosed_tsupport _) initialDatum_support

theorem lifespan_le_one : lifespan.duration ≤ 1 :=
  lifespan_le_base.trans constructionScales.time_small

/-- Has smooth euler solution, given by `∃ hT : 0 < T, ∃ U : Evolution T hT.le, (U.velocity
⟨0,le_rfl,hT.le⟩).field=u₀`. -/
def HasSmoothEulerSolution (u₀ : Space → Space) (T : ℝ) : Prop :=
  ∃ hT : 0 < T, ∃ U : Evolution T hT.le,
    (U.velocity ⟨0,le_rfl,hT.le⟩).field=u₀

theorem hasSmoothEulerSolution_iff (A : SmoothL2Field Space) (T : ℝ) :
    HasSmoothEulerSolution A.field T ↔ HasEulerEvolution A T := by
  constructor
  · rintro ⟨hT,U,hU⟩
    exact ⟨hT,U,field_ext hU⟩
  · rintro ⟨hT,U,hU⟩
    exact ⟨hT,U,congrArg SmoothL2Field.field hU⟩

theorem exists_compact_smooth_finite_lifespan :
    ∃ u₀ : Space → Space, ContDiff ℝ ∞ u₀ ∧ HasCompactSupport u₀ ∧
      (∀ x, divergence u₀ x=0) ∧
      ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧
        (∀ t : ℝ, 0 < t → t < T → HasSmoothEulerSolution u₀ t) ∧
        (∀ t : ℝ, T < t → ¬ HasSmoothEulerSolution u₀ t) := by
  refine ⟨initialDatum.field,initialDatum.smooth,initialDatum_compact,initialDatum_divergence,
    lifespan.duration,lifespan.duration_pos,lifespan_le_one,?_,?_⟩
  · intro t ht htT
    exact (hasSmoothEulerSolution_iff initialDatum t).mpr (lifespan.shorter t ht htT)
  · intro t hTt h
    exact lifespan.maximal t hTt ((hasSmoothEulerSolution_iff initialDatum t).mp h)

end EulerPacketInduction

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInfiniteConstruction
public import LeanPool.NavierStokesAndEuler.Euler.PacketStageInitialLimit
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerLifespan
import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalConstraints
import LeanPool.NavierStokesAndEuler.Euler.PacketStageLocalExistence

/-! The limiting initial datum of the actual recursive packet family.
Its genuine Euler solutions have a positive, finite maximal horizon. -/

@[expose] public section


noncomputable section

namespace EulerPacketInduction

open Set Filter EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerPhysicalL2Scaling EulerPacketBaseGuardScales EulerOrdinarySobolev
  EulerMeanSolenoidal EulerMeanClassical
open scoped Topology

/-- Initial datum, given by `Stage.initialDataLimit packets le_rfl le_rfl`. -/
def initialDatum : SmoothL2Field Space := Stage.initialDataLimit packets le_rfl le_rfl

theorem initialDatum_Hm (s : ℕ) :
    Tendsto (fun n => derivativeSum s
      ((fun x => (packets n).state.evolution.velocity (0,x))-initialDatum.field))
      atTop (𝓝 0) :=
  Stage.initialDataLimit_Hm packets le_rfl le_rfl
    (fun n hn => stages_initial_step constructionScales le_rfl le_rfl n hn) s

theorem initialDatum_local : ∃ T, HasEulerEvolution initialDatum T := by
  obtain ⟨T,hT,_,U,hU⟩ := Stage.exists_local_evolution packets initialDatum initialDatum_Hm
  exact ⟨T,hT,U,field_ext hU⟩

theorem initialDatum_no_base :
    ¬ HasEulerEvolution initialDatum (baseHorizon constructionScales.J constructionScales.X) := by
  rintro ⟨hT,U,hU⟩
  have hno := Stage.initialDataLimit_no_euler packets le_rfl le_rfl
    (fun n hn => stages_initial_step constructionScales le_rfl le_rfl n hn)
  exact hno ⟨U,congrArg SmoothL2Field.field hU⟩

theorem initialDatum_solenoidal : initialDatum.toLp ∈ solenoidalSpace := by
  obtain ⟨T,hT,U,hU⟩ := initialDatum_local
  exact hU ▸ U.solenoidal ⟨0,le_rfl,hT.le⟩

theorem initialDatum_divergence (x : Space) : divergence initialDatum.field x=0 :=
  solenoidal_representative_divergence initialDatum.toLp initialDatum_solenoidal
    initialDatum.field initialDatum.smooth initialDatum.toLp_ae x

theorem initialDatum_finite_lifespan :
    ∃ L : FiniteLifespan initialDatum,
      L.duration ≤ baseHorizon constructionScales.J constructionScales.X :=
  exists_finite_lifespan initialDatum
    (baseHorizon constructionScales.J constructionScales.X)
    (baseHorizon_pos constructionScales.J constructionScales.j_one constructionScales.x_pos)
    initialDatum_local initialDatum_no_base

/-- Lifespan, given by `initialDatum_finite_lifespan.choose`. -/
def lifespan : FiniteLifespan initialDatum := initialDatum_finite_lifespan.choose

theorem lifespan_le_base :
    lifespan.duration ≤ baseHorizon constructionScales.J constructionScales.X :=
  initialDatum_finite_lifespan.choose_spec

end EulerPacketInduction

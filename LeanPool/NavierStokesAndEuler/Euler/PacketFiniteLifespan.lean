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
public import LeanPool.NavierStokesAndEuler.Euler.PacketInductionStage
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerDifference
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryH3Norms
public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldPhysicalSobolev
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryAdvectionLimit
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerLocalCauchy
import LeanPool.NavierStokesAndEuler.Euler.PacketInductionScaleBounds
import LeanPool.NavierStokesAndEuler.Euler.ParentOrdinaryEvolution
import LeanPool.NavierStokesAndEuler.Euler.SmoothL2Series

/-! The limiting initial datum of the actual recursive packet family.
Its genuine Euler solutions have a positive, finite maximal horizon. -/

section

/-! An actual stage family with convergent initial data has a genuine
positive-time Euler solution for its limiting datum. Only the already
proved common packet interval and actual stability are used. -/

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open Finset EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field

theorem tensorNorm_sub_triangle (A B C : SmoothL2Field Space) (s : ℕ) :
    tensorNorm s (fieldSub A B) ≤ tensorNorm s (fieldSub A C)+tensorNorm s (fieldSub B C) := by
  simp only [tensorNorm,← sum_add_distrib,jetLp_fieldSub]
  apply sum_le_sum
  intro n _
  calc
    ‖A.jetLp n-B.jetLp n‖ = ‖(A.jetLp n-C.jetLp n)-(B.jetLp n-C.jetLp n)‖ := by congr 1; abel
    _ ≤ _ := norm_sub_le _ _

end EulerOrdinarySobolev

namespace EulerPacketInduction.Stage

open Set Real Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerPhysicalL2Scaling EulerOrdinarySobolev
  EulerPacketInductionScales EulerPacketBaseGuardScales EulerSmoothL2Series
open scoped Topology

variable {c B : ℝ} {S : Scales c B} (P : ∀ n, Stage S n) (u₀ : SmoothL2Field Space)
  (hinit : ∀ q, Tendsto (fun n => derivativeSum q
    ((fun x => (P n).state.evolution.velocity (0, x)) - u₀.field)) atTop (𝓝 0))

include hinit in
theorem exists_local_evolution :
    ∃ L : ℝ, ∃ hL : 0 < L, L ≤ baseHorizon S.J S.X/12 ∧
      ∃ E : Evolution L hL.le, (E.velocity ⟨0,le_rfl,hL.le⟩).field=u₀.field := by
  let T := baseHorizon S.J S.X/12
  have hT : 0 < T := div_pos (baseHorizon_pos S.J S.j_one S.x_pos) (by norm_num)
  let V : ℕ → Evolution T hT.le := fun n =>
    ((P n).state.regularity.ordinaryEvolution).restrictTime T hT.le (P n).horizon_lower.le
  have hv (n : ℕ) : ((V n).velocity ⟨0,le_rfl,hT.le⟩).field =
      fun x => (P n).state.evolution.velocity (0,x) := by
    funext x
    exact ((P n).state.regularity.velocity_match ⟨0,le_rfl,(P n).parent.T_pos.le⟩ x).symm
  have herr (q : ℕ) : Tendsto (fun n => tensorNorm q
      (fieldSub ((V n).velocity ⟨0,le_rfl,hT.le⟩) u₀)) atTop (𝓝 0) := by
    have heq (n : ℕ) : tensorNorm q (fieldSub ((V n).velocity ⟨0,le_rfl,hT.le⟩) u₀) =
        derivativeSum q ((fun x => (P n).state.evolution.velocity (0,x))-u₀.field) := by
      rw [tensorNorm_eq_derivativeSum]
      congr 1
      funext x
      rw [fieldSub_field]
      exact congrArg (fun f : Space → Space => f x-u₀.field x) (hv n)
    simpa only [heq] using hinit q
  have hCauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i, N ≤ i → ∀ j, N ≤ j →
      tensorNorm 3 (fieldSub ((V i).velocity ⟨0,le_rfl,hT.le⟩)
        ((V j).velocity ⟨0,le_rfl,hT.le⟩)) ≤ ε := by
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp ((herr 3).eventually_le_const (by positivity : 0 < ε/2))
    refine ⟨N,?_⟩
    intro i hi j hj
    have h := tensorNorm_sub_triangle ((V i).velocity ⟨0,le_rfl,hT.le⟩)
      ((V j).velocity ⟨0,le_rfl,hT.le⟩) u₀ 3
    linarith only [h,hN i hi,hN j hj]
  have hb : ∀ q, ∃ R : ℝ, ∀ n, tensorNorm q ((V n).velocity ⟨0,le_rfl,hT.le⟩) ≤ R := by
    intro q
    obtain ⟨R,hR⟩ := (herr q).bddAbove_range
    refine ⟨R+tensorNorm q u₀,?_⟩
    intro n
    exact (tensorNorm_le_sub_add ((V n).velocity ⟨0,le_rfl,hT.le⟩) u₀ q).trans
      (add_le_add (hR (mem_range_self n)) le_rfl)
  have hu : Tendsto (fun n => ((V n).velocity ⟨0,le_rfl,hT.le⟩).toLp) atTop (𝓝 u₀.toLp) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [tensorNorm_zero,toLp_fieldSub] using herr 0
  obtain ⟨L,hL,hLT,E,hE⟩ := exists_local_evolution_of_cauchy V hT hCauchy hb u₀.toLp hu
  refine ⟨L,hL,hLT,E,?_⟩
  have hae : (E.velocity ⟨0,le_rfl,hL.le⟩).field=ᵐ[volume] u₀.field :=
    (E.velocity ⟨0,le_rfl,hL.le⟩).toLp_ae.symm.trans (hE ▸ u₀.toLp_ae)
  exact Measure.eq_of_ae_eq hae (E.velocity ⟨0,le_rfl,hL.le⟩).smooth.continuous u₀.smooth.continuous

end EulerPacketInduction.Stage

end
end

end

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

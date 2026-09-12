/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerMaximal
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerContinuation
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteLifespan
import LeanPool.NavierStokesAndEuler.Euler.PacketFirstStageSupport
public import LeanPool.NavierStokesAndEuler.Euler.PacketStageInitialLimit

/-! C¹ breakdown for the concrete compactly supported datum. The
infinite-limsup statement is expressed directly: after every time below
the maximal time, the actual gradient supremum exceeds every real bound.
The norms are bounded-continuous-function norms at individual times,
not totalized real L∞ seminorms of unverified measurable fields. -/

section

/-! The full smooth initial datum retains the common support of its
finite initial base and its actual summable packet increments. -/

@[expose] public section

noncomputable section

namespace EulerPacketInduction.Stage

open Set EulerSmoothLimit EulerPacketInductionScales EulerPacketLowConstants
  EulerParentNeighborThreshold EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence
  EulerNormalPacketParameters EulerPacketInitial EulerLpTranslation
  EulerLpTranslation.SmoothL2Field

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} (P : ∀ n, Stage S n)
  (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)

theorem initialDataLimit_support
    (hbase : tsupport (initialBase P).field ⊆ Metric.closedBall 0 2) :
    tsupport (initialDataLimit P hq hB).field ⊆ Metric.closedBall 0 2 := by
  let tail := initialLimit (initialTailInput P hq hB) (S.J+1)
    (by have h := S.stage_large; omega) (sourceConstant 4) 320 (sourceConstant_pos 4)
    (by norm_num) 20 1000 (scaleSequence S.J S.X 1) (S.sequence_one 1)
    (initialTail_parameter P hq hB) (initialTail_scale P hq hB) (initialTail_sigma P hq hB)
    (initialTail_four (S := S)) (initialTail_frequency P hq hB)
  have htail : tsupport tail.field ⊆ Metric.closedBall 0 2 :=
    initialLimit_support (initialTailInput P hq hB) (S.J+1)
      (by have h := S.stage_large; omega) (sourceConstant 4) 320 (sourceConstant_pos 4)
      (by norm_num) 20 1000 (scaleSequence S.J S.X 1) (S.sequence_one 1)
      (initialTail_parameter P hq hB) (initialTail_scale P hq hB) (initialTail_sigma P hq hB)
      (initialTail_four (S := S)) (initialTail_frequency P hq hB)
  change tsupport ((initialBase P).field+tail.field) ⊆ Metric.closedBall 0 2
  exact (tsupport_add _ _).trans (union_subset hbase htail)

theorem initialDataLimit_compact
    (hbase : tsupport (initialBase P).field ⊆ Metric.closedBall 0 2) :
    HasCompactSupport (initialDataLimit P hq hB).field :=
  (isCompact_closedBall (0 : Space) 2).of_isClosed_subset (isClosed_tsupport _)
    (initialDataLimit_support P hq hB hbase)

theorem initialDataLimit_support_of_physical
    (hbase : tsupport (fun x => (P 1).state.evolution.velocity (0, x)) ⊆ Metric.closedBall 0 2) :
    tsupport (initialDataLimit P hq hB).field ⊆ Metric.closedBall 0 2 := by
  apply initialDataLimit_support P hq hB
  have he : (initialBase P).field=(fun x => (P 1).state.evolution.velocity (0, x)) :=
    funext (fun x => ((P 1).state.regularity.velocity_match (P 1).parent.zeroTime x).symm)
  rwa [he]

end EulerPacketInduction.Stage

end
end

end

section

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

end
end

end

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev.FiniteLifespan

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanSobolevBoundedField

variable {A : SmoothL2Field Space} (L : FiniteLifespan A)

/-- Maximal velocity norm, given by `‖finiteField (L.maximalField t)‖`. -/
def maximalVelocityNorm (t : L.Time) : ℝ := ‖finiteField (L.maximalField t)‖

/-- Maximal gradient norm, given by `‖finiteField (L.maximalField t).derivative‖`. -/
def maximalGradientNorm (t : L.Time) : ℝ := ‖finiteField (L.maximalField t).derivative‖

/-- Maximal C1 norm, given by `L.maximalVelocityNorm t+L.maximalGradientNorm t`. -/
def maximalC1Norm (t : L.Time) : ℝ := L.maximalVelocityNorm t+L.maximalGradientNorm t

theorem maximalVelocityNorm_nonneg (t : L.Time) : 0 ≤ L.maximalVelocityNorm t := norm_nonneg _

theorem maximalGradientNorm_nonneg (t : L.Time) : 0 ≤ L.maximalGradientNorm t := norm_nonneg _

theorem maximalVelocityNorm_le_iff (t : L.Time) (K : ℝ) :
    L.maximalVelocityNorm t ≤ K ↔ ∀ x, ‖L.maximalVelocity t x‖ ≤ K := by
  rw [maximalVelocityNorm,BoundedContinuousFunction.norm_le_of_nonempty]
  simp only [finiteField_apply,maximalVelocity]

theorem maximalGradientNorm_le_iff (t : L.Time) (K : ℝ) :
    L.maximalGradientNorm t ≤ K ↔ ∀ x, ‖fderiv ℝ (L.maximalVelocity t) x‖ ≤ K := by
  rw [maximalGradientNorm,BoundedContinuousFunction.norm_le_of_nonempty]
  simp only [finiteField_apply]
  rfl

theorem maximalVelocityNorm_continuous : Continuous L.maximalVelocityNorm :=
  (continuous_finiteField L.maximalField L.maximalField_jet_continuous).norm

theorem maximalGradientNorm_continuous : Continuous L.maximalGradientNorm :=
  (continuous_finiteField (fun t => (L.maximalField t).derivative)
    (continuous_jetLp_derivative L.maximalField L.maximalField_jet_continuous)).norm

theorem maximalC1Norm_continuous : Continuous L.maximalC1Norm :=
  L.maximalVelocityNorm_continuous.add L.maximalGradientNorm_continuous

theorem maximalGradientNorm_eq_evolution (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
    (t : Icc (0 : ℝ) S) :
    L.maximalGradientNorm (L.shorterTime S hSL t)=(L.evolution S hS hSL).gradientNormPath t := by
  change ‖finiteField (L.maximalField (L.shorterTime S hSL t)).derivative‖=_
  rw [L.maximalField_eq_evolution S hS hSL t]
  rfl

theorem maximalVelocity_gradient_unbounded_near_endpoint (τ K : ℝ) (hτ : τ < L.duration) :
    ∃ (t : L.Time) (x : Space), τ < t ∧ K < ‖fderiv ℝ (L.maximalVelocity t) x‖ := by
  obtain ⟨S,hS,hSL,t,x,ht,hx⟩ := L.gradient_unbounded_near_endpoint τ K hτ
  refine ⟨L.shorterTime S hSL t,x,ht,?_⟩
  rwa [L.maximalVelocity_eq_evolution S hS hSL t]

theorem maximalGradientNorm_unbounded_near_endpoint (τ K : ℝ) (hτ : τ < L.duration) :
    ∃ t : L.Time, τ < t ∧ K < L.maximalGradientNorm t := by
  obtain ⟨t,x,ht,hx⟩ := L.maximalVelocity_gradient_unbounded_near_endpoint τ K hτ
  exact ⟨t,ht,hx.trans_le ((L.maximalGradientNorm_le_iff t _).mp le_rfl x)⟩

theorem maximalC1Norm_unbounded_near_endpoint (τ K : ℝ) (hτ : τ < L.duration) :
    ∃ t : L.Time, τ < t ∧ K < L.maximalC1Norm t := by
  obtain ⟨t,ht,hK⟩ := L.maximalGradientNorm_unbounded_near_endpoint τ K hτ
  exact ⟨t,ht,hK.trans_le (le_add_of_nonneg_left (L.maximalVelocityNorm_nonneg t))⟩

end EulerOrdinarySobolev.FiniteLifespan

namespace EulerPacketInduction

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerOrdinarySobolev
open scoped ContDiff

/-- Maximal time: an abbreviation for `lifespan.Time`. -/
abbrev MaximalTime : Type := lifespan.Time

/-- Maximal velocity, given by `lifespan.maximalVelocity t`. -/
def maximalVelocity (t : MaximalTime) : Space → Space := lifespan.maximalVelocity t

/-- Maximal pressure, given by `lifespan.maximalPressure t`. -/
def maximalPressure (t : MaximalTime) : Space → ℝ := lifespan.maximalPressure t

/-- Maximal velocity norm, given by `lifespan.maximalVelocityNorm t`. -/
def maximalVelocityNorm (t : MaximalTime) : ℝ := lifespan.maximalVelocityNorm t

/-- Maximal gradient norm, given by `lifespan.maximalGradientNorm t`. -/
def maximalGradientNorm (t : MaximalTime) : ℝ := lifespan.maximalGradientNorm t

/-- Maximal C1 norm, given by `lifespan.maximalC1Norm t`. -/
def maximalC1Norm (t : MaximalTime) : ℝ := lifespan.maximalC1Norm t

theorem initialDatum_no_endpoint : ¬ HasSmoothEulerSolution initialDatum.field lifespan.duration :=
    by
  intro h
  exact lifespan.no_endpoint ((hasSmoothEulerSolution_iff initialDatum lifespan.duration).mp h)

theorem maximalVelocity_initial : maximalVelocity lifespan.initialTime=initialDatum.field :=
  lifespan.maximalVelocity_initial

theorem maximalVelocity_smooth (t : MaximalTime) : ContDiff ℝ ∞ (maximalVelocity t) :=
  lifespan.maximalVelocity_smooth t

theorem maximalVelocity_joint_continuous :
    Continuous (fun z : MaximalTime × Space => maximalVelocity z.1 z.2) :=
  lifespan.maximalVelocity_joint_continuous

theorem maximalVelocity_divergence (t : MaximalTime) (x : Space) :
    divergence (maximalVelocity t) x=0 := lifespan.maximalVelocity_divergence t x

theorem maximalPressure_spec (t : MaximalTime) :
    ContDiff ℝ ∞ (maximalPressure t) ∧ maximalPressure t 0=0 ∧
      ∀ x, _root_.gradient (maximalPressure t) x=(lifespan.maximalPressureField t).field x :=
  lifespan.maximalPressure_spec t

theorem maximalGradientNorm_spec (t : MaximalTime) (K : ℝ) :
    maximalGradientNorm t ≤ K ↔ ∀ x, ‖fderiv ℝ (maximalVelocity t) x‖ ≤ K :=
  lifespan.maximalGradientNorm_le_iff t K

theorem maximalVelocityNorm_spec (t : MaximalTime) (K : ℝ) :
    maximalVelocityNorm t ≤ K ↔ ∀ x, ‖maximalVelocity t x‖ ≤ K :=
  lifespan.maximalVelocityNorm_le_iff t K

theorem maximalGradientNorm_continuous : Continuous maximalGradientNorm :=
  lifespan.maximalGradientNorm_continuous

theorem maximalC1Norm_continuous : Continuous maximalC1Norm :=
  lifespan.maximalC1Norm_continuous

theorem pointwiseGradient_unbounded_near_maximal_time (τ K : ℝ) (hτ : τ < lifespan.duration) :
    ∃ (t : MaximalTime) (x : Space), τ < t ∧ K < ‖fderiv ℝ (maximalVelocity t) x‖ :=
  lifespan.maximalVelocity_gradient_unbounded_near_endpoint τ K hτ

/-- The gradient supremum has infinite upper limit at the actual maximal time. -/
theorem gradient_unbounded_near_maximal_time (τ K : ℝ) (hτ : τ < lifespan.duration) :
    ∃ t : MaximalTime, τ < t ∧ K < maximalGradientNorm t :=
  lifespan.maximalGradientNorm_unbounded_near_endpoint τ K hτ

/-- The same characterization for the sum of the actual velocity and gradient suprema. -/
theorem c1_unbounded_near_maximal_time (τ K : ℝ) (hτ : τ < lifespan.duration) :
    ∃ t : MaximalTime, τ < t ∧ K < maximalC1Norm t :=
  lifespan.maximalC1Norm_unbounded_near_endpoint τ K hτ

theorem initialDatum_c1_breakdown :
    0 < lifespan.duration ∧ lifespan.duration ≤ 1 ∧
      ¬ HasSmoothEulerSolution initialDatum.field lifespan.duration ∧
      ∀ τ : ℝ, τ < lifespan.duration → ∀ K : ℝ,
        ∃ t : MaximalTime, τ < t ∧ K < maximalC1Norm t :=
  ⟨lifespan.duration_pos,lifespan_le_one,initialDatum_no_endpoint,
    fun τ hτ K => c1_unbounded_near_maximal_time τ K hτ⟩

end EulerPacketInduction

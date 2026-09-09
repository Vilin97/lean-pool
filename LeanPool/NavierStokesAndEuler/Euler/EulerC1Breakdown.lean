/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerFiniteLifespan
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerMaximal
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerContinuation

@[expose] public section

/-! C¹ breakdown for the concrete compactly supported datum. The
infinite-limsup statement is expressed directly: after every time below
the maximal time, the actual gradient supremum exceeds every real bound.
The norms are bounded-continuous-function norms at individual times,
not totalized real L∞ seminorms of unverified measurable fields. -/

noncomputable section

namespace EulerOrdinarySobolev.FiniteLifespan

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanSobolevBoundedField

variable {A : SmoothL2Field Space} (L : FiniteLifespan A)

def maximalVelocityNorm (t : L.Time) : ℝ := ‖finiteField (L.maximalField t)‖

def maximalGradientNorm (t : L.Time) : ℝ := ‖finiteField (L.maximalField t).derivative‖

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

abbrev MaximalTime : Type := lifespan.Time

def maximalVelocity (t : MaximalTime) : Space → Space := lifespan.maximalVelocity t

def maximalPressure (t : MaximalTime) : Space → ℝ := lifespan.maximalPressure t

def maximalVelocityNorm (t : MaximalTime) : ℝ := lifespan.maximalVelocityNorm t

def maximalGradientNorm (t : MaximalTime) : ℝ := lifespan.maximalGradientNorm t

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

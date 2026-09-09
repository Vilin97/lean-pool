/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerClassicalClass
public import LeanPool.NavierStokesAndEuler.Euler.EulerC1Breakdown
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryMaximalVorticityIntegral
import LeanPool.NavierStokesAndEuler.Euler.EulerC1Limsup
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerBKM
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerContinuation
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerNontriviality

/-!
The final statement for the concrete packet construction. The initial
velocity is an ordinary compactly supported smooth field on Euclidean
three-space. Its maximal solution has a positive finite lifespan, a
divergent C¹ upper limit, and an infinite integral of the actual curl
supremum. All packet, scale, local existence, continuation, and logarithmic
estimate inputs have been constructed in the imported proofs.

`Evolution.sobolevSolutionClass` supplies one continuous strong time
derivative in every spatial Sobolev order for every shorter restriction. The norm
specification theorems below identify the quantities in the statement
with the pointwise suprema of the actual velocity, derivative, and curl.
-/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field

/-- Scalar-pressure Euler on the closed interval `[0,T]`, with the ordinary
all-order spatial and strong time regularity. No pressure-force path or
pressure norm is prescribed. The maximal solution itself is on `[0,T*)`. -/
def HasScalarEulerEvolution (A : SmoothL2Field Space) (T : ℝ) : Prop :=
  ∃ hT : 0 < T, ∃ u : Icc (0 : ℝ) T → SmoothL2Field Space,
    IsSmoothScalarEuler (hT := hT.le) u ∧ u ⟨0,le_rfl,hT.le⟩=A

theorem hasScalarEulerEvolution_iff (A : SmoothL2Field Space) (T : ℝ) :
    HasScalarEulerEvolution A T ↔ HasEulerEvolution A T := by
  constructor
  · rintro ⟨hT,u,hu,hinit⟩
    obtain ⟨U,hU⟩ := (exists_evolution_iff_scalar hT u).mpr hu
    exact ⟨hT,U,by rw [hU]; exact hinit⟩
  · rintro ⟨hT,U,hinit⟩
    exact ⟨hT,U.velocity,(exists_evolution_iff_scalar hT U.velocity).mp ⟨U,rfl⟩,hinit⟩

namespace FiniteLifespan

variable {A : SmoothL2Field Space} (L : FiniteLifespan A)

/-- The maximal duration is exactly the upper endpoint of the positive
closed intervals on which an ordinary smooth Euler evolution exists. -/
theorem hasEulerEvolution_iff (T : ℝ) :
    HasEulerEvolution A T ↔ 0 < T ∧ T < L.duration := by
  constructor
  · intro h
    refine ⟨h.choose,?_⟩
    by_contra hn
    rcases (le_of_not_gt hn).eq_or_lt with heq | hlt
    · rw [← heq] at h
      exact L.no_endpoint h
    · exact L.maximal T hlt h
  · rintro ⟨hT,hTL⟩
    exact L.shorter T hT hTL

theorem hasScalarEulerEvolution_iff (T : ℝ) :
    HasScalarEulerEvolution A T ↔ 0 < T ∧ T < L.duration :=
  (EulerOrdinarySobolev.hasScalarEulerEvolution_iff A T).trans (L.hasEulerEvolution_iff T)

end FiniteLifespan
end EulerOrdinarySobolev

namespace EulerPacketInduction

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanCutoffCurl
open scoped ContDiff ENNReal Topology

/-- Maximal vorticity norm, given by `lifespan.maximalVorticityNorm t`. -/
def maximalVorticityNorm (t : MaximalTime) : ℝ := lifespan.maximalVorticityNorm t

/-- Maximal vorticity density, given by `lifespan.maximalVorticityDensity r`. -/
def maximalVorticityDensity (r : ℝ) : ℝ := lifespan.maximalVorticityDensity r

/-- Maximal vorticity integral, given by `lifespan.maximalVorticityIntegral t`. -/
def maximalVorticityIntegral (t : MaximalTime) : ℝ := lifespan.maximalVorticityIntegral t

theorem maximalVorticityNorm_spec (t : MaximalTime) (K : ℝ) :
    maximalVorticityNorm t ≤ K ↔ ∀ x, ‖vectorCurl (maximalVelocity t) x‖ ≤ K :=
  lifespan.maximalVorticityNorm_le_iff t K

theorem maximalVorticityDensity_spec (t : MaximalTime) :
    maximalVorticityDensity t=maximalVorticityNorm t :=
  lifespan.maximalVorticityDensity_eq t

theorem maximalVorticityIntegral_spec (t : MaximalTime) :
    (∫ r in (0 : ℝ)..(t : ℝ), maximalVorticityDensity r)=maximalVorticityIntegral t :=
  lifespan.maximalVorticityDensity_integral_eq t

theorem initialDatum_nonzero : initialDatum.field ≠ 0 := lifespan.initial_nonzero

theorem initialDatum_existence_iff (T : ℝ) :
    HasSmoothEulerSolution initialDatum.field T ↔ 0 < T ∧ T < lifespan.duration :=
  (hasSmoothEulerSolution_iff initialDatum T).trans (lifespan.hasEulerEvolution_iff T)

theorem initialDatum_scalar_existence_iff (T : ℝ) :
    HasScalarEulerEvolution initialDatum T ↔ 0 < T ∧ T < lifespan.duration :=
  lifespan.hasScalarEulerEvolution_iff T

theorem maximalVorticityIntegral_tendsto :
    Tendsto maximalVorticityIntegral
      (Filter.comap (fun t : MaximalTime => (t : ℝ)) (𝓝[<] lifespan.duration)) atTop := by
  change Tendsto lifespan.maximalVorticityIntegral lifespan.endpointFilter atTop
  rw [lifespan.endpointFilter_eq_atTop]
  exact lifespan.vorticityIntegral_tendsto_atTop

theorem maximalVorticity_integral_infinite :
    (∫⁻ r in Ico (0 : ℝ) lifespan.duration, ENNReal.ofReal (maximalVorticityDensity r))=⊤ :=
  lifespan.vorticity_lintegral_eq_top

/-- The two breakdown conclusions for the actual constructed datum and
the actual maximal smooth solution. No unproved estimate is a premise. -/
theorem initialDatum_singularity :
    ContDiff ℝ ∞ initialDatum.field ∧ HasCompactSupport initialDatum.field ∧
      initialDatum.field ≠ 0 ∧ (∀ x, divergence initialDatum.field x=0) ∧
      0 < lifespan.duration ∧ lifespan.duration ≤ 1 ∧
      (∀ T : ℝ, HasSmoothEulerSolution initialDatum.field T ↔
        0 < T ∧ T < lifespan.duration) ∧
      Filter.limsup (fun t : MaximalTime => ENNReal.ofReal (maximalC1Norm t))
        (Filter.comap (fun t : MaximalTime => (t : ℝ)) (𝓝[<] lifespan.duration))=⊤ ∧
      (∫⁻ r in Ico (0 : ℝ) lifespan.duration,
        ENNReal.ofReal (maximalVorticityDensity r))=⊤ :=
  ⟨initialDatum.smooth,initialDatum_compact,initialDatum_nonzero,initialDatum_divergence,
    lifespan.duration_pos,lifespan_le_one,initialDatum_existence_iff,
    maximalC1Norm_limsup,maximalVorticity_integral_infinite⟩

/-- An existential form of the manuscript's claim. Every restriction of
the one maximal field is an actual Euler evolution. Its time and space
regularity, scalar pressure, and norm meanings are proved in the imported
ordinary-Euler interfaces, rather than assumed as construction inputs. -/
theorem exists_compact_smooth_euler_singularity :
    ∃ (A : SmoothL2Field Space) (L : FiniteLifespan A),
      ContDiff ℝ ∞ A.field ∧ HasCompactSupport A.field ∧ A.field ≠ 0 ∧
      (∀ x, divergence A.field x=0) ∧ 0 < L.duration ∧ L.duration ≤ 1 ∧
      (∀ T : ℝ, HasScalarEulerEvolution A T ↔ 0 < T ∧ T < L.duration) ∧
      L.maximalVelocity L.initialTime=A.field ∧
      (∀ (S : ℝ) (hS : 0 < S) (hSL : S < L.duration),
        ∃ U : Evolution S hS.le,
          U.velocity=(fun t => L.maximalField (L.shorterTime S hSL t)) ∧
          U.pressureForce=(fun t => L.maximalPressureField (L.shorterTime S hSL t)) ∧
          U.velocity ⟨0,le_rfl,hS.le⟩=A) ∧
      Filter.limsup (fun t : L.Time => ENNReal.ofReal (L.maximalC1Norm t))
        (Filter.comap (fun t : L.Time => (t : ℝ)) (𝓝[<] L.duration))=⊤ ∧
      (∫⁻ r in Ico (0 : ℝ) L.duration, ENNReal.ofReal (L.maximalVorticityDensity r))=⊤ :=
  ⟨initialDatum,lifespan,initialDatum.smooth,initialDatum_compact,initialDatum_nonzero,
    initialDatum_divergence,lifespan.duration_pos,lifespan_le_one,
    lifespan.hasScalarEulerEvolution_iff,lifespan.maximalVelocity_initial,
    lifespan.maximal_restriction_is_evolution,lifespan.maximalC1Norm_limsup,
    lifespan.vorticity_lintegral_eq_top⟩

end EulerPacketInduction

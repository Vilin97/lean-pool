/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ProductWeakLimitPassage
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.TimeDependentFourierTest

/-!
# Weak equation for time-dependent finite Fourier tests

The separated Fourier-mode identities sum to the weak equation for the spatial Fourier cutoff of
an arbitrary smooth periodic spacetime test.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped ENNReal RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance timeWeakEquationMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance timeWeakEquationMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance timeWeakEquationProbabilityUnitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance timeWeakEquationProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

/-- The coefficient vector selecting one real Fourier basis mode. -/
def realFourierUnitCoefficient (N : ℕ)
    (j : Fin (RealFourierDimension N)) : Coefficients (RealFourierDimension N) :=
  WithLp.toLp 2 (Pi.single j (1 : ℝ))

theorem TimeDependentWeakEquation.realFourierScalarMap_unit (N : ℕ)
    (j : Fin (RealFourierDimension N)) :
  realFourierScalarMap N (realFourierUnitCoefficient N j) = realFourierModeL2 N j := by
  rw [realFourierScalarMap_apply]
  simp [realFourierUnitCoefficient]

theorem TimeDependentWeakEquation.realFourierGradientMap_unit (N : ℕ)
    (j : Fin (RealFourierDimension N)) :
  realFourierGradientMap N (realFourierUnitCoefficient N j) = realFourierModeGradL2 N j := by
  rw [realFourierGradientMap_apply]
  simp [realFourierUnitCoefficient]

/-- Expansion of the coefficient vector selecting one real Fourier mode. -/
theorem modeExpansion_unit (N : ℕ)
    (j : Fin (RealFourierDimension N)) (x : Torus) :
  modeExpansion (RealFourierDimension N) (realFourierModeFin N)
      (realFourierUnitCoefficient N j) x = realFourierModeFin N j x := by
  simp [modeExpansion, realFourierUnitCoefficient]

/-- The synchronized product limits satisfy the weak equation for every finite spatial Fourier
cutoff of a smooth periodic spacetime test. -/
theorem FrozenDriftProblem.synchronized_limit_spacetimeFourierCutoff_identity
    (P : FrozenDriftProblem) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (Uprod : ScalarProductTimeL2) (Gprod : GradientProductTimeL2)
    (hUweak : ∀ v, Tendsto (fun n => inner ℝ (P.scalarProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Uprod v)))
    (hGweak : ∀ v, Tendsto (fun n => inner ℝ (P.gradientProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Gprod v)))
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (_hperiodic : ∀ t, AVenhance.IsZ2Periodic (φ t))
    (hterminal : ∀ t, 1 ≤ t → ∀ x, φ t x = 0)
    (N : ℕ) :
    -(∑ j : Fin (RealFourierDimension N),
        inner ℝ Uprod
          (scalarProductTestLp
            (deriv (spacetimeRealFourierCoefficient φ N j))
            (realFourierModeL2 N j)
            (continuous_time_memLp_top
              ((spacetimeRealFourierCoefficient_contDiff_one hφ N j).continuous_deriv_one)))) +
      (∑ j : Fin (RealFourierDimension N),
        inner ℝ Gprod
          (P.weightedDriftProductTestLp
            (spacetimeRealFourierCoefficient φ N j) N
            (realFourierUnitCoefficient N j)
            (continuous_time_memLp_top
              (spacetimeRealFourierCoefficient_contDiff_one hφ N j).continuous))) +
      P.κ * (∑ j : Fin (RealFourierDimension N),
        inner ℝ Gprod
          (gradientProductTestLp
            (spacetimeRealFourierCoefficient φ N j)
            (realFourierModeGradL2 N j)
            (continuous_time_memLp_top
              (spacetimeRealFourierCoefficient_contDiff_one hφ N j).continuous))) =
      ∑ j : Fin (RealFourierDimension N),
        spacetimeRealFourierCoefficient φ N j 0 *
          inner ℝ P.initialTorusL2 (realFourierModeL2 N j) := by
  classical
  let η : Fin (RealFourierDimension N) → ℝ → ℝ :=
    fun j => spacetimeRealFourierCoefficient φ N j
  have hη (j : Fin (RealFourierDimension N)) : ContDiff ℝ 1 (η j) :=
    spacetimeRealFourierCoefficient_contDiff_one hφ N j
  have hηmem (j : Fin (RealFourierDimension N)) :
      MemLp (η j) ⊤ GalerkinTimeMeasure :=
    continuous_time_memLp_top (hη j).continuous
  have hηderivmem (j : Fin (RealFourierDimension N)) :
      MemLp (deriv (η j)) ⊤ GalerkinTimeMeasure :=
    continuous_time_memLp_top (hη j).continuous_deriv_one
  have hterminal' : ∀ x, φ 1 x = 0 := fun x => hterminal 1 (by norm_num) x
  have hterm (j : Fin (RealFourierDimension N)) :
      -inner ℝ Uprod
          (scalarProductTestLp (deriv (η j)) (realFourierModeL2 N j) (hηderivmem j)) +
        inner ℝ Gprod
          (P.weightedDriftProductTestLp (η j) N (realFourierUnitCoefficient N j)
            (hηmem j)) +
        P.κ * inner ℝ Gprod
          (gradientProductTestLp (η j) (realFourierModeGradL2 N j) (hηmem j)) =
        η j 0 * inner ℝ P.initialTorusL2 (realFourierModeL2 N j) := by
    have hidentity := P.synchronized_limit_fourier_test_weak_identity N
      (realFourierUnitCoefficient N j) (η j) (hη j)
      (spacetimeRealFourierCoefficient_terminal hterminal' N j)
      (hηmem j) (hηderivmem j) σ hσ Uprod Gprod hUweak hGweak
    rw [TimeDependentWeakEquation.realFourierScalarMap_unit,
        TimeDependentWeakEquation.realFourierGradientMap_unit] at hidentity
    exact hidentity
  have hsum :
      (∑ j : Fin (RealFourierDimension N),
        (-inner ℝ Uprod (scalarProductTestLp (deriv (η j))
            (realFourierModeL2 N j) (hηderivmem j)) +
          inner ℝ Gprod (P.weightedDriftProductTestLp (η j) N
            (realFourierUnitCoefficient N j) (hηmem j)) +
          P.κ * inner ℝ Gprod (gradientProductTestLp (η j)
            (realFourierModeGradL2 N j) (hηmem j)))) =
      ∑ j : Fin (RealFourierDimension N),
        η j 0 * inner ℝ P.initialTorusL2 (realFourierModeL2 N j) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hterm j
  simpa [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum, η,
    hηmem, hηderivmem] using hsum

end AVenhance.Infra.Parabolic.FourierGalerkin

end

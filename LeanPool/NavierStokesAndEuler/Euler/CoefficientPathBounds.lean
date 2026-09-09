/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CoefficientPathSmooth
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.H6Pressure

/-!
The bounds stored in the actual recursive coefficient jet are controlled
by the true word derivatives of its bounded-field translation orbit. A
single enlargement of the coefficient radius gives fixed-base Sobolev
bounds, independent of the jet truncation.
-/

@[expose] public section


noncomputable section

namespace EulerCoefficientPath

open Set Finset ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMeanCoefficients EulerMetricTransport EulerTransportDerivatives
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerJetProductBounds
  EulerParameterWordGevrey EulerGevrey
open scoped ContDiff BoundedContinuousFunction

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Coefficient directions, given by `(standardDirection i).1`. -/
def coefficientDirections (i : Fin 4) : Space := (standardDirection i).1

theorem coefficientDirections_norm (i : Fin 4) : ‖coefficientDirections i‖ ≤ 1 := by
  cases i using Fin.cases <;> simp [coefficientDirections]

omit [CompactSpace K] in
theorem translateCoefficientPath_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : C(K, Space →ᵇ V)) : translateCoefficientPath A 0 = A := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro x
  change A t (x+0) = A t x
  rw [add_zero]

/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instCoefficientPathBounds1 : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instCoefficientPathBounds2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCoefficientPathBounds3 : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCoefficientPathBounds4 : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance

variable (P : ℝ) [Fact (0 < P)]
  (A : C(K, Space →ᵇ Space →L[ℝ] Space))
  (hA : ContDiff ℝ ∞ (translateCoefficientPath A))

theorem coefficientJet_boundLevel_le_words (s n : ℕ) (t : K) :
    boundLevel P (coefficientJet P A hA s t) n ≤
      wordSum coefficientDirections (translateCoefficientPath A) n 0 := by
  induction s generalizing A n with
  | zero =>
    cases n with
    | zero =>
      rw [wordSum_zero,translateCoefficientPath_zero]
      simp only [coefficientJet,boundLevel,smoothCoefficient]
      exact A.norm_coe_le_norm t
    | succ n =>
      simp only [coefficientJet,boundLevel]
      exact wordSum_nonneg _ _ _ _
  | succ s ih =>
    cases n with
    | zero =>
      rw [wordSum_zero,translateCoefficientPath_zero]
      simp only [coefficientJet,boundLevel,smoothCoefficient]
      exact A.norm_coe_le_norm t
    | succ n =>
      rw [wordSum_succ coefficientDirections (translateCoefficientPath A) hA n 0]
      rw [coefficientJet, boundLevel.eq_def]
      apply sum_le_sum
      intro i _
      have hh := ih (orbitDerivativePath A (coefficientDirections i))
        (orbitDerivativePath_orbit A hA (coefficientDirections i)) n
      have he : translateCoefficientPath (orbitDerivativePath A (coefficientDirections i)) =
          directional coefficientDirections (translateCoefficientPath A) i :=
        funext (orbitDerivativePath_translation A hA (coefficientDirections i))
      rw [he] at hh
      exact hh

theorem coefficientJet_boundLevel_le_tensor (s n : ℕ) (t : K) :
    boundLevel P (coefficientJet P A hA s t) n ≤
      (4 : ℝ)^n*‖iteratedFDeriv ℝ n (translateCoefficientPath A) 0‖ := by
  have hh := wordSum_le coefficientDirections coefficientDirections_norm (translateCoefficientPath
      A) n 0
  norm_num only [Fintype.card_fin] at hh
  exact (coefficientJet_boundLevel_le_words P A hA s n t).trans hh

theorem coefficientJet_block_le_words (s q n : ℕ) (t : K) :
    EulerH6Pressure.coefficientBlock P (coefficientJet P A hA s t) q n ≤
      EulerParameterWordGevrey.coefficientBlock coefficientDirections q (translateCoefficientPath
          A) n 0 := by
  change (2 : ℝ)^q*(∑ r ∈ range (q+1),boundLevel P (coefficientJet P A hA s t) (n+r)) ≤
    (2 : ℝ)^q*block coefficientDirections q (translateCoefficientPath A) n 0
  rw [block_eq_sum_levels coefficientDirections q (translateCoefficientPath A) hA n 0]
  exact mul_le_mul_of_nonneg_left
    (sum_le_sum (fun r _ => coefficientJet_boundLevel_le_words P A hA s (n+r) t)) (by positivity)

theorem coefficientJet_block_bound (s q : ℕ) (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n (translateCoefficientPath A) x‖ ≤ C * majorant Rc 0 n)
    (n : ℕ) (t : K) :
    EulerH6Pressure.coefficientBlock P (coefficientJet P A hA s t) q n ≤
      sobolevCoefficientAmplitude (Fin 4) q Rc C * majorant (sobolevCoefficientRadius (Fin 4) Rc) 0
          n :=
  (coefficientJet_block_le_words P A hA s q n t).trans
    (coefficientBlock_of_tensor_bound coefficientDirections coefficientDirections_norm q
      (translateCoefficientPath A) hA Rc C hRc hC hb n 0)

end EulerCoefficientPath

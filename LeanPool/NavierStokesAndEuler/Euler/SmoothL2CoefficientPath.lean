/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanSobolevBoundedField
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothJetField
public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientPathMap
public import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

@[expose] public section

/-!
# Actual bounded smooth coefficient paths from smooth L² jets

Finite-dimensional Sobolev evaluation supplies the uniform norm at every
spatial order. The resulting coefficient path contains the original field
and its actual derivative tensors; no bounded-derivative hypothesis is added.
-/

noncomputable section

namespace EulerMeanSobolevBoundedField

open MeasureTheory EulerSmoothLimit EulerMeanCoefficients EulerLpTranslation
  EulerLpTranslation.SmoothL2Field
open scoped BoundedContinuousFunction ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

local instance tensorFiniteDimensional (n : ℕ) : FiniteDimensional ℝ (Space [×n]→L[ℝ] V) := by
  let J : (Space [×n]→L[ℝ] V) →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin n => Space) V :=
    ContinuousMultilinearMap.toMultilinearMapLinear
  exact FiniteDimensional.of_injective J ContinuousMultilinearMap.toMultilinearMap_injective

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- The actual raw L² family as a uniformly smooth bounded coefficient path. -/
def coefficientPath (A : K → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) : SmoothCoefficientPath K V where
  field := ⟨fun t => finiteField (A t), continuous_finiteField A hA⟩
  smooth t := by
    change ContDiff ℝ ∞ (fun x => finiteField (A t) x)
    simpa only [finiteField_apply] using (A t).smooth
  jet n := ⟨fun t => finiteField (jetField n (A t)),
    continuous_finiteField (fun t => jetField n (A t)) (continuous_jetField_jet A hA n)⟩
  jet_eq n t x := by
    change finiteField (jetField n (A t)) x =
      iteratedFDeriv ℝ n (fun y => finiteField (A t) y) x
    simp only [finiteField_apply, jetField_field]

@[simp] theorem coefficientPath_apply (A : K → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (t : K) (x : Space) :
    (coefficientPath A hA).field t x = (A t).field x := finiteField_apply _ _

end EulerMeanSobolevBoundedField

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SolutionDefinitions
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerVorticity

/-! The extended spatial suprema in the independent challenge agree with the
ordinary development's bounded-function norms on every smooth Sobolev slice. -/

@[expose] public section


noncomputable section

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSobolevBoundedField
  EulerMeanBoundary EulerMeanCutoffCurl
open scoped ENNReal Topology ContDiff BoundedContinuousFunction

namespace Euler.ComparatorBridge

theorem vorticity_eq_vectorCurl (u : Space → Space) (hu : ContDiff ℝ ∞ u) :
    Euler.vorticity u = vectorCurl u := by
  funext x
  exact (vectorCurl_eq_matrix u x (hu.differentiable (by simp) x)).symm

theorem iSup_ofReal_norm_boundedContinuousFunction
    {X V : Type*} [TopologicalSpace X] [NormedAddCommGroup V]
    (f : X →ᵇ V) :
    (⨆ x, ENNReal.ofReal ‖f x‖) = ENNReal.ofReal ‖f‖ := by
  simpa only [ofReal_norm] using f.enorm_eq_iSup_enorm.symm

theorem velocityC1Norm_eq (A : SmoothL2Field Space) :
    Euler.velocityC1Norm A.field =
      ENNReal.ofReal (‖finiteField A‖ + ‖finiteField A.derivative‖) := by
  unfold Euler.velocityC1Norm
  rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  congr 1
  · simpa only [finiteField_apply] using
      iSup_ofReal_norm_boundedContinuousFunction (finiteField A)
  · simpa only [finiteField_apply, SmoothL2Field.derivative] using
      iSup_ofReal_norm_boundedContinuousFunction (finiteField A.derivative)

theorem vorticityNorm_eq (A : SmoothL2Field Space) :
    Euler.vorticityNorm A.field = ENNReal.ofReal (EulerOrdinarySobolev.vorticityNorm A) := by
  unfold Euler.vorticityNorm EulerOrdinarySobolev.vorticityNorm
  rw [vorticity_eq_vectorCurl A.field A.smooth]
  simpa only [finiteField_apply, EulerOrdinarySobolev.vorticityField_apply] using
    iSup_ofReal_norm_boundedContinuousFunction
      (finiteField (EulerOrdinarySobolev.vorticityField A))

end Euler.ComparatorBridge

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseForwardInverse
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import LeanPool.NavierStokesAndEuler.Euler.ContinuousGramPath
import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathCalculus
import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelParameter
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Genuine parameter regularity of the transverse forward inverse

The source coefficient is formed from the actual Gram inverse and frame
coefficients. These constructions and the forced forward solve are smooth
in the uniform time norm, without assuming parameter regularity of the
homogeneous evolution supplied by (H3).
-/

@[expose] public section


noncomputable section


namespace EulerTransverseForwardRegularity

open Set ContinuousLinearMap EulerContinuousTimeIntegral EulerContinuousPathCalculus
  EulerContinuousPathComposition EulerContinuousGramPath EulerTransverseGramPath
  EulerTransverseForwardInverse EulerLinearDuhamel
open scoped ContDiff

variable {P V E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (hT : 0 ≤ T) (Q Q₁ : P → C(Icc (0 : ℝ) T, V →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ x t v, c * ‖v‖ ^ 2 ≤ ‖Q x t v‖ ^ 2)

/-- The actual canonical frame left inverse varies smoothly in parameters. -/
theorem frameLeftInversePath_contDiff {n : ℕ∞ω} (hQr : ContDiff ℝ n Q) :
    ContDiff ℝ n (fun x => frameLeftInversePath T (Q x) c hc (hQ x)) := by
  exact contDiff_compose (fun x => gramInversePath T (Q x) c hc (hQ x))
    (fun x => adjointMap (Q x)) (gramInversePath_contDiff T c hc Q hQ hQr)
    (contDiff_adjoint Q hQr)

/-- The literal source generator is smoothly parameterized. -/
theorem generator_contDiff {n : ℕ∞ω} (hQr : ContDiff ℝ n Q) (hQ₁r : ContDiff ℝ n Q₁) :
    ContDiff ℝ n (fun x => generator T (Q x) (Q₁ x) c hc (hQ x)) := by
  have hr := (contDiff_compose (fun x => frameLeftInversePath T (Q x) c hc (hQ x)) Q₁
    (frameLeftInversePath_contDiff T Q c hc hQ hQr) hQ₁r).const_smul (-2 : ℝ)
  convert hr using 1 <;> rfl

/-- Applying the actual projected forcing map preserves smooth parameter dependence. -/
theorem forcing_contDiff (f : P → C(Icc (0 : ℝ) T, E)) {n : ℕ∞ω}
    (hQr : ContDiff ℝ n Q) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => forcingOperator T (Q x) c hc (hQ x) (f x)) :=
  contDiff_apply (fun x => frameLeftInversePath T (Q x) c hc (hQ x)) f
    (frameLeftInversePath_contDiff T Q c hc hQ hQr) hf

variable (U : ∀ x, Evolution T hT (generator T (Q x) (Q₁ x) c hc (hQ x)))
  (f : P → C(Icc (0 : ℝ) T, E)) (a₀ : P → V)

/-- The actually constructed coordinates are smooth in external parameters. -/
theorem coordinates_contDiff {n : ℕ∞ω} (hQr : ContDiff ℝ n Q) (hQ₁r : ContDiff ℝ n Q₁)
    (hf : ContDiff ℝ n f) (ha₀ : ContDiff ℝ n a₀) :
    ContDiff ℝ n (fun x => coordinates T hT (Q x) (Q₁ x) c hc (hQ x) (U x) (f x) (a₀ x)) :=
  solution_contDiff T hT (fun x => generator T (Q x) (Q₁ x) c hc (hQ x)) U
    (fun x => forcingOperator T (Q x) c hc (hQ x) (f x)) a₀
    (generator_contDiff T Q Q₁ c hc hQ hQr hQ₁r)
    (forcing_contDiff T Q c hc hQ f hQr hf) ha₀

/-- The actual physical velocity inherits uniform-time parameter smoothness. -/
theorem velocity_contDiff {n : ℕ∞ω} (hQr : ContDiff ℝ n Q) (hQ₁r : ContDiff ℝ n Q₁)
    (hf : ContDiff ℝ n f) (ha₀ : ContDiff ℝ n a₀) :
    ContDiff ℝ n (fun x => velocity T hT (Q x) (Q₁ x) c hc (hQ x) (U x) (f x) (a₀ x)) :=
  contDiff_apply Q _ hQr (coordinates_contDiff T hT Q Q₁ c hc hQ U f a₀ hQr hQ₁r hf ha₀)

/-- The actual coordinate derivative is smooth in external parameters too. -/
theorem coordinateDerivative_contDiff {n : ℕ∞ω} (hQr : ContDiff ℝ n Q) (hQ₁r : ContDiff ℝ n Q₁)
    (hf : ContDiff ℝ n f) (ha₀ : ContDiff ℝ n a₀) :
    ContDiff ℝ n (fun x => coordinateDerivative T hT (Q x) (Q₁ x) c hc (hQ x) (U x) (f x) (a₀ x)) :=
  (contDiff_apply _ _ (generator_contDiff T Q Q₁ c hc hQ hQr hQ₁r)
    (coordinates_contDiff T hT Q Q₁ c hc hQ U f a₀ hQr hQ₁r hf ha₀)).add
    (forcing_contDiff T Q c hc hQ f hQr hf)

/-- The actual physical time derivative is smooth in the same uniform-time parameter norm. -/
theorem velocityDerivative_contDiff {n : ℕ∞ω} (hQr : ContDiff ℝ n Q) (hQ₁r : ContDiff ℝ n Q₁)
    (hf : ContDiff ℝ n f) (ha₀ : ContDiff ℝ n a₀) :
    ContDiff ℝ n (fun x => velocityDerivative T hT (Q x) (Q₁ x) c hc (hQ x) (U x) (f x) (a₀ x)) :=
  (contDiff_apply Q₁ _ hQ₁r
    (coordinates_contDiff T hT Q Q₁ c hc hQ U f a₀ hQr hQ₁r hf ha₀)).add
    (contDiff_apply Q _ hQr
      (coordinateDerivative_contDiff T hT Q Q₁ c hc hQ U f a₀ hQr hQ₁r hf ha₀))

end EulerTransverseForwardRegularity

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanFixedTranslation
import LeanPool.NavierStokesAndEuler.Euler.HilbertCoerciveParameter
import Mathlib.Analysis.Calculus.ContDiff.Operations
public import LeanPool.NavierStokesAndEuler.Euler.BoundedCoefficientSmooth
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Related estimates used together by the same construction modules. -/

section

/-!
# The actual mean inverse on translated coefficient families

The inverse is built from the translated fixed form with the original proved
coercivity constant. Its solution for translated forcing is exactly the
spatial translation of the original solution. Thus regularity of known
coefficient families yields genuine spatial regularity of the solved field.
-/

@[expose] public section

noncomputable section

namespace EulerMeanTranslatedInverse

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerTimeLp EulerMeanTimeTranslation EulerMeanFixedSpaceInverse
  EulerMeanFixedTranslation EulerCoerciveProjection EulerHilbertCoerciveParameter
  EulerTransverseGramInverse
open scoped ContDiff

-- Reuse the nested Hilbert-space instances in the inverse and adjoint identities.
/-- Cache the standard `NormedAddCommGroup solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanTranslatedInverse1 : NormedAddCommGroup solenoidalSpace := inferInstance
/-- Cache the standard `InnerProductSpace ℝ solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanTranslatedInverse2 : InnerProductSpace ℝ solenoidalSpace := inferInstance
/-- Cache the standard `NormedAddCommGroup (TimeLp T L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanTranslatedInverse3 (T : ℝ) : NormedAddCommGroup (TimeLp T L2) :=
    inferInstance
/-- Cache the standard `InnerProductSpace ℝ (TimeLp T L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanTranslatedInverse4 (T : ℝ) : InnerProductSpace ℝ (TimeLp T L2) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (TimeLp T solenoidalSpace)` instance to shorten
typeclass synthesis. -/
local instance instMeanTranslatedInverse5 (T : ℝ) : NormedAddCommGroup (TimeLp T solenoidalSpace)
    := inferInstance
/-- Cache the standard `InnerProductSpace ℝ (TimeLp T solenoidalSpace)` instance to shorten
typeclass synthesis. -/
local instance instMeanTranslatedInverse6 (T : ℝ) : InnerProductSpace ℝ (TimeLp T solenoidalSpace)
    := inferInstance

variable (T : ℝ) (hT : 0 ≤ T)
  (F F₁ H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (M0 A : L2 →L[ℝ] L2) (L c : ℝ)
  (hc : 0 < c)
  (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪fixedMeanOperator T hT F F₁ H M0 A L v, v⟫_ℝ)

/-- The genuine inverse of the translated fixed mean operator. -/
def translatedMeanInverse (a : Space) : TimeLp T solenoidalSpace →L[ℝ] TimeLp T solenoidalSpace :=
  coerciveInverse (translatedMeanOperator T hT a F F₁ H M0 A L) c hc
    (translatedMeanOperator_coercive T hT a F F₁ H M0 A L c hcoercive)

/-- The actual translated forcing-to-coordinate-derivative solver. -/
def translatedMeanSolver (a : Space) : TimeLp T L2 →L[ℝ] TimeLp T solenoidalSpace :=
  (translatedMeanInverse T hT F F₁ H M0 A L c hc hcoercive a).comp
    (-(translatedMeanPrimitive T hT a F F₁).adjoint)

/-- The coercive inverse commutes with simultaneous translation of all coefficients. -/
theorem translatedMeanInverse_covariance (a : Space) (g : TimeLp T solenoidalSpace) :
    translatedMeanInverse T hT F F₁ H M0 A L c hc hcoercive a (timeSolenoidalTranslation T a g) =
      timeSolenoidalTranslation T a (coerciveInverse (fixedMeanOperator T hT F F₁ H M0 A L) c hc
          hcoercive g) := by
  apply (coerciveEquiv (translatedMeanOperator T hT a F F₁ H M0 A L) c hc
    (translatedMeanOperator_coercive T hT a F F₁ H M0 A L c hcoercive)).injective
  simp only [coerciveEquiv_apply]
  have hl := operator_inverse_apply (translatedMeanOperator T hT a F F₁ H M0 A L) c hc
    (translatedMeanOperator_coercive T hT a F F₁ H M0 A L c hcoercive) (timeSolenoidalTranslation T
        a g)
  have hr := (fixedMeanOperator_translate T hT a F F₁ H M0 A L
    (coerciveInverse (fixedMeanOperator T hT F F₁ H M0 A L) c hc hcoercive g)).trans
    (congrArg (timeSolenoidalTranslation T a)
      (operator_inverse_apply (fixedMeanOperator T hT F F₁ H M0 A L) c hc hcoercive g))
  exact hl.trans hr.symm

/-- The translated actual solve is the spatial orbit of the original solve. -/
theorem translatedMeanSolver_covariance (a : Space) (f : TimeLp T L2) :
    translatedMeanSolver T hT F F₁ H M0 A L c hc hcoercive a (timeTranslation T a f) =
      timeSolenoidalTranslation T a
        (coerciveInverse (fixedMeanOperator T hT F F₁ H M0 A L) c hc hcoercive
          (-(fixedMeanPrimitive T hT F F₁).adjoint f)) := by
  have hforce := (congrArg (fun z : TimeLp T solenoidalSpace => -z)
    (fixedMeanPrimitive_adjoint_translate T hT a F F₁ f)).trans
      ((timeSolenoidalTranslation T a).map_neg ((fixedMeanPrimitive T hT F F₁).adjoint f)).symm
  exact (congrArg (translatedMeanInverse T hT F F₁ H M0 A L c hc hcoercive a) hforce).trans
    (translatedMeanInverse_covariance T hT F F₁ H M0 A L c hc hcoercive a
      (-(fixedMeanPrimitive T hT F F₁).adjoint f))

/-- Uniform coercivity gives a uniform inverse norm for the actual translated family. -/
theorem translatedMeanInverse_norm (a : Space) :
    ‖translatedMeanInverse T hT F F₁ H M0 A L c hc hcoercive a‖ ≤ c⁻¹ :=
  coerciveInverse_norm_le (translatedMeanOperator T hT a F F₁ H M0 A L) c hc
    (translatedMeanOperator_coercive T hT a F F₁ H M0 A L c hcoercive)

/-- Known coefficient and forcing smoothness gives actual spatial translation
smoothness of the field solved by the genuine mean inverse. -/
theorem solution_translation_contDiff (f : TimeLp T L2) {n : ℕ∞ω}
    (hO : ContDiff ℝ n (fun a : Space => translatedMeanOperator T hT a F F₁ H M0 A L))
    (hJ : ContDiff ℝ n (fun a : Space => translatedMeanPrimitive T hT a F F₁))
    (hf : ContDiff ℝ n (fun a : Space => timeTranslation T a f)) :
    ContDiff ℝ n (fun a : Space => timeSolenoidalTranslation T a
      (coerciveInverse (fixedMeanOperator T hT F F₁ H M0 A L) c hc hcoercive
        (-(fixedMeanPrimitive T hT F F₁).adjoint f))) := by
  have hAdj : ContDiff ℝ n (fun a : Space => (translatedMeanPrimitive T hT a F F₁).adjoint) :=
    (realAdjoint (U := TimeLp T solenoidalSpace) (E := TimeLp T L2)).contDiff.comp hJ
  have hforce : ContDiff ℝ n (fun a : Space =>
      -(translatedMeanPrimitive T hT a F F₁).adjoint (timeTranslation T a f)) :=
    (hAdj.clm_apply hf).neg
  have hsol := contDiff_coerciveSolution_variable
    (fun a : Space => translatedMeanOperator T hT a F F₁ H M0 A L) (fun _ => c) (fun _ => hc)
    (fun a => translatedMeanOperator_coercive T hT a F F₁ H M0 A L c hcoercive)
    (fun a : Space => -(translatedMeanPrimitive T hT a F F₁).adjoint (timeTranslation T a f)) hO
        hforce
  have heq : (fun a : Space => translatedMeanSolver T hT F F₁ H M0 A L c hc hcoercive a
      (timeTranslation T a f)) =
      (fun a : Space => timeSolenoidalTranslation T a
        (coerciveInverse (fixedMeanOperator T hT F F₁ H M0 A L) c hc hcoercive
          (-(fixedMeanPrimitive T hT F F₁).adjoint f))) :=
    funext (fun a => translatedMeanSolver_covariance T hT F F₁ H M0 A L c hc hcoercive a f)
  exact Eq.mp (congrArg (fun g : Space → TimeLp T solenoidalSpace => ContDiff ℝ n g) heq) hsol

end EulerMeanTranslatedInverse

end
end

end

section

/-! Actual derivatives and factorial bounds for the translated multiplication operators. -/

@[expose] public section

noncomputable section

namespace EulerMeanCoefficients

open EulerSmoothLimit MeasureTheory InnerProductSpace
open scoped ContDiff BoundedContinuousFunction

section BoundedFields

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Evaluating a parameter derivative gives the ordinary spatial derivative at the translated point.
-/
theorem BoundedSmoothField.iteratedFDeriv_translation_apply (A : BoundedSmoothField V)
    (n : ℕ) (a x : Space) (v : Fin n → Space) :
    (iteratedFDeriv ℝ n (translated A.field) a v) x =
      iteratedFDeriv ℝ n (A.field : Space → V) (x+a) v := by
  let ev : (Space →ᵇ V) →L[ℝ] V := BoundedContinuousFunction.evalCLM ℝ x
  have he := ContinuousLinearMap.iteratedFDeriv_comp_left (𝕜 := ℝ)
    (E := Space) (F := Space →ᵇ V) (G := V) ev
    (A.translation_contDiff.contDiffAt (x := a)) (i := n) (by simp)
  have hv := congrArg (fun L : Space [×n]→L[ℝ] V => L v) he
  change iteratedFDeriv ℝ n (fun b => A.field (x+b)) a v =
    (iteratedFDeriv ℝ n (translated A.field) a v) x at hv
  rw [iteratedFDeriv_comp_add_left] at hv
  exact hv.symm

/-- Passing from pointwise spatial bounds to parameter derivatives in sup norm costs no constant. -/
theorem BoundedSmoothField.norm_iteratedFDeriv_translation_le (A : BoundedSmoothField V)
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖iteratedFDeriv ℝ n (A.field : Space → V) x‖ ≤ C) (a : Space) :
    ‖iteratedFDeriv ℝ n (translated A.field) a‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro v
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hC (by positivity))).2
  intro x
  rw [A.iteratedFDeriv_translation_apply]
  exact ((iteratedFDeriv ℝ n (A.field : Space → V) (x+a)).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hbound (x+a)) (by positivity))

end BoundedFields

/-- Cache the standard `NormedAddCommGroup Field` instance to shorten typeclass synthesis. -/
local instance instBoundedCoefficientJets1 : NormedAddCommGroup Field := inferInstance
/-- Cache the standard `NormedSpace ℝ Field` instance to shorten typeclass synthesis. -/
local instance instBoundedCoefficientJets2 : NormedSpace ℝ Field := inferInstance
/-- Cache the standard `NormedAddCommGroup (EulerMeanSolenoidal.L2 →L[ℝ]
EulerMeanSolenoidal.L2)` instance to shorten typeclass synthesis. -/
local instance instBoundedCoefficientJets3 : NormedAddCommGroup (EulerMeanSolenoidal.L2 →L[ℝ]
    EulerMeanSolenoidal.L2)
    := inferInstance
/-- Cache the standard `NormedSpace ℝ (EulerMeanSolenoidal.L2 →L[ℝ] EulerMeanSolenoidal.L2)`
instance to shorten typeclass synthesis. -/
local instance instBoundedCoefficientJets4 : NormedSpace ℝ (EulerMeanSolenoidal.L2 →L[ℝ]
    EulerMeanSolenoidal.L2) :=
    inferInstance

theorem multiplierMap_norm_le_one : ‖multiplierMap‖ ≤ 1 :=
  multiplierMap.opNorm_le_bound zero_le_one (fun A => by
    simpa only [one_mul, multiplierMap_apply] using multiplier_norm_le A)

theorem multiplierTranslation_contDiff (A : BoundedSmoothField (Space →L[ℝ] Space)) :
    ContDiff ℝ ∞ (fun a => multiplier (translated A.field a)) := by
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) (E := Field)
    (F := EulerMeanSolenoidal.L2 →L[ℝ] EulerMeanSolenoidal.L2) multiplierMap).comp
        A.translation_contDiff

theorem norm_iteratedFDeriv_multiplierTranslation_le
    (A : BoundedSmoothField (Space →L[ℝ] Space)) (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖iteratedFDeriv ℝ n (A.field : Space → Space →L[ℝ] Space) x‖ ≤ C)
    (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b => multiplier (translated A.field b)) a‖ ≤ C := by
  have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := Space)
    (F := Field) (G := EulerMeanSolenoidal.L2 →L[ℝ] EulerMeanSolenoidal.L2)
    multiplierMap (A.translation_contDiff.contDiffAt (x := a)) (n := n) (by simp)
  exact h.trans ((mul_le_mul_of_nonneg_right multiplierMap_norm_le_one (norm_nonneg _)).trans
    (by simpa only [one_mul] using A.norm_iteratedFDeriv_translation_le n C hC hbound a))

end EulerMeanCoefficients

end
end

end

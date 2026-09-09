/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanFixedTranslation
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpGramInverse
public import LeanPool.NavierStokesAndEuler.Euler.MeanStrongCoordinates

@[expose] public section

/-!
# Translation covariance of the actual mean acceleration

The Gram inverse on the fixed solenoidal time space is the genuine coercive
inverse. Its translated family has the same lower bound, and its application
is the spatial orbit of the original acceleration. The final identification
uses the already proved strong equation of the actual variational solution.
-/

noncomputable section

open EulerMeanSolenoidal EulerTimeLp

-- Reuse the nested Hilbert-space instances throughout both namespaces.
private local instance : NormedAddCommGroup solenoidalSpace := inferInstance
private local instance : InnerProductSpace ℝ solenoidalSpace := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup (TimeLp T L2) := inferInstance
private local instance (T : ℝ) : InnerProductSpace ℝ (TimeLp T L2) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup (TimeLp T solenoidalSpace) := inferInstance
private local instance (T : ℝ) : InnerProductSpace ℝ (TimeLp T solenoidalSpace) := inferInstance

namespace EulerMeanGramTranslation

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerMeanTimeTranslation EulerMeanOperatorTranslation
  EulerMeanFixedTranslation EulerMeanVariationalInverse EulerTimeLp
  EulerVolterraConvolution EulerTimeLpGramInverse EulerCoerciveProjection
  EulerTransverseGramInverse EulerTransverseStrongEstimates

variable (T : ℝ) (hT : 0 ≤ T)

/-- The actual spatially translated frame retains its original lower bound. -/
theorem translatedFrame_lower (F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (c : ℝ)
    (hF : ∀ t v, c*‖v‖^2 ≤ ‖solenoidalFrame T F t v‖^2)
    (a : Space) (t : Icc (0 : ℝ) T) (v : solenoidalSpace) :
    c*‖v‖^2 ≤ ‖solenoidalFrame T (translatePath T a F) t v‖^2 := by
  have h := hF t (solenoidalTranslation (-a) v)
  change c*‖solenoidalTranslation (-a) v‖^2 ≤
    ‖F t (translation (-a) (v : L2))‖^2 at h
  change c*‖v‖^2 ≤ ‖translation a (F t (translation (-a) (v : L2)))‖^2
  simpa only [LinearIsometry.norm_map] using h

/-- The adjoint frame multiplier transforms by ordinary spatial translation. -/
theorem frameMultiplier_adjoint_translate (a : Space)
    (F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (f : TimeLp T L2) :
    (timeMultiplier T hT (solenoidalFrame T (translatePath T a F))).adjoint
        (timeTranslation T a f) =
      timeSolenoidalTranslation T a ((timeMultiplier T hT (solenoidalFrame T F)).adjoint f) := by
  apply eq_of_translated_pairing T a
  intro v
  exact (adjoint_inner_left (timeMultiplier T hT (solenoidalFrame T (translatePath T a F)))
      (timeSolenoidalTranslation T a v) (timeTranslation T a f)).trans
    ((congrArg (fun z : TimeLp T L2 => ⟪timeTranslation T a f,z⟫_ℝ)
        (frameMultiplier_translate T hT a F v)).trans
      (((timeTranslation T a).inner_map_map f (timeMultiplier T hT (solenoidalFrame T F) v)).trans
        ((adjoint_inner_left (timeMultiplier T hT (solenoidalFrame T F)) v f).symm.trans
          ((timeSolenoidalTranslation T a).inner_map_map
            ((timeMultiplier T hT (solenoidalFrame T F)).adjoint f) v).symm)))

/-- Spatial translation conjugates the actual time Gram operator. -/
theorem gramOperator_translate (a : Space)
    (F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (u : TimeLp T solenoidalSpace) :
    gramOperator T hT (solenoidalFrame T (translatePath T a F))
        (timeSolenoidalTranslation T a u) =
      timeSolenoidalTranslation T a (gramOperator T hT (solenoidalFrame T F) u) :=
  (congrArg (timeMultiplier T hT (solenoidalFrame T (translatePath T a F))).adjoint
    (frameMultiplier_translate T hT a F u)).trans
      (frameMultiplier_adjoint_translate T hT a F (timeMultiplier T hT (solenoidalFrame T F) u))

/-- The actual coercive Gram inverse is covariant; no regularity of an inverse
or of the unknown solution is assumed. -/
theorem gramSolver_translate (a : Space)
    (F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (c : ℝ) (hc : 0 < c)
    (hF : ∀ t v, c*‖v‖^2 ≤ ‖solenoidalFrame T F t v‖^2)
    (g : TimeLp T solenoidalSpace) :
    gramSolver T hT (solenoidalFrame T (translatePath T a F)) c hc
        (translatedFrame_lower T F c hF a) (timeSolenoidalTranslation T a g) =
      timeSolenoidalTranslation T a (gramSolver T hT (solenoidalFrame T F) c hc hF g) := by
  apply (coerciveEquiv (gramOperator T hT (solenoidalFrame T (translatePath T a F))) c hc
    (gramOperator_coercive T hT (solenoidalFrame T (translatePath T a F)) c
      (translatedFrame_lower T F c hF a))).injective
  simp only [coerciveEquiv_apply]
  have hl := operator_inverse_apply (gramOperator T hT (solenoidalFrame T (translatePath T a F)))
    c hc (gramOperator_coercive T hT (solenoidalFrame T (translatePath T a F)) c
      (translatedFrame_lower T F c hF a)) (timeSolenoidalTranslation T a g)
  have hr := (gramOperator_translate T hT a F (gramSolver T hT (solenoidalFrame T F) c hc hF
    g)).trans
    (congrArg (timeSolenoidalTranslation T a)
      (operator_inverse_apply (gramOperator T hT (solenoidalFrame T F)) c hc
        (gramOperator_coercive T hT (solenoidalFrame T F) c hF) g))
  exact hl.trans hr.symm

/-- The genuine fixed-coordinate acceleration recovered from velocity and forcing. -/
def meanAcceleration (F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (c : ℝ) (hc : 0 < c) (hF : ∀ t v, c*‖v‖^2 ≤ ‖solenoidalFrame T F t v‖^2)
    (v : TimeLp T solenoidalSpace) (f : TimeLp T L2) : TimeLp T solenoidalSpace :=
  gramSolver T hT (solenoidalFrame T F) c hc hF
    ((timeMultiplier T hT (solenoidalFrame T F)).adjoint
      (f-(2 : ℝ) • timeMultiplier T hT (solenoidalFrame T F₁) v))

/-- The translated acceleration is obtained by the actual translated coefficients. -/
theorem meanAcceleration_translate (a : Space)
    (F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (c : ℝ) (hc : 0 < c) (hF : ∀ t v, c*‖v‖^2 ≤ ‖solenoidalFrame T F t v‖^2)
    (v : TimeLp T solenoidalSpace) (f : TimeLp T L2) :
    meanAcceleration T hT (translatePath T a F) (translatePath T a F₁) c hc
        (translatedFrame_lower T F c hF a) (timeSolenoidalTranslation T a v) (timeTranslation T a
          f) =
      timeSolenoidalTranslation T a (meanAcceleration T hT F F₁ c hc hF v f) := by
  have hr := congrArg (fun z : TimeLp T L2 => timeTranslation T a f-(2 : ℝ) • z)
    (frameMultiplier_translate T hT a F₁ v)
  have hr' : timeTranslation T a f-(2 : ℝ) •
      timeMultiplier T hT (solenoidalFrame T (translatePath T a F₁))
        (timeSolenoidalTranslation T a v) =
      timeTranslation T a (f-(2 : ℝ) • timeMultiplier T hT (solenoidalFrame T F₁) v) :=
    hr.trans (by simp only [map_sub, map_smul])
  have hg := (congrArg (timeMultiplier T hT (solenoidalFrame T (translatePath T a F))).adjoint
      hr').trans
    (frameMultiplier_adjoint_translate T hT a F
      (f-(2 : ℝ) • timeMultiplier T hT (solenoidalFrame T F₁) v))
  exact (congrArg (gramSolver T hT (solenoidalFrame T (translatePath T a F)) c hc
      (translatedFrame_lower T F c hF a)) hg).trans
    (gramSolver_translate T hT a F c hc hF
      ((timeMultiplier T hT (solenoidalFrame T F)).adjoint
        (f-(2 : ℝ) • timeMultiplier T hT (solenoidalFrame T F₁) v)))

end EulerMeanGramTranslation

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open Set MeasureTheory ContinuousLinearMap EulerTimeLp EulerVolterraConvolution
  EulerMeanSolenoidal EulerTransverseGramInverse EulerTransverseStrongEstimates
  EulerTimeLpGramInverse EulerMeanGramTranslation

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)

/-- The acceleration already constructed from the strong weak-solution theorem
is exactly the coercive Gram solve used for the spatial estimates. -/
theorem acceleration_eq_meanAcceleration (c : ℝ) (hc : 0 < c)
    (hF : ∀ t v, c*‖v‖^2 ≤ ‖solenoidalFrame T F t v‖^2) :
    s.acceleration = meanAcceleration T hT F F₁ c hc hF s.velocityLp f := by
  have heq : ∀ᵐ t ∂timeMeasure T,
      gram (extendPath T hT (solenoidalFrame T F) t) (s.acceleration t) =
      (solenoidalFrame T F (projIcc 0 T hT t)).adjoint
        (f t-(2 : ℝ) • solenoidalFrame T F₁ (projIcc 0 T hT t) (s.velocityLp t)) := by
    filter_upwards [s.equation, s.velocity_ae] with t ht hv
    have hh := congrArg (fun v : solenoidalSpace =>
      solenoidalProjection ((F (projIcc 0 T hT t)).adjoint
        (f t-(2 : ℝ) • F₁ (projIcc 0 T hT t) (v : L2)))) hv
    exact gram_equation_of_ordinary (F (projIcc 0 T hT t)) (F₁ (projIcc 0 T hT t))
      (f t) (s.acceleration t) (s.velocityLp t) (ht.trans hh.symm)
  exact (EulerTransverseStrongEstimates.acceleration_eq_inverse T (solenoidalFrame T F)
    (solenoidalFrame T F₁) c hc hF hT s.velocityLp s.acceleration f heq).trans
      (congrArg (fun G : TimeLp T solenoidalSpace →L[ℝ] TimeLp T solenoidalSpace =>
        G ((timeMultiplier T hT (solenoidalFrame T F)).adjoint
          (f-(2 : ℝ) • timeMultiplier T hT (solenoidalFrame T F₁) s.velocityLp)))
        (gramSolver_eq_multiplier T hT (solenoidalFrame T F) c hc hF)).symm

end EulerMeanVariationalInverse.StrongMeanEvolution

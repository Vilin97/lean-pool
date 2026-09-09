/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral
public import LeanPool.NavierStokesAndEuler.Euler.MeanContinuousVelocity
public import LeanPool.NavierStokesAndEuler.Euler.MeanCoordinatePath
public import LeanPool.NavierStokesAndEuler.Euler.MeanOperatorTranslation
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient
import LeanPool.NavierStokesAndEuler.Euler.MeanContinuousPhysical
import LeanPool.NavierStokesAndEuler.Euler.MeanMomentumRegularity
import LeanPool.NavierStokesAndEuler.Euler.MeanTimeSobolev
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevOperations
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The actual continuous mean pressure residual

The residual is constructed from the genuine continuous Gram acceleration.
Its F-adjoint lies in the ordinary closed gradient space at every time.
The true physical equation and fixed-Sobolev estimates hold in the same
continuous path space, including the interval endpoints.
-/

@[expose] public section


noncomputable section

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerMeanTimeTranslation EulerMeanOperatorTranslation
  EulerMeanTimeContinuousTranslation EulerMeanCoordinatePath EulerMeanContinuousPhysical
  EulerMeanTimeSobolev EulerContinuousTimeIntegral EulerContinuousGramAcceleration
  EulerTransverseGramInverse EulerTimeLp EulerVolterraConvolution
  EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)
  (c : ℝ) (hc : 0 < c) (hLower : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖solenoidalFrame T F t v‖ ^ 2)
  (fC : C(Icc (0 : ℝ) T, L2))

/-- The physical pressure force in the actual continuous strong equation. -/
def pressurePath : C(Icc (0 : ℝ) T,L2) :=
  fC-multiplier (solenoidalFrame T F) (s.classicalAcceleration c hc hLower fC) -
    (2 : ℝ) • multiplier (solenoidalFrame T F₁) s.coordinateVelocityPath

/-- The projected equation forces the actual pullback residual to be a gradient
at every time, not just almost everywhere in time. -/
theorem pressurePath_gradient (t : Icc (0 : ℝ) T) :
    (F t).adjoint (s.pressurePath c hc hLower fC t) ∈ gradientSpace := by
  have hg := accelerationPath_equation T (solenoidalFrame T F) (solenoidalFrame T F₁)
    c hc hLower s.coordinateVelocityPath fC t
  have hz : (solenoidalFrame T F t).adjoint (s.pressurePath c hc hLower fC t) = 0 := by
    have he : s.pressurePath c hc hLower fC t =
        fC t-(2 : ℝ) • solenoidalFrame T F₁ t (s.coordinateVelocityPath t) -
          solenoidalFrame T F t (s.classicalAcceleration c hc hLower fC t) := by
      change fC t-solenoidalFrame T F t (s.classicalAcceleration c hc hLower fC t) -
        (2 : ℝ) • solenoidalFrame T F₁ t (s.coordinateVelocityPath t) = _
      abel
    exact (congrArg (solenoidalFrame T F t).adjoint he).trans
      (((solenoidalFrame T F t).adjoint.map_sub _ _).trans (sub_eq_zero.mpr hg.symm))
  apply (solenoidalProjection_eq_zero_iff _).1
  have hh := congrArg (fun z : solenoidalSpace => (z : L2)) hz
  exact (congrArg (fun G : L2 →L[ℝ] solenoidalSpace =>
    (G (s.pressurePath c hc hLower fC t) : L2)) (solenoidalFrame_adjoint T F t)).symm.trans hh

/-- The physical pressure force is exactly f-B_t-MB for the given actual
coefficient relation F_t=MF. -/
theorem pressurePath_equation (hTpos : 0 < T)
    (hFTime : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    (M : C(Icc (0 : ℝ) T,L2 →L[ℝ] L2))
    (hMF : ∀ t v, F₁ t v = M t (F t v)) (t : Icc (0 : ℝ) T) :
    s.classicalPhysicalDerivative c hc hLower fC t+M t (s.continuousVelocity t) +
      s.pressurePath c hc hLower fC t = fC t := by
  rw [s.continuousVelocity_eq_frame hTpos hFTime]
  change F₁ t (s.coordinateVelocityPath t : L2) +
    F t (s.classicalAcceleration c hc hLower fC t : L2) +
    M t (F t (s.coordinateVelocityPath t : L2)) +
    (fC t-F t (s.classicalAcceleration c hc hLower fC t : L2) -
      (2 : ℝ) • F₁ t (s.coordinateVelocityPath t : L2)) = fC t
  rw [← hMF]
  simp only [two_smul]
  abel

/-- The actual spatial orbit of the pressure force has the literal residual formula. -/
theorem pressurePath_orbit_eq :
    (fun a : Space => pathTranslation T a (s.pressurePath c hc hLower fC)) =
      (fun a : Space => pathTranslation T a fC) -
      (fun a : Space => pathTranslation T a (multiplier (solenoidalFrame T F)
        (s.classicalAcceleration c hc hLower fC))) -
      (fun a : Space => (2 : ℝ) • pathTranslation T a
        (multiplier (solenoidalFrame T F₁) s.coordinateVelocityPath)) := by
  funext a
  simp only [pressurePath, map_sub, map_smul, Pi.sub_apply]

/-- Known actual field and coefficient orbits imply pressure-force regularity. -/
theorem pressurePath_translation_contDiff
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ ∞ (fun a : Space => coordinatePathTranslation T a s.coordinateVelocityPath))
    (ha : ContDiff ℝ ∞ (fun a : Space => coordinatePathTranslation T a (s.classicalAcceleration c
        hc hLower fC)))
    (hfC : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a fC)) :
    ContDiff ℝ ∞ (fun a : Space => pathTranslation T a (s.pressurePath c hc hLower fC)) := by
  rw [s.pressurePath_orbit_eq c hc hLower fC]
  exact (hfC.sub (framePathApply_translation_contDiff T F _ hF ha)).sub
    ((framePathApply_translation_contDiff T F₁ _ hF₁ hv).const_smul 2)

/-- The actual physical pressure gradient costs no further factorial shift. -/
theorem pressurePath_translation_block_gevrey {ι : Type*} [Fintype ι]
    (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ ∞ (fun a : Space => coordinatePathTranslation T a s.coordinateVelocityPath))
    (ha : ContDiff ℝ ∞ (fun a : Space => coordinatePathTranslation T a (s.classicalAcceleration c
        hc hLower fC)))
    (hfC : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a fC))
    (Rc R CF CF₁ Cf Cv Ca : ℝ) (hRc : 0 ≤ Rc) (hRcR : sobolevCoefficientRadius ι Rc ≤ R)
    (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCv : 0 ≤ Cv) (hCa : 0 ≤ Ca) (d : ℕ)
    (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant Rc 0
        n)
    (hF₁b : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant Rc
        0 n)
    (hfb : ∀ n a, block directions q (fun b : Space => pathTranslation T b fC) n a ≤ Cf*majorant R
        d n)
    (hvb : ∀ n a, block directions q (fun b : Space => coordinatePathTranslation T b
        s.coordinateVelocityPath) n a ≤ Cv*majorant R d n)
    (hab : ∀ n a, block directions q (fun b : Space => coordinatePathTranslation T b
        (s.classicalAcceleration c hc hLower fC)) n a ≤ Ca*majorant R d n)
    (n : ℕ) (a : Space) :
    block directions q (fun b : Space => pathTranslation T b (s.pressurePath c hc hLower fC)) n a ≤
      (Cf+3*sobolevCoefficientAmplitude ι q Rc CF*Ca +
        6*sobolevCoefficientAmplitude ι q Rc CF₁*Cv)*majorant R d n := by
  have hbA := framePathApply_translation_block_gevrey directions hd q T F _ hF ha
    Rc R CF Ca hRc hRcR hCF hCa d hFb hab
  have hbV := framePathApply_translation_block_gevrey directions hd q T F₁ _ hF₁ hv
    Rc R CF₁ Cv hRc hRcR hCF₁ hCv d hF₁b hvb
  have hb2V (k b) : block directions q (fun x : Space => (2 : ℝ) • pathTranslation T x
      (multiplier (solenoidalFrame T F₁) s.coordinateVelocityPath)) k b ≤
        (6*sobolevCoefficientAmplitude ι q Rc CF₁*Cv)*majorant R d k := by
    have hh := block_smul_gevrey directions q 2 _
      (framePathApply_translation_contDiff T F₁ _ hF₁ hv) R
      (3*sobolevCoefficientAmplitude ι q Rc CF₁*Cv) d hbV k b
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hh
    convert hh using 1
    ring
  have hbsub := block_sub_gevrey directions q _ _ hfC
    (framePathApply_translation_contDiff T F _ hF ha)
    R Cf (3*sobolevCoefficientAmplitude ι q Rc CF*Ca) d hfb hbA
  rw [s.pressurePath_orbit_eq c hc hLower fC]
  exact block_sub_gevrey directions q _ _
    (hfC.sub (framePathApply_translation_contDiff T F _ hF ha))
    ((framePathApply_translation_contDiff T F₁ _ hF₁ hv).const_smul 2)
    R (Cf+3*sobolevCoefficientAmplitude ι q Rc CF*Ca)
    (6*sobolevCoefficientAmplitude ι q Rc CF₁*Cv) d hbsub hb2V n a

end EulerMeanVariationalInverse.StrongMeanEvolution

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
import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathCalculus
import LeanPool.NavierStokesAndEuler.Euler.MeanContinuousPhysical
import LeanPool.NavierStokesAndEuler.Euler.MeanFixedCoefficientGevrey
import LeanPool.NavierStokesAndEuler.Euler.MeanFixedCoefficientRegularity
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevProductGevrey
import LeanPool.NavierStokesAndEuler.Euler.TimeH1SobolevReconstruction

/-!
# Genuine mean time traces and physical fields in fixed Sobolev word blocks

The fixed time reconstruction and actual frame products preserve the input
radius. No conversion of forcing or solution tensors is used.
-/

@[expose] public section


noncomputable section

namespace EulerMeanTimeSobolev

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanOperatorTranslation EulerMeanVariationalInverse
  EulerMeanTimeContinuousTranslation EulerMeanCoordinatePath EulerMeanContinuousPhysical
  EulerMeanFixedCoefficientRegularity EulerMeanFixedCoefficientGevrey
  EulerContinuousTimeIntegral EulerContinuousPathCalculus EulerGevrey
  EulerParameterWordGevrey
open scoped ContDiff

/-- Cache the standard `NormedAddCommGroup solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanTimeSobolev1 : NormedAddCommGroup solenoidalSpace := inferInstance
/-- Cache the standard `InnerProductSpace ℝ solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanTimeSobolev2 : InnerProductSpace ℝ solenoidalSpace := inferInstance
/-- Cache the standard `NormedAddCommGroup (solenoidalSpace →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanTimeSobolev3 : NormedAddCommGroup (solenoidalSpace →L[ℝ] L2) := inferInstance
/-- Cache the standard `NormedSpace ℝ (solenoidalSpace →L[ℝ] L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanTimeSobolev4 : NormedSpace ℝ (solenoidalSpace →L[ℝ] L2) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,L2 →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanTimeSobolev5 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,L2 →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,L2 →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanTimeSobolev6 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,L2 →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,solenoidalSpace →L[ℝ] L2)` instance
to shorten typeclass synthesis. -/
local instance instMeanTimeSobolev7 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,solenoidalSpace
    →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,solenoidalSpace →L[ℝ] L2)` instance to
shorten typeclass synthesis. -/
local instance instMeanTimeSobolev8 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,solenoidalSpace →L[ℝ]
    L2) :=
    inferInstance

/-- Multiplication by the genuine mean frame preserves the fixed base order
and the external radius. Its coefficient cost is paid once. -/
theorem framePathApply_translation_block_gevrey {ι : Type*} [Fintype ι]
    (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (T : ℝ) (F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (v : C(Icc (0 : ℝ) T, solenoidalSpace))
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hv : ContDiff ℝ ∞ (fun a : Space => coordinatePathTranslation T a v))
    (Rc R CF Cv : ℝ) (hRc : 0 ≤ Rc) (hRcR : sobolevCoefficientRadius ι Rc ≤ R)
    (hCF : 0 ≤ CF) (hCv : 0 ≤ Cv) (d : ℕ)
    (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant Rc 0
        n)
    (hvb : ∀ n a, block directions q (fun b : Space => coordinatePathTranslation T b v) n a ≤
        Cv*majorant R d n)
    (n : ℕ) (a : Space) :
    block directions q (fun b : Space => pathTranslation T b (multiplier (solenoidalFrame T F) v))
        n a ≤
      (3*sobolevCoefficientAmplitude ι q Rc CF*Cv)*majorant R d n := by
  let Q := fun b : Space => solenoidalFrame T (translatePath T b F)
  let A := fun b : Space => multiplier (Q b)
  have hQ : ContDiff ℝ ∞ Q := contDiff_solenoidalFrame T (fun b => translatePath T b F) hF
  have hA : ContDiff ℝ ∞ A := contDiff_multiplier Q hQ
  have hbA := multiplier_bound Q hQ Rc CF hRc hCF 0
    (solenoidalFrame_bound T (fun b => translatePath T b F) hF Rc CF hRc hCF 0 hFb)
  have hcA := coefficientBlock_of_tensor_bound directions hd q A hA Rc CF hRc hCF hbA
  have hs := block_clm_apply_gevrey directions q A (fun b => coordinatePathTranslation T b v)
    hA hv (sobolevCoefficientRadius ι Rc) R (sobolevCoefficientAmplitude ι q Rc CF) Cv
    (sobolevCoefficientRadius_nonneg Rc hRc) hRcR
    (sobolevCoefficientAmplitude_nonneg q Rc CF hRc hCF) hCv hcA d hvb n a
  exact (congrArg (fun g : Space → C(Icc (0 : ℝ) T,L2) => block directions q g n a)
    (framePathApply_orbit_eq T F v)).trans_le hs

end EulerMeanTimeSobolev

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal EulerMeanTimeTranslation
  EulerMeanOperatorTranslation EulerMeanTimeContinuousTranslation EulerMeanCoordinatePath
  EulerMeanContinuousPhysical  EulerMeanTimeSobolev
  EulerContinuousTimeIntegral EulerTimeH1SobolevReconstruction EulerTimeLp EulerVolterraConvolution
  EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)

/-- The actual H¹ coordinate trace preserves all external/base spatial words. -/
theorem coordinateVelocityPath_translation_block_gevrey {ι : Type*} [Fintype ι]
    (directions : ι → Space) (q : ℕ) (hTpos : 0 < T)
    (hv : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.velocityLp))
    (ha : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.acceleration))
    (R Cv Ca : ℝ) (d : ℕ)
    (hvb : ∀ n a, block directions q (fun b : Space => timeSolenoidalTranslation T b s.velocityLp)
        n a ≤ Cv*majorant R d n)
    (hab : ∀ n a, block directions q (fun b : Space => timeSolenoidalTranslation T b
        s.acceleration) n a ≤ Ca*majorant R d n)
    (n : ℕ) (a : Space) :
    block directions q (fun b : Space => coordinatePathTranslation T b s.coordinateVelocityPath) n
        a ≤
      (T⁻¹*Real.sqrt T*Cv+2*Real.sqrt T*Ca)*majorant R d n :=
  (congrArg (fun g : Space → C(Icc (0 : ℝ) T,solenoidalSpace) => block directions q g n a)
    (s.coordinateVelocityPath_orbit_eq hTpos)).trans_le
      (reconstruction_block_gevrey directions q T hTpos
        (fun b : Space => timeSolenoidalTranslation T b s.velocityLp)
        (fun b : Space => timeSolenoidalTranslation T b s.acceleration) hv ha R Cv Ca d hvb hab n a)

/-- The continuous physical velocity is the literal frame product at every time. -/
theorem continuousVelocity_eq_frame (hTpos : 0 < T)
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t) :
    s.continuousVelocity = multiplier (solenoidalFrame T F) s.coordinateVelocityPath := by
  apply ContinuousMap.ext
  intro t
  exact (s.continuousVelocity_eq_physicalPath hTpos hF t).trans
    (congrArg (fun r : Icc (0 : ℝ) T => F r (s.velocity t : L2))
      (projIcc_of_mem hT t.property))

/-- The actual physical time derivative is bounded by its two real frame
products, in exactly the same fixed Sobolev blocks. -/
theorem classicalPhysicalDerivative_translation_block_gevrey {ι : Type*} [Fintype ι]
    (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (c : ℝ) (hc : 0 < c) (hLower : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖solenoidalFrame T F t v‖ ^ 2)
    (fC : C(Icc (0 : ℝ) T, L2))
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ ∞ (fun a : Space => coordinatePathTranslation T a s.coordinateVelocityPath))
    (ha : ContDiff ℝ ∞ (fun a : Space => coordinatePathTranslation T a (s.classicalAcceleration c
        hc hLower fC)))
    (Rc R CF CF₁ Cv Ca : ℝ) (hRc : 0 ≤ Rc) (hRcR : sobolevCoefficientRadius ι Rc ≤ R)
    (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCv : 0 ≤ Cv) (hCa : 0 ≤ Ca) (d : ℕ)
    (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant Rc 0
        n)
    (hF₁b : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant Rc
        0 n)
    (hvb : ∀ n a, block directions q (fun b : Space => coordinatePathTranslation T b
        s.coordinateVelocityPath) n a ≤ Cv*majorant R d n)
    (hab : ∀ n a, block directions q (fun b : Space => coordinatePathTranslation T b
        (s.classicalAcceleration c hc hLower fC)) n a ≤ Ca*majorant R d n)
    (n : ℕ) (a : Space) :
    block directions q (fun b : Space => pathTranslation T b (s.classicalPhysicalDerivative c hc
        hLower fC)) n a ≤
      (3*(sobolevCoefficientAmplitude ι q Rc CF₁*Cv +
        sobolevCoefficientAmplitude ι q Rc CF*Ca))*majorant R d n := by
  have he : (fun b : Space => pathTranslation T b (s.classicalPhysicalDerivative c hc hLower fC)) =
      (fun b : Space => pathTranslation T b (multiplier (solenoidalFrame T F₁)
          s.coordinateVelocityPath)) +
      (fun b : Space => pathTranslation T b (multiplier (solenoidalFrame T F)
          (s.classicalAcceleration c hc hLower fC))) := by
    funext b
    exact (congrArg (pathTranslation T b) (s.classicalPhysicalDerivative_eq_products c hc hLower
        fC)).trans
      ((pathTranslation T b).map_add _ _)
  have hb := block_add_gevrey directions q
    (fun b : Space => pathTranslation T b (multiplier (solenoidalFrame T F₁)
        s.coordinateVelocityPath))
    (fun b : Space => pathTranslation T b (multiplier (solenoidalFrame T F)
        (s.classicalAcceleration c hc hLower fC)))
    (framePathApply_translation_contDiff T F₁ s.coordinateVelocityPath hF₁ hv)
    (framePathApply_translation_contDiff T F (s.classicalAcceleration c hc hLower fC) hF ha)
    R (3*sobolevCoefficientAmplitude ι q Rc CF₁*Cv) (3*sobolevCoefficientAmplitude ι q Rc CF*Ca) d
    (framePathApply_translation_block_gevrey directions hd q T F₁ s.coordinateVelocityPath
      hF₁ hv Rc R CF₁ Cv hRc hRcR hCF₁ hCv d hF₁b hvb)
    (framePathApply_translation_block_gevrey directions hd q T F (s.classicalAcceleration c hc
        hLower fC)
      hF ha Rc R CF Ca hRc hRcR hCF hCa d hFb hab) n a
  rw [he]
  exact hb.trans_eq (by ring)

end EulerMeanVariationalInverse.StrongMeanEvolution

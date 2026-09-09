/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanSourceSpatialRegularity
public import LeanPool.NavierStokesAndEuler.Euler.MeanStrongGevrey
public import LeanPool.NavierStokesAndEuler.Euler.MeanSourceSobolev
public import LeanPool.NavierStokesAndEuler.Euler.MeanSourceStrongSobolev
public import LeanPool.NavierStokesAndEuler.Euler.MeanStrongSobolev
public import LeanPool.NavierStokesAndEuler.Euler.MeanPressureSobolev

@[expose] public section

/-!
# Concrete source estimates for the strong mean inverse

The literal source coefficient bounds and actual forcing orbit bounds imply
the successive coordinate and physical-field factorial estimates. Coercivity,
boundary cutoff calculus, Gram inversion, and time reconstruction are all
proved constructions used by this theorem.
-/

noncomputable section

namespace EulerMeanSourcePressureSobolev

open MeasureTheory Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanCoefficients EulerMeanBoundary EulerMeanHarmonic EulerMeanSourceInverse
  EulerMeanVariationalInverse EulerMeanSourceFixedInverse EulerMeanSourceGevrey
  EulerMeanSourceSpatialRegularity EulerMeanTimeTranslation EulerMeanOperatorTranslation
  EulerMeanTimeContinuousTranslation EulerMeanTranslatedGevrey EulerTimeLp EulerVolterraConvolution
  EulerTimeLpGramGevrey EulerGevrey EulerParameterWordGevrey
  EulerMeanSourceSobolev EulerMeanFixedSobolevGevrey EulerMeanSourceStrongSobolev
  EulerMeanStrongContinuousGevrey EulerTimeLpGramSobolev
open scoped NNReal ContDiff

variable {ι : Type*} [Fintype ι]
  (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (T : ℝ) (hT : 0 ≤ T) (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1)
  (F F₁ H : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (M0 : BoundedSmoothField (Space →L[ℝ] Space)) (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (Be Bc L r : ℝ) (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc)
  (hL : boundaryLocalizationC1*Bc ≤ L) (hr : 0 ≤ r) (hrquarter : r ≤ 1/4)
  (hext : ∀ x, r ≤ ‖ℓ • x‖ → ∀ v : Space, -Be*‖v‖^2 ≤ ⟪M0.field x v,v⟫_ℝ)
  (hcore : ∀ x, ‖ℓ • x‖ < r → ∀ v : Space, -Bc*‖v‖^2 ≤ ⟪M0.field x v,v⟫_ℝ)
  (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (operatorPath T F.field t x) = x)
  (hF : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT (operatorPath T F.field))
      (operatorPath T F₁.field t) (Icc (0 : ℝ) T) t)
  (hRight : ∀ (t : Icc (0 : ℝ) T) (x : L2), operatorPath T F.field t (FInv t x) = x)
  (K : ℝ) (hK : 0 ≤ K)
  (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
  (hH : ∀ t x v, ⟪H.field t x v,v⟫_ℝ ≤ K*‖v‖^2)
  (hsmall : K*(T^2/2)+Be*T+boundaryLocalizationC2*Bc*r^3*T ≤ 1/2)
  (f : TimeLp T L2)
  (s : StrongMeanEvolution T hT FInv (operatorPath T F.field) (operatorPath T F₁.field)
    (boundaryOperator (scaledCutoff ℓ hℓ)) L
    (sourceMeanSolver T hT ℓ hℓ M0.field M0.field.continuous.aestronglyMeasurable
      ‖M0.field‖₊ M0.field.norm_coe_le_norm Be Bc L r hBe hBc hL hr hrquarter hext hcore
      FInv (operatorPath T H.field) K hK hF0 (operatorPath_quadratic_upper T H.field K hH) hsmall
        f) f)
  (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f))
  (Rc R M CF CF₁ CH CM Cf : ℝ) (hRc : 1024 ≤ Rc)
  (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCH : 0 ≤ CH) (hCM : 0 ≤ CM) (hCf : 0 ≤ Cf)
  (hM : 1 ≤ M)
  (hMC : sobolevInverseCost (sourceFixedCoercivity T F F₁ FInv)⁻¹
    (operatorBlockAmplitude ι q T Rc CF CF₁ CH CM scaledBoundaryOperatorAmplitude L) q*
    operatorBlockAmplitude ι q T Rc CF CF₁ CH CM scaledBoundaryOperatorAmplitude L ≤ M)
  (hMD : sobolevInverseCost (sourceFixedCoercivity T F F₁ FInv)⁻¹
    (operatorBlockAmplitude ι q T Rc CF CF₁ CH CM scaledBoundaryOperatorAmplitude L) q*
    forcingBlockAmplitude ι q T Rc CF CF₁ Cf ≤ M)
  (hR : 2*M*(sobolevCoefficientRadius ι Rc+1) ≤ R)
  (hFb : ∀ n t x, ‖iteratedFDeriv ℝ n (F.field t : Space → Space →L[ℝ] Space) x‖ ≤ CF*majorant Rc 0
    n)
  (hF₁b : ∀ n t x, ‖iteratedFDeriv ℝ n (F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ CF₁*majorant
    Rc 0 n)
  (hHb : ∀ n t x, ‖iteratedFDeriv ℝ n (H.field t : Space → Space →L[ℝ] Space) x‖ ≤ CH*majorant Rc 0
    n)
  (hMb : ∀ n x, ‖iteratedFDeriv ℝ n (M0.field : Space → Space →L[ℝ] Space) x‖ ≤ CM*majorant Rc 0 n)
  (d : ℕ)
  (hfb : ∀ n a, block directions q (fun b : Space => timeTranslation T b f) n a ≤ Cf*majorant R d n)

include hd hℓ1 hInv hF hRight hf hRc hCF hCF₁ hCH hCM hCf hM hMC hMD hR hFb hF₁b hHb hMb hfb

/-- The literal source pressure force is smooth and has the same fixed-Hq grade as B_t. -/
theorem source_pressure_block_bounds
    (hstrong : 2*gramBlockCost ι q (meanFrameCoercivity T FInv) Rc CF
      (accelerationBlockAmplitude ι q Rc CF CF₁ Cf 1)*(sobolevCoefficientRadius ι Rc+1) ≤ R)
    (hstrongC : 2*gramBlockCost ι q (meanFrameCoercivity T FInv) Rc CF
      (accelerationBlockAmplitude ι q Rc CF CF₁ Cf (coordinateTraceCost T))*
      (sobolevCoefficientRadius ι Rc+1) ≤ R)
    (hTpos : 0 < T) (fC : C(Icc (0 : ℝ) T,L2))
    (hfC : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a fC))
    (hfCb : ∀ n a, block directions q (fun b : Space => pathTranslation T b fC) n a ≤ Cf*majorant R
      d n) :
    (ContDiff ℝ ∞ (fun a : Space => pathTranslation T a
      (s.pressurePath (meanFrameCoercivity T FInv) (meanFrameCoercivity_pos T FInv)
        (solenoidalFrame_lower T FInv (operatorPath T F.field) hInv) fC))) ∧
    (∀ n a, block directions q (fun b : Space => pathTranslation T b
      (s.pressurePath (meanFrameCoercivity T FInv) (meanFrameCoercivity_pos T FInv)
        (solenoidalFrame_lower T FInv (operatorPath T F.field) hInv) fC)) n a ≤
      (Cf+3*sobolevCoefficientAmplitude ι q Rc CF+
        6*sobolevCoefficientAmplitude ι q Rc CF₁*coordinateTraceCost T)*majorant R (d+3) n) := by
  have hRc0 : 0 ≤ Rc := (by norm_num : (0 : ℝ) ≤ 1024).trans hRc
  have hrc : 0 ≤ sobolevCoefficientRadius ι Rc := sobolevCoefficientRadius_nonneg Rc hRc0
  have hR1 : 1 ≤ R := by nlinarith
  have hRcR : sobolevCoefficientRadius ι Rc ≤ R := by nlinarith
  have hFr : ContDiff ℝ ∞ (fun a : Space => translatePath T a (operatorPath T F.field)) := by
    simpa only [translatePath_operatorPath] using operatorPathTranslation_contDiff T F
  have hF₁r : ContDiff ℝ ∞ (fun a : Space => translatePath T a (operatorPath T F₁.field)) := by
    simpa only [translatePath_operatorPath] using operatorPathTranslation_contDiff T F₁
  have hv := EulerMeanSourceSpatialRegularity.velocity_translation_contDiff
    T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r hBe hBc hL hr hrquarter hext hcore
    hInv hF hRight K hK hF0 hH hsmall f s hf
  have hvb := velocity_translation_block_gevrey directions hd q T hT ℓ hℓ hℓ1
    F F₁ H M0 FInv Be Bc L r hBe hBc hL hr hrquarter hext hcore hInv hF hRight
    K hK hF0 hH hsmall f s hf Rc R M CF CF₁ CH CM Cf hRc hCF hCF₁ hCH hCM hCf
    hM hMC hMD hR hFb hF₁b hHb hMb d hfb
  exact s.pressure_time_block_bounds directions hd q hTpos
    (meanFrameCoercivity T FInv) (meanFrameCoercivity_pos T FInv)
    (solenoidalFrame_lower T FInv (operatorPath T F.field) hInv) fC
    hFr hF₁r hv hf hfC Rc R CF CF₁ Cf hRc0 hR1 hRcR hCF hCF₁ hCf hstrong hstrongC
    (translatedPath_bound T F Rc CF hRc0 hCF hFb)
    (translatedPath_bound T F₁ Rc CF₁ hRc0 hCF₁ hF₁b) d hfb hfCb hvb

end EulerMeanSourcePressureSobolev

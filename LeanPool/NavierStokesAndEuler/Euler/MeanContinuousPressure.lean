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
import LeanPool.NavierStokesAndEuler.Euler.MeanTimeSobolev
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevOperations
import Mathlib.Analysis.Calculus.ContDiff.Operations
public import LeanPool.NavierStokesAndEuler.Euler.MeanDisplacementRegularity
public import LeanPool.NavierStokesAndEuler.Euler.TransverseMomentumRegularity
import LeanPool.NavierStokesAndEuler.Euler.TimeWeakDerivative

/-!
# The actual continuous mean pressure residual

The residual is constructed from the genuine continuous Gram acceleration.
Its F-adjoint lies in the ordinary closed gradient space at every time.
The true physical equation and fixed-Sobolev estimates hold in the same
continuous path space, including the interval endpoints.
-/

section

/-!
# Genuine mean momentum regularity from the variational solve

Zero-initial-trace solenoidal test primitives are mapped by F into the actual
mean test space. The two original boundary terms then vanish, and the weak
identity constructs an AC representative of `Pσ F* η_t`. This is a regularity
conclusion, not an assumed momentum equation or an assumed second derivative.
-/

@[expose] public section

noncomputable section

namespace EulerMeanVariationalInverse

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerVolterraConvolution EulerMeanSolenoidal
  EulerTimeH1OperatorProduct EulerTimeWeakDerivative EulerTransverseMomentumRegularity

variable (T : ℝ) (hT : 0 ≤ T)
  (FInv F F' : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))

/-- The frame adjoint is the actual ordinary solenoidal projection of `F*`. -/
theorem solenoidalFrame_adjoint (t : Icc (0 : ℝ) T) :
    (solenoidalFrame T F t).adjoint =
      solenoidalSpace.orthogonalProjectionOnto.comp (F t).adjoint := by
  change ((F t).comp solenoidalSpace.subtypeL).adjoint = _
  calc
    _ = solenoidalSpace.subtypeL.adjoint.comp (F t).adjoint :=
      adjoint_comp _ _
    _ = _ := congrArg (fun A : L2 →L[ℝ] solenoidalSpace => A.comp (F t).adjoint)
      (Submodule.adjoint_subtypeL solenoidalSpace)

/-- Thus the momentum's actual representative is `Pσ F* u`, with ordinary
spatial L² projection and no abstract replacement of the solenoidal space. -/
theorem meanMomentum_ae (u : TimeLp T L2) :
    (fun t => ((momentum T hT (solenoidalFrame T F) u t : solenoidalSpace) : L2))
      =ᵐ[timeMeasure T]
      fun t => solenoidalProjection ((extendPath T hT F t).adjoint (u t)) := by
  filter_upwards [momentum_ae T hT (solenoidalFrame T F) u] with t ht
  rw [ht]
  change (((solenoidalFrame T F (projIcc 0 T hT t)).adjoint (u t) : solenoidalSpace) : L2) = _
  exact congrArg (fun A : L2 →L[ℝ] solenoidalSpace => (A (u t) : L2))
    (solenoidalFrame_adjoint T F (projIcc 0 T hT t))

/-- The exact mean variational identity determines the weak derivative of its
actual projected momentum after the trace-zero test restriction. -/
theorem meanMomentum_weak
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F' t) (Icc (0 : ℝ) T) t)
    (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (F t x) = x)
    (H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (M0 A : L2 →L[ℝ] L2) (L : ℝ)
    (u : meanDerivatives T hT FInv) (f : TimeLp T L2)
    (hu : ∀ w : meanDerivatives T hT FInv,
      ⟪(u : TimeLp T L2), (w : TimeLp T L2)⟫_ℝ -
        ⟪timeMultiplier T hT H (meanPrimitive T hT FInv u), meanPrimitive T hT FInv w⟫_ℝ +
        ⟪M0 (meanTrace T hT FInv u), meanTrace T hT FInv w⟫_ℝ +
        L*⟪A (meanTrace T hT FInv u), meanTrace T hT FInv w⟫_ℝ =
        -⟪f, meanPrimitive T hT FInv w⟫_ℝ)
    (v : TimeLp T solenoidalSpace) (hv : initialTrace T hT v = 0) :
    ⟪momentum T hT (solenoidalFrame T F) (u : TimeLp T L2), v⟫_ℝ =
      -⟪momentumForcing T hT (solenoidalFrame T F) (solenoidalFrame T F') H
        (u : TimeLp T L2) f, primitiveTimeLp T hT v⟫_ℝ := by
  apply momentum_weak_of_product_tests T hT (solenoidalFrame T F) (solenoidalFrame T F')
    (solenoidalFrame_hasDerivWithinAt T hT F F' hF) H (u : TimeLp T L2) f v
  have h := hu (meanTestMap T hT FInv F F' hF hInv v)
  simpa only [meanTestMap_trace_zero T hT FInv F F' hF hInv v hv,
    inner_zero_right, mul_zero, add_zero, meanPrimitive, comp_apply,
    Submodule.subtypeL_apply, meanTestMap_coe] using h

/-- An actual weak mean solution has an AC momentum representative with the
explicit Bochner L² derivative forced by the variational identity. -/
theorem meanMomentum_ac (hTpos : 0 < T)
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F' t) (Icc (0 : ℝ) T) t)
    (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (F t x) = x)
    (H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (M0 A : L2 →L[ℝ] L2) (L : ℝ)
    (u : meanDerivatives T hT FInv) (f : TimeLp T L2)
    (hu : ∀ w : meanDerivatives T hT FInv,
      ⟪(u : TimeLp T L2), (w : TimeLp T L2)⟫_ℝ -
        ⟪timeMultiplier T hT H (meanPrimitive T hT FInv u), meanPrimitive T hT FInv w⟫_ℝ +
        ⟪M0 (meanTrace T hT FInv u), meanTrace T hT FInv w⟫_ℝ +
        L*⟪A (meanTrace T hT FInv u), meanTrace T hT FInv w⟫_ℝ =
        -⟪f, meanPrimitive T hT FInv w⟫_ℝ) :
    ∃ p : ℝ → solenoidalSpace,
      AbsolutelyContinuousOnInterval p 0 T ∧
      (momentum T hT (solenoidalFrame T F) (u : TimeLp T L2) : ℝ → solenoidalSpace)
        =ᵐ[timeMeasure T] p ∧
      ∀ᵐ t ∂timeMeasure T,
        HasDerivAt p (momentumForcing T hT (solenoidalFrame T F) (solenoidalFrame T F')
          H (u : TimeLp T L2) f t) t := by
  apply exists_ac_representative_of_weak T hTpos
  intro v hv
  exact meanMomentum_weak T hT FInv F F' hF hInv H M0 A L u f hu v hv

/-- In particular the already constructed mean variational inverse has genuine
projected momentum regularity. The coefficient/boundary lower bounds are used
only by that solve; no regularity of the answer is assumed. -/
theorem meanSolver_momentum_ac (hTpos : 0 < T)
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F' t) (Icc (0 : ℝ) T) t)
    (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (F t x) = x)
    (H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (M0 A : L2 →L[ℝ] L2)
    (L K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
    (hH : ∀ t z, ⟪H t z, z⟫_ℝ ≤ K*‖z‖^2)
    (hboundary : ∀ z : L2, z ∈ solenoidalSpace →
      -B*‖z‖^2 ≤ ⟪M0 z, z⟫_ℝ+L*⟪A z, z⟫_ℝ)
    (hsmall : K*(T^2/2)+B*T ≤ 1/2) (f : TimeLp T L2) :
    let u : TimeLp T L2 :=
      meanSolver T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f
    ∃ p : ℝ → solenoidalSpace,
      AbsolutelyContinuousOnInterval p 0 T ∧
      (momentum T hT (solenoidalFrame T F) u : ℝ → solenoidalSpace) =ᵐ[timeMeasure T] p ∧
      ∀ᵐ t ∂timeMeasure T,
        HasDerivAt p (momentumForcing T hT (solenoidalFrame T F) (solenoidalFrame T F') H u f t) t
            :=
  meanMomentum_ac T hT FInv F F' hTpos hF hInv H M0 A L
    (meanSolver T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f) f
    (meanSolver_weak T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f)

end EulerMeanVariationalInverse

end
end

end

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

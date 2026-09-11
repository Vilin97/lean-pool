/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanContinuousVelocity
public import LeanPool.NavierStokesAndEuler.Euler.MeanOperatorTranslation
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpGramGevrey
import LeanPool.NavierStokesAndEuler.Euler.MeanAccelerationGevrey
import LeanPool.NavierStokesAndEuler.Euler.MeanPhysicalTranslation
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
public import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalTime
import LeanPool.NavierStokesAndEuler.Euler.MeanContinuousPhysical
import LeanPool.NavierStokesAndEuler.Euler.MeanPathSpatialRepresentative
import LeanPool.NavierStokesAndEuler.Euler.MeanPathTimeDerivative

/-! Related estimates used together by the same construction modules. -/

section

/-!
# All-order estimates for the genuine strong mean fields

The actual coordinate velocity estimate supplied by the weak inverse gives
the next-shift acceleration estimate and the physical B, B_t estimates.
The constants are fixed polynomials in the coefficient amplitudes and the
proved inverse bound; none depends on the derivative order.
-/

@[expose] public section

noncomputable section

namespace EulerMeanStrongGevrey

open EulerGevrey

/-- Enlarging the integer shift preserves a factorial bound when the radius is at least one. -/
theorem majorant_shift_mono (R : ℝ) (hR : 1 ≤ R) (d n : ℕ) :
    majorant R d n ≤ majorant R (d+1) n := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have h : majorant R d n ≤ R*majorant R d n := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hR (majorant_nonneg R hR0 d n)
  exact h.trans (majorant_shift_le R hR0 d n)

end EulerMeanStrongGevrey

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanTimeContinuousTranslation
  EulerMeanGramTranslation EulerMeanAccelerationGevrey EulerMeanStrongGevrey
  EulerTimeLp EulerVolterraConvolution EulerTimeLpGramGevrey EulerOperatorGevreyCalculus EulerGevrey
open scoped ContDiff

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)

/-- The genuine acceleration is spatially smooth once the solved coordinate
velocity and prescribed coefficients and forcing are. -/
theorem acceleration_orbit_contDiff
    (c : ℝ) (hc : 0 < c)
    (hLower : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖solenoidalFrame T F t v‖ ^ 2)
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.velocityLp))
    (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f)) :
    ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.acceleration) := by
  have heq := congrArg (fun v : TimeLp T solenoidalSpace =>
    fun a : Space => timeSolenoidalTranslation T a v) (s.acceleration_eq_meanAcceleration c hc
        hLower)
  exact Eq.mpr (congrArg (fun g : Space → TimeLp T solenoidalSpace => ContDiff ℝ ∞ g) heq)
    (meanAcceleration_translation_contDiff T hT F F₁ c hc hLower s.velocityLp f hF hF₁ hv hf)

variable (c : ℝ) (hc : 0 < c)
  (hLower : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖solenoidalFrame T F t v‖ ^ 2)
  (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
  (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
  (hv : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.velocityLp))
  (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f))
  (Rc R CF CF₁ Cf : ℝ) (hRc : 0 ≤ Rc) (hR : 1 ≤ R) (hRcR : Rc ≤ R)
  (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCf : 0 ≤ Cf)
  (hstrong : 2 * gramCost c CF (3 * CF * (Cf + 6 * CF₁)) * (Rc + 1) ≤ R)
  (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF * majorant Rc 0
      n)
  (hF₁b : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁ * majorant Rc
      0
      n)
  (d : ℕ)
  (hfb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeTranslation T b f) a‖ ≤ Cf * majorant R d
      n)
  (hvb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeSolenoidalTranslation T b s.velocityLp)
      a‖ ≤ majorant R (d + 1) n)

include hc hLower hF hF₁ hv hf hRc hR hRcR hCF hCF₁ hCf hstrong hFb hF₁b hfb hvb in
/-- The actual strong fields have the source's successive factorial shifts. -/
theorem spatial_gevrey_bounds :
    (∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeSolenoidalTranslation T b s.acceleration) a‖ ≤
      majorant R (d+2) n) ∧
    (∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeTranslation T b s.velocityField) a‖ ≤
      (3*CF)*majorant R (d+1) n) ∧
    (∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeTranslation T b s.velocityDerivative) a‖ ≤
      (3*(CF₁+CF))*majorant R (d+2) n) := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hfb' (n a) : ‖iteratedFDeriv ℝ n (fun b : Space => timeTranslation T b f) a‖ ≤
      Cf*majorant R (d+1) n :=
    (hfb n a).trans (mul_le_mul_of_nonneg_left (majorant_shift_mono R hR d n) hCf)
  have hva (n a) := meanAcceleration_translation_gevrey T hT F F₁ c hc hLower s.velocityLp f
    hF hF₁ hv hf Rc R CF CF₁ Cf 1 hRc hR0 hRcR hCF hCF₁ hCf zero_le_one
    (by simpa only [mul_one] using hstrong) hFb hF₁b (d+1) hfb'
    (by simpa only [one_mul] using hvb) n a
  have heq := congrArg (fun v : TimeLp T solenoidalSpace =>
    fun a : Space => timeSolenoidalTranslation T a v) (s.acceleration_eq_meanAcceleration c hc
        hLower)
  have hab (n a) : ‖iteratedFDeriv ℝ n (fun b : Space => timeSolenoidalTranslation T b
      s.acceleration) a‖ ≤
      majorant R (d+2) n := by
    have h := (congrArg (fun g : Space → TimeLp T solenoidalSpace => ‖iteratedFDeriv ℝ n g a‖)
        heq).trans_le (hva n a)
    simpa only [Nat.add_assoc] using h
  have hFR (n a) : ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant R 0
      n :=
    (hFb n a).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc R hRc hRcR 0 n) hCF)
  have hF₁R (n a) : ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant R
      0 n :=
    (hF₁b n a).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc R hRc hRcR 0 n) hCF₁)
  have hBb (n a) : ‖iteratedFDeriv ℝ n (fun b : Space => timeTranslation T b s.velocityField) a‖ ≤
      (3*CF)*majorant R (d+1) n := by
    simpa only [mul_one] using s.velocityField_translation_gevrey hF hv R CF 1 hR0 hCF zero_le_one
      (d+1) hFR (by simpa only [one_mul] using hvb) n a
  have hvb' (n a) : ‖iteratedFDeriv ℝ n (fun b : Space => timeSolenoidalTranslation T b
      s.velocityLp) a‖ ≤
      1*majorant R (d+2) n := by
    simpa only [one_mul, Nat.add_assoc] using (hvb n a).trans (majorant_shift_mono R hR (d+1) n)
  have ha := s.acceleration_orbit_contDiff c hc hLower hF hF₁ hv hf
  refine ⟨hab, hBb, ?_⟩
  intro n a
  simpa only [mul_one] using s.velocityDerivative_translation_gevrey hF hF₁ hv ha
    R CF CF₁ 1 1 hR0 hCF hCF₁ zero_le_one zero_le_one (d+2) hFR hF₁R hvb'
    (by simpa only [one_mul] using hab) n a

include hc hLower hF hF₁ hv hf hRc hR hRcR hCF hCF₁ hCf hstrong hFb hF₁b hfb hvb in
/-- The actual continuous-time velocity has the same fixed factorial radius. -/
theorem continuousVelocity_spatial_gevrey (hTpos : 0 < T) (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => pathTranslation T b s.continuousVelocity) a‖ ≤
      ((T⁻¹*Real.sqrt T)*(3*CF)+(2*Real.sqrt T)*(3*(CF₁+CF)))*majorant R (d+2) n := by
  have hb := s.spatial_gevrey_bounds c hc hLower hF hF₁ hv hf Rc R CF CF₁ Cf hRc hR hRcR
    hCF hCF₁ hCf hstrong hFb hF₁b d hfb hvb
  have hBb (k b) : ‖iteratedFDeriv ℝ k (fun x : Space => timeTranslation T x s.velocityField) b‖ ≤
      (3*CF)*majorant R (d+2) k := by
    have h := (hb.2.1 k b).trans (mul_le_mul_of_nonneg_left (majorant_shift_mono R hR (d+1) k) (by
        positivity))
    simpa only [Nat.add_assoc] using h
  have ha := s.acceleration_orbit_contDiff c hc hLower hF hF₁ hv hf
  exact s.continuousVelocity_translation_gevrey hTpos (s.velocityField_translation_contDiff hF hv)
    (s.velocityDerivative_translation_contDiff hF hF₁ hv ha)
    R (3*CF) (3*(CF₁+CF)) (zero_le_one.trans hR) (by positivity) (by positivity) (d+2)
    hBb hb.2.2 n a

end EulerMeanVariationalInverse.StrongMeanEvolution

end
end

end

section

/-!
# Classical spatial representatives of the actual mean time evolution

The actual continuous velocity and continuous time derivative have smooth
spatial translation orbits. The bounded time-integral identity commutes
with those spatial derivatives, giving genuine jointly continuous spatial
representatives and their pointwise classical time derivative.
-/

@[expose] public section

noncomputable section

namespace EulerMeanClassicalSpatialTime

open Set MeasureTheory EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeContinuousTranslation EulerMeanSmoothRepresentative EulerVolterraConvolution
open scoped ContDiff

/-- Actual smooth representatives of a continuous L² path and its genuine
continuous derivative, with no separate mixed-derivative hypothesis. -/
theorem exists_classical_pair (T : ℝ) (hT : 0 ≤ T)
    (p q : C(Icc (0 : ℝ) T, L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p))
    (hq : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a q))
    (hder : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT p) (q t) (Icc (0 : ℝ) T) t) :
    ∃ B Bt : Icc (0 : ℝ) T → Space → Space,
      Continuous (fun z : Icc (0 : ℝ) T × Space => B z.1 z.2) ∧
      Continuous (fun z : Icc (0 : ℝ) T × Space => Bt z.1 z.2) ∧
      (∀ t, ContDiff ℝ ∞ (B t)) ∧ (∀ t, ContDiff ℝ ∞ (Bt t)) ∧
      (∀ t, (p t : Space → Space) =ᵐ[volume] B t) ∧
      (∀ t, (q t : Space → Space) =ᵐ[volume] Bt t) ∧
      ∀ t : Icc (0 : ℝ) T, ∀ x : Space,
        HasDerivWithinAt (fun r => B (projIcc 0 T hT r) x) (Bt t x) (Icc (0 : ℝ) T) t := by
  let B := fun t : Icc (0 : ℝ) T =>
    representative (p t) (pathTranslation_evaluation_contDiff T p hp t)
  let Bt := fun t : Icc (0 : ℝ) T =>
    representative (q t) (pathTranslation_evaluation_contDiff T q hq t)
  refine ⟨B, Bt, path_representative_joint_continuous T p hp,
    path_representative_joint_continuous T q hq,
    path_representative_smooth T p hp, path_representative_smooth T q hq,
    path_representative_ae T p hp, path_representative_ae T q hq, ?_⟩
  intro t x
  exact EulerMeanPathTimeDerivative.representative_hasDerivWithinAt T hT p q hder hp hq t x

end EulerMeanClassicalSpatialTime

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open Set MeasureTheory EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanTimeContinuousTranslation
  EulerMeanCoordinatePath EulerMeanClassicalSpatialTime EulerVolterraConvolution EulerTimeLp
open scoped ContDiff

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)
  (c : ℝ) (hc : 0 < c)
  (hLower : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖solenoidalFrame T F t v‖ ^ 2)
  (fC : C(Icc (0 : ℝ) T, L2))

/-- The reconstructed velocity path has its actual continuous derivative
at every time, including within-interval endpoint derivatives. -/
theorem continuousVelocity_hasDerivWithinAt (hTpos : 0 < T)
    (hf : (f : ℝ → L2) =ᵐ[timeMeasure T] extendPath T hT fC)
    (hFTime : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT s.continuousVelocity)
      (s.classicalPhysicalDerivative c hc hLower fC t) (Icc (0 : ℝ) T) t := by
  apply (s.physical_hasDerivWithinAt c hc hLower fC hf hFTime t).congr_of_mem _ t.property
  intro r hr
  change s.continuousVelocity (projIcc 0 T hT r) = s.physicalPath r
  rw [projIcc_of_mem hT hr]
  exact s.continuousVelocity_eq_physicalPath hTpos hFTime ⟨r, hr⟩

/-- Genuine space-time classical mean fields are obtained from the actual
solved coordinate velocity and acceleration orbits. -/
theorem exists_classical_spatial_pair (hTpos : 0 < T)
    (hf : (f : ℝ → L2) =ᵐ[timeMeasure T] extendPath T hT fC)
    (hFTime : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.velocityLp))
    (ha : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.acceleration))
    (hfC : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a fC)) :
    ∃ B Bt : Icc (0 : ℝ) T → Space → Space,
      Continuous (fun z : Icc (0 : ℝ) T × Space => B z.1 z.2) ∧
      Continuous (fun z : Icc (0 : ℝ) T × Space => Bt z.1 z.2) ∧
      (∀ t, ContDiff ℝ ∞ (B t)) ∧ (∀ t, ContDiff ℝ ∞ (Bt t)) ∧
      (∀ t : Icc (0 : ℝ) T, (s.physicalPath t : Space → Space) =ᵐ[volume] B t) ∧
      (∀ t, (s.classicalPhysicalDerivative c hc hLower fC t : Space → Space) =ᵐ[volume] Bt t) ∧
      ∀ t : Icc (0 : ℝ) T, ∀ x : Space,
        HasDerivWithinAt (fun r => B (projIcc 0 T hT r) x) (Bt t x) (Icc (0 : ℝ) T) t := by
  have hp := s.continuousVelocity_translation_contDiff
    (s.velocityField_translation_contDiff hF hv)
    (s.velocityDerivative_translation_contDiff hF hF₁ hv ha)
  have hvc := s.coordinateVelocityPath_translation_contDiff hTpos hv ha
  have hq := s.classicalPhysicalDerivative_translation_contDiff c hc hLower fC hF hF₁ hvc hfC
  obtain ⟨B, Bt, hBc, hBtc, hBs, hBts, hBa, hBta, hd⟩ :=
    exists_classical_pair T hT s.continuousVelocity (s.classicalPhysicalDerivative c hc hLower fC)
      hp hq (s.continuousVelocity_hasDerivWithinAt c hc hLower fC hTpos hf hFTime)
  refine ⟨B, Bt, hBc, hBtc, hBs, hBts, ?_, hBta, hd⟩
  intro t
  rw [← s.continuousVelocity_eq_physicalPath hTpos hFTime t]
  exact hBa t

end EulerMeanVariationalInverse.StrongMeanEvolution

end
end

end

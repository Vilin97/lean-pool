/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanAccelerationGevrey
public import LeanPool.NavierStokesAndEuler.Euler.MeanPhysicalTranslation
public import LeanPool.NavierStokesAndEuler.Euler.MeanContinuousVelocity

@[expose] public section

/-!
# All-order estimates for the genuine strong mean fields

The actual coordinate velocity estimate supplied by the weak inverse gives
the next-shift acceleration estimate and the physical B, B_t estimates.
The constants are fixed polynomials in the coefficient amplitudes and the
proved inverse bound; none depends on the derivative order.
-/

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
    (hLower : ∀ t v, c*‖v‖^2 ≤ ‖solenoidalFrame T F t v‖^2)
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
  (hLower : ∀ t v, c*‖v‖^2 ≤ ‖solenoidalFrame T F t v‖^2)
  (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
  (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
  (hv : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.velocityLp))
  (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f))
  (Rc R CF CF₁ Cf : ℝ) (hRc : 0 ≤ Rc) (hR : 1 ≤ R) (hRcR : Rc ≤ R)
  (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCf : 0 ≤ Cf)
  (hstrong : 2*gramCost c CF (3*CF*(Cf+6*CF₁))*(Rc+1) ≤ R)
  (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant Rc 0 n)
  (hF₁b : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant Rc 0
    n)
  (d : ℕ)
  (hfb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeTranslation T b f) a‖ ≤ Cf*majorant R d n)
  (hvb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeSolenoidalTranslation T b s.velocityLp)
    a‖ ≤ majorant R (d+1) n)

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

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanContinuousPhysical
public import LeanPool.NavierStokesAndEuler.Euler.MeanStrongGevrey

@[expose] public section

/-!
# Uniform-time factorial bounds for the strong mean solution

The proved H¹ reconstruction estimates the continuous coordinate velocity.
The actual continuous Gram inverse then controls acceleration and the
physical time derivative. All bounds concern genuine spatial derivatives.
-/

noncomputable section

namespace EulerMeanStrongContinuousGevrey

open EulerGevrey

/-- The fixed H¹ trace cost for unit velocity and acceleration jet amplitudes. -/
def coordinateTraceCost (T : ℝ) : ℝ := T⁻¹*Real.sqrt T+2*Real.sqrt T

theorem coordinateTraceCost_nonneg (T : ℝ) (hT : 0 ≤ T) : 0 ≤ coordinateTraceCost T := by
  unfold coordinateTraceCost
  positivity

end EulerMeanStrongContinuousGevrey

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanTimeContinuousTranslation
  EulerMeanCoordinatePath EulerMeanContinuousAcceleration EulerMeanStrongGevrey
  EulerMeanStrongContinuousGevrey EulerOperatorGevreyCalculus EulerTimeLpGramGevrey
  EulerTimeLp EulerGevrey
open scoped ContDiff

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T,L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)
  (c : ℝ) (hc : 0 < c)
  (hLower : ∀ t v, c*‖v‖^2 ≤ ‖solenoidalFrame T F t v‖^2)
  (fC : C(Icc (0 : ℝ) T,L2))

/-- Actual continuous acceleration and B_t obey uniform-time spatial
factorial bounds, with a fixed H¹ trace cost and one further Gram-inverse shift. -/
theorem continuous_strong_spatial_gevrey (hTpos : 0 < T)
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.velocityLp))
    (ha : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.acceleration))
    (hfC : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a fC))
    (Rc R CF CF₁ Cf : ℝ) (hRc : 0 ≤ Rc) (hR : 1 ≤ R) (hRcR : Rc ≤ R)
    (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCf : 0 ≤ Cf)
    (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant Rc 0
      n)
    (hF₁b : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant Rc
      0 n)
    (d : ℕ)
    (hvb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeSolenoidalTranslation T b s.velocityLp)
      a‖ ≤ majorant R (d+1) n)
    (hab : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeSolenoidalTranslation T b
      s.acceleration) a‖ ≤ majorant R (d+2) n)
    (hfb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => pathTranslation T b fC) a‖ ≤ Cf*majorant R
      d n)
    (hstrong : 2*gramCost c CF (3*CF*(Cf+6*CF₁*coordinateTraceCost T))*(Rc+1) ≤ R) :
    (∀ n a, ‖iteratedFDeriv ℝ n
      (fun b : Space => coordinatePathTranslation T b (s.classicalAcceleration c hc hLower fC)) a‖ ≤
        majorant R (d+3) n) ∧
    (∀ n a, ‖iteratedFDeriv ℝ n
      (fun b : Space => pathTranslation T b (s.classicalPhysicalDerivative c hc hLower fC)) a‖ ≤
        (3*(CF₁*coordinateTraceCost T+CF))*majorant R (d+3) n) := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have htrace := coordinateTraceCost_nonneg T hT
  have hvc := s.coordinateVelocityPath_translation_contDiff hTpos hv ha
  have hvcb (n : ℕ) (a : Space) :
      ‖iteratedFDeriv ℝ n (fun b : Space => coordinatePathTranslation T b s.coordinateVelocityPath)
        a‖ ≤
        coordinateTraceCost T*majorant R (d+2) n := by
    have h := s.coordinateVelocityPath_translation_gevrey hTpos hv ha R 1 1 hR0
      zero_le_one zero_le_one (d+2)
      (fun k x => by
        simpa only [one_mul, Nat.add_assoc] using
          (hvb k x).trans (majorant_shift_mono R hR (d+1) k))
      (fun k x => by simpa only [one_mul] using hab k x) n a
    simpa only [coordinateTraceCost, mul_one] using h
  have hfcb (n : ℕ) (a : Space) :
      ‖iteratedFDeriv ℝ n (fun b : Space => pathTranslation T b fC) a‖ ≤ Cf*majorant R (d+2) n := by
    apply (hfb n a).trans
    apply mul_le_mul_of_nonneg_left _ hCf
    simpa only [Nat.add_assoc] using
      (majorant_shift_mono R hR d n).trans (majorant_shift_mono R hR (d+1) n)
  have hac := s.classicalAcceleration_translation_contDiff c hc hLower fC hF hF₁ hvc hfC
  have hacb (n : ℕ) (a : Space) :
      ‖iteratedFDeriv ℝ n
        (fun b : Space => coordinatePathTranslation T b (s.classicalAcceleration c hc hLower fC))
          a‖ ≤
          majorant R (d+3) n := by
    have h := meanAccelerationPath_translation_gevrey T F F₁ c hc hLower s.coordinateVelocityPath fC
      hF hF₁ hvc hfC Rc R CF CF₁ Cf (coordinateTraceCost T) hRc hR0 hRcR
      hCF hCF₁ hCf htrace hstrong hFb hF₁b (d+2) hfcb hvcb n a
    simpa only [Nat.add_assoc, meanAccelerationPath, classicalAcceleration] using h
  refine ⟨hacb, ?_⟩
  have hFbR (n : ℕ) (a : Space) :
      ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant R 0 n :=
    (hFb n a).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc R hRc hRcR 0 n) hCF)
  have hF₁bR (n : ℕ) (a : Space) :
      ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant R 0 n :=
    (hF₁b n a).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc R hRc hRcR 0 n) hCF₁)
  intro n a
  have h := s.classicalPhysicalDerivative_translation_gevrey c hc hLower fC hF hF₁ hvc hac
    R CF CF₁ (coordinateTraceCost T) 1 hR0 hCF hCF₁ htrace zero_le_one (d+3) hFbR hF₁bR
    (fun k x => (hvcb k x).trans (mul_le_mul_of_nonneg_left
      (by simpa only [Nat.add_assoc] using majorant_shift_mono R hR (d+2) k) htrace))
    (fun k x => by simpa only [one_mul] using hacb k x) n a
  simpa only [mul_one] using h

end EulerMeanVariationalInverse.StrongMeanEvolution

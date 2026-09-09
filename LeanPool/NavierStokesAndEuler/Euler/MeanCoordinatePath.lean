/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalTime
public import LeanPool.NavierStokesAndEuler.Euler.MeanStrongGevrey
public import LeanPool.NavierStokesAndEuler.Euler.TimeH1ReconstructionNaturality

@[expose] public section

/-!
# Actual continuous coordinate-velocity spatial orbits

The coordinate velocity is reconstructed from its genuine L² value and
acceleration. Consequently its uniform-time spatial derivatives have the
same fixed H¹ trace bound as the physical velocity.
-/

noncomputable section

namespace EulerMeanCoordinatePath

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal EulerMeanTimeTranslation
  EulerTimeLp EulerTimeH1Reconstruction EulerGevrey
open scoped ContDiff

/-- Spatial translation of continuous solenoidal coordinate paths. -/
def coordinatePathTranslation (T : ℝ) (a : Space) :
    C(Icc (0 : ℝ) T,solenoidalSpace) →L[ℝ] C(Icc (0 : ℝ) T,solenoidalSpace) :=
  (solenoidalTranslation a).toContinuousLinearMap.compLeftContinuous ℝ (Icc (0 : ℝ) T)

@[simp] theorem coordinatePathTranslation_apply (T : ℝ) (a : Space)
    (p : C(Icc (0 : ℝ) T,solenoidalSpace)) (t : Icc (0 : ℝ) T) :
    coordinatePathTranslation T a p t = solenoidalTranslation a (p t) := rfl

theorem reconstruction_translation (T : ℝ) (hT : 0 ≤ T) (a : Space)
    (p q : TimeLp T solenoidalSpace) :
    coordinatePathTranslation T a (reconstruction T hT (p,q)) =
      reconstruction T hT (timeSolenoidalTranslation T a p, timeSolenoidalTranslation T a q) := by
  apply ContinuousMap.ext
  intro t
  exact (reconstruction_timeLift T hT (solenoidalTranslation a).toContinuousLinearMap p q t).symm

end EulerMeanCoordinatePath

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal EulerMeanTimeTranslation
  EulerMeanCoordinatePath EulerTimeLp EulerTimeH1Reconstruction EulerGevrey
open scoped ContDiff

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)

theorem coordinateVelocityPath_eq_reconstruction (hTpos : 0 < T) :
    s.coordinateVelocityPath = reconstruction T hT (s.velocityLp,s.acceleration) := by
  apply ContinuousMap.ext
  intro t
  exact (reconstruction_eq_path T hTpos s.velocityLp s.acceleration s.velocity
    s.velocity_ac s.velocity_ae s.velocity_derivative t).symm

theorem coordinateVelocityPath_orbit_eq (hTpos : 0 < T) :
    (fun a : Space => coordinatePathTranslation T a s.coordinateVelocityPath) =
      fun a : Space => reconstruction T hT
        (timeSolenoidalTranslation T a s.velocityLp, timeSolenoidalTranslation T a s.acceleration)
          := by
  funext a
  exact (congrArg (coordinatePathTranslation T a) (s.coordinateVelocityPath_eq_reconstruction
    hTpos)).trans
    (reconstruction_translation T hT a s.velocityLp s.acceleration)

/-- Uniform-time coordinate orbit regularity comes from the actual H¹ data. -/
theorem coordinateVelocityPath_translation_contDiff (hTpos : 0 < T) {n : ℕ∞ω}
    (hv : ContDiff ℝ n (fun a : Space => timeSolenoidalTranslation T a s.velocityLp))
    (ha : ContDiff ℝ n (fun a : Space => timeSolenoidalTranslation T a s.acceleration)) :
    ContDiff ℝ n (fun a : Space => coordinatePathTranslation T a s.coordinateVelocityPath) :=
  Eq.mpr (congrArg (fun g : Space → C(Icc (0 : ℝ) T,solenoidalSpace) => ContDiff ℝ n g)
    (s.coordinateVelocityPath_orbit_eq hTpos))
    (reconstruction_contDiff T hT (fun a : Space => timeSolenoidalTranslation T a s.velocityLp)
      (fun a : Space => timeSolenoidalTranslation T a s.acceleration) hv ha)

/-- Every spatial coordinate-velocity derivative has the same uniform-time trace cost. -/
theorem coordinateVelocityPath_translation_gevrey (hTpos : 0 < T)
    (hv : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.velocityLp))
    (ha : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.acceleration))
    (R Cv Ca : ℝ) (hR : 0 ≤ R) (hCv : 0 ≤ Cv) (hCa : 0 ≤ Ca) (d : ℕ)
    (hvb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeSolenoidalTranslation T b s.velocityLp)
      a‖ ≤ Cv*majorant R d n)
    (hab : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeSolenoidalTranslation T b
      s.acceleration) a‖ ≤ Ca*majorant R d n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => coordinatePathTranslation T b s.coordinateVelocityPath)
      a‖ ≤
      ((T⁻¹*Real.sqrt T)*Cv+(2*Real.sqrt T)*Ca)*majorant R d n :=
  (congrArg (fun g : Space → C(Icc (0 : ℝ) T,solenoidalSpace) => ‖iteratedFDeriv ℝ n g a‖)
    (s.coordinateVelocityPath_orbit_eq hTpos)).trans_le
      (reconstruction_gevrey T hTpos (fun b : Space => timeSolenoidalTranslation T b s.velocityLp)
        (fun b : Space => timeSolenoidalTranslation T b s.acceleration)
        hv ha R Cv Ca hR hCv hCa d hvb hab n a)

end EulerMeanVariationalInverse.StrongMeanEvolution

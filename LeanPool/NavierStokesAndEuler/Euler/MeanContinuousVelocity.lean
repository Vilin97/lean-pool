/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanVelocityPressure
public import LeanPool.NavierStokesAndEuler.Euler.MeanTimeContinuousTranslation

@[expose] public section

/-!
# Uniform-time spatial bounds for the actual mean velocity

The continuous velocity is reconstructed from its actual L² value and actual
L² time derivative. Terminal-primitive uniqueness identifies this path with
the physical velocity already constructed by the strong mean inverse.
-/

noncomputable section

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeTranslation EulerMeanTimeContinuousTranslation EulerTimeH1Reconstruction
  EulerTimeLp EulerVolterraConvolution EulerGevrey
open scoped ContDiff

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)

/-- The continuous time path constructed from the actual B and B_t. -/
def continuousVelocity : C(Icc (0 : ℝ) T, L2) :=
  reconstruction T hT (s.velocityField, s.velocityDerivative)

/-- This reconstruction is exactly the physical representative, at every time. -/
theorem continuousVelocity_eq_physicalPath (hTpos : 0 < T)
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    (t : Icc (0 : ℝ) T) : s.continuousVelocity t = s.physicalPath t := by
  have hh := s.physical_h1 hF
  exact reconstruction_eq_path T hTpos s.velocityField s.velocityDerivative s.physicalPath
    hh.1 hh.2.1 hh.2.2 t

/-- The actual continuous velocity inherits spatial regularity uniformly in time. -/
theorem continuousVelocity_translation_contDiff {n : ℕ∞ω}
    (hB : ContDiff ℝ n (fun a : Space => timeTranslation T a s.velocityField))
    (hBt : ContDiff ℝ n (fun a : Space => timeTranslation T a s.velocityDerivative)) :
    ContDiff ℝ n (fun a : Space => pathTranslation T a s.continuousVelocity) :=
  reconstruction_translation_contDiff T hT s.velocityField s.velocityDerivative hB hBt

/-- The actual spatial orbit of B(t) is regular for every t, including both endpoints. -/
theorem physicalPath_translation_contDiff (hTpos : 0 < T)
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    {n : ℕ∞ω}
    (hB : ContDiff ℝ n (fun a : Space => timeTranslation T a s.velocityField))
    (hBt : ContDiff ℝ n (fun a : Space => timeTranslation T a s.velocityDerivative))
    (t : Icc (0 : ℝ) T) :
    ContDiff ℝ n (fun a : Space => translation a (s.physicalPath t)) := by
  have hp := pathTranslation_evaluation_contDiff T s.continuousVelocity
    (s.continuousVelocity_translation_contDiff hB hBt) t
  have heq : (fun a : Space => translation a (s.continuousVelocity t)) =
      fun a : Space => translation a (s.physicalPath t) :=
    funext (fun a => congrArg (translation a) (s.continuousVelocity_eq_physicalPath hTpos hF t))
  exact Eq.mp (congrArg (fun g : Space → L2 => ContDiff ℝ n g) heq) hp

/-- The actual uniform-time velocity has the explicit H¹ trace amplitude. -/
theorem continuousVelocity_translation_gevrey (hTpos : 0 < T)
    (hB : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a s.velocityField))
    (hBt : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a s.velocityDerivative))
    (R C D : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D) (d : ℕ)
    (hBb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeTranslation T b s.velocityField) a‖ ≤
      C*majorant R d n)
    (hBtb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeTranslation T b s.velocityDerivative)
      a‖ ≤ D*majorant R d n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => pathTranslation T b s.continuousVelocity) a‖ ≤
      ((T⁻¹*Real.sqrt T)*C+(2*Real.sqrt T)*D)*majorant R d n :=
  reconstruction_translation_gevrey T hTpos s.velocityField s.velocityDerivative
    hB hBt R C D hR hC hD d hBb hBtb n a

/-- Every actual time slice obeys the same bound, with no extra spatial derivative loss. -/
theorem physicalPath_translation_gevrey (hTpos : 0 < T)
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    (hB : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a s.velocityField))
    (hBt : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a s.velocityDerivative))
    (R C D : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D) (d : ℕ)
    (hBb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeTranslation T b s.velocityField) a‖ ≤
      C*majorant R d n)
    (hBtb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeTranslation T b s.velocityDerivative)
      a‖ ≤ D*majorant R d n)
    (t : Icc (0 : ℝ) T) (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => translation b (s.physicalPath t)) a‖ ≤
      ((T⁻¹*Real.sqrt T)*C+(2*Real.sqrt T)*D)*majorant R d n := by
  have hpath := s.continuousVelocity_translation_contDiff hB hBt
  have hpathb := s.continuousVelocity_translation_gevrey hTpos hB hBt
    R C D hR hC hD d hBb hBtb
  have ht := pathTranslation_evaluation_gevrey T s.continuousVelocity hpath
    R ((T⁻¹*Real.sqrt T)*C+(2*Real.sqrt T)*D) hR (by positivity) d hpathb t n a
  have heq : (fun b : Space => translation b (s.physicalPath t)) =
      fun b : Space => translation b (s.continuousVelocity t) :=
    funext (fun b => congrArg (translation b) (s.continuousVelocity_eq_physicalPath hTpos hF
      t).symm)
  exact (congrArg (fun g : Space → L2 => ‖iteratedFDeriv ℝ n g a‖) heq).trans_le ht

end EulerMeanVariationalInverse.StrongMeanEvolution

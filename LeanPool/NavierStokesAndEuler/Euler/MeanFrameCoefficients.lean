/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanDisplacementRegularity

@[expose] public section

/-!
# Actual coefficient adapters for the mean solenoidal frame

A bounded inverse deformation supplies a strictly positive lower frame bound
on the ordinary infinite-dimensional solenoidal Hilbert space. The actual mean
constraint supplies the range property needed to reconstruct coordinates.
-/

noncomputable section

namespace EulerMeanVariationalInverse

open Set ContinuousLinearMap EulerTimeLp EulerTerminalTimePrimitive EulerMeanSolenoidal

variable (T : ℝ) (hT : 0 ≤ T)
  (FInv F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))

/-- A concrete positive Gram lower-bound constant from the actual inverse path. -/
def meanFrameCoercivity : ℝ := ((‖FInv‖+1)^2)⁻¹

theorem meanFrameCoercivity_pos : 0 < meanFrameCoercivity T FInv := by
  unfold meanFrameCoercivity
  positivity

/-- Bounded left inversion of F gives genuine coercivity of the solenoidal frame. -/
theorem solenoidalFrame_lower
    (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (F t x) = x)
    (t : Icc (0 : ℝ) T) (z : solenoidalSpace) :
    meanFrameCoercivity T FInv * ‖z‖^2 ≤ ‖solenoidalFrame T F t z‖^2 := by
  have hd : 0 < ‖FInv‖+1 := by positivity
  have hn : ‖z‖ ≤ (‖FInv‖+1)*‖solenoidalFrame T F t z‖ := by
    calc
      ‖z‖ = ‖FInv t (F t (z : L2))‖ := by rw [hInv]; rfl
      _ ≤ ‖FInv t‖ * ‖F t (z : L2)‖ := (FInv t).le_opNorm _
      _ ≤ (‖FInv‖+1) * ‖solenoidalFrame T F t z‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact (FInv.norm_coe_le_norm t).trans (by linarith)
  have hs := pow_le_pow_left₀ (norm_nonneg z) hn 2
  calc
    meanFrameCoercivity T FInv * ‖z‖^2 = ‖z‖^2 / (‖FInv‖+1)^2 := by
      simp only [meanFrameCoercivity, div_eq_mul_inv]
      ring
    _ ≤ ‖solenoidalFrame T F t z‖^2 := by
      apply (div_le_iff₀ (sq_pos_of_pos hd)).2
      nlinarith only [hs]

/-- The actual mean constraint and right inversion place every physical
primitive in the range of the solenoidal frame, at every time. -/
theorem meanPrimitive_in_frame_range
    (hRight : ∀ (t : Icc (0 : ℝ) T) (x : L2), F t (FInv t x) = x)
    (u : meanDerivatives T hT FInv) (t : Icc (0 : ℝ) T) :
    ∃ z : solenoidalSpace, solenoidalFrame T F t z = realPrimitive T (u : TimeLp T L2) t := by
  have hz : FInv t (realPrimitive T (u : TimeLp T L2) t) ∈ solenoidalSpace := by
    simpa only [terminalPrimitive_apply] using u.property t
  refine ⟨⟨FInv t (realPrimitive T (u : TimeLp T L2) t), hz⟩, ?_⟩
  exact hRight t _

/-- The genuine deformation ODE descends to its restriction to solenoidal fields. -/
theorem solenoidalFrame_ode
    (F₂ H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (hODE : ∀ t, F₂ t = -(H t).comp (F t)) (t : Icc (0 : ℝ) T) :
    solenoidalFrame T F₂ t = -(H t).comp (solenoidalFrame T F t) := by
  apply ContinuousLinearMap.ext
  intro z
  change F₂ t (z : L2) = -(H t (F t (z : L2)))
  simpa only [neg_apply, comp_apply] using congrArg (fun A : L2 →L[ℝ] L2 => A (z : L2)) (hODE t)

end EulerMeanVariationalInverse

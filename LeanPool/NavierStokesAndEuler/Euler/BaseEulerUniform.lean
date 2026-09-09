/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BaseEulerGevrey
import Mathlib.Algebra.Order.Star.Real

/-! A single factorial budget for every base datum with |β|≤1.
In particular this covers β=x₀⁻² with x₀≥1, independently of the
eventual frequency and iteration scales. -/

@[expose] public section


noncomputable section

namespace EulerBaseDatum

open Set EulerSmoothLimit EulerGevrey EulerLpTranslation EulerPacketPiola
  EulerPacketParentLabelBounds EulerMeanClassicalWordBounds EulerParameterWordGevrey

/-- Uniform amplitude, given by `1+‖curlOperator‖*(3*(3*cutoffAmplitude*(24*2))*256)`. -/
def uniformAmplitude : ℝ := 1+‖curlOperator‖*(3*(3*cutoffAmplitude*(24*2))*256)

theorem uniformAmplitude_pos : 0 < uniformAmplitude := by
  have h := cutoffAmplitude_nonneg
  unfold uniformAmplitude
  positivity

theorem velocityAmplitude_le_uniform (β : ℝ) (hβ : |β| ≤ 1) :
    velocityAmplitude (linear β) ≤ uniformAmplitude := by
  have hL : ‖linear β‖ ≤ 2 := (linear_norm β).trans (by linarith)
  have hc := cutoffAmplitude_nonneg
  calc
    velocityAmplitude (linear β) ≤ ‖curlOperator‖*(3*(3*cutoffAmplitude*(24*2))*256) := by
      unfold velocityAmplitude potentialAmplitude
      gcongr
    _ ≤ uniformAmplitude := by unfold uniformAmplitude; linarith

theorem velocity_uniform_sup (β : ℝ) (hβ : |β| ≤ 1) :
    HasSupBound (velocity (linear β)) uniformAmplitude 1024 :=
  (velocity_sup_bound (linear β)).mono (velocityAmplitude_nonneg _) (by norm_num)
    (velocityAmplitude_le_uniform β hβ) le_rfl

/-- Uniform L² amplitude, given by `uniformAmplitude*volumeFactor`. -/
def uniformL2Amplitude : ℝ := uniformAmplitude*volumeFactor

theorem uniformL2Amplitude_nonneg : 0 ≤ uniformL2Amplitude :=
  mul_nonneg uniformAmplitude_pos.le volumeFactor_nonneg

theorem field_uniform_jet (β : ℝ) (hβ : |β| ≤ 1) :
    (field (linear β)).HasJetBound uniformL2Amplitude 1024 :=
  (field_jet_bound (linear β)).mono
    (mul_nonneg (velocityAmplitude_nonneg _) volumeFactor_nonneg) (by norm_num)
    (mul_le_mul_of_nonneg_right (velocityAmplitude_le_uniform β hβ) volumeFactor_nonneg) le_rfl

/-- Uniform label bound, given by `1+sobolevCoefficientAmplitude (Fin 3) 6 1024
uniformL2Amplitude + sobolevCoefficientRadius (Fin 3) 1024`. -/
def uniformLabelBound : ℝ :=
  1+sobolevCoefficientAmplitude (Fin 3) 6 1024 uniformL2Amplitude +
    sobolevCoefficientRadius (Fin 3) 1024

theorem uniformLabelBound_one : 1 ≤ uniformLabelBound := by
  have ha := sobolevCoefficientAmplitude_nonneg (ι := Fin 3) 6 1024 uniformL2Amplitude
    (by norm_num) uniformL2Amplitude_nonneg
  have hr := sobolevCoefficientRadius_nonneg (ι := Fin 3) 1024 (by norm_num)
  unfold uniformLabelBound
  linarith

theorem field_uniform_label (β : ℝ) (hβ : |β| ≤ 1) :
    HasLabelBound uniformLabelBound (field (linear β)) := by
  have ha := sobolevCoefficientAmplitude_nonneg (ι := Fin 3) 6 1024 uniformL2Amplitude
    (by norm_num) uniformL2Amplitude_nonneg
  have hr := sobolevCoefficientRadius_nonneg (ι := Fin 3) 1024 (by norm_num)
  apply SmoothL2Field.hasLabelBound_of_jet_bound (field (linear β)) uniformL2Amplitude
    1024 uniformLabelBound uniformL2Amplitude_nonneg (by norm_num) (field_uniform_jet β hβ)
  · unfold uniformLabelBound
    linarith
  · unfold uniformLabelBound
    linarith

theorem field_uniform_Hq (β : ℝ) (hβ : |β| ≤ 1) (q n : ℕ) :
    classicalBlockSize direction q (field (linear β)).toLp
      (field (linear β)).translation_contDiff n ≤
        sobolevCoefficientAmplitude (Fin 3) q 1024 uniformL2Amplitude *
          (sobolevCoefficientRadius (Fin 3) 1024)^n*(n.factorial : ℝ)^2 :=
  SmoothL2Field.classicalBlockSize_of_jet_bound direction (by intro i; simp [direction]) q
    (field (linear β)) uniformL2Amplitude 1024 uniformL2Amplitude_nonneg (by norm_num)
    (field_uniform_jet β hβ) n

theorem beta_bound (x₀ : ℝ) (hx : 1 ≤ x₀) : |(x₀^2)⁻¹| ≤ 1 := by
  have hpow : (1 : ℝ) ≤ x₀^2 := one_le_pow₀ hx
  rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg x₀))]
  exact inv_le_one_of_one_le₀ hpow

theorem initial_gradient (x₀ : ℝ) :
    fderiv ℝ (field (linear ((x₀^2)⁻¹))).field 0=linear ((x₀^2)⁻¹) :=
  velocity_fderiv_plateau _ (linear_trace _) 0 (by simp)

end EulerBaseDatum

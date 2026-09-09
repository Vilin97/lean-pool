/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketParentLabelBounds
public import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalWordBounds
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import Mathlib.Algebra.Order.Star.Real

/-! The physical-label estimate (21) supplies the multiplier inputs in (H1).
The displacement, velocity and acceleration are the actual L² fields.  The
identity part of the deformation is never asserted to lie in L². -/

@[expose] public section


noncomputable section

namespace EulerPacketParentLabelBounds

open MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanSmoothRepresentative EulerMeanClassicalWordBounds EulerParameterWordGevrey
  EulerGevrey EulerOperatorGevreyCalculus
open scoped ContDiff

/-- Coefficient radius, given by `max 1024 (4*K)`. -/
def coefficientRadius (K : ℝ) : ℝ := max 1024 (4*K)
/-- Gradient amplitude, given by `embeddingCost*K^2`. -/
def gradientAmplitude (K : ℝ) : ℝ := embeddingCost*K^2
/-- Frame amplitude, given by `1+gradientAmplitude K`. -/
def frameAmplitude (K : ℝ) : ℝ := 1+gradientAmplitude K

theorem coefficientRadius_lower (K : ℝ) : 1024 ≤ coefficientRadius K := le_max_left _ _
theorem coefficientRadius_nonneg (K : ℝ) : 0 ≤ coefficientRadius K :=
  (by norm_num : (0 : ℝ) ≤ 1024).trans (coefficientRadius_lower K)
theorem gradientAmplitude_nonneg (K : ℝ) : 0 ≤ gradientAmplitude K :=
  mul_nonneg embeddingCost_nonneg (sq_nonneg K)
theorem frameAmplitude_nonneg (K : ℝ) : 0 ≤ frameAmplitude K :=
  add_nonneg zero_le_one (gradientAmplitude_nonneg K)

/-- An actual scalar label scaling with 0≤ℓ≤1 is a linear contraction. -/
theorem labelScaling_norm_le (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) :
    ‖ℓ • ContinuousLinearMap.id ℝ Space‖ ≤ 1 := by
  rw [norm_smul,Real.norm_of_nonneg hℓ]
  exact (mul_le_mul_of_nonneg_left norm_id_le hℓ).trans (by simpa only [mul_one] using hℓ1)

theorem source_block_bound (u : L2) (hu : SmoothOrbit u) (K : ℝ)
    (hb : ∀ n, classicalBlockSize direction 6 u hu n ≤ K ^ (n + 1) * (n.factorial : ℝ) ^ 2)
    (n : ℕ) : block direction 6 (fun a : Space => translation a u) n 0 ≤ K*majorant K 0 n := by
  have h := hb n
  rw [classicalBlockSize_eq] at h
  convert h using 1
  simp only [majorant,Nat.add_zero,pow_succ]
  ring

/-- A velocity or acceleration in the literal physical-label H⁶ word norm
gives its actual spatial Jacobian at one polynomial coefficient radius. -/
theorem source_gradient_bound (u : L2) (hu : SmoothOrbit u)
    (f : Space → Space) (hf : ContDiff ℝ ∞ f) (hrep : (u : Space → Space) =ᵐ[volume] f)
    (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ n, classicalBlockSize direction 6 u hu n ≤ K ^ (n + 1) * (n.factorial : ℝ) ^ 2)
    (L : Space →L[ℝ] Space) (hL : ‖L‖ ≤ 1) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ f (L y)) x‖ ≤
      gradientAmplitude K*majorant (coefficientRadius K) 0 n := by
  have h := gradient_scaled_gevrey u hu f hf hrep 6 (by omega) K K hK hK
    (source_block_bound u hu K hb) L hL n x
  have hr := majorant_radius_mono (4*K) (coefficientRadius K) (by positivity) (le_max_right _ _) 0 n
  have he : embeddingCost*K*K = gradientAmplitude K := by unfold gradientAmplitude; ring
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left hr (gradientAmplitude_nonneg K))

/-- The parent displacement bound gives the full deformation, including
its constant identity, without making the identity an L² datum. -/
theorem source_deformation_bound (u : L2) (hu : SmoothOrbit u)
    (f : Space → Space) (hf : ContDiff ℝ ∞ f) (hrep : (u : Space → Space) =ᵐ[volume] f)
    (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ n, classicalBlockSize direction 6 u hu n ≤ K ^ (n + 1) * (n.factorial : ℝ) ^ 2)
    (L : Space →L[ℝ] Space) (hL : ‖L‖ ≤ 1) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (fun y => ContinuousLinearMap.id ℝ Space+fderiv ℝ f (L y)) x‖ ≤
      frameAmplitude K*majorant (coefficientRadius K) 0 n := by
  have h := deformation_scaled_gevrey u hu f hf hrep 6 (by omega) K K hK hK
    (source_block_bound u hu K hb) L hL n x
  have hr := majorant_radius_mono (4*K) (coefficientRadius K) (by positivity) (le_max_right _ _) 0 n
  have he : 1+embeddingCost*K*K = frameAmplitude K := by
      unfold frameAmplitude gradientAmplitude; ring
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left hr (frameAmplitude_nonneg K))

end EulerPacketParentLabelBounds

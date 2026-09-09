/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryData

@[expose] public section

/-! Exact scale normalization from the actual parent frame and shear.
The physical interval ends at the chosen scaled horizon; no extension
beyond the source time interval is required. -/

noncomputable section

namespace EulerPacketMovingFrame

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerPacketNormalizedPrimary EulerPacketCrossProduct

theorem activation_coupling_match (B : ℝ → Space →L[ℝ] Space)
    (m v : ℝ → Space) (t₀ ε : ℝ) :
    let a := normalizedCoupling (B t₀) (m t₀) (v t₀)
    rescaledFrame B m v t₀ a ε 0 0 1 = a := by
  simp [rescaledFrame,physicalTime,frameMatrix,frame,normalizedCoupling]

theorem activation_tilt_match (B : ℝ → Space →L[ℝ] Space)
    (m v : ℝ → Space) (t₀ ε : ℝ)
    (ha : normalizedCoupling (B t₀) (m t₀) (v t₀) ≠ 0)
    (hβ : 0 ≤ normalizedTilt (B t₀) (m t₀) (v t₀)) :
    let a := normalizedCoupling (B t₀) (m t₀) (v t₀)
    let σ := Real.sqrt (normalizedTilt (B t₀) (m t₀) (v t₀))
    rescaledFrame B m v t₀ a ε 0 2 1 = a*σ^2 := by
  dsimp only
  rw [Real.sq_sqrt hβ]
  simp only [rescaledFrame,physicalTime,mul_zero,add_zero,frameMatrix,frame,
    Matrix.cons_val_two,Matrix.cons_val_one,Matrix.cons_val_zero,normalizedTilt]
  exact (mul_div_cancel₀ _ ha).symm

theorem activation_shear_match (c : ℝ) (m v : ℝ → Space) (t₀ a : ℝ)
    (ha : 0 < a) (hh : 0 < primaryShear c m v t₀) :
    let ε := Real.sqrt (a/primaryShear c m v t₀)
    0 < ε ∧ rescaledShear c m v t₀ a ε 0 = a/ε^2 := by
  dsimp only
  have hratio := div_pos ha hh
  refine ⟨Real.sqrt_pos.mpr hratio,?_⟩
  rw [Real.sq_sqrt hratio.le]
  simp only [rescaledShear,physicalTime,mul_zero,add_zero]
  field_simp

theorem activation_horizon_exact (t₀ T a ε : ℝ) (ha : a ≠ 0) (hε : ε ≠ 0) :
    physicalTime t₀ a ε (a*(T-t₀)/ε) = T := by
  unfold physicalTime
  field_simp
  ring

theorem activation_horizon_maps (t₀ T a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    MapsTo (physicalTime t₀ a ε) (Icc 0 (a*(T-t₀)/ε)) (Icc t₀ T) := by
  intro s hs
  constructor
  · change t₀ ≤ t₀+(ε/a)*s
    exact le_add_of_nonneg_right (mul_nonneg (div_nonneg hε.le ha.le) hs.1)
  · calc
      physicalTime t₀ a ε s ≤ physicalTime t₀ a ε (a*(T-t₀)/ε) := by
        unfold physicalTime
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hs.2 (div_nonneg hε.le ha.le))
      _ = T := activation_horizon_exact t₀ T a ε ha.ne' hε.ne'

end EulerPacketMovingFrame

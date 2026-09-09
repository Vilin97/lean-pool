/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketLabelData
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldRestriction

/-! Restricting the actual parent to a nested horizon preserves its
flow identities, physical-label budget and the source low-order guards. -/

@[expose] public section


noncomputable section

namespace EulerParentPacketFrames

open Set ContinuousLinearMap EulerTimeIntervalRestriction EulerSmoothLimit
  EulerMeanBoundary EulerMeanHarmonic

namespace Parent

variable (G : Parent) (S : ℝ) (hS : 0 < S) (hST : S ≤ G.T)

/-- Restrict time, bundling `T`, `T_pos`, `ell`, `ell_pos` and the required compatibility
proofs. -/
def restrictTime : Parent where
  T := S
  T_pos := hS
  ell := G.ell
  ell_pos := G.ell_pos
  ell_le_one := G.ell_le_one
  displacement := G.displacement.compTime (initialInclusion G.T S hST)
  velocity := G.velocity.compTime (initialInclusion G.T S hST)
  acceleration := G.acceleration.compTime (initialInclusion G.T S hST)
  displacement_time := SmoothTimeField.TimeDerivative.restrictInitial hS.le hST G.displacement_time
  velocity_time := SmoothTimeField.TimeDerivative.restrictInitial hS.le hST G.velocity_time
  initial := G.initial
  determinant t x := G.determinant (initialInclusion G.T S hST t) x

theorem restrictTime_frame (t : Icc (0 : ℝ) S) (x : Space) :
    (G.restrictTime S hS hST).frame.field t x=G.frame.field (initialInclusion G.T S hST t) x := by
  erw [frame_apply]

theorem restrictTime_first (t : Icc (0 : ℝ) S) (x : Space) :
    (G.restrictTime S hS hST).first.field t x=G.first.field (initialInclusion G.T S hST t) x := by
  erw [first_apply]

theorem restrictTime_second (t : Icc (0 : ℝ) S) (x : Space) :
    (G.restrictTime S hS hST).second.field t x=G.second.field (initialInclusion G.T S hST t) x := by
  erw [second_apply]

theorem restrictTime_inverse (t : Icc (0 : ℝ) S) (x : Space) :
    (G.restrictTime S hS hST).inverse.field t x=G.inverse.field (initialInclusion G.T S hST t) x :=
        by
  erw [inverse_apply]

theorem restrictTime_strain (t : Icc (0 : ℝ) S) (x : Space) :
    (G.restrictTime S hS hST).strain.field t x=G.strain.field (initialInclusion G.T S hST t) x := by
  erw [strain_apply]

theorem restrictTime_curvature (t : Icc (0 : ℝ) S) (x : Space) :
    (G.restrictTime S hS hST).curvature.field t x=G.curvature.field (initialInclusion G.T S hST t)
        x := by
  erw [curvature_apply]

theorem restrictTime_initialStrain (x : Space) :
    (G.restrictTime S hS hST).initialStrain.field x=G.initialStrain.field x := by
  erw [initialStrain_apply,initialStrain_apply,G.restrictTime_first]

end Parent

namespace LabelData

variable {G : Parent} (L : LabelData G) (S : ℝ) (hS : 0 < S) (hST : S ≤ G.T)

/-- Restrict time, bundling `K`, `K_one`, `displacement`, `velocity` and the required
compatibility proofs. -/
def restrictTime : LabelData (G.restrictTime S hS hST) where
  K := L.K
  K_one := L.K_one
  displacement t := L.displacement (initialInclusion G.T S hST t)
  velocity t := L.velocity (initialInclusion G.T S hST t)
  acceleration t := L.acceleration (initialInclusion G.T S hST t)
  displacement_match t x := L.displacement_match (initialInclusion G.T S hST t) x
  velocity_match t x := L.velocity_match (initialInclusion G.T S hST t) x
  acceleration_match t x := L.acceleration_match (initialInclusion G.T S hST t) x
  displacement_bound t := L.displacement_bound (initialInclusion G.T S hST t)
  velocity_bound t := L.velocity_bound (initialInclusion G.T S hST t)
  acceleration_bound t := L.acceleration_bound (initialInclusion G.T S hST t)

end LabelData

namespace LowBounds

variable {G : Parent} (H : LowBounds G) (S : ℝ) (hS : 0 < S) (hST : S ≤ G.T)

/-- Restrict time, bundling `Be`, `Bc`, `L`, `r` and the required compatibility proofs. -/
def restrictTime : LowBounds (G.restrictTime S hS hST) where
  Be := H.Be
  Bc := H.Bc
  L := H.L
  r := H.r
  K := H.K
  Be_nonneg := H.Be_nonneg
  Bc_nonneg := H.Bc_nonneg
  L_lower := H.L_lower
  r_nonneg := H.r_nonneg
  r_le_quarter := H.r_le_quarter
  K_nonneg := H.K_nonneg
  exterior_lower x hx v := by
    rw [G.restrictTime_initialStrain]
    exact H.exterior_lower x hx v
  core_lower x hx v := by
    rw [G.restrictTime_initialStrain]
    exact H.core_lower x hx v
  curvature_upper t x v := by
    erw [G.restrictTime_curvature]
    exact H.curvature_upper (initialInclusion G.T S hST t) x v
  small := by
    apply le_trans ?_ H.small
    change H.K*(S^2/2)+H.Be*S+boundaryLocalizationC2*H.Bc*H.r^3*S ≤ _
    have h1 := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ hS.le hST 2) (by
          norm_num : (0 : ℝ) ≤ 2)) H.K_nonneg
    have h2 := mul_le_mul_of_nonneg_left hST H.Be_nonneg
    have h3 := mul_le_mul_of_nonneg_left hST
      (mul_nonneg (mul_nonneg boundaryLocalizationC2_nonneg H.Bc_nonneg) (pow_nonneg H.r_nonneg 3))
    exact add_le_add (add_le_add h1 h2) h3

end LowBounds
end EulerParentPacketFrames

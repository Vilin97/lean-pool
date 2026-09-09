/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BasePacketSetup
public import LeanPool.NavierStokesAndEuler.Euler.ParentHomogeneousPacketLowBounds

@[expose] public section

/-! The first packet's size and sign hypotheses are proved for the
concrete base solution on its actual restricted horizon. -/

noncomputable section

namespace EulerBaseDatum

open Set InnerProductSpace EulerSmoothLimit EulerParentPacketFrames
  EulerBaseEulerGuards EulerPacketSupport EulerPacketFirstLowBounds

variable (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
  (T : ℝ) (hT : 0 < T) (hTB : T ≤ initialTime)

def firstPacketData : EulerTransversePacketProvider.Data FirstPlane :=
  (packetBaseParent β hβ ell hell hell1 T hT hTB).transverseData
    firstNormal firstNormal_unit firstFrame support compact

theorem firstPacket_primary_size (t : Icc (0 : ℝ) T) (x : Space) :
    ‖(firstPacketData β hβ ell hell hell1 T hT hTB).normal.field t x‖*
      ‖EulerPacketForwardFactorization.canonicalVelocity
        (firstPacketData β hβ ell hell hell1 T hT hTB) firstCoordinate t x‖ ≤ firstRatio := by
  apply primary_size_le (firstPacketData β hβ ell hell hell1 T hT hTB)
    initialCoefficientCost initialCoefficientCost_nonneg x
    (fun s => packetBase_strain_bound β hβ ell hell hell1 T hT hTB s x)
    (packetBase_short T hTB) firstCoordinate
  · change ‖((packetBaseParent β hβ ell hell hell1 T hT hTB).transverseData
      firstNormal firstNormal_unit firstFrame support compact).normal.field
        (packetBaseParent β hβ ell hell hell1 T hT hTB).zeroTime x‖=1
    rw [source_normal_initial]
    exact firstNormal_unit
  · change ‖((packetBaseParent β hβ ell hell hell1 T hT hTB).transverseData
      firstNormal firstNormal_unit firstFrame support compact).frame.field
        (packetBaseParent β hβ ell hell hell1 T hT hTB).zeroTime x firstCoordinate‖=1
    rw [source_frame_initial,firstCoordinate_map]
    simp

theorem firstPacket_primary_flux (t : Icc (0 : ℝ) T) (x : Space) :
    0 ≤ ⟪(firstPacketData β hβ ell hell hell1 T hT hTB).normal.field t x,
      (firstPacketData β hβ ell hell hell1 T hT hTB).M.field t x
        (EulerPacketForwardFactorization.canonicalVelocity
          (firstPacketData β hβ ell hell hell1 T hT hTB) firstCoordinate t x)⟫_ℝ := by
  apply primary_flux_nonneg (firstPacketData β hβ ell hell hell1 T hT hTB) x firstCoordinate t
  intro hx
  exact (by norm_num : (0 : ℝ) ≤ 1/2).trans
    (firstPacket_pressure_numerator β hβ ell hell hell1 T hT hTB t x hx)

theorem packetBase_physical_strain (t : Icc (0 : ℝ) T) (x : Space) :
    ‖fderiv ℝ (fun y => (packetBaseState β hβ ell hell hell1 T hT hTB).evolution.velocity (t,y)) x‖
      ≤
      initialCoefficientCost := by
  rw [← (packetBaseState β hβ ell hell hell1 T hT hTB).evolution.strain_at_normalized_inverse t x]
  exact packetBase_strain_bound β hβ ell hell hell1 T hT hTB t _

theorem packetBase_physical_force (t : Icc (0 : ℝ) T) (x : Space) :
    ‖fderiv ℝ ((packetBaseState β hβ ell hell hell1 T hT hTB).evolution.force t) x‖ ≤
      initialCoefficientCost := by
  let E := (packetBaseState β hβ ell hell hell1 T hT hTB).evolution
  have h := packetBase_curvature_bound β hβ ell hell hell1 T hT hTB t
    (ell⁻¹ • E.inverse.field t x)
  erw [E.curvature_eq] at h
  change ‖fderiv ℝ (E.force t)
    ((packetBaseParent β hβ ell hell hell1 T hT hTB).position t (ell • (ell⁻¹ • E.inverse.field t
      x)))‖ ≤ _ at h
  simp only [smul_smul,mul_inv_cancel₀ hell.ne',one_smul] at h
  erw [E.inverse.right_inverse] at h
  exact h

end EulerBaseDatum

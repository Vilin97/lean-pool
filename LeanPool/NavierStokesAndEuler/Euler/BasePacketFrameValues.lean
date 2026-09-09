/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BasePacketSetup
public import LeanPool.NavierStokesAndEuler.Euler.ParentStateGeometry
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerLowBounds

@[expose] public section

/-! Exact initial frame parameters for the first normal stage: its
coupling is one, tilt is beta, and shear is the prescribed first shear. -/

noncomputable section

namespace EulerBaseDatum

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerParentPacketFrames
  EulerPacketSupport EulerBaseEulerGuards EulerPacketMovingFrame EulerPacketNormalizedPrimary
  EulerPacketCrossProduct EulerPacketSourceGeometry EulerVolterraConvolution

theorem first_basis_cross : cross firstNormal (EuclideanSpace.single 1 1)=EuclideanSpace.single 2 1
  := by
  ext i
  fin_cases i <;> simp [cross,firstNormal,cross_apply]

theorem first_normalizedCoupling (β : ℝ) :
    normalizedCoupling (linear β) firstNormal (EuclideanSpace.single 1 1)=1 := by
  simp [normalizedCoupling,unit,firstNormal,EuclideanSpace.inner_single_left,
    PiLp.add_apply,PiLp.smul_apply]

theorem first_normalizedTilt (β : ℝ) :
    normalizedTilt (linear β) firstNormal (EuclideanSpace.single 1 1)=β := by
  rw [normalizedTilt,first_normalizedCoupling]
  have hp : unit firstNormal=firstNormal := by rw [unit,firstNormal_unit,inv_one,one_smul]
  have hq : unit (EuclideanSpace.single 1 1 : Space)=EuclideanSpace.single 1 1 := by simp [unit]
  rw [hp,hq,first_basis_cross,linear_q]
  simp [EuclideanSpace.inner_single_left,PiLp.add_apply,PiLp.smul_apply]

variable (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
  (T : ℝ) (hT : 0 < T) (hTB : T ≤ initialTime)

theorem packetBase_centerStrain_initial :
    (packetBaseParent β hβ ell hell hell1 T hT hTB).centerStrain 0=linear β := by
  let A := packetBaseParent β hβ ell hell hell1 T hT hTB
  let S := packetBaseState β hβ ell hell hell1 T hT hTB
  change A.centerStrain 0=linear β
  have h0 : (0 : Space) ∈ support := subset_tsupport _ (by
    simp [Function.mem_support,EulerSpatialCutoffs.innerCutoff_zero])
  calc
    _ = A.strain.field A.zeroTime 0 := by
      change A.strain.field (projIcc 0 A.T A.T_pos.le 0) 0=A.strain.field A.zeroTime 0
      rw [projIcc_of_mem A.T_pos.le (show (0 : ℝ) ∈ Icc 0 A.T from ⟨le_rfl,A.T_pos.le⟩)]
      rfl
    _ = A.initialStrain.field 0 := by
      rw [S.evolution.strain_origin S.odd,S.evolution.initialStrain_eq,smul_zero]
      rfl
    _ = linear β := packetBase_initialStrain β hβ ell hell hell1 T hT hTB 0 h0

theorem packetBase_sourceNormal_initial :
    (packetBaseParent β hβ ell hell hell1 T hT hTB).sourceNormal firstNormal 0=firstNormal := by
  let A := packetBaseParent β hβ ell hell hell1 T hT hTB
  calc
    _ = (A.transverseData firstNormal firstNormal_unit firstFrame support compact).normal.field
        A.zeroTime 0 := (A.source_normal_eq firstNormal firstNormal_unit firstFrame support compact
          A.zeroTime).symm
    _ = _ := source_normal_initial firstNormal firstNormal_unit firstFrame support compact 0

theorem packetBase_sourceVelocity_initial :
    (packetBaseParent β hβ ell hell hell1 T hT hTB).sourceVelocity
      firstNormal firstNormal_unit firstFrame support compact firstCoordinate
        0=EuclideanSpace.single 1 1 := by
  change EulerPacketForwardFactorization.uncutVelocity
    ((packetBaseParent β hβ ell hell hell1 T hT hTB).transverseData
      firstNormal firstNormal_unit firstFrame support compact) firstCoordinate 0 0=_
  rw [EulerPacketForwardFactorization.uncutVelocity_initial]
  exact (source_frame_initial (G := packetBaseParent β hβ ell hell hell1 T hT hTB)
    firstNormal firstNormal_unit firstFrame support compact firstCoordinate 0).trans
      firstCoordinate_map

theorem first_frame_parameters {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    {D : EulerTransversePacketProvider.Data U} (P : ParentFrame D 0) (hchild : ℝ)
    (hB : P.B 0=(packetBaseParent β hβ ell hell hell1 T hT hTB).centerStrain 0)
    (hm : P.m 0=(packetBaseParent β hβ ell hell hell1 T hT hTB).sourceNormal firstNormal 0)
    (hv : P.v 0=(packetBaseParent β hβ ell hell hell1 T hT hTB).sourceVelocity
      firstNormal firstNormal_unit firstFrame support compact firstCoordinate 0)
    (hc : P.c=hchild) : P.a=1 ∧ P.sigma=Real.sqrt β ∧ P.shear=hchild := by
  have hB' := hB.trans (packetBase_centerStrain_initial β hβ ell hell hell1 T hT hTB)
  have hm' := hm.trans (packetBase_sourceNormal_initial β hβ ell hell hell1 T hT hTB)
  have hv' := hv.trans (packetBase_sourceVelocity_initial β hβ ell hell hell1 T hT hTB)
  refine ⟨?_,?_,?_⟩
  · rw [ParentFrame.a,hB',hm',hv',first_normalizedCoupling]
  · rw [ParentFrame.sigma,hB',hm',hv',first_normalizedTilt]
  · rw [ParentFrame.shear,primaryShear,hc,hm',hv',firstNormal_unit]
    simp

end EulerBaseDatum

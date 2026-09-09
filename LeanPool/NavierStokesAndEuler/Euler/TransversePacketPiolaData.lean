/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketConstructedPiola
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketData

/-! The given inverse deformation defines the exact equivalences used by the Piola packet
construction. -/

@[expose] public section


noncomputable section

namespace EulerTransversePacketProvider.Data

open Set EulerSmoothLimit
  EulerLiftedGradientSpace EulerPacketConstructedPiola

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : Data U)

/-- Deformation equiv, given by `ContinuousLinearEquiv.equivOfInverse (D.F.field t x)
(D.FInv.field t x) (D.inverse_left t x) (D.inverse_right t x)`. -/
def deformationEquiv (t : Icc (0 : ℝ) D.T) (x : Space) : Space ≃L[ℝ] Space :=
  ContinuousLinearEquiv.equivOfInverse (D.F.field t x) (D.FInv.field t x)
    (D.inverse_left t x) (D.inverse_right t x)

@[simp] theorem deformationEquiv_coe (t : Icc (0 : ℝ) D.T) (x : Space) :
    (D.deformationEquiv t x).toContinuousLinearMap = D.F.field t x := rfl

@[simp] theorem deformationEquiv_symm_coe (t : Icc (0 : ℝ) D.T) (x : Space) :
    (D.deformationEquiv t x).symm.toContinuousLinearMap = D.FInv.field t x := rfl

@[simp] theorem deformationEquiv_normal (t : Icc (0 : ℝ) D.T) :
    EulerPacketConstructedPiola.normal (D.deformationEquiv t) D.m₀ = D.normal.field t := rfl

theorem initialNormal_ne_zero : D.m₀ ≠ 0 := by
  intro h
  have hn := D.m₀_unit
  rw [h,norm_zero] at hn
  exact zero_ne_one hn

end EulerTransversePacketProvider.Data

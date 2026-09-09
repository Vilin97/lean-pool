/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketSourceData
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceGeometryData
public import LeanPool.NavierStokesAndEuler.Euler.PacketActivationSourceData

/-! Changing the source normal and reference plane leaves the older
physical frame and its scalar parameters unchanged. The source strain
and time interval are the actual fields of the same parent. -/

@[expose] public section


noncomputable section

namespace EulerPacketSourceGeometry.ParentFrame

open Set EulerSmoothLimit EulerParentPacketFrames EulerTransversePacketProvider
  EulerTransverseFrameCoordinates

variable {A : Parent} {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {m : Space} {hm : ‖m‖ = 1} {R : U ≃ₗᵢ[ℝ] referencePlane m}
  {S : Set Space} {hS : IsCompact S} {τ : ℝ}
  (P : ParentFrame (A.transverseData m hm R S hS) τ)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (m' : Space) (hm' : ‖m'‖ = 1) (R' : V ≃ₗᵢ[ℝ] referencePlane m')

/-- Reframe, bundling `B`, `B₁`, `m`, `v` and the required compatibility proofs. -/
def reframe : ParentFrame (A.transverseData m' hm' R' S hS) τ where
  B := P.B
  B₁ := P.B₁
  m := P.m
  v := P.v
  c := P.c
  G := P.G
  error := P.error
  G_lower := P.G_lower
  error_nonneg := P.error_nonneg
  B_derivative := P.B_derivative
  ray_equation := P.ray_equation
  velocity_equation := P.velocity_equation
  ray_nonzero := P.ray_nonzero
  velocity_nonzero := P.velocity_nonzero
  tangent := P.tangent
  B_bound := P.B_bound
  B₁_bound := P.B₁_bound
  remainder_bound := P.remainder_bound

@[simp] theorem reframe_B : (P.reframe m' hm' R').B=P.B := rfl
@[simp] theorem reframe_B₁ : (P.reframe m' hm' R').B₁=P.B₁ := rfl
@[simp] theorem reframe_m : (P.reframe m' hm' R').m=P.m := rfl
@[simp] theorem reframe_v : (P.reframe m' hm' R').v=P.v := rfl
@[simp] theorem reframe_c : (P.reframe m' hm' R').c=P.c := rfl
@[simp] theorem reframe_G : (P.reframe m' hm' R').G=P.G := rfl
@[simp] theorem reframe_error : (P.reframe m' hm' R').error=P.error := rfl
@[simp] theorem reframe_a : (P.reframe m' hm' R').a=P.a := rfl
@[simp] theorem reframe_sigma : (P.reframe m' hm' R').sigma=P.sigma := rfl
@[simp] theorem reframe_shear : (P.reframe m' hm' R').shear=P.shear := rfl
@[simp] theorem reframe_epsilon : (P.reframe m' hm' R').epsilon=P.epsilon := rfl
@[simp] theorem reframe_horizon : (P.reframe m' hm' R').horizon=P.horizon := rfl

@[simp] theorem reframe_rayScale (hτ : 0 < τ) (hτT : τ < A.T) :
    (P.reframe m' hm' R').rayScale hτ hτT=P.rayScale hτ hτT := rfl

@[simp] theorem reframe_terminalBound (CM CH : ℝ) :
    (P.reframe m' hm' R').terminalBound CM CH=P.terminalBound CM CH := rfl

end EulerPacketSourceGeometry.ParentFrame

namespace EulerParentPacketFrames.Parent

open Set EulerSmoothLimit EulerTransversePacketProvider EulerTransverseFrameCoordinates

variable (A : Parent) {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (S : Set Space) (hS : IsCompact S)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (m' : Space) (hm' : ‖m'‖ = 1) (R' : V ≃ₗᵢ[ℝ] referencePlane m')

theorem transverse_deformation_reframe (t : Icc (0 : ℝ) A.T) (x : Space) :
    (A.transverseData m' hm' R' S hS).deformationEquiv t x =
      (A.transverseData m hm R S hS).deformationEquiv t x := rfl

theorem transverse_reframe :
    (A.transverseData m hm R S hS).reframe m' hm' =
      A.transverseData m' hm' (LinearIsometryEquiv.refl ℝ (referencePlane m')) S hS := rfl

end EulerParentPacketFrames.Parent

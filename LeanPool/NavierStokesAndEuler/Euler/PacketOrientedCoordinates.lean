/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketMovingVelocity

@[expose] public section

/-! Oriented cross products in the actual normalized primary frame. -/

noncomputable section


namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketCrossProduct InnerProductSpace ContinuousLinearMap WithLp

def frameCoordinates (p q x : Space) (i : Fin 3) : ℝ := ⟪frame p q i,x⟫_ℝ

def frameVector (p q : Space) (X : Fin 3 → ℝ) : Space :=
  X 0 • p+X 1 • q+X 2 • cross p q

theorem frameVector_coordinates (p q x : Space)
    (hp : ⟪p,p⟫_ℝ = 1) (hq : ⟪q,q⟫_ℝ = 1) (hpq : ⟪p,q⟫_ℝ = 0) :
    frameVector p q (frameCoordinates p q x) = x := by
  have h := (frameBasis p q hp hq hpq).sum_repr' x
  simp only [frameBasis_apply, Fin.sum_univ_three] at h
  dsimp [frame] at h
  exact h

theorem cross_add_left (x y z : Space) : cross (x+y) z = cross x z+cross y z := by
  change crossBilinear (x+y) z = crossBilinear x z+crossBilinear y z
  simp only [map_add, add_apply]

theorem cross_add_right (x y z : Space) : cross x (y+z) = cross x y+cross x z := by
  exact (crossBilinear x).map_add y z

theorem cross_smul_left (a : ℝ) (x y : Space) : cross (a • x) y = a • cross x y := by
  change crossBilinear (a • x) y = a • crossBilinear x y
  simp only [map_smul, smul_apply]

theorem cross_smul_right (a : ℝ) (x y : Space) : cross x (a • y) = a • cross x y := by
  exact (crossBilinear x).map_smul a y

theorem cross_same (x : Space) : cross x x = 0 := by
  simp only [cross, _root_.cross_self, toLp_zero]

theorem cross_swap (x y : Space) : cross y x = -cross x y := by
  simp only [cross, ← _root_.cross_anticomm (ofLp x) (ofLp y), toLp_neg]

theorem cross_frameVector (p q : Space) (X Y : Fin 3 → ℝ)
    (hp : ⟪p,p⟫_ℝ = 1) (hq : ⟪q,q⟫_ℝ = 1) (hpq : ⟪p,q⟫_ℝ = 0) :
    cross (frameVector p q X) (frameVector p q Y) = frameVector p q (_root_.crossProduct X Y) := by
  have hp2 : ‖p‖^2 = 1 := by simpa only [real_inner_self_eq_norm_sq] using hp
  have hq2 : ‖q‖^2 = 1 := by simpa only [real_inner_self_eq_norm_sq] using hq
  have hqp : ⟪q,p⟫_ℝ = 0 := (real_inner_comm _ _).trans hpq
  have hpn : cross p (cross p q) = -q := by rw [EulerPacketCrossProduct.cross_cross, hpq, hp2,
    zero_smul, one_smul, zero_sub]
  have hqn : cross q (cross p q) = p := by
    rw [cross_swap q p]
    change (crossBilinear q) (-(cross q p)) = p
    rw [map_neg]
    change -(cross q (cross q p)) = p
    rw [EulerPacketCrossProduct.cross_cross, hqp, hq2, zero_smul, one_smul, zero_sub, neg_neg]
  have hnp : cross (cross p q) p = q := by rw [cross_swap p (cross p q), hpn, neg_neg]
  have hnq : cross (cross p q) q = -p := by rw [cross_swap q (cross p q), hqn]
  simp [frameVector, _root_.cross_apply, cross_add_left, cross_add_right, cross_smul_left,
    cross_smul_right,
    cross_same, hpn, hqn, hnp, hnq, cross_swap p q]
  module

theorem frameVector_inner (p q z : Space) (X : Fin 3 → ℝ) :
    ⟪frameVector p q X,z⟫_ℝ =
      X 0*frameCoordinates p q z 0+X 1*frameCoordinates p q z 1+X 2*frameCoordinates p q z 2 := by
  dsimp [frameVector, frameCoordinates, frame]
  simp only [inner_add_left, real_inner_smul_left]

/-- Cross-product and orientation errors cannot be hidden in a coordinate
model: the triple product equals the actual oriented-frame expression. -/
theorem cross_inner_coordinates (p q x y z : Space)
    (hp : ⟪p,p⟫_ℝ = 1) (hq : ⟪q,q⟫_ℝ = 1) (hpq : ⟪p,q⟫_ℝ = 0) :
    ⟪cross x y,z⟫_ℝ =
      (_root_.crossProduct (frameCoordinates p q x) (frameCoordinates p q y)) 0*frameCoordinates p
        q z 0+
      (_root_.crossProduct (frameCoordinates p q x) (frameCoordinates p q y)) 1*frameCoordinates p
        q z 1+
      (_root_.crossProduct (frameCoordinates p q x) (frameCoordinates p q y)) 2*frameCoordinates p
        q z 2 := by
  calc
    _ = ⟪cross (frameVector p q (frameCoordinates p q x))
        (frameVector p q (frameCoordinates p q y)),z⟫_ℝ := by
      rw [frameVector_coordinates p q x hp hq hpq, frameVector_coordinates p q y hp hq hpq]
    _ = _ := by rw [cross_frameVector p q _ _ hp hq hpq, frameVector_inner]

end EulerPacketMovingFrame

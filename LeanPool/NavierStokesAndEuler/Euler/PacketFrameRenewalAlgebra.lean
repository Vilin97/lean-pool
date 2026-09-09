/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledVelocityAlgebra
public import Mathlib.LinearAlgebra.CrossProduct

@[expose] public section

/-! Exact scaled cross and pressure algebra used by physical frame renewal. -/

noncomputable section


namespace EulerPacketMovingFrame

open EulerPacketRay EulerPacketFrameStability

theorem velocityNumerator_homogeneous (A : Fin 3 → Fin 3 → ℝ)
    (P Q N U V W : ℝ) (hV : V ≠ 0) :
    velocityNumerator A P Q N U V W =
      V*velocityNumerator A P Q N (U/V) 1 (W/V) := by
  unfold velocityNumerator
  field_simp

theorem scaling_cross_flux {a : ℝ} (ha : a ≠ 0) (s₀ ε : ℝ)
    (M : Fin 3 → Fin 3 → ℝ) (R V : Fin 3 → ℝ) (hV : V 1 ≠ 0) :
    (∑ i : Fin 3,
      (_root_.crossProduct (fun j => s₀*rayScale ε j*R j) (fun j => velocityScale ε j*V j)) i *
        (∑ j : Fin 3, M i j*(velocityScale ε j*V j))) =
      s₀*a*(V 1)^2*frameCrossNumerator ε (R 0) (R 1) (R 2) (V 0/V 1) (V 2/V 1)
        (rowAction (scaledVelocityEntry a ε M) 0 (V 0/V 1) (V 2/V 1))
        (rowAction (scaledVelocityEntry a ε M) 1 (V 0/V 1) (V 2/V 1))
        (rowAction (scaledVelocityEntry a ε M) 2 (V 0/V 1) (V 2/V 1)) := by
  norm_num [Fin.sum_univ_three, _root_.cross_apply, velocityScale, rayScale,
    scaledVelocityEntry, frameCrossNumerator, rowAction, Fin.ext_iff,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  field_simp
  ring

theorem scaling_pressure_ratio {a : ℝ} (ha : a ≠ 0) (s₀ ε : ℝ)
    (M : Fin 3 → Fin 3 → ℝ) (R V : Fin 3 → ℝ) (hV : V 1 ≠ 0) :
    (∑ i : Fin 3, (s₀*rayScale ε i*R i)*(∑ j : Fin 3, M i j*(velocityScale ε j*V j))) =
      s₀*a*(V 1)*velocityNumerator (scaledVelocityEntry a ε M)
        (R 0) (R 1) (R 2) (V 0/V 1) 1 (V 2/V 1) := by
  rw [scaling_flux ha, velocityNumerator_homogeneous _ _ _ _ _ _ _ hV]
  ring

end EulerPacketMovingFrame

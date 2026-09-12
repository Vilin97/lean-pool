/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeSupport
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Finset

/-!
Exact grade expansion of a finite packet's momentum residual. The operators
may be instantiated by the actual value/derivative jets at each space-time
point; this file proves the finite algebra and does not assume an Euler solve.
-/

@[expose] public section


noncomputable section

namespace EulerPacketResidual

open Finset EulerFiniteGrades

variable {V Q W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup Q] [Module ℝ Q] [AddCommGroup W] [Module ℝ W]

/-- Residual, constructed using `L`. -/
def residual (M : ℕ) (κ : ℝ) (L : V →ₗ[ℝ] W) (G H : Q →ₗ[ℝ] W)
    (B C : V →ₗ[ℝ] V →ₗ[ℝ] W) (u : ℕ → V) (p : ℕ → Q) : W :=
  L (evaluate M κ u) + G (evaluate M κ p) + κ⁻¹ • H (evaluate M κ p) +
    B (evaluate M κ u) (evaluate M κ u) + κ⁻¹ • C (evaluate M κ u) (evaluate M κ u)

/-- Coefficient, constructed using `truncate`. -/
def coefficient (M : ℕ) (L : V →ₗ[ℝ] W) (G H : Q →ₗ[ℝ] W)
    (B C : V →ₗ[ℝ] V →ₗ[ℝ] W) (u : ℕ → V) (p : ℕ → Q) (n : ℕ) : W :=
  truncate M (fun j => L (u j)) n + truncate M (fun j => G (p j)) n +
    shiftDown M (fun j => H (p j)) n + convolution M B u u n +
    shiftDown (2*M) (convolution M C u u) n

/-- The fast terms lose one grade, with their potentially negative grade proved absent. -/
theorem residual_eq_evaluate (M : ℕ) (κ : ℝ) (hκ : κ ≠ 0)
    (L : V →ₗ[ℝ] W) (G H : Q →ₗ[ℝ] W) (B C : V →ₗ[ℝ] V →ₗ[ℝ] W)
    (u : ℕ → V) (p : ℕ → Q) (hu : u 0 = 0) (hp : H (p 0) = 0) :
    residual M κ L G H B C u p = evaluate (2*M) κ (coefficient M L G H B C u p) := by
  have hL := evaluate_truncate_extend M (2*M) (by omega) κ (fun j => L (u j))
  have hG := evaluate_truncate_extend M (2*M) (by omega) κ (fun j => G (p j))
  have hH := inverse_evaluate_shiftDown_extend M (2*M) (by omega) κ hκ (fun j => H (p j)) hp
  have hC := inverse_evaluate_shiftDown (2*M) κ hκ (convolution M C u u)
    (convolution_zero M C u u hu)
  unfold residual
  rw [bilinear_evaluate M κ B u u, bilinear_evaluate M κ C u u]
  rw [map_evaluate M κ L u, map_evaluate M κ G p, map_evaluate M κ H p]
  rw [← hL, ← hG, hH, hC]
  simp only [coefficient, evaluate, smul_add, sum_add_distrib]

/-- Cancellation of each low coefficient removes precisely those grades from the actual residual. -/
theorem residual_eq_tail (M K : ℕ) (hK : K ≤ 2 * M + 1) (κ : ℝ) (hκ : κ ≠ 0)
    (L : V →ₗ[ℝ] W) (G H : Q →ₗ[ℝ] W) (B C : V →ₗ[ℝ] V →ₗ[ℝ] W)
    (u : ℕ → V) (p : ℕ → Q) (hu : u 0 = 0) (hp : H (p 0) = 0)
    (hcancel : ∀ n < K, coefficient M L G H B C u p n = 0) :
    residual M κ L G H B C u p =
      ∑ n ∈ Ico K (2*M+1), κ^n • coefficient M L G H B C u p n := by
  rw [residual_eq_evaluate M κ hκ L G H B C u p hu hp]
  exact evaluate_eq_tail (2*M) K hK κ _ hcancel

/-- For N profiles plus the last divergence corrector, the remaining grades are N+1 through 2N+2. -/
theorem packet_residual_eq_tail (N : ℕ) (κ : ℝ) (hκ : κ ≠ 0)
    (L : V →ₗ[ℝ] W) (G H : Q →ₗ[ℝ] W) (B C : V →ₗ[ℝ] V →ₗ[ℝ] W)
    (u : ℕ → V) (p : ℕ → Q) (hu : u 0 = 0) (hp : H (p 0) = 0)
    (hcancel : ∀ n ≤ N, coefficient (N + 1) L G H B C u p n = 0) :
    residual (N+1) κ L G H B C u p =
      ∑ n ∈ Ico (N+1) (2*N+3), κ^n • coefficient (N+1) L G H B C u p n := by
  have h := residual_eq_tail (N+1) (N+1) (by omega) κ hκ L G H B C u p hu hp
    (fun n hn => hcancel n (by omega))
  simpa only [show 2*(N+1)+1 = 2*N+3 by omega] using h

end EulerPacketResidual

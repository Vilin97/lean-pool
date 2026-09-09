/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketMomentumExpansion
import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeDiagonal

/-! The low coefficients of the actual packet residual, before solving their equations. -/

@[expose] public section


noncomputable section

namespace EulerPacketResidual

open Finset EulerFiniteGrades

variable {V Q W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup Q] [Module ℝ Q] [AddCommGroup W] [Module ℝ W]

theorem coefficient_eq_diagonal (M n : ℕ) (hn : n + 1 ≤ M)
    (L : V →ₗ[ℝ] W) (G H : Q →ₗ[ℝ] W) (B C : V →ₗ[ℝ] V →ₗ[ℝ] W)
    (u : ℕ → V) (p : ℕ → Q) :
    coefficient M L G H B C u p n =
      L (u n) + G (p n) + H (p (n+1)) +
      (∑ i ∈ range (n+1), B (u i) (u (n-i))) +
      (∑ i ∈ range (n+2), C (u i) (u (n+1-i))) := by
  unfold coefficient shiftDown
  rw [truncate_of_le M n _ (by omega), truncate_of_le M n _ (by omega),
    truncate_of_le M (n+1) _ hn, truncate_of_le (2*M) (n+1) _ (by omega),
    convolution_eq_range M n (by omega), convolution_eq_range M (n+1) hn]

end EulerPacketResidual

namespace EulerPacketPointJets

open Finset EulerSmoothLimit EulerPacketResidual

/-- This is the coefficient equation used in the source recursion, with actual derivatives. -/
theorem momentumGrade_eq_diagonal (N n : ℕ) (hn : n + 1 ≤ N)
    (FInv M : Space →L[ℝ] Space) (m : Space)
    (u : ℕ → Domain → Space) (p : ℕ → Domain → ℝ) (z : Domain) :
    momentumGrade N FInv M m u p z n =
      linearPart M (jet (u n) z) + slowPressure FInv (jet (p n) z) +
      fastPressure m (jet (p (n+1)) z) +
      (∑ i ∈ range (n+1), slowAdvection FInv (jet (u i) z) (jet (u (n-i)) z)) +
      (∑ i ∈ range (n+2), fastAdvection m (jet (u i) z) (jet (u (n+1-i)) z)) :=
  coefficient_eq_diagonal N n hn _ _ _ _ _ _ _

end EulerPacketPointJets

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureJet
public import LeanPool.NavierStokesAndEuler.Euler.PacketResidualGrades

/-! Exact residual expansion with genuine derivatives within the prescribed time interval. -/

@[expose] public section


noncomputable section

namespace EulerPacketPointJets

open EulerSmoothLimit EulerFiniteGrades EulerPacketResidual Finset Set

/-- Sliced momentum residual, constructed using `linearPart`. -/
def slicedMomentumResidual (s : Set ℝ) (κ : ℝ) (FInv M : Space →L[ℝ] Space) (m : Space)
    (u : Domain → Space) (p : Domain → ℝ) (z : Domain) : Space :=
  linearPart M (slicedJet s u z)+slowPressure FInv (pressureJet p z) +
    κ⁻¹ • fastPressure m (pressureJet p z) +
    slowAdvection FInv (slicedJet s u z) (slicedJet s u z) +
    κ⁻¹ • fastAdvection m (slicedJet s u z) (slicedJet s u z)

/-- Sliced momentum grade, constructed using `coefficient`. -/
def slicedMomentumGrade (s : Set ℝ) (N : ℕ) (FInv M : Space →L[ℝ] Space) (m : Space)
    (u : ℕ → Domain → Space) (p : ℕ → Domain → ℝ) (z : Domain) (n : ℕ) : Space :=
  coefficient N (linearPart M) (slowPressure FInv) (fastPressure m)
    (slowAdvection FInv) (fastAdvection m) (fun i => slicedJet s (u i) z)
      (fun i => pressureJet (p i) z) n

theorem slicedMomentum_fieldSum_eq (s : Set ℝ) (N : ℕ) (κ : ℝ) (hκ : κ ≠ 0)
    (FInv M : Space →L[ℝ] Space) (m : Space)
    (u : ℕ → Domain → Space) (p : ℕ → Domain → ℝ) (z : Domain)
    (hs : UniqueDiffWithinAt ℝ s z.1)
    (hut : ∀ i ≤ N, DifferentiableWithinAt ℝ (fun t => u i (t, z.2)) s z.1)
    (hux : ∀ i ≤ N, DifferentiableAt ℝ (fun y => u i (z.1, y)) z.2)
    (hpx : ∀ i ≤ N, DifferentiableAt ℝ (fun y => p i (z.1, y)) z.2)
    (hu0 : slicedJet s (u 0) z = 0) (hp0 : fastPressure m (pressureJet (p 0) z) = 0) :
    slicedMomentumResidual s κ FInv M m (fieldSum N κ u) (fieldSum N κ p) z =
      evaluate (2*N) κ (slicedMomentumGrade s N FInv M m u p z) := by
  unfold slicedMomentumResidual
  rw [slicedJet_fieldSum s N κ u z hs hut hux, pressureJet_fieldSum N κ p z hpx]
  exact residual_eq_evaluate N κ hκ (linearPart M) (slowPressure FInv) (fastPressure m)
    (slowAdvection FInv) (fastAdvection m) (fun i => slicedJet s (u i) z)
      (fun i => pressureJet (p i) z) hu0 hp0

/-- This identity is valid at both endpoints when s=[0,T] and T>0. -/
theorem slicedMomentum_fieldSum_tail (s : Set ℝ) (N : ℕ) (κ : ℝ) (hκ : κ ≠ 0)
    (FInv M : Space →L[ℝ] Space) (m : Space)
    (u : ℕ → Domain → Space) (p : ℕ → Domain → ℝ) (z : Domain)
    (hs : UniqueDiffWithinAt ℝ s z.1)
    (hut : ∀ i ≤ N + 1, DifferentiableWithinAt ℝ (fun t => u i (t, z.2)) s z.1)
    (hux : ∀ i ≤ N + 1, DifferentiableAt ℝ (fun y => u i (z.1, y)) z.2)
    (hpx : ∀ i ≤ N + 1, DifferentiableAt ℝ (fun y => p i (z.1, y)) z.2)
    (hu0 : slicedJet s (u 0) z = 0) (hp0 : fastPressure m (pressureJet (p 0) z) = 0)
    (hcancel : ∀ n ≤ N, slicedMomentumGrade s (N + 1) FInv M m u p z n = 0) :
    slicedMomentumResidual s κ FInv M m (fieldSum (N+1) κ u) (fieldSum (N+1) κ p) z =
      ∑ n ∈ Ico (N+1) (2*N+3), κ^n • slicedMomentumGrade s (N+1) FInv M m u p z n := by
  unfold slicedMomentumResidual
  rw [slicedJet_fieldSum s (N+1) κ u z hs hut hux,
    pressureJet_fieldSum (N+1) κ p z hpx]
  exact packet_residual_eq_tail N κ hκ (linearPart M) (slowPressure FInv) (fastPressure m)
    (slowAdvection FInv) (fastAdvection m) (fun i => slicedJet s (u i) z)
      (fun i => pressureJet (p i) z) hu0 hp0 hcancel

end EulerPacketPointJets

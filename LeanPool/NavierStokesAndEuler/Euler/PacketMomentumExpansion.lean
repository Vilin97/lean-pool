/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPointJets
public import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeDiagonal

@[expose] public section

/-! The graded expansion and tail estimate for the actual normalized momentum expression. -/

noncomputable section

namespace EulerPacketPointJets

open Finset EulerSmoothLimit EulerFiniteGrades EulerPacketResidual

def momentumGrade (N : ℕ) (FInv M : Space →L[ℝ] Space) (m : Space)
    (u : ℕ → Domain → Space) (p : ℕ → Domain → ℝ) (z : Domain) (n : ℕ) : Space :=
  coefficient N (linearPart M) (slowPressure FInv) (fastPressure m)
    (slowAdvection FInv) (fastAdvection m) (fun i => jet (u i) z) (fun i => jet (p i) z) n

/-- The equality expands the actual derivatives of the finite velocity and pressure sums. -/
theorem momentum_fieldSum_eq (N : ℕ) (κ : ℝ) (hκ : κ ≠ 0)
    (FInv M : Space →L[ℝ] Space) (m : Space)
    (u : ℕ → Domain → Space) (p : ℕ → Domain → ℝ) (z : Domain)
    (hu : ∀ i ≤ N, DifferentiableAt ℝ (u i) z)
    (hp : ∀ i ≤ N, DifferentiableAt ℝ (p i) z)
    (hu0 : jet (u 0) z=0) (hp0 : fastPressure m (jet (p 0) z)=0) :
    momentumResidual κ FInv M m (fieldSum N κ u) (fieldSum N κ p) z =
      evaluate (2*N) κ (momentumGrade N FInv M m u p z) := by
  unfold momentumResidual
  rw [jet_fieldSum N κ u z hu, jet_fieldSum N κ p z hp]
  exact residual_eq_evaluate N κ hκ (linearPart M) (slowPressure FInv) (fastPressure m)
    (slowAdvection FInv) (fastAdvection m) (fun i => jet (u i) z) (fun i => jet (p i) z) hu0 hp0

/-- The source's finite packet has no residual grades through N once its coefficient equations hold. -/
theorem momentum_fieldSum_tail (N : ℕ) (κ : ℝ) (hκ : κ ≠ 0)
    (FInv M : Space →L[ℝ] Space) (m : Space)
    (u : ℕ → Domain → Space) (p : ℕ → Domain → ℝ) (z : Domain)
    (hu : ∀ i ≤ N+1, DifferentiableAt ℝ (u i) z)
    (hp : ∀ i ≤ N+1, DifferentiableAt ℝ (p i) z)
    (hu0 : jet (u 0) z=0) (hp0 : fastPressure m (jet (p 0) z)=0)
    (hcancel : ∀ n ≤ N, momentumGrade (N+1) FInv M m u p z n=0) :
    momentumResidual κ FInv M m (fieldSum (N+1) κ u) (fieldSum (N+1) κ p) z =
      ∑ n ∈ Ico (N+1) (2*N+3), κ^n • momentumGrade (N+1) FInv M m u p z n := by
  unfold momentumResidual
  rw [jet_fieldSum (N+1) κ u z hu, jet_fieldSum (N+1) κ p z hp]
  exact packet_residual_eq_tail N κ hκ (linearPart M) (slowPressure FInv) (fastPressure m)
    (slowAdvection FInv) (fastAdvection m) (fun i => jet (u i) z) (fun i => jet (p i) z)
    hu0 hp0 hcancel

/-- A bound on the actual residual follows from the surviving coefficient norms. -/
theorem norm_momentum_fieldSum_le (N : ℕ) (κ : ℝ) (hκ : κ ≠ 0)
    (FInv M : Space →L[ℝ] Space) (m : Space)
    (u : ℕ → Domain → Space) (p : ℕ → Domain → ℝ) (z : Domain)
    (hu : ∀ i ≤ N+1, DifferentiableAt ℝ (u i) z)
    (hp : ∀ i ≤ N+1, DifferentiableAt ℝ (p i) z)
    (hu0 : jet (u 0) z=0) (hp0 : fastPressure m (jet (p 0) z)=0)
    (hcancel : ∀ n ≤ N, momentumGrade (N+1) FInv M m u p z n=0) :
    ‖momentumResidual κ FInv M m (fieldSum (N+1) κ u) (fieldSum (N+1) κ p) z‖ ≤
      ∑ n ∈ Ico (N+1) (2*N+3), |κ|^n * ‖momentumGrade (N+1) FInv M m u p z n‖ := by
  rw [momentum_fieldSum_tail N κ hκ FInv M m u p z hu hp hu0 hp0 hcancel]
  calc
    _ ≤ ∑ n ∈ Ico (N+1) (2*N+3), ‖κ^n • momentumGrade (N+1) FInv M m u p z n‖ :=
      norm_sum_le _ _
    _ = _ := by simp only [norm_smul, norm_pow, Real.norm_eq_abs]

end EulerPacketPointJets

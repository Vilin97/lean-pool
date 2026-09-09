/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPointJets
public import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeAssembly

@[expose] public section

/-! The literal packet sums and their genuine first derivatives match the graded assembly. -/

noncomputable section

namespace EulerPacketPointJets

open EulerFiniteGrades Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem jet_zero (z : Domain) : jet (fun _ : Domain => (0 : E)) z = 0 := by
  simp [jet]

theorem jet_add (f g : Domain → E) (z : Domain)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    jet (f+g) z = jet f z+jet g z := by
  simp only [jet, Pi.add_apply, fderiv_add hf hg, Prod.mk_add_mk]

theorem jet_truncate (N n : ℕ) (u : ℕ → Domain → E) (z : Domain) :
    jet (truncate N u n) z = truncate N (fun i => jet (u i) z) n := by
  by_cases hn : n ≤ N
  · simp only [truncate_of_le N n _ hn]
  · simp only [truncate_of_gt N n _ (by omega), Pi.zero_def]
    exact jet_zero z

theorem jet_shiftUp (N n : ℕ) (u : ℕ → Domain → E) (z : Domain) :
    jet (shiftUp N u n) z = shiftUp N (fun i => jet (u i) z) n := by
  cases n with
  | zero => exact jet_zero z
  | succ n => exact jet_truncate N n u z

theorem differentiableAt_truncate (N n : ℕ) (u : ℕ → Domain → E) (z : Domain)
    (hu : ∀ i ≤ N, DifferentiableAt ℝ (u i) z) :
    DifferentiableAt ℝ (truncate N u n) z := by
  by_cases hn : n ≤ N
  · simpa only [truncate_of_le N n _ hn] using hu n hn
  · simpa only [truncate_of_gt N n _ (by omega), Pi.zero_def] using
      (differentiableAt_const (c := (0 : E)))

theorem differentiableAt_shiftUp (N n : ℕ) (u : ℕ → Domain → E) (z : Domain)
    (hu : ∀ i ≤ N, DifferentiableAt ℝ (u i) z) :
    DifferentiableAt ℝ (shiftUp N u n) z := by
  cases n with
  | zero => exact differentiableAt_const (c := (0 : E))
  | succ n => exact differentiableAt_truncate N n u z hu

theorem jet_assemble (N n : ℕ) (u c : ℕ → Domain → E) (z : Domain)
    (hu : ∀ i ≤ N, DifferentiableAt ℝ (u i) z)
    (hc : ∀ i ≤ N, DifferentiableAt ℝ (c i) z) :
    jet (assemble N u c n) z =
      assemble N (fun i => jet (u i) z) (fun i => jet (c i) z) n := by
  change jet (truncate N u n+shiftUp N c n) z = _
  rw [jet_add _ _ z (differentiableAt_truncate N n u z hu)
      (differentiableAt_shiftUp N n c z hc), jet_truncate, jet_shiftUp]
  rfl

theorem differentiableAt_assemble (N n : ℕ) (u c : ℕ → Domain → E) (z : Domain)
    (hu : ∀ i ≤ N, DifferentiableAt ℝ (u i) z)
    (hc : ∀ i ≤ N, DifferentiableAt ℝ (c i) z) :
    DifferentiableAt ℝ (assemble N u c n) z :=
  (differentiableAt_truncate N n u z hu).add (differentiableAt_shiftUp N n c z hc)

/-- The extra degree N+1 is precisely the final divergence corrector in (13). -/
theorem fieldSum_assemble_from_one (N : ℕ) (κ : ℝ) (u c : ℕ → Domain → E)
    (hu : u 0=0) (hc : c 0=0) (z : Domain) :
    fieldSum (N+1) κ (assemble N u c) z =
      ∑ i ∈ range N, (κ^(i+1) • u (i+1) z+κ^(i+2) • c (i+1) z) := by
  have h := congrArg (fun f : Domain → E => f z)
    (evaluate_assemble_from_one N κ u c hu hc)
  simpa only [fieldSum, evaluate, Finset.sum_apply, Pi.smul_apply, Pi.add_apply] using h

end EulerPacketPointJets

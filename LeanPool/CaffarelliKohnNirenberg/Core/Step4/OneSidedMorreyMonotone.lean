/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedMorrey

/-!
# One Sided Morrey Monotone

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped ENNReal


noncomputable section

namespace CKN.Core.Step4

open CKN.Core.Endgame

/-- The one-sided Morrey transfer constant is monotone in both integral
arguments A and B. -/
theorem oneSidedMorreyBound_mono {P τ ρ₀ : ℝ} {A₁ A₂ B₁ B₂ : ℝ≥0∞}
    (hP : 0 < P) (hA : A₁ ≤ A₂) (hB : B₁ ≤ B₂) :
    oneSidedMorreyBound P τ ρ₀ A₁ B₁ ≤ oneSidedMorreyBound P τ ρ₀ A₂ B₂ := by
  unfold oneSidedMorreyBound
  gcongr

/-- The one-sided Morrey transfer constant is monotone in A alone. -/
theorem oneSidedMorreyBound_mono_left {P τ ρ₀ : ℝ} {A₁ A₂ B : ℝ≥0∞}
    (hP : 0 < P) (hA : A₁ ≤ A₂) :
    oneSidedMorreyBound P τ ρ₀ A₁ B ≤ oneSidedMorreyBound P τ ρ₀ A₂ B := by
  unfold oneSidedMorreyBound
  gcongr

/-- The one-sided Morrey transfer constant is monotone in B alone. -/
theorem oneSidedMorreyBound_mono_right {P τ ρ₀ : ℝ} {A B₁ B₂ : ℝ≥0∞}
    (hP : 0 < P) (hB : B₁ ≤ B₂) :
    oneSidedMorreyBound P τ ρ₀ A B₁ ≤ oneSidedMorreyBound P τ ρ₀ A B₂ := by
  unfold oneSidedMorreyBound
  gcongr

end CKN.Core.Step4

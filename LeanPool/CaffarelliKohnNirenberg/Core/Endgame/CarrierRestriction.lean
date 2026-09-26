/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedMeasurability
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic
public import LeanPool.CaffarelliKohnNirenberg.Statements.MorreyVecMem

/-! # Restriction of indicated Morrey data

Smaller carriers retain the same numerical Morrey bound. Joint measurability
on a spatial-time strip gives globally measurable past-cylinder indications.
-/

public section

open Set MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Endgame

/-- Restricting an indicated source cannot increase its Morrey norm. -/
theorem morreyNorm_indicator_mono_set {P τ : ℝ} (hP : 0 ≤ P)
    {S T : Set ParabolicPoint} (hST : S ⊆ T) (f : ParabolicPoint → ℝ) :
    morreyNorm P τ (S.indicator f) ≤ morreyNorm P τ (T.indicator f) := by
  apply morreyNorm_mono hP
  intro z
  by_cases hz : z ∈ S
  · rw [indicator_of_mem hz, indicator_of_mem (hST hz)]
  · rw [indicator_of_notMem hz, abs_zero]
    exact abs_nonneg _

/-- Componentwise ball-Morrey membership restricts to any smaller carrier. -/
theorem morreyVecMem_mono_carrier {P τ : ℝ} (hP : 0 ≤ P)
    {S T : Set ParabolicPoint} {u : ParabolicPoint → Vec3}
    (hST : S ⊆ T) (hu : morreyVecMem P τ T u) : morreyVecMem P τ S u := by
  intro i
  apply lt_of_le_of_lt _ (hu i)
  apply morreyBallNorm_mono hP
  intro z
  by_cases hz : z ∈ S
  · rw [indicator_of_mem hz, indicator_of_mem (hST hz)]
  · rw [indicator_of_notMem hz, abs_zero]
    exact abs_nonneg _


end CKN.Core.Endgame

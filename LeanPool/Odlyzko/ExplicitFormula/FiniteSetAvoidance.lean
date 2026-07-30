/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Finite Set Avoidance

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Set
open scoped ENNReal

namespace NumberField.Odlyzko

/-- A finite set avoidance radius on length used in the Odlyzko-bound argument. -/
def finiteSetAvoidanceRadiusOnLength (L : ℝ) (S : Finset ℝ) : ℝ :=
  L / (4 * (S.card + 1))

theorem finiteSetAvoidanceRadiusOnLength_pos {L : ℝ} (hL : 0 < L)
    (S : Finset ℝ) :
    0 < finiteSetAvoidanceRadiusOnLength L S := by
  unfold finiteSetAvoidanceRadiusOnLength
  positivity

theorem exists_mem_Ioo_abs_sub_ge_finiteSetAvoidanceRadiusOnLength
    (S : Finset ℝ) (A : ℝ) {L : ℝ} (hL : 0 < L) :
    ∃ T ∈ Ioo A (A + L), ∀ u ∈ S,
      finiteSetAvoidanceRadiusOnLength L S ≤ |T - u| := by
  let r := finiteSetAvoidanceRadiusOnLength L S
  let U : Set ℝ := ⋃ u ∈ S, Ioo (u - r) (u + r)
  have hr : 0 < r := finiteSetAvoidanceRadiusOnLength_pos hL S
  have hU :
      volume.real U ≤ ∑ u ∈ S, volume.real (Ioo (u - r) (u + r)) := by
    exact measureReal_biUnion_finset_le S fun u ↦ Ioo (u - r) (u + r)
  have hU' : volume.real U ≤ (S.card : ℝ) * (2 * r) := by
    calc
      volume.real U ≤
          ∑ u ∈ S, volume.real (Ioo (u - r) (u + r)) := hU
      _ = ∑ _u ∈ S, 2 * r := by
        apply Finset.sum_congr rfl
        intro u _
        simp [Measure.real, Real.volume_Ioo, hr.le]
        ring
      _ = (S.card : ℝ) * (2 * r) := by simp
  have hsmall : (S.card : ℝ) * (2 * r) < L := by
    dsimp [r, finiteSetAvoidanceRadiusOnLength]
    rw [div_eq_mul_inv]
    field_simp
    nlinarith
  by_contra! h
  have hsubset : Ioo A (A + L) ⊆ U := by
    intro T hT
    obtain ⟨u, huS, hu⟩ := h T hT
    have hmem : T ∈ Ioo (u - r) (u + r) := by grind
    exact Set.mem_iUnion.2 ⟨u, Set.mem_iUnion.2 ⟨huS, hmem⟩⟩
  have hUtop : volume U ≠ ∞ := by
    apply ne_of_lt
    dsimp [U]
    apply measure_biUnion_lt_top S.finite_toSet
    simp
  have hmeasure :
      volume.real (Ioo A (A + L)) ≤ volume.real U :=
    measureReal_mono hsubset hUtop
  have hlength : volume.real (Ioo A (A + L)) = L := by
    simp [Measure.real, Real.volume_Ioo, hL.le]
  grind

end NumberField.Odlyzko

/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FastVelocityMixedInduction

/-! Finite ordering measures for material/spatial commutator induction. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Number of spatial letters in an actual derivative word. -/
def amnrSpatialCount : List (Option (Fin 2)) → ℕ
  | [] => 0
  | none :: w => amnrSpatialCount w
  | some _ :: w => amnrSpatialCount w + 1

/-- Number of material letters, tracked separately from the weighted budget. -/
def amnrMaterialCount : List (Option (Fin 2)) → ℕ
  | [] => 0
  | none :: w => amnrMaterialCount w + 1
  | some _ :: w => amnrMaterialCount w

/-- Number of material letters lying outside a spatial derivative. -/
def amnrWordInversions : List (Option (Fin 2)) → ℕ
  | [] => 0
  | none :: w => amnrSpatialCount w + amnrWordInversions w
  | some _ :: w => amnrWordInversions w

theorem amnrSpatialCount_append (w v : List (Option (Fin 2))) :
    amnrSpatialCount (w ++ v) = amnrSpatialCount w + amnrSpatialCount v := by
  induction w with
  | nil => simp [amnrSpatialCount]
  | cons d w ih => cases d <;> simp [amnrSpatialCount, ih, Nat.add_comm, Nat.add_left_comm]

theorem amnrMaterialCount_append (w v : List (Option (Fin 2))) :
    amnrMaterialCount (w ++ v) = amnrMaterialCount w + amnrMaterialCount v := by
  induction w with
  | nil => simp [amnrMaterialCount]
  | cons d w ih => cases d <;> simp [amnrMaterialCount, ih, Nat.add_comm, Nat.add_left_comm]

theorem amnrMaterialCount_eq_count_none (w : List (Option (Fin 2))) :
    amnrMaterialCount w = w.count none := by
  induction w with
  | nil => rfl
  | cons d w ih => cases d <;> simp [amnrMaterialCount, ih]

theorem amnrCounts_length (w : List (Option (Fin 2))) :
    amnrSpatialCount w + amnrMaterialCount w = w.length := by
  induction w with
  | nil => rfl
  | cons d w ih => cases d <;> simp only [amnrSpatialCount, amnrMaterialCount, List.length_cons]
      <;> omega

theorem amnrCounts_budget (w : List (Option (Fin 2))) :
    amnrSpatialCount w + 2 * amnrMaterialCount w = amnrBudget w := by
  induction w with
  | nil => rfl
  | cons d w ih =>
    cases d <;> simp only [amnrSpatialCount, amnrMaterialCount, amnrBudget, List.map_cons,
        List.sum_cons] at * <;> omega

/-- Concatenation counts precisely the new cross inversions. -/
theorem amnrWordInversions_append (w v : List (Option (Fin 2))) :
    amnrWordInversions (w ++ v) = amnrWordInversions w + amnrWordInversions v +
      amnrMaterialCount w * amnrSpatialCount v := by
  induction w with
  | nil => simp [amnrWordInversions, amnrMaterialCount]
  | cons d w ih =>
    cases d with
    | none => simp only [List.cons_append, amnrWordInversions, amnrMaterialCount,
        amnrSpatialCount_append, ih]; ring
    | some i => simp only [List.cons_append, amnrWordInversions, amnrMaterialCount, ih]

/-- Swapping an adjacent material/spatial pair removes exactly one inversion. -/
theorem amnrWordInversions_swap (u v : List (Option (Fin 2))) (i : Fin 2) :
    amnrWordInversions (u ++ none :: some i :: v) =
      amnrWordInversions (u ++ some i :: none :: v) + 1 := by
  rw [amnrWordInversions_append, amnrWordInversions_append]
  simp only [amnrWordInversions, amnrSpatialCount]
  ring

/-- Every inversion measure stays within the square of the weighted budget. -/
theorem amnrWordInversions_le_length_sq (w : List (Option (Fin 2))) :
    amnrWordInversions w ≤ w.length ^ 2 := by
  induction w with
  | nil => simp [amnrWordInversions]
  | cons d w ih =>
    have hc := amnrCounts_length w
    cases d <;> simp only [amnrWordInversions, List.length_cons] <;> nlinarith

/-- A word is canonical or admits one adjacent commutator swap. -/
theorem amnrWord_mixed_or_adjacent (w : List (Option (Fin 2))) :
    IsAmnrMixedWord w ∨ ∃ u : List (Option (Fin 2)), ∃ i : Fin 2,
      ∃ v : List (Option (Fin 2)), w = u ++ none :: some i :: v := by
  induction w with
  | nil => left; simp [IsAmnrMixedWord]
  | cons d w ih =>
    rcases ih with hm | ⟨u, i, v, heq⟩
    · cases d with
      | some i => left; exact List.pairwise_cons.mpr ⟨by simp, hm⟩
      | none =>
        obtain ⟨α, n, heq⟩ := IsAmnrMixedWord.normalForm hm
        cases α with
        | nil =>
          left
          rw [heq]
          simp [amnrMixedWord, IsAmnrMixedWord, List.pairwise_replicate]
        | cons i α =>
          right
          exact ⟨[], i, α.map some ++ List.replicate n none, by
            rw [heq]; simp [amnrMixedWord]⟩
    · right
      exact ⟨d :: u, i, v, by rw [heq]; rfl⟩

end AVenhance.Infra.Section4

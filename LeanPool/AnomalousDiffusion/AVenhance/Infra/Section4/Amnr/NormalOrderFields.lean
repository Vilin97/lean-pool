/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.NormalOrderConstants

/-! Actual primitive fields and budget reserves in the normal-order induction. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- The scalar and the four actual velocity-gradient coefficients are the
only primitive fields needed by material/spatial normal ordering. -/
def amnrNormalField (b : AmnrSpace → Vec 2) (f : AmnrSpace → ℝ) :
    Option (Fin 2 × Fin 2) → AmnrSpace → ℝ
  | none => f
  | some (p, i) => amnrVelocityGradient b p i

/-- Two weighted units reserve the velocity gradient's stream derivatives. -/
def amnrNormalFieldCost : Option (Fin 2 × Fin 2) → ℕ
  | none => 0
  | some _ => 2

/-- Gradient coefficients consume a strictly lower material level. -/
def amnrNormalFieldReserve : Option (Fin 2 × Fin 2) → ℕ
  | none => 0
  | some _ => 1

/-- Actual primitive amplitudes in the source derivative calculus. -/
def amnrNormalFieldAmplitude (F Cb H : ℝ) : Option (Fin 2 × Fin 2) → ℝ
  | none => F
  | some _ => Cb * H

theorem amnrNormalField_contDiff {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (a : Option (Fin 2 × Fin 2)) : ContDiff ℝ (⊤ : ℕ∞) (amnrNormalField b f a) := by
  cases a with
  | none => exact hf
  | some p =>
    exact contDiffOn_univ.mp
      (amnrVelocityGradient_contDiffOn_infty isOpen_univ hb.contDiffOn p.1 p.2)

theorem amnrNormalFieldAmplitude_nonneg {F Cb H : ℝ} (hF : 0 ≤ F) (hCb : 0 ≤ Cb)
    (hH : 0 ≤ H) (a : Option (Fin 2 × Fin 2)) : 0 ≤ amnrNormalFieldAmplitude F Cb H a := by
  cases a with
  | none => exact hF
  | some p => exact mul_nonneg hCb hH

/-- Subword material counts never exceed the outer word's count. -/
theorem amnrMaterialCount_sublist {u v : List (Option (Fin 2))} (hu : u.Sublist v) :
    amnrMaterialCount u ≤ amnrMaterialCount v := by
  rw [amnrMaterialCount_eq_count_none, amnrMaterialCount_eq_count_none]
  exact hu.count_le none

/-- Each correction factor consumes a strictly smaller weighted budget,
including the primitive gradient reserve. -/
theorem amnrAdjacent_subword_budgets (u v : List (Option (Fin 2))) (i p : Fin 2)
    {s : List (Option (Fin 2))} (hs : s.Sublist u) (c : ℕ) :
    amnrBudget s + 2 < amnrBudget (u ++ none :: some i :: v) + c ∧
      amnrBudget (s ++ some p :: v) + c < amnrBudget (u ++ none :: some i :: v) + c := by
  have hh := amnrBudget_sublist hs
  have hnone (w : List (Option (Fin 2))) : amnrBudget (none :: w) = 2 + amnrBudget w := rfl
  have hsome (j : Fin 2) (w : List (Option (Fin 2))) : amnrBudget (some j :: w) = 1 + amnrBudget w
      := rfl
  rw [amnrBudget_append, hnone, hsome, amnrBudget_append, hsome]
  omega

/-- Both correction factors remain below the material count of the original
word. This is the strict lower-level condition needed by the source induction. -/
theorem amnrAdjacent_subword_material_counts (u v : List (Option (Fin 2))) (i p : Fin 2)
    {s : List (Option (Fin 2))} (hs : s.Sublist u) :
    amnrMaterialCount s + 1 ≤ amnrMaterialCount (u ++ none :: some i :: v) ∧
      amnrMaterialCount (s ++ some p :: v) + 1 ≤ amnrMaterialCount (u ++ none :: some i :: v) := by
  have hh := amnrMaterialCount_sublist hs
  rw [amnrMaterialCount_append, amnrMaterialCount_append]
  simp only [amnrMaterialCount]
  omega

/-- An adjacent swap preserves both rates exactly. -/
theorem amnrAdjacent_weight (S H : ℝ) (u v : List (Option (Fin 2))) (i : Fin 2) :
    amnrWeight S H (u ++ none :: some i :: v) =
      amnrWeight S H (u ++ some i :: none :: v) := by
  rw [amnrWeight_append, amnrWeight_append]
  simp only [amnrWeight, List.map_cons, List.prod_cons]
  ring

/-- Exact factorization of the rates in the original commutator word. -/
theorem amnrAdjacent_weight_factor (S H : ℝ) (u v : List (Option (Fin 2))) (i : Fin 2) :
    amnrWeight S H (u ++ none :: some i :: v) =
      amnrWeight S H u * H * S * amnrWeight S H v := by
  rw [amnrWeight_append]
  simp only [amnrWeight, List.map_cons, List.prod_cons]
  ring

theorem amnrMaterialCount_mixed (α : List (Fin 2)) (n : ℕ) :
    amnrMaterialCount (amnrMixedWord α n) = n := by
  rw [amnrMaterialCount_eq_count_none, amnrMixedWord_count_none]

theorem amnrAdjacent_budget (u v : List (Option (Fin 2))) (i : Fin 2) :
    amnrBudget (u ++ none :: some i :: v) = amnrBudget (u ++ some i :: none :: v) := by
  rw [amnrBudget_append, amnrBudget_append]
  have hnone (w : List (Option (Fin 2))) : amnrBudget (none :: w) = 2 + amnrBudget w := rfl
  have hsome (j : Fin 2) (w : List (Option (Fin 2))) : amnrBudget (some j :: w) = 1 + amnrBudget w
      := rfl
  rw [hnone, hsome, hsome, hnone]
  omega

theorem amnrAdjacent_material_count (u v : List (Option (Fin 2))) (i : Fin 2) :
    amnrMaterialCount (u ++ none :: some i :: v) =
      amnrMaterialCount (u ++ some i :: none :: v) := by
  rw [amnrMaterialCount_append, amnrMaterialCount_append]
  rfl

end AVenhance.Infra.Section4

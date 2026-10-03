/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.CorrectionBudgets

/-! Finite combinatorial bounds for actual material correction lists. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

theorem amnrAdvectionDerivativeTerms_length (d : Option (Fin 2))
    (A : List AmnrAdvectionFactor) (w : List (Option (Fin 2))) :
    (amnrAdvectionDerivativeTerms d A w).length = A.length + 1 := by
  induction A with
  | nil => rfl
  | cons a A ih => simp [amnrAdvectionDerivativeTerms, ih]

theorem amnrChangedAdvectionDerivativeTerms_length (t : AmnrAdvectionTerm) :
    (amnrChangedAdvectionDerivativeTerms t).length = 3 * (t.factors.length + 1) := by
  simp only [amnrChangedAdvectionDerivativeTerms, List.length_append, List.length_map,
    amnrAdvectionDerivativeTerms_length]
  omega

/-- A finite sum of derivative-list lengths is controlled by the common
bound; no analytic assumption enters the number of correction monomials. -/
theorem amnr_flatMap_length_le {α β : Type*} (T : List α) (F : α → List β)
    (K : ℕ) (hK : ∀ t ∈ T, (F t).length ≤ K) :
    (T.flatMap F).length ≤ T.length * K := by
  induction T with
  | nil => simp
  | cons t T ih =>
    have ht := hK t (by simp)
    have hT := ih (fun a ha => hK a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Recursive bound on the number of terms in the material error expansion. -/
def amnrMaterialErrorCardinality : ℕ → ℕ
  | 0 => 0
  | n + 1 => amnrMaterialErrorCardinality n * (3 * (n + 1)) + 2

theorem amnrMaterialErrorTerms_length_le (n : ℕ) :
    (amnrMaterialErrorTerms n).length ≤ amnrMaterialErrorCardinality n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have hh := amnr_flatMap_length_le (amnrMaterialErrorTerms n)
      amnrChangedAdvectionDerivativeTerms (3 * (n + 1)) (by
        intro t ht
        obtain ⟨_, _, hM⟩ := amnrMaterialErrorTerms_counts n t ht
        rw [amnrChangedAdvectionDerivativeTerms_length]
        omega)
    have hp := Nat.mul_le_mul_right (3 * (n + 1)) ih
    simp only [amnrMaterialErrorTerms, List.length_append, List.length_cons, List.length_nil,
      amnrMaterialErrorCardinality]
    omega

theorem amnrSpatialAdvectionTerms_length_le (α : List (Fin 2))
    (T : List AmnrAdvectionTerm) (n : ℕ) (hT : ∀ t ∈ T, t.factors.length ≤ n) :
    (amnrSpatialAdvectionTerms α T).length ≤ T.length * (n + 1) ^ α.length := by
  induction α with
  | nil => simp [amnrSpatialAdvectionTerms]
  | cons i α ih =>
    have hh := amnr_flatMap_length_le (amnrSpatialAdvectionTerms α T)
      (fun t => amnrAdvectionDerivativeTerms (some i) t.factors t.scalarWord) (n + 1) (by
        intro t ht
        obtain ⟨a, ha, hL, _, _, _⟩ := amnrSpatialAdvectionTerms_counts α T t ht
        rw [amnrAdvectionDerivativeTerms_length]
        have ha' := hT a ha
        omega)
    have hp := Nat.mul_le_mul_right (n + 1) ih
    simp only [amnrSpatialAdvectionTerms, List.length_cons, pow_succ]
    calc
      _ ≤ (T.length * (n + 1) ^ α.length) * (n + 1) := hh.trans hp
      _ = _ := by ring

/-- Uniform finite bound at each material level and each spatial order. -/
theorem amnrSpatialMaterialErrorTerms_length_le (α : List (Fin 2)) (n : ℕ) :
    (amnrSpatialAdvectionTerms α (amnrMaterialErrorTerms n)).length ≤
      amnrMaterialErrorCardinality n * (n + 1) ^ α.length := by
  have hh := amnrSpatialAdvectionTerms_length_le α (amnrMaterialErrorTerms n) n (by
    intro t ht
    obtain ⟨_, _, hM⟩ := amnrMaterialErrorTerms_counts n t ht
    omega)
  exact hh.trans (Nat.mul_le_mul_right _ (amnrMaterialErrorTerms_length_le n))

end AVenhance.Infra.Section4

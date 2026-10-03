/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.ChangedMaterialExpansion

/-! Exact spatial and material counts of ordered correction monomials. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- Total number of spatial derivatives in an advection term. -/
def amnrTermSpatialCount (t : AmnrAdvectionTerm) : ℕ :=
  (t.factors.map (fun a => amnrSpatialCount a.2)).sum + amnrSpatialCount t.scalarWord

/-- Total number of material derivatives in an advection term. -/
def amnrTermMaterialCount (t : AmnrAdvectionTerm) : ℕ :=
  (t.factors.map (fun a => amnrMaterialCount a.2)).sum + amnrMaterialCount t.scalarWord

theorem amnrAdvectionDerivativeTerms_counts (d : Option (Fin 2))
    (A : List AmnrAdvectionFactor) (w : List (Option (Fin 2)))
    (t : AmnrAdvectionTerm) (ht : t ∈ amnrAdvectionDerivativeTerms d A w) :
    t.factors.length = A.length ∧
    amnrTermSpatialCount t = amnrTermSpatialCount ⟨A, w⟩ + amnrSpatialCount [d] ∧
    amnrTermMaterialCount t = amnrTermMaterialCount ⟨A, w⟩ + amnrMaterialCount [d] := by
  induction A generalizing t with
  | nil =>
    simp only [amnrAdvectionDerivativeTerms, List.mem_singleton] at ht
    subst t
    cases d <;> simp [amnrTermSpatialCount, amnrTermMaterialCount,
      amnrSpatialCount, amnrMaterialCount]
  | cons a A ih =>
    simp only [amnrAdvectionDerivativeTerms, List.mem_cons, List.mem_map] at ht
    rcases ht with rfl | ⟨u, hu, rfl⟩
    · cases d <;> simp [amnrTermSpatialCount, amnrTermMaterialCount,
        amnrSpatialCount, amnrMaterialCount, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · obtain ⟨hL, hS, hM⟩ := ih u hu
      dsimp [amnrAdvectionTermPrepend, amnrTermSpatialCount, amnrTermMaterialCount] at *
      simp only [List.map_cons, List.sum_cons]
      exact ⟨by omega, by omega, by omega⟩

/-- A coarse derivative adds one material letter; each fast-advection
branch instead adds one spatial letter and one velocity factor. -/
theorem amnrChangedAdvectionDerivativeTerms_counts (a t : AmnrAdvectionTerm)
    (ht : t ∈ amnrChangedAdvectionDerivativeTerms a) :
    amnrTermMaterialCount t + t.factors.length =
      amnrTermMaterialCount a + a.factors.length + 1 ∧
    amnrTermSpatialCount t = amnrTermSpatialCount a +
      (t.factors.length - a.factors.length) ∧
    a.factors.length ≤ t.factors.length := by
  simp only [amnrChangedAdvectionDerivativeTerms, List.mem_append, List.mem_map] at ht
  rcases ht with (ht | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩
  · obtain ⟨hL, hS, hM⟩ := amnrAdvectionDerivativeTerms_counts none a.factors a.scalarWord t ht
    simp only [amnrSpatialCount, amnrMaterialCount] at hS hM
    have hSa : amnrTermSpatialCount ⟨a.factors, a.scalarWord⟩ = amnrTermSpatialCount a := rfl
    have hMa : amnrTermMaterialCount ⟨a.factors, a.scalarWord⟩ = amnrTermMaterialCount a := rfl
    exact ⟨by omega, by omega, by omega⟩
  · obtain ⟨hL, hS, hM⟩ := amnrAdvectionDerivativeTerms_counts (some 0) a.factors a.scalarWord u hu
    simp only [amnrSpatialCount, amnrMaterialCount] at hS hM
    dsimp [amnrAdvectionTermPrepend, amnrTermSpatialCount, amnrTermMaterialCount] at *
    simp only [List.map_cons, List.sum_cons, amnrSpatialCount,
      amnrMaterialCount]
    exact ⟨by omega, by omega, by omega⟩
  · obtain ⟨hL, hS, hM⟩ := amnrAdvectionDerivativeTerms_counts (some 1) a.factors a.scalarWord u hu
    simp only [amnrSpatialCount, amnrMaterialCount] at hS hM
    dsimp [amnrAdvectionTermPrepend, amnrTermSpatialCount, amnrTermMaterialCount] at *
    simp only [List.map_cons, List.sum_cons, amnrSpatialCount,
      amnrMaterialCount]
    exact ⟨by omega, by omega, by omega⟩

theorem amnrCounts_replicate_none (n : ℕ) :
    amnrSpatialCount (List.replicate n (none : Option (Fin 2))) = 0 ∧
    amnrMaterialCount (List.replicate n (none : Option (Fin 2))) = n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih => simp [List.replicate_succ, amnrSpatialCount, amnrMaterialCount, ih]

/-- Every material error has a genuine fast factor. Its total counts are
exact, so no highest-level material jet occurs in any correction factor. -/
theorem amnrMaterialErrorTerms_counts (n : ℕ) (t : AmnrAdvectionTerm)
    (ht : t ∈ amnrMaterialErrorTerms n) :
    1 ≤ t.factors.length ∧ amnrTermSpatialCount t = t.factors.length ∧
    amnrTermMaterialCount t + t.factors.length = n := by
  induction n generalizing t with
  | zero => simp [amnrMaterialErrorTerms] at ht
  | succ n ih =>
    simp only [amnrMaterialErrorTerms, List.mem_append, List.mem_flatMap,
      List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with ⟨a, ha, ht⟩ | (rfl | rfl)
    · obtain ⟨hL, hS, hM⟩ := ih a ha
      obtain ⟨hM', hS', hL'⟩ := amnrChangedAdvectionDerivativeTerms_counts a t ht
      exact ⟨by omega, by omega, by omega⟩
    · obtain ⟨hS, hM⟩ := amnrCounts_replicate_none n
      simp [amnrTermSpatialCount, amnrTermMaterialCount, amnrSpatialCount,
        amnrMaterialCount, hS, hM]
    · obtain ⟨hS, hM⟩ := amnrCounts_replicate_none n
      simp [amnrTermSpatialCount, amnrTermMaterialCount, amnrSpatialCount,
        amnrMaterialCount, hS, hM]

/-- Differentiating a monomial never removes a spatial scalar derivative. -/
theorem amnrAdvectionDerivativeTerms_scalar_spatial (d : Option (Fin 2))
    (A : List AmnrAdvectionFactor) (w : List (Option (Fin 2)))
    (t : AmnrAdvectionTerm) (ht : t ∈ amnrAdvectionDerivativeTerms d A w) :
    amnrSpatialCount w ≤ amnrSpatialCount t.scalarWord := by
  induction A generalizing t with
  | nil =>
    simp only [amnrAdvectionDerivativeTerms, List.mem_singleton] at ht
    subst t
    cases d <;> simp [amnrSpatialCount]
  | cons a A ih =>
    simp only [amnrAdvectionDerivativeTerms, List.mem_cons, List.mem_map] at ht
    rcases ht with rfl | ⟨u, hu, rfl⟩
    · exact le_rfl
    · exact ih u hu

theorem amnrChangedAdvectionDerivativeTerms_scalar_spatial (a t : AmnrAdvectionTerm)
    (ht : t ∈ amnrChangedAdvectionDerivativeTerms a) :
    amnrSpatialCount a.scalarWord ≤ amnrSpatialCount t.scalarWord := by
  simp only [amnrChangedAdvectionDerivativeTerms, List.mem_append, List.mem_map] at ht
  rcases ht with (ht | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩
  · exact amnrAdvectionDerivativeTerms_scalar_spatial none a.factors a.scalarWord t ht
  · exact amnrAdvectionDerivativeTerms_scalar_spatial (some 0) a.factors a.scalarWord u hu
  · exact amnrAdvectionDerivativeTerms_scalar_spatial (some 1) a.factors a.scalarWord u hu

/-- The scalar in every material correction has a spatial derivative, so
centering the coarse velocity loses no correction term. -/
theorem amnrMaterialErrorTerms_scalar_spatial (n : ℕ) (t : AmnrAdvectionTerm)
    (ht : t ∈ amnrMaterialErrorTerms n) : 1 ≤ amnrSpatialCount t.scalarWord := by
  induction n generalizing t with
  | zero => simp [amnrMaterialErrorTerms] at ht
  | succ n ih =>
    simp only [amnrMaterialErrorTerms, List.mem_append, List.mem_flatMap,
      List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with ⟨a, ha, ht⟩ | (rfl | rfl)
    · exact (ih a ha).trans (amnrChangedAdvectionDerivativeTerms_scalar_spatial a t ht)
    · simp [amnrSpatialCount]
    · simp [amnrSpatialCount]

end AVenhance.Infra.Section4

/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.AdvectionTermCounts

/-! Actual outer spatial derivatives of ordered material corrections. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Expand a list of advection terms under an ordered sequence of spatial derivatives. -/
def amnrSpatialAdvectionTerms : List (Fin 2) → List AmnrAdvectionTerm → List AmnrAdvectionTerm
  | [], T => T
  | i :: α, T => (amnrSpatialAdvectionTerms α T).flatMap
      (fun t => amnrAdvectionDerivativeTerms (some i) t.factors t.scalarWord)

theorem amnrAdvectionDerivativeTerms_list_value {c : AmnrSpace → Vec 2}
    {v : Fin 2 → AmnrSpace → ℝ} {f : AmnrSpace → ℝ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hv : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (v p))
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (d : Option (Fin 2)) (T : List AmnrAdvectionTerm)
    (z : AmnrSpace) :
    amnrOp c d ((T.map (amnrAdvectionTermValue c v f)).sum) z =
      ((T.flatMap (fun t => amnrAdvectionDerivativeTerms d t.factors t.scalarWord)).map
        (fun t => amnrAdvectionTermValue c v f t z)).sum := by
  have hT : ∀ g ∈ T.map (amnrAdvectionTermValue c v f), ContDiff ℝ (⊤ : ℕ∞) g := by
    intro g hg
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hg
    exact amnrAdvectionTermValue_contDiff hc hv hf t
  change amnrWord c [d] ((T.map (amnrAdvectionTermValue c v f)).sum) z = _
  have hs := congrFun (amnrWord_list_sum_global hc
    (T.map (amnrAdvectionTermValue c v f)) hT [d]) z
  rw [hs, amnr_list_sum_apply]
  simp only [List.map_map, Function.comp_def]
  clear hs hT
  induction T with
  | nil => rfl
  | cons t T ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons,
      List.map_append, List.sum_append]
    rw [ih]
    change amnrOp c d (amnrAdvectionTermValue c v f t) z + _ = _
    rw [amnrAdvectionDerivativeTerms_value hc hv hf]

/-- Every spatial word differentiates the actual finite correction sum into
its explicit Leibniz list, preserving the order of all derivatives. -/
theorem amnrSpatialAdvectionTerms_value {c : AmnrSpace → Vec 2}
    {v : Fin 2 → AmnrSpace → ℝ} {f : AmnrSpace → ℝ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hv : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (v p))
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (α : List (Fin 2)) (T : List AmnrAdvectionTerm) :
    amnrWord c (α.map some) ((T.map (amnrAdvectionTermValue c v f)).sum) =
      ((amnrSpatialAdvectionTerms α T).map (amnrAdvectionTermValue c v f)).sum := by
  induction α with
  | nil => rfl
  | cons i α ih =>
    funext z
    simp only [List.map_cons, amnrWord, amnrSpatialAdvectionTerms]
    rw [ih, amnrAdvectionDerivativeTerms_list_value hc hv hf]
    simpa only [List.map_map, Function.comp_def, amnrSpatialAdvectionTerms] using
      (amnr_list_sum_apply
        ((amnrSpatialAdvectionTerms (i :: α) T).map (amnrAdvectionTermValue c v f)) z).symm

/-- Outer spatial differentiation changes only the total spatial count. -/
theorem amnrSpatialAdvectionTerms_counts (α : List (Fin 2)) (T : List AmnrAdvectionTerm)
    (t : AmnrAdvectionTerm) (ht : t ∈ amnrSpatialAdvectionTerms α T) :
    ∃ a ∈ T, t.factors.length = a.factors.length ∧
      amnrTermMaterialCount t = amnrTermMaterialCount a ∧
      amnrTermSpatialCount t = amnrTermSpatialCount a + α.length ∧
      amnrSpatialCount a.scalarWord ≤ amnrSpatialCount t.scalarWord := by
  induction α generalizing t with
  | nil => exact ⟨t, ht, rfl, rfl, by simp, le_rfl⟩
  | cons i α ih =>
    obtain ⟨u, hu, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨a, ha, hL, hM, hS, hW⟩ := ih u hu
    obtain ⟨hL', hS', hM'⟩ := amnrAdvectionDerivativeTerms_counts (some i)
      u.factors u.scalarWord t ht
    have hW' := amnrAdvectionDerivativeTerms_scalar_spatial (some i)
      u.factors u.scalarWord t ht
    have huS : amnrTermSpatialCount ⟨u.factors, u.scalarWord⟩ = amnrTermSpatialCount u := rfl
    have huM : amnrTermMaterialCount ⟨u.factors, u.scalarWord⟩ = amnrTermMaterialCount u := rfl
    rw [huS] at hS'
    rw [huM] at hM'
    simp only [amnrSpatialCount, amnrMaterialCount] at hS' hM'
    simp only [List.length_cons]
    exact ⟨a, ha, by omega, by omega, by omega, hW.trans hW'⟩

/-- Exact count identities after every outer spatial word and material level. -/
theorem amnrSpatialMaterialErrorTerms_counts (α : List (Fin 2)) (n : ℕ)
    (t : AmnrAdvectionTerm) (ht : t ∈ amnrSpatialAdvectionTerms α (amnrMaterialErrorTerms n)) :
    1 ≤ t.factors.length ∧ 1 ≤ amnrSpatialCount t.scalarWord ∧
    amnrTermSpatialCount t = t.factors.length + α.length ∧
    amnrTermMaterialCount t + t.factors.length = n := by
  obtain ⟨a, ha, hL, hM, hS, hW⟩ := amnrSpatialAdvectionTerms_counts α _ t ht
  obtain ⟨haL, haS, haM⟩ := amnrMaterialErrorTerms_counts n a ha
  have haW := amnrMaterialErrorTerms_scalar_spatial n a ha
  exact ⟨by omega, by omega, by omega, by omega⟩

end AVenhance.Infra.Section4

/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesBasic

/-! Joint smoothness and spatial periodicity for the actual T iterates.

The `IsClassicalSol` predicate already packages joint smoothness up to
the initial time and spatial periodicity.  This module exposes those facts as
an iteration-indexed API, including the base iterate `T 0 = θprev`.
-/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section4

open AVenhance

/-- Every actual iterate through the budget is jointly smooth on the
closed nonnegative-time domain.  For positive iterates this is the smoothness
field of `IsClassicalSol`; the base iterate uses the classical previous-scale
solution. -/
theorem tIterate_contDiffOn_nonneg {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ}
    {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    {i : ℕ} (hi : i ≤ Nstar β) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T i p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  by_cases hi0 : i = 0
  · subst i
    simpa only [hT.1] using hθ.1
  · exact (hT.2 i (by omega) hi).1

/-- Every nonnegative-time slice of an actual T iterate is spatially smooth. -/
theorem tIterate_space_contDiff {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ}
    {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    {i : ℕ} (hi : i ≤ Nstar β) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ (⊤ : ℕ∞) (T i t) := by
  let embed : Vec 2 → ℝ × Vec 2 := fun x => (t, x)
  have hembed : ContDiff ℝ (⊤ : ℕ∞) embed := by fun_prop
  have hmaps : ∀ x, embed x ∈ Set.Ici (0 : ℝ) ×ˢ Set.univ := by
    intro x
    exact ⟨ht, Set.mem_univ x⟩
  have hcomp := (tIterate_contDiffOn_nonneg I hΦ hT hθ hi).comp_contDiff
    hembed hmaps
  simpa only [Function.comp_def] using hcomp

/-- Spatial periodicity of every actual iterate through the finite iteration
budget. -/
theorem tIterate_periodic {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ}
    {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    {i : ℕ} (hi : i ≤ Nstar β) {t : ℝ} (ht : 0 ≤ t) :
    IsZ2Periodic (T i t) := by
  exact iterates_periodic I hΦ hT (fun t ht => hθ.2.1 t ht) hi ht

/-- Joint regularity and periodicity of the terminal iterate used as
`T_{m-1}` in the Section 5 residuals. -/
theorem terminalT_contDiffOn_nonneg_and_periodic {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ}
    {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev) :
    ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => T (Nstar β) p.1 p.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
      ∀ t : ℝ, 0 ≤ t → IsZ2Periodic (T (Nstar β) t) := by
  exact ⟨tIterate_contDiffOn_nonneg I hΦ hT hθ le_rfl,
    fun t ht => tIterate_periodic I hΦ hT hθ le_rfl ht⟩

end AVenhance.Infra.Section4

/-
Copyright (c) 2026 Tutte formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tutte formalization contributors
-/
module

public import LeanPool.TuttePath.Definitions
public import LeanPool.TuttePath.PathInduction

-- Modified for Lean Pool: module integration, public visibility, and import paths.

/-!
Tutte's path theorem for finite matroids, proved by corank induction.

Source: Baker–Jin–Lorscheid, arXiv:2601.02582v2, Theorem 1.8 (`thm:path-theorem`).
Definitions appear in `LeanPool.TuttePath.Definitions`.
Structural dependencies are proved in the imported project modules.
-/

public section

namespace TutteFormalization

/-- The stronger path theorem: connectedness of the contraction by `F` suffices.
Properness of `F` follows from containment in the endpoint hyperplane. -/
theorem path_theorem_of_indecomposable {α : Type*} (M : Matroid α) [M.Finite]
    (Γ : Set (Set α)) (hΓ : ModularCut M Γ) (F : Set α) (hF : Indecomposable M F)
    (X Y : Set α) (hX : IsHyperplane M X) (hY : IsHyperplane M Y)
    (hFX : F ⊆ X) (hFY : F ⊆ Y) (hXoff : X ∉ Γ) (hYoff : Y ∉ Γ) :
    ∃ p : TuttePath M, p.origin = X ∧ p.terminus = Y ∧ p.On F ∧ p.Off Γ :=
  path_theorem_induction M Γ hΓ F hF X Y hX hY hFX hFY hXoff hYoff

/-- `thm:path-theorem`, the two-endpoints-off-cut BJL formulation.
A source-faithful specialization of `path_theorem_of_indecomposable`. -/
theorem path_theorem {α : Type*} (M : Matroid α) [M.Finite]
    (_hM : Connected M) (Γ : Set (Set α)) (hΓ : ModularCut M Γ)
    (F : Set α) (hF : Indecomposable M F) (_hFproper : F ≠ M.E)
    (X Y : Set α) (hX : IsHyperplane M X) (hY : IsHyperplane M Y)
    (hFX : F ⊆ X) (hFY : F ⊆ Y) (hXoff : X ∉ Γ) (hYoff : Y ∉ Γ) :
    ∃ p : TuttePath M, p.origin = X ∧ p.terminus = Y ∧ p.On F ∧ p.Off Γ := by
  exact path_theorem_of_indecomposable M Γ hΓ F hF X Y hX hY hFX hFY hXoff hYoff

end TutteFormalization

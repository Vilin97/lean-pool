/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
import LeanPool.DirectedTopologyLean4.Constructions

/-
  This file contains the definition of the directed unit interval.
  The directedness is induced by the preorder it inherits from ℝ.
-/

open scoped unitInterval

universe u

namespace DirectedUnitInterval

/-- Construct the directed unit interval by using the preorder inherited from ℝ
-/
instance : DirectedSpace I := DirectedSpace.Preorder I

/-- The identity on I as a path I → I.
-/
def IdentityPath : Path (0 : I) (1 : I) :=
{
  toFun := fun x => x,
  continuous_toFun := by continuity,
  source' := by simp,
  target' := by simp,
}

/-- The identity path is a directed path. -/
lemma isDipath_identityPath : IsDipath IdentityPath := fun _ _ hab => hab

/-- If `γ` is path and the identity path on I composed with `γ` is a directed path, then `γ` is a
directed path.
-/
lemma isDipath_of_isDipath_comp_id {X : Type u} [DirectedSpace X] {x y : X} {γ : Path x y}
  (h : IsDipath <| IdentityPath.map γ.continuous_toFun) : IsDipath γ := by
  convert isDipath_cast (IdentityPath.map γ.continuous_toFun) (γ.source.symm) (γ.target.symm) h

/-- A directed map from I to I is monotone -/
lemma monotone_of_directed (f : D(I,I)) : Monotone f :=
  fun _ _ h => (f.directed_toFun IdentityPath isDipath_identityPath) h

/-- A continuous map from I to I that is monotone is directed -/
lemma directed_of_monotone (f : C(I, I)) (hf_mono : Monotone f) : DirectedMap.Directed f :=
  fun _ _ _ γ_dipath _ _ ht₀t₁ => hf_mono (γ_dipath ht₀t₁)

/-- A directed path on I is bounded by its source and target -/
lemma directed_path_bounded {t₀ t₁ : I} {γ : Path t₀ t₁} (γ_dipath : IsDipath γ)
    : ∀ t, t₀ ≤ γ t ∧ γ t ≤ t₁ :=
  monotone_path_bounded γ_dipath

/-- The source of a directed path on I is `≤` than its target -/
lemma directed_path_source_le_target {t₀ t₁ : I} {γ : Path t₀ t₁} (γ_dipath : IsDipath γ) : t₀ ≤ t₁
    :=
  monotone_path_source_le_target γ_dipath

end DirectedUnitInterval

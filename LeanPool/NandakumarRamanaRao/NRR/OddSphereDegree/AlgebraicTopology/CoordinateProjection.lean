/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SubordinateChains
import Mathlib

/-! # Coordinate Projection -/

open CategoryTheory AlgebraicTopology Limits
open SphereOddDegree.AffineBarycentricSubdivision

namespace SphereOddDegree

variable {R : Type} [CommRing R] {X : TopCat.{0}}
noncomputable def keepHom (R : Type) [CommRing R] (X : TopCat.{0}) {n : ℕ}
    (P : singularSimplices X n → Prop) [DecidablePred P] :
    singularChainGroup R X n ⟶ singularChainGroup R X n :=
  Sigma.desc fun σ =>
    if P σ then Sigma.ι (fun (_ : singularSimplices X n) => ModuleCat.of R R) σ else 0

theorem keepHom_generator {n : ℕ} (P : singularSimplices X n → Prop) [DecidablePred P]
    (σ : singularSimplices X n) :
    (keepHom R X P).hom (chainGenerator R X n σ)
      = if P σ then chainGenerator R X n σ else 0 := by
  have h := Sigma.ι_desc (fun σ => if P σ then Sigma.ι (fun (_ : singularSimplices X n) => ModuleCat.of R R) σ else 0) σ
  have h2 := congrArg (fun (m : ModuleCat.of R R ⟶ singularChainGroup R X n) => m.hom (1 : R)) h
  erw [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  have hgen : chainGenerator R X n σ = (Sigma.ι (fun (_ : singularSimplices X n) => ModuleCat.of R R) σ).hom (1 : R) := rfl
  rw [hgen]
  refine h2.trans ?_
  by_cases hP : P σ
  · rw [if_pos hP]
    erw [if_pos hP]
    rfl
  · rw [if_neg hP]
    erw [if_neg hP, ModuleCat.hom_zero, LinearMap.zero_apply]

theorem keepHom_mem_subChainSubmodule {n : ℕ} {S T : Set X}
    [DecidablePred (IsSubordinate (X := X) S (n := n))]
    {c : singularChainGroup R X n} (hc : c ∈ subChainSubmodule R X T n) :
    (keepHom R X (IsSubordinate S)).hom c ∈ subChainSubmodule R X (S ∩ T) n := by
  refine subChainSubmodule_induction (S := T)
    (p := fun x => (keepHom R X (IsSubordinate S)).hom x ∈ subChainSubmodule R X (S ∩ T) n)
    ?_ ?_ ?_ ?_ hc
  · intro σ hσ
    rw [keepHom_generator]
    by_cases hS : IsSubordinate S σ
    · rw [if_pos hS]
      exact chainGenerator_mem_subChainSubmodule (Set.subset_inter hS hσ)
    · rw [if_neg hS]
      exact Submodule.zero_mem _
  · show (keepHom R X (IsSubordinate S)).hom 0 ∈ _
    rw [map_zero]; exact Submodule.zero_mem _
  · intro x y hx hy
    show (keepHom R X (IsSubordinate S)).hom (x + y) ∈ _
    rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro a x hx
    show (keepHom R X (IsSubordinate S)).hom (a • x) ∈ _
    rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem keepHom_eq_self_of_mem {n : ℕ} {S : Set X}
    [DecidablePred (IsSubordinate (X := X) S (n := n))]
    {c : singularChainGroup R X n} (hc : c ∈ subChainSubmodule R X S n) :
    (keepHom R X (IsSubordinate S)).hom c = c := by
  refine subChainSubmodule_induction (S := S)
    (p := fun x => (keepHom R X (IsSubordinate S)).hom x = x) ?_ ?_ ?_ ?_ hc
  · intro σ hσ
    rw [keepHom_generator, if_pos hσ]
  · show (keepHom R X (IsSubordinate S)).hom 0 = 0
    rw [map_zero]
  · intro x y hx hy
    show (keepHom R X (IsSubordinate S)).hom (x + y) = x + y
    rw [map_add, hx, hy]
  · intro a x hx
    show (keepHom R X (IsSubordinate S)).hom (a • x) = a • x
    rw [map_smul, hx]

end SphereOddDegree

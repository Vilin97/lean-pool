/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Relation norms and Galois–Tukey morphisms

The definitions and inequalities in the preliminary section of the manuscript.
The direction of a morphism agrees with that section: a morphism from `A` to `B`
gives `B.norm ≤ A.norm`.
-/

open Cardinal Set

universe u

namespace NonMRR

/-- A relation whose every challenge has a response. -/
structure Relation where
  /-- The objects that must be solved. -/
  Challenge : Type u
  /-- The potential solutions to challenges. -/
  Response : Type u
  /-- Whether a response solves a challenge. -/
  relates : Challenge → Response → Prop
  total : ∀ x, ∃ y, relates x y

namespace Relation

/-- A family of responses solving every challenge. -/
def Dominating (A : Relation.{u}) (s : Set A.Response) : Prop :=
  ∀ x, ∃ y ∈ s, A.relates x y

/-- The least cardinality of a dominating family. -/
noncomputable def norm (A : Relation.{u}) : Cardinal.{u} :=
  sInf {κ | ∃ s : Set A.Response, A.Dominating s ∧ #s = κ}

theorem dominating_univ (A : Relation.{u}) : A.Dominating univ := by
  intro x
  obtain ⟨y, hy⟩ := A.total x
  exact ⟨y, mem_univ _, hy⟩

theorem norm_le (A : Relation.{u}) {s : Set A.Response} (hs : A.Dominating s) :
    A.norm ≤ #s :=
  csInf_le' ⟨s, hs, rfl⟩

theorem exists_dominating_of_norm (A : Relation.{u}) :
    ∃ s : Set A.Response, A.Dominating s ∧ #s = A.norm := by
  change sInf {κ | ∃ s : Set A.Response, A.Dominating s ∧ #s = κ} ∈
    {κ | ∃ s : Set A.Response, A.Dominating s ∧ #s = κ}
  apply csInf_mem
  exact ⟨#(univ : Set A.Response), univ, A.dominating_univ, rfl⟩

/-- The contravariant challenge map and covariant response map of a morphism. -/
structure Morphism (A B : Relation.{u}) where
  /-- Pull a target challenge back to the source relation. -/
  challenge : B.Challenge → A.Challenge
  /-- Send a source response to the target relation. -/
  response : A.Response → B.Response
  map_rel : ∀ x y, A.relates (challenge x) y → B.relates x (response y)

theorem Morphism.dominating_image {A B : Relation.{u}} (f : Morphism A B)
    {s : Set A.Response} (hs : A.Dominating s) : B.Dominating (f.response '' s) := by
  intro x
  obtain ⟨y, hys, hy⟩ := hs (f.challenge x)
  exact ⟨f.response y, mem_image_of_mem _ hys, f.map_rel x y hy⟩

/-- Morphisms reverse the ordering of norms. -/
theorem Morphism.norm_le {A B : Relation.{u}} (f : Morphism A B) : B.norm ≤ A.norm := by
  obtain ⟨s, hs, hcard⟩ := A.exists_dominating_of_norm
  calc
    B.norm ≤ #(f.response '' s) := B.norm_le (f.dominating_image hs)
    _ ≤ #s := Cardinal.mk_image_le
    _ = A.norm := hcard

/-- The second challenge in a sequential composition depends on the first response. -/
def sequential (A B : Relation.{u}) : Relation.{u} where
  Challenge := A.Challenge × (A.Response → B.Challenge)
  Response := A.Response × B.Response
  relates x y := A.relates x.1 y.1 ∧ B.relates (x.2 y.1) y.2
  total x := by
    obtain ⟨a, ha⟩ := A.total x.1
    obtain ⟨b, hb⟩ := B.total (x.2 a)
    exact ⟨(a, b), ha, hb⟩

theorem dominating_product {A B : Relation.{u}} {s : Set A.Response}
    {t : Set B.Response} (hs : A.Dominating s) (ht : B.Dominating t) :
    (A.sequential B).Dominating (s ×ˢ t) := by
  intro x
  obtain ⟨a, has, ha⟩ := hs x.1
  obtain ⟨b, hbt, hb⟩ := ht (x.2 a)
  exact ⟨(a, b), ⟨has, hbt⟩, ha, hb⟩

/-- The upper bound for sequential composition used in the manuscript. -/
theorem sequential_norm_le (A B : Relation.{u}) :
    (A.sequential B).norm ≤ A.norm * B.norm := by
  obtain ⟨s, hs, hsc⟩ := A.exists_dominating_of_norm
  obtain ⟨t, ht, htc⟩ := B.exists_dominating_of_norm
  calc
    (A.sequential B).norm ≤ #(s ×ˢ t) :=
      (A.sequential B).norm_le (dominating_product hs ht)
    _ = #s * #t := by
      simpa only [Cardinal.mk_prod, Cardinal.lift_id] using
        Cardinal.mk_congr (Equiv.Set.prod s t)
    _ = A.norm * B.norm := by rw [hsc, htc]

/-- The purely cardinal final step of the argument. -/
theorem norm_le_of_sequential_morphism {A B C : Relation.{u}}
    (f : Morphism (A.sequential B) C) (hB : ℵ₀ ≤ B.norm) (hAB : A.norm ≤ B.norm) :
    C.norm ≤ B.norm := by
  calc
    C.norm ≤ (A.sequential B).norm := f.norm_le
    _ ≤ A.norm * B.norm := sequential_norm_le A B
    _ ≤ B.norm * B.norm := mul_le_mul_left hAB _
    _ = B.norm := Cardinal.mul_eq_self hB

end Relation

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/

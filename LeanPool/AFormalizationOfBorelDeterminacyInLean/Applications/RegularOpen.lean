/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Applications.General
import Mathlib.Order.Heyting.Regular
import Mathlib.Tactic.ApplyFun
import Mathlib.Topology.Sets.Opens

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Applications.RegularOpen

Auxiliary declarations for the Borel determinacy formalization.
-/


variable {X : Type*} [tX : TopologicalSpace X] {A B : Set X} {U V : tX.Opens}

namespace TopologicalSpace.Opens
lemma le_def : U ≤ V ↔ (U : Set X) ⊆ V := by simp only [SetLike.coe_subset_coe]
@[simp] lemma coe_himp' : U ⇨ V = interior (V ∪ (U : Set X)ᶜ) := by
  suffices U ⇨ V = Opens.interior (V ∪ (U : Set X)ᶜ) by
    apply_fun (fun U ↦ (U : Set X)) at this
    simpa using this
  apply eq_of_forall_le_iff; intro W
  simp_rw [le_himp_iff, ← SetLike.coe_subset_coe, coe_inf, coe_interior,
    W.isOpen.subset_interior_iff]
  constructor <;> (intro h; tauto_set)
@[simp] lemma coe_compl' : Uᶜ = interior (U : Set X)ᶜ := by rw [← himp_bot, coe_himp']; simp
lemma coe_compl_compl : ((Uᶜᶜ : tX.Opens) : Set X) = interior (closure U) := by simp
lemma isRegular_iff : Heyting.IsRegular U ↔ interior (closure U) = (U : Set X) := by
  simp [Heyting.IsRegular, Opens.ext_iff]
end TopologicalSpace.Opens
open TopologicalSpace

lemma interior_closure_interior_closure_eq_interior_closure :
  interior (closure (interior (closure A))) = interior (closure A) :=
  subset_antisymm (interior_mono (isClosed_closure.closure_interior_subset))
    isOpen_interior.subset_interior_closure
lemma IsClosed.interior_isRegular (hA : IsClosed A) : Heyting.IsRegular (Opens.interior A) := by
  rw [Opens.isRegular_iff, ← hA.closure_eq, Opens.coe_interior,
    interior_closure_interior_closure_eq_interior_closure]

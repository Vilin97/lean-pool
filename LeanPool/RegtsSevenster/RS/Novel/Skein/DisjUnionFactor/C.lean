/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.DisjUnionFactor.B

/-!
# The disjoint union: canonical migration

Migrating canonical data between a union and its components.
-/

namespace RS

open scoped Classical

/-! ## The canonical-value migration

The corrected (canonical) constrained value pins a path-canonical
orientation and weights it by the Pfaffian chord-diagram sign.  The
factorization migrates: the product of two path-canonical component
orientations is path-canonical for the union (chains stay
componentwise), and cross-component chords never interleave under
any order placing every left label below every right label, so the
crossing count — hence the path sign — is additive. -/

section CanonMigration

open EdgeSubset

variable {α β : Type}

/-! ### Boundary membership over the union -/

/-- Being a boundary flag is componentwise on the left. -/
theorem inl_mem_boundary
    {W₁ : Fragment α} {W₂ : Fragment β} {F : EdgeSubset (W₁.disjUnion W₂)}
    {g : W₁.Flag} :
    (Sum.inl g : (W₁.disjUnion W₂).Flag) ∈ F.boundaryFlags ↔
      g ∈ (leftSub F).boundaryFlags := by
  constructor
  · intro h
    obtain ⟨hf, hl⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr
      ⟨mem_leftSub_flags.mpr hf, attach_inl_label_iff.mp hl⟩
  · intro h
    obtain ⟨hf, hl⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr
      ⟨mem_leftSub_flags.mp hf, attach_inl_label_iff.mpr hl⟩

/-- And on the right. -/
theorem inr_mem_boundary
    {W₁ : Fragment α} {W₂ : Fragment β} {F : EdgeSubset (W₁.disjUnion W₂)}
    {g : W₂.Flag} :
    (Sum.inr g : (W₁.disjUnion W₂).Flag) ∈ F.boundaryFlags ↔
      g ∈ (rightSub F).boundaryFlags := by
  constructor
  · intro h
    obtain ⟨hf, hl⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr
      ⟨mem_rightSub_flags.mpr hf, attach_inr_label_iff.mp hl⟩
  · intro h
    obtain ⟨hf, hl⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr
      ⟨mem_rightSub_flags.mp hf, attach_inr_label_iff.mpr hl⟩

/-! ### The path match of the product system is componentwise -/

-- The proof introduces the lexicographic order on the sum, which
-- needs both component orders even though the statement does not.
/-- A left boundary flag's chain stays left, so the product
system's path matching is the left component's. -/
theorem pathMatch_prodRel_inl
    [LinearOrder α] [LinearOrder β] {W₁ : Fragment α} {W₂ : Fragment β}
    {F : EdgeSubset (W₁.disjUnion W₂)}
    (κ₁ : (leftSub F).RelTransitionSystem)
    (κ₂ : (rightSub F).RelTransitionSystem)
    {g : W₁.Flag}
    (hb : (Sum.inl g : (W₁.disjUnion W₂).Flag) ∈ F.boundaryFlags)
    (hb' : g ∈ (leftSub F).boundaryFlags) :
    (prodRel (F := F) κ₁ κ₂).pathMatch (Sum.inl g) hb =
      Sum.inl (κ₁.pathMatch g hb') := by
  letI := sumLexLinearOrder α β
  obtain ⟨k, -, hcont, hpm⟩ := pathMatch_chain_length κ₁ hb'
  have hterm : W₁.pairing (iterWalk κ₁ g k) ∈
      (leftSub F).boundaryFlags := by
    rw [← hpm]
    exact κ₁.pathMatch_mem hb'
  have hcontU : ∀ t, t < k →
      (W₁.disjUnion W₂).pairing
        (iterWalk (prodRel (F := F) κ₁ κ₂) (Sum.inl g) t) ∈
          F.internalFlags := by
    intro t ht
    rw [iterWalk_prodRel_inl κ₁ κ₂ g t, pairing_inl]
    exact inl_mem_internal.mpr (hcont t ht)
  have htermU : (W₁.disjUnion W₂).pairing
      (iterWalk (prodRel (F := F) κ₁ κ₂) (Sum.inl g) k) ∈
        F.boundaryFlags := by
    rw [iterWalk_prodRel_inl κ₁ κ₂ g k, pairing_inl]
    exact inl_mem_boundary.mpr hterm
  refine (pathMatch_eq_of_chain (prodRel (F := F) κ₁ κ₂) hb
    hcontU htermU).trans ?_
  rw [iterWalk_prodRel_inl κ₁ κ₂ g k, pairing_inl, hpm]

-- The proof introduces the lexicographic order on the sum, which
-- needs both component orders even though the statement does not.
/-- And likewise on the right. -/
theorem pathMatch_prodRel_inr
    [LinearOrder α] [LinearOrder β] {W₁ : Fragment α} {W₂ : Fragment β}
    {F : EdgeSubset (W₁.disjUnion W₂)}
    (κ₁ : (leftSub F).RelTransitionSystem)
    (κ₂ : (rightSub F).RelTransitionSystem)
    {g : W₂.Flag}
    (hb : (Sum.inr g : (W₁.disjUnion W₂).Flag) ∈ F.boundaryFlags)
    (hb' : g ∈ (rightSub F).boundaryFlags) :
    (prodRel (F := F) κ₁ κ₂).pathMatch (Sum.inr g) hb =
      Sum.inr (κ₂.pathMatch g hb') := by
  letI := sumLexLinearOrder α β
  obtain ⟨k, -, hcont, hpm⟩ := pathMatch_chain_length κ₂ hb'
  have hterm : W₂.pairing (iterWalk κ₂ g k) ∈
      (rightSub F).boundaryFlags := by
    rw [← hpm]
    exact κ₂.pathMatch_mem hb'
  have hcontU : ∀ t, t < k →
      (W₁.disjUnion W₂).pairing
        (iterWalk (prodRel (F := F) κ₁ κ₂) (Sum.inr g) t) ∈
          F.internalFlags := by
    intro t ht
    rw [iterWalk_prodRel_inr κ₁ κ₂ g t, pairing_inr]
    exact inr_mem_internal.mpr (hcont t ht)
  have htermU : (W₁.disjUnion W₂).pairing
      (iterWalk (prodRel (F := F) κ₁ κ₂) (Sum.inr g) k) ∈
        F.boundaryFlags := by
    rw [iterWalk_prodRel_inr κ₁ κ₂ g k, pairing_inr]
    exact inr_mem_boundary.mpr hterm
  refine (pathMatch_eq_of_chain (prodRel (F := F) κ₁ κ₂) hb
    hcontU htermU).trans ?_
  rw [iterWalk_prodRel_inr κ₁ κ₂ g k, pairing_inr, hpm]

end CanonMigration

end RS

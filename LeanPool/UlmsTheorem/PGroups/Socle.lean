/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth
-/

import Mathlib.Algebra.Module.ZMod
import LeanPool.UlmsTheorem.PGroups.Defs

/-!
# Socle-level constructions

This file contains the p-socle and its interaction with the Ulm filtration.
-/

namespace UlmsTheorem

open Ordinal

variable (p : ℕ)

/-- The `p`-socle `P = {x | p • x = 0}`. -/
def pSocle {G : Type*} [AddCommGroup G] : AddSubgroup G where
  carrier   := {x | p • x = 0}
  zero_mem' := by simp
  add_mem'  := by
    rintro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [smul_add, ha, hb, add_zero]
  neg_mem'  := by
    rintro a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [smul_neg, ha, neg_zero]

section SocleLemmas

variable {G : Type*} [AddCommGroup G]

@[simp] lemma mem_pSocle (x : G) : x ∈ pSocle p (G := G) ↔ p • x = 0 := Iff.rfl

/-- The filtered socle `P_α = P ∩ G_α`. -/
noncomputable def pSocleAt (α : Ordinal) : AddSubgroup G :=
  pSocle p ⊓ ulmSubgroup p α

@[simp] lemma mem_pSocleAt (α : Ordinal) (x : G) :
    x ∈ pSocleAt p α (G := G) ↔ p • x = 0 ∧ x ∈ ulmSubgroup p α := Iff.rfl

lemma pSocleAt_zero : pSocleAt p (0 : Ordinal) (G := G) = pSocle p := by
  simp [pSocleAt, ulmSubgroup_zero]

lemma pSocleAt_antitone : Antitone (fun α ↦ pSocleAt p α (G := G)) := fun _ _ h ↦
  inf_le_inf_left _ (ulmSubgroup_antitone p h)

lemma pSocleAt_succ_le (α : Ordinal) :
    pSocleAt p (Order.succ α) (G := G) ≤ pSocleAt p α :=
  pSocleAt_antitone p (Order.le_succ α)

lemma pSocleAt_le_pSocle (α : Ordinal) :
    pSocleAt p α (G := G) ≤ pSocle p :=
  inf_le_left

noncomputable instance pSocleZModModule :
    Module (ZMod p) (pSocle p (G := G)) := by
  classical
  refine AddCommGroup.zmodModule (n := p) (G := pSocle p (G := G)) ?_
  intro x
  apply Subtype.ext
  exact x.property

noncomputable instance pSocleAtZModModule (α : Ordinal) :
    Module (ZMod p) (pSocleAt p α (G := G)) := by
  classical
  refine AddCommGroup.zmodModule (n := p) (G := pSocleAt p α (G := G)) ?_
  intro x
  have hx : p • (x : G) = 0 := (mem_pSocleAt p α (x : G)).1 x.property |>.1
  ext
  simp [hx]

/-- `P_{α+1}` viewed as a subgroup of `P_α`. -/
noncomputable def pSocleAtSuccSubgroupOf (α : Ordinal) :
    AddSubgroup (pSocleAt p α (G := G)) :=
  (pSocleAt p (Order.succ α) (G := G)).comap
    (AddSubgroup.subtype (pSocleAt p α))

noncomputable instance pSocleAtQuotModule (α : Ordinal) :
    Module (ZMod p) ((pSocleAt p α (G := G)) ⧸ pSocleAtSuccSubgroupOf p α) := by
  classical
  refine QuotientAddGroup.zmodModule (n := p)
    (G := pSocleAt p α (G := G)) (H := pSocleAtSuccSubgroupOf p α) ?_
  intro x
  have hx' : p • (x : G) = 0 := (mem_pSocleAt p α (x : G)).1 x.property |>.1
  have hx : p • x = 0 := by
    ext
    simp [hx']
  simp [hx]

end SocleLemmas

end UlmsTheorem

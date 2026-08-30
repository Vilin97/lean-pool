/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth
-/

import LeanPool.UlmsTheorem.PGroups.Basic

/-!
# Subgroup-level algebra for reduced abelian p-groups

This file contains the basic subgroup constructions used throughout the
development: the natural-number powers `pPow` and the image-of-multiplication
construction `pImage`.
-/

namespace UlmsTheorem

variable (p : ℕ)

/-! ### Natural-number Ulm subgroups -/

/-- `p^n·G = { p^n • y | y : G }`. -/
def pPow {G : Type*} [AddCommGroup G] (n : ℕ) : AddSubgroup G where
  carrier   := {x | ∃ y : G, p ^ n • y = x}
  zero_mem' := ⟨0, by simp⟩
  add_mem'  := by
    rintro a b ⟨ya, rfl⟩ ⟨yb, rfl⟩
    exact ⟨ya + yb, smul_add (p ^ n) ya yb⟩
  neg_mem'  := by
    rintro a ⟨y, rfl⟩
    exact ⟨-y, smul_neg (p ^ n) y⟩

section PowLemmas

variable {G : Type*} [AddCommGroup G]

@[simp] lemma pPow_mem_iff (x : G) (n : ℕ) :
    x ∈ pPow p n ↔ ∃ y : G, p ^ n • y = x := Iff.rfl

lemma pPow_zero_eq : pPow p 0 (G := G) = ⊤ := by
  ext x
  simp [pow_zero, one_smul]

lemma pPow_succ_le (n : ℕ) : pPow p (n + 1) ≤ pPow p (G := G) n := by
  intro x ⟨y, hy⟩
  exact ⟨p • y, by rw [← hy, pow_succ, mul_smul]⟩

lemma pPow_antitone : Antitone (fun n ↦ pPow p n (G := G)) :=
  antitone_nat_of_succ_le (pPow_succ_le p)

lemma pPow_succ_eq (n : ℕ) :
    (pPow p (G := G) (n + 1) : Set G) = {x | ∃ y ∈ pPow p (G := G) n, p • y = x} := by
  ext x
  simp only [pPow_mem_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨p ^ n • y, ⟨y, rfl⟩, by rw [← hy, smul_smul, mul_comm, ← pow_succ]⟩
  · rintro ⟨z, ⟨w, rfl⟩, hz⟩
    exact ⟨w, by rw [pow_succ, mul_comm, ← smul_smul]; exact hz⟩

end PowLemmas

/-! ### `p`-image of a subgroup -/

/-- `{ p • y | y ∈ H }` as a subgroup of `G`. -/
def pImage {G : Type*} [AddCommGroup G] (H : AddSubgroup G) : AddSubgroup G where
  carrier   := {x | ∃ y ∈ H, p • y = x}
  zero_mem' := ⟨0, H.zero_mem, by simp⟩
  add_mem'  := by
    rintro a b ⟨ya, hya, rfl⟩ ⟨yb, hyb, rfl⟩
    exact ⟨ya + yb, H.add_mem hya hyb, smul_add p ya yb⟩
  neg_mem'  := by
    rintro a ⟨y, hy, rfl⟩
    exact ⟨-y, H.neg_mem hy, smul_neg p y⟩

section PImageLemmas

variable {G : Type*} [AddCommGroup G]

@[simp] lemma mem_pImage (H : AddSubgroup G) (x : G) :
    x ∈ pImage p H ↔ ∃ y ∈ H, p • y = x := Iff.rfl

lemma pImage_pPow (n : ℕ) :
    pImage p (pPow p n (G := G)) = pPow p (n + 1) := by
  ext x
  simp only [mem_pImage, pPow_mem_iff]
  constructor
  · rintro ⟨y, ⟨z, hz⟩, hpy⟩
    exact ⟨z, by rw [← hpy, ← hz, pow_succ, mul_smul, smul_comm]⟩
  · rintro ⟨y, hy⟩
    exact ⟨p ^ n • y, ⟨y, rfl⟩, by rw [← hy, pow_succ, mul_smul, smul_comm]⟩

end PImageLemmas

end UlmsTheorem

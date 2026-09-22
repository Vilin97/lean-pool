/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Finite subfields in a common overfield

Finite fields have a unique subfield of each possible degree inside a fixed
finite overfield.  The form needed for constant extensions is an inclusion of
the ranges of two specified embeddings: if the degree of `A / C` divides the
degree of `B / C`, then the image of `A` lies in the image of `B`.

The proof is elementary and keeps the embeddings explicit.  The image of `B`
already supplies `#B` roots of `X ^ (#B) - X`; the polynomial has at most
`#B` roots.  Divisibility of extension degrees then shows that every element
of the image of `A` is another root of the same polynomial.
-/

open Polynomial

namespace BGS.HasseWeil

noncomputable section

/-- In a common finite overfield, the image of a finite field of degree `d`
is contained in the image of one of degree `n` whenever `d ∣ n` over the
same finite base field. -/
theorem finiteField_fieldRange_le_of_finrank_dvd
    {C A B Ω : Type*}
    [Field C] [Field A] [Field B] [Field Ω]
    [Algebra C A] [Algebra C B] [Algebra C Ω]
    [Finite C] [Finite A] [Finite B] [Finite Ω]
    (f : A →ₐ[C] Ω) (g : B →ₐ[C] Ω)
    (hdiv : Module.finrank C A ∣ Module.finrank C B) :
    f.fieldRange ≤ g.fieldRange := by
  let : Fintype C := Fintype.ofFinite C
  let : Fintype A := Fintype.ofFinite A
  let : Fintype B := Fintype.ofFinite B
  let : Fintype Ω := Fintype.ofFinite Ω
  classical
  let p : Ω[X] := X ^ Fintype.card B - X
  have hcardB : 1 < Fintype.card B := Fintype.one_lt_card
  have hp0 : p ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero Ω hcardB
  have himageRoots : Finset.univ.image g ⊆ p.roots.toFinset := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, -, rfl⟩ := hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0, IsRoot.def]
    simp only [p, eval_sub, eval_pow, eval_X]
    rw [← map_pow, FiniteField.pow_card, sub_self]
  have himageCard : (Finset.univ.image g).card = Fintype.card B := by
    rw [Finset.card_image_iff.mpr]
    · exact Finset.card_univ
    · exact g.injective.injOn
  have hrootsCard : p.roots.toFinset.card ≤ Fintype.card B := by
    calc
      p.roots.toFinset.card ≤ p.roots.card := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := Polynomial.card_roots' p
      _ = Fintype.card B :=
        FiniteField.X_pow_card_sub_X_natDegree_eq Ω hcardB
  have hrootsEq : p.roots.toFinset = Finset.univ.image g := by
    exact (Finset.eq_of_subset_of_card_le himageRoots
      (by simpa [himageCard] using hrootsCard)).symm
  intro y hy
  rw [AlgHom.mem_fieldRange] at hy ⊢
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨k, hk⟩ := hdiv
  have hroot : f x ∈ p.roots := by
    rw [Polynomial.mem_roots hp0, IsRoot.def]
    simp only [p, eval_sub, eval_pow, eval_X]
    rw [Module.card_eq_pow_finrank (K := C) (V := B), hk, pow_mul,
      ← Module.card_eq_pow_finrank (K := C) (V := A)]
    rw [← map_pow, FiniteField.pow_card_pow, sub_self]
  have hmem : f x ∈ Finset.univ.image g := by
    rw [← hrootsEq]
    exact Multiset.mem_toFinset.mpr hroot
  rw [Finset.mem_image] at hmem
  obtain ⟨z, -, hz⟩ := hmem
  exact ⟨z, hz⟩

end

end BGS.HasseWeil

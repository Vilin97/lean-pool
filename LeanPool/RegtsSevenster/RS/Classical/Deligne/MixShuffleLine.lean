/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.MixShuffle

/-!
# Peeling a line summand off a mixed sum

The mixed sum `L.mix p (q + 1)` of `p` copies of the unit and
`q + 1` copies of an odd line decomposes as a binary biproduct
of one line summand and the smaller mixed sum `L.mix p q`.  The
isomorphism is pure index bookkeeping: the first line index is
peeled off and the remaining indices are shifted down by one.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {D : Type u}

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- Shift the line indices of a mixed sum up by one, leaving the
unit indices unchanged. -/
def mixShiftL (p q : ℕ) : Fin p ⊕ Fin q → Fin p ⊕ Fin (q + 1) :=
  Sum.elim Sum.inl (fun j => Sum.inr j.succ)

/-- Shifting an index does not change the associated summand. -/
theorem OddLine.mixShiftL_summand
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D]
    (L : OddLine D) (p q : ℕ)
    (j : Fin p ⊕ Fin q) :
    L.mixFun p (q + 1) (mixShiftL p q j) = L.mixFun p q j := by
  rcases j with i | k <;> rfl

/-- The shift never produces the first line index. -/
theorem mixShiftL_ne_inr_zero (p q : ℕ) (j : Fin p ⊕ Fin q) :
    mixShiftL p q j ≠ Sum.inr 0 := by
  rcases j with i | k
  · simp [mixShiftL]
  · simp [mixShiftL, Fin.succ_ne_zero]

/-- The index shift is injective. -/
theorem mixShiftL_injective (p q : ℕ) :
    Function.Injective (mixShiftL p q) := by
  rintro (i | k) (i' | k') h <;>
    simp only [mixShiftL, Sum.elim_inl, Sum.elim_inr,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
      Fin.succ_inj] at h <;>
    simp [h]

/-- Project a mixed sum onto its first line summand together
with the remaining, downshifted, mixed sum. -/
noncomputable def OddLine.mixLineSuccHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D)
    (p q : ℕ) :
    (⨁ L.mixFun p (q + 1)) ⟶ L.obj ⊞ (⨁ L.mixFun p q) :=
  biprod.lift
    (biproduct.π (L.mixFun p (q + 1)) (Sum.inr 0) ≫
      eqToHom (L.mixFun_inr p (q + 1) 0))
    (biproduct.lift fun j =>
      biproduct.π (L.mixFun p (q + 1)) (mixShiftL p q j) ≫
        eqToHom (L.mixShiftL_summand p q j))

/-- Rebuild a mixed sum from its first line summand and the
remaining, downshifted, mixed sum. -/
noncomputable def OddLine.mixLineSuccInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D)
    (p q : ℕ) :
    L.obj ⊞ (⨁ L.mixFun p q) ⟶ ⨁ L.mixFun p (q + 1) :=
  biprod.desc
    (eqToHom (L.mixFun_inr p (q + 1) 0).symm ≫
      biproduct.ι (L.mixFun p (q + 1)) (Sum.inr 0))
    (biproduct.desc fun j =>
      eqToHom (L.mixShiftL_summand p q j).symm ≫
        biproduct.ι (L.mixFun p (q + 1)) (mixShiftL p q j))

/-- The peeling map restricted to the first line summand is the
left biproduct inclusion. -/
@[reassoc]
theorem OddLine.ι_inr_zero_mixLineSuccHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D)
    (p q : ℕ) :
    biproduct.ι (L.mixFun p (q + 1)) (Sum.inr 0) ≫
        L.mixLineSuccHom p q =
      eqToHom (L.mixFun_inr p (q + 1) 0) ≫ biprod.inl := by
  apply biprod.hom_ext
  · simp only [mixLineSuccHom, Category.assoc, biprod.lift_fst]
    rw [← Category.assoc, biproduct.ι_π_self, Category.id_comp,
      biprod.inl_fst, Category.comp_id]
  · apply biproduct.hom_ext
    intro j
    simp only [mixLineSuccHom, Category.assoc,
      biprod.lift_snd_assoc, biproduct.lift_π,
      biprod.inl_snd_assoc, zero_comp, comp_zero]
    rw [← Category.assoc,
      biproduct.ι_π_ne _ (Ne.symm (mixShiftL_ne_inr_zero p q j)),
      zero_comp]

/-- The peeling map restricted to a shifted summand is the right
inclusion of the corresponding summand of the smaller sum. -/
@[reassoc]
theorem OddLine.ι_mixShiftL_mixLineSuccHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D)
    (p q : ℕ) (j : Fin p ⊕ Fin q) :
    biproduct.ι (L.mixFun p (q + 1)) (mixShiftL p q j) ≫
        L.mixLineSuccHom p q =
      eqToHom (L.mixShiftL_summand p q j) ≫
        biproduct.ι (L.mixFun p q) j ≫ biprod.inr := by
  apply biprod.hom_ext
  · simp only [mixLineSuccHom, Category.assoc, biprod.lift_fst,
      biprod.inr_fst, comp_zero]
    rw [← Category.assoc,
      biproduct.ι_π_ne _ (mixShiftL_ne_inr_zero p q j), zero_comp]
  · apply biproduct.hom_ext
    intro j'
    simp only [mixLineSuccHom, Category.assoc,
      biprod.lift_snd_assoc, biproduct.lift_π,
      biprod.inr_snd_assoc]
    by_cases h : j = j'
    · subst h
      rw [← Category.assoc, biproduct.ι_π_self, Category.id_comp,
        biproduct.ι_π_self, Category.comp_id]
    · rw [← Category.assoc,
        biproduct.ι_π_ne _
          fun hh => h (mixShiftL_injective p q hh),
        zero_comp, biproduct.ι_π_ne _ h, comp_zero]

/-- Every index of the longer mixed sum is either the first line
index or a shifted index. -/
theorem mixShiftL_cases (p q : ℕ) (i : Fin p ⊕ Fin (q + 1)) :
    i = Sum.inr 0 ∨ ∃ j, i = mixShiftL p q j := by
  rcases i with i | k
  · exact Or.inr ⟨Sum.inl i, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ k with h | ⟨k', h⟩
    · exact Or.inl (by rw [h])
    · exact Or.inr ⟨Sum.inr k', by rw [h]; rfl⟩

/-- The peeling map followed by the rebuilding map is the
identity on the longer mixed sum. -/
theorem OddLine.mixLineSucc_hom_inv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (p q : ℕ) :
    L.mixLineSuccHom p q ≫ L.mixLineSuccInv p q =
      𝟙 (⨁ L.mixFun p (q + 1)) := by
  apply biproduct.hom_ext'
  intro i
  rcases mixShiftL_cases p q i with rfl | ⟨j, rfl⟩
  · rw [← Category.assoc, L.ι_inr_zero_mixLineSuccHom p q]
    simp only [mixLineSuccInv, Category.assoc, biprod.inl_desc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Category.comp_id]
  · rw [← Category.assoc, L.ι_mixShiftL_mixLineSuccHom p q j]
    simp only [mixLineSuccInv, Category.assoc, biprod.inr_desc,
      biproduct.ι_desc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Category.comp_id]

/-- The rebuilding map followed by the peeling map is the
identity on the peeled form. -/
theorem OddLine.mixLineSucc_inv_hom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (p q : ℕ) :
    L.mixLineSuccInv p q ≫ L.mixLineSuccHom p q =
      𝟙 (L.obj ⊞ (⨁ L.mixFun p q)) := by
  apply biprod.hom_ext'
  · simp only [mixLineSuccInv, biprod.inl_desc_assoc,
      Category.assoc, L.ι_inr_zero_mixLineSuccHom p q,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Category.comp_id]
  · apply biproduct.hom_ext'
    intro j
    simp only [mixLineSuccInv, Category.assoc,
      biprod.inr_desc_assoc, biproduct.ι_desc_assoc,
      L.ι_mixShiftL_mixLineSuccHom p q, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Peeling one line summand off a mixed sum: the mixed sum of
`p` units and `q + 1` lines is a line plus the mixed sum of `p`
units and `q` lines. -/
noncomputable def OddLine.mixLineSuccIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D)
    (p q : ℕ) :
    L.mix p (q + 1) ≅ L.obj ⊞ L.mix p q where
  hom := L.mixLineSuccHom p q
  inv := L.mixLineSuccInv p q
  hom_inv_id := L.mixLineSucc_hom_inv p q
  inv_hom_id := L.mixLineSucc_inv_hom p q

end RS

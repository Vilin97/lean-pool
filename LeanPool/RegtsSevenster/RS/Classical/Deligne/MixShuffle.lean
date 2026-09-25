/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.Prop29

/-!
# Peeling a unit summand off a mixed sum

The mixed sum `L.mix (p + 1) q` of `p + 1` copies of the unit and
`q` copies of an odd line decomposes as a binary biproduct of one
unit summand and the smaller mixed sum `L.mix p q`.  The
isomorphism is pure index bookkeeping: the first unit index is
peeled off and the remaining indices are shifted down by one.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {D : Type u}

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- Shift the unit indices of a mixed sum up by one, leaving the
line indices unchanged. -/
def mixShift (p q : ℕ) : Fin p ⊕ Fin q → Fin (p + 1) ⊕ Fin q :=
  Sum.elim (fun i => Sum.inl i.succ) Sum.inr

/-- The summand family of the mixed sum: the unit at each `Fin p`
index, the line at each `Fin q` index. -/
abbrev OddLine.mixFun
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D]
    (L : OddLine D) (p q : ℕ)
    (i : Fin p ⊕ Fin q) : D :=
  Sum.elim (fun _ => 𝟙_ D) (fun _ => L.obj) i

/-- Shifting an index does not change the associated summand. -/
theorem OddLine.mixShift_summand
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D]
    (L : OddLine D) (p q : ℕ)
    (j : Fin p ⊕ Fin q) :
    L.mixFun (p + 1) q (mixShift p q j) = L.mixFun p q j := by
  rcases j with i | k <;> rfl

/-- The shift never produces the first unit index. -/
theorem mixShift_ne_inl_zero (p q : ℕ) (j : Fin p ⊕ Fin q) :
    mixShift p q j ≠ Sum.inl 0 := by
  rcases j with i | k
  · simp [mixShift, Fin.succ_ne_zero]
  · simp [mixShift]

/-- The index shift is injective. -/
theorem mixShift_injective (p q : ℕ) :
    Function.Injective (mixShift p q) := by
  rintro (i | k) (i' | k') h <;>
    simp only [mixShift, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, Fin.succ_inj] at h <;>
    simp [h]

/-- Every unit summand of a mixed sum is the unit. -/
theorem OddLine.mixFun_inl
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D]
    (L : OddLine D) (p q : ℕ) (i : Fin p) :
    L.mixFun p q (Sum.inl i) = 𝟙_ D := rfl

/-- Every line summand of a mixed sum is the line. -/
theorem OddLine.mixFun_inr
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D]
    (L : OddLine D) (p q : ℕ) (j : Fin q) :
    L.mixFun p q (Sum.inr j) = L.obj := rfl

/-- Project a mixed sum onto its first unit summand together with
the remaining, downshifted, mixed sum. -/
noncomputable def OddLine.mixSuccHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (p q : ℕ) :
    (⨁ L.mixFun (p + 1) q) ⟶ (𝟙_ D) ⊞ (⨁ L.mixFun p q) :=
  biprod.lift
    (biproduct.π (L.mixFun (p + 1) q) (Sum.inl 0) ≫
      eqToHom (L.mixFun_inl (p + 1) q 0))
    (biproduct.lift fun j =>
      biproduct.π (L.mixFun (p + 1) q) (mixShift p q j) ≫
        eqToHom (L.mixShift_summand p q j))

/-- Rebuild a mixed sum from its first unit summand and the
remaining, downshifted, mixed sum. -/
noncomputable def OddLine.mixSuccInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (p q : ℕ) :
    (𝟙_ D) ⊞ (⨁ L.mixFun p q) ⟶ ⨁ L.mixFun (p + 1) q :=
  biprod.desc
    (eqToHom (L.mixFun_inl (p + 1) q 0).symm ≫
      biproduct.ι (L.mixFun (p + 1) q) (Sum.inl 0))
    (biproduct.desc fun j =>
      eqToHom (L.mixShift_summand p q j).symm ≫
        biproduct.ι (L.mixFun (p + 1) q) (mixShift p q j))

/-- The peeling map restricted to the first unit summand is the
left biproduct inclusion. -/
@[reassoc]
theorem OddLine.ι_zero_mixSuccHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (p q : ℕ) :
    biproduct.ι (L.mixFun (p + 1) q) (Sum.inl 0) ≫
        L.mixSuccHom p q =
      eqToHom (L.mixFun_inl (p + 1) q 0) ≫ biprod.inl := by
  apply biprod.hom_ext
  · simp only [mixSuccHom, Category.assoc, biprod.lift_fst]
    rw [← Category.assoc, biproduct.ι_π_self, Category.id_comp,
      biprod.inl_fst, Category.comp_id]
  · apply biproduct.hom_ext
    intro j
    simp only [mixSuccHom, Category.assoc, biprod.lift_snd_assoc,
      biproduct.lift_π, biprod.inl_snd_assoc, zero_comp, comp_zero]
    rw [← Category.assoc,
      biproduct.ι_π_ne _ (Ne.symm (mixShift_ne_inl_zero p q j)),
      zero_comp]

/-- The peeling map restricted to a shifted summand is the right
inclusion of the corresponding summand of the smaller sum. -/
@[reassoc]
theorem OddLine.ι_mixShift_mixSuccHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (p q : ℕ)
    (j : Fin p ⊕ Fin q) :
    biproduct.ι (L.mixFun (p + 1) q) (mixShift p q j) ≫
        L.mixSuccHom p q =
      eqToHom (L.mixShift_summand p q j) ≫
        biproduct.ι (L.mixFun p q) j ≫ biprod.inr := by
  apply biprod.hom_ext
  · simp only [mixSuccHom, Category.assoc, biprod.lift_fst,
      biprod.inr_fst, comp_zero]
    rw [← Category.assoc,
      biproduct.ι_π_ne _ (mixShift_ne_inl_zero p q j), zero_comp]
  · apply biproduct.hom_ext
    intro j'
    simp only [mixSuccHom, Category.assoc, biprod.lift_snd_assoc,
      biproduct.lift_π, biprod.inr_snd_assoc]
    by_cases h : j = j'
    · subst h
      rw [← Category.assoc, biproduct.ι_π_self, Category.id_comp,
        biproduct.ι_π_self, Category.comp_id]
    · rw [← Category.assoc,
        biproduct.ι_π_ne _ fun hh => h (mixShift_injective p q hh),
        zero_comp, biproduct.ι_π_ne _ h, comp_zero]

/-- Every index of the longer mixed sum is either the first unit
index or a shifted index. -/
theorem mixShift_cases (p q : ℕ) (i : Fin (p + 1) ⊕ Fin q) :
    i = Sum.inl 0 ∨ ∃ j, i = mixShift p q j := by
  rcases i with i | k
  · rcases Fin.eq_zero_or_eq_succ i with h | ⟨i', h⟩
    · exact Or.inl (by rw [h])
    · exact Or.inr ⟨Sum.inl i', by rw [h]; rfl⟩
  · exact Or.inr ⟨Sum.inr k, rfl⟩

/-- The peeling map followed by the rebuilding map is the
identity on the longer mixed sum. -/
theorem OddLine.mixSucc_hom_inv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (p q : ℕ) :
    L.mixSuccHom p q ≫ L.mixSuccInv p q =
      𝟙 (⨁ L.mixFun (p + 1) q) := by
  apply biproduct.hom_ext'
  intro i
  rcases mixShift_cases p q i with rfl | ⟨j, rfl⟩
  · rw [← Category.assoc, L.ι_zero_mixSuccHom p q]
    simp only [mixSuccInv, Category.assoc, biprod.inl_desc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Category.comp_id]
  · rw [← Category.assoc, L.ι_mixShift_mixSuccHom p q j]
    simp only [mixSuccInv, Category.assoc, biprod.inr_desc,
      biproduct.ι_desc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Category.comp_id]

/-- The rebuilding map followed by the peeling map is the
identity on the peeled form. -/
theorem OddLine.mixSucc_inv_hom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (p q : ℕ) :
    L.mixSuccInv p q ≫ L.mixSuccHom p q =
      𝟙 ((𝟙_ D) ⊞ (⨁ L.mixFun p q)) := by
  apply biprod.hom_ext'
  · simp only [mixSuccInv, biprod.inl_desc_assoc, Category.assoc,
      L.ι_zero_mixSuccHom p q, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Category.comp_id]
  · apply biproduct.hom_ext'
    intro j
    simp only [mixSuccInv, Category.assoc, biprod.inr_desc_assoc,
      biproduct.ι_desc_assoc, L.ι_mixShift_mixSuccHom p q,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Category.comp_id]

/-- Peeling one unit summand off a mixed sum: the mixed sum of
`p + 1` units and `q` lines is a unit plus the mixed sum of `p`
units and `q` lines. -/
noncomputable def OddLine.mixSuccIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (p q : ℕ) :
    L.mix (p + 1) q ≅ (𝟙_ D) ⊞ L.mix p q where
  hom := L.mixSuccHom p q
  inv := L.mixSuccInv p q
  hom_inv_id := L.mixSucc_hom_inv p q
  inv_hom_id := L.mixSucc_inv_hom p q

end RS

/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.MixShuffle
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperEmbed

/-!
# Mixed sums as folded biproduct powers

The mixed sum `L.mix (p + 1) (q + 1)` of the dévissage is indexed
by a `Sum` of two `Fin` types.  Splitting the biproduct along the
two injections and folding each constant family into the iterated
binary sum `sumPow` identifies the mixed sum with the object
`sumPow (𝟙_ D) p ⊞ sumPow L.obj q` of the 1.9 layer.  The
nonvanishing of the mixed sum at every diagram avoiding the cell
`(p + 1, q + 1)` then transports across the isomorphism.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {D : Type u}

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- Split a mixed sum into its unit part and its line part. -/
noncomputable def OddLine.mixSplitHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (p q : ℕ) :
    (⨁ L.mixFun (p + 1) (q + 1)) ⟶
      (⨁ fun _ : Fin (p + 1) => 𝟙_ D) ⊞
        (⨁ fun _ : Fin (q + 1) => L.obj) :=
  biprod.lift
    (biproduct.lift fun i =>
      biproduct.π (L.mixFun (p + 1) (q + 1)) (Sum.inl i) ≫
        eqToHom (L.mixFun_inl (p + 1) (q + 1) i))
    (biproduct.lift fun j =>
      biproduct.π (L.mixFun (p + 1) (q + 1)) (Sum.inr j) ≫
        eqToHom (L.mixFun_inr (p + 1) (q + 1) j))

/-- Rebuild a mixed sum from its unit part and its line part. -/
noncomputable def OddLine.mixSplitInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (p q : ℕ) :
    (⨁ fun _ : Fin (p + 1) => 𝟙_ D) ⊞
        (⨁ fun _ : Fin (q + 1) => L.obj) ⟶
      ⨁ L.mixFun (p + 1) (q + 1) :=
  biprod.desc
    (biproduct.desc fun i =>
      eqToHom (L.mixFun_inl (p + 1) (q + 1) i).symm ≫
        biproduct.ι (L.mixFun (p + 1) (q + 1)) (Sum.inl i))
    (biproduct.desc fun j =>
      eqToHom (L.mixFun_inr (p + 1) (q + 1) j).symm ≫
        biproduct.ι (L.mixFun (p + 1) (q + 1)) (Sum.inr j))

/-- The splitting map restricted to a unit summand is the matching
inclusion into the unit part. -/
@[reassoc]
theorem OddLine.ι_inl_mixSplitHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (p q : ℕ)
    (i : Fin (p + 1)) :
    biproduct.ι (L.mixFun (p + 1) (q + 1)) (Sum.inl i) ≫
        L.mixSplitHom p q =
      eqToHom (L.mixFun_inl (p + 1) (q + 1) i) ≫
        biproduct.ι (fun _ : Fin (p + 1) => 𝟙_ D) i ≫
          biprod.inl := by
  apply biprod.hom_ext
  · apply biproduct.hom_ext
    intro i'
    simp only [mixSplitHom, Category.assoc, biprod.lift_fst,
      biproduct.lift_π, biprod.inl_fst, Category.comp_id]
    by_cases h : i = i'
    · subst h
      rw [← Category.assoc, biproduct.ι_π_self, Category.id_comp,
        biproduct.ι_π_self, Category.comp_id]
    · rw [← Category.assoc,
        biproduct.ι_π_ne _ fun hh => h (Sum.inl_injective hh),
        zero_comp, biproduct.ι_π_ne _ h, comp_zero]
  · apply biproduct.hom_ext
    intro j
    simp only [mixSplitHom, Category.assoc, biprod.lift_snd,
      biproduct.lift_π, biprod.inl_snd, comp_zero, zero_comp]
    rw [← Category.assoc, biproduct.ι_π_ne _ Sum.inl_ne_inr,
      zero_comp]

/-- The splitting map restricted to a line summand is the matching
inclusion into the line part. -/
@[reassoc]
theorem OddLine.ι_inr_mixSplitHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (p q : ℕ)
    (j : Fin (q + 1)) :
    biproduct.ι (L.mixFun (p + 1) (q + 1)) (Sum.inr j) ≫
        L.mixSplitHom p q =
      eqToHom (L.mixFun_inr (p + 1) (q + 1) j) ≫
        biproduct.ι (fun _ : Fin (q + 1) => L.obj) j ≫
          biprod.inr := by
  apply biprod.hom_ext
  · apply biproduct.hom_ext
    intro i
    simp only [mixSplitHom, Category.assoc, biprod.lift_fst,
      biproduct.lift_π, biprod.inr_fst, comp_zero, zero_comp]
    rw [← Category.assoc, biproduct.ι_π_ne _ Sum.inr_ne_inl,
      zero_comp]
  · apply biproduct.hom_ext
    intro j'
    simp only [mixSplitHom, Category.assoc, biprod.lift_snd,
      biproduct.lift_π, biprod.inr_snd, Category.comp_id]
    by_cases h : j = j'
    · subst h
      rw [← Category.assoc, biproduct.ι_π_self, Category.id_comp,
        biproduct.ι_π_self, Category.comp_id]
    · rw [← Category.assoc,
        biproduct.ι_π_ne _ fun hh => h (Sum.inr_injective hh),
        zero_comp, biproduct.ι_π_ne _ h, comp_zero]

/-- Splitting then rebuilding is the identity on the mixed sum. -/
theorem OddLine.mixSplit_hom_inv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (p q : ℕ) :
    L.mixSplitHom p q ≫ L.mixSplitInv p q =
      𝟙 (⨁ L.mixFun (p + 1) (q + 1)) := by
  apply biproduct.hom_ext'
  rintro (i | j)
  · rw [← Category.assoc, L.ι_inl_mixSplitHom p q i]
    simp only [mixSplitInv, Category.assoc, biprod.inl_desc,
      biproduct.ι_desc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Category.comp_id]
  · rw [← Category.assoc, L.ι_inr_mixSplitHom p q j]
    simp only [mixSplitInv, Category.assoc, biprod.inr_desc,
      biproduct.ι_desc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Category.comp_id]

/-- Rebuilding then splitting is the identity on the split
form. -/
theorem OddLine.mixSplit_inv_hom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (p q : ℕ) :
    L.mixSplitInv p q ≫ L.mixSplitHom p q =
      𝟙 ((⨁ fun _ : Fin (p + 1) => 𝟙_ D) ⊞
        (⨁ fun _ : Fin (q + 1) => L.obj)) := by
  apply biprod.hom_ext'
  · apply biproduct.hom_ext'
    intro i
    simp only [mixSplitInv, Category.assoc, biprod.inl_desc_assoc,
      biproduct.ι_desc_assoc, L.ι_inl_mixSplitHom p q,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Category.comp_id]
  · apply biproduct.hom_ext'
    intro j
    simp only [mixSplitInv, Category.assoc, biprod.inr_desc_assoc,
      biproduct.ι_desc_assoc, L.ι_inr_mixSplitHom p q,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Category.comp_id]

/-- A mixed sum is the biproduct of its unit part and its line
part. -/
noncomputable def OddLine.mixSplitIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (p q : ℕ) :
    L.mix (p + 1) (q + 1) ≅
      (⨁ fun _ : Fin (p + 1) => 𝟙_ D) ⊞
        (⨁ fun _ : Fin (q + 1) => L.obj) where
  hom := L.mixSplitHom p q
  inv := L.mixSplitInv p q
  hom_inv_id := L.mixSplit_hom_inv p q
  inv_hom_id := L.mixSplit_inv_hom p q

/-- Folding a constant biproduct into the iterated binary sum. -/
noncomputable def constSumIso
    [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]
    (X : D) (k : ℕ) :
    (⨁ fun _ : Fin (k + 1) => X) ≅ sumPow X k where
  hom := biproduct.desc (sumPowIns X k)
  inv := biproduct.lift (sumPowPrj X k)
  hom_inv_id := by
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro i'
    simp only [Category.assoc, biproduct.ι_desc_assoc,
      biproduct.lift_π, Category.id_comp]
    by_cases h : i = i'
    · subst h
      rw [sumPowIns_prj_same X k i, biproduct.ι_π_self]
    · rw [sumPowIns_prj_ne X k h, biproduct.ι_π_ne _ h]
  inv_hom_id := by
    rw [biproduct.lift_desc]
    exact sumPow_total X k

/-- **The mixed sum in fold form**: the mixed sum of `p + 1` units
and `q + 1` lines is the biproduct of the folded unit power and
the folded line power. -/
noncomputable def OddLine.mixSumPowIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (p q : ℕ) :
    L.mix (p + 1) (q + 1) ≅
      sumPow (𝟙_ D) p ⊞ sumPow L.obj q :=
  L.mixSplitIso p q ≪≫
    biprod.mapIso (constSumIso (𝟙_ D) p) (constSumIso L.obj q)

section Killed

/-- **Nonvanishing of the mixed sum**: in a nontrivial ambient
category, the mixed sum of `p + 1` units and `q + 1` odd lines is
not Schur-killed at any diagram avoiding the cell
`(p + 1, q + 1)`. -/
theorem OddLine.not_schurKilled_mix
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [Linear ℂ D]
    [MonoidalPreadditive D] [MonoidalLinear ℂ D]
    (P : SchurPackage.{v})
    (P₀ : SchurPackage.{0}) (hone : ¬ Limits.IsZero (𝟙_ D))
    (L : OddLine D) (p q : ℕ) {lam : YoungDiagram}
    (hcell : ((p + 1, q + 1) : ℕ × ℕ) ∉ lam) :
    ¬ SchurKilled P (L.mix (p + 1) (q + 1)) lam := fun h =>
  not_schurKilled_sum P P₀ hone L.sq L.braid_neg p q hcell
    (SchurKilled.of_iso P (L.mixSumPowIso p q) h)

end Killed

end RS

/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.CatTheory.Length
public import LeanPool.RegtsSevenster.RS.Classical.CatTheory.LinearCategory

/-!
# Length bounded by the endomorphism dimension

In a ℂ-linear semisimple category with finite-dimensional
Hom-spaces, the categorical length of an object is bounded by the
dimension of its endomorphism algebra.  Writing `Y ≅ ⨁ S` with the
`S i` simple over `Fin n`, the biproduct of `n` simple objects has
length at most `n`; and the `n` composites of a projection with
the matching inclusion form pairwise-orthogonal nonzero idempotents
in `End Y`, hence a linearly independent family, so that
`n ≤ dim End Y`.  Monotonicity of the length bound combines the
two halves.
-/

@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u}

/-! ### Length of a biproduct of simple objects -/

/-- The biproduct of a family over `Fin (n + 1)` splits off its
head summand as a binary biproduct with the biproduct of its
tail. -/
private noncomputable def biproductSuccIso [Category.{v} C]
    [Preadditive C]
    [HasFiniteBiproducts C] [HasBinaryBiproducts C] {n : ℕ}
    (S : Fin (n + 1) → C) :
    (⨁ S) ≅ S 0 ⊞ ⨁ (fun j : Fin n => S j.succ) where
  hom := biprod.lift (biproduct.π S 0)
    (biproduct.lift fun j => biproduct.π S j.succ)
  inv := biprod.desc (biproduct.ι S 0)
    (biproduct.desc fun j => biproduct.ι S j.succ)
  hom_inv_id := by
    rw [biprod.lift_desc, biproduct.lift_desc, ← biproduct.total,
      Fin.sum_univ_succ]
  inv_hom_id := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext
      · simp
      · apply biproduct.hom_ext
        intro j
        simp [biproduct.ι_π_ne S (Fin.succ_ne_zero j).symm]
    · apply biprod.hom_ext
      · apply biproduct.hom_ext'
        intro j
        simp [biproduct.ι_π_ne S (Fin.succ_ne_zero j)]
      · apply biproduct.hom_ext'
        intro j
        apply biproduct.hom_ext
        intro k
        by_cases h : j = k
        · subst h; simp
        · simp [biproduct.ι_π_ne S
            (fun hs => h (Fin.succ_injective n hs)),
            biproduct.ι_π_ne _ h]

/-- A biproduct of `n` simple objects has length at most `n`. -/
theorem lengthLE_biproduct_of_simple [Category.{v} C]
    [Abelian C] [HasFiniteBiproducts C]
    {n : ℕ} (S : Fin n → C) (hS : ∀ i, Simple (S i)) :
    LengthLE (⨁ S) n := by
  induction n with
  | zero =>
    refine lengthLE_of_isZero ?_
    rw [IsZero.iff_id_eq_zero]
    exact biproduct.hom_ext _ _ fun j => j.elim0
  | succ n ih =>
    have := hS 0
    have htail := ih (fun j => S j.succ) fun j => hS j.succ
    exact ((lengthLE_of_simple.biprod htail).of_iso
      (biproductSuccIso S).symm).mono (by omega)

/-! ### Counting orthogonal idempotents -/

/-- Pairwise-orthogonal nonzero idempotent endomorphisms are
linearly independent over ℂ. -/
private lemma linearIndependent_of_orthogonal_idempotents [Category.{v} C]
    [Preadditive C] [Linear ℂ C] {Y : C} {n : ℕ}
    (p : Fin n → (Y ⟶ Y)) (hne : ∀ i, p i ≠ 0)
    (hidem : ∀ i, p i ≫ p i = p i)
    (horth : ∀ i j, i ≠ j → p i ≫ p j = 0) :
    LinearIndependent ℂ p := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h0 : (∑ i, g i • p i) ≫ p j = 0 := by
    rw [hg]; exact zero_comp
  rw [Preadditive.sum_comp] at h0
  have hterm : ∀ i, (g i • p i) ≫ p j =
      if i = j then g j • p j else 0 := by
    intro i
    by_cases h : i = j
    · subst h
      rw [ite_eq_left rfl, Linear.smul_comp, hidem]
    · rw [ite_eq_right h, Linear.smul_comp, horth i j h, smul_zero]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_eq'
    Finset.univ j fun _ => g j • p j, ite_eq_left (Finset.mem_univ j)] at h0
  by_contra hgj
  exact hne j (by
    rw [← one_smul ℂ (p j), ← inv_mul_cancel₀ hgj, mul_smul, h0,
      smul_zero])

/-- An object isomorphic to a biproduct of `n` simple objects has
`n` pairwise-orthogonal nonzero idempotent endomorphisms, so `n`
is at most the dimension of its endomorphism algebra. -/
private lemma card_le_finrank_end [Category.{v} C]
    [Preadditive C] [Linear ℂ C]
    [HasFiniteBiproducts C] {Y : C} {n : ℕ} {S : Fin n → C}
    (hS : ∀ i, Simple (S i)) (e : Y ≅ ⨁ S)
    (hfd : FiniteDimensional ℂ (End Y)) :
    n ≤ Module.finrank ℂ (End Y) := by
  set p : Fin n → (Y ⟶ Y) := fun i =>
    e.hom ≫ biproduct.π S i ≫ biproduct.ι S i ≫ e.inv with hp
  have hidem : ∀ i, p i ≫ p i = p i := by
    intro i
    simp [hp]
  have horth : ∀ i j, i ≠ j → p i ≫ p j = 0 := by
    intro i j hij
    simp [hp, biproduct.ι_π_ne_assoc S hij]
  have hne : ∀ i, p i ≠ 0 := by
    intro i hzero
    have := hS i
    apply id_nonzero (S i)
    have hcalc : (biproduct.ι S i ≫ e.inv) ≫ p i ≫
        (e.hom ≫ biproduct.π S i) = 𝟙 (S i) := by
      simp [hp]
    rw [hzero, zero_comp, comp_zero] at hcalc
    exact hcalc.symm
  have hli :=
    linearIndependent_of_orthogonal_idempotents p hne hidem horth
  have : FiniteDimensional ℂ (Y ⟶ Y) := hfd
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  exact hcard

/-! ### Reconciling independently supplied structures

A category may carry its preadditive and its abelian structure as
independent instances — the envelope of the development does.  The
two then disagree on which zero-morphism structure to use, and a
hypothesis stated over one does not typecheck against a lemma stated
over the other.  Zero-morphism structures are unique, so the
abelian structure can be rebuilt over a prescribed preadditive one:
everything abelianness adds beyond preadditivity is `Prop`-valued
data that transports along that uniqueness.
-/

/-- The abelian structure rebuilt over a prescribed preadditive
structure. -/
@[reducible]
private def abelianOver [Category.{v} C]
    [hpre : Preadditive C] (hab : Abelian C) :
    Abelian C :=
  have hzero :
      @Preadditive.preadditiveHasZeroMorphisms C _ hab.toPreadditive =
        @Preadditive.preadditiveHasZeroMorphisms C _ hpre :=
    Subsingleton.elim _ _
  { toPreadditive := hpre
    toIsNormalMonoCategory := hzero ▸ hab.toIsNormalMonoCategory
    toIsNormalEpiCategory := hzero ▸ hab.toIsNormalEpiCategory
    has_finite_products := hab.has_finite_products
    has_kernels := hzero ▸ hab.has_kernels
    has_cokernels := hzero ▸ hab.has_cokernels }

/-! ### The bound -/

/-- **Length is bounded by the endomorphism dimension**: in a
ℂ-linear semisimple category with finite-dimensional Hom-spaces,
every object `Y` satisfies the length bound at `dim End Y`.  The
semisimplicity and finiteness hypotheses are read over the
preadditive structure, and the abelian structure is rebuilt over it
so that the two halves compose. -/
theorem lengthLE_finrank_end [Category.{v} C]
    [Preadditive C] [Linear ℂ C]
    [HasFiniteBiproducts C] (hab : Abelian C)
    (hss : IsSemisimple C) (hfd : HasFinDimHom C) (Y : C) :
    LengthLE Y (Module.finrank ℂ (End Y)) := by
  obtain ⟨n, S, hS, ⟨e⟩⟩ := hss Y
  have hfin : FiniteDimensional ℂ (End Y) := hfd Y Y
  let : Abelian C := abelianOver hab
  exact ((lengthLE_biproduct_of_simple S hS).of_iso e.symm).mono
    (card_le_finrank_end hS e hfin)

end RS

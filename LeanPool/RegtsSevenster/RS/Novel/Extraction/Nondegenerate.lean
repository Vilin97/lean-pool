/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Extraction.Coordinates

/-!
# Nondegeneracy from the snake identities

A form `b : V ⊗ V ⟶ 𝟙` admitting a copairing `C : 𝟙 ⟶ V ⊗ V`
with the two snake identities has nondegenerate blocks — the
hypothesis shape produced by rigidity, and the hypothesis shape
consumed by `exists_coordinates`.

The route: writing the copairing's even element as a pair of
finite sums of pure tensors (`TensorProduct.exists_finset`), the
two snake identities evaluated on generators become four
*contraction identities* (`exists_contraction_families`):

* `∀ x, Σ_{(m,n)} b(x, m) • n = x` and
  `∀ x, Σ_{(m,n)} b(n, x) • m = x` on the even block,
* the same two identities on the odd block.

Each identity forces the corresponding separation property, so
the even block separates on the left and the odd block is
nondegenerate (`blocks_nondegenerate_of_snake`), and the graded
coordinate identification follows unconditionally
(`exists_coordinates_of_snake`).
-/

noncomputable section

namespace RS

open CategoryTheory
open scoped TensorProduct
open LinearMap (BilinForm)

/-! ### Reduced views of the remaining morphism components -/

/-- The odd component of a form morphism, with its domain and
codomain presented in reduced form. -/
def formOddMap {V : SuperVect}
    (b : SuperVect.Hom (SuperVect.tensorObj V V) SuperVect.tensorUnit) :
    ((V.even ⊗[ℂ] V.odd) × (V.odd ⊗[ℂ] V.even)) →ₗ[ℂ] PUnit :=
  b.oddMap

/-- The even component of a copairing morphism `𝟙 ⟶ V ⊗ V`, with
its domain and codomain presented in reduced form. -/
def formCoevMap {V : SuperVect}
    (C : SuperVect.Hom SuperVect.tensorUnit (SuperVect.tensorObj V V)) :
    ℂ →ₗ[ℂ] ((V.even ⊗[ℂ] V.even) × (V.odd ⊗[ℂ] V.odd)) :=
  C.evenMap

/-- The odd component of a copairing morphism, with its domain and
codomain presented in reduced form. -/
def formCoevOddMap {V : SuperVect}
    (C : SuperVect.Hom SuperVect.tensorUnit (SuperVect.tensorObj V V)) :
    PUnit →ₗ[ℂ] ((V.even ⊗[ℂ] V.odd) × (V.odd ⊗[ℂ] V.even)) :=
  C.oddMap

/-! ### The contraction identities

The sum-shuffling these proofs run on -- pushing a finite sum
through a bound map, splitting it across the summands of a
product -- is `Common/ProdSum.lean`; the maps there are bound so
that instance search never meets a metavariable. -/

open MonoidalCategory in
/-- **Contraction families from the snake identities**
(accompanying paper §5.2): the even copairing element decomposes as
finite
sums of pure tensors over each graded block, and the two snake
identities become the four contraction identities relating those
families to the blocks of the form. -/
theorem exists_contraction_families {V : SuperVect}
    (b : SuperVect.Hom (SuperVect.tensorObj V V) SuperVect.tensorUnit)
    (C : SuperVect.Hom SuperVect.tensorUnit (SuperVect.tensorObj V V))
    (h1 : V ◁ (show 𝟙_ SuperVect ⟶ V ⊗ V from C) ≫
        (α_ V V V).inv ≫
        (show V ⊗ V ⟶ 𝟙_ SuperVect from b) ▷ V =
        (ρ_ V).hom ≫ (λ_ V).inv)
    (h2 : (show 𝟙_ SuperVect ⟶ V ⊗ V from C) ▷ V ≫
        (α_ V V V).hom ≫
        V ◁ (show V ⊗ V ⟶ 𝟙_ SuperVect from b) =
        (λ_ V).hom ≫ (ρ_ V).inv) :
    ∃ (S : Finset (V.even × V.even)) (T : Finset (V.odd × V.odd)),
      ((formCoevMap C) 1).1 = (∑ i ∈ S, i.1 ⊗ₜ[ℂ] i.2) ∧
      ((formCoevMap C) 1).2 = (∑ i ∈ T, i.1 ⊗ₜ[ℂ] i.2) ∧
      (∀ x, ∑ i ∈ S, formEvenBlock b x i.1 • i.2 = x) ∧
      (∀ x, ∑ i ∈ S, formEvenBlock b i.2 x • i.1 = x) ∧
      (∀ x, ∑ i ∈ T, formOddBlock b x i.1 • i.2 = x) ∧
      (∀ x, ∑ i ∈ T, formOddBlock b i.2 x • i.1 = x) := by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset ((formCoevMap C) 1).1
  obtain ⟨T, hT⟩ := TensorProduct.exists_finset ((formCoevMap C) 1).2
  have htC : formCoevMap C 1 =
      (∑ i ∈ S, i.1 ⊗ₜ[ℂ] i.2, ∑ i ∈ T, i.1 ⊗ₜ[ℂ] i.2) := by
    rw [← hS, ← hT]
  -- ═══════ THE FOUR CONTRACTION IDENTITIES ═══════
  -- Each snake identity, evaluated on a generator of one graded
  -- block, gives one of the four.
  refine ⟨S, T, hS, hT, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · -- (i) even, from h1: Σ b(x, m) • n = x
    have h := congrArg SuperVect.Hom.evenMap h1
    have hx := LinearMap.congr_fun h
      ((x ⊗ₜ[ℂ] (1 : ℂ), 0) : (V.even ⊗[ℂ] ℂ) × (V.odd ⊗[ℂ] PUnit.{1}))
    have hx' :
        (LinearMap.prodMap
            (TensorProduct.map (formEvenMap b) LinearMap.id)
            (TensorProduct.map (formOddMap b) LinearMap.id))
          ((SuperVect.assocAux V.even V.odd V.even V.odd
              V.even V.odd).symm
            ((LinearMap.prodMap
                (TensorProduct.map LinearMap.id (formCoevMap C))
                (TensorProduct.map LinearMap.id (formCoevOddMap C)))
              ((x ⊗ₜ[ℂ] (1 : ℂ), 0) :
                (V.even ⊗[ℂ] ℂ) × (V.odd ⊗[ℂ] PUnit.{1})))) =
        (LinearMap.inl ℂ (ℂ ⊗[ℂ] V.even) (PUnit.{1} ⊗[ℂ] V.odd))
          ((TensorProduct.lid ℂ V.even).symm
            ((TensorProduct.rid ℂ V.even)
              ((LinearMap.fst ℂ (V.even ⊗[ℂ] ℂ) (V.odd ⊗[ℂ] PUnit.{1}))
                (x ⊗ₜ[ℂ] (1 : ℂ), 0)))) := hx
    simp only [LinearMap.prodMap_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, lmap_zero, LinearMap.fst_apply,
      TensorProduct.rid_tmul, one_smul, TensorProduct.lid_symm_apply,
      LinearMap.inl_apply] at hx'
    rw [htC, mk_sum_split, TensorProduct.tmul_add,
      TensorProduct.tmul_sum, TensorProduct.tmul_sum,
      mk_add_left, mk_sum_left, mk_sum_left] at hx'
    simp only [equiv_add, equiv_sum, SuperVect.assocAux_symm_ee,
      SuperVect.assocAux_symm_eo] at hx'
    have h1st := congrArg Prod.fst hx'
    simp only [Prod.fst_add, Prod.fst_sum, Finset.sum_const_zero,
      add_zero, lmap_sum, TensorProduct.map_tmul,
      LinearMap.id_apply] at h1st
    have hfin := congrArg (TensorProduct.lid ℂ V.even) h1st
    simp only [equiv_sum, TensorProduct.lid_tmul, one_smul] at hfin
    exact hfin
  · -- (ii) even, from h2: Σ b(n, x) • m = x
    have h := congrArg SuperVect.Hom.evenMap h2
    have hx := LinearMap.congr_fun h
      (((1 : ℂ) ⊗ₜ[ℂ] x, 0) : (ℂ ⊗[ℂ] V.even) × (PUnit.{1} ⊗[ℂ] V.odd))
    have hx' :
        (LinearMap.prodMap
            (TensorProduct.map LinearMap.id (formEvenMap b))
            (TensorProduct.map LinearMap.id (formOddMap b)))
          ((SuperVect.assocAux V.even V.odd V.even V.odd
              V.even V.odd)
            ((LinearMap.prodMap
                (TensorProduct.map (formCoevMap C) LinearMap.id)
                (TensorProduct.map (formCoevOddMap C) LinearMap.id))
              (((1 : ℂ) ⊗ₜ[ℂ] x, 0) :
                (ℂ ⊗[ℂ] V.even) × (PUnit.{1} ⊗[ℂ] V.odd)))) =
        (LinearMap.inl ℂ (V.even ⊗[ℂ] ℂ) (V.odd ⊗[ℂ] PUnit.{1}))
          ((TensorProduct.rid ℂ V.even).symm
            ((TensorProduct.lid ℂ V.even)
              ((LinearMap.fst ℂ (ℂ ⊗[ℂ] V.even) (PUnit.{1} ⊗[ℂ] V.odd))
                ((1 : ℂ) ⊗ₜ[ℂ] x, 0)))) := hx
    simp only [LinearMap.prodMap_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, lmap_zero, LinearMap.fst_apply,
      TensorProduct.lid_tmul, one_smul, TensorProduct.rid_symm_apply,
      LinearMap.inl_apply] at hx'
    rw [htC, mk_sum_split, TensorProduct.add_tmul,
      TensorProduct.sum_tmul, TensorProduct.sum_tmul,
      mk_add_left, mk_sum_left, mk_sum_left] at hx'
    simp only [equiv_add, equiv_sum, SuperVect.assocAux_ee,
      SuperVect.assocAux_oo] at hx'
    have h1st := congrArg Prod.fst hx'
    simp only [Prod.fst_add, Prod.fst_sum, Finset.sum_const_zero,
      add_zero, lmap_sum, TensorProduct.map_tmul,
      LinearMap.id_apply] at h1st
    have hfin := congrArg (TensorProduct.rid ℂ V.even) h1st
    simp only [equiv_sum, TensorProduct.rid_tmul, one_smul] at hfin
    exact hfin
  · -- (iii) odd, from h1: Σ b(x, p) • q = x
    have h := congrArg SuperVect.Hom.oddMap h1
    have hx := LinearMap.congr_fun h
      ((0, x ⊗ₜ[ℂ] (1 : ℂ)) : (V.even ⊗[ℂ] PUnit.{1}) × (V.odd ⊗[ℂ] ℂ))
    have hx' :
        (LinearMap.prodMap
            (TensorProduct.map (formEvenMap b) LinearMap.id)
            (TensorProduct.map (formOddMap b) LinearMap.id))
          ((SuperVect.assocAux V.even V.odd V.even V.odd
              V.odd V.even).symm
            ((LinearMap.prodMap
                (TensorProduct.map LinearMap.id (formCoevOddMap C))
                (TensorProduct.map LinearMap.id (formCoevMap C)))
              ((0, x ⊗ₜ[ℂ] (1 : ℂ)) :
                (V.even ⊗[ℂ] PUnit.{1}) × (V.odd ⊗[ℂ] ℂ)))) =
        (LinearMap.inl ℂ (ℂ ⊗[ℂ] V.odd) (PUnit.{1} ⊗[ℂ] V.even))
          ((TensorProduct.lid ℂ V.odd).symm
            ((TensorProduct.rid ℂ V.odd)
              ((LinearMap.snd ℂ (V.even ⊗[ℂ] PUnit.{1}) (V.odd ⊗[ℂ] ℂ))
                (0, x ⊗ₜ[ℂ] (1 : ℂ))))) := hx
    simp only [LinearMap.prodMap_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, lmap_zero, LinearMap.snd_apply,
      TensorProduct.rid_tmul, one_smul, TensorProduct.lid_symm_apply,
      LinearMap.inl_apply] at hx'
    rw [htC, mk_sum_split, TensorProduct.tmul_add,
      TensorProduct.tmul_sum, TensorProduct.tmul_sum,
      mk_add_right, mk_sum_right, mk_sum_right] at hx'
    simp only [equiv_add, equiv_sum, SuperVect.assocAux_symm_oe,
      SuperVect.assocAux_symm_oo] at hx'
    have h1st := congrArg Prod.fst hx'
    simp only [Prod.fst_add, Prod.fst_sum, Finset.sum_const_zero,
      zero_add, lmap_sum, TensorProduct.map_tmul,
      LinearMap.id_apply] at h1st
    have hfin := congrArg (TensorProduct.lid ℂ V.odd) h1st
    simp only [equiv_sum, TensorProduct.lid_tmul, one_smul] at hfin
    exact hfin
  · -- (iv) odd, from h2: Σ b(q, x) • p = x
    have h := congrArg SuperVect.Hom.oddMap h2
    have hx := LinearMap.congr_fun h
      (((1 : ℂ) ⊗ₜ[ℂ] x, 0) : (ℂ ⊗[ℂ] V.odd) × (PUnit.{1} ⊗[ℂ] V.even))
    have hx' :
        (LinearMap.prodMap
            (TensorProduct.map LinearMap.id (formOddMap b))
            (TensorProduct.map LinearMap.id (formEvenMap b)))
          ((SuperVect.assocAux V.even V.odd V.even V.odd
              V.odd V.even)
            ((LinearMap.prodMap
                (TensorProduct.map (formCoevMap C) LinearMap.id)
                (TensorProduct.map (formCoevOddMap C) LinearMap.id))
              (((1 : ℂ) ⊗ₜ[ℂ] x, 0) :
                (ℂ ⊗[ℂ] V.odd) × (PUnit.{1} ⊗[ℂ] V.even)))) =
        (LinearMap.inr ℂ (V.even ⊗[ℂ] PUnit.{1}) (V.odd ⊗[ℂ] ℂ))
          ((TensorProduct.rid ℂ V.odd).symm
            ((TensorProduct.lid ℂ V.odd)
              ((LinearMap.fst ℂ (ℂ ⊗[ℂ] V.odd) (PUnit.{1} ⊗[ℂ] V.even))
                ((1 : ℂ) ⊗ₜ[ℂ] x, 0)))) := hx
    simp only [LinearMap.prodMap_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, lmap_zero, LinearMap.fst_apply,
      TensorProduct.lid_tmul, one_smul, TensorProduct.rid_symm_apply,
      LinearMap.inr_apply] at hx'
    rw [htC, mk_sum_split, TensorProduct.add_tmul,
      TensorProduct.sum_tmul, TensorProduct.sum_tmul,
      mk_add_left, mk_sum_left, mk_sum_left] at hx'
    simp only [equiv_add, equiv_sum, SuperVect.assocAux_ee,
      SuperVect.assocAux_oo] at hx'
    have h2nd := congrArg Prod.snd hx'
    simp only [Prod.snd_add, Prod.snd_sum, Finset.sum_const_zero,
      zero_add, lmap_sum, TensorProduct.map_tmul,
      LinearMap.id_apply] at h2nd
    have hfin := congrArg (TensorProduct.rid ℂ V.odd) h2nd
    simp only [equiv_sum, TensorProduct.rid_tmul, one_smul] at hfin
    exact hfin

/-! ### Nondegeneracy of the blocks -/

open MonoidalCategory in
/-- **Nondegeneracy from the snake identities**: the even block
separates on the left and the odd block is nondegenerate —
exactly the hypotheses of `exists_coordinates`. -/
theorem blocks_nondegenerate_of_snake {V : SuperVect}
    (b : SuperVect.Hom (SuperVect.tensorObj V V) SuperVect.tensorUnit)
    (C : SuperVect.Hom SuperVect.tensorUnit (SuperVect.tensorObj V V))
    (h1 : V ◁ (show 𝟙_ SuperVect ⟶ V ⊗ V from C) ≫
        (α_ V V V).inv ≫
        (show V ⊗ V ⟶ 𝟙_ SuperVect from b) ▷ V =
        (ρ_ V).hom ≫ (λ_ V).inv)
    (h2 : (show 𝟙_ SuperVect ⟶ V ⊗ V from C) ▷ V ≫
        (α_ V V V).hom ≫
        V ◁ (show V ⊗ V ⟶ 𝟙_ SuperVect from b) =
        (λ_ V).hom ≫ (ρ_ V).inv) :
    (∀ x, (∀ y, formEvenBlock b x y = 0) → x = 0) ∧
      (formOddBlock b).Nondegenerate := by
  obtain ⟨S, T, _, _, hi, _, hiii, hiv⟩ :=
    exists_contraction_families b C h1 h2
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have h := hi x
    rw [Finset.sum_eq_zero (fun i _ => by rw [hx i.1, zero_smul])] at h
    exact h.symm
  · have h := hiii x
    rw [Finset.sum_eq_zero (fun i _ => by rw [hx i.1, zero_smul])] at h
    exact h.symm
  · have h := hiv x
    rw [Finset.sum_eq_zero (fun i _ => by rw [hx i.2, zero_smul])] at h
    exact h.symm

/-! ### The unconditional coordinate identification -/

open MonoidalCategory in
/-- **Standard coordinates from rigidity** (accompanying paper §5.1): a
super
vector space with a supersymmetric form admitting a copairing
with the snake identities carries graded coordinates taking the
form's blocks to the standard forms. -/
theorem exists_coordinates_of_snake {V : SuperVect}
    (b : SuperVect.Hom (SuperVect.tensorObj V V) SuperVect.tensorUnit)
    (C : SuperVect.Hom SuperVect.tensorUnit (SuperVect.tensorObj V V))
    (hb : SuperVect.Hom.comp b (SuperVect.koszulBraiding V V) = b)
    (h1 : V ◁ (show 𝟙_ SuperVect ⟶ V ⊗ V from C) ≫
        (α_ V V V).inv ≫
        (show V ⊗ V ⟶ 𝟙_ SuperVect from b) ▷ V =
        (ρ_ V).hom ≫ (λ_ V).inv)
    (h2 : (show 𝟙_ SuperVect ⟶ V ⊗ V from C) ▷ V ≫
        (α_ V V V).hom ≫
        V ◁ (show V ⊗ V ⟶ 𝟙_ SuperVect from b) =
        (λ_ V).hom ≫ (ρ_ V).inv) :
    ∃ (k ℓ : ℕ) (eE : (Fin k → ℂ) ≃ₗ[ℂ] V.even)
      (eO : (Fin (2 * ℓ) → ℂ) ≃ₗ[ℂ] V.odd),
      (∀ x y, formEvenBlock b (eE x) (eE y) = stdFormEven k x y) ∧
      (∀ x y, formOddBlock b (eO x) (eO y) = stdFormOdd ℓ x y) := by
  obtain ⟨hE, hO⟩ := blocks_nondegenerate_of_snake b C h1 h2
  exact exists_coordinates b hb hE hO

end RS

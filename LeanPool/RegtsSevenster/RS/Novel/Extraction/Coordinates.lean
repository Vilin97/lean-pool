/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Super.OrthonormalBasis
import LeanPool.RegtsSevenster.RS.Classical.Super.SymplecticBasis
import LeanPool.RegtsSevenster.RS.Novel.Extraction.StdDuality

/-!
# Standard orthosymplectic coordinates

The coordinate-identification step of §5.1: a super vector space `V`
carrying a supersymmetric nondegenerate form `b : V ⊗ V ⟶ 𝟙` is
isomorphic, as a graded space with form, to the standard model
`stdSuperPair k ℓ` with the standard form.

The route:

* `formEvenBlock` / `formOddBlock` extract the two bilinear blocks
  of the even component of `b` (the mixed blocks land in the odd
  component, which is zero).
* Supersymmetry `b ∘ β = b` makes the even block symmetric and the
  odd block alternating (`formEvenBlock_symm`, `formOddBlock_isAlt`)
  — the Koszul sign on the odd⊗odd summand is exactly the
  antisymmetry.
* `exists_even_coordinates` and `exists_odd_coordinates` convert
  the orthonormal- and symplectic-basis theorems into linear
  coordinate equivalences carrying each block to `stdFormEven` /
  `stdFormOdd`.
* `exists_coordinates` assembles the graded statement.
-/

noncomputable section

namespace RS

open scoped TensorProduct
open LinearMap (BilinForm)
open Module

/-! ### The bilinear blocks of a form morphism -/

/-- The even component of a form morphism `V ⊗ V ⟶ 𝟙`, with its
domain and codomain presented in reduced form. -/
def formEvenMap {V : SuperVect}
    (b : SuperVect.Hom (SuperVect.tensorObj V V) SuperVect.tensorUnit) :
    ((V.even ⊗[ℂ] V.even) × (V.odd ⊗[ℂ] V.odd)) →ₗ[ℂ] ℂ :=
  b.evenMap

/-- The even block of a form morphism, as a bilinear form on
`V.even`. -/
def formEvenBlock {V : SuperVect}
    (b : SuperVect.Hom (SuperVect.tensorObj V V) SuperVect.tensorUnit) :
    BilinForm ℂ V.even :=
  TensorProduct.curry ((formEvenMap b).comp (LinearMap.inl ℂ _ _))

/-- The odd block of a form morphism, as a bilinear form on
`V.odd`. -/
def formOddBlock {V : SuperVect}
    (b : SuperVect.Hom (SuperVect.tensorObj V V) SuperVect.tensorUnit) :
    BilinForm ℂ V.odd :=
  TensorProduct.curry ((formEvenMap b).comp (LinearMap.inr ℂ _ _))

/-- The even block evaluates the even map on the even⊗even
summand. -/
theorem formEvenBlock_apply {V : SuperVect}
    (b : SuperVect.Hom (SuperVect.tensorObj V V) SuperVect.tensorUnit)
    (x y : V.even) :
    formEvenBlock b x y = formEvenMap b (x ⊗ₜ[ℂ] y, 0) := rfl

/-- The odd block evaluates the even map on the odd⊗odd summand. -/
theorem formOddBlock_apply {V : SuperVect}
    (b : SuperVect.Hom (SuperVect.tensorObj V V) SuperVect.tensorUnit)
    (x y : V.odd) :
    formOddBlock b x y = formEvenMap b (0, x ⊗ₜ[ℂ] y) := rfl

/-! ### Supersymmetry makes the blocks symmetric and alternating -/

/-- Supersymmetry restricted to the even block: the even map
absorbs the Koszul braiding, whose even⊗even component is the
plain swap. -/
theorem formEvenBlock_symm {V : SuperVect}
    (b : SuperVect.Hom (SuperVect.tensorObj V V) SuperVect.tensorUnit)
    (hb : SuperVect.Hom.comp b (SuperVect.koszulBraiding V V) = b)
    (x y : V.even) :
    formEvenBlock b x y = formEvenBlock b y x := by
  have he : (formEvenMap b).comp
      (SuperVect.koszulEvenAux V.even V.even V.odd V.odd) =
      formEvenMap b :=
    congrArg SuperVect.Hom.evenMap hb
  have hxy := LinearMap.congr_fun he
    ((y ⊗ₜ[ℂ] x, 0) : (V.even ⊗[ℂ] V.even) × (V.odd ⊗[ℂ] V.odd))
  rw [LinearMap.comp_apply, SuperVect.koszulEvenAux_fst] at hxy
  rw [formEvenBlock_apply, formEvenBlock_apply, hxy]

/-- Supersymmetry restricted to the odd block: the Koszul sign on
the odd⊗odd summand makes the block skew-symmetric. -/
theorem formOddBlock_skew {V : SuperVect}
    (b : SuperVect.Hom (SuperVect.tensorObj V V) SuperVect.tensorUnit)
    (hb : SuperVect.Hom.comp b (SuperVect.koszulBraiding V V) = b)
    (x y : V.odd) :
    formOddBlock b x y = -formOddBlock b y x := by
  have he : (formEvenMap b).comp
      (SuperVect.koszulEvenAux V.even V.even V.odd V.odd) =
      formEvenMap b :=
    congrArg SuperVect.Hom.evenMap hb
  have hxy := LinearMap.congr_fun he
    ((0, y ⊗ₜ[ℂ] x) : (V.even ⊗[ℂ] V.even) × (V.odd ⊗[ℂ] V.odd))
  rw [LinearMap.comp_apply, SuperVect.koszulEvenAux_snd, map_neg] at hxy
  rw [formOddBlock_apply, formOddBlock_apply, ← hxy, neg_neg]

/-- The odd block of a supersymmetric form is alternating. -/
theorem formOddBlock_isAlt {V : SuperVect}
    (b : SuperVect.Hom (SuperVect.tensorObj V V) SuperVect.tensorUnit)
    (hb : SuperVect.Hom.comp b (SuperVect.koszulBraiding V V) = b) :
    (formOddBlock b).IsAlt := by
  intro x
  have h := formOddBlock_skew b hb x x
  have h2 : (2 : ℂ) * formOddBlock b x x = 0 := by
    rw [two_mul]
    nth_rewrite 1 [h]
    rw [neg_add_cancel]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 two_ne_zero
  · exact h3

/-! ### The symplectic normal form matches the standard odd form -/

/-- The symplectic normal-form matrix delivered by
`exists_symplectic_basis` equals the partner/sign matrix of
`stdFormOdd`. -/
theorem symplecticMatrix_eq_std (ℓ : ℕ) (i j : Fin (2 * ℓ)) :
    (if (i : ℕ) + ℓ = (j : ℕ) then (1 : ℂ)
      else if (j : ℕ) + ℓ = (i : ℕ) then -1 else 0) =
      if j = oddPartner ℓ i then -(oddPartnerSign ℓ i : ℂ) else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  have hpart : (j = oddPartner ℓ i) ↔
      ((i : ℕ) + ℓ = (j : ℕ) ∨ (j : ℕ) + ℓ = (i : ℕ)) := by
    unfold oddPartner
    rcases Nat.lt_or_ge i.val ℓ with h | h
    · rw [dite_eq_left h]
      constructor
      · intro hh
        have h2 : (j : ℕ) = i.val + ℓ := congrArg Fin.val hh
        omega
      · intro hh
        refine Fin.ext ?_
        change (j : ℕ) = i.val + ℓ
        omega
    · rw [dite_eq_right (Nat.not_lt.mpr h)]
      constructor
      · intro hh
        have h2 : (j : ℕ) = i.val - ℓ := congrArg Fin.val hh
        omega
      · intro hh
        refine Fin.ext ?_
        change (j : ℕ) = i.val - ℓ
        omega
  by_cases hp : j = oddPartner ℓ i
  · rw [ite_eq_left hp]
    unfold oddPartnerSign
    rcases hpart.mp hp with h1 | h1
    · rw [ite_eq_left h1, ite_eq_left (show i.val < ℓ by omega)]
      norm_num
    · rw [ite_eq_right (show ¬ (i : ℕ) + ℓ = (j : ℕ) by omega), ite_eq_left h1,
        ite_eq_right (show ¬ i.val < ℓ by omega)]
      norm_num
  · rw [ite_eq_right hp,
      ite_eq_right (fun hh => hp (hpart.mpr (Or.inl hh))),
      ite_eq_right (fun hh => hp (hpart.mpr (Or.inr hh)))]

/-! ### Coordinates for the two blocks -/

/-- **Even coordinates**: a symmetric nondegenerate bilinear form
is carried to the standard even form by the coordinate
equivalence of an orthonormal basis. -/
theorem exists_even_coordinates {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (B : BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) :
    ∃ (k : ℕ) (e : (Fin k → ℂ) ≃ₗ[ℂ] V),
      ∀ x y, B (e x) (e y) = stdFormEven k x y := by
  obtain ⟨bb, hbb⟩ := exists_orthonormal_basis B hsymm hnd
  refine ⟨finrank ℂ V, bb.equivFun.symm, fun x y => ?_⟩
  rw [Basis.equivFun_symm_apply, Basis.equivFun_symm_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, hbb]
  unfold stdFormEven
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i, ite_eq_left rfl, mul_one]
  · exact mul_comm _ _
  · intro m _ hm
    rw [ite_eq_right hm, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ i) hmem

/-- **Odd coordinates**: an alternating nondegenerate bilinear
form is carried to the standard odd form by the coordinate
equivalence of a symplectic basis. -/
theorem exists_odd_coordinates {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (B : BilinForm ℂ V)
    (hAlt : B.IsAlt) (hND : B.Nondegenerate) :
    ∃ (ℓ : ℕ) (e : (Fin (2 * ℓ) → ℂ) ≃ₗ[ℂ] V),
      ∀ x y, B (e x) (e y) = stdFormOdd ℓ x y := by
  obtain ⟨ℓ, _, f, hf⟩ := exists_symplectic_basis B hAlt hND
  have hfM : ∀ i j, B (f i) (f j) =
      if j = oddPartner ℓ i then -(oddPartnerSign ℓ i : ℂ) else 0 :=
    fun i j => (hf i j).trans (symplecticMatrix_eq_std ℓ i j)
  refine ⟨ℓ, f.equivFun.symm, fun x y => ?_⟩
  rw [Basis.equivFun_symm_apply, Basis.equivFun_symm_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, hfM]
  unfold stdFormOdd
  refine Fintype.sum_equiv
    ⟨oddPartner ℓ, oddPartner ℓ, oddPartner_invol ℓ, oddPartner_invol ℓ⟩
    _ _ (fun i => ?_)
  simp only [Equiv.coe_fn_mk]
  rw [Finset.sum_eq_single (oddPartner ℓ i),
    ite_eq_left (oddPartner_invol ℓ i).symm, oddPartner_invol]
  · ring
  · intro m _ hm
    rw [ite_eq_right (fun hh => hm (by rw [hh, oddPartner_invol])), mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ (oddPartner ℓ i)) hmem

/-! ### The graded coordinate identification -/

/-- **Standard orthosymplectic coordinates** (accompanying paper §5.1): a
super vector space with a supersymmetric form whose blocks are
nondegenerate admits graded coordinates carrying the blocks to
the standard forms of `stdSuperPair k ℓ`. -/
theorem exists_coordinates {V : SuperVect}
    (b : SuperVect.Hom (SuperVect.tensorObj V V) SuperVect.tensorUnit)
    (hb : SuperVect.Hom.comp b (SuperVect.koszulBraiding V V) = b)
    (hndE : ∀ x, (∀ y, formEvenBlock b x y = 0) → x = 0)
    (hndO : (formOddBlock b).Nondegenerate) :
    ∃ (k ℓ : ℕ) (eE : (Fin k → ℂ) ≃ₗ[ℂ] V.even)
      (eO : (Fin (2 * ℓ) → ℂ) ≃ₗ[ℂ] V.odd),
      (∀ x y, formEvenBlock b (eE x) (eE y) = stdFormEven k x y) ∧
      (∀ x y, formOddBlock b (eO x) (eO y) = stdFormOdd ℓ x y) := by
  obtain ⟨k, eE, hE⟩ := exists_even_coordinates (formEvenBlock b)
    (formEvenBlock_symm b hb) hndE
  obtain ⟨ℓ, eO, hO⟩ := exists_odd_coordinates (formOddBlock b)
    (formOddBlock_isAlt b hb) hndO
  exact ⟨k, ℓ, eE, eO, hE, hO⟩

end RS

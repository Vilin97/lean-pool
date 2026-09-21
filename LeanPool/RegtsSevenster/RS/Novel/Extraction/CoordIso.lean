/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Extraction.Nondegenerate

/-!
# The standard-model isomorphism

The morphism-level packaging of the coordinate identification: a
super vector space carrying a supersymmetric form with a rigid
copairing is isomorphic to a standard model `stdSuperPair k ℓ`, by an
isomorphism pulling the form back to the standard form
(`exists_std_iso`).  This is the full statement of the §5.1
coordinate conventions: every self-dual object of SuperVect *is*
a standard orthosymplectic space, form and all.
-/

noncomputable section

namespace RS

open CategoryTheory
open scoped TensorProduct

/-- The graded coordinate equivalences packaged as a morphism of
super vector spaces. -/
def coordHom {V : SuperVect} {k ℓ : ℕ}
    (eE : (Fin k → ℂ) ≃ₗ[ℂ] V.even)
    (eO : (Fin (2 * ℓ) → ℂ) ≃ₗ[ℂ] V.odd) :
    SuperVect.Hom (stdSuperPair k ℓ) V := by
  refine ⟨?_, ?_⟩
  · change (Fin k → ℂ) →ₗ[ℂ] V.even
    exact eE.toLinearMap
  · change (Fin (2 * ℓ) → ℂ) →ₗ[ℂ] V.odd
    exact eO.toLinearMap

/-- The inverse coordinate morphism. -/
def coordInv {V : SuperVect} {k ℓ : ℕ}
    (eE : (Fin k → ℂ) ≃ₗ[ℂ] V.even)
    (eO : (Fin (2 * ℓ) → ℂ) ≃ₗ[ℂ] V.odd) :
    SuperVect.Hom V (stdSuperPair k ℓ) := by
  refine ⟨?_, ?_⟩
  · change V.even →ₗ[ℂ] (Fin k → ℂ)
    exact eE.symm.toLinearMap
  · change V.odd →ₗ[ℂ] (Fin (2 * ℓ) → ℂ)
    exact eO.symm.toLinearMap

/-- One round trip of the coordinate identification is the
identity. -/
theorem coordInv_comp_coordHom {V : SuperVect} {k ℓ : ℕ}
    (eE : (Fin k → ℂ) ≃ₗ[ℂ] V.even)
    (eO : (Fin (2 * ℓ) → ℂ) ≃ₗ[ℂ] V.odd) :
    SuperVect.Hom.comp (coordInv eE eO) (coordHom eE eO) =
      SuperVect.Hom.id (stdSuperPair k ℓ) := by
  apply SuperVect.Hom.ext
  · change eE.symm.toLinearMap.comp eE.toLinearMap = LinearMap.id
    exact LinearMap.ext fun z => eE.symm_apply_apply z
  · change eO.symm.toLinearMap.comp eO.toLinearMap = LinearMap.id
    exact LinearMap.ext fun z => eO.symm_apply_apply z

/-- And so is the other — the two are mutually inverse. -/
theorem coordHom_comp_coordInv {V : SuperVect} {k ℓ : ℕ}
    (eE : (Fin k → ℂ) ≃ₗ[ℂ] V.even)
    (eO : (Fin (2 * ℓ) → ℂ) ≃ₗ[ℂ] V.odd) :
    SuperVect.Hom.comp (coordHom eE eO) (coordInv eE eO) =
      SuperVect.Hom.id V := by
  apply SuperVect.Hom.ext
  · change eE.toLinearMap.comp eE.symm.toLinearMap = LinearMap.id
    exact LinearMap.ext fun z => eE.apply_symm_apply z
  · change eO.toLinearMap.comp eO.symm.toLinearMap = LinearMap.id
    exact LinearMap.ext fun z => eO.apply_symm_apply z

/-- **Pullback of the form along the coordinate morphism**: when
the coordinate equivalences carry the blocks of `b` to the
standard forms, the coordinate morphism pulls `b` back to
`stdForm` as a morphism equation. -/
theorem coordHom_form {V : SuperVect} {k ℓ : ℕ}
    (b : SuperVect.Hom (SuperVect.tensorObj V V) SuperVect.tensorUnit)
    (eE : (Fin k → ℂ) ≃ₗ[ℂ] V.even)
    (eO : (Fin (2 * ℓ) → ℂ) ≃ₗ[ℂ] V.odd)
    (hE : ∀ x y, formEvenBlock b (eE x) (eE y) = stdFormEven k x y)
    (hO : ∀ x y, formOddBlock b (eO x) (eO y) = stdFormOdd ℓ x y) :
    SuperVect.Hom.comp b
        (SuperVect.tensorHom (coordHom eE eO) (coordHom eE eO)) =
      stdForm k ℓ := by
  apply SuperVect.Hom.ext
  · change (formEvenMap b).comp
        (LinearMap.prodMap
          (TensorProduct.map eE.toLinearMap eE.toLinearMap)
          (TensorProduct.map eO.toLinearMap eO.toLinearMap)) =
      LinearMap.coprod (TensorProduct.lift (stdFormEvenBilin k))
        (TensorProduct.lift (stdFormOddBilin ℓ))
    refine LinearMap.prod_ext (TensorProduct.ext' fun u v => ?_)
      (TensorProduct.ext' fun u v => ?_)
    · simp only [LinearMap.comp_apply, LinearMap.inl_apply,
        LinearMap.prodMap_apply, TensorProduct.map_tmul,
        map_zero, LinearMap.coprod_apply, TensorProduct.lift.tmul,
        add_zero, LinearEquiv.coe_coe]
      exact hE u v
    · simp only [LinearMap.comp_apply, LinearMap.inr_apply,
        LinearMap.prodMap_apply, TensorProduct.map_tmul,
        map_zero, LinearMap.coprod_apply, TensorProduct.lift.tmul,
        zero_add, LinearEquiv.coe_coe]
      exact hO u v
  · exact LinearMap.ext fun z => Subsingleton.elim _ _

open MonoidalCategory in
/-- **The standard-model isomorphism** (accompanying paper §5.1): a super
vector space with a supersymmetric form and a rigid copairing is
isomorphic to a standard model, by an isomorphism carrying the
form to the standard form. -/
theorem exists_std_iso {V : SuperVect}
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
    ∃ (k ℓ : ℕ) (e : SuperVect.Hom (stdSuperPair k ℓ) V)
      (e' : SuperVect.Hom V (stdSuperPair k ℓ)),
      SuperVect.Hom.comp e' e = SuperVect.Hom.id (stdSuperPair k ℓ) ∧
      SuperVect.Hom.comp e e' = SuperVect.Hom.id V ∧
      SuperVect.Hom.comp b (SuperVect.tensorHom e e) = stdForm k ℓ := by
  obtain ⟨k, ℓ, eE, eO, hE, hO⟩ :=
    exists_coordinates_of_snake b C hb h1 h2
  exact ⟨k, ℓ, coordHom eE eO, coordInv eE eO,
    coordInv_comp_coordHom eE eO, coordHom_comp_coordInv eE eO,
    coordHom_form b eE eO hE hO⟩

end RS

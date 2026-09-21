/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionQuotient
import LeanPool.MarkoffModP.BGS.HasseWeil.FrobeniusPlaceCardinality

/-!
# Finite places of an exact constant extension

This file embeds the enlarged constant field into the finite normalization
over the original polynomial ring.  The canonical constant quotient is
compatible with the resulting Galois action.  Consequently, at every finite
place whose residue field has degree one over the enlarged constants, the
kernel of constant restriction on the decomposition group is exactly inertia.
-/

open scoped Pointwise Polynomial TensorProduct

namespace BGS.HasseWeil

open BGS.CorvajaZannier

noncomputable section


variable (C N S : Type*) [Field C] [Field N] [Field S]
  [Algebra C N] [Algebra (RatFunc C) N]
  [IsScalarTower C (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

section Exact

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

omit [FiniteDimensional C S] [IsGalois C S] in
private theorem exactConstantExtension_polynomialTower :
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra C[X] (ExactConstantExtension C N S) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc C) (ExactConstantExtension C N S)).comp
          (algebraMap C[X] (RatFunc C)))
    IsScalarTower C C[X] (ExactConstantExtension C N S) := by
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : Algebra C[X] (ExactConstantExtension C N S) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc C) (ExactConstantExtension C N S)).comp
        (algebraMap C[X] (RatFunc C)))
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  change algebraMap C (S ⊗[C] N) c = (1 : S) ⊗ₜ[C]
      algebraMap (RatFunc C) N
        (algebraMap C[X] (RatFunc C) (Polynomial.C c))
  rw [RatFunc.algebraMap_C]
  change algebraMap C S c ⊗ₜ[C] (1 : N) =
    (1 : S) ⊗ₜ[C]
      algebraMap (RatFunc C) N (algebraMap C (RatFunc C) c)
  rw [← IsScalarTower.algebraMap_apply C (RatFunc C) N]
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul c

/-- The enlarged constants map into the finite normalization. -/
noncomputable def exactConstantExtensionConstantToFiniteIntegralClosureRingHom :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    S →+* RatFuncFiniteIntegralClosure C
      (ExactConstantExtension C N S) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : Algebra C[X] (ExactConstantExtension C N S) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc C) (ExactConstantExtension C N S)).comp
        (algebraMap C[X] (RatFunc C)))
  letI : IsScalarTower C C[X] (ExactConstantExtension C N S) :=
    exactConstantExtension_polynomialTower C N S
  let f : S →ₐ[C] ExactConstantExtension C N S :=
    Algebra.TensorProduct.includeLeft
  exact
    { toFun := fun s =>
        ⟨f s, by
          have hs : IsIntegral C s := Algebra.IsIntegral.isIntegral s
          exact (hs.map f).tower_top⟩
      map_one' := by ext; exact map_one f
      map_mul' := fun x y => by ext; exact map_mul f x y
      map_zero' := by ext; exact map_zero f
      map_add' := fun x y => by ext; exact map_add f x y
    }

/-- The `S`-algebra structure on the finite normalization induced by the
embedded enlarged constants. -/
@[reducible] noncomputable def exactConstantExtensionFiniteIntegralClosureConstantAlgebra :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    Algebra S (RatFuncFiniteIntegralClosure C
      (ExactConstantExtension C N S)) :=
  RingHom.toAlgebra
    (exactConstantExtensionConstantToFiniteIntegralClosureRingHom C N S hExact)

theorem exactConstantExtensionFiniteIntegralClosure_algebraMap_val (s : S) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra S (RatFuncFiniteIntegralClosure C
        (ExactConstantExtension C N S)) :=
      exactConstantExtensionFiniteIntegralClosureConstantAlgebra C N S hExact
    ((algebraMap S (RatFuncFiniteIntegralClosure C
      (ExactConstantExtension C N S)) s) : ExactConstantExtension C N S) =
        (Algebra.TensorProduct.includeLeft
          (R := C) (S := C) (A := S) (B := N)) s := by
  rfl

section FullGroup

variable (L : Type*) [Field L]
  [Algebra C L] [Algebra L N] [IsScalarTower C L N]
  [Algebra (RatFunc C) L] [FiniteDimensional (RatFunc C) L]
  [Algebra.IsSeparable (RatFunc C) L]
  [IsScalarTower (RatFunc C) L N]
  [FiniteDimensional L N] [IsGalois L N]

omit [IsScalarTower C (RatFunc C) N]
  [FiniteDimensional C S] [IsGalois C S]
  [Algebra C L] [IsScalarTower C L N]
  [FiniteDimensional (RatFunc C) L]
  [Algebra.IsSeparable (RatFunc C) L]
  [FiniteDimensional L N] [IsGalois L N] in
private theorem exactConstantExtension_ratFuncBaseTower :
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    IsScalarTower (RatFunc C) L (ExactConstantExtension C N S) := by
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : Algebra L (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C L N S
  apply IsScalarTower.of_algebraMap_eq'
  ext x
  change (1 : S) ⊗ₜ[C] algebraMap (RatFunc C) N x =
    (1 : S) ⊗ₜ[C] algebraMap L N (algebraMap (RatFunc C) L x)
  congr 1
  exact IsScalarTower.algebraMap_apply (RatFunc C) L N x

omit [Algebra.IsSeparable (RatFunc C) L] in
theorem exactConstantExtensionConstantQuotient_action_on_finiteNormalization
    :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    letI : IsScalarTower (RatFunc C) L
        (ExactConstantExtension C N S) :=
      exactConstantExtension_ratFuncBaseTower C N S L
    letI : IsGalois L (ExactConstantExtension C N S) :=
      exactConstantExtension_isGalois C L N S hExact
    letI : Algebra S (RatFuncFiniteIntegralClosure C
        (ExactConstantExtension C N S)) :=
      exactConstantExtensionFiniteIntegralClosureConstantAlgebra C N S hExact
    letI : MulSemiringAction
        (ExactConstantExtension C N S ≃ₐ[L] ExactConstantExtension C N S)
        (RatFuncFiniteIntegralClosure C (ExactConstantExtension C N S)) :=
      finiteIntegralClosureGalAction C L (ExactConstantExtension C N S)
    ∀ (g : ExactConstantExtension C N S ≃ₐ[L]
        ExactConstantExtension C N S) (s : S),
      g • algebraMap S (RatFuncFiniteIntegralClosure C
          (ExactConstantExtension C N S)) s =
        algebraMap S (RatFuncFiniteIntegralClosure C
          (ExactConstantExtension C N S))
          (exactConstantExtensionConstantQuotient C L N S hExact g s) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : Algebra L (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C L N S
  letI : IsScalarTower (RatFunc C) L (ExactConstantExtension C N S) :=
    exactConstantExtension_ratFuncBaseTower C N S L
  letI : Algebra C[X] L :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc C) L).comp (algebraMap C[X] (RatFunc C)))
  letI : IsScalarTower C[X] (RatFunc C) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra C[X] (ExactConstantExtension C N S) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc C) (ExactConstantExtension C N S)).comp
        (algebraMap C[X] (RatFunc C)))
  letI : IsScalarTower C[X] (RatFunc C)
      (ExactConstantExtension C N S) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsGalois L (ExactConstantExtension C N S) :=
    exactConstantExtension_isGalois C L N S hExact
  letI : Algebra S (RatFuncFiniteIntegralClosure C
      (ExactConstantExtension C N S)) :=
    exactConstantExtensionFiniteIntegralClosureConstantAlgebra C N S hExact
  letI : MulSemiringAction
      (ExactConstantExtension C N S ≃ₐ[L] ExactConstantExtension C N S)
      (RatFuncFiniteIntegralClosure C (ExactConstantExtension C N S)) :=
    finiteIntegralClosureGalAction C L (ExactConstantExtension C N S)
  letI : Algebra (RatFuncFiniteIntegralClosure C L)
      (RatFuncFiniteIntegralClosure C (ExactConstantExtension C N S)) :=
    (finiteIntegralClosureMap C L (ExactConstantExtension C N S)).toAlgebra
  letI : IsScalarTower (RatFuncFiniteIntegralClosure C L) L
      (ExactConstantExtension C N S) := inferInstance
  letI : Algebra.IsIntegral C[X] (RatFuncFiniteIntegralClosure C L) :=
    IsIntegralClosure.isIntegral_algebra C[X] L
  letI : IsScalarTower C[X] (RatFuncFiniteIntegralClosure C L)
      (ExactConstantExtension C N S) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap (RatFunc C) (ExactConstantExtension C N S)
        (algebraMap C[X] (RatFunc C) x) =
      algebraMap L (ExactConstantExtension C N S)
        (algebraMap (RatFunc C) L (algebraMap C[X] (RatFunc C) x))
    exact IsScalarTower.algebraMap_apply (RatFunc C) L
      (ExactConstantExtension C N S) _
  letI : IsScalarTower (RatFuncFiniteIntegralClosure C L)
      (RatFuncFiniteIntegralClosure C (ExactConstantExtension C N S))
      (ExactConstantExtension C N S) :=
    ⟨fun r t x => by
      simp only [Algebra.smul_def, map_mul]
      rw [show algebraMap
          (RatFuncFiniteIntegralClosure C (ExactConstantExtension C N S))
          (ExactConstantExtension C N S)
            (algebraMap (RatFuncFiniteIntegralClosure C L)
              (RatFuncFiniteIntegralClosure C
                (ExactConstantExtension C N S)) r) =
          algebraMap (RatFuncFiniteIntegralClosure C L)
            (ExactConstantExtension C N S) r by rfl]
      ring⟩
  letI : IsIntegralClosure
      (RatFuncFiniteIntegralClosure C (ExactConstantExtension C N S))
      (RatFuncFiniteIntegralClosure C L)
      (ExactConstantExtension C N S) :=
    IsIntegralClosure.tower_top (R := C[X])
  intro g s
  apply Subtype.ext
  calc
    ((g • algebraMap S (RatFuncFiniteIntegralClosure C
        (ExactConstantExtension C N S)) s :
      RatFuncFiniteIntegralClosure C (ExactConstantExtension C N S)) :
        ExactConstantExtension C N S) =
        g ((algebraMap S (RatFuncFiniteIntegralClosure C
          (ExactConstantExtension C N S)) s :
            RatFuncFiniteIntegralClosure C (ExactConstantExtension C N S)) :
          ExactConstantExtension C N S) := by
      exact algebraMap_galRestrict'_apply
        (RatFuncFiniteIntegralClosure C L)
        (RatFuncFiniteIntegralClosure C (ExactConstantExtension C N S))
        (RatFuncFiniteIntegralClosure C (ExactConstantExtension C N S))
        g.toAlgHom _
    _ = (Algebra.TensorProduct.includeLeft
          (R := C) (S := C) (A := S) (B := N))
        (exactConstantExtensionConstantQuotient C L N S hExact g s) := by
      rw [exactConstantExtensionFiniteIntegralClosure_algebraMap_val]
      exact exactConstantExtensionConstantQuotient_action_on_constants
        C L N S hExact g s
    _ = ((algebraMap S (RatFuncFiniteIntegralClosure C
        (ExactConstantExtension C N S))
          (exactConstantExtensionConstantQuotient C L N S hExact g s) :
        RatFuncFiniteIntegralClosure C (ExactConstantExtension C N S)) :
          ExactConstantExtension C N S) := by
      rw [exactConstantExtensionFiniteIntegralClosure_algebraMap_val]

/-- On a residue-degree-one finite place, the kernel of constant restriction
on the decomposition group is inertia. -/
theorem exactConstantExtensionFinitePlace_stabilizerRestriction_ker_eq_inertia
    :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    letI : IsScalarTower (RatFunc C) L
        (ExactConstantExtension C N S) :=
      exactConstantExtension_ratFuncBaseTower C N S L
    letI : IsGalois L (ExactConstantExtension C N S) :=
      exactConstantExtension_isGalois C L N S hExact
    letI : Algebra S (RatFuncFiniteIntegralClosure C
        (ExactConstantExtension C N S)) :=
      exactConstantExtensionFiniteIntegralClosureConstantAlgebra C N S hExact
    letI : MulSemiringAction
        (ExactConstantExtension C N S ≃ₐ[L] ExactConstantExtension C N S)
        (RatFuncFiniteIntegralClosure C (ExactConstantExtension C N S)) :=
      finiteIntegralClosureGalAction C L (ExactConstantExtension C N S)
    ∀ (Q : FiniteExtensionFinitePlace C (ExactConstantExtension C N S)),
      Module.finrank S Q.asIdeal.ResidueField = 1 →
        ((exactConstantExtensionConstantQuotient C L N S hExact).comp
          (MulAction.stabilizer
            (ExactConstantExtension C N S ≃ₐ[L]
              ExactConstantExtension C N S) Q.asIdeal).subtype).ker =
          Q.asIdeal.inertia
            (MulAction.stabilizer
              (ExactConstantExtension C N S ≃ₐ[L]
                ExactConstantExtension C N S) Q.asIdeal) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : Algebra L (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C L N S
  letI : IsScalarTower (RatFunc C) L (ExactConstantExtension C N S) :=
    exactConstantExtension_ratFuncBaseTower C N S L
  letI : IsGalois L (ExactConstantExtension C N S) :=
    exactConstantExtension_isGalois C L N S hExact
  letI : Algebra S (RatFuncFiniteIntegralClosure C
      (ExactConstantExtension C N S)) :=
    exactConstantExtensionFiniteIntegralClosureConstantAlgebra C N S hExact
  letI : MulSemiringAction
      (ExactConstantExtension C N S ≃ₐ[L] ExactConstantExtension C N S)
      (RatFuncFiniteIntegralClosure C (ExactConstantExtension C N S)) :=
    finiteIntegralClosureGalAction C L (ExactConstantExtension C N S)
  letI : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  letI : IsScalarTower (RatFunc C) N (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  letI : Module.Finite (RatFunc C) N := Module.Finite.trans L N
  let e := exactConstantExtensionLinearEquiv C N S
  letI : Module.Finite N (N ⊗[C] S) :=
    Module.Finite.base_change C N S
  letI : Module.Finite N (ExactConstantExtension C N S) :=
    Module.Finite.equiv e
  letI : Module.Finite (RatFunc C) (ExactConstantExtension C N S) :=
    Module.Finite.trans N (ExactConstantExtension C N S)
  letI : Algebra C[X] (ExactConstantExtension C N S) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc C) (ExactConstantExtension C N S)).comp
        (algebraMap C[X] (RatFunc C)))
  letI : IsScalarTower C[X] (RatFunc C)
      (ExactConstantExtension C N S) :=
    IsScalarTower.of_algebraMap_eq' rfl
  intro Q hdegree
  letI : Algebra.IsSeparable L (ExactConstantExtension C N S) :=
    IsGalois.to_isSeparable
  letI : Algebra.IsSeparable (RatFunc C)
      (ExactConstantExtension C N S) :=
    Algebra.IsSeparable.trans (RatFunc C) L
      (ExactConstantExtension C N S)
  letI : IsDedekindDomain (RatFuncFiniteIntegralClosure C
      (ExactConstantExtension C N S)) := inferInstance
  letI : Q.asIdeal.IsMaximal := Q.isMaximal
  exact stabilizerRestriction_ker_eq_inertia_of_residue_finrank_one
    Q.asIdeal (exactConstantExtensionConstantQuotient C L N S hExact)
      (exactConstantExtensionConstantQuotient_action_on_finiteNormalization
        C N S hExact L) hdegree

section FiniteConstants

variable [Fintype C] [DecidableEq C] [DecidableEq (RatFunc C)]

/-- The decomposition-group cardinality required by Frobenius-coset
averaging, specialized to the exact constant extension. -/
theorem exactConstantExtensionFinitePlace_decompositionGroup_card
    :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    letI : IsScalarTower (RatFunc C) L
        (ExactConstantExtension C N S) :=
      exactConstantExtension_ratFuncBaseTower C N S L
    letI : IsGalois L (ExactConstantExtension C N S) :=
      exactConstantExtension_isGalois C L N S hExact
    letI : Algebra S (RatFuncFiniteIntegralClosure C
        (ExactConstantExtension C N S)) :=
      exactConstantExtensionFiniteIntegralClosureConstantAlgebra C N S hExact
    letI : MulSemiringAction
        (ExactConstantExtension C N S ≃ₐ[L] ExactConstantExtension C N S)
        (RatFuncFiniteIntegralClosure C (ExactConstantExtension C N S)) :=
      finiteIntegralClosureGalAction C L (ExactConstantExtension C N S)
    ∀ (Q : FiniteExtensionFinitePlace C (ExactConstantExtension C N S)),
      Module.finrank S Q.asIdeal.ResidueField = 1 →
      finiteExtensionPlaceDegree C (ExactConstantExtension C N S) (.inl Q) =
          Module.finrank C S →
      finiteExtensionPlaceDegree C L
          (.inl (finitePlaceUnder C L (ExactConstantExtension C N S) Q)) = 1 →
      Nat.card (finitePlaceDecompositionGroup C L
          (ExactConstantExtension C N S) Q) =
        Nat.card
            ((exactConstantExtensionConstantQuotient C L N S hExact).comp
              (finitePlaceDecompositionGroup C L
                (ExactConstantExtension C N S) Q).subtype).ker *
          Nat.card (S ≃ₐ[C] S) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : Algebra L (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C L N S
  letI : IsScalarTower (RatFunc C) L (ExactConstantExtension C N S) :=
    exactConstantExtension_ratFuncBaseTower C N S L
  letI : IsGalois L (ExactConstantExtension C N S) :=
    exactConstantExtension_isGalois C L N S hExact
  letI : Algebra S (RatFuncFiniteIntegralClosure C
      (ExactConstantExtension C N S)) :=
    exactConstantExtensionFiniteIntegralClosureConstantAlgebra C N S hExact
  letI : MulSemiringAction
      (ExactConstantExtension C N S ≃ₐ[L] ExactConstantExtension C N S)
      (RatFuncFiniteIntegralClosure C (ExactConstantExtension C N S)) :=
    finiteIntegralClosureGalAction C L (ExactConstantExtension C N S)
  letI : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  letI : IsScalarTower (RatFunc C) N (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  letI : Module.Finite (RatFunc C) N := Module.Finite.trans L N
  let e := exactConstantExtensionLinearEquiv C N S
  letI : Module.Finite N (N ⊗[C] S) :=
    Module.Finite.base_change C N S
  letI : Module.Finite N (ExactConstantExtension C N S) :=
    Module.Finite.equiv e
  letI : Module.Finite (RatFunc C) (ExactConstantExtension C N S) :=
    Module.Finite.trans N (ExactConstantExtension C N S)
  letI : Algebra.IsSeparable L (ExactConstantExtension C N S) :=
    IsGalois.to_isSeparable
  letI : Algebra.IsSeparable (RatFunc C)
      (ExactConstantExtension C N S) :=
    Algebra.IsSeparable.trans (RatFunc C) L
      (ExactConstantExtension C N S)
  intro Q hResidue hTop hBase
  have hker :=
    exactConstantExtensionFinitePlace_stabilizerRestriction_ker_eq_inertia
      C N S hExact L Q hResidue
  exact
    finitePlaceDecompositionGroup_card_eq_restrictedKernel_mul_card_constantAut
      C L (ExactConstantExtension C N S) S
        (exactConstantExtensionConstantQuotient C L N S hExact)
        Q hTop hBase hker

end FiniteConstants

end FullGroup

end Exact

end


end BGS.HasseWeil

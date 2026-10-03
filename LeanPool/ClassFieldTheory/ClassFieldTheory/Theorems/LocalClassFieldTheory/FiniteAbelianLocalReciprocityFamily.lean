/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FiniteAbelianLocalExtension
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidueNaturality
/-!
# A coherent family of finite local Artin maps

The finite-level Artin maps can be chosen simultaneously for all finite
abelian subextensions of a fixed separable closure. Their norm kernels and
restriction compatibility refer to the same family, not to independently
chosen maps for each tower. The arithmetic-Frobenius normalization is a
separate property of this family. This theorem currently uses the source
construction at `Type 0`; arbitrary-universe transport remains separate.
-/

@[expose] public section

noncomputable
section

namespace ClassFieldTheory

/-- One family of continuous local Artin maps has the expected norm kernels
and commutes with inclusion of finite abelian subextensions. -/
theorem finiteAbelianLocalReciprocity_family
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∃ artin : (E : FiniteAbelianLocalExtension K) →
        Kˣ →ₜ* (E.1 ≃ₐ[K] E.1),
      (∀ E : FiniteAbelianLocalExtension K,
        Function.Surjective (artin E) ∧
          (artin E).toMonoidHom.ker = E.normSubgroup) ∧
      ∀ (E F : FiniteAbelianLocalExtension K)
        (hEF : E.1 ≤ F.1) (x : Kˣ) (y : E.1),
        IntermediateField.inclusion hEF ((artin E x) y) =
          (artin F x) (IntermediateField.inclusion hEF y) := by
  refine ⟨fun E => LocalClassFieldTheory.abelianLocalArtinMap K E.1, ?_, ?_⟩
  · intro E
    constructor
    · exact LocalClassFieldTheory.abelianLocalArtinMap_surjective K E.1
    · change
        (LocalClassFieldTheory.abelianLocalArtinMap K E.1).toMonoidHom.ker =
          LocalFieldTheory.localNormSubgroup K E.1
      exact LocalClassFieldTheory.abelianLocalArtinMap_ker K E.1
  · intro E F hEF x y
    have hrestrict := DFunLike.congr_fun
      (LocalClassFieldTheory.abelianLocalArtinMap_restrict K E.1 F.1 hEF) x
    change
      RamificationTheory.intermediateFieldRestrictNormalHom E.1 F.1 hEF
          (LocalClassFieldTheory.abelianLocalArtinMap K F.1 x) =
        LocalClassFieldTheory.abelianLocalArtinMap K E.1 x at hrestrict
    apply Subtype.ext
    change
      E.1.val ((LocalClassFieldTheory.abelianLocalArtinMap K E.1 x) y) =
        F.1.val ((LocalClassFieldTheory.abelianLocalArtinMap K F.1 x)
          (IntermediateField.inclusion hEF y))
    calc
      E.1.val ((LocalClassFieldTheory.abelianLocalArtinMap K E.1 x) y) =
          E.1.val
            ((RamificationTheory.intermediateFieldRestrictNormalHom
                E.1 F.1 hEF
                (LocalClassFieldTheory.abelianLocalArtinMap K F.1 x)) y) := by
            rw [hrestrict]
      _ = F.1.val ((LocalClassFieldTheory.abelianLocalArtinMap K F.1 x)
            (IntermediateField.inclusion hEF y)) :=
          RamificationTheory.intermediateFieldRestrictNormalHom_apply_val
            E.1 F.1 hEF
            (LocalClassFieldTheory.abelianLocalArtinMap K F.1 x) y

end ClassFieldTheory

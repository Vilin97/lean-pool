/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality
/-!
# Tower compatibility of finite local reciprocity

The canonical finite local Artin maps are compatible with restriction in a
tower of finite abelian extensions. This is stronger than separately choosing
the maps supplied by the finite-level existence theorem; the proof uses the
single compatible construction in the implementation layer.
-/

@[expose] public section

noncomputable
section

namespace ClassFieldTheory

/-- In a finite abelian tower `K ⊆ E ⊆ L`, one can choose the two continuous
Artin maps so that restriction of the upper map equals the lower map. Both
maps retain the expected norm kernels. -/
theorem finiteAbelianLocalReciprocity_tower
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [IsAbelianGalois K E] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∃ artinL : Kˣ →ₜ* (L ≃ₐ[K] L),
      ∃ artinE : Kˣ →ₜ* (E ≃ₐ[K] E),
        Function.Surjective artinL ∧
        Function.Surjective artinE ∧
        artinL.ker = fieldNormSubgroup K L ∧
        artinE.ker = fieldNormSubgroup K E ∧
        (AlgEquiv.restrictNormalHom E).comp artinL.toMonoidHom =
          artinE.toMonoidHom := by
  refine ⟨LocalClassFieldTheory.abelianLocalArtinMap K L,
    LocalClassFieldTheory.abelianLocalArtinMap K E,
    LocalClassFieldTheory.abelianLocalArtinMap_surjective K L,
    LocalClassFieldTheory.abelianLocalArtinMap_surjective K E,
    ?_, ?_, ?_⟩
  · change (LocalClassFieldTheory.abelianLocalArtinMap K L).toMonoidHom.ker =
      LocalFieldTheory.localNormSubgroup K L
    exact LocalClassFieldTheory.abelianLocalArtinMap_ker K L
  · change (LocalClassFieldTheory.abelianLocalArtinMap K E).toMonoidHom.ker =
      LocalFieldTheory.localNormSubgroup K E
    exact LocalClassFieldTheory.abelianLocalArtinMap_ker K E
  · rw [LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom K L,
      LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom K E]
    exact LocalClassFieldTheory.abelianLocalArtinMonoidHom_restrict_tower K E L

end ClassFieldTheory

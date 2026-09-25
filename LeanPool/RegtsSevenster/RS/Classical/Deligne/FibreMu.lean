/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaPairNat
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeModTensor

/-!
# The monoidal comparison of the fibre functor

Deligne's `ω` sends an object to the realization of its free
module, so its monoidal comparison is the comparison map of
(2.11.1) at two free modules, followed by the identification of the
relative tensor of two free modules with the free module of the
tensor product.  On the generators of the tensor product of super
modules the composite has a completely explicit form: tensor the
two morphisms and shuffle.  No coequalizer survives in that
formula, which is what makes the coherence of `ω` a computation in
the ambient category alone.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

section

variable {D : Type u}

open SuperCommAlgebra.Mod

/-- **The monoidal comparison of the fibre functor.** -/
noncomputable def fibreMu
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (V : D) (W : D) :
    (gammaModule D L R (freeMod R V).X).tensor
        (gammaModule D L R (freeMod R W).X) ⟶
      gammaModule D L R (freeMod R (V ⊗ W)).X :=
  gammaPairComparison L R (freeMod R V) (freeMod R W) ≫
    gammaFunMap L R (freeModTensorIso R V W).hom

/-- The monoidal comparison on even-even generators. -/
@[simp] theorem fibreMu_evenMap_tmulEE
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (V : D) (W : D)
    (m : 𝟙_ D ⟶ R ⊗ V)
    (n : 𝟙_ D ⟶ R ⊗ W) :
    (fibreMu L R V W).evenMap
        (tmulEE (gammaModule D L R (freeMod R V).X)
          (gammaModule D L R (freeMod R W).X) m n) =
      (λ_ (𝟙_ D)).inv ≫ (m ⊗ₘ n) ≫ freeModShuffle R V W := by
  have h : (fibreMu L R V W).evenMap
      (tmulEE (gammaModule D L R (freeMod R V).X)
        (gammaModule D L R (freeMod R W).X) m n) =
      gammaPairEven L R (freeMod R V) (freeMod R W)
        (tmulEE _ _ m n) ≫
          (freeModTensorIso R V W).hom.hom := rfl
  erw [h, gammaPairEven_tmulEE, gpairLin_apply]
  exact Eq.trans (Category.assoc _ _ _)
    (whisker_eq _ (freeModTensorIso_gpair R V W m n))

/-- The monoidal comparison on odd-odd generators. -/
@[simp] theorem fibreMu_evenMap_tmulOO
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (V : D) (W : D)
    (m : L.obj ⟶ R ⊗ V)
    (n : L.obj ⟶ R ⊗ W) :
    (fibreMu L R V W).evenMap
        (tmulOO (gammaModule D L R (freeMod R V).X)
          (gammaModule D L R (freeMod R W).X) m n) =
      L.sq.inv ≫ (m ⊗ₘ n) ≫ freeModShuffle R V W := by
  have h : (fibreMu L R V W).evenMap
      (tmulOO (gammaModule D L R (freeMod R V).X)
        (gammaModule D L R (freeMod R W).X) m n) =
      gammaPairEven L R (freeMod R V) (freeMod R W)
        (tmulOO _ _ m n) ≫
          (freeModTensorIso R V W).hom.hom := rfl
  erw [h, gammaPairEven_tmulOO, gpairLin_apply]
  exact Eq.trans (Category.assoc _ _ _)
    (whisker_eq _ (freeModTensorIso_gpair R V W m n))

/-- The monoidal comparison on even-odd generators. -/
@[simp] theorem fibreMu_oddMap_tmulEO
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (V : D) (W : D)
    (m : 𝟙_ D ⟶ R ⊗ V)
    (n : L.obj ⟶ R ⊗ W) :
    (fibreMu L R V W).oddMap
        (tmulEO (gammaModule D L R (freeMod R V).X)
          (gammaModule D L R (freeMod R W).X) m n) =
      (λ_ L.obj).inv ≫ (m ⊗ₘ n) ≫ freeModShuffle R V W := by
  have h : (fibreMu L R V W).oddMap
      (tmulEO (gammaModule D L R (freeMod R V).X)
        (gammaModule D L R (freeMod R W).X) m n) =
      gammaPairOdd L R (freeMod R V) (freeMod R W)
        (tmulEO _ _ m n) ≫
          (freeModTensorIso R V W).hom.hom := rfl
  erw [h, gammaPairOdd_tmulEO, gpairLin_apply]
  exact Eq.trans (Category.assoc _ _ _)
    (whisker_eq _ (freeModTensorIso_gpair R V W m n))

/-- The monoidal comparison on odd-even generators. -/
@[simp] theorem fibreMu_oddMap_tmulOE
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (V : D) (W : D)
    (m : L.obj ⟶ R ⊗ V)
    (n : 𝟙_ D ⟶ R ⊗ W) :
    (fibreMu L R V W).oddMap
        (tmulOE (gammaModule D L R (freeMod R V).X)
          (gammaModule D L R (freeMod R W).X) m n) =
      (ρ_ L.obj).inv ≫ (m ⊗ₘ n) ≫ freeModShuffle R V W := by
  have h : (fibreMu L R V W).oddMap
      (tmulOE (gammaModule D L R (freeMod R V).X)
        (gammaModule D L R (freeMod R W).X) m n) =
      gammaPairOdd L R (freeMod R V) (freeMod R W)
        (tmulOE _ _ m n) ≫
          (freeModTensorIso R V W).hom.hom := rfl
  erw [h, gammaPairOdd_tmulOE, gpairLin_apply]
  exact Eq.trans (Category.assoc _ _ _)
    (whisker_eq _ (freeModTensorIso_gpair R V W m n))

/-- **The monoidal comparison is invertible as soon as the
comparison map of (2.11.1) is.** -/
theorem isIso_fibreMu
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (V : D) (W : D)
    (h : IsIso (gammaPairComparison L R (freeMod R V)
      (freeMod R W))) : IsIso (fibreMu L R V W) := by
  have := h
  have : IsIso (gammaFunMap L R (freeModTensorIso R V W).hom) :=
    ((gammaModuleFunctor L R).mapIso
      (freeModTensorIso R V W)).isIso_hom
  exact IsIso.comp_isIso

end

end RS

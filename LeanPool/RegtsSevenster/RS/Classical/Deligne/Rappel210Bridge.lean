/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowPoint
import LeanPool.RegtsSevenster.RS.Classical.Deligne.CoverFactor
import LeanPool.RegtsSevenster.RS.Classical.Deligne.Rappel210Chain

/-!
# The stage units of the local splitting chain are point powers

The bridge between the chain and the nonvanishing substrate: the
stage units of the local splitting chain are the symmetrised
point powers, so for a monic point in a rigid category with
nonzero unit no stage unit vanishes.  The class of the object in
the splitting algebra restricts on the point to the unit.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- The singleton point in the tensor power, as the point against
the unitor. -/
theorem tensorPowPoint_one
    [Category.{v} D] [MonoidalCategory D] (Y : D) (pt : 𝟙_ D ⟶ Y) :
    tensorPowPoint pt 1 = pt ≫ (λ_ Y).inv := by
  rw [tensorPowPoint_succ, tensorPowPoint_zero]
  have h : (𝟙 (𝟙_ D) ⊗ₘ pt) = ((𝟙_ D) ◁ pt) :=
    MonoidalCategory.id_tensorHom _ _
  exact (whisker_eq _ h).trans
    ((eq_whisker unitors_inv_equal.symm _).trans
      (leftUnitor_inv_naturality pt).symm)

/-- **The seed is the symmetrised singleton point.** -/
theorem splitSeed_eq [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] [Linear ℂ D]
    (Y : D) (pt : 𝟙_ D ⟶ Y) :
    splitSeed Y pt =
      tensorPowPoint pt 1 ≫ modPowπ (𝟙_ D) Y 1 ≫
        symPowπ (𝟙_ D) Y 1 := by
  rw [splitSeed, tensorPowPoint_one,
    show (symPowOne (𝟙_ D) Y).inv =
      (modPowOne (𝟙_ D) Y).inv ≫ symPowπ (𝟙_ D) Y 1 from rfl,
    modPowOne_inv]
  simp only [Category.assoc]
  exact (Category.assoc _ _ _).symm

/-- **The stage units are the symmetrised point powers.** -/
theorem splitUnitStage_eq
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D) (pt : 𝟙_ D ⟶ Y) :
    ∀ n : ℕ,
    splitUnitStage Y pt n =
      tensorPowPoint pt (n + 1) ≫ modPowπ (𝟙_ D) Y (n + 1) ≫
        symPowπ (𝟙_ D) Y (n + 1)
  | 0 => splitSeed_eq Y pt
  | (n + 1) => by
    have hIH := splitUnitStage_eq Y pt n
    have hpair : (tensorPowPoint pt (n + 1) ⊗ₘ
        tensorPowPoint pt 1) ≫
        ((modPowπ (𝟙_ D) Y (n + 1) ≫
            symPowπ (𝟙_ D) Y (n + 1)) ⊗ₘ
          (modPowπ (𝟙_ D) Y 1 ≫ symPowπ (𝟙_ D) Y 1)) ≫
        symMul (𝟙_ D) Y (n + 1) 1 =
      (tensorPowPoint pt (n + 1) ⊗ₘ tensorPowPoint pt 1) ≫
        (tensorPowConcat Y (n + 1) 1).hom ≫
        modPowπ (𝟙_ D) Y (n + 1 + 1) ≫
        symPowπ (𝟙_ D) Y (n + 1 + 1) := by
      rw [← MonoidalCategory.tensorHom_comp_tensorHom,
        Category.assoc, symPowπ_tensor_symMul,
        modPowπ_tensor_modPowMul_assoc]
    calc splitUnitStage Y pt (n + 1)
        = (tensorPowPoint pt (n + 1) ≫
            modPowπ (𝟙_ D) Y (n + 1) ≫
            symPowπ (𝟙_ D) Y (n + 1)) ≫
            (ρ_ (splitStage Y n)).inv ≫
            (splitStage Y n ◁ splitSeed Y pt) ≫
            symMul (𝟙_ D) Y (n + 1) 1 := by
          rw [← splitUnitStage_succ, hIH]
          rfl
      _ = (ρ_ (𝟙_ D)).inv ≫
            ((tensorPowPoint pt (n + 1) ≫
              modPowπ (𝟙_ D) Y (n + 1) ≫
              symPowπ (𝟙_ D) Y (n + 1)) ⊗ₘ
              splitSeed Y pt) ≫
            symMul (𝟙_ D) Y (n + 1) 1 := by
          have ha : (tensorPowPoint pt (n + 1) ≫
              modPowπ (𝟙_ D) Y (n + 1) ≫
              symPowπ (𝟙_ D) Y (n + 1)) ≫
              (ρ_ (splitStage Y n)).inv =
            (ρ_ (𝟙_ D)).inv ≫ ((tensorPowPoint pt (n + 1) ≫
              modPowπ (𝟙_ D) Y (n + 1) ≫
              symPowπ (𝟙_ D) Y (n + 1)) ▷ (𝟙_ D)) :=
            rightUnitor_inv_naturality _
          have hb : ((tensorPowPoint pt (n + 1) ≫
              modPowπ (𝟙_ D) Y (n + 1) ≫
              symPowπ (𝟙_ D) Y (n + 1)) ▷ (𝟙_ D)) ≫
              (splitStage Y n ◁ splitSeed Y pt) =
            ((tensorPowPoint pt (n + 1) ≫
              modPowπ (𝟙_ D) Y (n + 1) ≫
              symPowπ (𝟙_ D) Y (n + 1)) ⊗ₘ splitSeed Y pt) :=
            (MonoidalCategory.tensorHom_def _ _).symm
          exact (Category.assoc _ _ _).symm.trans
            ((eq_whisker ha _).trans
              ((Category.assoc _ _ _).trans
                (whisker_eq _
                  ((Category.assoc _ _ _).symm.trans
                    (eq_whisker hb _)))))
      _ = (ρ_ (𝟙_ D)).inv ≫
            ((tensorPowPoint pt (n + 1) ⊗ₘ
              tensorPowPoint pt 1) ≫
              ((modPowπ (𝟙_ D) Y (n + 1) ≫
                symPowπ (𝟙_ D) Y (n + 1)) ⊗ₘ
                (modPowπ (𝟙_ D) Y 1 ≫
                  symPowπ (𝟙_ D) Y 1))) ≫
            symMul (𝟙_ D) Y (n + 1) 1 := by
          rw [splitSeed_eq,
            MonoidalCategory.tensorHom_comp_tensorHom]
          rfl
      _ = (ρ_ (𝟙_ D)).inv ≫
            ((tensorPowPoint pt (n + 1) ⊗ₘ
              tensorPowPoint pt 1) ≫
              (tensorPowConcat Y (n + 1) 1).hom) ≫
            modPowπ (𝟙_ D) Y (n + 1 + 1) ≫
            symPowπ (𝟙_ D) Y (n + 1 + 1) := by
          rw [Category.assoc, hpair]
          simp only [Category.assoc]
      _ = (ρ_ (𝟙_ D)).inv ≫ ((λ_ (𝟙_ D)).hom ≫
            tensorPowPoint pt (n + 1 + 1)) ≫
            modPowπ (𝟙_ D) Y (n + 1 + 1) ≫
            symPowπ (𝟙_ D) Y (n + 1 + 1) := by
          rw [tensorPowPoint_concat]
      _ = tensorPowPoint pt (n + 1 + 1) ≫
            modPowπ (𝟙_ D) Y (n + 1 + 1) ≫
            symPowπ (𝟙_ D) Y (n + 1 + 1) := by
          have hrl : (ρ_ (𝟙_ D)).inv ≫ (λ_ (𝟙_ D)).hom =
              𝟙 (𝟙_ D) := by
            rw [unitors_equal]
            exact (ρ_ (𝟙_ D)).inv_hom_id
          exact (whisker_eq _ (Category.assoc _ _ _)).trans
            ((Category.assoc _ _ _).symm.trans
              ((eq_whisker hrl _).trans (Category.id_comp _)))

/-- The stage-unit nonvanishing, from mono preservation of the
tensor factors alone — the form consumed over an
ind-completion. -/
theorem splitUnitStage_ne_zero'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D) (pt : 𝟙_ D ⟶ Y)
    [∀ Z : D, (tensorLeft Z).PreservesMonomorphisms]
    [∀ Z : D, (tensorRight Z).PreservesMonomorphisms]
    [Mono pt] (h1 : ¬ IsZero (𝟙_ D)) (n : ℕ) :
    splitUnitStage Y pt n ≠ 0 := by
  rw [splitUnitStage_eq]
  exact point_symPow_ne_zero' Y pt h1 (n + 1)

section Class

/-- **The class of the object in the splitting algebra**: the
singleton power, included at the bottom stage. -/
noncomputable def splitCls
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D) (pt : 𝟙_ D ⟶ Y) [HasColimitsOfShape SmallNat.{v} D] :
    Y ⟶ splitAlgebra Y pt :=
  (symPowOne (𝟙_ D) Y).inv ≫
    chainColimitι (splitStage Y) (splitDelta Y pt) 0

/-- **The class restricts on the point to the unit.** -/
theorem splitCls_point
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D) (pt : 𝟙_ D ⟶ Y) [HasColimitsOfShape SmallNat.{v} D] :
    pt ≫ splitCls Y pt = splitAlgebraUnit Y pt :=
  (Category.assoc _ _ _).symm

end Class

end RS

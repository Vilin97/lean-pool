/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.KeyLemmaData
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SplitMonHom
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SplitPairDef
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainBNonzero
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndAllColim

/-!
# The Key Lemma, closed over the ind-completion

The splitting data of Deligne's Key Lemma (2.8), assembled from
the graded splitting algebra: the carrier is the ℤ-graded
chain algebra, the base enters in degree zero, the module and its
dual in degrees `±1`, the pair product two stages up the
degree-zero line, and the section identity is the advancement of
the seed.  Nonvanishing is the stage-detection argument of the
balanced line.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v

variable {C : Type v}

/-- Tensoring preserves integer-indexed coproducts in the
ind-category, by transport from the universe-sized discrete
shape. -/
instance tensorLeft_ind_preservesShapeInt
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    (X : Ind C) :
    PreservesColimitsOfShape (Discrete ℤ) (tensorLeft X) :=
  preservesColimitsOfShape_of_equiv
    (Discrete.equivalence Equiv.ulift.{v}) _

/-- Tensoring preserves integer-indexed coproducts in the
ind-category, right-hand version. -/
instance tensorRight_ind_preservesShapeInt
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    (X : Ind C) :
    PreservesColimitsOfShape (Discrete ℤ) (tensorRight X) :=
  preservesColimitsOfShape_of_equiv
    (Discrete.equivalence Equiv.ulift.{v}) _

/-- **The Key Lemma** (Deligne 2.8) over the ind-completion: a
duality datum with the zigzag laws, over a base whose symmetric
powers of the module never vanish, admits splitting data — the
graded splitting algebra with its degree-`±1` insertions. -/
theorem keyLemmaData_ind
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    [CategoryTheory.Linear ℂ (Ind C)] [MonoidalLinear ℂ (Ind C)] (B : Ind C)
    [MonObj B] [IsCommMonObj B] (N : Mod (Ind C) B) (N' : Mod (Ind C) B)
    (d : ModDualityDatum B N N') :
    KeyLemmaDataStatement B d := by
  intro hz _ hS
  let := chainBGrMonObj B N N' d
  exact ⟨{ carrier := chainBGr B N N' d
           monObj := chainBGrMonObj B N N' d
           comm := chainBGr_isCommMonObj B N N' d
           ofBase := splitOfBase B N N' d
           ofBase_monHom :=
             ⟨splitOfBase_unit B N N' d,
               splitOfBase_mul B N N' d⟩
           unit_ne_zero := chainBGrUnit_ne_zero B N N' d
             (chainBUnit_ne_zero B N N' d hz
               fun n => hS (n + 1))
           ins := splitIns B N N' d
           ins' := splitIns' B N N' d
           ins_linear := splitIns_linear B N N' d
           ins'_linear := splitIns'_linear B N N' d
           pairMul := splitPairMul B N N' d
           pairMul_def := modTensorπ_splitPairMul B N N' d
           delta_eq := Eq.trans (Category.assoc _ _ _).symm
             (copairUnit_splitPairMul B N N' d) }⟩

end RS

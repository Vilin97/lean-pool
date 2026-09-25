/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndCoeq
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.CoprodPreserve

/-!
# The ind tensor preserves all small colimits

Combining the finite-colimit half (`IndCoeq`), the filtered half
(`IndTensorExact`) and the preservation of coproducts from finite
and filtered (`CoprodPreserve`): tensoring on either side in the
ind-category preserves every small colimit.  This is the form in
which the coend presentations of §3 pass through the tensor
product.
-/

@[expose] public section

namespace RS

open CategoryTheory Limits MonoidalCategory

universe v

variable {C : Type v}

instance tensorLeft_ind_preservesShapeDiscrete
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    (A : Ind C)
    (α : Type v) :
    PreservesColimitsOfShape (Discrete α) (tensorLeft A) :=
  preservesColimitsOfShape_discrete_of_finite_and_filtered
    (tensorLeft A)

instance tensorRight_ind_preservesShapeDiscrete
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    (A : Ind C)
    (α : Type v) :
    PreservesColimitsOfShape (Discrete α) (tensorRight A) :=
  preservesColimitsOfShape_discrete_of_finite_and_filtered
    (tensorRight A)

/-- **Tensoring preserves all small colimits in the
ind-category**, left-hand version. -/
instance tensorLeft_ind_preservesColimits
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    (A : Ind C) :
    PreservesColimitsOfSize.{v, v} (tensorLeft A) :=
  preservesColimits_of_preservesCoequalizers_and_coproducts
    (tensorLeft A)

/-- **Tensoring preserves all small colimits in the
ind-category**, right-hand version. -/
instance tensorRight_ind_preservesColimits
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    (A : Ind C) :
    PreservesColimitsOfSize.{v, v} (tensorRight A) :=
  preservesColimits_of_preservesCoequalizers_and_coproducts
    (tensorRight A)

end RS

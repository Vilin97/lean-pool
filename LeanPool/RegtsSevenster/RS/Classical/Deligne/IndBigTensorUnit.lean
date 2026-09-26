/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.BigTensorUnit
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndPointTensor
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndAllColim

/-!
# The unit of a big tensor product of ind-algebras survives

In the ind-completion the two inputs of the general criterion are
available: the tensor of two nonzero points is nonzero, and a
point of a filtered colimit vanishes only if it already vanishes
at a later stage.  So a tensor product of an arbitrary family of
algebras with nonvanishing units again has a nonvanishing unit —
the step Deligne asserts without proof in 2.11.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v

variable {C : Type v}

/-- The identity of the unit of the ind-completion is nonzero. -/
theorem id_indUnit_ne_zero [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ C]
    (hu : HasScalarUnit C) :
    𝟙 (𝟙_ (Ind C)) ≠ 0 := by
  intro h
  refine id_unit_ne_zero hu ?_
  refine (indOf_map_eq_zero_iff (𝟙 (𝟙_ C))).mp ?_
  rw [CategoryTheory.Functor.map_id]
  have hconj := congrArg
    (fun t => (indOfUnitIso (C := C)).inv ≫ t ≫
      (indOfUnitIso (C := C)).hom) h
  simpa using hconj

/-- **The unit of a big tensor product of ind-algebras
survives.** -/
theorem bigTensorUnit_ne_zero_ind
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [RigidCategory C] [BraidedCategory (Ind C)] {ι : Type v} [LinearOrder ι]
    (B : ι → Ind C) [∀ i, MonObj (B i)]
    (hu : HasScalarUnit C)
    (hB : ∀ i, MonObj.one (X := B i) ≠ 0) :
    bigTensorUnit B ≠ 0 := by
  refine bigTensorUnit_ne_zero B (id_indUnit_ne_zero hu)
    (fun u v hu0 hv0 => indTensorHom_point_ne_zero hu hu0 hv0)
    hB ?_
  intro s f hf
  obtain ⟨t, α, ht⟩ :=
    (unit_colimit_eq_zero_iff (finTensorDiagram B) f).mp hf
  exact ⟨t, leOfHom α, ht⟩

end RS

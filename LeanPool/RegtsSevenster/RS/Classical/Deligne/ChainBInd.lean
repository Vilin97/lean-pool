/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainB
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndCoeq

/-!
# The splitting chain in the ind-category

`RS.Classical.Deligne.ChainB` assembles the splitting-chain
algebra `chainB` over any ambient category in which the chain
machinery runs.  This file instantiates the ambient at the
ind-category of a small rigid abelian symmetric monoidal category
with preadditive tensor, where the colimit shape exists and the
stage-detection principle of `RS.Classical.Deligne.ChainAlgebra`
applies.  The outcome is `RS.chainBUnit_eq_zero_iff`: the unit of
the splitting-chain algebra vanishes exactly when a stage unit
dies.

Every hypothesis of the `Colimit` section of `ChainB` holds for
`D := Ind C` by an existing instance:

* `MonoidalCategory (Ind C)` and `SymmetricCategory (Ind C)` —
  the transport instances of `RS.Classical.Deligne.IndMonoidal`;
* `Preadditive (Ind C)` and `HasFiniteBiproducts (Ind C)` —
  `Mathlib.CategoryTheory.Preadditive.Indization`, for `C`
  preadditive with finite colimits (both supplied by `Abelian C`);
* `MonoidalPreadditive (Ind C)` — the preadditive half of
  `RS.Classical.Deligne.IndTensorExact`;
* `HasCoequalizers (Ind C)` — the `WalkingParallelPair` colimit
  instance of `Mathlib.CategoryTheory.Limits.Indization.Category`;
* `PreservesColimitsOfShape WalkingParallelPair` for every
  `tensorLeft Z` and `tensorRight Z` —
  `RS.tensorLeft_ind_preservesCoequalizers` and
  `RS.tensorRight_ind_preservesCoequalizers` of
  `RS.Classical.Deligne.IndCoeq`, for `C` rigid abelian;
* `HasColimitsOfShape SmallNat (Ind C)` — Mathlib's
  `HasFilteredColimits (Ind C)`, since `SmallNat` is small
  filtered;
* `PreservesColimitsOfShape SmallNat` for every `tensorLeft X`
  and `tensorRight X` —
  `RS.tensorLeft_ind_preservesColimitsOfShape` and its right-hand
  twin in `RS.Classical.Deligne.IndTensorExact`, the filtered
  half of Deligne 2.2.

The ℂ-linear structure of `Ind C` is not canonical: it is induced
by a choice of scalar unit `ψ : ℂ ≃+* End (𝟙_ C)` through
`RS.linearOfScalarUnit (RS.indScalarUnit ψ)` and
`RS.monoidalLinearOfScalarUnitBraided (RS.indScalarUnit ψ)`
(`RS.Classical.Deligne.ScalarLinear`, acceptance section).  It is
therefore carried as a hypothesis, as in
`RS.Classical.Deligne.SuperRealize`.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v

variable {C : Type v}

/-- **Unit-vanishing detection for the splitting-chain algebra**:
over the ind-category, the unit of the algebra `chainB` vanishes
exactly when the unit dies at a finite stage of the chain. -/
theorem chainBUnit_eq_zero_iff
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] [Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)] (A : Ind C) [MonObj A] [IsCommMonObj A]
    (M : Mod (Ind C) A) (M' : Mod (Ind C) A)
    (d : ModDualityDatum A M M') :
    chainBUnit A M M' d = 0 ↔
      ∃ n, chainUnitStage A M M' d n = 0 :=
  chainColimitUnit_eq_zero_iff (chainStage A M M')
    (chainDelta A M M' d) (chainUnitStage A M M' d)
    (chainUnitStage_succ A M M' d)

/-! ## Acceptance

The full assembly of `ChainB` synthesises over the ind-category:
the algebra, its monoid structure and its commutativity all
instantiate at `D := Ind C`. -/

noncomputable example
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] [Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)] (A : Ind C) [MonObj A] [IsCommMonObj A]
    (M : Mod (Ind C) A) (M' : Mod (Ind C) A)
    (d : ModDualityDatum A M M') : Ind C :=
  chainB A M M' d

noncomputable example
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] [Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)] (A : Ind C) [MonObj A] [IsCommMonObj A]
    (M : Mod (Ind C) A) (M' : Mod (Ind C) A)
    (d : ModDualityDatum A M M') :
    MonObj (chainB A M M' d) :=
  chainBMonObj A M M' d

example
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] [Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)] (A : Ind C) [MonObj A] [IsCommMonObj A]
    (M : Mod (Ind C) A) (M' : Mod (Ind C) A)
    (d : ModDualityDatum A M M') :
    letI := chainBMonObj A M M' d
    IsCommMonObj (chainB A M M' d) :=
  chainB_isCommMonObj A M M' d

end RS

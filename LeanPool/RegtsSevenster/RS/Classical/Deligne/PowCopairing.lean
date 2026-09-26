/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowPairing

/-!
# The power copairing

The mirror of the power pairing: the copairing side of a
Mod-internal duality datum.  The copairing lands in the quotient
`modTensor A M M'`, so there is no raw section; every primitive
lives at the descended level.  The file provides the copairing
unit `copairUnit` — the seed of the chain units of the Key
Lemma — with its linearity laws, the braiding `modTensorSwap` of
the module tensor product with its defining equation, involution
and module-linearity, and the zigzag scalar `zig` together with
the retraction law: under the zigzag identity of the datum the
scalar is the unit of the base.  The retraction is the
nonvanishing engine of the Key Lemma's chain: a vanishing chain
unit forces the unit of the base to vanish.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## The copairing unit -/

section Braided

/-- **The copairing unit**: the copairing of the datum evaluated
at the unit of the base.  The seed of the chain units of the Key
Lemma. -/
noncomputable def copairUnit
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    𝟙_ D ⟶ modTensor A M M' :=
  η[A] ≫ d.copair

/-- Linearity of the copairing, phrased at the descended action:
multiplying before the copairing is acting after it. -/
@[reassoc]
theorem copair_act [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    μ[A] ≫ d.copair =
      (A ◁ d.copair) ≫ modTensorAct A M M' :=
  d.copair_linear

/-- Linearity through the braided right action: the copairing
carries right multiplication to the braided right action on the
module tensor product. -/
@[reassoc]
theorem copair_braid_act
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    (d.copair ▷ A) ≫ (β_ (modTensor A M M') A).hom ≫
        modTensorAct A M M' =
      μ[A] ≫ d.copair := by
  rw [BraidedCategory.braiding_naturality_left_assoc,
    ← copair_act A M M' d, IsCommMonObj.mul_comm_assoc]

/-- The action on the copairing unit collapses onto the
copairing: the copairing unit is a relative invariant of the
module tensor product. -/
@[reassoc]
theorem copairUnit_act [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    (A ◁ copairUnit A M M' d) ≫ modTensorAct A M M' =
      (ρ_ A).hom ≫ d.copair := by
  rw [copairUnit, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, ← copair_act A M M' d, ← Category.assoc,
    MonObj.mul_one]

end Braided

/-! ## The braiding of the module tensor product

The copairing is consumed against the pairing through the
braiding of the module tensor product: the braiding of the
underlying factors descends through the coequalizers, the
relation carried across by the window exchange of `ModCross`.
The exchange swaps the two legs, so the two-sided descent needs
the symmetric base — the generality of the Key Lemma itself.
-/

section Symmetric

/-- The strand crossing behind the braiding of the module tensor
product: crossing the pair as a block and braiding back across
the first factor equals crossing the second factor alone. -/
private theorem swap_cross
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (P Q R : D) :
    (α_ P Q R).inv ≫ (β_ (P ⊗ Q) R).hom ≫ (α_ R P Q).inv ≫
        ((β_ R P).hom ▷ Q) =
      (P ◁ (β_ Q R).hom) ≫ (α_ P R Q).inv := by
  rw [BraidedCategory.braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc]
  rw [← MonoidalCategory.comp_whiskerRight,
    SymmetricCategory.symmetry, MonoidalCategory.id_whiskerRight,
    Category.comp_id]

section Swap

/-- **The braiding of the module tensor product**: the braiding
of the underlying factors descends through the coequalizers, the
relation carried across by the window exchange. -/
noncomputable def modTensorSwap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A) :
    modTensor A M N ⟶ modTensor A N M :=
  modTensorDesc A M N ((β_ M.X N.X).hom ≫ modTensorπ A N M)
    (by rw [modWinSwap_legM_assoc, modWinSwap_legN_assoc,
      modTensor_condition])

/-- Defining equation of the braiding of the module tensor
product: on the projection it is the braiding of the factors. -/
@[reassoc (attr := simp)]
theorem modTensorπ_swap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A) :
    modTensorπ A M N ≫ modTensorSwap A M N =
      (β_ M.X N.X).hom ≫ modTensorπ A N M :=
  modTensorπ_desc A M N _ _

/-- The braiding of the module tensor product is an
involution. -/
@[reassoc (attr := simp)]
theorem modTensorSwap_modTensorSwap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A) :
    modTensorSwap A M N ≫ modTensorSwap A N M =
      𝟙 (modTensor A M N) := by
  apply modTensor_hom_ext
  rw [modTensorπ_swap_assoc, modTensorπ_swap, ← Category.assoc,
    SymmetricCategory.symmetry, Category.id_comp,
    Category.comp_id]

end Swap

section SwapLinear

/-- **The braiding of the module tensor product is a module
map**: it intertwines the descended actions. -/
@[reassoc]
theorem modTensorAct_swap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [IsCommMonObj A] (M : Mod D A) (N : Mod D A) :
    modTensorAct A M N ≫ modTensorSwap A M N =
      (A ◁ modTensorSwap A M N) ≫ modTensorAct A N M := by
  apply modTensor_whisker_hom_ext A M N A
  have hleg : (N.X ◁ actLeft A M.X) ≫ modTensorπ A N M =
      (α_ N.X A M.X).inv ≫ ((β_ N.X A).hom ▷ M.X) ≫
        (actLeft A N.X ▷ M.X) ≫ modTensorπ A N M := by
    have h := modTensor_condition A N M
    rw [modTensorLegM, modTensorLegN, actRight,
      MonoidalCategory.comp_whiskerRight, Category.assoc,
      Category.assoc] at h
    rw [h, Iso.inv_hom_id_assoc]
  conv_lhs => rw [whiskerLeft_modTensorπ_act_assoc,
    modTensorπ_swap]
  conv_lhs => rw [BraidedCategory.braiding_naturality_left_assoc,
    hleg]
  conv_rhs => rw [← MonoidalCategory.whiskerLeft_comp_assoc,
    modTensorπ_swap, MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_modTensorπ_act]
  conv_rhs => simp only [Category.assoc]
  rw [reassoc_of% swap_cross A M.X N.X]

end SwapLinear

/-! ## The zigzag scalar and the retraction law

The composite of the copairing with the pairing through the
braiding of the module tensor product.  The zigzag identity of
the datum — Deligne's (1.15.1) duality — is taken as a
hypothesis; it is not derivable from the bare datum.
-/

section Zigzag

/-- **The zigzag scalar** of a duality datum: the copairing
unit, braided across the module tensor product and consumed by
the pairing. -/
noncomputable def zig
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    𝟙_ D ⟶ A :=
  copairUnit A M M' d ≫ modTensorSwap A M M' ≫ d.pair

/-- **The retraction law**: under the zigzag identity of the
datum, the zigzag scalar is the unit of the base. -/
theorem zig_eq_unit [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (hzig : d.copair ≫ modTensorSwap A M M' ≫ d.pair = 𝟙 A) :
    zig A M M' d = η[A] := by
  rw [zig, copairUnit, Category.assoc, hzig, Category.comp_id]

end Zigzag

end Symmetric

end RS

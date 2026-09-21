/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowZig
import LeanPool.RegtsSevenster.RS.Classical.Deligne.ZigzagNonzero

/-!
# The power duality datum

The tensor powers of a dual pair of modules form a dual pair:
the power pairing and the copairing power assemble into a
`ModDualityDatum` at every level.  The pairing's linearity is
`modPowPairing_linear`; the copairing's linearity is proved here
from the associativity of the descended action, since the
copairing power is the action on the unit-stage element.

The zigzag laws for the power datum — the inheritance of the
triangle identities up the powers — are the peel induction and
live separately; once available, `ZigzagNonzero` applied to the
power datum detects the nonvanishing of the copairing powers
from the nonvanishing of the power modules.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **Acting on a point is linear**: for an associative action on
a carrier, the orbit map of a global point is a module map from
the regular module.  Stated over an abstract carrier so that
instantiations at definitional wrappers stay uniformly typed. -/
theorem act_on_point_linear
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    {X : D} (act : A ⊗ X ⟶ X)
    (hact : (μ[A] ▷ X) ≫ act =
      (α_ A A X).hom ≫ (A ◁ act) ≫ act)
    (u : 𝟙_ D ⟶ X) :
    μ[A] ≫ (ρ_ A).inv ≫ (A ◁ u) ≫ act =
      (A ◁ ((ρ_ A).inv ≫ (A ◁ u) ≫ act)) ≫ act := by
  have hnat : ((A ⊗ A) ◁ u) ≫ (α_ A A X).hom =
      (α_ A A (𝟙_ D)).hom ≫ (A ◁ (A ◁ u)) :=
    associator_naturality_right A A u
  rw [← Category.assoc, rightUnitor_inv_naturality, Category.assoc,
    ← Category.assoc (μ[A] ▷ 𝟙_ D), ← whisker_exchange,
    Category.assoc, hact, reassoc_of% hnat,
    ← Category.assoc ((ρ_ (A ⊗ A)).inv),
    (by monoidal : (ρ_ (A ⊗ A)).inv ≫ (α_ A A (𝟙_ D)).hom =
      A ◁ (ρ_ A).inv),
    MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    Category.assoc]

/-- **The orbit map returns the point at the unit**: for a unital
action, evaluating the orbit map of a global point at the monoid
unit recovers the point. -/
theorem act_on_point_unit
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    {X : D} (act : A ⊗ X ⟶ X)
    (hone : (η[A] ▷ X) ≫ act = (λ_ X).hom)
    (u : 𝟙_ D ⟶ X) :
    η[A] ≫ (ρ_ A).inv ≫ (A ◁ u) ≫ act = u := by
  rw [← Category.assoc, rightUnitor_inv_naturality, Category.assoc,
    ← Category.assoc (η[A] ▷ 𝟙_ D), ← whisker_exchange,
    Category.assoc, hone, leftUnitor_naturality,
    ← Category.assoc,
    (by monoidal : (ρ_ (𝟙_ D)).inv ≫ (λ_ (𝟙_ D)).hom =
      𝟙 (𝟙_ D)),
    Category.id_comp]

/-- **The unit of the copairing power is the unit stage**: the
copair element of the power datum is the chain unit. -/
theorem powCopairA_unit
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') (n : ℕ) :
    η[A] ≫ powCopairA A M M' d n = powUnitStage A M M' d n :=
  act_on_point_unit A
    (modTensorAct A (modPowMod A M.X n) (modPowMod A M'.X n))
    (modTensorAct_one A (modPowMod A M.X n) (modPowMod A M'.X n))
    (powUnitStage A M M' d n)

/-- **The copairing power is linear**: the copairing power is the
action on the unit-stage element, so its linearity is the
associativity of the descended action. -/
theorem powCopairA_linear
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') (n : ℕ) :
    haveI := modTensorModObj A (modPowMod A M.X n)
      (modPowMod A M'.X n)
    μ[A] ≫ powCopairA A M M' d n =
      (A ◁ powCopairA A M M' d n) ≫
        actLeft A (modTensor A (modPowMod A M.X n)
          (modPowMod A M'.X n)) :=
  act_on_point_linear A
    (modTensorAct A (modPowMod A M.X n) (modPowMod A M'.X n))
    (modTensorAct_mul A (modPowMod A M.X n) (modPowMod A M'.X n))
    (powUnitStage A M M' d n)

/-- **The power duality datum**: the tensor powers of a dual pair
form a dual pair, with the power pairing and the copairing
power. -/
noncomputable def powDualityDatum
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    ModDualityDatum A (modPowMod A M.X n) (modPowMod A M'.X n) where
  pair := modPowPairing A M M' d n
  copair := powCopairA A M M' d n
  pair_linear := modPowPairing_linear A M M' d n
  copair_linear := powCopairA_linear A M M' d n

end RS

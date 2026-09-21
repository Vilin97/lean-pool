/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.KeyLemma

/-!
# The Key Lemma conclusion, in Deligne's insertion form

The conclusion of record for Deligne 2.8, per the source: a
nonzero commutative algebra under the base together with module
insertions of the module and its dual, multiplying the copair
element to the unit.  This is the data from which the direct
factor `1_B ∣ M_B` is rebuilt by the algebra structure (the
consumer's reconstruction), stated without any base-changed
module category.

The earlier element form (`SplittingAlgebra` in `KeyLemma.lean`)
is superseded: it does not retain the individual insertions that
the 2.9 dévissage consumes.  The witness algebra is the full
ℤ-graded splitting algebra, of which the balanced chain `chainB`
is the degree-zero part — the unit lives in degree zero, so the
nonvanishing argument is unaffected; the insertions live in
degrees `±1`.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

section Data

/-- **The conclusion of the Key Lemma** (Deligne 2.8), in the
insertion form of the source: a commutative algebra `B` under
`A`, nonzero in the unit-detection sense, with module insertions
`v` of `M` and `u` of `M'` whose product carries the copair
element to the unit of `B`.  The insertions are linear over the
base through the structure morphism, and their product on the
relative tensor is packaged as the descended map `pairMul` with
its defining equation. -/
structure SplittingData
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A]
    {M M' : Mod D A}
    (d : ModDualityDatum A M M') where
  /-- The underlying object of the splitting algebra. -/
  carrier : D
  /-- The monoid structure. -/
  monObj : MonObj carrier
  /-- Commutativity. -/
  comm : letI := monObj; IsCommMonObj carrier
  /-- The structure morphism from the base algebra. -/
  ofBase : A ⟶ carrier
  /-- The structure morphism is a monoid map. -/
  ofBase_monHom : letI := monObj; IsMonHom ofBase
  /-- The algebra is nonzero: its unit does not vanish. -/
  unit_ne_zero : letI := monObj; η[carrier] ≠ 0
  /-- The insertion of the module. -/
  ins : M.X ⟶ carrier
  /-- The insertion of the dual module. -/
  ins' : M'.X ⟶ carrier
  /-- The insertion of the module is linear over the base,
  through the structure morphism. -/
  ins_linear : letI := monObj;
    actLeft A M.X ≫ ins =
      (A ◁ ins) ≫ (ofBase ▷ carrier) ≫ μ[carrier]
  /-- The insertion of the dual module is linear over the base,
  through the structure morphism. -/
  ins'_linear : letI := monObj;
    actLeft A M'.X ≫ ins' =
      (A ◁ ins') ≫ (ofBase ▷ carrier) ≫ μ[carrier]
  /-- The product of the insertions, descended to the relative
  tensor. -/
  pairMul : modTensor A M M' ⟶ carrier
  /-- Defining equation of the descended product of the
  insertions. -/
  pairMul_def : letI := monObj;
    modTensorπ A M M' ≫ pairMul =
      (ins ⊗ₘ ins') ≫ μ[carrier]
  /-- **The section identity**: the product of the insertions
  carries the copair element to the unit. -/
  delta_eq : letI := monObj;
    η[A] ≫ d.copair ≫ pairMul = η[carrier]

end Data

section Statement

/-- **The Key Lemma statement of record** (Deligne 2.8, the
consumed direction): a duality datum with the zigzag laws, over
a nonzero base whose symmetric powers of the module never
vanish, admits splitting data. -/
def KeyLemmaDataStatement
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [CategoryTheory.Linear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A]
    {M M' : Mod D A}
    (d : ModDualityDatum A M M') : Prop :=
  ModZigzagDatum A d → η[A] ≠ 0 →
    (∀ n : ℕ, ¬ Limits.IsZero (symPow A M.X n)) →
    Nonempty (SplittingData A d)

end Statement

end RS

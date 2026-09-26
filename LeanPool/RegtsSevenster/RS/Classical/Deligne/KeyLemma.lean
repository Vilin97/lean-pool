/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SymMul
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModContractL
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainUnit

/-!
# The Key Lemma: the universal splitting algebra

Deligne 2.8, the consumed direction: for a dualizable module over
a commutative algebra whose symmetric powers do not vanish, there
is a nonzero algebra over which the module acquires the unit as a
direct factor.  The construction is the colimit of the chain of
paired symmetric powers, with copair-insertion transitions; its
nonvanishing is stage detection for the unit, and the splitting
pair is built from the tautological pairing against the
multiplication.

The duality of the module is Mod-internal: the pairing and
copairing are given as data with zigzag identities stated at the
multi-tensor level, where the wide-coequalizer presentation makes
them associativity-free.

## The form of the conclusion

The conclusion is in element form: a nonzero commutative
algebra `B` under `A` together with a global point of
`modTensor A M' M ⊗ B` on which the pairing evaluates to the unit
of `B`.  This is the section-of-the-evaluation reading of the
splitting: the point is exactly the datum needed to produce a
`B`-linear section of the base-changed evaluation by
multiplication.  A direct splitting of the unit off `M_B` itself
is not the right reading: counting `M`-letters minus `M'`-letters
grades every morphism constructible from a duality datum, and
`M_B` sits in degree one while `B` sits in degree zero, so no
constructible morphism connects them.  The degree-zero object
`modTensor A M' M ⊗ B` is where the splitting genuinely lives.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

section Datum

/-- A Mod-internal duality datum for a pair of modules over a
monoid object: a descended `A`-valued pairing and a copairing
into the relative tensor, each a module map.  The zigzag
identities live one level up, through the multi-tensor insertion
and contraction constructors, and are packaged separately as
`ModZigzagDatum`. -/
structure ModDualityDatum
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Limits.HasCoequalizers D] (A : D)
    [MonObj A] [IsCommMonObj A] (M M' : Mod D A)
    [∀ Z : D, Limits.PreservesColimitsOfShape
      Limits.WalkingParallelPair (tensorLeft Z)] where
  /-- The descended `A`-valued pairing on the relative tensor. -/
  pair : modTensor A M' M ⟶ A
  /-- The copairing into the relative tensor. -/
  copair : A ⟶ modTensor A M M'
  /-- The pairing is a module map for the descended action and
  the regular action. -/
  pair_linear :
    haveI := modTensorModObj A M' M
    actLeft A (modTensor A M' M) ≫ pair =
      (A ◁ pair) ≫ μ[A]
  /-- The copairing is a module map for the regular action and
  the descended action. -/
  copair_linear :
    haveI := modTensorModObj A M M'
    μ[A] ≫ copair =
      (A ◁ copair) ≫ actLeft A (modTensor A M M')

end Datum

section Bundles

/-- The pairing of a duality datum, as a module map into the
regular module. -/
noncomputable def ModDualityDatum.pairMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Limits.HasCoequalizers D]
    [∀ Z : D, Limits.PreservesColimitsOfShape Limits.WalkingParallelPair
      (tensorLeft Z)] (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A}
    {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    modTensorMod A M' M ⟶ regularMod A :=
  Mod.Hom.mk' d.pair d.pair_linear

/-- The copairing of a duality datum, as a module map from the
regular module. -/
noncomputable def ModDualityDatum.copairMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Limits.HasCoequalizers D]
    [∀ Z : D, Limits.PreservesColimitsOfShape Limits.WalkingParallelPair
      (tensorLeft Z)] (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A}
    {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    regularMod A ⟶ modTensorMod A M M' :=
  Mod.Hom.mk' d.copair d.copair_linear

end Bundles

section Zigzag

/-- **The zigzag laws of a duality datum.**  Both triangle
identities, stated through the multi-tensor insertion and
contraction constructors: inserting the copairing and contracting
the pairing across the original factor is the identity, on each
side.  These are the dimension-free dualizability
conditions: the inserted `M'` is contracted against the original
`M` (and mirrored), never against its own partner — the latter
composite is the categorical dimension and carries no
information about dualizability. -/
structure ModZigzagDatum
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A]
    {M M' : Mod D A}
    (d : ModDualityDatum A M M') : Prop where
  /-- The zig triangle: insert on the left, contract the
  trailing cross pair, on the single-factor multi-tensor
  at `M`. -/
  zig : zigComposite A d.copair d.pair d.pair_linear =
    𝟙 (modMulti A [M])
  /-- The zag triangle: insert on the right, contract the
  leading cross pair, on the single-factor multi-tensor
  at `M'`. -/
  zag : zagComposite A d.copair d.pair d.pair_linear =
    𝟙 (modMulti A [M'])

/-- **The conclusion of the Key Lemma** (Deligne 2.8), packaged
for the 2.9 consumer: a commutative algebra `B` under `A`,
nonzero in the unit-detection sense, together with a global
point of `modTensor A M' M ⊗ B` on which the base-changed
evaluation returns the unit of `B`.  Multiplication by the point
produces a `B`-linear section of the evaluation, so the unit of
`B` splits off the base change of `modTensor A M' M`. -/
structure SplittingAlgebra
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
  /-- The splitting point: a global element of the pairing's
  source, base-changed to the algebra. -/
  point : 𝟙_ D ⟶ modTensor A M' M ⊗ carrier
  /-- The pairing evaluates the point to the unit of the
  algebra: the section identity. -/
  point_eval : letI := monObj;
    point ≫ (d.pair ▷ carrier) ≫ (ofBase ▷ carrier) ≫
      μ[carrier] = η[carrier]

end Zigzag

section Statement

end Statement

end RS

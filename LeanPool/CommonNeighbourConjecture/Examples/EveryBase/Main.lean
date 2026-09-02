/-
Copyright (c) 2026 Aluna Rizzoli and Adam R. Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aluna Rizzoli, Adam R. Thomas
-/

import LeanPool.CommonNeighbourConjecture.Examples.EveryBase.Irreducible
import LeanPool.CommonNeighbourConjecture.Examples.EveryBase.GeneralConstruction
import LeanPool.CommonNeighbourConjecture.Saxl.PermWreath.Irreducible

/-!
# Counterexamples at every base size

This module instantiates the abstract obstruction construction with the affine
Frobenius groups and their deleted binary permutation modules.
-/

noncomputable section

namespace SaxlCounterexamples.EveryBase

open scoped Pointwise

/-- The concrete binary seed attached to `GF(3^d)`. -/
noncomputable def hqSeed (d : Nat) (hd : Odd d) (hd3 : 3 ≤ d) :
    EveryBaseSeed where
  Ω := Fq d
  H := Hq d
  V := Vq d
  omega0 := 0
  u := hqBadSeedVector d hd
  odd_card_H := hq_odd_card d hd
  regular_exists := hq_regularOrbit_exists d hd
  coord := deletedCoord d
  coord_smul := by
    intro h v ω
    rfl
  u_coord := hqBadSeedVector_apply d hd
  avoidingCycle := hqAvoidingCycle d hd hd3

/-- The canonical regular-tuple colour tower for the concrete seed. -/
noncomputable def hqColourTower (d : Nat) (hd : Odd d) (hd3 : 3 ≤ d) :
    RegularTupleColourTower (hqSeed d hd hd3) :=
  quotientRegularTupleColourTower (hqSeed d hd hd3)

/-- The canonical tuple and vector colours at the requested tail length. -/
noncomputable def hqColours
    (d : Nat) (hd : Odd d) (hd3 : 3 ≤ d) (tail : Nat) :
    BaseArrayColours (hqSeed d hd hd3) tail :=
  quotientBaseArrayColours (hqSeed d hd hd3) tail

/-- A chosen colour at the requested tail length. -/
noncomputable def hqFirstColour
    (d : Nat) (hd : Odd d) (hd3 : 3 ≤ d) (tail : Nat) :
    (hqColours d hd hd3 tail).C :=
  Classical.choice ((hqColourTower d hd hd3).colour_nonempty tail)

/-- The tuple-colour type for the concrete construction. -/
abbrev HqColourType
    (d : Nat) (hd : Odd d) (hd3 : 3 ≤ d) (tail : Nat) :=
  (hqColours d hd hd3 tail).C

/-- The linear permutation-wreath group in the construction. -/
abbrev HqLinearGroup
    (d : Nat) (hd : Odd d) (hd3 : 3 ≤ d) (tail : Nat) :=
  Saxl.PermWreath (Hq d)
    (Equiv.Perm (HqColourType d hd hd3 tail))
    (HqColourType d hd hd3 tail)

/-- The product module on which the linear group acts. -/
abbrev HqProductModule
    (d : Nat) (hd : Odd d) (hd3 : 3 ≤ d) (tail : Nat) :=
  HqColourType d hd hd3 tail → Vq d

/-- The affine permutation group used for base size `tail + 2`. -/
abbrev GBd
    (d : Nat) (hd : Odd d) (hd3 : 3 ≤ d) (tail : Nat) :=
  Saxl.AffineGroup (HqLinearGroup d hd hd3 tail)
    (HqProductModule d hd hd3 tail)

/-- The explicit vector outside the doubled generalized neighborhood. -/
noncomputable def hqBadVector
    (d : Nat) (hd : Odd d) (hd3 : 3 ≤ d) (tail : Nat) :
    HqProductModule d hd hd3 tail :=
  badVector (hqSeed d hd hd3) (hqColours d hd hd3 tail)
    (hqFirstColour d hd hd3 tail)

/-- At base size two, the displayed vertices are nonadjacent. -/
theorem hq_zero_not_generalizedAdjacent_badVector
    (d : Nat) (hd : Odd d) (hd3 : 3 ≤ d) :
    ¬ Saxl.GeneralizedAdjacent (GBd d hd hd3 0)
      (HqProductModule d hd hd3 0) 0
      0 (hqBadVector d hd hd3 0) := by
  rw [Saxl.generalizedAffineAdjacent_iff_mem_kernelSet, sub_zero]
  rintro ⟨z, _hinj, hbase⟩
  apply hqBadSeedVector_not_regular d hd hd3
  intro h hh
  have hcolumn :=
    (permWreath_isBaseTuple_iff (Hq d)
      (Equiv.Perm (HqColourType d hd hd3 0))
      (HqColourType d hd hd3 0) (Vq d)
      (Fin.cons (hqBadVector d hd hd3 0) z)).1 hbase |>.1
        (hqFirstColour d hd hd3 0)
  apply hcolumn h
  intro j
  fin_cases j
  change h • hqBadVector d hd hd3 0 (hqFirstColour d hd hd3 0) =
    hqBadVector d hd hd3 0 (hqFirstColour d hd hd3 0)
  have hvalue : hqBadVector d hd hd3 0 (hqFirstColour d hd hd3 0) =
      hqBadSeedVector d hd := by
    change badVector (hqSeed d hd hd3) (hqColours d hd hd3 0)
      (hqFirstColour d hd hd3 0) (hqFirstColour d hd hd3 0) = _
    rw [badVector_at]
    rfl
  rw [hvalue]
  exact hh

theorem hq_exactBase_and_noCommonNeighbour
    (d : Nat) (hd : Odd d) (hd3 : 3 ≤ d) (tail : Nat) :
    Saxl.ExactBaseSize
        (Saxl.AffineGroup
          (LinearTop (hqSeed d hd hd3) (hqColours d hd hd3 tail))
          (ProductModule (hqSeed d hd hd3) (hqColours d hd hd3 tail)))
        (ProductModule (hqSeed d hd hd3) (hqColours d hd hd3 tail))
        (tail + 2) ∧
      ¬ Saxl.HasCommonNeighbour
        (ProductModule (hqSeed d hd hd3) (hqColours d hd hd3 tail))
        (Saxl.GeneralizedAdjacent
          (Saxl.AffineGroup
            (LinearTop (hqSeed d hd hd3) (hqColours d hd hd3 tail))
            (ProductModule (hqSeed d hd hd3) (hqColours d hd hd3 tail)))
          (ProductModule (hqSeed d hd hd3) (hqColours d hd hd3 tail)) tail)
        0
        (badVector (hqSeed d hd hd3) (hqColours d hd hd3 tail)
          (hqFirstColour d hd hd3 tail)) := by
  let _ : Nontrivial (hqSeed d hd hd3).H := hqNontrivial d
  let _ : Nontrivial (hqSeed d hd hd3).V := vqNontrivial d
  apply abstractCoreFamily
  exact (hqColourTower d hd hd3).linear_exactTupleBaseSize_of_seed tail

theorem hq_linearTop_irreducible
    (d : Nat) (hd : Odd d) (hd3 : 3 ≤ d) (tail : Nat) :
    Representation.IsIrreducible
      (Representation.ofDistribMulAction F2
        (Saxl.PermWreath (Hq d)
          (Equiv.Perm (hqColours d hd hd3 tail).C)
          (hqColours d hd hd3 tail).C)
        ((hqColours d hd hd3 tail).C → Vq d)) := by
  let _ : FaithfulSMul (Hq d) (Vq d) := hq_faithful d hd
  let _ : Nonempty (hqColours d hd hd3 tail).C :=
    (hqColourTower d hd hd3).colour_nonempty tail
  exact Saxl.PermWreath.isIrreducible_of_faithful
    (F := F2) (H := Hq d)
    (Q := Equiv.Perm (hqColours d hd hd3 tail).C)
    (ι := (hqColours d hd hd3 tail).C) (V := Vq d)
    (hq_irreducible d hd) inferInstance

theorem hq_primitive
    (d : Nat) (hd : Odd d) (hd3 : 3 ≤ d) (tail : Nat) :
    MulAction.IsPreprimitive (GBd d hd hd3 tail)
      (HqProductModule d hd hd3 tail) := by
  let _ : Representation.IsIrreducible
      (Representation.ofDistribMulAction F2
        (HqLinearGroup d hd hd3 tail)
        (HqProductModule d hd hd3 tail)) :=
    hq_linearTop_irreducible d hd hd3 tail
  exact Saxl.affine_primitive_of_irreducible
    (HqLinearGroup d hd hd3 tail)
    (HqProductModule d hd hd3 tail) 2

theorem hq_coreFamily
    (d : Nat) (hd : Odd d) (hd3 : 3 ≤ d) (tail : Nat) :
    Saxl.ExactBaseSize (GBd d hd hd3 tail)
        (HqProductModule d hd hd3 tail) (tail + 2) ∧
      MulAction.IsPreprimitive (GBd d hd hd3 tail)
        (HqProductModule d hd hd3 tail) ∧
      ¬ Saxl.HasCommonNeighbour
        (HqProductModule d hd hd3 tail)
        (Saxl.GeneralizedAdjacent (GBd d hd hd3 tail)
          (HqProductModule d hd hd3 tail) tail)
        0 (hqBadVector d hd hd3 tail) := by
  have hcore := hq_exactBase_and_noCommonNeighbour d hd hd3 tail
  refine ⟨?_, hq_primitive d hd hd3 tail, ?_⟩
  · exact hcore.1
  · exact hcore.2

theorem vq_card_le_productModule_card
    (d : Nat) (hd : Odd d) (hd3 : 3 ≤ d) (tail : Nat) :
    Nat.card (Vq d) ≤ Nat.card (HqProductModule d hd hd3 tail) := by
  let c0 : (hqColours d hd hd3 tail).C :=
    Classical.choice ((hqColourTower d hd hd3).colour_nonempty tail)
  refine Nat.card_le_card_of_injective (fun v : Vq d ↦
    (fun _ : (hqColours d hd hd3 tail).C ↦ v)) ?_
  intro v w h
  exact congrFun h c0

end SaxlCounterexamples.EveryBase

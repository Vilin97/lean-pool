/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.IntegerPartSplitting

/-!
# API checks for LM24 integer-part splitting

This separately compiled client checks the exact source and target rings in LM24,
Fact 2.4.2(5), and verifies that the equivalence sends a fixed source series to its split
truncation. The nested coefficient subring excludes the nearby wrong target using the whole
inner Hahn field.
-/

public noncomputable section

namespace Tests

open HahnSeries FiniteArchimedeanClass

theorem integerPartSplitting_apply
    {K G R : Type*}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R)
    (x : Nonpositive.fixedIntegerPartSubring (K := K) (G := G) (R := R) c Z) :
    ((Nonpositive.splitFixedIntegerPartRingEquiv u c Z x :
      truncationIntegerPart (u.stratum c)
        (Nonpositive.innerIntegerPartSubring (K := K) (G := G) c Z)) :
          Nonpositive (u.stratum c) R⟦ball K c⟧) =
      Nonpositive.splitTruncation u c (x : Nonpositive G R) :=
  Nonpositive.coe_splitFixedIntegerPartRingEquiv u c Z x

theorem integerPartSplitting_round_trip
    {K G R : Type*}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R)
    (y : truncationIntegerPart (u.stratum c)
      (Nonpositive.innerIntegerPartSubring (K := K) (G := G) c Z)) :
    Nonpositive.splitFixedIntegerPartRingEquiv u c Z
      ((Nonpositive.splitFixedIntegerPartRingEquiv u c Z).symm y) = y :=
  (Nonpositive.splitFixedIntegerPartRingEquiv u c Z).apply_symm_apply y

end Tests

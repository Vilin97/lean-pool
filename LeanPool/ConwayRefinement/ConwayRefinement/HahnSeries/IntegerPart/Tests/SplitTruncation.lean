/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.SplitTruncation

/-!
# API checks for the LM24 split truncation

This separately compiled client checks the constant-coefficient interface used by LM24,
Proposition 9.2.2.
-/

public noncomputable section

namespace Tests

open HahnSeries FiniteArchimedeanClass

theorem splitTruncation_constantCoeff
    {K G R : Type*}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) :
    Nonpositive.constantCoeff (Nonpositive.splitTruncation u c x) =
      Nonpositive.tauBall c x :=
  Nonpositive.constantCoeff_splitTruncation u c x

theorem splitTruncation_primality_at_one
    {K G R : Type*}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (S : Subring R⟦ball K c⟧) (x : Nonpositive G R)
    (htau : Nonpositive.tauBall c x = 1) :
    IsPrimal (Nonpositive.splitTruncationIntegerPart u c S x
      (htau.symm ▸ S.one_mem)) ↔
      IsPrimal (Nonpositive.splitTruncation u c x) :=
  Nonpositive.isPrimal_splitTruncationIntegerPart_iff_of_tau_eq_one u c S x htau

theorem splitTruncation_primality_at_zero
    {K G R : Type*}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (S : Subring R⟦ball K c⟧) (hfrac : Subring.fracSubring S = ⊤)
    (x : Nonpositive G R) (htau : Nonpositive.tauBall c x = 0) :
    IsPrimal (Nonpositive.splitTruncationIntegerPart u c S x
      (htau.symm ▸ S.zero_mem)) ↔
      IsPrimal (Nonpositive.splitTruncation u c x) :=
  Nonpositive.isPrimal_splitTruncationIntegerPart_iff_of_tau_eq_zero
    u c S hfrac x htau

theorem reduced_splitTruncation_primality
    {K G R : Type*}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    (u : HahnEmbedding.ArchimedeanStrata K G) (b : Nonpositive G R) (hb0 : b ≠ 0)
    (horder : (b : R⟦G⟧).order ≠ 0) (hbReduced : Nonpositive.IsReduced b)
    (S : Subring R⟦ball K (Nonpositive.leadingClass b horder)⟧)
    (hfrac : Subring.fracSubring S = ⊤)
    (htauMem : Nonpositive.tauBall (Nonpositive.leadingClass b horder) b ∈ S) :
    IsPrimal (Nonpositive.splitTruncationIntegerPart u
      (Nonpositive.leadingClass b horder) S b htauMem) ↔
      IsPrimal (Nonpositive.splitTruncation u (Nonpositive.leadingClass b horder) b) :=
  Nonpositive.isPrimal_splitTruncationIntegerPart_iff_of_isReduced
    u b hb0 horder hbReduced S hfrac htauMem

end Tests

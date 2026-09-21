/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.PrimalityTransfer

/-!
# API checks for leading-class primality transfer

This separately compiled client exercises both residue branches of the generic set-level core of
LM24, Proposition 9.2.2. The residue-one branch needs no fraction-field hypothesis; the
residue-zero branch requires exactly that the embedded inner integer part generate the coefficient
Hahn field.
-/

public noncomputable section

namespace Tests

open HahnSeries FiniteArchimedeanClass

theorem primalityTransfer_residue_one
    {K G R : Type*}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    (u : HahnEmbedding.ArchimedeanStrata K G) (Z : Subring R)
    (b : truncationIntegerPart G Z) (hb0 : (b : Nonpositive G R) ≠ 0)
    (horder : ((b : Nonpositive G R) : R⟦G⟧).order ≠ 0)
    (htau : Nonpositive.tauBall (K := K)
      (Nonpositive.leadingClass (b : Nonpositive G R) horder)
      (b : Nonpositive G R) = 1) :
    IsPrimal b ↔
      IsPrimal (Nonpositive.splitTruncation u
        (Nonpositive.leadingClass (b : Nonpositive G R) horder)
        (b : Nonpositive G R)) :=
  Nonpositive.isPrimal_iff_isPrimal_splitTruncation_of_tau_eq_one
    u Z b hb0 horder htau

theorem primalityTransfer_residue_zero
    {K G R : Type*}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    (u : HahnEmbedding.ArchimedeanStrata K G) (Z : Subring R)
    (b : truncationIntegerPart G Z) (hb0 : (b : Nonpositive G R) ≠ 0)
    (horder : ((b : Nonpositive G R) : R⟦G⟧).order ≠ 0)
    (hfrac : Subring.fracSubring
      (Nonpositive.innerIntegerPartSubring (K := K) (G := G)
        (Nonpositive.leadingClass (b : Nonpositive G R) horder) Z) = ⊤)
    (htau : Nonpositive.tauBall (K := K)
      (Nonpositive.leadingClass (b : Nonpositive G R) horder)
      (b : Nonpositive G R) = 0) :
    IsPrimal b ↔
      IsPrimal (Nonpositive.splitTruncation u
        (Nonpositive.leadingClass (b : Nonpositive G R) horder)
        (b : Nonpositive G R)) :=
  Nonpositive.isPrimal_iff_isPrimal_splitTruncation_of_tau_eq_zero
    u Z b hb0 horder hfrac htau

theorem primalityTransfer_reduced
    {K G R : Type*}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    (u : HahnEmbedding.ArchimedeanStrata K G) (Z : Subring R)
    (b : truncationIntegerPart G Z) (hb0 : (b : Nonpositive G R) ≠ 0)
    (horder : ((b : Nonpositive G R) : R⟦G⟧).order ≠ 0)
    (hbReduced : Nonpositive.IsReduced (b : Nonpositive G R))
    (hfrac : Nonpositive.tauBall (K := K)
        (Nonpositive.leadingClass (b : Nonpositive G R) horder)
        (b : Nonpositive G R) = 0 →
      Subring.fracSubring (Nonpositive.innerIntegerPartSubring (K := K) (G := G)
        (Nonpositive.leadingClass (b : Nonpositive G R) horder) Z) = ⊤) :
    IsPrimal b ↔
      IsPrimal (Nonpositive.splitTruncation u
        (Nonpositive.leadingClass (b : Nonpositive G R) horder)
        (b : Nonpositive G R)) :=
  Nonpositive.isPrimal_iff_isPrimal_splitTruncation_of_isReduced
    u Z b hb0 horder hbReduced hfrac

end Tests

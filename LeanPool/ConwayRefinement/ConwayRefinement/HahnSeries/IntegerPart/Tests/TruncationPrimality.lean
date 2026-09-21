/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.TruncationPrimality

/-!
# API checks for primality in a leading-class truncation ring

This separately compiled client checks the source-side localization step used in LM24,
Proposition 9.2.2.
-/

public noncomputable section

namespace Tests

open HahnSeries

theorem primality_in_leading_truncation_subring
    {K G R : Type*}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    (b : Nonpositive G R) (hb0 : b ≠ 0) (horder : (b : R⟦G⟧).order ≠ 0) :
    IsPrimal (Nonpositive.leadingTruncationElement (K := K) b horder) ↔ IsPrimal b :=
  Nonpositive.isPrimal_leadingTruncationElement_iff b hb0 horder

end Tests

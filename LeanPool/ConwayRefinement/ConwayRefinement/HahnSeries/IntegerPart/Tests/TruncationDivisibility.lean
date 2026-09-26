/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.TruncationDivisibility

/-!
# API checks for LM24 truncation divisibility

This separately compiled client certifies Proposition 8.2.1 at the leading class and the full
nonconstant reduced case of Proposition 8.2.8 through their public APIs.
-/

public noncomputable section

namespace Tests

open HahnSeries

theorem leading_truncation_fixes_divisor
    {K G R : Type*}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    (b : Nonpositive G R) (hb0 : b ≠ 0) (horder : (b : R⟦G⟧).order ≠ 0)
    {a : Nonpositive G R} (ha : a ∣ b) :
    Nonpositive.T (K := K) (Nonpositive.leadingClass b horder) a = a :=
  Nonpositive.T_leadingClass_of_dvd b hb0 horder ha

theorem dvd_iff_dvd_leading_truncation
    {K G R : Type*}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    (b : Nonpositive G R) (hb0 : b ≠ 0) (horder : (b : R⟦G⟧).order ≠ 0)
    (c : Nonpositive G R) :
    b ∣ c ↔ b ∣ Nonpositive.T (K := K) (Nonpositive.leadingClass b horder) c :=
  Nonpositive.dvd_iff_dvd_T_leadingClass b hb0 horder c

theorem reduced_dvd_iff_dvd_leading_reduction
    {K G R : Type*}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    (u : HahnEmbedding.ArchimedeanStrata K G) (b : Nonpositive G R) (hb0 : b ≠ 0)
    (horder : (b : R⟦G⟧).order ≠ 0) (hbReduced : Nonpositive.IsReduced b)
    (c : Nonpositive G R) :
    b ∣ c ↔ b ∣ Nonpositive.rho u (Nonpositive.leadingClass b horder) c :=
  Nonpositive.dvd_iff_dvd_rho_leadingClass u b hb0 horder hbReduced c

end Tests

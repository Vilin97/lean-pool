/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.ReducedDivisibility

/-!
# API checks for reduced divisibility

This separately compiled client checks both public conclusions needed from the reduction-algebra
core of LM24, Proposition 8.2.8: `rho(c)` divides `T(c)`, and for a reduced nonconstant divisor
`b`, divisibility of `T(c)` by `b` is equivalent to divisibility of `rho(c)` by `b`.
-/

public noncomputable section

namespace Tests

open HahnSeries

theorem rho_dvd_closed_truncation
    {K G R : Type*}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    (u : HahnEmbedding.ArchimedeanStrata K G) (sigma : FiniteArchimedeanClass G)
    (c : Nonpositive G R) :
    Nonpositive.rho u sigma c ∣ Nonpositive.T (K := K) sigma c :=
  Nonpositive.rho_dvd_T u sigma c

theorem reduced_divisor_dvd_closed_iff_dvd_rho
    {K G R : Type*}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    (u : HahnEmbedding.ArchimedeanStrata K G) (b : Nonpositive G R) (hb0 : b ≠ 0)
    (horder : (b : R⟦G⟧).order ≠ 0) (hbReduced : Nonpositive.IsReduced b)
    (c : Nonpositive G R) :
    b ∣ Nonpositive.T (K := K) (Nonpositive.leadingClass b horder) c ↔
      b ∣ Nonpositive.rho u (Nonpositive.leadingClass b horder) c :=
  Nonpositive.dvd_T_iff_dvd_rho_leadingClass u b hb0 horder hbReduced c

end Tests

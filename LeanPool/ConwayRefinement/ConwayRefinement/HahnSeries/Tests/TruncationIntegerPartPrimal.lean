/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.TruncationIntegerPartPrimal

/-!
# API checks for truncation-integer-part primality

This separately compiled client checks the Hahn-series specialization of LM24, Lemma 9.2.1.
-/

public noncomputable section

namespace Tests

open HahnSeries

theorem truncationIntegerPart_primality_cases
    {G L : Type*}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Field L]
    (Z : Subring L) (b : truncationIntegerPart G Z) :
    IsPrimal b ↔
      (Nonpositive.constantCoeffAlgHom (b : Nonpositive G L) ≠ 0 ∧
        IsPrimal (⟨Nonpositive.constantCoeffAlgHom (b : Nonpositive G L), by
          rw [Nonpositive.constantCoeffAlgHom_apply]
          exact (mem_truncationIntegerPart (R := L) (Γ := G)).mp b.2⟩ : Z) ∧
        IsPrimal (b : Nonpositive G L)) ∨
      (Nonpositive.constantCoeffAlgHom (b : Nonpositive G L) = 0 ∧
        IsPrimal (⟨(b : Nonpositive G L), Subring.le_fracSubring (by
          change Nonpositive.constantCoeffAlgHom (b : Nonpositive G L) ∈ Z
          rw [Nonpositive.constantCoeffAlgHom_apply]
          exact (mem_truncationIntegerPart (R := L) (Γ := G)).mp b.2)⟩ :
          Subring.residueSubring Nonpositive.constantCoeffAlgHom
            (Subring.fracSubring Z))) :=
  Nonpositive.isPrimal_truncationIntegerPart_iff Z b

theorem truncationIntegerPart_primality_at_one
    {G L : Type*}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Field L]
    (Z : Subring L) (b : truncationIntegerPart G Z)
    (hb : Nonpositive.constantCoeffAlgHom (b : Nonpositive G L) = 1) :
    IsPrimal b ↔ IsPrimal (b : Nonpositive G L) :=
  Nonpositive.isPrimal_truncationIntegerPart_iff_of_constantCoeff_eq_one Z b hb

theorem truncationIntegerPart_primality_at_zero
    {G L : Type*}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Field L]
    (Z : Subring L) (hfrac : Subring.fracSubring Z = ⊤)
    (b : truncationIntegerPart G Z)
    (hb : Nonpositive.constantCoeffAlgHom (b : Nonpositive G L) = 0) :
    IsPrimal b ↔ IsPrimal (b : Nonpositive G L) :=
  Nonpositive.isPrimal_truncationIntegerPart_iff_of_constantCoeff_eq_zero Z hfrac b hb

end Tests

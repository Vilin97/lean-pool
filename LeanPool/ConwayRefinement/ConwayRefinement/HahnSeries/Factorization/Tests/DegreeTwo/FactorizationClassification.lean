/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.DegreeTwo.FactorizationClassification

/-!
# Public-interface check for PS06 Lemma 3.1

This separately compiled client exercises the complete factorisation classification through its
public signature. It does not unfold the degree-two support predicates or the critical-point
machinery used in the proof.
-/

universe v

open scoped HahnSeries NatOrdinal

public noncomputable section

namespace Tests

/-- The public PS06 Lemma 3.1 API reproduces the printed constant-or-balanced dichotomy. -/
theorem ps06_degreeTwo_factorization_client
    {K : Type v} [Field K] [CharZero K]
    {a b c : Berarducci.Series K}
    (haNear : a ∉ Berarducci.nearConstantSubgroup K)
    (haType : (a : K⟦ℝ⟧).supportOrderType =
        (Ordinal.omega0 ^ (2 : Ordinal)) ∨
      (a : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (2 : Ordinal) + 1)
    (habc : a = b * c)
    (hle : Berarducci.ordinalValue b ≤ Berarducci.ordinalValue c) :
    (∃ k : K, k ≠ 0 ∧ b = HahnSeries.Nonpositive.C k ∧
      c = HahnSeries.Nonpositive.C k⁻¹ * a ∧
      (c : K⟦ℝ⟧).supportOrderType = (a : K⟦ℝ⟧).supportOrderType) ∨
      (((b : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ∨
          (b : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 + 1) ∧
        ((c : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ∨
          (c : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 + 1) ∧
        Berarducci.ordinalValue b = ω^ (1 : NatOrdinal) ∧
        Berarducci.ordinalValue c = ω^ (1 : NatOrdinal)) :=
  PommersheimShahriari.factorization_cases_of_supportOrderType_wpow_two
    haNear haType habc hle

end Tests

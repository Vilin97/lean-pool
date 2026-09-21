/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.SetOrderType

import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.OrderedUnion
import Mathlib.SetTheory.Ordinal.Principal

/-!
# API certificate for the separated indexed-union estimate

This client applies Berarducci's ordered-union estimate at the infinite factors
`ρ = ω` and `l = ω * 2`. It also proves that the source conclusion `ρ * l` differs from the
reversed product `l * ρ` at these values. Thus the certificate detects a silent reversal of
ordinary ordinal multiplication; a finite or symmetric test would not.
-/

universe u

open Order Ordinal

public noncomputable section

namespace Tests

/-- At `ρ = ω` and `l = ω * 2`, the ordinary product in Berarducci, Lemma 4.7 differs
from the product with its factors reversed. -/
theorem omega_mul_omega_mul_two_ne_omega_mul_two_mul_omega :
    Ordinal.omega0.{u} * (Ordinal.omega0 * 2) ≠
      (Ordinal.omega0 * 2) * Ordinal.omega0 := by
  have htwo : (2 : Ordinal.{u}) * Ordinal.omega0 = Ordinal.omega0 :=
    Ordinal.natCast_mul_omega0 (n := 2) (by simp)
  have hright : (Ordinal.omega0 * 2) * Ordinal.omega0 =
      Ordinal.omega0 * Ordinal.omega0 := by
    calc
      (Ordinal.omega0 * 2) * Ordinal.omega0 =
          Ordinal.omega0 * (2 * Ordinal.omega0) := mul_assoc _ _ _
      _ = Ordinal.omega0 * Ordinal.omega0 := by rw [htwo]
  have hpos : 0 < Ordinal.omega0.{u} * Ordinal.omega0.{u} :=
    mul_pos Ordinal.omega0_pos Ordinal.omega0_pos
  have hleft : Ordinal.omega0 * Ordinal.omega0 <
      Ordinal.omega0 * (Ordinal.omega0 * 2) := by
    rw [← mul_assoc]
    simpa only [mul_one] using
      (mul_lt_mul_of_pos_left (show (1 : Ordinal.{u}) < 2 by simp) hpos)
  exact hright ▸ ne_of_gt hleft

/-- The public ordered-union interface produces the source's ordinary product in the
noncommuting test case `ρ = ω` and `l = ω * 2`. -/
theorem omega_mul_omega_mul_two_le_orderType_iUnion
    {α : Type u} [LinearOrder α]
    (B : (Ordinal.omega0.{u} * 2).ToType → Set α)
    (hB : ∀ i, (B i).IsPWO)
    (hseparated : ∀ {i j}, i < j → ∃ y ∈ B j, ∀ x ∈ B i, x < y)
    (hfinal : ∀ (i : (Ordinal.omega0.{u} * 2).ToType) (C : Set α)
      (hC : IsRelUpperSet C (· ∈ B i)), C.Nonempty →
        Ordinal.omega0 ≤ ((hB i).mono fun _ hx ↦ (hC hx).1).orderType)
    (hUnion : (⋃ i, B i).IsPWO) :
    Ordinal.omega0.{u} * (Ordinal.omega0 * 2) ≤ hUnion.orderType := by
  exact Set.IsPWO.mul_le_orderType_iUnion_of_isSuccLimit
    (l := Ordinal.omega0.{u} * 2) (ρ := Ordinal.omega0.{u})
    (Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 (by simp))
    B hB hseparated hfinal hUnion

end Tests

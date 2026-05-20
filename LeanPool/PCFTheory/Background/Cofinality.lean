/-
Copyright (c) 2026 YnirPaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YnirPaz
-/

import Mathlib.SetTheory.Cardinal.Cofinality
import LeanPool.PCFTheory.Background.Ordinal

/-!
# Cofinality results for indexed suprema

A more general universe version of `iSup_lt_ord_lift` and a related corollary
phrased in terms of `Iio`.
-/

universe u v

open Cardinal Set

namespace Ordinal

/-- A version of `lift_iSup_lt_of_lt_cof` with more general universes. -/
theorem iSup_lt_ord_lift' {ι : Type v} {f : ι → Ordinal.{u}} {c : Ordinal.{u}}
    (hι : Cardinal.lift.{u} #ι < Cardinal.lift.{v} c.cof) : (∀ i, f i < c) → iSup f < c :=
  fun h ↦ lift_iSup_lt_of_lt_cof (by rw [← lift_cof]; exact hι) h

theorem iSup_Iio_lt_ord {δ : Ordinal.{u}} {ℓ : Ordinal.{v}} {f : Iio ℓ → Ordinal.{u}}
    (hf : ∀ i, f i < δ) (hcard : Cardinal.lift.{u} ℓ.card < Cardinal.lift.{v} δ.cof) :
    iSup f < δ := by
  refine iSup_lt_ord_lift' ?_ hf
  · rw [Cardinal.mk_Iio_ordinal, Cardinal.lift_lift]
    have aux1 : Cardinal.lift.{max (v + 1) u, v} ℓ.card =
      Cardinal.lift.{v + 1} (Cardinal.lift.{u, v} ℓ.card) := (Cardinal.lift_lift _).symm
    have aux2 : Cardinal.lift.{v + 1, u} δ.cof =
      Cardinal.lift.{v + 1} (Cardinal.lift.{v, u} δ.cof) := (Cardinal.lift_lift _).symm
    rwa [aux1, aux2, Cardinal.lift_lt]

end Ordinal

/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.Degree
public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.HahnSeries.Basic

/-!
# Degree of a surreal Hahn series

The degree of a Conway normal form is the leading Cantor exponent of the order type of its
support. This is the finite-degree paper's own extension of LM24's degree from `K((ℝ^{≤0}))` to
Conway's series: LM24 names this map and declines it beyond `ℝ` (Remark 3.4.4), its own notion for
a general exponent group being the leading-class degree `deg_σ` (Corollary 8.1.4), to which the
transfer module relates it. It is therefore not a result of LM24 and does not live under
`ConwayRefinement/HahnSeries/Degree/`.

`SurrealHahnSeries` uses supports well-founded under `>`, because its exponent is the exponent of
`ω`, rather than the exponent of LM24's variable `t = ω⁻¹`. Its upstream `length` is therefore
the ordinary order type relevant to LM24 after this sign reversal. It also uses `Shrink` to place
the order type in `Ordinal.{u}`; `SurrealHahnSeries.type_support` identifies its lift with the
unrestricted order type of the support in `Ordinal.{u+1}`.

This file defines degree from that already validated order type. The explicit finite-support
theorem below checks that the universe lowering preserves the source's zero-degree convention.
-/

universe u

public noncomputable section

namespace SurrealHahnSeries

open Ordinal

/-- `deg(ot(b))`, the Cantor degree of `ot(b)`, the order type of the support of a surreal Hahn
series `b` (the upstream `length`); the value at zero is `⊥`. -/
def supportDegree (x : SurrealHahnSeries.{u}) : WithBot NatOrdinal.{u} :=
  Ordinal.cantorDegree x.length

/-- Degree is the leading Cantor exponent of the small support order type. -/
theorem supportDegree_eq_cantorDegree (x : SurrealHahnSeries.{u}) :
    supportDegree x = Ordinal.cantorDegree x.length :=
  (rfl)

@[simp]
theorem supportDegree_eq_bot {x : SurrealHahnSeries.{u}} : supportDegree x = ⊥ ↔ x = 0 := by
  rw [supportDegree, Ordinal.cantorDegree_eq_bot, length_eq_zero]

@[simp]
theorem supportDegree_zero : supportDegree (0 : SurrealHahnSeries.{u}) = ⊥ :=
  supportDegree_eq_bot.mpr rfl

/-- A surreal Hahn series has finite support exactly when its small order type is below `ω`. -/
theorem support_finite_iff_length_lt_omega {x : SurrealHahnSeries.{u}} :
    x.support.Finite ↔ x.length < (Ordinal.omega0 : Ordinal.{u}) := by
  rw [Set.Finite, ← Cardinal.mk_lt_aleph0_iff]
  rw [← Ordinal.card_type (· > ·), type_support, Ordinal.card_lt_aleph0]
  rw [← (Ordinal.lift_omega0 :
    Ordinal.lift.{u + 1, u} (Ordinal.omega0 : Ordinal.{u}) = Ordinal.omega0),
    Ordinal.lift_lt]

/-- Degree zero is equivalent to nonzero finite support. -/
@[simp]
theorem supportDegree_eq_zero {x : SurrealHahnSeries.{u}} :
    supportDegree x = (0 : WithBot NatOrdinal) ↔ x ≠ 0 ∧ x.support.Finite := by
  rw [supportDegree, Ordinal.cantorDegree_eq_zero]
  constructor
  · rintro ⟨hlength, hlt⟩
    exact ⟨length_eq_zero.not.mp hlength, support_finite_iff_length_lt_omega.mpr hlt⟩
  · rintro ⟨hx, hfinite⟩
    exact ⟨length_eq_zero.not.mpr hx, support_finite_iff_length_lt_omega.mp hfinite⟩

/-- This is LM24's maximum characterization of degree in the small support universe. -/
theorem coe_le_supportDegree_iff {x : SurrealHahnSeries.{u}} {a : Ordinal.{u}} (hx : x ≠ 0) :
    (NatOrdinal.of a : WithBot NatOrdinal) ≤ supportDegree x ↔ ω ^ a ≤ x.length := by
  exact Ordinal.coe_le_cantorDegree_iff (length_eq_zero.not.mpr hx)

end SurrealHahnSeries

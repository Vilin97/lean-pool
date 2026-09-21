/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrderType
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.Full
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.Degree

import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.Degree

/-!
# Degree of Conway normal forms in the full Hahn field

This module identifies the support order type used by LM24 with `ot(b)`, the order type of the
support of a Conway normal form `b` (the upstream `length`). The full Hahn exponent is
`Surrealᵒᵈ`, so its increasing support order is exactly the decreasing Conway-exponent order. The
only universe adjustment is the lift already recorded by `SurrealHahnSeries.type_support`.

Consequently, the surreal degree is the Cantor degree of the support order type of the full Hahn
image — the finite-degree paper's extension of LM24's degree to Conway's series, not a notion of
LM24 (Remark 3.4.4). It lies below `ω` exactly when the support order type of the normal form lies
below `ω ^ ω`, which is how the omnific-integer theorem states its hypothesis.
-/

universe u

public noncomputable section

namespace Surreal

private def fullSupportRelIso (x : Surreal.{u}) :
    Subrel (fun a b : Surrealᵒᵈ ↦ a < b) (· ∈ x.toFullHahnSeries.support) ≃r
      (fun a b : x.toHahnSeries.support ↦ a > b) where
  toFun i := ⟨i.1.ofDual, by
    simpa only [support_toHahnSeries] using
      mem_support_toFullHahnSeries.mp i.2⟩
  invFun i := ⟨OrderDual.toDual i.1, by
    apply mem_support_toFullHahnSeries.mpr
    simpa only [OrderDual.ofDual_toDual, support_toHahnSeries] using i.2⟩
  left_inv i := by
    apply Subtype.ext
    simp
  right_inv i := by
    apply Subtype.ext
    simp
  map_rel_iff' := by
    intro i j
    rfl

/-- The full Hahn support order type is the lift of `ot(b)`, the order type of the support of the
Conway normal form. -/
theorem supportOrderType_toFullHahnSeries (x : Surreal.{u}) :
    x.toFullHahnSeries.supportOrderType =
      Ordinal.lift.{u + 1, u} x.length := by
  rw [HahnSeries.supportOrderType_eq_type_of_relIso (fullSupportRelIso x)]
  rw [← length_toHahnSeries]
  exact SurrealHahnSeries.type_support x.toHahnSeries

/-- `deg(ot(b))`, the Cantor degree of `ot(b)`, the order type of the support of the Conway normal
form of a surreal `b`, lifted one universe. -/
def supportDegree (x : Surreal.{u}) : WithBot NatOrdinal.{u + 1} :=
  Ordinal.cantorDegree (Ordinal.lift.{u + 1, u} x.length)

/-- Surreal degree is the Cantor degree of the lifted `ot(b)`. -/
theorem supportDegree_eq_cantorDegree_lift_length (x : Surreal.{u}) :
    x.supportDegree = Ordinal.cantorDegree (Ordinal.lift.{u + 1, u} x.length) :=
  (rfl)

/-- Passing to the full Conway Hahn series preserves degree exactly. -/
@[simp]
theorem supportDegree_toFullHahnSeries (x : Surreal.{u}) :
    x.toFullHahnSeries.degree = x.supportDegree := by
  rw [HahnSeries.degree_eq_cantorDegree,
    supportOrderType_toFullHahnSeries, supportDegree_eq_cantorDegree_lift_length]

/-- A surreal has bottom degree exactly when it is zero. -/
@[simp]
theorem supportDegree_eq_bot {x : Surreal.{u}} : x.supportDegree = ⊥ ↔ x = 0 := by
  rw [← supportDegree_toFullHahnSeries, HahnSeries.degree_eq_bot]
  constructor
  · intro hx
    apply toFullHahnSeries_injective
    rw [hx, toFullHahnSeries_zero]
  · rintro rfl
    exact toFullHahnSeries_zero

/-- A Conway normal form `b` has degree below `ω` exactly when `ot(b)`, the order type of its
support, lies below `ω ^ ω`. -/
theorem supportDegree_lt_omega_iff_length_lt_omega0_opow_omega0 (x : Surreal.{u}) :
    x.supportDegree < (NatOrdinal.of Ordinal.omega0 : WithBot NatOrdinal) ↔
      x.length < Ordinal.omega0 ^ Ordinal.omega0 := by
  rw [← supportDegree_toFullHahnSeries, HahnSeries.degree_lt_coe_iff_supportOrderType_lt_wpow,
    supportOrderType_toFullHahnSeries, NatOrdinal.val_wpow, NatOrdinal.val_of,
    ← Ordinal.lift_omega0_opow_omega0.{u + 1, u}, Ordinal.lift_lt]

end Surreal

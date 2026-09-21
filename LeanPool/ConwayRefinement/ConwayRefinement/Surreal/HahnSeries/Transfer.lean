/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.NormalForm

/-!
# Transfer surreal Hahn-series definitions to surreal numbers

This module transfers coefficients, support, length, and truncation along the Conway normal-form
order equivalence. It follows CombinatorialGames PR #263, adapted to the pinned module-safe API.
Arithmetic compatibility is proved in later modules.
-/

universe u

public noncomputable section

namespace Surreal

open Set

/-! ### Coefficients -/

/-- The coefficient of `ω ^ i` in the Conway normal form of a surreal number. -/
def coeff (x : Surreal) : Surreal → ℝ :=
  x.toHahnSeries.coeff

@[simp]
theorem coeff_zero : coeff 0 = 0 := by
  simp [coeff]

@[simp]
theorem coeff_wpow (x : Surreal) : coeff (ω^ x) = Pi.single x 1 := by
  rw [coeff, toHahnSeries_wpow, SurrealHahnSeries.coeff_single]

/-- A real surreal has only its constant Conway coefficient. -/
@[simp]
theorem coeff_realCast (r : ℝ) :
    coeff (r : Surreal.{u}) = Pi.single 0 r := by
  rw [coeff, toHahnSeries_realCast, SurrealHahnSeries.coeff_single]

@[simp]
theorem coeff_toHahnSeries (x : Surreal) : x.toHahnSeries.coeff = x.coeff :=
  (rfl)

@[simp]
theorem _root_.SurrealHahnSeries.coeff_toSurreal (x : SurrealHahnSeries) :
    x.toSurreal.coeff = x.coeff := by
  simp [coeff]

/-! ### Support -/

/-- The support of the Conway normal form of a surreal number. -/
def support (x : Surreal) : Set Surreal :=
  x.toHahnSeries.support

@[simp]
theorem support_coeff (x : Surreal) : x.coeff.support = x.support :=
  (rfl)

@[simp]
theorem support_zero : support 0 = ∅ := by
  simp [support]

@[simp]
theorem support_wpow (x : Surreal) : support (ω^ x) = {x} := by
  aesop (add simp [support])

/-- The Conway support of a real surreal is finite. -/
theorem support_realCast_finite (r : ℝ) :
    (support (r : Surreal.{u})).Finite := by
  rw [← support_coeff, coeff_realCast]
  exact Set.Finite.subset (Set.finite_singleton 0) Pi.support_single_subset

@[simp]
theorem support_eq_empty {x : Surreal} : x.support = ∅ ↔ x = 0 := by
  simp [support]

@[simp]
theorem support_toHahnSeries (x : Surreal) : x.toHahnSeries.support = x.support :=
  (rfl)

@[simp]
theorem _root_.SurrealHahnSeries.support_toSurreal (x : SurrealHahnSeries) :
    x.toSurreal.support = x.support := by
  simp [support]

theorem wellFoundedOn_support (x : Surreal) : x.support.WellFoundedOn (fun a b ↦ a > b) :=
  x.toHahnSeries.wellFoundedOn_support

instance (x : Surreal.{u}) : Small.{u} x.support :=
  inferInstanceAs (Small (SurrealHahnSeries.support _))

instance (x : Surreal) : WellFoundedGT x.support :=
  inferInstanceAs (WellFoundedGT (SurrealHahnSeries.support _))

/-! ### Length -/

/-- The ordinal length of the Conway normal form of a surreal number. -/
def length (x : Surreal) : Ordinal :=
  x.toHahnSeries.length

@[simp]
theorem length_zero : length 0 = 0 := by
  simp [length]

@[simp]
theorem length_wpow (x : Surreal) : length (ω^ x) = 1 := by
  simp [length]

@[simp, grind =]
theorem mem_support_iff {x i : Surreal} : i ∈ x.support ↔ x.coeff i ≠ 0 :=
  (Iff.rfl)

theorem notMem_support_iff {x i : Surreal} : i ∉ x.support ↔ x.coeff i = 0 :=
  mem_support_iff.not_left

@[simp]
theorem length_toHahnSeries (x : Surreal) : x.toHahnSeries.length = x.length :=
  (rfl)

theorem PartialSum.length_top (x : Surreal) : (⊤ : PartialSum x).length = x.length := by
  rw [PartialSum.length_eq_carrier_length, PartialSum.carrier_top, length_toHahnSeries]

@[simp]
theorem type_support (x : Surreal.{u}) :
    @Ordinal.type x.support (fun a b ↦ a > b) _ = Ordinal.lift.{u + 1} x.length :=
  SurrealHahnSeries.type_support _

@[simp]
theorem _root_.SurrealHahnSeries.length_toSurreal (x : SurrealHahnSeries) :
    x.toSurreal.length = x.length := by
  simp [length]

/-! ### Truncation -/

/-- Remove the terms of the Conway normal form whose exponents are at most `i`. -/
def trunc (x i : Surreal) : Surreal :=
  x.toHahnSeries.trunc i

@[simp]
theorem trunc_zero (i : Surreal) : trunc 0 i = 0 := by
  rw [trunc]
  have h : (0 : SurrealHahnSeries).trunc i = 0 :=
    SurrealHahnSeries.trunc_eq_self fun j hj ↦ by simp at hj
  rw [toHahnSeries_zero, h, SurrealHahnSeries.toSurreal_zero]

@[simp]
theorem toHahnSeries_trunc (x i : Surreal) :
    (x.trunc i).toHahnSeries = x.toHahnSeries.trunc i := by
  simp [trunc]

@[simp]
theorem _root_.SurrealHahnSeries.toSurreal_trunc (x : SurrealHahnSeries) (i : Surreal) :
    x.trunc i = x.toSurreal.trunc i := by
  simp [trunc]

@[aesop simp]
theorem coeff_trunc (x i : Surreal) :
    (x.trunc i).coeff = fun j ↦ if i < j then x.coeff j else 0 := by
  unfold coeff
  aesop

@[simp]
theorem coeff_trunc_of_lt {x i j : Surreal} (h : i < j) :
    (x.trunc i).coeff j = x.coeff j := by
  rw [coeff_trunc]
  exact ite_eq_left h

@[simp]
theorem coeff_trunc_of_le {x i j : Surreal} (h : j ≤ i) :
    (x.trunc i).coeff j = 0 := by
  rw [coeff_trunc]
  exact ite_eq_right h.not_gt

@[simp, grind =]
theorem support_trunc (x i : Surreal) : (x.trunc i).support = x.support ∩ Ioi i := by
  aesop

theorem support_trunc_subset (x i : Surreal) : (x.trunc i).support ⊆ x.support := by
  simp

theorem support_trunc_anti {x : Surreal} : Antitone fun i ↦ (trunc x i).support :=
  fun _ _ _ _ ↦ by aesop (add safe tactic (by order))

theorem coeff_trunc_eq_zero {x i j : Surreal} (h : x.coeff i = 0) :
    (x.trunc j).coeff i = 0 := by
  aesop

theorem coeff_trunc_of_mem {x i j : Surreal} (h : j ∈ (x.trunc i).support) :
    (x.trunc i).coeff j = x.coeff j := by
  aesop

theorem trunc_eq_self_iff {x i : Surreal} : x.trunc i = x ↔ ∀ j ∈ x.support, i < j := by
  nth_rw 2 [← toSurreal_toHahnSeries x]
  rw [trunc, SurrealHahnSeries.toSurreal_inj]
  exact SurrealHahnSeries.trunc_eq_self_iff

alias ⟨_, trunc_eq_self⟩ := trunc_eq_self_iff

theorem trunc_eq_trunc {x i j : Surreal} (h : i ≤ j)
    (H : ∀ k, i < k → k ≤ j → x.coeff k = 0) : x.trunc i = x.trunc j := by
  simpa [← toHahnSeries_trunc] using x.toHahnSeries.trunc_eq_trunc h H

open SurrealHahnSeries in
theorem PartialSum.mem_range_trunc {x : Surreal} (y : PartialSum x) :
    y.carrier.toSurreal ∈ range x.trunc := by
  rw [← truncIdx_length_of_le (y := y) le_top, carrier_truncIdx, carrier_top]
  obtain ⟨z, hz⟩ := truncIdx_mem_range_trunc x.toHahnSeries y.length
  rw [← hz]
  simp

end Surreal

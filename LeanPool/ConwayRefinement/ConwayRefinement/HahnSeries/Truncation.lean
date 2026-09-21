/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.RingTheory.HahnSeries.Addition

/-!
# Coefficient restrictions and truncations of Hahn series

This module restricts a Hahn series to an arbitrary decidable predicate on its exponents. The four
interval restrictions specialize this operation to LM24, Definition 3.2.2. Mathlib already
provides the strict lower truncation `HahnSeries.truncLT`; the definitions here add the weak lower,
weak upper, and strict upper truncations with the same argument order and `ZeroHom` interface.
Every resulting support is a subset of the original support, so these operations preserve any
fixed upper bound on support cardinality used in LM24.

The inequalities use the ambient order on the exponents. Thus `truncLE c x` retains the coefficient
of `x` at `i` exactly when `i ≤ c`; no reversal of the support order occurs.

Mathlib supplies `HahnSeries.truncLT`, which is reused directly. `Finsupp.filter` cannot apply to an
arbitrary well-ordered, possibly infinite support, and CombinatorialGames' surreal truncation uses
its reverse-support representation. The operations here therefore work directly with Hahn-series
coefficients and support proofs.
-/

universe u v

public noncomputable section

namespace HahnSeries

variable {R : Type v} {G : Type u}

section Zero

variable [PartialOrder G] [Zero R]

/-- Keep exactly the coefficients whose indices satisfy `p`. -/
def filter (p : G → Prop) [DecidablePred p] : ZeroHom R⟦G⟧ R⟦G⟧ where
  toFun x :=
    { coeff i := if p i then x.coeff i else 0
      isPWO_support' := x.isPWO_support.mono (by simp) }
  map_zero' := by ext; simp

@[simp]
protected theorem coeff_filter (p : G → Prop) [DecidablePred p] (x : R⟦G⟧) (i : G) :
    (filter p x).coeff i = if p i then x.coeff i else 0 :=
  (rfl)

/-- The support of a coefficient restriction is the corresponding subset of the original support. -/
theorem support_filter (p : G → Prop) [DecidablePred p] (x : R⟦G⟧) :
    (filter p x).support = {i ∈ x.support | p i} := by
  ext i
  simp [and_comm]

theorem support_filter_subset (p : G → Prop) [DecidablePred p] (x : R⟦G⟧) :
    (filter p x).support ⊆ x.support := by
  rw [support_filter]
  exact Set.sep_subset _ _

/-- Keeps exactly the coefficients at indices `i` satisfying `i ≤ c`. -/
def truncLE [DecidableLE G] (c : G) : ZeroHom R⟦G⟧ R⟦G⟧ :=
  filter (· ≤ c)

/-- Keeps exactly the coefficients at indices `i` satisfying `c ≤ i`. -/
def truncGE [DecidableLE G] (c : G) : ZeroHom R⟦G⟧ R⟦G⟧ :=
  filter (c ≤ ·)

/-- Keeps exactly the coefficients at indices `i` satisfying `c < i`. -/
def truncGT [DecidableLT G] (c : G) : ZeroHom R⟦G⟧ R⟦G⟧ :=
  filter (c < ·)

@[simp]
protected theorem coeff_truncLE [DecidableLE G] (c : G) (x : R⟦G⟧) (i : G) :
    (truncLE c x).coeff i = if i ≤ c then x.coeff i else 0 :=
  (rfl)

@[simp]
protected theorem coeff_truncGE [DecidableLE G] (c : G) (x : R⟦G⟧) (i : G) :
    (truncGE c x).coeff i = if c ≤ i then x.coeff i else 0 :=
  (rfl)

@[simp]
protected theorem coeff_truncGT [DecidableLT G] (c : G) (x : R⟦G⟧) (i : G) :
    (truncGT c x).coeff i = if c < i then x.coeff i else 0 :=
  (rfl)

theorem coeff_truncLE_of_le [DecidableLE G] {c i : G} (h : i ≤ c) (x : R⟦G⟧) :
    (truncLE c x).coeff i = x.coeff i := by
  simp [h]

theorem coeff_truncLE_of_lt [DecidableLE G] {c i : G} (h : c < i) (x : R⟦G⟧) :
    (truncLE c x).coeff i = 0 := by
  simp [not_le_of_gt h]

theorem coeff_truncGE_of_le [DecidableLE G] {c i : G} (h : c ≤ i) (x : R⟦G⟧) :
    (truncGE c x).coeff i = x.coeff i := by
  simp [h]

theorem coeff_truncGE_of_lt [DecidableLE G] {c i : G} (h : i < c) (x : R⟦G⟧) :
    (truncGE c x).coeff i = 0 := by
  simp [not_le_of_gt h]

theorem coeff_truncGT_of_lt [DecidableLT G] {c i : G} (h : c < i) (x : R⟦G⟧) :
    (truncGT c x).coeff i = x.coeff i := by
  simp [h]

theorem coeff_truncGT_of_le [DecidableLT G] {c i : G} (h : i ≤ c) (x : R⟦G⟧) :
    (truncGT c x).coeff i = 0 := by
  simp [not_lt_of_ge h]

theorem support_truncLE [DecidableLE G] (c : G) (x : R⟦G⟧) :
    (truncLE c x).support = {i ∈ x.support | i ≤ c} :=
  support_filter _ _

theorem support_truncGE [DecidableLE G] (c : G) (x : R⟦G⟧) :
    (truncGE c x).support = {i ∈ x.support | c ≤ i} :=
  support_filter _ _

theorem support_truncGT [DecidableLT G] (c : G) (x : R⟦G⟧) :
    (truncGT c x).support = {i ∈ x.support | c < i} :=
  support_filter _ _

theorem support_truncLE_subset [DecidableLE G] (c : G) (x : R⟦G⟧) :
    (truncLE c x).support ⊆ x.support :=
  support_filter_subset _ _

theorem support_truncGE_subset [DecidableLE G] (c : G) (x : R⟦G⟧) :
    (truncGE c x).support ⊆ x.support :=
  support_filter_subset _ _

theorem support_truncGT_subset [DecidableLT G] (c : G) (x : R⟦G⟧) :
    (truncGT c x).support ⊆ x.support :=
  support_filter_subset _ _

/-- A weak lower truncation is the original series when the support lies below its cutoff. -/
theorem truncLE_eq_self_of_support_subset_Iic [DecidableLE G]
    {c : G} {x : R⟦G⟧} (h : x.support ⊆ Set.Iic c) :
    truncLE c x = x := by
  ext i
  by_cases hi : i ∈ x.support
  · exact coeff_truncLE_of_le (h hi) x
  · have hcoeff : x.coeff i = 0 := not_ne_iff.mp hi
    simp [hcoeff]

end Zero

section AddMonoid

variable [PartialOrder G] [AddMonoid R]

theorem filter_add (p : G → Prop) [DecidablePred p] (x y : R⟦G⟧) :
    filter p (x + y) = filter p x + filter p y := by
  ext i
  by_cases hi : p i <;> simp [hi]

theorem truncLE_add [DecidableLE G] (c : G) (x y : R⟦G⟧) :
    truncLE c (x + y) = truncLE c x + truncLE c y :=
  filter_add _ _ _

theorem truncGE_add [DecidableLE G] (c : G) (x y : R⟦G⟧) :
    truncGE c (x + y) = truncGE c x + truncGE c y :=
  filter_add _ _ _

theorem truncGT_add [DecidableLT G] (c : G) (x y : R⟦G⟧) :
    truncGT c (x + y) = truncGT c x + truncGT c y :=
  filter_add _ _ _

end AddMonoid

section LinearOrder

variable [LinearOrder G] [AddMonoid R]

/-- A Hahn series is the sum of its strict lower and weak upper truncations. -/
theorem truncLT_add_truncGE (c : G) (x : R⟦G⟧) :
    truncLT c x + truncGE c x = x := by
  ext i
  by_cases hi : i < c
  · simp [hi, not_le_of_gt hi]
  · simp [hi, le_of_not_gt hi]

/-- A Hahn series is the sum of its weak lower and strict upper truncations. -/
theorem truncLE_add_truncGT (c : G) (x : R⟦G⟧) :
    truncLE c x + truncGT c x = x := by
  ext i
  by_cases hi : i ≤ c
  · simp [hi, not_lt_of_ge hi]
  · simp [hi, lt_of_not_ge hi]

end LinearOrder

end HahnSeries

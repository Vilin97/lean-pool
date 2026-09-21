/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.ValuativeRel
/-!
# The p-adic field as a nonarchimedean local field

This file connects Mathlib's normed and valuative structures on `ℚ_p` to
the topology-first local-field interface used by this library.
-/

noncomputable section

open scoped ValuativeRel WithZero

namespace LocalFieldTheory.Padic

variable (p : ℕ) [Fact p.Prime]

/-- The canonical multiplicative valuation of `ℚ_p` is at most one exactly
when the p-adic norm is at most one. -/
theorem mulValuation_le_one_iff_norm_le_one
    (x : ℚ_[p]) :
    Padic.mulValuation (p := p) x ≤ 1 ↔ ‖x‖ ≤ 1 := by
  classical
  by_cases hx : x = 0
  · simp [hx]
  · rw [Padic.norm_le_one_iff_val_nonneg]
    change (if x = 0 then 0 else WithZero.exp (-x.valuation)) ≤ 1 ↔
      0 ≤ x.valuation
    rw [ite_eq_right hx, ← WithZero.exp_zero, WithZero.exp_le_exp, neg_nonpos]

/-- The integer ring defined by the canonical valuative relation on `ℚ_p`
consists exactly of the elements of norm at most one. -/
theorem integer_mem_iff_norm_le_one (x : ℚ_[p]) :
    x ∈ (ValuativeRel.valuation ℚ_[p]).integer ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff,
    ← Valuation.vle_one_iff (ValuativeRel.valuation ℚ_[p]),
    Valuation.vle_one_iff (Padic.mulValuation (p := p)),
    mulValuation_le_one_iff_norm_le_one]

/-- The norm-induced valuation on `ℚ_p` is compatible with the canonical
p-adic valuation ordering. -/
theorem normedFieldValuation_compatible_padic :
    (NormedField.valuation : Valuation ℚ_[p] NNReal).Compatible := by
  classical
  constructor
  intro x y
  rw [(Padic.mulValuation (p := p)).vle_iff_le]
  change Padic.mulValuation x ≤ Padic.mulValuation y ↔ ‖x‖₊ ≤ ‖y‖₊
  rw [← NNReal.coe_le_coe]
  change Padic.mulValuation x ≤ Padic.mulValuation y ↔ ‖x‖ ≤ ‖y‖
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy, hx]
  rw [Padic.norm_eq_zpow_neg_valuation hx,
    Padic.norm_eq_zpow_neg_valuation hy]
  change (if x = 0 then 0 else WithZero.exp (-x.valuation)) ≤
      (if y = 0 then 0 else WithZero.exp (-y.valuation)) ↔
    (p : ℝ) ^ (-x.valuation) ≤ (p : ℝ) ^ (-y.valuation)
  rw [ite_eq_right hx, ite_eq_right hy, WithZero.exp_le_exp]
  have hpone : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  exact (zpow_right_strictMono₀ hpone).le_iff_le.symm

/-- The usual topology on `ℚ_p` is induced by its canonical valuation. -/
theorem padicIsValuativeTopology : IsValuativeTopology ℚ_[p] := by
  let v : Valuation ℚ_[p] NNReal := NormedField.valuation
  let : Valued ℚ_[p] NNReal := NormedField.toValued
  let : v.Compatible := normedFieldValuation_compatible_padic p
  apply IsValuativeTopology.of_mem_nhds_zero_iff_vle v
  intro s
  exact Valued.mem_nhds_zero

/-- Mathlib's p-adic field is a nonarchimedean local field for the
topology-first interface used by local class field theory. -/
noncomputable instance padicIsNonarchimedeanLocalField :
    IsNonarchimedeanLocalField ℚ_[p] where
  toIsValuativeTopology := padicIsValuativeTopology p
  toLocallyCompactSpace := inferInstance
  toIsNontrivial := inferInstance

end LocalFieldTheory.Padic

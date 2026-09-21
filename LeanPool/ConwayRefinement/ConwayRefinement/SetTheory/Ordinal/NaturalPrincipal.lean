/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.NatOrdinal.Pow
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.MultiplicativelyPrincipal

import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.Degree
import Mathlib.Tactic.Ring

/-!
# Principality of the natural operations

Berarducci, Fact 3.7: an additive-principal ordinal is closed under the natural sum of two
strictly smaller ordinals, and a multiplicative-principal ordinal is closed under their natural
product. Both statements are strictly stronger than the closure under the ordinary operations used
to define the two predicates, and both are what the ordinal estimates in Berarducci, Lemma 7.7 and
Lemma 8.2 actually require.

The natural operations are carried by `NatOrdinal`, so each statement converts its arguments with
`NatOrdinal.of` and reads the result back with `NatOrdinal.val`. Convenience forms stated entirely
inside `NatOrdinal` are supplied alongside.

The multiplicative case reduces to `NatOrdinal.cantorDegree_mul` and `NatOrdinal.add_lt_wpow`
through the corrected classification of Berarducci's multiplicative-principal predicate, whose
finite cases `1` and `2` are handled directly.
-/

universe u

open scoped NatOrdinal

public noncomputable section

namespace NatOrdinal

/-- A power of `ω` whose exponent is again a power of `ω` is closed under Hessenberg products. -/
theorem mul_lt_wpow_wpow {a b e : NatOrdinal.{u}}
    (ha : a < ω^ (ω^ e)) (hb : b < ω^ (ω^ e)) : a * b < ω^ (ω^ e) := by
  obtain rfl | ha0 := eq_or_ne a 0
  · simp [wpow_pos]
  obtain rfl | hb0 := eq_or_ne b 0
  · simp [wpow_pos]
  rw [← cantorDegree_lt_coe_iff] at ha hb ⊢
  rw [cantorDegree_mul]
  obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.mp (cantorDegree_eq_bot.not.mpr ha0)
  obtain ⟨y, hy⟩ := WithBot.ne_bot_iff_exists.mp (cantorDegree_eq_bot.not.mpr hb0)
  rw [← hx] at ha ⊢
  rw [← hy] at hb ⊢
  rw [← WithBot.coe_add, WithBot.coe_lt_coe] at *
  exact add_lt_wpow ha hb

end NatOrdinal

namespace Ordinal

/-- Berarducci, Fact 3.7, additive case: an additive-principal ordinal is closed under the natural
sum of two strictly smaller ordinals. -/
theorem IsAdditivelyPrincipal.naturalAdd_lt {o b c : Ordinal.{u}}
    (ho : IsAdditivelyPrincipal o) (hb : b < o) (hc : c < o) :
    (NatOrdinal.of b + NatOrdinal.of c).val < o := by
  obtain ⟨e, rfl⟩ := isAdditivelyPrincipal_iff.mp ho
  rw [show (omega0 ^ e) = (NatOrdinal.of (omega0 ^ e)).val from
    (NatOrdinal.val_of _).symm, NatOrdinal.val.lt_iff_lt]
  simp only [NatOrdinal.of_omega0_opow]
  exact NatOrdinal.add_lt_wpow (by simpa using NatOrdinal.of.lt_iff_lt.mpr hb)
    (by simpa using NatOrdinal.of.lt_iff_lt.mpr hc)

/-- Berarducci, Fact 3.7, multiplicative case: a multiplicative-principal ordinal is closed under
the natural product of two strictly smaller ordinals. -/
theorem IsMultiplicativelyPrincipal.naturalMul_lt {o b c : Ordinal.{u}}
    (ho : IsMultiplicativelyPrincipal o) (hb : b < o) (hc : c < o) :
    (NatOrdinal.of b * NatOrdinal.of c).val < o := by
  rw [show o = (NatOrdinal.of o).val from (NatOrdinal.val_of o).symm,
    NatOrdinal.val.lt_iff_lt]
  rcases isMultiplicativelyPrincipal_iff_one_or_two_or_omega0_opow_opow.mp ho with
    rfl | rfl | ⟨e, rfl⟩
  · rw [Order.lt_one_iff] at hb hc
    subst hb
    subst hc
    simp
  · have hb1 : NatOrdinal.of b ≤ 1 := by
      have h : b ≤ 1 :=
        Order.lt_succ_iff.mp (by rwa [Order.succ_eq_add_one, one_add_one_eq_two])
      simpa using NatOrdinal.of.monotone h
    have hc1 : NatOrdinal.of c ≤ 1 := by
      have h : c ≤ 1 :=
        Order.lt_succ_iff.mp (by rwa [Order.succ_eq_add_one, one_add_one_eq_two])
      simpa using NatOrdinal.of.monotone h
    calc NatOrdinal.of b * NatOrdinal.of c ≤ 1 := by simpa using mul_le_mul' hb1 hc1
      _ < NatOrdinal.of 2 := by simp
  · simp only [NatOrdinal.of_omega0_opow]
    exact NatOrdinal.mul_lt_wpow_wpow (by simpa using NatOrdinal.of.lt_iff_lt.mpr hb)
      (by simpa using NatOrdinal.of.lt_iff_lt.mpr hc)

end Ordinal

namespace NatOrdinal

/-- Berarducci, Fact 3.7, additive case, stated inside `NatOrdinal`. -/
theorem add_lt_of_isAdditivelyPrincipal {o a b : NatOrdinal.{u}}
    (ho : Ordinal.IsAdditivelyPrincipal o.val) (ha : a < o) (hb : b < o) : a + b < o := by
  have h := ho.naturalAdd_lt (val.lt_iff_lt.mpr ha) (val.lt_iff_lt.mpr hb)
  simpa using val.lt_iff_lt.mp (by simpa using h)

/-- Berarducci, Fact 3.7, multiplicative case, stated inside `NatOrdinal`. -/
theorem mul_lt_of_isMultiplicativelyPrincipal {o a b : NatOrdinal.{u}}
    (ho : Ordinal.IsMultiplicativelyPrincipal o.val) (ha : a < o) (hb : b < o) : a * b < o := by
  have h := ho.naturalMul_lt (val.lt_iff_lt.mpr ha) (val.lt_iff_lt.mpr hb)
  simpa using val.lt_iff_lt.mp (by simpa using h)

/-- The natural product of two ordinary products stays strictly below the natural
product of the two multipliers with a multiplicative-principal bound. This is the ordinal
estimate of Berarducci, Lemma 7.7 and Lemma 8.2. -/
theorem naturalMul_mul_lt_of_lt {ρ₁ ρ₂ π₁ π₂ α₁ α₂ : NatOrdinal}
    (hmp : Ordinal.IsMultiplicativelyPrincipal π₂.val)
    (hπ : π₁ ≤ π₂) (hα₁ : α₁ < π₁) (hα₂ : α₂ < π₂)
    (hρ : 0 < ρ₁ * ρ₂) :
    NatOrdinal.of (ρ₁.val * α₁.val) * NatOrdinal.of (ρ₂.val * α₂.val) <
      ρ₁ * ρ₂ * π₂ := by
  have h₁ : NatOrdinal.of (ρ₁.val * α₁.val) ≤ ρ₁ * α₁ := by
    simpa using NatOrdinal.of.le_iff_le.mpr (NatOrdinal.omul_le_mul' ρ₁.val α₁.val)
  have h₂ : NatOrdinal.of (ρ₂.val * α₂.val) ≤ ρ₂ * α₂ := by
    simpa using NatOrdinal.of.le_iff_le.mpr (NatOrdinal.omul_le_mul' ρ₂.val α₂.val)
  calc NatOrdinal.of (ρ₁.val * α₁.val) * NatOrdinal.of (ρ₂.val * α₂.val)
      ≤ (ρ₁ * α₁) * (ρ₂ * α₂) := mul_le_mul' h₁ h₂
    _ = (ρ₁ * ρ₂) * (α₁ * α₂) := by ring
    _ < (ρ₁ * ρ₂) * π₂ := by
        refine mul_lt_mul_of_pos_left ?_ hρ
        exact mul_lt_of_isMultiplicativelyPrincipal hmp (hα₁.trans_le hπ) hα₂

end NatOrdinal

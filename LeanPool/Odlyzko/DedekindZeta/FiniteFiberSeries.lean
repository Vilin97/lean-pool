/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! TODO: Add doc-string. -/

@[expose] public section

namespace NumberField.Odlyzko

theorem tsum_sigma_of_summable {β E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    [ContinuousAdd E] [T3Space E]
    {γ : β → Type*} (w : (Σ b, γ b) → E)
    (hfiber : ∀ b, Summable (fun x : γ b ↦ w ⟨b, x⟩))
    (hw : Summable w) :
    (∑' x, w x) = ∑' b, ∑' x, w ⟨b, x⟩ :=
  Summable.tsum_sigma' hfiber hw

theorem hasSum_inversePower_eq_lSeries_fiberCard
    {α : Type*} (ν : α → ℕ) [∀ n, Finite {a : α // ν a = n}]
    (hν : ∀ a, ν a ≠ 0) {s : ℂ}
    (hsum : Summable (fun a ↦ ((ν a : ℂ) ^ (-s)))) :
    HasSum (fun a ↦ ((ν a : ℂ) ^ (-s)))
      (LSeries (fun n ↦ (Nat.card {a : α // ν a = n} : ℂ)) s) := by
  let e := Equiv.sigmaFiberEquiv ν
  apply e.hasSum_iff.mp
  have hsigma :
      Summable (fun x : Σ n, {a : α // ν a = n} ↦
        ((ν x.2.1 : ℂ) ^ (-s))) :=
    hsum.comp_injective e.injective
  have hfiber (n : ℕ) :
      Summable (fun a : {a : α // ν a = n} ↦
        ((ν a.1 : ℂ) ^ (-s))) :=
    Summable.of_finite
  have hfiberSum (n : ℕ) :
      (∑' a : {a : α // ν a = n}, ((ν a.1 : ℂ) ^ (-s))) =
        LSeries.term
          (fun n ↦ (Nat.card {a : α // ν a = n} : ℂ)) s n := by
    by_cases hn : n = 0
    · subst n
      haveI : IsEmpty {a : α // ν a = 0} :=
        ⟨fun a ↦ (hν a.1) a.2⟩
      simp
    · letI : Fintype {a : α // ν a = n} := Fintype.ofFinite _
      rw [tsum_fintype, LSeries.term_of_ne_zero hn]
      simp_rw [show ∀ a : {a : α // ν a = n}, ν a.1 = n from fun a ↦ a.2]
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card,
        Finset.card_univ, Complex.cpow_neg, div_eq_mul_inv]
  have heq :
      (∑' x : Σ n, {a : α // ν a = n},
        ((ν x.2.1 : ℂ) ^ (-s))) =
        LSeries (fun n ↦ (Nat.card {a : α // ν a = n} : ℂ)) s := by
    calc
      _ = ∑' n, ∑' a : {a : α // ν a = n},
          ((ν a.1 : ℂ) ^ (-s)) :=
        tsum_sigma_of_summable
          (fun x : Σ n, {a : α // ν a = n} ↦
            ((ν x.2.1 : ℂ) ^ (-s))) hfiber hsigma
      _ = ∑' n, LSeries.term
          (fun n ↦ (Nat.card {a : α // ν a = n} : ℂ)) s n := by simp_all
      _ = LSeries (fun n ↦
          (Nat.card {a : α // ν a = n} : ℂ)) s := rfl
  exact heq ▸ hsigma.hasSum

theorem summable_inversePower_of_lSeriesSummable_fiberCard
    {α : Type*} (ν : α → ℕ) [∀ n, Finite {a : α // ν a = n}]
    (hν : ∀ a, ν a ≠ 0) {s : ℂ}
    (hsum :
      LSeriesSummable
        (fun n ↦ (Nat.card {a : α // ν a = n} : ℂ)) s) :
    Summable (fun a ↦ ((ν a : ℂ) ^ (-s))) := by
  rw [← summable_norm_iff]
  let e := Equiv.sigmaFiberEquiv ν
  apply e.summable_iff.mp
  change Summable (fun x : Σ n, {a : α // ν a = n} ↦
    ‖((ν x.2.1 : ℂ) ^ (-s))‖)
  apply (summable_sigma_of_nonneg fun _ ↦ norm_nonneg _).mpr
  constructor
  · intro n
    exact Summable.of_finite
  · have houter :
        (fun n ↦
          ∑' a : {a : α // ν a = n},
            ‖((ν a.1 : ℂ) ^ (-s))‖) =
        (fun n ↦
          ‖LSeries.term
            (fun n ↦ (Nat.card {a : α // ν a = n} : ℂ)) s n‖) := by
      funext n
      by_cases hn : n = 0
      · subst n
        haveI : IsEmpty {a : α // ν a = 0} :=
          ⟨fun a ↦ (hν a.1) a.2⟩
        simp
      · letI : Fintype {a : α // ν a = n} := Fintype.ofFinite _
        rw [tsum_fintype, LSeries.term_of_ne_zero hn]
        simp_rw [show ∀ a : {a : α // ν a = n}, ν a.1 = n from
          fun a ↦ a.2]
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card,
          Finset.card_univ, norm_div, Complex.norm_natCast,
          Complex.cpow_neg, norm_inv, div_eq_mul_inv]
    rw [houter]
    exact hsum.norm

end NumberField.Odlyzko

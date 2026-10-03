/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset

/-!
# Maclaurin's inequality, top case

The origin inequality needs

  `(1/N) ∑ⱼ ∏_{k≠j} bₖ ≤ ((1/N) ∑ₖ bₖ) ^ (N-1)`,

that is `p_{N-1} ≤ p₁^{N-1}` for the elementary symmetric means.  Mathlib has neither
Maclaurin's nor Newton's inequalities, and the usual route to them — real-rootedness of the
derivative, via Rolle — is a sizeable development on its own.

It is not needed.  Writing `E s` for `∑ⱼ ∏_{k≠j}`, splitting off one element gives

  `E (a ::ₘ t) = t.prod + a * E t`,

and after the inductive hypothesis and AM–GM the step reduces, on dividing by `uᴺ` where `u`
is the mean of `t`, to `1 + N(w-1) ≤ wᴺ` — **Bernoulli's inequality**, which Mathlib has.

AM–GM itself is proved here the same way rather than imported, because the Mathlib version is
stated for a `Finset`-indexed family and the whole development uses multisets (roots come as
multisets, and repeated roots must be allowed).  Its induction step reduces to Bernoulli too,
so the two proofs share their only real ingredient.

Neither statement mentions anything Sendov-specific; both are candidates for upstreaming.

## Main statements

* `Sendov.Multiset.prod_le_mean_pow`: `∏ s ≤ (mean s) ^ card s`;
* `Sendov.Multiset.esymm_card_pred_le`: `e_{N-1}(s) ≤ N (mean s)^{N-1}`.
-/

public section

namespace Sendov

open Multiset

variable {a : ℝ} {t : Multiset ℝ}

/-! ### The two Bernoulli steps -/

/-- The AM–GM induction step: `a uᴺ ≤ μ^{N+1}` where `μ` is the mean of `a` together with `N`
copies of `u`.  Dividing by `u^{N+1}` this is Bernoulli. -/
lemma amgm_step (N : ℕ) {u : ℝ} (hu : 0 < u) (ha : 0 ≤ a) :
    a * u ^ N ≤ ((a + N * u) / (N + 1)) ^ (N + 1) := by
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set w : ℝ := (a + N * u) / ((N + 1) * u) with hw
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hbase : (a + (N : ℝ) * u) / ((N : ℝ) + 1) = w * u := by
    rw [hw]; field_simp
  have hber : 1 + ((N : ℝ) + 1) * (w - 1) ≤ w ^ (N + 1) := by
    have := one_add_mul_le_pow (a := w - 1) (by linarith) (N + 1)
    simpa using this
  have hau : a / u = ((N : ℝ) + 1) * w - N := by
    rw [hw]; field_simp; ring
  have hkey : a / u ≤ w ^ (N + 1) := by linarith [hber]
  rw [hbase, mul_pow]
  have : a ≤ w ^ (N + 1) * u := by
    rw [div_le_iff₀ hu] at hkey; linarith
  calc a * u ^ N ≤ (w ^ (N + 1) * u) * u ^ N := by
        exact mul_le_mul_of_nonneg_right this (by positivity)
    _ = w ^ (N + 1) * u ^ (N + 1) := by ring

/-- The Maclaurin induction step. -/
lemma maclaurin_step (N : ℕ) (hN : 1 ≤ N) {u : ℝ} (hu : 0 < u) (ha : 0 ≤ a) :
    u ^ N + N * a * u ^ (N - 1) ≤ ((N : ℝ) + 1) * ((a + N * u) / (N + 1)) ^ N := by
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set w : ℝ := (a + N * u) / ((N + 1) * u) with hw
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hbase : (a + (N : ℝ) * u) / ((N : ℝ) + 1) = w * u := by
    rw [hw]; field_simp
  have hber : 1 + (N : ℝ) * (w - 1) ≤ w ^ N := by
    have := one_add_mul_le_pow (a := w - 1) (by linarith) N
    simpa using this
  have hau : a / u = ((N : ℝ) + 1) * w - N := by
    rw [hw]; field_simp; ring
  -- `u ^ N = u ^ (N-1) * u`
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hpow : u ^ (m + 1) = u ^ m * u := by ring
  rw [hbase, mul_pow]
  simp only [Nat.add_sub_cancel]
  push_cast
  have hkey : 1 + ((m : ℝ) + 1) * (a / u) ≤ ((m : ℝ) + 1 + 1) * w ^ (m + 1) := by
    push_cast at hber hau ⊢
    nlinarith [hber, hau]
  have humpos : (0 : ℝ) < u ^ m := by positivity
  have := mul_le_mul_of_nonneg_right hkey humpos.le
  calc u ^ (m + 1) + ((m : ℝ) + 1) * a * u ^ m
      = (1 + ((m : ℝ) + 1) * (a / u)) * u ^ m * u := by field_simp; ring
    _ ≤ (((m : ℝ) + 1 + 1) * w ^ (m + 1)) * u ^ m * u := by
        exact mul_le_mul_of_nonneg_right this hu.le
    _ = ((m : ℝ) + 1 + 1) * (w ^ (m + 1) * u ^ (m + 1)) := by ring

/-! ### AM–GM -/

/-- **AM–GM for multisets.**  `∏ s ≤ (mean s) ^ card s`. -/
theorem Multiset.prod_le_mean_pow : ∀ (s : Multiset ℝ), (∀ x ∈ s, 0 ≤ x) →
    s.prod ≤ (s.sum / s.card) ^ s.card := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons a t ih =>
    intro hs
    have ha : 0 ≤ a := hs a (mem_cons_self a t)
    have ht : ∀ x ∈ t, 0 ≤ x := fun x hx => hs x (mem_cons_of_mem hx)
    have hIH := ih ht
    have htsum : 0 ≤ t.sum := Multiset.sum_nonneg ht
    have htprod : 0 ≤ t.prod := Multiset.prod_nonneg ht
    simp only [Multiset.card_cons, Multiset.sum_cons, Multiset.prod_cons, Nat.cast_add,
      Nat.cast_one]
    rcases Nat.eq_zero_or_pos t.card with hc | hc
    · -- `t` is empty
      have ht0 : t = 0 := Multiset.card_eq_zero.1 hc
      subst ht0
      simp
    · have hcpos : (0 : ℝ) < t.card := by exact_mod_cast hc
      set u : ℝ := t.sum / t.card with hu
      have hu0 : 0 ≤ u := by rw [hu]; positivity
      have hsum : t.sum = t.card * u := by rw [hu]; field_simp
      rcases eq_or_lt_of_le hu0 with hz | hupos
      · -- `u = 0` forces `t.prod = 0`
        have hzero : t.prod = 0 := by
          have : t.prod ≤ u ^ t.card := hIH
          rw [← hz] at this
          have h0 : (0 : ℝ) ^ t.card = 0 := zero_pow (by omega)
          rw [h0] at this
          linarith
        rw [hzero, mul_zero]
        positivity
      · have hstep := amgm_step (a := a) t.card hupos ha
        calc a * t.prod ≤ a * u ^ t.card := mul_le_mul_of_nonneg_left hIH ha
          _ ≤ ((a + t.card * u) / (t.card + 1)) ^ (t.card + 1) := hstep
          _ = ((a + t.sum) / (t.card + 1)) ^ (t.card + 1) := by rw [hsum]

/-! ### Maclaurin -/

/-- Splitting off one element: `E (a ::ₘ t) = ∏ t + a · E t`. -/
lemma esymm_card_cons (a : ℝ) (t : Multiset ℝ) (ht : t ≠ 0) :
    (a ::ₘ t).esymm t.card = t.prod + a * t.esymm (t.card - 1) := by
  obtain ⟨m, hm⟩ : ∃ m, t.card = m + 1 := ⟨t.card - 1, by
    have : 0 < t.card := Multiset.card_pos.2 ht
    omega⟩
  rw [hm]
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Nat.add_sub_cancel]
  congr 1
  · rw [← hm, Multiset.powersetCard_self]
    simp
  · rw [← Multiset.sum_map_mul_left]
    congr 1
    apply Multiset.map_congr rfl
    intro u _
    simp

/-- **Maclaurin's inequality, top case.**  `e_{N-1}(s) ≤ N (mean s)^{N-1}`. -/
theorem Multiset.esymm_card_pred_le : ∀ (s : Multiset ℝ), (∀ x ∈ s, 0 ≤ x) → s ≠ 0 →
    s.esymm (s.card - 1) ≤ s.card * (s.sum / s.card) ^ (s.card - 1) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _ h; exact absurd rfl h
  | cons a t ih =>
    intro hs _
    have ha : 0 ≤ a := hs a (mem_cons_self a t)
    have ht : ∀ x ∈ t, 0 ≤ x := fun x hx => hs x (mem_cons_of_mem hx)
    have htsum : 0 ≤ t.sum := Multiset.sum_nonneg ht
    have htprod : 0 ≤ t.prod := Multiset.prod_nonneg ht
    have hamgm := Multiset.prod_le_mean_pow t ht
    simp only [Multiset.card_cons, Multiset.sum_cons, Nat.add_sub_cancel, Nat.cast_add,
      Nat.cast_one]
    rcases eq_or_ne t 0 with rfl | ht0
    · simp [Multiset.esymm]
    · have hc : 0 < t.card := Multiset.card_pos.2 ht0
      have hcpos : (0 : ℝ) < t.card := by exact_mod_cast hc
      have hIH := ih ht ht0
      rw [esymm_card_cons a t ht0]
      set u : ℝ := t.sum / t.card with hu
      have hu0 : 0 ≤ u := by rw [hu]; positivity
      have hsum : t.sum = t.card * u := by rw [hu]; field_simp
      rcases eq_or_lt_of_le hu0 with hz | hupos
      · -- `u = 0`
        have hzero : t.prod = 0 := by
          have h0 : (0 : ℝ) ^ t.card = 0 := zero_pow (by omega)
          rw [← hz, h0] at hamgm
          linarith
        have hsum0 : t.sum = 0 := by rw [hsum, ← hz, mul_zero]
        rw [hzero, hsum0, zero_add, add_zero]
        rcases Nat.lt_or_ge t.card 2 with h1 | h2
        · -- `card t = 1`
          have hc1 : t.card = 1 := by omega
          have he0 : t.esymm (t.card - 1) = 1 := by
            rw [hc1]
            simp [Multiset.esymm]
          rw [he0, hc1]
          norm_num
          linarith
        · -- `card t ≥ 2`
          have hz0 : (0 : ℝ) ^ (t.card - 1) = 0 := zero_pow (by omega)
          rw [← hz, hz0, mul_zero] at hIH
          have : a * t.esymm (t.card - 1) ≤ 0 := by nlinarith [hIH, ha]
          have hrhs : (0 : ℝ) ≤ ((t.card : ℝ) + 1) * (a / ((t.card : ℝ) + 1)) ^ t.card := by
            positivity
          linarith
      · have hstep := maclaurin_step (a := a) t.card hc hupos ha
        calc t.prod + a * t.esymm (t.card - 1)
            ≤ u ^ t.card + a * ((t.card : ℝ) * u ^ (t.card - 1)) := by
              have h2 : a * t.esymm (t.card - 1) ≤ a * ((t.card : ℝ) * u ^ (t.card - 1)) :=
                mul_le_mul_of_nonneg_left hIH ha
              linarith [hamgm]
          _ = u ^ t.card + (t.card : ℝ) * a * u ^ (t.card - 1) := by ring
          _ ≤ ((t.card : ℝ) + 1) * ((a + t.card * u) / (t.card + 1)) ^ t.card := hstep
          _ = ((t.card : ℝ) + 1) * ((a + t.sum) / ((t.card : ℝ) + 1)) ^ t.card := by rw [hsum]

end Sendov

/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Egrs75.LogIrrationality
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
EGRS75 two-prime — THE DIOPHANTINE SEED (paper condition (2)), 2026-06-12.

NEW file.  Imports `Equidist_mathlibapi` (for the kernel-clean irrationality
`irrational_log_div_log`) + Mathlib's Dirichlet approximation.  Modifies nothing.

GOAL (`seed_window`): for distinct primes `p q` (q ≥ 3) and every floor `F`,
produce a PURE POWER `p^α` landing in the base-`q` window

    (q-1)/2 · q^(e+3)  <  p^α  <  (q-1)/2 · q^(e+3) + q^(e+1)/4,

with `q^(e+3) > F`.  Such a seed has base-`q` digits:  digit(e+3) = (q-1)/2 = B
(good), digit(e+2) = 0 (STRICTLY good), everything above zero, and the excess
below `q^(e+1)` — exactly the "B-led staircase" start EGRS75 manufacture with
their condition (2) (Math. Comp. 29 (1975), p.84).  `p^α` is automatically
`LowDigits p`.  The iterated repair (file `EgrsSeedClose_2026-06-12.lean`)
consumes this seed and never sinks below `B·q^(e+3)`.

METHOD (fully elementary given Mathlib):
  1. `irrational_log_div_log` (REUSED, kernel-clean): log p / log q ∉ ℚ.
  2. Dirichlet (`Real.exists_int_int_abs_mul_sub_le`): a NONZERO step
     δ = a·log p − b·log q with |δ| < window-width, a ≥ 1.
  3. `walk_hits`: an arithmetic walk with positive step smaller than the window
     width cannot jump over the window — the first crossing lands inside.
  4. Transfer the log-inequalities back to ℕ via exp monotonicity + casts.

No `native_decide`, no `axiom`, no `sorry`.  Formalizes part of the KNOWN
theorem EGRS75 (1975); three primes is Erdős #376 (OPEN) — not attempted.
Recon: ~/Knowledge/Construct/recon/erdos_376.md.
-/

namespace Egrs75.SeedWindow

open Nat
open Egrs75

/-! ## Real-log bridge -/

/-- exp-bridge: `log a < log b → a < b` for positive reals. -/
theorem lt_of_log_lt {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : Real.log a < Real.log b) : a < b := by
  have := Real.exp_lt_exp.mpr h
  rwa [Real.exp_log ha, Real.exp_log hb] at this

/-! ## The walk: a small-step arithmetic progression cannot jump a window -/

/-- **Walk lemma (KERNEL-CLEAN).**  If `0 < δ < w₂ − w₁` and the walk
`start + t·δ` begins below `w₁`, then its FIRST crossing of `w₁` lands strictly
inside `(w₁, w₂)`. -/
theorem walk_hits {δ w₁ w₂ start : ℝ} (hδ0 : 0 < δ) (hδw : δ < w₂ - w₁)
    (hstart : start < w₁) :
    ∃ t : ℕ, 1 ≤ t ∧ w₁ < start + t * δ ∧ start + t * δ < w₂ := by
  classical
  have hex : ∃ T : ℕ, w₁ < start + T * δ := by
    obtain ⟨T, hT⟩ := exists_nat_gt ((w₁ - start) / δ)
    refine ⟨T, ?_⟩
    have := (div_lt_iff₀ hδ0).mp hT
    linarith
  have ht : w₁ < start + (Nat.find hex : ℝ) * δ := Nat.find_spec hex
  set t := Nat.find hex with htdef
  have ht1 : 1 ≤ t := by
    by_contra h
    have h0 : t = 0 := by omega
    rw [h0] at ht
    push_cast at ht
    linarith
  have hprev : ¬ w₁ < start + ((t - 1 : ℕ) : ℝ) * δ := by
    rw [htdef]
    exact Nat.find_min hex (by omega)
  push Not at hprev
  have hcast : ((t : ℕ) : ℝ) = ((t - 1 : ℕ) : ℝ) + 1 := by
    have h : (t - 1) + 1 = t := by omega
    calc ((t : ℕ) : ℝ) = (((t - 1) + 1 : ℕ) : ℝ) := by rw [h]
      _ = ((t - 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  refine ⟨t, ht1, ht, ?_⟩
  have hstep : start + (t : ℝ) * δ = (start + ((t - 1 : ℕ) : ℝ) * δ) + δ := by
    rw [hcast]; ring
  rw [hstep]
  linarith

/-! ## The small nonzero step: Dirichlet + irrationality -/

/-- **Small-step lemma (KERNEL-CLEAN).**  For distinct primes `p q` and any
`ε > 0` there are naturals `a ≥ 1`, `b` with `δ := a·log p − b·log q` NONZERO,
`|δ| < ε`, and `b ≥ 1` whenever `δ < 0`.  Dirichlet supplies the approximation;
the kernel-clean `irrational_log_div_log` rules out `δ = 0`. -/
theorem exists_small_step {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a b : ℕ, 1 ≤ a ∧
      (a : ℝ) * Real.log p - (b : ℝ) * Real.log q ≠ 0 ∧
      |(a : ℝ) * Real.log p - (b : ℝ) * Real.log q| < ε ∧
      ((a : ℝ) * Real.log p - (b : ℝ) * Real.log q < 0 → 1 ≤ b) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hL : 0 < Real.log p := Real.log_pos hp1
  have hM : 0 < Real.log q := Real.log_pos hq1
  set θ : ℝ := Real.log p / Real.log q with hθdef
  have hθpos : 0 < θ := div_pos hL hM
  have hθirr : Irrational θ := MathlibAPI.irrational_log_div_log hp hq hpq
  -- pick n with log q / (n+1) < ε
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (Real.log q / ε)
  set n : ℕ := max n₀ 1 with hndef
  have hnpos : 0 < n := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
  have hsmall : Real.log q / ((n : ℝ) + 1) < ε := by
    have hn0R : Real.log q / ε < (n : ℝ) := by
      have h : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_max_left n₀ 1
      linarith
    have h1 : Real.log q < ε * (n : ℝ) := by
      have := (div_lt_iff₀ hε).mp hn0R
      linarith
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) + 1)]
    nlinarith
  -- Dirichlet at θ
  obtain ⟨j, k, hk0, _hkn, happ⟩ := Real.exists_int_int_abs_mul_sub_le θ hnpos
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hkθ : 0 < (k : ℝ) * θ := mul_pos hkR hθpos
  -- error at most 1/2, so j ≥ 0
  have hhalf : 1 / ((n : ℝ) + 1) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  have hj0 : 0 ≤ j := by
    by_contra hneg
    push Not at hneg
    have hjle : j ≤ -1 := by omega
    have hjR : (j : ℝ) ≤ -1 := by exact_mod_cast hjle
    have h1 : (1 : ℝ) ≤ (k : ℝ) * θ - (j : ℝ) := by linarith
    have h2 : (1 : ℝ) ≤ |(k : ℝ) * θ - (j : ℝ)| := le_trans h1 (le_abs_self _)
    linarith [le_trans happ hhalf]
  -- the step
  have hkt : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg hk0.le)
  have hjt : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg hj0)
  have ha1 : 1 ≤ k.toNat := by omega
  have hδeq : (k.toNat : ℝ) * Real.log p - (j.toNat : ℝ) * Real.log q
      = ((k : ℝ) * θ - (j : ℝ)) * Real.log q := by
    rw [hkt, hjt, hθdef]
    field_simp
  refine ⟨k.toNat, j.toNat, ha1, ?_, ?_, ?_⟩
  · -- nonzero
    rw [hδeq]
    intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · -- kθ = j ⟹ θ = j/k rational
      have hθval : θ = (j : ℝ) / (k : ℝ) := by
        rw [eq_div_iff (ne_of_gt hkR)]
        linarith
      exact hθirr ⟨(j : ℚ) / (k : ℚ), by rw [hθval]; push_cast; ring⟩
    · exact absurd h2 (ne_of_gt hM)
  · -- |δ| < ε
    rw [hδeq, abs_mul, abs_of_pos hM]
    calc |(k : ℝ) * θ - (j : ℝ)| * Real.log q
        ≤ (1 / ((n : ℝ) + 1)) * Real.log q := by
          exact mul_le_mul_of_nonneg_right happ hM.le
      _ = Real.log q / ((n : ℝ) + 1) := by ring
      _ < ε := hsmall
  · -- δ < 0 ⟹ b ≥ 1
    intro hδ0
    by_contra hb
    have hb0 : j.toNat = 0 := by omega
    rw [hb0] at hδ0
    push_cast at hδ0
    have hposs : 0 < (k.toNat : ℝ) * Real.log p := by
      have h1 : (0 : ℝ) < (k.toNat : ℝ) := by exact_mod_cast ha1
      exact mul_pos h1 hL
    linarith

/-! ## The seed window -/

/-- **THE DIOPHANTINE SEED (KERNEL-CLEAN).**  For distinct primes `p q` with
`q ≥ 3` and any floor `F`, there are `α ≥ 1` and `e` with `q^(e+3) > F` and

    (q-1)/2 · q^(e+3)  <  p^α   and   4·p^α < 4·((q-1)/2 · q^(e+3)) + q^(e+1).

So `p^α` (automatically `LowDigits p`) has base-`q` digit `(q-1)/2` at `e+3`,
digit `0` at `e+2`, zeros above `e+3`, and excess `< q^(e+1)` — the EGRS75
condition-(2) staircase seed at arbitrary height. -/
theorem seed_window {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hq3 : 3 ≤ q)
    (hpq : p ≠ q) (F : ℕ) :
    ∃ α e : ℕ, 1 ≤ α ∧ F < q ^ (e + 3) ∧
      (q - 1) / 2 * q ^ (e + 3) < p ^ α ∧
      4 * p ^ α < 4 * ((q - 1) / 2 * q ^ (e + 3)) + q ^ (e + 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hL : 0 < Real.log p := Real.log_pos hp1
  have hM : 0 < Real.log q := Real.log_pos hq1
  have hqR0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hBq1 : 1 ≤ (q - 1) / 2 := by omega
  have hBqR : (1 : ℝ) ≤ (((q - 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hBq1
  set c₁ : ℝ := (((q - 1) / 2 : ℕ) : ℝ) with hc₁def
  set c₂ : ℝ := c₁ + 1 / (4 * (q : ℝ) ^ 2) with hc₂def
  have hc₁pos : 0 < c₁ := by rw [hc₁def]; linarith
  have hquad : (0 : ℝ) < 1 / (4 * (q : ℝ) ^ 2) := by positivity
  have hc₂pos : 0 < c₂ := by rw [hc₂def]; linarith
  have hc₁₂ : c₁ < c₂ := by rw [hc₂def]; linarith
  set w₁ : ℝ := Real.log c₁ with hw₁def
  set w₂ : ℝ := Real.log c₂ with hw₂def
  have hw₁0 : 0 ≤ w₁ := Real.log_nonneg hBqR
  have hw₁₂ : w₁ < w₂ := Real.log_lt_log hc₁pos hc₁₂
  set β₀ : ℕ := max (F + 1) 3 with hβ₀def
  have hβ₀3 : 3 ≤ β₀ := le_max_right _ _
  have hβ₀F : F + 1 ≤ β₀ := le_max_left _ _
  -- the small step
  obtain ⟨a, b, ha1, hδne, hδabs, hδbneg⟩ :=
    exists_small_step hp hq hpq (sub_pos.mpr hw₁₂)
  -- main: α, βe with γ := α·log p − βe·log q ∈ (w₁, w₂), 1 ≤ α, β₀ ≤ βe
  have hmain : ∃ α βe : ℕ, 1 ≤ α ∧ β₀ ≤ βe ∧
      w₁ < (α : ℝ) * Real.log p - (βe : ℝ) * Real.log q ∧
      (α : ℝ) * Real.log p - (βe : ℝ) * Real.log q < w₂ := by
    set δ : ℝ := (a : ℝ) * Real.log p - (b : ℝ) * Real.log q with hδdef
    have habs2 := abs_lt.mp hδabs
    rcases lt_trichotomy δ 0 with hneg | h0 | hpos
    · -- δ < 0: walk γ DOWN from a tall pure power α₀·log p
      have hb1 : 1 ≤ b := hδbneg hneg
      have hδ'0 : 0 < -δ := by linarith
      have hδ'w : -δ < w₂ - w₁ := by linarith [habs2.1]
      obtain ⟨α₀, hα₀⟩ := exists_nat_gt ((w₂ + (β₀ : ℝ) * (w₂ - w₁)) / Real.log p)
      have hα₀L : w₂ + (β₀ : ℝ) * (w₂ - w₁) < (α₀ : ℝ) * Real.log p := by
        have := (div_lt_iff₀ hL).mp hα₀
        linarith
      have hβ₀R0 : (0 : ℝ) ≤ (β₀ : ℝ) * (w₂ - w₁) := by
        have h1 : (0 : ℝ) ≤ (β₀ : ℝ) := by positivity
        have h2 : (0 : ℝ) ≤ w₂ - w₁ := by linarith
        exact mul_nonneg h1 h2
      have hstart : -((α₀ : ℝ) * Real.log p) < -w₂ := by linarith
      obtain ⟨t, ht1, hlo, hhi⟩ :=
        walk_hits hδ'0 (by linarith : -δ < (-w₁) - (-w₂)) hstart
      -- height: t > β₀
      have htβ : β₀ < t := by
        have hwpos : 0 < w₂ - w₁ := by linarith
        have h1 : (β₀ : ℝ) * (w₂ - w₁) < (t : ℝ) * (-δ) := by linarith
        have htδ : (t : ℝ) * (-δ) ≤ (t : ℝ) * (w₂ - w₁) :=
          mul_le_mul_of_nonneg_left (le_of_lt hδ'w) (by positivity)
        have h2 : (β₀ : ℝ) * (w₂ - w₁) < (t : ℝ) * (w₂ - w₁) := lt_of_lt_of_le h1 htδ
        have hβ₀t : (β₀ : ℝ) < (t : ℝ) := lt_of_mul_lt_mul_right h2 (le_of_lt hwpos)
        exact_mod_cast hβ₀t
      have hta : 1 ≤ t * a := Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by omega) (by omega))
      have htb : t ≤ t * b := Nat.le_mul_of_pos_right t (by omega)
      have hid : ((α₀ + t * a : ℕ) : ℝ) * Real.log p - ((t * b : ℕ) : ℝ) * Real.log q
          = -(-((α₀ : ℝ) * Real.log p) + (t : ℝ) * (-δ)) := by
        push_cast
        rw [hδdef]
        ring
      refine ⟨α₀ + t * a, t * b, by omega, by omega, ?_, ?_⟩
      · rw [hid]; linarith
      · rw [hid]; linarith
    · exact absurd h0 hδne
    · -- δ > 0: walk γ UP from −β₀·log q
      have hδw : δ < w₂ - w₁ := habs2.2
      have hstart : -((β₀ : ℝ) * Real.log q) < w₁ := by
        have h1 : (0 : ℝ) < (β₀ : ℝ) := by
          have : (0 : ℕ) < β₀ := by omega
          exact_mod_cast this
        have h2 : 0 < (β₀ : ℝ) * Real.log q := mul_pos h1 hM
        linarith
      obtain ⟨t, ht1, hlo, hhi⟩ := walk_hits hpos hδw hstart
      have hta : 1 ≤ t * a := Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by omega) (by omega))
      have hid : ((t * a : ℕ) : ℝ) * Real.log p - ((t * b + β₀ : ℕ) : ℝ) * Real.log q
          = -((β₀ : ℝ) * Real.log q) + (t : ℝ) * δ := by
        push_cast
        rw [hδdef]
        ring
      refine ⟨t * a, t * b + β₀, by omega, by omega, ?_, ?_⟩
      · rw [hid]; exact hlo
      · rw [hid]; exact hhi
  -- transfer back to ℕ
  obtain ⟨α, βe, hα1, hβe, hγlo, hγhi⟩ := hmain
  have hβe3 : 3 ≤ βe := le_trans hβ₀3 hβe
  refine ⟨α, βe - 3, hα1, ?_, ?_, ?_⟩
  all_goals have hee : βe - 3 + 3 = βe := by omega
  · -- F < q^(βe)
    rw [hee]
    have h2 : F < 2 ^ F := Nat.lt_two_pow_self
    have h3 : (2 : ℕ) ^ F ≤ q ^ F := Nat.pow_le_pow_left (by omega) F
    have h4 : q ^ F ≤ q ^ βe := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · -- left bound
    rw [hee]
    have h1 : Real.log (c₁ * (q : ℝ) ^ βe) < Real.log ((p : ℝ) ^ α) := by
      rw [Real.log_mul (ne_of_gt hc₁pos) (by positivity), Real.log_pow, Real.log_pow]
      have hlogq : Real.log ((q : ℝ) ^ βe) = (βe : ℝ) * Real.log q := Real.log_pow _ _
      linarith [hγlo]
    have h2 : c₁ * (q : ℝ) ^ βe < (p : ℝ) ^ α :=
      lt_of_log_lt (by positivity) (by positivity) h1
    have h3 : (((q - 1) / 2 * q ^ βe : ℕ) : ℝ) < ((p ^ α : ℕ) : ℝ) := by
      push_cast
      rw [hc₁def] at h2
      linarith
    exact_mod_cast h3
  · -- right bound
    rw [hee]
    have h1 : Real.log ((p : ℝ) ^ α) < Real.log (c₂ * (q : ℝ) ^ βe) := by
      rw [Real.log_mul (ne_of_gt hc₂pos) (by positivity), Real.log_pow, Real.log_pow]
      linarith [hγhi]
    have h2 : (p : ℝ) ^ α < c₂ * (q : ℝ) ^ βe :=
      lt_of_log_lt (by positivity) (by positivity) h1
    have hsplit : (q : ℝ) ^ βe = (q : ℝ) ^ (βe - 3 + 1) * (q : ℝ) ^ 2 := by
      rw [← pow_add]
      congr 1
      omega
    have h3 : c₂ * (q : ℝ) ^ βe
        = c₁ * (q : ℝ) ^ βe + (q : ℝ) ^ (βe - 3 + 1) / 4 := by
      rw [hc₂def, hsplit]
      have hq2 : (q : ℝ) ^ 2 ≠ 0 := by positivity
      field_simp
    have h4 : 4 * ((p ^ α : ℕ) : ℝ)
        < 4 * (((q - 1) / 2 * q ^ βe : ℕ) : ℝ) + ((q ^ (βe - 3 + 1) : ℕ) : ℝ) := by
      push_cast
      rw [hc₁def] at h3
      nlinarith [h2, h3]
    exact_mod_cast h4

end Egrs75.SeedWindow

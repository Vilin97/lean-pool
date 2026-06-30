/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/

import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Common

/-!
# Erdős Problem #137: powerful products of consecutive integers (conditional finiteness)

Erdős Problem #137 asks whether the product of `k ≥ 3` consecutive positive integers,
`F k n = n(n+1)⋯(n+k-1)`, can ever be *powerful* (a number `N` with `p ∣ N ⟹ p² ∣ N`).

This file formalizes the deduction that, **under the Granville–Langevin radical lower
bound** `RadLB k` (a consequence of the abc conjecture, taken here as an explicit
hypothesis — it is NOT proved here), `F k n` is powerful for only finitely many `n`,
for each fixed `k ≥ 3`. The underlying mathematics is due to Shorey–Tijdeman (2016)
and Langevin / Granville; this is a formalization of the deduction, not a new result.

## Main results
* `lemma_star` (unconditional): `rad m ^ 2 * B2 m ≤ m ^ 2`.
* `powerful_rad_sq_le`: a powerful `N ≠ 0` satisfies `rad N ^ 2 ≤ N`.
* `erdos137_eventually_not_powerful` / `erdos137_finite` (conditional on `RadLB`, `k ≥ 3`):
  `F k n` is powerful for only finitely many `n`.

The radical bound `RadLB` is the only nonelementary input and appears as a hypothesis.
-/

namespace Erdos137

open scoped BigOperators
open Finset

noncomputable section

/-! ### Definitions -/

/-- The radical of `m`: product of its distinct prime factors. rad(0) = rad(1) = 1 by convention. -/
def rad (m : ℕ) : ℕ := ∏ p ∈ m.factorization.support, p

/-- The 2-full (powerful) part of `m`: product of p^{a_p} over primes with a_p ≥ 2. -/
def B2 (m : ℕ) : ℕ :=
  ∏ p ∈ m.factorization.support.filter (fun p => 2 ≤ m.factorization p), p ^ m.factorization p

/-- Product of k consecutive integers starting at n. -/
def F (k n : ℕ) : ℕ := ∏ i ∈ Finset.range k, (n + i)

/-! ### Auxiliary lemmas -/

/-- Every element of the factorization support is a prime. -/
lemma prime_of_mem_factorization_support {m p : ℕ} (hp : p ∈ m.factorization.support) :
    Nat.Prime p := by
  rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
  exact hp.1

/-
rad(m) ≥ 1 for all m.
-/
lemma rad_pos (m : ℕ) : 1 ≤ rad m := by
  exact Finset.prod_pos fun p hp => Nat.Prime.pos ( prime_of_mem_factorization_support hp )

/-
F(k, n) ≥ 1 when n ≥ 1.
-/
lemma F_pos {k n : ℕ} (hn : 1 ≤ n) : 1 ≤ F k n := by
  exact Nat.one_le_iff_ne_zero.mpr <| Finset.prod_ne_zero_iff.mpr fun i hi => by linarith;

/-
F(k, n) ≠ 0 when n ≥ 1.
-/
lemma F_ne_zero {k n : ℕ} (hn : 1 ≤ n) : F k n ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun _ _ => by positivity;

/-
Each factor n + i ≤ k * n for i < k, when n ≥ 1 and k ≥ 1.
-/
lemma factor_le_mul {k n i : ℕ} (_hk : 1 ≤ k) (hn : 1 ≤ n) (hi : i < k) :
    n + i ≤ k * n := by
  nlinarith

/-
F(k, n) ≤ (k * n) ^ k for n ≥ 1, k ≥ 1.
-/
lemma F_le_pow {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) : F k n ≤ (k * n) ^ k := by
  exact le_trans ( Finset.prod_le_prod' fun _ _ => factor_le_mul hk hn ( Finset.mem_range.mp ‹_› ) )
    ( by norm_num )

/-! ### LEMMA STAR -/

/-
**Lemma Star** (unconditional): rad(m)² · B₂(m) ≤ m² for all m.

Proof idea: express both sides as products over the prime factorization support.
For each prime p with exponent a_p:
- If a_p = 1: LHS contributes p², RHS contributes p² (equal).
- If a_p ≥ 2: LHS contributes p^{2+a_p}, RHS contributes p^{2a_p}, and 2+a_p ≤ 2a_p.
-/
theorem lemma_star (m : ℕ) (hm : m ≠ 0) : rad m ^ 2 * B2 m ≤ m ^ 2 := by
  -- Express m^2 using the prime factorization of m.
  have h_factorization :
      m ^ 2 = ∏ p ∈ (Nat.factorization m).support, p ^ (2 * (Nat.factorization m p)) := by
    conv_lhs => rw [ ← Nat.prod_factorization_pow_eq_self hm ];
    simp +decide [ pow_mul', Finset.prod_pow ];
    rfl;
  -- Express rad(m)^2 * B2(m) using the prime factorization of m.
  have h_rad_B2 : rad m ^ 2 * B2 m = (∏ p ∈ (Nat.factorization m).support,
      p ^ (if 2 ≤ (Nat.factorization m p) then 2 + (Nat.factorization m p) else 2)) := by
    unfold rad B2;
    rw [ ← Finset.prod_pow ]; rw [ Finset.prod_filter ]; rw [ ← Finset.prod_mul_distrib ];
    congr; ext; split_ifs <;> ring;
  rw [ h_factorization, h_rad_B2 ];
  exact Finset.prod_le_prod' fun p hp => Nat.pow_le_pow_right ( Nat.pos_of_mem_primeFactors hp )
    ( by split_ifs <;> linarith [ Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp hp ) ] )

/-! ### Bridge to ℝ -/

/-
Cast of lemma_star to ℝ: B₂(m) ≤ m²/rad(m)².
-/
lemma B2_le_sq_div_rad_sq (m : ℕ) (hm : m ≠ 0) :
    (B2 m : ℝ) ≤ (m : ℝ) ^ 2 / (rad m : ℝ) ^ 2 := by
  rw [ le_div_iff₀ ] <;> norm_cast;
  · linarith [ lemma_star m hm ];
  · exact pow_pos ( rad_pos m ) 2

/-
rad(m) cast to ℝ is positive for m ≠ 0. Actually rad is always ≥ 1.
-/
lemma rad_cast_pos (m : ℕ) : (0 : ℝ) < (rad m : ℝ) := by
  exact_mod_cast rad_pos m

/-! ### RadLB hypothesis and conditional theorem -/

/-- The Granville--Langevin radical lower bound, taken as a hypothesis.
For every ε > 0 there is C > 0 such that rad(F(k,n)) ≥ C · n^{k-1-ε} for all n ≥ 1. -/
def RadLB (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → (rad (F k n) : ℝ) ≥ C * (n : ℝ) ^ ((k : ℝ) - 1 - ε)

/-! ### Erdős #137: conditional finiteness of powerful products -/

/-- `N` is **powerful** if every prime dividing `N` divides it with multiplicity at least two,
i.e. `p ∣ N → p ^ 2 ∣ N` for all primes `p`. -/
def Powerful (N : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ N → p ^ 2 ∣ N

/-- For powerful `N`, the 2-full part `B2 N` is all of `N`. -/
theorem powerful_B2_eq {N : ℕ} (hN : N ≠ 0) (hP : Powerful N) : B2 N = N := by
  unfold B2
  have hfilter : (N.factorization.support.filter (fun p => 2 ≤ N.factorization p))
      = N.factorization.support := by
    apply Finset.filter_true_of_mem
    intro p hp
    have hpprime : p.Prime := prime_of_mem_factorization_support hp
    have hpdvd : p ∣ N := by
      rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
      exact hp.2.1
    have h2 : p ^ 2 ∣ N := hP p hpprime hpdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization hpprime hN).mp h2
  rw [hfilter]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hN]
  rfl

/-- For powerful `N ≠ 0`, `rad N ^ 2 ≤ N`. -/
theorem powerful_rad_sq_le {N : ℕ} (hN : N ≠ 0) (hP : Powerful N) : rad N ^ 2 ≤ N := by
  have hstar := lemma_star N hN
  rw [powerful_B2_eq hN hP] at hstar
  -- hstar : rad N ^ 2 * N ≤ N ^ 2
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hstar' : rad N ^ 2 * N ≤ N * N := by rw [← sq]; exact hstar
  exact Nat.le_of_mul_le_mul_right (by rwa [mul_comm N N] at hstar') hNpos

/-- Main conditional finiteness theorem (k ≥ 3). -/
theorem erdos137_eventually_not_powerful (k : ℕ) (hk : 3 ≤ k) (hRadLB : RadLB k) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ¬ Powerful (F k n) := by
  set ε : ℝ := ((k : ℝ) - 2) / 4 with hε_def
  have hk1 : (1 : ℕ) ≤ k := by omega
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hε_pos : 0 < ε := by rw [hε_def]; nlinarith
  obtain ⟨C, hC_pos, hC⟩ := hRadLB ε hε_pos
  set δ : ℝ := 2 * ((k : ℝ) - 1 - ε) - (k : ℝ) with hδ_def
  have hδ_pos : 0 < δ := by rw [hδ_def, hε_def]; nlinarith
  have hCsq_pos : (0 : ℝ) < C ^ 2 := by positivity
  have hkk_pos : (0 : ℝ) < (k : ℝ) ^ k := pow_pos hkpos k
  have hRatio_pos : (0 : ℝ) < (k : ℝ) ^ k / C ^ 2 := by positivity
  set T : ℝ := ((k : ℝ) ^ k / C ^ 2) ^ (1 / δ) with hT_def
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max T 1)
  refine ⟨N₀, ?_⟩
  intro n hn hPow
  have hN₀gtT : T < (N₀ : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN₀
  have hN₀gt1 : (1 : ℝ) < (N₀ : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN₀
  have hnR : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℕ) ≤ n := by
    have : (1 : ℝ) < (n : ℝ) := lt_of_lt_of_le hN₀gt1 hnR
    exact_mod_cast le_of_lt this
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hrad := hC n hn1
  have hradsq : rad (F k n) ^ 2 ≤ F k n := powerful_rad_sq_le (F_ne_zero hn1) hPow
  have hFle : F k n ≤ (k * n) ^ k := F_le_pow hk1 hn1
  have hcast : (rad (F k n) : ℝ) ^ 2 ≤ ((k : ℝ) * (n : ℝ)) ^ k := by
    have h1 : (rad (F k n) : ℝ) ^ 2 ≤ (F k n : ℝ) := by exact_mod_cast hradsq
    have h2 : (F k n : ℝ) ≤ ((k : ℝ) * (n : ℝ)) ^ k := by
      have := (Nat.cast_le (α := ℝ)).mpr hFle
      rw [Nat.cast_pow, Nat.cast_mul] at this
      exact this
    exact le_trans h1 h2
  have hlowbase : C * (n : ℝ) ^ ((k : ℝ) - 1 - ε) ≤ (rad (F k n) : ℝ) := hrad
  have hlowpos : (0 : ℝ) ≤ C * (n : ℝ) ^ ((k : ℝ) - 1 - ε) := by
    apply mul_nonneg (le_of_lt hC_pos)
    exact Real.rpow_nonneg (le_of_lt hnpos) _
  have hlow : (C * (n : ℝ) ^ ((k : ℝ) - 1 - ε)) ^ 2 ≤ (rad (F k n) : ℝ) ^ 2 :=
    pow_le_pow_left₀ hlowpos hlowbase 2
  have hcombine : (C * (n : ℝ) ^ ((k : ℝ) - 1 - ε)) ^ 2 ≤ ((k : ℝ) * (n : ℝ)) ^ k :=
    le_trans hlow hcast
  have hLHS : (C * (n : ℝ) ^ ((k : ℝ) - 1 - ε)) ^ 2
      = C ^ 2 * (n : ℝ) ^ (2 * ((k : ℝ) - 1 - ε)) := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast ((n : ℝ) ^ ((k : ℝ) - 1 - ε)) 2, ← Real.rpow_mul (le_of_lt hnpos)]
    push_cast
    ring_nf
  have hRHS : ((k : ℝ) * (n : ℝ)) ^ k = (k : ℝ) ^ k * (n : ℝ) ^ (k : ℝ) := by
    rw [mul_pow]
    congr 1
    rw [Real.rpow_natCast]
  rw [hLHS, hRHS] at hcombine
  have hnk_pos : (0 : ℝ) < (n : ℝ) ^ (k : ℝ) := Real.rpow_pos_of_pos hnpos _
  have hsplit : (n : ℝ) ^ (2 * ((k : ℝ) - 1 - ε)) = (n : ℝ) ^ δ * (n : ℝ) ^ (k : ℝ) := by
    rw [← Real.rpow_add hnpos, hδ_def]
    ring_nf
  rw [hsplit] at hcombine
  have hcombine2 : C ^ 2 * (n : ℝ) ^ δ ≤ (k : ℝ) ^ k := by
    have h : C ^ 2 * (n : ℝ) ^ δ * (n : ℝ) ^ (k:ℝ) ≤ (k : ℝ) ^ k * (n : ℝ) ^ (k:ℝ) := by
      rw [mul_assoc]; linarith [hcombine]
    exact le_of_mul_le_mul_right h hnk_pos
  -- T^δ = k^k / C^2
  have hTpow : T ^ δ = (k : ℝ) ^ k / C ^ 2 := by
    rw [hT_def, ← Real.rpow_mul (le_of_lt hRatio_pos)]
    rw [one_div, inv_mul_cancel₀ (ne_of_gt hδ_pos), Real.rpow_one]
  have hT_nonneg : (0 : ℝ) ≤ T := Real.rpow_nonneg (le_of_lt hRatio_pos) _
  have hTltn : T < (n : ℝ) := lt_of_lt_of_le hN₀gtT hnR
  have hmono : T ^ δ < (n : ℝ) ^ δ := Real.rpow_lt_rpow hT_nonneg hTltn hδ_pos
  rw [hTpow] at hmono
  have hfinal : (k : ℝ) ^ k < C ^ 2 * (n : ℝ) ^ δ := by
    have := (div_lt_iff₀ hCsq_pos).mp hmono
    linarith [this, mul_comm (C^2) ((n:ℝ)^δ)]
  exact absurd hcombine2 (not_le.mpr hfinal)

/-- The set of positive `n` for which `F k n` is powerful is finite
(k ≥ 3, conditional on RadLB). -/
theorem erdos137_finite (k : ℕ) (hk : 3 ≤ k) (hRadLB : RadLB k) :
    {n : ℕ | 1 ≤ n ∧ Powerful (F k n)}.Finite := by
  obtain ⟨N₀, hN₀⟩ := erdos137_eventually_not_powerful k hk hRadLB
  apply Set.Finite.subset (Set.finite_Iio N₀)
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  simp only [Set.mem_Iio]
  by_contra hcontra
  push Not at hcontra
  exact hN₀ n hcontra hn.2

end  -- noncomputable section

end Erdos137

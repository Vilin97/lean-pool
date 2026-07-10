/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Conditional upper bound on B₂ via a radical lower bound (Erdős #367)

We formalize the "Langevin route" for the general-k upper bound in Erdős #367,
taking the deep unproven ingredient — a radical lower bound for products of
consecutive integers — as an **explicit hypothesis** (`RadLB`).

## Definitions

* `rad m` — the radical (squarefree kernel) of `m`: product of its distinct prime factors.
* `B2 m` — the powerful (2-full) part of `m`: ∏_{p : v_p(m) ≥ 2} p^{v_p(m)}.
* `F k n` — the product of `k` consecutive integers starting at `n`.

## Main results

* `lemma_star` (unconditional): `rad m ^ 2 * B2 m ≤ m ^ 2`.
* `B2_upper_bound` (conditional on `RadLB`): for every `ε > 0` there is `C' > 0` with
  `B2 (F k n) ≤ C' * n ^ (2 + ε)` for all `n ≥ 1`.
-/

namespace GeneralK

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
  exact le_trans
    (Finset.prod_le_prod' fun _ _ => factor_le_mul hk hn (Finset.mem_range.mp ‹_›))
    (by norm_num)

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
      m ^ 2 = ∏ p ∈ (Nat.factorization m).support,
        p ^ (2 * (Nat.factorization m p)) := by
    conv_lhs => rw [ ← Nat.prod_factorization_pow_eq_self hm ];
    simp +decide [ pow_mul', Finset.prod_pow ];
    rfl;
  -- Express rad(m)^2 * B2(m) using the prime factorization of m.
  have h_rad_B2 :
      rad m ^ 2 * B2 m =
        (∏ p ∈ (Nat.factorization m).support,
          p ^ (if 2 ≤ (Nat.factorization m p) then
            2 + (Nat.factorization m p)
          else
            2)) := by
    unfold rad B2;
    rw [ ← Finset.prod_pow ]; rw [ Finset.prod_filter ];
    rw [ ← Finset.prod_mul_distrib ]; congr; ext; split_ifs <;> ring;
  rw [ h_factorization, h_rad_B2 ];
  exact Finset.prod_le_prod' fun p hp =>
    Nat.pow_le_pow_right (Nat.pos_of_mem_primeFactors hp) (by
      split_ifs <;> linarith [Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)])

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

/-- The "Langevin route" radical lower bound, taken as a hypothesis.
For every ε > 0 there is C > 0 such that rad(F(k,n)) ≥ C · n^{k-1-ε} for all n ≥ 1. -/
def RadLB (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      (rad (F k n) : ℝ) ≥ C * (n : ℝ) ^ ((k : ℝ) - 1 - ε)

/-
**Conditional theorem**: assuming RadLB, for every ε > 0 there is C' > 0 with
B₂(F(k,n)) ≤ C' · n^{2+ε} for all n ≥ 1.

This isolates the logical core of the proposed "Langevin route" argument for the
general-k upper bound in Erdős #367.
-/
theorem B2_upper_bound (k : ℕ) (hk : 1 ≤ k) (hRadLB : RadLB k) :
    ∀ ε : ℝ, 0 < ε → ∃ C' : ℝ, 0 < C' ∧
      ∀ n : ℕ, 1 ≤ n → (B2 (F k n) : ℝ) ≤ C' * (n : ℝ) ^ ((2 : ℝ) + ε) := by
  intro ε hε_pos
  obtain ⟨C, hC_pos, hC⟩ :
      ∃ C : ℝ, 0 < C ∧
        ∀ n : ℕ, 1 ≤ n →
          (rad (F k n) : ℝ) ≥ C * (n : ℝ) ^ ((k : ℝ) - 1 - ε / 2) := by
    exact hRadLB ( ε / 2 ) ( half_pos hε_pos )
  use ((k : ℝ) ^ (2 * k)) / C ^ 2
  constructor
  · positivity
  · intro n hn
    -- By B2_le_sq_div_rad_sq (using F_ne_zero for F k n ≠ 0):
    have h_B2_le :
        (B2 (F k n) : ℝ) ≤
          ((k : ℝ) * (n : ℝ)) ^ (2 * k) /
            (C * (n : ℝ) ^ ((k : ℝ) - 1 - ε / 2)) ^ 2 := by
      refine le_trans ( B2_le_sq_div_rad_sq _ <| F_ne_zero hn ) ?_;
      gcongr;
      · exact_mod_cast by
          rw [ pow_mul' ]
          exact pow_le_pow_left₀ (Nat.cast_nonneg _) (F_le_pow hk hn) _
      · exact hC n hn;
    convert h_B2_le using 1; ring;
    norm_num [ sq, mul_assoc, ← Real.rpow_add ( by positivity : 0 < ( n : ℝ ) ),
      ← Real.rpow_neg ( by positivity : 0 ≤ ( n : ℝ ) ) ]; ring;
    exact Or.inl (by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity)]
      push_cast
      ring)

-- Remark (not part of the proof):
-- ∏_{i=0}^{k-1} B₂(n+i) ≤ B₂(F(n)) up to a factor depending only on k
-- (the only shared primes among the n+i are ≤ k), so the theorem also bounds
-- the Erdős #367 product ∏ B₂(n+i) ≪ n^{2+ε}.
-- For k=3 the hypothesis RadLB is a THEOREM under abc (via the identity
-- (n+1)² = n(n+2)+1); for k ≥ 4 whether RadLB holds is open.

end

end GeneralK

/-
Copyright (c) 2026 Junqi Liu, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jujian Zhang
-/

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorization.LCM
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.PrimeCounting

/-!
# LeanPool.Zeta3Irrational.D
-/

namespace LeanPool.Zeta3Irrational

open scoped Nat
open BigOperators

/-- The least common multiple of a finite set of natural numbers. -/
def d (s : Finset ℕ) : ℕ := s.lcm id

theorem d_insert (s : Finset ℕ) (n : ℕ) : d (insert n s) = Nat.lcm n (d s) := by
  simp only [d, Finset.lcm_insert, id_eq]
  rfl

theorem d_empty : d (∅ : Finset ℕ) = 1 := by simp [d]

theorem dvd_d_of_mem (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ d s :=
  Finset.dvd_lcm h

theorem d_dvd_d_of_le (s t : Finset ℕ) (h : s ≤ t) : d s ∣ d t := by
  apply Finset.lcm_dvd
  intro n hn
  exact dvd_d_of_mem t n (h hn)

theorem d_ne_zero (s : Finset ℕ) (hs : 0 ∉ s) : d s ≠ 0 := by
  delta d
  intro r
  rw [Finset.lcm_eq_zero_iff] at r
  exact hs (by simpa using r)

theorem d_eq_zero (s : Finset ℕ) (hs : 0 ∈ s) : d s = 0 := by
  delta d
  rw [Finset.lcm_eq_zero_iff]
  simpa

theorem Nat_Prime_dvd_lcm {p} (hp : Nat.Prime p) (a b) (h : p ∣ Nat.lcm a b) :
    p ∣ a ∨ p ∣ b := by
  have := h.trans <| Nat.lcm_dvd_mul a b
  rwa [Nat.Prime.dvd_mul hp] at this

theorem Nat_primeFactors_lcm {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a.lcm b).primeFactors = a.primeFactors ∪ b.primeFactors := by
  ext p
  rw [Nat.mem_primeFactors_iff_mem_primeFactorsList, Finset.mem_union,
    Nat.mem_primeFactors_iff_mem_primeFactorsList, Nat.mem_primeFactors_iff_mem_primeFactorsList]
  simp only [Nat.mem_primeFactorsList', ne_eq]
  constructor
  · rintro ⟨hp1, hp2, hp3⟩
    obtain hp4 | hp4 := Nat_Prime_dvd_lcm hp1 a b hp2
    · left; refine ⟨hp1, hp4, ?_⟩
      contrapose! hp3
      subst hp3
      simp
    · right; refine ⟨hp1, hp4, ?_⟩
      contrapose! hp3
      subst hp3
      simp
  · rintro (⟨hp1, hp2, hp3⟩|⟨hp1, hp2, hp3⟩)
    · refine ⟨hp1, hp2.trans <| dvd_lcm_left a b, ?_⟩
      contrapose! hp3
      erw [lcm_eq_zero_iff] at hp3
      refine hp3.elim id fun hb' => absurd hb' hb
    · refine ⟨hp1, hp2.trans <| dvd_lcm_right a b, ?_⟩
      contrapose! hp3
      erw [lcm_eq_zero_iff] at hp3
      refine hp3.elim (fun ha' => absurd ha' ha) id

theorem Nat_lcm_pow_two (a b : ℕ) : (Nat.lcm a b) ^ 2 = Nat.lcm (a ^ 2) (b ^ 2) := by
  by_cases ha : a = 0
  · subst ha
    simp
  by_cases hb : b = 0
  · subst hb
    simp
  apply Nat.eq_of_factorization_eq
  · exact pow_ne_zero 2 (Nat.lcm_ne_zero ha hb)
  · exact Nat.lcm_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hb)
  intro p
  rw [Nat.factorization_pow, Nat.factorization_lcm ha hb,
    Nat.factorization_lcm (pow_ne_zero 2 ha) (pow_ne_zero 2 hb), Nat.factorization_pow,
    Nat.factorization_pow]
  simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.sup_apply]
  change 2 * (a.factorization p ⊔ b.factorization p) =
    2 * a.factorization p ⊔ 2 * b.factorization p
  exact mul_max_of_nonneg _ _ (Nat.zero_le 2)

theorem Nat_lcm_pow_three (a b : ℕ) :
    (Nat.lcm a b) ^ 3 = Nat.lcm (a ^ 3) (b ^ 3) := by
  by_cases ha : a = 0
  · subst ha
    simp
  by_cases hb : b = 0
  · subst hb
    simp
  apply Nat.eq_of_factorization_eq
  · exact pow_ne_zero 3 (Nat.lcm_ne_zero ha hb)
  · exact Nat.lcm_ne_zero (pow_ne_zero 3 ha) (pow_ne_zero 3 hb)
  intro p
  rw [Nat.factorization_pow, Nat.factorization_lcm ha hb,
    Nat.factorization_lcm (pow_ne_zero 3 ha) (pow_ne_zero 3 hb), Nat.factorization_pow,
    Nat.factorization_pow]
  simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.sup_apply]
  change 3 * (a.factorization p ⊔ b.factorization p) =
    3 * a.factorization p ⊔ 3 * b.factorization p
  exact mul_max_of_nonneg _ _ (Nat.zero_le 3)

theorem d_sq (s : Finset ℕ) : (d s)^2 = d (s.image (· ^ 2)) := by
  induction s using Finset.induction_on with
  | empty => simp [d]
  | @insert i s hi ih =>
    rw [d_insert, Finset.image_insert, d_insert, ← ih, Nat_lcm_pow_two]

theorem d_cube (s : Finset ℕ) : (d s)^3 = d (s.image (· ^ 3)) := by
  induction s using Finset.induction_on with
  | empty => simp [d]
  | @insert i s hi ih =>
    rw [d_insert, Finset.image_insert, d_insert, ← ih, Nat_lcm_pow_three]

theorem d_sq' (n : ℕ) :
    d (Finset.Icc 1 n)^2 = d (Finset.Icc 1 n |>.image (· ^ 2))  := d_sq _

theorem d_cube' (n : ℕ) :
    d (Finset.Icc 1 n)^3 = d (Finset.Icc 1 n |>.image (· ^ 3))  := d_cube _

theorem fin_d_neq_zero (n : ℕ) : d (Finset.Icc 1 n) > 0 := by
  suffices d (Finset.Icc 1 n) ≠ 0 by omega
  apply d_ne_zero
  simp only [Finset.mem_Icc, nonpos_iff_eq_zero, one_ne_zero, zero_le, and_true, not_false_eq_true]

theorem lcm_factorization (m n p : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    (m.lcm n).factorization p = max (m.factorization p) (n.factorization p) := by
  rw [Nat.factorization_lcm hm hn]
  aesop

theorem d_factorization (s : Finset ℕ) (hs : s.Nonempty) (p : ℕ) (hs₁ : 0 ∉ s) :
    (d s).factorization p =
    (s.image fun i => i.factorization p).max' (by aesop) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.not_nonempty_empty] at hs
  | @insert m s hm ih =>
    rw [d_insert, lcm_factorization _ _ _]
    · if hs : s.Nonempty
      then
      simp only [Finset.image_insert]
      have hs₀ : 0 ∉ s := by
        intro h0
        exact hs₁ (Finset.mem_insert_of_mem h0)
      rw [ih hs hs₀]
      rw [Finset.max'_insert]
      else
      simp only [Finset.not_nonempty_iff_eq_empty] at hs
      subst hs
      simp only [d_empty, Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply, zero_le,
        max_eq_left, insert_empty_eq, Finset.image_singleton, Finset.max'_singleton]
    · aesop
    · apply d_ne_zero
      aesop

theorem d_factorization' (s : Finset ℕ) (hs : s.Nonempty) (p : ℕ) (hs₁ : 0 ∉ s) :
    ((d s).factorization p : ℝ) =
    (((s.image fun (i : ℕ) => (i.factorization p : ℝ)))).max' (by aesop) := by
  rw [d_factorization s hs p hs₁]
  induction s using Finset.induction_on with
  | empty => simp only [Finset.not_nonempty_empty] at hs
  | @insert m s _ ih =>
    simp_rw [Finset.image_insert]
    if hs : s.Nonempty
    then
    symm
    rw [Finset.max'_insert (H := by aesop)]
    specialize ih hs (by aesop)
    rw [← ih, ← Nat.cast_max]
    norm_cast
    rw [← Finset.max'_insert (H := by aesop)]
    else
    aesop

theorem d_primeFactors (s : Finset ℕ) (hs : 0 ∉ s) :
    (d s).primeFactors = s.sup fun i => i.primeFactors := by
   induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sup_empty, Finset.bot_eq_empty, Nat.primeFactors_eq_empty]
    right
    simp only [d_empty]
  | @insert m s hm ih =>
    simp only [Finset.mem_insert, not_or] at hs
    rw [d_insert, Nat_primeFactors_lcm (by aesop) (d_ne_zero _ (by aesop))]
    simp only [Finset.sup_insert, Finset.sup_eq_union]
    rw [ih (by aesop)]

theorem d_factorization_eq_div_log'' (p : ℕ) :
    (d (Finset.Icc 1 0)).factorization p =
    ⌊Real.log 0 / Real.log p⌋₊ := by
  simp [d_empty]

theorem d_factorization_eq_div_log' (n p : ℕ) (hp : Nat.Prime p) :
    (d (Finset.Icc 1 (n + 1))).factorization p =
    ⌊Real.log (n + 1) / Real.log p⌋₊ := by
  symm
  rw [Real.log_div_log]
  rw [Nat.floor_eq_iff]
  · rw [d_factorization' (s := Finset.Icc 1 (n + 1)) (hs := by exact ⟨1, by simp⟩)
      (p := p) (hs₁ := by simp)]
    · constructor
      · rw [Finset.max'_le_iff]
        intro y hy
        rw [Real.le_logb_iff_rpow_le]
        · simp only [Finset.mem_image, Finset.mem_Icc] at hy
          obtain ⟨x, hx, rfl⟩ := hy
          have h := @Nat.pow_factorization_choose_le p x 1 (by omega)
          norm_cast
          simp only [Nat.choose_one_right] at h
          linarith
        · norm_cast
          exact Nat.Prime.one_lt hp
        · norm_cast
          omega
      · rw [← sub_lt_iff_lt_add]
        · by_contra! h
          rw [Finset.max'_le_iff] at h
          set y := (Finset.image (fun i ↦ i.factorization p)
            (Finset.Icc 1 (n + 1))).max' (by aesop)
          have hy : (y : ℝ) ∈
              (Finset.image (fun i ↦ (i.factorization p : ℝ)) (Finset.Icc 1 (n + 1))) := by
            simp only [Finset.mem_image, Finset.mem_Icc, Nat.cast_inj]
            simp_rw [← Finset.mem_Icc]
            rw [← Finset.mem_image]
            exact Finset.max'_mem _ _
          specialize h (y : ℝ) hy
          rw [le_sub_iff_add_le, Real.le_logb_iff_rpow_le] at h
          · have h2 : y + 1 ∉
                (Finset.image (fun i ↦ i.factorization p) (Finset.Icc 1 (n + 1))) := by
              by_contra! hy1
              suffices y + 1 ≤ y by linarith
              exact Finset.le_max' _ _ hy1
            simp only [Finset.mem_image, Finset.mem_Icc, not_exists, not_and, and_imp] at h2
            norm_cast at h
            specialize h2 (p ^ (y + 1)) (by exact one_le_pow_of_one_le' (Nat.Prime.one_le hp) _) h
            aesop
          · norm_cast
            exact Nat.Prime.one_lt hp
          · norm_cast
            omega
  · apply Real.logb_nonneg
    · norm_cast
      exact Nat.Prime.one_lt hp
    · norm_cast
      omega

theorem d_factorization_eq_div_log (n p : ℕ) (hp : Nat.Prime p) :
    (d (Finset.Icc 1 n)).factorization p =
    ⌊Real.log n / Real.log p⌋₊ := by
  cases n
  · simp only [zero_lt_one, Finset.Icc_eq_empty_of_lt, d_empty, Nat.factorization_one,
    Finsupp.coe_zero, Pi.zero_apply, CharP.cast_eq_zero, Real.log_zero, zero_div, Nat.floor_zero]
  · rw [d_factorization_eq_div_log' (hp := hp)]
    simp

theorem d_eq_prod_pow' (n : ℕ) :
    d (Finset.Icc 1 (n + 1)) =
    ∏ p ∈ (((n + 1) + 1).primesBelow),
      p ^ ((Finset.Icc 1 (n + 1)).image (fun i => i.factorization p)).max' (by aesop) := by
  rw [← Nat.prod_factorization_pow_eq_self (n := d (Finset.Icc 1 (n + 1)))]
  · simp only [Finsupp.prod, Nat.support_factorization]
    rw [d_primeFactors _ (by aesop)]
    refine Finset.prod_congr ?_ ?_
    · ext p
      constructor <;> intro hp
      · rw [Finset.mem_sup] at hp
        obtain ⟨m, H, h⟩ := hp
        simp only [Finset.mem_Icc] at H
        rw [Nat.mem_primesBelow]
        simp only [Nat.mem_primeFactors, ne_eq] at h
        constructor
        · linarith [Nat.le_of_dvd (by omega) h.2.1]
        · exact h.1
      · rw [Finset.mem_sup]
        use p
        simp only [Finset.mem_Icc, Nat.mem_primeFactors, dvd_refl, ne_eq, true_and]
        rw [Nat.mem_primesBelow] at hp
        constructor
        · exact ⟨Nat.Prime.one_le hp.2, (by linarith)⟩
        · aesop
    · intro p _
      rw [d_factorization (s := Finset.Icc 1 (n + 1)) (hs := by exact ⟨1, by simp⟩)
        (p := p) (hs₁ := by simp)]
  · apply d_ne_zero
    aesop

theorem d_eq_prod_pow'' (n : ℕ) :
    d (Finset.Icc 1 (n + 1)) =
    ∏ p ∈ (((n + 1) + 1).primesBelow),
      p ^ ⌊(Real.log ((n + 1) : ℝ)) / (Real.log (p : ℝ))⌋₊ := by
  rw [d_eq_prod_pow']
  refine Finset.prod_congr rfl ?_
  intro p hp
  simp only [Nat.mem_primesBelow] at hp
  congr 1
  have eq := d_factorization_eq_div_log (n + 1) p
  simp only [Nat.cast_add, Nat.cast_one] at eq
  rw [← eq hp.2, d_factorization (s := Finset.Icc 1 (n + 1)) (hs := by exact ⟨1, by simp⟩)
    (p := p) (hs₁ := by simp)]

theorem d_eq_prod_pow (n : ℕ) :
    d (Finset.Icc 1 n) =
    ∏ p ∈ ((n + 1).primesBelow),
      p ^ ⌊(Real.log (n : ℝ)) / (Real.log (p : ℝ))⌋₊ := by
  cases n
  · simp [d_empty]
  · rw [d_eq_prod_pow'']
    simp

theorem d_le_pow_counting (n : ℕ) : d (Finset.Icc 1 n) ≤ n ^ (n.primeCounting) := by
  if h : n = 0 then
    rw [h]; aesop
  else
    have h1 : 1 ≤ n := by omega
    rw [d_eq_prod_pow n]
    calc
    _ ≤ ∏ _ ∈ ((n + 1).primesBelow), n := by
      apply Finset.prod_le_prod
      · intro p _
        simp only [zero_le]
      · intro p hp
        rw [Nat.mem_primesBelow] at hp
        have h2 : 1 ≤ p := by
          by_contra! h
          have : p = 0 := by omega
          aesop
        suffices p ^ (⌊(Real.log (n : ℝ)) / (Real.log (p : ℝ))⌋₊ : ℝ) ≤
            (n : ℝ) by
          norm_cast at this
        trans p ^ ((Real.log (n : ℝ)) / (Real.log (p : ℝ)))
        · apply Real.rpow_le_rpow_of_exponent_le (by norm_cast)
          · apply Nat.floor_le
            if h2 : n = 1 ∨ p = 1 then
              rcases h2 with (rfl | rfl) <;> simp
            else
              rcases (not_or.1 h2) with ⟨_, h2⟩
              have h1 : 1 < n := by omega
              have h2 : 1 < p := by omega
              suffices 0 < Real.log (n : ℝ) / Real.log (p : ℝ) by linarith
              apply div_pos <;>
              exact Real.log_pos (by norm_cast)
        · nth_rewrite 1 [← Real.exp_log (x := (p : ℝ)) (by norm_cast), ← Real.exp_one_rpow,
            ← Real.rpow_mul (by exact Real.exp_nonneg 1), mul_div, mul_comm, ← mul_div]
          if hp : p = 1 then
            rw [hp]; simp only [Nat.cast_one, Real.log_one, div_zero, mul_zero, Real.rpow_zero,
              Nat.one_le_cast, h1]
          else
            rw [div_self, mul_one, Real.exp_one_rpow, Real.exp_log (by norm_cast)]
            rw [Real.log_ne_zero]
            norm_cast
            simp only [not_false_eq_true, and_true]
            omega
    _ ≤ n ^ (n.primeCounting) := by
      rw [Finset.prod_const]
      suffices ((n + 1).primesBelow).card = n.primeCounting by
        apply Nat.pow_le_pow_right <;> linarith
      rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting']

end LeanPool.Zeta3Irrational

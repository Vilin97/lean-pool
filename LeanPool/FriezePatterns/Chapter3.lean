/-
Copyright (c) 2026 Antoine de Saint-Germain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine de Saint-Germain, Akselai, Jon Cheah, Bockman Cheung, Eaton Liu
-/

import LeanPool.FriezePatterns.Chapter1
import LeanPool.FriezePatterns.Chapter2
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

/-!
# LeanPool.FriezePatterns.Chapter3

Imported Lean Pool material for `LeanPool.FriezePatterns.Chapter3`.
-/


/-- An *arithmetic frieze pattern* of height `n`: a rational-valued frieze pattern with all
denominators equal to one and positive interior entries. -/
class arith_fp (f : ℕ × ℕ → ℚ) (n : ℕ) : Prop where
  topBordZeros : ∀ m, f (0, m) = 0
  topBordOnes : ∀ m, f (1, m) = 1
  botBordOnes_n : ∀ m, f (n, m) = 1
  botBordZeros_n : ∀ i, ∀ m, i ≥ n + 1 → (f (i, m) = 0)
  diamond : ∀ i, ∀ m, i ≤ n - 1 → f (i + 1, m) * f (i + 1, m + 1) - 1 = f (i + 2, m) * f (i, m + 1)
  integral : ∀ i, ∀ m, (f (i, m)).den = 1
  positive : ∀ i, ∀ m, 1 ≤ i → i ≤ n → f (i, m) > 0

instance [arith_fp f n] : nzPattern_n ℚ f n := {
  topBordZeros := arith_fp.topBordZeros n,
  topBordOnes := arith_fp.topBordOnes n,
  botBordOnes_n := arith_fp.botBordOnes_n,
  botBordZeros_n := arith_fp.botBordZeros_n,
  diamond := arith_fp.diamond,
  non_zero := fun i m ⟨hi1, hi2⟩ => by linarith [@arith_fp.positive f n _ i m hi1 hi2]
}

-- The definition is only sensible when `n ≥ 2`; otherwise `i % 0 = i` for all `i`.
-- The shifted indexing avoids starting the sequence with `(1, 1, ...)`.
/-- The flute underlying sequence extracted from an arithmetic frieze pattern. -/
def fluteF (f : ℕ × ℕ → ℚ) (n m : ℕ) (i : ℕ) : ℕ :=
  ((f (i % (n - 1) + 1, m)).num).toNat

/-- The flute associated to an arithmetic frieze pattern of height `n ≥ 2`. -/
def friezeToFlute (f : ℕ × ℕ → ℚ) (n m : ℕ) (hn : 2 ≤ n) [arith_fp f n] : flute n := by
  have pos : ∀ i, fluteF f n m i > 0 := by
    intro i
    have zero_lt_n_sub_one : 0 < n - 1 :=
        calc 0 < 1 := by simp
            _≤ 2 - 1 := by simp
            _≤  n - 1 := Nat.sub_le_sub_right hn 1
    unfold fluteF
    simp only [gt_iff_lt, Int.lt_toNat, Nat.cast_zero, Rat.num_pos]
    have a₁ : 1 ≤ i%(n-1) + 1 := by omega
    have a₂ : i%(n-1) + 1 ≤ n :=
        calc i%(n-1) + 1
            ≤ (n - 1) + 1 :=
              Nat.add_le_add_right (Nat.le_of_lt (Nat.mod_lt i zero_lt_n_sub_one)) 1
            _≤ n := by omega
    exact arith_fp.positive (i%(n-1) + 1) m a₁ a₂   --finish if 1 < (n-1) and i%(n-1) ≠ 0
  have hd : fluteF f n m 0 = 1 := by
    unfold fluteF
    simp [arith_fp.topBordOnes n m]
  have period : ∀ i, fluteF f n m i = fluteF f n m (i + (n-1)) := by
    intro i
    unfold fluteF
    simp                  --finish if i%(n-1) ≠ 0
  have div : ∀ i, fluteF f n m (i + 1) ∣ (fluteF f n m (i) + fluteF f n m (i + 2)) := by
    intro i
    unfold fluteF
    by_cases n_eq_two : n=2
    · simp [n_eq_two]
      simp [Nat.mod_one]                             --finish if n=2
    by_cases n_eq_three : n=3
    · by_cases i_even : i%2 = 0
      · have i_plus_one_odd : (i+1)%2 = 1 := by omega
        have i_plus_two_even : (i+2)%2 = 0 := by rw[Nat.add_mod_right i 2, i_even]
        simp only [n_eq_three, Nat.add_one_sub_one, Nat.add_mod_right]
        simp only [i_plus_one_odd, Nat.reduceAdd, i_even, zero_add]
        rw[@pattern_n.topBordOnes ℚ _ f n _ m]
        simp only [Rat.num_ofNat, Int.toNat_one, Nat.reduceAdd]
        have this : f (2, m) * f (2, m + 1) = 2 :=
            calc f (2, m) * f (2, m + 1) = f (2, m) * f (2, m + 1) - 1 + 1 := by simp
                  _= f (3, m)*f (1, m + 1) + 1 := by
                    rw[@pattern_n.diamond ℚ _ f n _ 1 (m) (by omega)]
                  _= f (3, m) * 1 + 1 := by rw[@pattern_n.topBordOnes ℚ _ f n _ (m+1)]
                  _= f (n, m) * 1 + 1 := by rw[n_eq_three]
                  _= 1 * 1 + 1 := by rw[@pattern_n.botBordOnes_n ℚ _ f n _ (m)]
                  _= 2 := by ring
        have this.num : (f (2, m)).num * (f (2, m + 1)).num = 2 := by
          have key : (f (2, m)).num * (f (2, m + 1)).num = (f (2, m) * f (2, m + 1)).num := by
            simp [Rat.mul_num, arith_fp.integral n]
          simp [key, this]
        have this.num.toNat : (f (2, m)).num.toNat * (f (2, m + 1)).num.toNat = 2 := by
          have h₃ : 0 ≤ (f (2,m)).num := by
            linarith [Rat.num_pos.mpr (@arith_fp.positive f n _ 2 m (by omega) (by omega))]
          have h₄ : 0 ≤ (f (2,m+1)).num := by
            linarith [Rat.num_pos.mpr (@arith_fp.positive f n _ 2 (m+1) (by omega) (by omega))]
          zify; rw [Int.toNat_of_nonneg h₃, Int.toNat_of_nonneg h₄, this.num]
        nth_rewrite 2 [← this.num.toNat]
        simp                                              --finish if n=3, i_even
      · have i_plus_one_even : (i+1)%2 = 0 := by omega
        simp only [n_eq_three, Nat.add_one_sub_one, i_plus_one_even, zero_add, Nat.add_mod_right]
        rw[@pattern_n.topBordOnes ℚ _ f n _ m]
        simp                                          --finish if n=3, i_odd
    -- now do 4 ≤ n
    have four_le_n : 4 ≤ n := by omega
    have one_lt_n_sub_one : 1 < n - 1 := by omega
    have two_lt_n_sub_one : 2 < n - 1 := by omega
    by_cases boundary : (i + 1) % (n - 1) = 0
    · -- finish boundary case if (i + 1) % (n - 1) = 0
      simp[boundary, arith_fp.topBordOnes n m]
    by_cases boundary' : (i + 2) % (n - 1) = 0
    · -- this now makes sense as n ≥ 4
      have i_mod_n_sub_one_eq_n_sub_three : (i) % (n - 1) = n - 3 :=
          calc (i) % (n - 1) = (i + (n - 1)) % (n - 1) :=  by simp
              _= (i + (n - 1) + 2 - 2) % (n - 1) := by simp
              _= (i + 2 + (n - 1) - 2) % (n - 1) := by rw[add_right_comm]
              _= (i + 2 + ((n - 1) - 2)) % (n - 1) := by
                  rw[Nat.add_sub_assoc (Nat.le_of_lt two_lt_n_sub_one) (i+2)]
              _= ((i + 2) % (n - 1) + ((n - 1) - 2) % (n - 1)) % (n - 1) := by rw[Nat.add_mod]
              _= (((n - 1) - 2) % (n - 1)) % (n - 1) := by simp [boundary']
              _= ((n - 1) - 2) % (n - 1) := by rw[Nat.mod_mod]
              _= (n - 3) % (n - 1) := by rw[Nat.sub_sub n 1 2]
              _= n - 3 := by rw[Nat.mod_eq_of_lt (by omega)]
      have i_plus_one_mod_n_sub_one_eq_n_sub_two : (i + 1) % (n - 1) = n - 2 := by
          rw[Nat.add_mod]
          rw[i_mod_n_sub_one_eq_n_sub_three, Nat.mod_eq_of_lt (one_lt_n_sub_one)]
          rw[Nat.mod_eq_of_lt (by omega)]
          omega
      simp only [i_plus_one_mod_n_sub_one_eq_n_sub_two, i_mod_n_sub_one_eq_n_sub_three, boundary',
        zero_add]
      have BordOnes : f (1,m) = f (n,m) := by
          rw[@pattern_n.topBordOnes ℚ _ f n _ m]
          rw[@pattern_n.botBordOnes_n ℚ _ f n _ m]
      rw[BordOnes]
      have a₁ : n - 3 + 1 = n - 2 := by omega
      have a₂ : n = n - 2 + 2 := by omega
      rw[a₁]
      nth_rewrite 3 [a₂]
      have continuant3 : (f ((n-2), m)) + (f ((n-2) + 1 + 1, m)) =
          (f (2, m + (n-2))) * (f ((n-2)+ 1,m)) := by
        rw[pattern_nContinuant1 ℚ f n (n-2) (by omega) m]
        simp
      have continuant3.num : (f ((n - 2), m)).num + (f ((n - 2) + 1 + 1, m)).num =
          (f (2, m + ((n - 2)))).num * (f ((n - 2) + 1,m)).num := by
        have key₁ : (f ((n - 2), m)).num + (f ((n - 2) + 1 + 1, m)).num =
            (f ((n - 2), m) + f ((n - 2) + 1 + 1, m)).num := by
          simp only [Rat.add_num_den, arith_fp.integral n ((n - 2)) m, Nat.cast_one, one_mul,
            Rat.divInt_ofNat]
          simp only [arith_fp.integral n ((n - 2) + 1 + 1) m, Nat.cast_one, mul_one]
          rw [Rat.mkRat_one]
          norm_cast
        have key₂ : (f (2, m + ((n - 2)))).num * (f ((n - 2) + 1,m)).num =
            (f (2, m + ((n - 2))) * f ((n - 2) + 1,m)).num := by
          simp [Rat.mul_num, arith_fp.integral n 2 (m + ((n - 2))),
            arith_fp.integral n ((n - 2) + 1) m]
        simp [key₁, key₂, continuant3]
      have continuant3.num.toNat :
          (f ((n - 2), m)).num.toNat + (f ((n - 2) + 1 + 1, m)).num.toNat =
          (f (2, m + ((n - 2)))).num.toNat * (f ((n - 2) + 1,m)).num.toNat := by
        have h₂ : 0 ≤ (f ((n - 2), m)).num := by
          linarith [Rat.num_pos.mpr (@arith_fp.positive f n _ ((n - 2)) m (by omega) (by omega))]
        have h₃ : 0 ≤ (f ((n - 2) + 1 + 1, m)).num := by
          linarith [Rat.num_pos.mpr
            (@arith_fp.positive f n _ ((n - 2) + 1 + 1) m (by omega) (by omega))]
        have h₄ : 0 ≤ (f (2, m + ((n - 2)))).num := by
          linarith [Rat.num_pos.mpr
            (@arith_fp.positive f n _ 2 (m + ((n - 2))) (by omega) (by omega))]
        have h₅ : 0 ≤ (f ((n - 2) + 1,m)).num := by
          linarith [Rat.num_pos.mpr
            (@arith_fp.positive f n _ ((n - 2) + 1) m (by omega) (by omega))]
        zify
        rw [Int.toNat_of_nonneg h₂, Int.toNat_of_nonneg h₃, Int.toNat_of_nonneg h₄,
          Int.toNat_of_nonneg h₅, continuant3.num]
      -- finish boundary' case if (i + 2) % (n - 1) = 0
      simp[continuant3.num.toNat]
    have i_plus_one_mod_n_sub_one_bd_below : 1 ≤ (i + 1) % (n - 1) := by
        rw[Nat.one_le_iff_ne_zero]
        simp[boundary]
    have i_mod_n_sub_one_bd_above : (i) % (n - 1) < (n - 1) := Nat.mod_lt (i) (by omega)
    -- These three feed some linarith's below, don't delete
    have i_plus_one_mod_n_sub_one_bd_above : (i + 1) % (n - 1) < (n - 1) :=
      Nat.mod_lt (i+1) (by omega)
    have i_plus_two_mod_n_sub_one_bd_above : (i + 2) % (n - 1) < (n - 1) :=
      Nat.mod_lt (i+2) (by omega)
    have a₀₁ : (i) % (n - 1) + (1) % (n - 1) < n - 1 := by
        rw[Nat.mod_eq_of_lt (one_lt_n_sub_one)]
        by_contra boundary_neg
        rw [Nat.not_lt] at boundary_neg
        apply boundary
        have this : i % (n - 1) + 1 = n - 1 := by linarith
        rw[Nat.add_mod, Nat.mod_eq_of_lt (one_lt_n_sub_one), this]
        simp
    have a₁ : (i + 1) % (n - 1) = (i) % (n - 1) + 1 := by
        rw[Nat.add_mod_of_add_mod_lt a₀₁]
        simp only [Nat.add_left_cancel_iff]
        rw[Nat.mod_eq_of_lt (by linarith)]
    have a₀₂ : (i) % (n - 1) + (2) % (n - 1) < n - 1 := by
        rw[Nat.mod_eq_of_lt (two_lt_n_sub_one)]
        by_contra boundary_neg
        rw [Nat.not_lt] at boundary_neg
        apply boundary'
        have this : n - 1 = i % (n - 1) + 2 := by omega
        rw[Nat.add_mod]
        rw[Nat.mod_eq_of_lt (two_lt_n_sub_one)]
        rw[← this]
        simp
    have a₂ : (i + 2) % (n - 1) = (i) % (n - 1) + 2 := by
        rw[Nat.add_mod_of_add_mod_lt (a₀₂)]
        simp only [Nat.add_left_cancel_iff]
        rw[Nat.mod_eq_of_lt (by omega)]
    rw[a₁,a₂, add_right_comm]
    have h₁ : i % (n - 1) + 1 ≤ n - 1 :=
        calc  i % (n - 1) + 1 ≤ (i) % (n - 1) + (1) % (n - 1) := by
                rw[Nat.mod_eq_of_lt (one_lt_n_sub_one)]
              _≤ n - 1 := Nat.le_of_lt (a₀₁)
    have continuant : (f (i % (n - 1) + 1, m)) + (f (i % (n - 1) + 1 + 1 + 1, m)) =
        (f (2, m + (i % (n - 1) + 1))) * (f (i % (n - 1) + 1 + 1,m)) := by
      rw[pattern_nContinuant1 ℚ f n (i % (n - 1) + 1) h₁ m]
      simp
    have continuant.num : (f (i % (n - 1) + 1, m)).num + (f (i % (n - 1) + 1 + 1 + 1, m)).num =
        (f (2, m + (i % (n - 1) + 1))).num * (f (i % (n - 1) + 1 + 1,m)).num := by
      have key₁ : (f (i % (n - 1) + 1, m)).num + (f (i % (n - 1) + 1 + 1 + 1, m)).num =
          (f (i % (n - 1) + 1, m) + f (i % (n - 1) + 1 + 1 + 1, m)).num := by
        simp only [Rat.add_num_den, arith_fp.integral n (i % (n - 1) + 1) m, Nat.cast_one, one_mul,
          Rat.divInt_ofNat]
        simp only [arith_fp.integral n (i % (n - 1) + 1 + 1 + 1) m, Nat.cast_one, mul_one]
        rw [Rat.mkRat_one]
        norm_cast
      have key₂ : (f (2, m + (i % (n - 1) + 1))).num * (f (i % (n - 1) + 1 + 1,m)).num =
          (f (2, m + (i % (n - 1) + 1)) * f (i % (n - 1) + 1 + 1,m)).num := by
        simp [Rat.mul_num, arith_fp.integral n 2 (m + (i % (n - 1) + 1)),
          arith_fp.integral n (i % (n - 1) + 1 + 1) m]
      simp [key₁, key₂, continuant]
    have continuant.num.toNat :
        (f (i % (n - 1) + 1, m)).num.toNat + (f (i % (n - 1) + 1 + 1 + 1, m)).num.toNat =
        (f (2, m + (i % (n - 1) + 1))).num.toNat * (f (i % (n - 1) + 1 + 1,m)).num.toNat := by
      have h₂ : 0 ≤ (f (i % (n - 1) + 1, m)).num := by
        linarith [Rat.num_pos.mpr
          (@arith_fp.positive f n _ (i % (n - 1) + 1) m (by omega) (by omega))]
      have h₃ : 0 ≤ (f (i % (n - 1) + 1 + 1 + 1, m)).num := by
        linarith [Rat.num_pos.mpr
          (@arith_fp.positive f n _ (i % (n - 1) + 1 + 1 + 1) m (by omega) (by omega))]
      have h₄ : 0 ≤ (f (2, m + (i % (n - 1) + 1))).num := by
        linarith [Rat.num_pos.mpr
          (@arith_fp.positive f n _ 2 (m + (i % (n - 1) + 1)) (by omega) (by omega))]
      have h₅ : 0 ≤ (f (i % (n - 1) + 1 + 1,m)).num := by
        linarith [Rat.num_pos.mpr
          (@arith_fp.positive f n _ (i % (n - 1) + 1 + 1) m (by omega) (by omega))]
      zify
      rw [Int.toNat_of_nonneg h₂, Int.toNat_of_nonneg h₃, Int.toNat_of_nonneg h₄,
        Int.toNat_of_nonneg h₅, continuant.num]
    simp[continuant.num.toNat]
  exact ⟨fluteF f n m, pos, hd, period, div⟩




/-- The arithmetic frieze pattern associated to a flute, defined recursively over the second
coordinate `m` (and as a tie-breaker the first coordinate `i`). -/
def friezeF {n : ℕ} (g : flute n) : ℕ × ℕ → ℚ :=
  fun ⟨i, m⟩ =>
    if i = 0 then 0
    else if i ≥ n + 1 then 0
    else if m = 0 then g.a (i - 1)
    else (friezeF g (i + 1, m - 1) * friezeF g (i - 1, m) + 1) / friezeF g (i, m - 1)
    termination_by x => (x.2, x.1)

/-- The frieze pattern built from a flute is in fact an arithmetic frieze pattern. -/
lemma fluteToFrieze {n : ℕ} (g : flute n) (hn : n ≠ 0) : arith_fp (friezeF g) n := by
  have topBordZeros : ∀ m, friezeF g (0,m) = 0 := fun m => (by simp [friezeF])
  have botBordZeros_n : ∀ i, ∀ m,  i ≥ n+1 → (friezeF g (i,m) = 0) :=
    fun i m h => by simp [friezeF, h]
  have topBordOnes : ∀ m, friezeF g (1,m) = 1 := by
    intro m
    induction m with
    | zero => simp [friezeF, hn, g.hd]
    | succ m ih =>
      have : ¬ 1 ≥ n+1 := by omega
      unfold friezeF; simp only [one_ne_zero, ↓reduceIte, ge_iff_le, this, Nat.add_eq_zero_iff,
        and_false, Nat.reduceAdd, add_tsub_cancel_right, tsub_self, ih, div_one, add_eq_right,
        mul_eq_zero]
      right
      exact topBordZeros (m+1)
  have botBordOnes_n : ∀ m, friezeF g (n, m) = 1 := by
    intro m
    induction m with
    | zero =>
      simp only [friezeF, hn, ↓reduceIte, ge_iff_le, add_le_iff_nonpos_right, nonpos_iff_eq_zero,
        one_ne_zero, Rat.natCast_eq_one_iff]
      have := g.period 0
      simp [g.hd] at this
      exact this.symm
    | succ m ih =>
      have : ¬ n ≥ n+1 := by omega
      unfold friezeF; simp only [hn, ↓reduceIte, ge_iff_le, this, Nat.add_eq_zero_iff,
        one_ne_zero, and_false, add_tsub_cancel_right, ih, div_one, add_eq_right, mul_eq_zero]
      left
      exact botBordZeros_n (n+1) m (by rfl)
  have positive: ∀ i, ∀ m, 1 ≤ i → i ≤ n → friezeF g (i,m) > 0 := by
    intro i m
    induction m generalizing i with
    | zero =>
      intro hi₁ hi₂
      have hi₃ : ¬ i = 0 := by omega
      have hi₄ : ¬ i ≥ n+1 := by omega
      unfold friezeF; simp only [hi₃, ↓reduceIte, ge_iff_le, hi₄, gt_iff_lt, Nat.cast_pos]
      exact g.pos (i-1)
    | succ m ih₁ =>
      induction i with
      | zero => omega
      | succ i ih₂ =>
        intro hi₁ hi₂
        by_cases hi : i = 0
        · simp [hi, topBordOnes]
        · by_cases hi' : i = n-1
          · have : n-1+1 = n := by omega
            simp [this, hi', botBordOnes_n]
          · specialize ih₂ (by omega) (by omega)
            have : ¬ n ≤ i := by omega
            unfold friezeF
            simp +arith only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, ge_iff_le,
              add_le_add_iff_right, this, add_tsub_cancel_right, gt_iff_lt]
            have h₁ := ih₁ (i+1) (by omega) (by omega)
            have h₂ := ih₁ (i+2) (by omega) (by omega)
            exact div_pos (by linarith [mul_pos h₂ ih₂]) h₁
  have diamond : ∀ i, ∀ m,  i ≤ n-1 → friezeF g (i+1,m) * friezeF g (i+1,m+1)-1 =
      friezeF g (i+2,m) * friezeF g (i,m+1) := by
    intro i m hi
    conv =>
      enter [1,1,2]
      unfold friezeF
    have : ¬ n ≤ i := by omega
    simp +arith [this]
    have hpos : friezeF g (i+1, m) > 0 := by linarith [positive (i+1) m (by omega) (by omega)]
    field_simp
    ring
  have non_zero : ∀ i m, 1 ≤ i ∧ i ≤ n → friezeF g (i,m) ≠ 0 :=
    fun i m ⟨hi₁, hi₂⟩ => by linarith [positive i m hi₁ hi₂]
  have : nzPattern_n ℚ (friezeF g) n := by
    exact {topBordZeros, topBordOnes, botBordOnes_n, botBordZeros_n, diamond, non_zero}
  have integral: ∀ i, ∀ m, (friezeF g (i,m)).den = 1 := by
    have key : ∀ m, (friezeF g (2, m)).den = 1 := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
      by_cases hm : m = 0
      · simp [hm, friezeF]
        norm_cast
      by_cases hm₂ : m ≤ n-2
      · have key := pattern_nContinuant1 ℚ (friezeF g) n m (by omega) 0
        have div : ∃ k : ℕ, (friezeF g (m,0) + friezeF g (m+2,0)) = friezeF g (m+1,0)*k := by
          have hm₃ : ¬ n ≤ m := by omega
          have hm₄ : ¬ n ≤ m+1 := by omega
          have hm₅ : ¬ n+1 ≤ m := by omega
          unfold friezeF; simp only [hm, ↓reduceIte, ge_iff_le, hm₅, Nat.add_eq_zero_iff,
            OfNat.ofNat_ne_zero, and_self, add_le_add_iff_right, hm₄, Nat.add_one_sub_one,
            one_ne_zero, hm₃, add_tsub_cancel_right]
          norm_cast
          have := g.div (m-1)
          have hm₆ : m-1+1 = m := by omega
          have hm₇ : m-1+2 = m+1 := by omega
          simp only [hm₆, hm₇] at this
          exact this
        rcases div with ⟨k, hk⟩
        simp only [zero_add] at key
        have hne : friezeF g (m+1, 0) ≠ 0 := by
          linarith [positive (m+1) 0 (by omega) (by omega)]
        have hfrac : friezeF g (2,m) = k := by
          have hkey : friezeF g (2, m) * friezeF g (m + 1, 0) =
              friezeF g (m, 0) + friezeF g (m + 2, 0) := by
            linarith [key]
          have : friezeF g (2, m) * friezeF g (m + 1, 0) = ↑k * friezeF g (m + 1, 0) := by
            rw [hkey, hk]; ring
          exact mul_right_cancel₀ hne this
        rw [hfrac]
        norm_cast
      have : n+1-(n-1)=2 := by omega
      by_cases hm₃ : m = n-1
      · have key := glideSymm ℚ (friezeF g) n (n-1) (by omega) 0
        simp [this] at key
        simp [hm₃, key, friezeF]
        norm_cast
      by_cases hm₄ : m = n
      · have key := glideSymm ℚ (friezeF g) n (n-1) (by omega) 1
        have hm₅ : 1+(n-1)=n := by omega
        simp only [this, hm₅] at key
        rw [hm₄, key]; rw [hm₄] at ih
        suffices h_den : ∀ i ≤ n-1, (friezeF g (i,1)).den = 1 by
          exact h_den (n-1) (by omega)
        intro i hi
        induction i using Nat.twoStepInduction with
        | zero => simp [friezeF]
        | one => simp [friezeF, hn, g.hd]
        | more i ih₁ ih₂ =>
          specialize ih₁ (by omega)
          specialize ih₂ (by omega)
          have := pattern_nContinuant1 ℚ (friezeF g) n i (by omega) 1
          rw [this]
          have := ih (1+i) (by omega)
          -- there should be a tactic to do the following two steps?
          rw [Rat.sub_eq_add_neg, Rat.add_num_den, Rat.neg_den, Rat.mul_den, ih₁, ih₂, this]
          simp
      have h := translationInvariance ℚ (friezeF g) n 2 (by omega) (m-(n+1))
      have : m-(n+1)+n+1 = m := by omega
      rw [this] at h
      exact h ▸ ih (m-(n+1)) (by omega)
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
    match i with
    | 0 => intro; simp [topBordZeros]
    | 1 => intro; simp [topBordOnes]
    | 2 => exact key
    | i+3 =>
      by_cases hi : i+2 ≥ n
      · intro; simp [botBordZeros_n (i+3) _ (by omega)]
      intro m
      have key₂ := pattern_nContinuant1 ℚ (friezeF g) n (i+1) (by omega) m
      simp +arith only at key₂
      rw [key₂]
      have h₁ : (friezeF g (2, i+m+1)).den = 1 := by
        have := key (m+(i+1))
        convert this using 2; ring_nf
      have h₂ := ih (i+1) (by omega) m
      have h₃ := ih (i+2) (by omega) m
      rw [Rat.sub_eq_add_neg, Rat.add_num_den, Rat.neg_den, Rat.mul_den, h₁, h₂, h₃]
      simp
  exact {topBordZeros, topBordOnes, botBordOnes_n, botBordZeros_n, diamond, integral, positive}

/-- The set of arithmetic frieze patterns of height `n`. -/
def arithFriezePatSet (n : ℕ) : Set (ℕ × ℕ → ℚ) :=
  { f | arith_fp f n}


-- Now we can use the nonemptyness of Flute n to prove the nonemptyness of arithFriezePatSet n.
lemma arithFriezePatSetNonEmpty {n : ℕ} (h : n ≠ 0) : (arithFriezePatSet n).Nonempty  := by
  rcases csteFlute n with ⟨a⟩
  exact ⟨friezeF a, fluteToFrieze a h⟩



lemma main1 (n : ℕ) (h : n ≠ 0) : ∀ (f : ℕ × ℕ → ℚ) (_ : arith_fp f n), ∀ (a : ℕ × ℕ),
    f a ≤ Nat.fib n := by
  intro f hf ⟨i, m⟩
  by_cases hn : n = 1
  · simp only [hn, Nat.fib_one]
    match i with
    | 0 => simp [hf.topBordZeros m]
    | 1 => simp [hf.topBordOnes m]
    | i + 2 => simp [hf.botBordZeros_n (i + 2) m (by omega)]
  have hn' : n > 1 := by omega
  let g := @friezeToFlute f n m (by omega) hf
  by_cases hi₀ : i = 0
  · simp [hi₀, hf.topBordZeros m]
  by_cases hi₁ : i = 1
  · simp only [hi₁, hf.topBordOnes m]
    have hn'' : n > 0 := by omega
    have : Nat.fib n > 0 := Nat.fib_pos.mpr hn''
    exact_mod_cast this
  by_cases hi₂ : i ≥ n + 1
  · simp [hf.botBordZeros_n i m hi₂]
  by_cases hi₃ : i = n
  · simp only [hi₃, hf.botBordOnes_n m]
    have hi₄ : 0 < Nat.fib n := Nat.fib_pos.mpr (by omega)
    exact_mod_cast hi₄
  have key := FluteBounded n (by omega) g (i - 1) (by omega)
  have hg : g = @friezeToFlute f n m (by omega) hf := rfl
  rw [hg] at key; unfold friezeToFlute at key; dsimp only at key; unfold fluteF at key
  simp only [Int.toNat_le] at key
  have hi₆ : (i - 1) % (n - 1) + 1 = i := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [hi₆] at key
  have hd : (f (i, m)).den = 1 := hf.integral i m
  rw [show (f (i, m) : ℚ) = ((f (i, m)).num : ℚ) by
    rw [← Rat.num_div_den (f (i, m)), hd]; simp]
  exact_mod_cast key

lemma main2 (n : ℕ) (hn : n ≠ 0) :
    ∃ (f : ℕ × ℕ → ℚ) (_ : arith_fp f n), ∃ (a : ℕ × ℕ), f a = Nat.fib n := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  -- even case
  · have : k > 0 := by
      by_contra!
      simp only [nonpos_iff_eq_zero] at this; rw [this] at hk; simp at hk; omega
    have : k ≠ 0 := by omega
    let j := k-1
    have hj : n = 2*j+2 := by omega
    use friezeF (fibFluteEven j)
    let temp := fluteToFrieze (fibFluteEven j) (by omega)
    conv at temp =>
      rhs
      rw [←hj]
    use temp
    have h₁ : ∃ (w : ℕ × ℕ), friezeF (fibFluteEven j) w = Nat.fib (2 * j + 2) := by
      use (j + 1, 0)
      have h₃ : ¬ 2 * j + 2 ≤ j := by omega
      simp only [friezeF, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, ge_iff_le,
        add_le_add_iff_right, h₃, add_tsub_cancel_right, Nat.cast_inj]
      unfold fibFluteEven
      by_cases h₂ : j = 0
      · simp only [h₂, mul_zero, zero_add, Nat.fib_two]
        unfold aEven
        simp
      -- j ≠ 0
      simp only
      have h₄ : ¬ j ≥ 2 * j + 1 := by omega
      unfold aEven
      simp [h₄]
    choose w hw using h₁
    use w
    rw [hj]
    assumption
  -- odd case
  · use friezeF (fibFluteOdd k)
    let temp := fluteToFrieze (fibFluteOdd k) (by omega)
    conv at temp =>
      rhs
      rw [← hk]
    use temp
    have h₁ : ∃ (w : ℕ × ℕ), friezeF (fibFluteOdd k) w = Nat.fib (2 * k + 1) := by
      use (k + 1, 0)
      have h₃ : ¬ 2 * k + 1 ≤ k := by omega
      simp only [friezeF, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, ge_iff_le,
        add_le_add_iff_right, h₃, add_tsub_cancel_right, Nat.cast_inj]
      unfold fibFluteOdd
      by_cases h₂ : k = 0
      · simp only [h₂, ↓reduceDIte, Pi.natCast_apply, Nat.cast_id, mul_zero, zero_add, Nat.fib_one]
        unfold aOdd
        simp
      -- k ≠ 0
      simp only [h₂, ↓reduceDIte]
      have h₄ : ¬ 2 * k ≤ k := by omega
      have h₅ : 1 + 4 * k - 2 * k = 2 * k + 1 := by omega
      unfold aOdd
      simp [h₂, h₄, h₅]
    choose w hw using h₁
    use w
    rw [hk]
    assumption

theorem main3 (n : ℕ) (hn : n ≠ 0) : ∃ (g : ℕ × ℕ → ℚ) (_ : arith_fp g n),
    ∃ (b : ℕ × ℕ), (∀ (f : ℕ × ℕ → ℚ) (_ : arith_fp f n), ∀ (a : ℕ × ℕ),
      (f a ≥ g b → f a = g b)) ∧ g b = Nat.fib n := by
  have h : ∃ (g : ℕ × ℕ → ℚ) (_ : arith_fp g n), ∃ (b : ℕ × ℕ), g b = Nat.fib n := main2 n hn
  choose g hg b hb using h
  use g; use hg; use b
  constructor
  · intro f hf ⟨i,m⟩
    have h : f (i,m) ≤ g b := by
      calc f (i,m) ≤ Nat.fib n := main1 n hn f hf (i,m)
      _ = g b := by rw [hb]
    intro h'
    linarith
  · exact hb

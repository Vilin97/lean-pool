/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.GKPCarry.ModularPrefix

/-!
# Kernel-checked bounded C3 certificate

The Boolean certificates cover `27 ≤ m ≤ 6560` over the five ranges on which
the ternary length is constant. Within each range, modular residues are advanced
by multiplication by four, so only the first power is computed from scratch.
Their soundness is transported through proved modular exponentiation and ternary
prefix lemmas, yielding the headline carry theorem at the end of this file.
-/

namespace GKPCarry

private lemma powMod_succ (base exponent modulus : ℕ) :
    powMod base (exponent + 1) modulus =
      base * powMod base exponent modulus % modulus := by
  rw [powMod_eq_pow_mod, powMod_eq_pow_mod, pow_succ,
    Nat.mul_comm (base ^ exponent) base, Nat.mul_mod_mod]

private lemma powMod_add (base left right modulus : ℕ) :
    powMod base (left + right) modulus =
      powMod base left modulus * powMod base right modulus % modulus := by
  rw [powMod_eq_pow_mod, powMod_eq_pow_mod, powMod_eq_pow_mod, pow_add,
    Nat.mod_mul_mod, Nat.mul_mod_mod]

/-- Advance a residue by `count` multiplications by four. -/
private def finiteAdvance (modulus residue : ℕ) : ℕ → ℕ
  | 0 => residue
  | count + 1 =>
      finiteAdvance modulus (4 * residue % modulus) count

/-- Check `count` consecutive residues. -/
private def finiteCheckBlock (modulus residue : ℕ) : ℕ → Bool
  | 0 => true
  | count + 1 =>
      decide (2 ≤ (Nat.digits 3 residue).count 2) &&
        finiteCheckBlock modulus (4 * residue % modulus) count

/-- Compute the residue after `blocks` blocks without a deep recursive term. -/
private def finiteAdvanceBlocks (modulus residue blocks : ℕ) : ℕ :=
  powMod 4 (64 * blocks) modulus * residue % modulus

/-- Run `blocks` blocks of 64 consecutive residues. -/
private def finiteCheckBlocks (modulus residue : ℕ) : ℕ → Bool
  | 0 => true
  | blocks + 1 =>
      finiteCheckBlock modulus residue 64 &&
        finiteCheckBlocks modulus (finiteAdvance modulus residue 64) blocks

private def finiteCheck (lower count digitLength : ℕ) : Bool :=
  let modulus := 3 ^ (6 * digitLength)
  let blocks := finiteCheckBlocks modulus (powMod 4 lower modulus) (count / 64)
  let residue := finiteAdvanceBlocks modulus (powMod 4 lower modulus) (count / 64)
  blocks && finiteCheckBlock modulus residue (count % 64)

private lemma finiteAdvance_sound
    {modulus residue lower count : ℕ}
    (hresidue : residue = powMod 4 lower modulus) :
    finiteAdvance modulus residue count = powMod 4 (lower + count) modulus := by
  induction count generalizing lower residue with
  | zero => simpa [finiteAdvance] using hresidue
  | succ count ih =>
      have hnext : 4 * residue % modulus = powMod 4 (lower + 1) modulus := by
        rw [hresidue, powMod_succ]
      rw [finiteAdvance]
      simpa [Nat.add_assoc, Nat.add_comm 1 count] using ih hnext

private lemma finiteCheckBlock_sound
    {modulus residue lower count : ℕ}
    (hresidue : residue = powMod 4 lower modulus)
    (hcheck : finiteCheckBlock modulus residue count = true) :
    ∀ {m : ℕ}, lower ≤ m → m < lower + count →
      2 ≤ (Nat.digits 3 (powMod 4 m modulus)).count 2 := by
  induction count generalizing lower residue with
  | zero => omega
  | succ count ih =>
      change (decide (2 ≤ (Nat.digits 3 residue).count 2) &&
        finiteCheckBlock modulus (4 * residue % modulus) count) = true at hcheck
      rw [Bool.and_eq_true] at hcheck
      have hnext : 4 * residue % modulus = powMod 4 (lower + 1) modulus := by
        rw [hresidue, powMod_succ]
      intro m hlower hupper
      by_cases hm : m = lower
      · subst m
        simpa [hresidue] using
          (show 2 ≤ (Nat.digits 3 residue).count 2 by
            simpa only [decide_eq_true_eq] using hcheck.1)
      · exact ih hnext hcheck.2 (by omega) (by omega)

private lemma finiteAdvanceBlocks_sound
    {modulus residue lower blocks : ℕ}
    (hresidue : residue = powMod 4 lower modulus) :
    finiteAdvanceBlocks modulus residue blocks =
      powMod 4 (lower + 64 * blocks) modulus := by
  rw [finiteAdvanceBlocks, hresidue, ← powMod_add]
  rw [Nat.add_comm (64 * blocks) lower]

private lemma finiteCheckBlocks_sound
    {modulus residue lower blocks : ℕ}
    (hresidue : residue = powMod 4 lower modulus)
    (hcheck : finiteCheckBlocks modulus residue blocks = true) :
    ∀ {m : ℕ}, lower ≤ m → m < lower + 64 * blocks →
      2 ≤ (Nat.digits 3 (powMod 4 m modulus)).count 2 := by
  induction blocks generalizing lower residue with
  | zero => omega
  | succ blocks ih =>
      change (finiteCheckBlock modulus residue 64 &&
        finiteCheckBlocks modulus (finiteAdvance modulus residue 64) blocks) = true at hcheck
      rw [Bool.and_eq_true] at hcheck
      have hnext : finiteAdvance modulus residue 64 =
          powMod 4 (lower + 64) modulus := by
        exact finiteAdvance_sound hresidue
      intro m hlower hupper
      by_cases hfirst : m < lower + 64
      · exact finiteCheckBlock_sound hresidue hcheck.1 hlower hfirst
      · exact ih hnext hcheck.2 (by omega) (by omega)

private lemma finiteCheck_sound
    {lower count digitLength m : ℕ}
    (hcheck : finiteCheck lower count digitLength = true)
    (hlower : lower ≤ m) (hupper : m < lower + count) :
    2 ≤ (Nat.digits 3
      (powMod 4 m (3 ^ (6 * digitLength)))).count 2 := by
  let modulus := 3 ^ (6 * digitLength)
  let initial := powMod 4 lower modulus
  let blocks := finiteCheckBlocks modulus initial (count / 64)
  let residue := finiteAdvanceBlocks modulus initial (count / 64)
  change (blocks && finiteCheckBlock modulus residue (count % 64)) = true at hcheck
  rw [Bool.and_eq_true] at hcheck
  have hinitial : initial = powMod 4 lower modulus := rfl
  have hresidue : residue = powMod 4 (lower + 64 * (count / 64)) modulus :=
    finiteAdvanceBlocks_sound hinitial
  have hcount := Nat.mod_add_div count 64
  by_cases hfull : m < lower + 64 * (count / 64)
  · exact finiteCheckBlocks_sound hinitial hcheck.1 hlower hfull
  · exact finiteCheckBlock_sound hresidue hcheck.2 (by omega) (by omega)

private lemma ternaryLength_eq_of_pow_bounds
    {m digitLength : ℕ} (hpositive : 0 < digitLength)
    (hlower : 3 ^ (digitLength - 1) ≤ m) (hupper : m < 3 ^ digitLength) :
    ternaryLength m = digitLength := by
  unfold ternaryLength
  apply Nat.le_antisymm
  · exact (Nat.digits_length_le_iff (b := 3) (by decide) m).mpr hupper
  · have hlt := (Nat.lt_digits_length_iff (b := 3) (k := digitLength - 1)
        (by decide) m).mpr hlower
    omega

private theorem finiteCheck_length_four : finiteCheck 27 54 4 = true := by decide
private theorem finiteCheck_length_five : finiteCheck 81 162 5 = true := by decide
private theorem finiteCheck_length_six_a : finiteCheck 243 256 6 = true := by decide
private theorem finiteCheck_length_six_b : finiteCheck 499 230 6 = true := by decide
private theorem finiteCheck_length_seven_a : finiteCheck 729 256 7 = true := by decide
private theorem finiteCheck_length_seven_b : finiteCheck 985 256 7 = true := by decide
private theorem finiteCheck_length_seven_c : finiteCheck 1241 256 7 = true := by decide
private theorem finiteCheck_length_seven_d : finiteCheck 1497 256 7 = true := by decide
private theorem finiteCheck_length_seven_e : finiteCheck 1753 256 7 = true := by decide
private theorem finiteCheck_length_seven_f : finiteCheck 2009 178 7 = true := by decide
private theorem finiteCheck_length_eight_a : finiteCheck 2187 256 8 = true := by decide
private theorem finiteCheck_length_eight_b : finiteCheck 2443 256 8 = true := by decide
private theorem finiteCheck_length_eight_c : finiteCheck 2699 256 8 = true := by decide
private theorem finiteCheck_length_eight_d : finiteCheck 2955 256 8 = true := by decide
private theorem finiteCheck_length_eight_e : finiteCheck 3211 256 8 = true := by decide
private theorem finiteCheck_length_eight_f : finiteCheck 3467 256 8 = true := by decide
private theorem finiteCheck_length_eight_g : finiteCheck 3723 256 8 = true := by decide
private theorem finiteCheck_length_eight_h : finiteCheck 3979 256 8 = true := by decide
private theorem finiteCheck_length_eight_i : finiteCheck 4235 256 8 = true := by decide
private theorem finiteCheck_length_eight_j : finiteCheck 4491 256 8 = true := by decide
private theorem finiteCheck_length_eight_k : finiteCheck 4747 256 8 = true := by decide
private theorem finiteCheck_length_eight_l : finiteCheck 5003 256 8 = true := by decide
private theorem finiteCheck_length_eight_m : finiteCheck 5259 256 8 = true := by decide
private theorem finiteCheck_length_eight_n : finiteCheck 5515 256 8 = true := by decide
private theorem finiteCheck_length_eight_o : finiteCheck 5771 256 8 = true := by decide
private theorem finiteCheck_length_eight_p : finiteCheck 6027 256 8 = true := by decide
private theorem finiteCheck_length_eight_q : finiteCheck 6283 256 8 = true := by decide
private theorem finiteCheck_length_eight_r : finiteCheck 6539 22 8 = true := by decide

private theorem finiteModularCertificate_length_six
    {m : ℕ} (hlower : 243 ≤ m) (hupper : m ≤ 728) :
    2 ≤ (Nat.digits 3 (powMod 4 m (3 ^ (6 * 6)))).count 2 := by
  by_cases h498 : m ≤ 498
  · exact finiteCheck_sound finiteCheck_length_six_a hlower (by omega)
  · exact finiteCheck_sound finiteCheck_length_six_b (by omega) (by omega)

private theorem finiteModularCertificate_length_seven
    {m : ℕ} (hlower : 729 ≤ m) (hupper : m ≤ 2186) :
    2 ≤ (Nat.digits 3 (powMod 4 m (3 ^ (6 * 7)))).count 2 := by
  by_cases h984 : m ≤ 984
  · exact finiteCheck_sound finiteCheck_length_seven_a hlower (by omega)
  by_cases h1240 : m ≤ 1240
  · exact finiteCheck_sound finiteCheck_length_seven_b (by omega) (by omega)
  by_cases h1496 : m ≤ 1496
  · exact finiteCheck_sound finiteCheck_length_seven_c (by omega) (by omega)
  by_cases h1752 : m ≤ 1752
  · exact finiteCheck_sound finiteCheck_length_seven_d (by omega) (by omega)
  by_cases h2008 : m ≤ 2008
  · exact finiteCheck_sound finiteCheck_length_seven_e (by omega) (by omega)
  · exact finiteCheck_sound finiteCheck_length_seven_f (by omega) (by omega)

private theorem finiteModularCertificate_length_eight
    {m : ℕ} (hlower : 2187 ≤ m) (hupper : m ≤ 6560) :
    2 ≤ (Nat.digits 3 (powMod 4 m (3 ^ (6 * 8)))).count 2 := by
  by_cases h2442 : m ≤ 2442
  · exact finiteCheck_sound finiteCheck_length_eight_a hlower (by omega)
  by_cases h2698 : m ≤ 2698
  · exact finiteCheck_sound finiteCheck_length_eight_b (by omega) (by omega)
  by_cases h2954 : m ≤ 2954
  · exact finiteCheck_sound finiteCheck_length_eight_c (by omega) (by omega)
  by_cases h3210 : m ≤ 3210
  · exact finiteCheck_sound finiteCheck_length_eight_d (by omega) (by omega)
  by_cases h3466 : m ≤ 3466
  · exact finiteCheck_sound finiteCheck_length_eight_e (by omega) (by omega)
  by_cases h3722 : m ≤ 3722
  · exact finiteCheck_sound finiteCheck_length_eight_f (by omega) (by omega)
  by_cases h3978 : m ≤ 3978
  · exact finiteCheck_sound finiteCheck_length_eight_g (by omega) (by omega)
  by_cases h4234 : m ≤ 4234
  · exact finiteCheck_sound finiteCheck_length_eight_h (by omega) (by omega)
  by_cases h4490 : m ≤ 4490
  · exact finiteCheck_sound finiteCheck_length_eight_i (by omega) (by omega)
  by_cases h4746 : m ≤ 4746
  · exact finiteCheck_sound finiteCheck_length_eight_j (by omega) (by omega)
  by_cases h5002 : m ≤ 5002
  · exact finiteCheck_sound finiteCheck_length_eight_k (by omega) (by omega)
  by_cases h5258 : m ≤ 5258
  · exact finiteCheck_sound finiteCheck_length_eight_l (by omega) (by omega)
  by_cases h5514 : m ≤ 5514
  · exact finiteCheck_sound finiteCheck_length_eight_m (by omega) (by omega)
  by_cases h5770 : m ≤ 5770
  · exact finiteCheck_sound finiteCheck_length_eight_n (by omega) (by omega)
  by_cases h6026 : m ≤ 6026
  · exact finiteCheck_sound finiteCheck_length_eight_o (by omega) (by omega)
  by_cases h6282 : m ≤ 6282
  · exact finiteCheck_sound finiteCheck_length_eight_p (by omega) (by omega)
  by_cases h6538 : m ≤ 6538
  · exact finiteCheck_sound finiteCheck_length_eight_q (by omega) (by omega)
  · exact finiteCheck_sound finiteCheck_length_eight_r (by omega) (by omega)

private theorem finiteModularCertificate
    {m : ℕ} (hlower : 27 ≤ m) (hupper : m ≤ 6560) :
    2 ≤ (Nat.digits 3
      (powMod 4 m (3 ^ (6 * ternaryLength m)))).count 2 := by
  by_cases h80 : m ≤ 80
  · have hlength : ternaryLength m = 4 := by
      apply ternaryLength_eq_of_pow_bounds (by norm_num) <;> norm_num <;> omega
    simpa [hlength] using
      finiteCheck_sound (m := m) finiteCheck_length_four hlower (by omega)
  by_cases h242 : m ≤ 242
  · have hlength : ternaryLength m = 5 := by
      apply ternaryLength_eq_of_pow_bounds (by norm_num) <;> norm_num <;> omega
    simpa [hlength] using
      finiteCheck_sound (m := m) finiteCheck_length_five (by omega) (by omega)
  by_cases h728 : m ≤ 728
  · have hlength : ternaryLength m = 6 := by
      apply ternaryLength_eq_of_pow_bounds (by norm_num) <;> norm_num <;> omega
    simpa [hlength] using
      finiteModularCertificate_length_six (m := m) (by omega) h728
  by_cases h2186 : m ≤ 2186
  · have hlength : ternaryLength m = 7 := by
      apply ternaryLength_eq_of_pow_bounds (by norm_num) <;> norm_num <;> omega
    simpa [hlength] using
      finiteModularCertificate_length_seven (m := m) (by omega) h2186
  · have hlength : ternaryLength m = 8 := by
      apply ternaryLength_eq_of_pow_bounds (by norm_num) <;> norm_num <;> omega
    simpa [hlength] using
      finiteModularCertificate_length_eight (m := m) (by omega) hupper

/-- For every `m` in the closed interval from `27` through `6560`, the first
`6 * ternaryLength m` little-endian ternary digits of `4 ^ m` contain at least
two digits equal to `2`. -/
theorem four_pow_has_two_ternary_twos_in_finite_range
    {m : ℕ} (hlower : 27 ≤ m) (hupper : m ≤ 6560) :
    hasTwoTernaryTwosBelow (6 * ternaryLength m) (4 ^ m) := by
  rw [hasTwoTernaryTwosBelow_iff_mod, ← powMod_eq_pow_mod]
  exact finiteModularCertificate hlower hupper

/-- Equivalent length-indexed form of the bounded ternary-prefix theorem. -/
theorem four_pow_has_two_ternary_twos_of_length_le_eight
    {m : ℕ} (hlower : 27 ≤ m) (hlength : ternaryLength m ≤ 8) :
    hasTwoTernaryTwosBelow (6 * ternaryLength m) (4 ^ m) := by
  have hupper : m < 3 ^ 8 :=
    (Nat.digits_length_le_iff (b := 3) (by decide) m).mp hlength
  norm_num at hupper
  exact four_pow_has_two_ternary_twos_in_finite_range hlower (by omega)

/-- Bounded C3 carry result: throughout `27 ≤ m ≤ 6560`, doubling
the selected prefix of the ternary expansion of `4 ^ m` produces at least two
outgoing carries. -/
theorem four_pow_prefix_carry_count_ge_two_in_finite_range
    {m : ℕ} (hlower : 27 ≤ m) (hupper : m ≤ 6560) :
    2 ≤ prefixTernaryDoubleCarryCount
      (6 * ternaryLength m) (4 ^ m) := by
  exact two_le_prefixTernaryDoubleCarryCount_of_hasTwoTernaryTwosBelow
    (four_pow_has_two_ternary_twos_in_finite_range hlower hupper)

end GKPCarry

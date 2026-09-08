/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A strict dyadic inequality on an integer circle

See the project entry module for the exact coordinate restrictions and source roles.
For two distinct integer vectors of the same nonzero squared norm, the squared
norm of their difference has strictly larger 2-adic valuation.
-/

namespace LeanPool.RareDistanceFields.DyadicNorm

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The squared Euclidean norm of an integer coordinate pair. -/
def normSq (a b : ℤ) : ℤ := a ^ 2 + b ^ 2

theorem square_mod_four (a : ℤ) : a ^ 2 % 4 = (a % 2) ^ 2 := by
  have h : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  rcases h with h|h|h|h
  all_goals
    have h2 : a % 2 = a % 4 % 2 := by omega
    rw [pow_two, Int.mul_emod, h, h2, h]
    norm_num

theorem four_dvd_norm_iff (a b : ℤ) : 4 ∣ normSq a b ↔ 2 ∣ a ∧ 2 ∣ b := by
  rw [Int.dvd_iff_emod_eq_zero, normSq, Int.add_emod, square_mod_four, square_mod_four]
  simp only [Int.dvd_iff_emod_eq_zero]
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases ha with ha|ha <;> rcases hb with hb|hb <;> simp [ha, hb]

theorem norm_mod_two (a b : ℤ) : normSq a b % 2 = (a + b) % 2 := by
  have hs (z : ℤ) : z ^ 2 % 2 = z % 2 := by
    rw [pow_two, Int.mul_emod]
    have hz : z % 2 = 0 ∨ z % 2 = 1 := by omega
    rcases hz with hz|hz <;> simp [hz]
  rw [normSq, Int.add_emod, hs, hs, ← Int.add_emod]

theorem equal_norm_difference_even (a b c d : ℤ) (he : normSq a b = normSq c d) :
    2 ∣ normSq (a - c) (b - d) := by
  have h := congrArg (fun z : ℤ => z % 2) he
  rw [norm_mod_two, norm_mod_two] at h
  rw [Int.dvd_iff_emod_eq_zero, norm_mod_two]
  omega

theorem even_norm_not_four (a b : ℤ) (he : 2 ∣ normSq a b) (hf : ¬ 4 ∣ normSq a b) :
    a % 2 = 1 ∧ b % 2 = 1 := by
  rw [Int.dvd_iff_emod_eq_zero, norm_mod_two] at he
  rw [four_dvd_norm_iff] at hf
  simp only [Int.dvd_iff_emod_eq_zero] at hf
  omega

theorem equal_norm_increase_aux (N : ℕ) :
    ∀ a b c d : ℤ, normSq a b = N → normSq c d = N → 0 < N →
      normSq (a - c) (b - d) ≠ 0 →
      padicValInt 2 (N : ℤ) < padicValInt 2 (normSq (a - c) (b - d)) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro a b c d ha hb hN hdiff
    by_cases h4 : (4 : ℤ) ∣ N
    · obtain ⟨a', rfl⟩ := (four_dvd_norm_iff a b).mp (ha ▸ h4) |>.1
      obtain ⟨b', rfl⟩ := (four_dvd_norm_iff (2 * a') b).mp (ha ▸ h4) |>.2
      obtain ⟨c', rfl⟩ := (four_dvd_norm_iff c d).mp (hb ▸ h4) |>.1
      obtain ⟨d', rfl⟩ := (four_dvd_norm_iff (2 * c') d).mp (hb ▸ h4) |>.2
      have hN4 : 4 ∣ N := by exact_mod_cast h4
      obtain ⟨M, hM⟩ := hN4
      have hMpos : 0 < M := by omega
      have hMN : M < N := by omega
      have ha' : normSq a' b' = M := by
        simp only [normSq] at ha ⊢
        rw [hM, Nat.cast_mul, Nat.cast_ofNat] at ha
        nlinarith
      have hb' : normSq c' d' = M := by
        simp only [normSq] at hb ⊢
        rw [hM, Nat.cast_mul, Nat.cast_ofNat] at hb
        nlinarith
      have heq : normSq (2 * a'-2 * c') (2 * b'-2 * d') = 4 * normSq (a'-c') (b'-d') := by
        simp only [normSq]; ring
      rw [heq] at hdiff ⊢
      have hd' : normSq (a'-c') (b'-d') ≠ 0 := by intro h; simp [h] at hdiff
      have hm0 : (M : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hMpos)
      have hi := ih M hMN a' b' c' d' ha' hb' hMpos hd'
      rw [hM, Nat.cast_mul, Nat.cast_ofNat, padicValInt.mul (by norm_num) hm0,
        padicValInt.mul (by norm_num) hd']
      omega
    · by_cases h2 : (2 : ℤ) ∣ N
      · have hab := even_norm_not_four a b (ha ▸ h2) (ha ▸ h4)
        have hcd := even_norm_not_four c d (hb ▸ h2) (hb ▸ h4)
        have hd4 : (4 : ℤ) ∣ normSq (a - c) (b - d) := by
          rw [four_dvd_norm_iff]
          simp only [Int.dvd_iff_emod_eq_zero]
          constructor <;> omega
        have hv : 2 ≤ padicValInt 2 (normSq (a - c) (b - d)) := by
          have hh := (padicValInt_dvd_iff (p := 2) 2 (normSq (a - c) (b - d))).mp
            (by simpa using hd4)
          exact hh.resolve_left hdiff
        have hvN : padicValInt 2 (N : ℤ) = 1 := by
          have hn0 : (N : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
          have hlo := (padicValInt_dvd_iff (p := 2) 1 (N : ℤ)).mp (by simpa using h2)
          have hhi : ¬ 2 ≤ padicValInt 2 (N : ℤ) := by
            intro h
            apply h4
            simpa using (padicValInt_dvd_iff (p := 2) 2 (N : ℤ)).mpr (Or.inr h)
          have := hlo.resolve_left hn0
          omega
        omega
      · rw [padicValInt.eq_zero_of_not_dvd h2]
        have hd2 := equal_norm_difference_even a b c d (ha.trans hb.symm)
        have hv := (padicValInt_dvd_iff (p := 2) 1 (normSq (a - c) (b - d))).mp (by simpa using hd2)
        have := hv.resolve_left hdiff
        omega

theorem equal_norm_increase (a b c d : ℤ) (hn : normSq a b ≠ 0)
    (he : normSq a b = normSq c d) (hd : normSq (a - c) (b - d) ≠ 0) :
    padicValInt 2 (normSq a b) < padicValInt 2 (normSq (a - c) (b - d)) := by
  have hnonneg : 0 ≤ normSq a b := by dsimp [normSq]; positivity
  have hpos : 0 < normSq a b := lt_of_le_of_ne hnonneg (Ne.symm hn)
  have ha : normSq a b = ((normSq a b).toNat : ℤ) := (Int.toNat_of_nonneg hnonneg).symm
  simpa only [Int.toNat_of_nonneg hnonneg] using
    equal_norm_increase_aux (normSq a b).toNat a b c d ha (he.symm.trans ha)
      (by omega) hd

end LeanPool.RareDistanceFields.DyadicNorm

/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Preliminaries.Arithmetic
import LeanPool.KasamiCyclicAdditive.MCM.Fourier
import LeanPool.KasamiCyclicAdditive.MCM.FrobeniusSum
import LeanPool.KasamiCyclicAdditive.MCM.DicksonPermutation
import LeanPool.KasamiCyclicAdditive.MCM.CharacterArithmetic
import LeanPool.KasamiCyclicAdditive.Preliminaries.FiniteCharacterCriterion

/-!
# The MCM permutation theorem

The Muller--Cohen--Matthews permutation theorem is proved here rather than
imported.  The ingredients are

* `mcmCharSum_eq_dickson` for generic multiplicative characters;
* `cubic_mcm_apply` for the exceptional cubic characters;
* `dickson_bijective` for the required Dickson permutation;
* `bijective_of_mulChar_sum_eq` for the final permutation argument.

The key character-sum theorem says that every nonprincipal multiplicative
character has vanishing untwisted MCM sum.  Together with the elementary fact
that the MCM map has zero as its unique zero, this makes all multiplicative
character sums preserved, hence the MCM map a permutation.
-/

open Finset Polynomial

namespace KasamiCyclicAdditive

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-- Odd `k` coprime to `n` is also coprime to `2n`. -/
theorem odd_coprime_two_mul {k n : ℕ} (hk : Odd k) (hkn : Nat.Coprime k n) :
    Nat.Coprime k (2 * n) := by
  have hk2 : Nat.Coprime k 2 := by
    obtain ⟨m, rfl⟩ := hk
    simp
  rw [Nat.coprime_mul_iff_right]
  exact ⟨hk2, hkn⟩

/-! ### The MCM map has no nonzero zero -/

omit [DecidableEq K] in
/-- Under the odd Kasami hypotheses, `mcmMap k` maps nonzero elements to
nonzero elements. -/
theorem mcmMap_ne_zero_of_ne_zero
    {n k : ℕ} (hcard : Fintype.card K = 2 ^ n) (hk : Odd k)
    (hkn : Nat.Coprime k n) {s : K} (hs : s ≠ 0) : mcmMap k s ≠ 0 := by
  rw [mcmMap]
  exact div_ne_zero
    (pow_ne_zero _ (frobSum_ne_zero_of_odd hcard hk hkn hs))
    (pow_ne_zero _ hs)

omit [DecidableEq K] in
/-- Zero is the unique zero of the odd-parameter MCM map. -/
theorem mcmMap_eq_zero_iff
    {n k : ℕ} (hcard : Fintype.card K = 2 ^ n) (hk : Odd k)
    (hkn : Nat.Coprime k n) (s : K) :
    mcmMap k s = 0 ↔ s = 0 := by
  constructor
  · intro hm
    by_contra hs
    exact mcmMap_ne_zero_of_ne_zero hcard hk hkn hs hm
  · rintro rfl
    simp [mcmMap, frobSum]

/-! ### Character sums -/

omit [DecidableEq K] in
/-- Every nonprincipal multiplicative character has vanishing untwisted MCM
sum under the odd Kasami hypotheses. -/
theorem mcmCharSum_eq_zero_of_ne_one
    {n k : ℕ} (hklt : k < n)
    (hcard : Fintype.card K = 2 ^ n) (hk : Odd k) (hkn : Nat.Coprime k n)
    (χ : MulChar K ℂ) (hchi : χ ≠ 1) :
    mcmCharSum k χ = 0 := by
  by_cases he : χ ^ (2 ^ k + 1) = 1
  · have hchi3 : χ ^ 3 = 1 :=
      mulChar_cube_eq_one_of_kasami_exceptional hcard hkn χ he
    rw [mcmCharSum]
    calc
      (∑ s : K, χ (mcmMap k s)) = ∑ s : K, χ s := by
        apply Finset.sum_congr rfl
        intro s hs
        exact cubic_mcm_apply hcard hk hkn χ hchi3 s
      _ = 0 := MulChar.sum_eq_zero_of_ne_one hchi
  · have hkn2 : Nat.Coprime k (2 * n) := odd_coprime_two_mul hk hkn
    have hm : Nat.Coprime (2 ^ k - 1) (Fintype.card K ^ 2 - 1) := by
      rw [hcard, ← pow_mul]
      simpa [mul_comm] using coprime_two_pow_sub_one hkn2
    have hD : Function.Bijective
        (fun x : K => (dickson 1 1 (2 ^ k - 1)).eval x) :=
      dickson_bijective hm
    have hsum :
        (∑ b : K, χ ((dickson 1 1 (2 ^ k - 1)).eval b)) = ∑ b : K, χ b := by
      refine Fintype.sum_bijective
        (fun x : K => (dickson 1 1 (2 ^ k - 1)).eval x) hD _ _ ?_
      intro x
      rfl
    have hA := mcmCharSum_eq_dickson hklt hcard
      (primitiveAddChar K) primitiveAddChar_isPrimitive primitiveAddChar_sq χ he
    rw [hsum, MulChar.sum_eq_zero_of_ne_one hchi, mul_zero] at hA
    exact hA

omit [DecidableEq K] in
/-- Every multiplicative character sum is preserved by the odd-parameter MCM
map. The nonprincipal case is `mcmCharSum_eq_zero_of_ne_one`; the principal case uses
that zero is the unique zero. -/
theorem mcmCharSum_eq_sum_of_odd
    {n k : ℕ} (hklt : k < n)
    (hcard : Fintype.card K = 2 ^ n) (hk : Odd k) (hkn : Nat.Coprime k n)
    (χ : MulChar K ℂ) :
    mcmCharSum k χ = ∑ s : K, χ s := by
  by_cases hchi : χ = 1
  · subst χ
    rw [mcmCharSum]
    apply Finset.sum_congr rfl
    intro s hs_mem
    by_cases hs : s = 0
    · subst s
      simp [mcmMap, frobSum]
    · rw [MulChar.one_apply
          (isUnit_iff_ne_zero.mpr (mcmMap_ne_zero_of_ne_zero hcard hk hkn hs)),
        MulChar.one_apply (isUnit_iff_ne_zero.mpr hs)]
  · rw [mcmCharSum_eq_zero_of_ne_one hklt hcard hk hkn χ hchi,
      MulChar.sum_eq_zero_of_ne_one hchi]

omit [DecidableEq K] in
/-- **Muller--Cohen--Matthews permutation theorem.**  For odd `k < n` coprime
to `n`, the MCM map is a permutation of every characteristic two finite field
of order `2^n`. -/
theorem mcmMap_bijective_of_odd
    {n k : ℕ} (hklt : k < n)
    (hcard : Fintype.card K = 2 ^ n) (hk : Odd k) (hkn : Nat.Coprime k n) :
    Function.Bijective (mcmMap (K := K) k) := by
  apply bijective_of_mulChar_sum_eq (mcmMap k)
  · intro s
    exact mcmMap_eq_zero_iff hcard hk hkn s
  · intro χ
    simpa [mcmCharSum] using mcmCharSum_eq_sum_of_odd hklt hcard hk hkn χ

end

end KasamiCyclicAdditive

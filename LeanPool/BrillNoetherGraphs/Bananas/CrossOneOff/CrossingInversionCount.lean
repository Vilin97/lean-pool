/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaInversionCount

/-!
# Counting a collision of crossing affine inversions

This file isolates the combinatorial counting step in the proof of paper
Proposition 6.1.  Two distinct inversions crossing the origin which represent
the same affine inversion class force at least `2 * k - 1` distinct affine
inversion classes.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- Normalize an ordinary inversion by translating its first coordinate into
the fundamental interval `[0, k)`. -/
def normalizeInversionFirst (k : ℕ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 % k, p.2 - (p.1 / k) * k)

private theorem crossing_collision_count_oriented
    {k : ℕ} {tau : ℤ → ℤ} (hk : 0 < k) (hAffine : IsKAffine k tau)
    {a b a' b' : ℤ}
    (haNeg : a < 0) (hbNonneg : 0 ≤ b)
    (haPos : 0 < tau a) (hbNonpos : tau b ≤ 0)
    (ha'Neg : a' < 0) (_hb'Nonneg : 0 ≤ b')
    (_ha'Pos : 0 < tau a') (hb'Nonpos : tau b' ≤ 0)
    (haa' : a < a')
    (hSame : normalizeInversionFirst k (a, b) =
      normalizeInversionFirst k (a', b')) :
    2 * k - 1 ≤ kInversionCount k tau := by
  have hkZ : 0 < (k : ℤ) := by exact_mod_cast hk
  by_cases hkOne : k = 1
  · subst k
    have hInv : (a, b) ∈ invSet tau := by
      exact ⟨by omega, by omega⟩
    have hmem := inversion_normalize_first_coordinate (k := 1)
      (tau := tau) (by omega) hAffine hInv
    have hfinite := kInversions_finite_of_isKAffine (k := 1)
      (τ := tau) (by omega) hAffine
    have hpos : 0 < kInversionCount 1 tau := by
      rw [kInversionCount, Set.ncard_pos hfinite]
      exact ⟨_, hmem⟩
    omega
  have hkTwo : 2 ≤ k := by omega
  change (a % k, b - (a / k) * k) =
    (a' % k, b' - (a' / k) * k) at hSame
  have hMod : a % k = a' % k := congrArg Prod.fst hSame
  have hSecond : b - (a / k) * k = b' - (a' / k) * k :=
    congrArg Prod.snd hSame
  let q : ℤ := a' / k - a / k
  have haRepr := int_eq_emod_add_ediv_period (k := k) (b := a) hk
  have ha'Repr := int_eq_emod_add_ediv_period (k := k) (b := a') hk
  have haa'q : a' = a + q * k := by
    calc
      a' = a' % k + k * (a' / k) := ha'Repr
      _ = a % k + k * (a' / k) := by rw [hMod]
      _ = (a % k + k * (a / k)) + q * k := by dsimp [q]; ring
      _ = a + q * k := by rw [← haRepr]
  have hqPos : 0 < q := by
    by_contra h
    have hqNonpos : q ≤ 0 := by omega
    nlinarith
  have hbb'q : b' = b + q * k := by
    dsimp [q]
    linarith
  have hLong : a + 2 * (k : ℤ) + 1 ≤ b' := by
    have hqOne : 1 ≤ q := by omega
    have hqk : (k : ℤ) ≤ q * k := by nlinarith
    nlinarith
  let interval : Finset ℤ := Finset.Icc (a + 1) (a + 2 * (k : ℤ) + 1)
  let I : Finset ℤ :=
    (interval.erase (a + k)).erase (a + 2 * (k : ℤ))
  have hFirstForbidden : a + (k : ℤ) ∈ interval := by
    simp only [interval, Finset.mem_Icc]
    constructor <;> omega
  have hForbiddenNe : a + 2 * (k : ℤ) ≠ a + k := by omega
  have hSecondForbidden :
      a + 2 * (k : ℤ) ∈ interval.erase (a + k) := by
    simp only [Finset.mem_erase]
    refine ⟨hForbiddenNe, ?_⟩
    simp only [interval, Finset.mem_Icc]
    constructor <;> omega
  have hcardInterval : interval.card = 2 * k + 1 := by
    simp only [interval, Int.card_Icc]
    have hcalc : a + 2 * (k : ℤ) + 1 + 1 - (a + 1) =
        ((2 * k + 1 : ℕ) : ℤ) := by push_cast; ring
    calc
      (a + 2 * (k : ℤ) + 1 + 1 - (a + 1)).toNat =
          (((2 * k + 1 : ℕ) : ℤ)).toNat := congrArg Int.toNat hcalc
      _ = 2 * k + 1 := Int.toNat_natCast _
  have hcardI : I.card = 2 * k - 1 := by
    simp only [I, Finset.card_erase_of_mem hSecondForbidden,
      Finset.card_erase_of_mem hFirstForbidden, hcardInterval]
    omega
  let candidate : ℤ → ℤ × ℤ := fun i =>
    if tau i ≤ 0 then (a, i) else (i, b')
  let representative : ℤ → ℤ × ℤ := fun i =>
    normalizeInversionFirst k (candidate i)
  have hmap : ∀ i ∈ I, representative i ∈ kInversions k tau := by
    intro i hi
    have hiData : i ∈ interval ∧ i ≠ a + k ∧
        i ≠ a + 2 * (k : ℤ) := by
      simpa [I, and_assoc, and_left_comm, and_comm] using hi
    have hiLo : a < i := by
      have := (Finset.mem_Icc.mp hiData.1).1
      omega
    have hiHi : i ≤ a + 2 * (k : ℤ) + 1 :=
      (Finset.mem_Icc.mp hiData.1).2
    by_cases hiTau : tau i ≤ 0
    · have hInv : (a, i) ∈ invSet tau := ⟨hiLo, by omega⟩
      simpa [representative, candidate, hiTau, normalizeInversionFirst] using
        inversion_normalize_first_coordinate hk hAffine hInv
    · have hib' : i < b' := by
        have : i ≤ b' := hiHi.trans hLong
        by_contra h
        have hibEq : i = b' := by omega
        subst i
        omega
      have hInv : (i, b') ∈ invSet tau := ⟨hib', by omega⟩
      simpa [representative, candidate, hiTau, normalizeInversionFirst] using
        inversion_normalize_first_coordinate hk hAffine hInv
  have hNotCongruent : ∀ i ∈ I, i % k ≠ a % k := by
    intro i hi hCongruent
    have hiData : i ∈ interval ∧ i ≠ a + k ∧
        i ≠ a + 2 * (k : ℤ) := by
      simpa [I, and_assoc, and_left_comm, and_comm] using hi
    have hiLo : a < i := by
      have := (Finset.mem_Icc.mp hiData.1).1
      omega
    have hiHi : i ≤ a + 2 * (k : ℤ) + 1 :=
      (Finset.mem_Icc.mp hiData.1).2
    have hiRepr := int_eq_emod_add_ediv_period (k := k) (b := i) hk
    have haRepr' := int_eq_emod_add_ediv_period (k := k) (b := a) hk
    let s : ℤ := i / k - a / k
    have hia : i = a + s * k := by
      calc
        i = i % k + k * (i / k) := hiRepr
        _ = a % k + k * (i / k) := by rw [hCongruent]
        _ = (a % k + k * (a / k)) + s * k := by dsimp [s]; ring
        _ = a + s * k := by rw [← haRepr']
    have hsPos : 0 < s := by
      by_contra h
      have : s ≤ 0 := by omega
      nlinarith
    have hsLt : s < 3 := by
      by_contra h
      have : 3 ≤ s := by omega
      nlinarith
    have hs : s = 1 ∨ s = 2 := by omega
    rcases hs with hs | hs
    · rw [hs] at hia
      exact hiData.2.1 (by simpa using hia)
    · rw [hs] at hia
      exact hiData.2.2 (by simpa using hia)
  have hinj : Set.InjOn representative (I : Set ℤ) := by
    intro i hi j hj hij
    have hiI : i ∈ I := hi
    have hjI : j ∈ I := hj
    by_cases hiTau : tau i ≤ 0
    · by_cases hjTau : tau j ≤ 0
      · have hsecond := congrArg Prod.snd hij
        simpa [representative, candidate, hiTau, hjTau,
          normalizeInversionFirst] using hsecond
      · have hfirst := congrArg Prod.fst hij
        have : a % k = j % k := by
          simpa [representative, candidate, hiTau, hjTau,
            normalizeInversionFirst] using hfirst
        exact False.elim ((hNotCongruent j hjI) this.symm)
    · by_cases hjTau : tau j ≤ 0
      · have hfirst := congrArg Prod.fst hij
        have : i % k = a % k := by
          simpa [representative, candidate, hiTau, hjTau,
            normalizeInversionFirst] using hfirst
        exact False.elim ((hNotCongruent i hiI) this)
      · have hfirst : i % k = j % k := by
          simpa [representative, candidate, hiTau, hjTau,
            normalizeInversionFirst] using congrArg Prod.fst hij
        have hsecond : b' - (i / k) * k = b' - (j / k) * k := by
          simpa [representative, candidate, hiTau, hjTau,
            normalizeInversionFirst] using congrArg Prod.snd hij
        have hquot : i / k = j / k := by
          have : (i / k) * (k : ℤ) = (j / k) * k := by linarith
          exact Int.eq_of_mul_eq_mul_right (by omega) this
        have hiRepr := int_eq_emod_add_ediv_period (k := k) (b := i) hk
        have hjRepr := int_eq_emod_add_ediv_period (k := k) (b := j) hk
        rw [hiRepr, hjRepr, hfirst, hquot]
  have hfinite := kInversions_finite_of_isKAffine hk hAffine
  have hle := Set.ncard_le_ncard_of_injOn
    (s := (I : Set ℤ)) (t := kInversions k tau)
    representative hmap hinj hfinite
  simpa [Set.ncard_coe_finset, hcardI, kInversionCount] using hle

/-- Two distinct crossing inversions with the same normalized first-coordinate
representative force at least `2 * k - 1` affine inversion classes.  This is
the counting kernel of paper Proposition 6.1. -/
theorem kInversionCount_ge_two_mul_sub_one_of_crossing_collision
    {k : ℕ} {tau : ℤ → ℤ} (hk : 0 < k) (hAffine : IsKAffine k tau)
    {a b a' b' : ℤ}
    (haNeg : a < 0) (hbNonneg : 0 ≤ b)
    (haPos : 0 < tau a) (hbNonpos : tau b ≤ 0)
    (ha'Neg : a' < 0) (hb'Nonneg : 0 ≤ b')
    (ha'Pos : 0 < tau a') (hb'Nonpos : tau b' ≤ 0)
    (hDistinct : (a, b) ≠ (a', b'))
    (hSame : normalizeInversionFirst k (a, b) =
      normalizeInversionFirst k (a', b')) :
    2 * k - 1 ≤ kInversionCount k tau := by
  have haa' : a ≠ a' := by
    intro h
    subst a'
    apply hDistinct
    have hsecond := congrArg Prod.snd hSame
    have : b = b' := by
      simpa [normalizeInversionFirst] using hsecond
    subst b'
    rfl
  rcases lt_or_gt_of_ne haa' with haa' | ha'a
  · exact crossing_collision_count_oriented hk hAffine
      haNeg hbNonneg haPos hbNonpos ha'Neg hb'Nonneg ha'Pos hb'Nonpos
      haa' hSame
  · exact crossing_collision_count_oriented hk hAffine
      ha'Neg hb'Nonneg ha'Pos hb'Nonpos haNeg hbNonneg haPos hbNonpos
      ha'a hSame.symm

end Bananas

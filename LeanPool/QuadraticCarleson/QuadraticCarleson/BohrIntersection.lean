/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.Bohr

/-!
# Intersection of localized Bohr sets

This file proves Lemma `l:bohrintersection` of the paper by counting integer
pairs near the line of slope `m / k`. The positive-frequency hypotheses
follow the paper's explicit convention `ℕ = {1, 2, …}`. The final two lemmas
record the zero-frequency behavior for Lean's different natural-number convention.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson

/-- A small torus norm gives a nearby integer. -/
theorem exists_int_abs_sub_le_of_torusNorm_le {x ρ : ℝ}
    (h : torusNorm x ≤ ρ) : ∃ a : ℤ, |x - a| ≤ ρ := by
  rcases min_le_iff.mp h with h | h
  · refine ⟨⌊x⌋, ?_⟩
    rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le x))]
    exact h
  · refine ⟨⌊x⌋ + 1, ?_⟩
    have hf := Int.fract_nonneg x
    have hf' := Int.fract_lt_one x
    rw [Int.fract] at h hf hf'
    rw [abs_le]
    push_cast
    constructor <;> linarith

/-- For localized Bohr sets, the integer witnessing the torus condition
lies between zero and the frequency. -/
theorem exists_int_near_of_mem_bohrSet {k : ℕ} {ρ x : ℝ}
    (hρ : ρ < 1 / 10) (hx : x ∈ bohrSet k ρ) :
    ∃ a : ℤ, 0 ≤ a ∧ a ≤ k ∧ |(k : ℝ) * x - a| ≤ ρ := by
  obtain ⟨a, ha⟩ := exists_int_abs_sub_le_of_torusNorm_le hx.2
  have ha' := abs_le.mp ha
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hx0 : 0 ≤ x := by linarith [hx.1.1]
  have hxl : (k : ℝ) * x ≤ k := by nlinarith [hx.1.2]
  have ha0 : (-1 : ℝ) < a := by nlinarith [mul_nonneg hk hx0]
  have hak : (a : ℝ) < (k : ℝ) + 1 := by linarith
  have ha0' : (-1 : ℤ) < a := by exact_mod_cast ha0
  have hak' : a < (k : ℤ) + 1 := by exact_mod_cast hak
  exact ⟨a, by omega, by omega, ha⟩

private theorem latticePairCode_injective {K M : ℤ} (hK : 0 < K)
    (hcop : Int.gcd K M = 1) :
    Function.Injective (fun p : ℤ × ℤ => (M * p.1 - K * p.2, p.1 / K)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ heq
  have hq : M * a - K * b = M * c - K * d := congrArg Prod.fst heq
  have hdiv : a / K = c / K := congrArg Prod.snd heq
  have hdvd : K ∣ M * (c - a) := ⟨d - b, by nlinarith [hq]⟩
  have hdvd' := Int.dvd_of_dvd_mul_right_of_gcd_one hdvd hcop
  have hmod : a % K = c % K := Int.modEq_iff_dvd.mpr hdvd'
  have hac : a = c := by
    have ha := Int.emod_add_ediv_mul a K
    have hc := Int.emod_add_ediv_mul c K
    rw [hmod, hdiv] at ha
    omega
  have hbd : b = d := by
    rw [hac] at hq
    nlinarith
  exact Prod.ext hac hbd

/-- Integer pairs in a rectangle whose determinant lies in a short interval. -/
private noncomputable def latticePairs (K M d : ℤ) (R : ℝ) : Finset (ℤ × ℤ) := by
  classical
  exact ((Finset.Icc 0 (K * d)).product (Finset.Icc 0 (M * d))).filter
    (fun p => |((M * p.1 - K * p.2 : ℤ) : ℝ)| ≤ R)

private theorem latticePairs_card_le {K M d : ℤ} {R : ℝ}
    (hK : 0 < K) (hd : 0 ≤ d) (hR : 0 ≤ R) (hcop : Int.gcd K M = 1) :
    ((latticePairs K M d R).card : ℝ) ≤ (2 * R + 1) * (d + 1) := by
  classical
  have hfloor : 0 ≤ ⌊R⌋ := Int.floor_nonneg.mpr hR
  have hcard := Finset.card_le_card_of_injOn
    (s := latticePairs K M d R)
    (t := (Finset.Icc (-⌊R⌋) ⌊R⌋).product (Finset.Icc 0 d))
    (fun p : ℤ × ℤ => (M * p.1 - K * p.2, p.1 / K)) ?_
    (latticePairCode_injective hK hcop).injOn
  · have h₁ : ((Finset.Icc (-⌊R⌋) ⌊R⌋).card : ℝ) = 2 * (⌊R⌋ : ℝ) + 1 := by
      have h := Int.card_Icc_of_le (a := -⌊R⌋) (b := ⌊R⌋) (by omega)
      have h' := congrArg (fun z : ℤ => (z : ℝ)) h
      push_cast at h'
      linarith
    have h₂ : ((Finset.Icc 0 d).card : ℝ) = d + 1 := by
      have h := Int.card_Icc_of_le (a := 0) (b := d) (by omega)
      have h' := congrArg (fun z : ℤ => (z : ℝ)) h
      push_cast at h'
      simpa using h'
    have hcard' : ((latticePairs K M d R).card : ℝ) ≤
        (2 * (⌊R⌋ : ℝ) + 1) * (d + 1) := by
      rw [← h₁, ← h₂]
      exact_mod_cast (show (latticePairs K M d R).card ≤
        (Finset.Icc (-⌊R⌋) ⌊R⌋).card * (Finset.Icc 0 d).card by
          simpa using hcard)
    calc
      ((latticePairs K M d R).card : ℝ) ≤
          (2 * (⌊R⌋ : ℝ) + 1) * (d + 1) := hcard'
      _ ≤ (2 * R + 1) * (d + 1) := by
        gcongr
        exact Int.floor_le R
  · rintro ⟨a, b⟩ hp
    change (a, b) ∈ latticePairs K M d R at hp
    simp only [latticePairs, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
      Finset.mem_Icc] at hp
    have hq := abs_le.mp hp.2
    have hq₁ : M * a - K * b ≤ ⌊R⌋ := Int.le_floor.mpr hq.2
    have hq₂ : -(M * a - K * b) ≤ ⌊R⌋ := by
      apply Int.le_floor.mpr
      rw [Int.cast_neg]
      linarith [hq.1]
    have hdiv₁ : 0 ≤ a / K := Int.ediv_nonneg hp.1.1.1 hK.le
    have hdiv₂ : a / K ≤ d := by
      apply (Int.ediv_le_iff_le_mul hK).mpr
      nlinarith [hp.1.1.2]
    change (M * a - K * b, a / K) ∈
      (Finset.Icc (-⌊R⌋) ⌊R⌋).product (Finset.Icc 0 d)
    simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨by omega, hq₁⟩, hdiv₁, hdiv₂⟩

private theorem bohrSet_inter_subset_latticeCover {k m : ℕ} {ρ : ℝ}
    {K M d : ℤ} (hρ : ρ < 1 / 10) (hK : 0 < K) (hM : 0 < M)
    (hmpos : 0 < m) (hk : (k : ℤ) = K * d) (hm : (m : ℤ) = M * d) :
    bohrSet k ρ ∩ bohrSet m ρ ⊆
      ⋃ p ∈ latticePairs K M d (ρ * (K + M)),
        Icc (((p.2 : ℝ) - ρ) / m) (((p.2 : ℝ) + ρ) / m) := by
  intro x hx
  obtain ⟨a, ha0, hak, ha⟩ := exists_int_near_of_mem_bohrSet hρ hx.1
  obtain ⟨b, hb0, hbm, hb⟩ := exists_int_near_of_mem_bohrSet hρ hx.2
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hmr : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hkr : (k : ℝ) = (K : ℝ) * d := by exact_mod_cast hk
  have hmr' : (m : ℝ) = (M : ℝ) * d := by exact_mod_cast hm
  have hdet : |((M * a - K * b : ℤ) : ℝ)| ≤ ρ * (K + M) := by
    calc
      |((M * a - K * b : ℤ) : ℝ)| =
          |(M : ℝ) * ((k : ℝ) * x - a) - (K : ℝ) * ((m : ℝ) * x - b)| := by
        rw [← abs_neg]
        congr 1
        push_cast
        rw [hkr, hmr']
        ring
      _ ≤ |(M : ℝ) * ((k : ℝ) * x - a)| +
          |(K : ℝ) * ((m : ℝ) * x - b)| := abs_sub _ _
      _ = (M : ℝ) * |(k : ℝ) * x - a| +
          (K : ℝ) * |(m : ℝ) * x - b| := by
        rw [abs_mul, abs_mul, abs_of_pos hMr, abs_of_pos hKr]
      _ ≤ (M : ℝ) * ρ + (K : ℝ) * ρ := by gcongr
      _ = ρ * (K + M) := by ring
  have hab : (a, b) ∈ latticePairs K M d (ρ * (K + M)) := by
    simp only [latticePairs, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
      Finset.mem_Icc]
    exact ⟨⟨⟨ha0, hk ▸ hak⟩, hb0, hm ▸ hbm⟩, hdet⟩
  apply mem_iUnion.mpr
  refine ⟨(a, b), mem_iUnion.mpr ⟨hab, ?_⟩⟩
  have hb' := abs_le.mp hb
  constructor
  · apply (div_le_iff₀ hmr).mpr
    nlinarith [hb'.2]
  · apply (le_div_iff₀ hmr).mpr
    nlinarith [hb'.1]

private theorem bohrSet_inter_volume_real_le_of_reduced {k m : ℕ} {ρ : ℝ}
    {K M d : ℤ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 10)
    (hK : 0 < K) (hM : 0 < M) (hd : 0 ≤ d) (hcop : Int.gcd K M = 1)
    (hmpos : 0 < m) (hk : (k : ℤ) = K * d) (hm : (m : ℤ) = M * d) :
    volume.real (bohrSet k ρ ∩ bohrSet m ρ) ≤
      (2 * (ρ * (K + M)) + 1) * (d + 1) * (2 * ρ / m) := by
  classical
  let s := latticePairs K M d (ρ * (K + M))
  let J : ℤ × ℤ → Set ℝ := fun p =>
    Icc (((p.2 : ℝ) - ρ) / m) (((p.2 : ℝ) + ρ) / m)
  have hmr : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hcover : bohrSet k ρ ∩ bohrSet m ρ ⊆ ⋃ p ∈ s, J p :=
    bohrSet_inter_subset_latticeCover hρ hK hM hmpos hk hm
  have hfinite : volume (⋃ p ∈ s, J p) ≠ ∞ := by
    apply ne_of_lt
    calc
      volume (⋃ p ∈ s, J p) ≤ ∑ p ∈ s, volume (J p) := measure_biUnion_finset_le _ _
      _ < ∞ := ENNReal.sum_lt_top.mpr fun p _ => by simp [J]
  have hJ : ∀ p, volume.real (J p) = 2 * ρ / m := by
    intro p
    dsimp [J]
    rw [Real.volume_real_Icc_of_le]
    · ring
    · apply div_le_div_of_nonneg_right _ hmr.le
      linarith
  have hR : 0 ≤ ρ * ((K : ℝ) + M) := by
    have hKr : (0 : ℝ) < K := by exact_mod_cast hK
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    positivity
  calc
    volume.real (bohrSet k ρ ∩ bohrSet m ρ) ≤ volume.real (⋃ p ∈ s, J p) :=
      measureReal_mono hcover hfinite
    _ ≤ ∑ p ∈ s, volume.real (J p) := measureReal_biUnion_finset_le _ _
    _ = (s.card : ℝ) * (2 * ρ / m) := by simp [hJ]
    _ ≤ (2 * (ρ * (K + M)) + 1) * (d + 1) * (2 * ρ / m) :=
      mul_le_mul_of_nonneg_right (latticePairs_card_le hK hd hR hcop) (by positivity)

private theorem bohrSet_inter_volume_real_le_of_le {k m : ℕ} {ρ : ℝ}
    (hkpos : 0 < k) (hmpos : 0 < m) (hkm : k ≤ m)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 10) :
    volume.real (bohrSet k ρ ∩ bohrSet m ρ) ≤
      16 * (ρ ^ 2 + ρ * (Nat.gcd k m : ℝ) / m) := by
  have hdpos : 0 < Nat.gcd k m := Nat.gcd_pos_of_pos_left m hkpos
  obtain ⟨K, M, hcop, hk, hm⟩ :=
    Int.exists_gcd_one (m := (k : ℤ)) (n := (m : ℤ)) (by simpa using hdpos)
  simp only [Int.gcd_natCast_natCast] at hk hm
  have hdi : (0 : ℤ) < Nat.gcd k m := by exact_mod_cast hdpos
  have hki : (0 : ℤ) < k := by exact_mod_cast hkpos
  have hmi : (0 : ℤ) < m := by exact_mod_cast hmpos
  have hK : 0 < K := by nlinarith [hk]
  have hM : 0 < M := by nlinarith [hm]
  have hkr : (k : ℝ) = (K : ℝ) * (Nat.gcd k m : ℝ) := by exact_mod_cast hk
  have hmr : (m : ℝ) = (M : ℝ) * (Nat.gcd k m : ℝ) := by exact_mod_cast hm
  have hmrpos : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hdr : (1 : ℝ) ≤ Nat.gcd k m := by exact_mod_cast hdpos
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hkmr : (k : ℝ) ≤ m := by exact_mod_cast hkm
  have hKM : (K : ℝ) ≤ M := by nlinarith [hkr, hmr]
  have hcount : (2 * (ρ * ((K : ℝ) + M)) + 1) * ((Nat.gcd k m : ℝ) + 1) ≤
      8 * ρ * m + 2 * (Nat.gcd k m : ℝ) := by
    calc
      (2 * (ρ * ((K : ℝ) + M)) + 1) * ((Nat.gcd k m : ℝ) + 1) ≤
          (4 * ρ * M + 1) * (2 * (Nat.gcd k m : ℝ)) := by
        apply mul_le_mul
        · nlinarith
        · linarith
        · positivity
        · positivity
      _ = 8 * ρ * m + 2 * (Nat.gcd k m : ℝ) := by rw [hmr]; ring
  calc
    volume.real (bohrSet k ρ ∩ bohrSet m ρ) ≤
        (2 * (ρ * ((K : ℝ) + M)) + 1) * ((Nat.gcd k m : ℝ) + 1) * (2 * ρ / m) := by
      simpa only [Int.cast_natCast] using
        bohrSet_inter_volume_real_le_of_reduced hρ0 hρ hK hM hdi.le hcop hmpos hk hm
    _ ≤ (8 * ρ * m + 2 * (Nat.gcd k m : ℝ)) * (2 * ρ / m) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = 16 * ρ ^ 2 + 4 * (ρ * (Nat.gcd k m : ℝ) / m) := by
      field_simp
      ring
    _ ≤ 16 * (ρ ^ 2 + ρ * (Nat.gcd k m : ℝ) / m) := by
      have hterm : 0 ≤ ρ * (Nat.gcd k m : ℝ) / m := by positivity
      nlinarith

/-- Lemma `l:bohrintersection`, with the explicit absolute constant `16`.
The positive frequencies follow the paper's convention `ℕ = {1, 2, …}`. -/
theorem bohrSet_inter_volume_real_le {k m : ℕ} {ρ : ℝ}
    (hk : 0 < k) (hm : 0 < m) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 10) :
    volume.real (bohrSet k ρ ∩ bohrSet m ρ) ≤
      16 * (ρ ^ 2 + ρ * (Nat.gcd k m : ℝ) / (max k m : ℕ)) := by
  rcases le_total k m with hkm | hmk
  · simpa only [max_eq_right hkm] using
      bohrSet_inter_volume_real_le_of_le hk hm hkm hρ0 hρ
  · simpa only [max_eq_left hmk, inter_comm, Nat.gcd_comm] using
      bohrSet_inter_volume_real_le_of_le hm hk hmk hρ0 hρ

/-- The same Bohr-intersection estimate expressed in the nonnegative extended
real codomain of Lebesgue measure. -/
theorem bohrSet_inter_volume_le {k m : ℕ} {ρ : ℝ}
    (hk : 0 < k) (hm : 0 < m) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 10) :
    volume (bohrSet k ρ ∩ bohrSet m ρ) ≤
      ENNReal.ofReal (16 * (ρ ^ 2 + ρ * (Nat.gcd k m : ℝ) / (max k m : ℕ))) := by
  have hfinite : volume (bohrSet k ρ ∩ bohrSet m ρ) ≠ ∞ :=
    measure_ne_top_of_subset
      (inter_subset_left.trans (bohrSet_subset_Ico k ρ)) (by simp)
  apply (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity)]
  exact bohrSet_inter_volume_real_le hk hm hρ0 hρ

/-- At zero frequency the Bohr condition is vacuous. This is a supplementary
note for Lean's convention that `0 ∈ ℕ`; the paper uses positive naturals. -/
theorem bohrSet_zero_of_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) :
    bohrSet 0 ρ = Ico (1 / 4 : ℝ) (1 / 2 : ℝ) := by
  ext x
  simp [bohrSet, torusNorm, hρ]

theorem volume_real_bohrSet_zero {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume.real (bohrSet 0 ρ) = 1 / 4 := by
  rw [bohrSet_zero_of_nonneg hρ, Real.volume_real_Ico]
  norm_num

end QuadraticCarleson

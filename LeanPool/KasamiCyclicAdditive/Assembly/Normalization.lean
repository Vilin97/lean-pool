/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Preliminaries.Arithmetic
import LeanPool.KasamiCyclicAdditive.Counting.Definitions
import LeanPool.KasamiCyclicAdditive.Statement.CoefficientForm
import LeanPool.KasamiCyclicAdditive.MCM.ComplementTransport
/-!
# Normalization and Frobenius coefficient transport

Two independent facts:

* `exists_normalized_parameter` — elementary arithmetic choosing between `k`
  and `n - k` so that the chosen representative avoids the bad class
  `k ≡ 3 (mod 6)`;
* `coefficientCount_transfer_complement` — the finite-field Frobenius
  bijection relating the counts at `k` and `n - k`.

Transport is stated in the original coefficient form.  This avoids the
incorrect stronger claim that `slopeTripleCount k ρ = slopeTripleCount (n-k) ρ`
at the *same* slope: Frobenius acts on the coefficients, hence on the slope,
as well.
-/

open Finset

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The arithmetic core of the parameter choice: an odd parameter coprime to `n` which additionally
avoids the exceptional residue `3 (mod 6)` whenever `n` is even produces the
required `m = (2 ^ k0 + 1)/3` coprime to `2 ^ n - 1`. -/
private lemma normalized_of_good {n k0 : ℕ} (hodd : Odd k0) (hcop : Nat.Coprime k0 n)
    (hgood : n % 2 = 1 ∨ k0 % 6 ≠ 3) :
    ∃ m, 2 ^ k0 + 1 = 3 * m ∧ Nat.Coprime m (2 ^ n - 1) := by
  have hk1 : k0 % 2 = 1 := Nat.odd_iff.mp hodd
  have h3 : (2 ^ k0 + 1) % 3 = 0 := by
    have h := two_pow_mod_three k0
    rw [hk1] at h
    omega
  obtain ⟨m, hm⟩ : 3 ∣ 2 ^ k0 + 1 := Nat.dvd_of_mod_eq_zero h3
  refine ⟨m, hm, ?_⟩
  have hmdvd : m ∣ 2 ^ (2 * k0) - 1 := by
    rw [two_pow_two_mul_sub_one, hm]
    exact (dvd_mul_left m 3).mul_right _
  have hD1 : Nat.gcd m (2 ^ n - 1) ∣ 2 ^ (2 * k0) - 1 := (Nat.gcd_dvd_left _ _).trans hmdvd
  have hD2 : Nat.gcd m (2 ^ n - 1) ∣ 2 ^ n - 1 := Nat.gcd_dvd_right _ _
  have hgdvd : Nat.gcd m (2 ^ n - 1) ∣ 2 ^ (Nat.gcd (2 * k0) n) - 1 := by
    rw [← Nat.pow_sub_one_gcd_pow_sub_one]
    exact Nat.dvd_gcd hD1 hD2
  have hg2 : Nat.gcd (2 * k0) n ∣ 2 := by
    have hco : Nat.Coprime (Nat.gcd (2 * k0) n) k0 :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) hcop.symm
    exact hco.dvd_of_dvd_mul_right (by rw [mul_comm]; exact Nat.gcd_dvd_left _ _)
  have hD3 : Nat.gcd m (2 ^ n - 1) ∣ 3 := by
    refine hgdvd.trans ?_
    rcases (Nat.dvd_prime Nat.prime_two).mp hg2 with h | h <;> rw [h] <;> norm_num
  rcases (Nat.dvd_prime Nat.prime_three).mp hD3 with h | h
  · exact h
  · exfalso
    have h3m : 3 ∣ m := h ▸ Nat.gcd_dvd_left _ _
    have h3n : 3 ∣ 2 ^ n - 1 := h ▸ Nat.gcd_dvd_right _ _
    have hne : n % 2 = 0 := by
      by_contra hodd'
      have h := two_pow_mod_three n
      have hn1 : n % 2 = 1 := by omega
      rw [hn1] at h
      have h1 : (1:ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
      omega
    have hk6 : k0 % 6 ≠ 3 := by rcases hgood with h' | h' <;> omega
    obtain ⟨s, hs⟩ := h3m
    have h9 : 2 ^ k0 % 9 = 8 := by
      have h' : 2 ^ k0 + 1 = 9 * s := by rw [hm, hs]; ring
      omega
    rw [two_pow_mod_nine] at h9
    have hr : k0 % 6 = 1 ∨ k0 % 6 = 3 ∨ k0 % 6 = 5 := by omega
    rcases hr with h' | h' | h' <;> rw [h'] at h9
    · norm_num at h9
    · omega
    · norm_num at h9

/-- For `k < n` coprime to `n`, one of `k`, `n - k` is odd, coprime to `n`, and
avoids `k ≡ 3 (mod 6)` when `n` is even, hence supplies an `m` with
`2 ^ k0 + 1 = 3 * m` and `gcd(m, 2 ^ n - 1) = 1`. -/
theorem exists_normalized_parameter {n k : ℕ}
    (hklt : k < n) (hkn : Nat.Coprime k n) :
    ∃ k0 m : ℕ,
      (k0 = k ∨ k0 = n - k) ∧
      Odd k0 ∧ Nat.Coprime k0 n ∧
      2 ^ k0 + 1 = 3 * m ∧ Nat.Coprime m (2 ^ n - 1) := by
  have hcompl : Nat.Coprime (n - k) n := (Nat.coprime_self_sub_left hklt.le).mpr hkn
  have hchoice : ∃ k0, (k0 = k ∨ k0 = n - k) ∧ Odd k0 ∧ Nat.Coprime k0 n ∧
      (n % 2 = 1 ∨ k0 % 6 ≠ 3) := by
    by_cases hk2 : k % 2 = 1
    · by_cases hn2 : n % 2 = 1
      · exact ⟨k, Or.inl rfl, Nat.odd_iff.mpr hk2, hkn, Or.inl hn2⟩
      · by_cases hk6 : k % 6 = 3
        · have h3k : (3:ℕ) ∣ k := by omega
          have hmod : n % 3 ≠ 0 := by
            intro h
            have hdvd : (3:ℕ) ∣ Nat.gcd k n := Nat.dvd_gcd h3k (Nat.dvd_of_mod_eq_zero h)
            rw [hkn] at hdvd
            omega
          exact ⟨n - k, Or.inr rfl, Nat.odd_iff.mpr (by omega), hcompl, Or.inr (by omega)⟩
        · exact ⟨k, Or.inl rfl, Nat.odd_iff.mpr hk2, hkn, Or.inr hk6⟩
    · have hn2 : n % 2 = 1 := by
        by_contra hn2
        have hdvd : (2:ℕ) ∣ Nat.gcd k n :=
          Nat.dvd_gcd (by omega) (by omega)
        rw [hkn] at hdvd
        omega
      exact ⟨n - k, Or.inr rfl, Nat.odd_iff.mpr (by omega), hcompl, Or.inl hn2⟩
  obtain ⟨k0, hk0, hodd, hcop, hgood⟩ := hchoice
  obtain ⟨m, hm, hcm⟩ := normalized_of_good hodd hcop hgood
  exact ⟨k0, m, hk0, hodd, hcop, hm, hcm⟩

/-! ### Frobenius transport auxiliaries -/

/-- Frobenius transport of the coefficient count from `k` to `n - k`.  The
coefficients move with `Δ`, so the transported count sits at new coefficients
`w1, w2` rather than at `v₁, v₂`. -/
theorem coefficientCount_transfer_complement [CharP K 2]
    {n k : ℕ} (hk : k ≤ n) (hcard : Fintype.card K = 2 ^ n)
    {v₁ v₂ : K} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    ∃ w1 w2 : K,
      w1 ≠ 0 ∧ w2 ≠ 0 ∧ w1 ≠ w2 ∧
      coefficientTripleCount k v₁ v₂ = coefficientTripleCount (n - k) w1 w2 := by
  let e : K ≃+* K := complementFrobeniusEquiv k
  have hdt : ∀ b : K, kasamiDerivative k b = e (kasamiDerivative (n - k) b) := by
    intro b
    rw [complementFrobeniusEquiv_apply]
    exact kasamiDerivative_complement hk hcard b
  have hDS : ∀ x : K, x ∈ derivativeImage k K ↔ e.symm x ∈ derivativeImage (n - k) K := by
    intro x
    simp only [derivativeImage, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b, by rw [hdt b, e.symm_apply_apply]⟩
    · rintro ⟨b, hb⟩
      exact ⟨b, by rw [hdt b, hb, e.apply_symm_apply]⟩
  refine ⟨e.symm v₁, e.symm v₂, by simpa using hv₁, by simpa using hv₂,
    e.symm.injective.ne hne, ?_⟩
  unfold coefficientTripleCount
  refine Finset.card_bij' (fun p _ => (e.symm p.1, e.symm p.2.1, e.symm p.2.2))
    (fun q _ => (e q.1, e q.2.1, e q.2.2)) ?_ ?_ ?_ ?_
  · rintro ⟨p1, p2, p3⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    obtain ⟨⟨h1, h2, h3⟩, hc⟩ := hp
    refine ⟨⟨(hDS p1).mp h1, (hDS p2).mp h2, (hDS p3).mp h3⟩, ?_⟩
    have h0 : e.symm (v₁ * p1 + v₂ * p2 + (v₁ + v₂) * p3) = 0 := by rw [hc, map_zero]
    simpa [map_add, map_mul] using h0
  · rintro ⟨q1, q2, q3⟩ hq
    simp only [Finset.mem_filter, Finset.mem_product] at hq ⊢
    obtain ⟨⟨h1, h2, h3⟩, hc⟩ := hq
    refine ⟨⟨(hDS _).mpr (by rwa [e.symm_apply_apply]), (hDS _).mpr (by rwa [e.symm_apply_apply]),
      (hDS _).mpr (by rwa [e.symm_apply_apply])⟩, ?_⟩
    have h0 : e (e.symm v₁ * q1 + e.symm v₂ * q2 + (e.symm v₁ + e.symm v₂) * q3) = 0 := by
      rw [hc, map_zero]
    simpa [map_add, map_mul, e.apply_symm_apply] using h0
  · rintro ⟨p1, p2, p3⟩ hp
    simp
  · rintro ⟨q1, q2, q3⟩ hq
    simp

/-- The normalized parameter `k0` together with the coefficients carrying the
count to it: `exists_normalized_parameter` chooses `k0 ∈ {k, n - k}`, and in the
complement case `coefficientCount_transfer_complement` supplies `w1, w2`. -/
theorem normalize_with_count_transport [CharP K 2]
    {n k : ℕ} (hkpos : 1 ≤ k) (hklt : k < n) (hkn : Nat.Coprime k n)
    (hcard : Fintype.card K = 2 ^ n)
    (hhalf : 2 * (derivativeImage k K).card = Fintype.card K)
    {v₁ v₂ : K} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    ∃ (k0 m : ℕ) (w1 w2 : K),
      (k0 = k ∨ k0 = n - k) ∧
      1 ≤ k0 ∧ k0 < n ∧
      Odd k0 ∧ Nat.Coprime k0 n ∧
      2 ^ k0 + 1 = 3 * m ∧ Nat.Coprime m (2 ^ n - 1) ∧
      2 * (derivativeImage k0 K).card = Fintype.card K ∧
      w1 ≠ 0 ∧ w2 ≠ 0 ∧ w1 ≠ w2 ∧
      coefficientTripleCount k v₁ v₂ = coefficientTripleCount k0 w1 w2 := by
  obtain ⟨k0, m, hk0, hodd, hcop0, he, hm⟩ :=
    exists_normalized_parameter hklt hkn
  rcases hk0 with hk0 | hk0
  · rw [hk0] at hodd hcop0 he
    exact ⟨k, m, v₁, v₂, Or.inl rfl, hkpos, hklt, hodd, hcop0, he, hm,
      hhalf, hv₁, hv₂, hne, rfl⟩
  · rw [hk0] at hodd hcop0 he
    have hk_le : k ≤ n := Nat.le_of_lt hklt
    have hhalf_comp : 2 * (derivativeImage (n - k) K).card = Fintype.card K := by
      rw [← card_derivativeImage_complement (K := K) hk_le hcard]
      exact hhalf
    obtain ⟨w1, w2, hw1, hw2, hwne, hcount⟩ :=
      coefficientCount_transfer_complement hk_le hcard hv₁ hv₂ hne
    have hkpos' : 1 ≤ n - k := by omega
    have hklt' : n - k < n := by omega
    exact ⟨n - k, m, w1, w2, Or.inr rfl, hkpos', hklt', hodd, hcop0, he, hm,
      hhalf_comp, hw1, hw2, hwne, hcount⟩

end KasamiCyclicAdditive

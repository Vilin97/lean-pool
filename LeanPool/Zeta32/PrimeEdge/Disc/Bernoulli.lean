/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.PrimeEdge.Local
public import LeanPool.Zeta32.Arith.Local.Val

/-! von Staudt–Clausen consequences used by the proof notes, Lemma 3:
`v_p(B'_k) ≥ -1` always, `v_p(B'_k) ≥ 0` unless `k > 0` and `(p - 1) ∣ k`, and the resulting
bounds on the local moments `locMoment s e = e B'_{e-1} + 2 s B'_e` for `v_p(s) ≥ 1`. -/

public section

open Polynomial
open scoped BigOperators
namespace Zeta32.PrimeEdge

open Zeta32.Arith.Local

variable {p : ℕ}

lemma VG_one_div_prime [hp : Fact p.Prime] {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) :
    VG p ((1 : ℚ) / q) 0 := by
  rw [one_div]
  have hv : padicValRat p (q : ℚ) = 0 := by
    rw [padicValRat.of_nat]
    have : ¬ p ∣ q := fun h => hqp ((Nat.prime_dvd_prime_iff_eq hp.out hq).mp h).symm
    simp [padicValNat.eq_zero_of_not_dvd this]
  have := VG.inv (p := p) (q := (q : ℚ))  (r := 0) (by rw [hv]; simp)
  simpa using this

lemma VG_one_div_self [hp : Fact p.Prime] : VG p ((1 : ℚ) / p) (-1) := by
  have h := VG.primePow (p := p) (-1)
  rw [zpow_neg_one] at h
  rw [one_div]
  simpa using h

/-- von Staudt–Clausen, even index: `B_{2m} = T - ∑_{q prime, (q-1) ∣ 2m} 1/q`. -/
lemma bernoulli_even_eq (m : ℕ) : ∃ T : ℤ, bernoulli (2 * m) =
    (T : ℚ) - ∑ q ∈ Finset.range (2 * m + 2) with q.Prime ∧ (q - 1) ∣ 2 * m, (1 : ℚ) / q := by
  obtain ⟨T, hT⟩ := Bernoulli.vonStaudt_clausen m
  exact ⟨T, by rw [hT]; ring⟩

lemma VG_bernoulli_even [Fact p.Prime] (m : ℕ) : VG p (bernoulli (2 * m)) (-1) := by
  obtain ⟨T, hT⟩ := bernoulli_even_eq m
  rw [hT]
  refine ((VG.intCast (p := p) T).mono (by norm_num)).sub (VG.sum _ fun q hq => ?_)
  rw [Finset.mem_filter] at hq
  by_cases hqp : q = p
  · rw [hqp]; exact VG_one_div_self
  · exact (VG_one_div_prime hq.2.1 hqp).mono (by norm_num)

lemma VG_bernoulli_even_of_not_dvd [Fact p.Prime] (m : ℕ) (hm : ¬ (p - 1) ∣ 2 * m) :
    VG p (bernoulli (2 * m)) 0 := by
  obtain ⟨T, hT⟩ := bernoulli_even_eq m
  rw [hT]
  refine (VG.intCast (p := p) T).sub (VG.sum _ fun q hq => ?_)
  rw [Finset.mem_filter] at hq
  have hqp : q ≠ p := by rintro rfl; exact hm hq.2.2
  exact VG_one_div_prime hq.2.1 hqp

lemma VG_half [hp : Fact p.Prime] (hp3 : 3 ≤ p) : VG p ((1 : ℚ) / 2) 0 := by
  have := VG_one_div_prime (p := p) (q := 2) Nat.prime_two (by omega)
  simpa using this

/-- `v_p(B'_k) ≥ -1`. -/
lemma VG_bernoulli' [Fact p.Prime] (hp3 : 3 ≤ p) (k : ℕ) : VG p (bernoulli' k) (-1) := by
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | hodd
  · rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0; rw [bernoulli'_zero]; exact VG.one.mono (by norm_num)
    · have hk1 : k ≠ 1 := by omega
      rw [← bernoulli_eq_bernoulli'_of_ne_one hk1, show k = 2 * m by omega]
      exact VG_bernoulli_even m
  · by_cases hk1 : k = 1
    · subst hk1; rw [bernoulli'_one]; exact (VG_half hp3).mono (by norm_num)
    · rw [bernoulli'_eq_zero_of_odd hodd (by obtain ⟨j, rfl⟩ := hodd; omega)]
      exact VG.zero _

/-- `v_p(B'_k) ≥ 0` for `k = 0` or `(p - 1) ∤ k`. -/
lemma VG_bernoulli'_zero [Fact p.Prime] (hp3 : 3 ≤ p) {k : ℕ} (hk : k = 0 ∨ ¬ (p - 1) ∣ k) :
    VG p (bernoulli' k) 0 := by
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | hodd
  · rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0; rw [bernoulli'_zero]; exact VG.one
    · have hk1 : k ≠ 1 := by omega
      have hnd : ¬ (p - 1) ∣ k := by
        rcases hk with h | h
        · omega
        · exact h
      rw [← bernoulli_eq_bernoulli'_of_ne_one hk1, show k = 2 * m by omega]
      exact VG_bernoulli_even_of_not_dvd m (by rw [show 2 * m = k by omega]; exact hnd)
  · by_cases hk1 : k = 1
    · subst hk1; rw [bernoulli'_one]; exact VG_half hp3
    · rw [bernoulli'_eq_zero_of_odd hodd (by obtain ⟨j, rfl⟩ := hodd; omega)]
      exact VG.zero _

/-- `B'_k` is `p`-integral for `k ≤ p - 2`. -/
lemma VG_bernoulli'_small [Fact p.Prime] (hp3 : 3 ≤ p) {k : ℕ} (hk : k + 2 ≤ p) :
    VG p (bernoulli' k) 0 := by
  refine VG_bernoulli'_zero hp3 ?_
  rcases Nat.eq_zero_or_pos k with h | h
  · exact Or.inl h
  · exact Or.inr fun hd => by have := Nat.le_of_dvd h hd; omega

lemma VG_two_mul [Fact p.Prime] {s r : ℚ} (h : VG p s r) : VG p (2 * s) r := by
  have := (VG.natCast (p := p) 2).mul h
  simpa using this

/-- `v_p(locMoment s e) ≥ -1` when `v_p(s) ≥ 1`. -/
lemma VG_locMoment [Fact p.Prime] (hp3 : 3 ≤ p) {s : ℚ} (hs : VG p s 1) (e : ℕ) :
    VG p (locMoment s e) (-1) := by
  unfold locMoment
  refine VG.add ?_ ?_
  · have := (VG.natCast (p := p) e).mul (VG_bernoulli' hp3 (e - 1))
    simpa using this
  · have := (VG_two_mul hs).mul (VG_bernoulli' hp3 e)
    refine (this.mono ?_)
    norm_num

/-- `v_p(locMoment s e) ≥ 0` for `e ≤ 2p - 2` (the only possible `p` in a denominator of
`B'_{e-1}` in that range is at `e = p`, where the factor `e` cancels it). -/
lemma VG_locMoment_zero [hp : Fact p.Prime] (hp3 : 3 ≤ p) {s : ℚ} (hs : VG p s 1) {e : ℕ}
    (he : e + 2 ≤ 2 * p) : VG p (locMoment s e) 0 := by
  unfold locMoment
  refine VG.add ?_ ?_
  · rcases Nat.eq_zero_or_pos e with h0 | hpos
    · subst h0; simp [VG.zero]
    · by_cases hd : e - 1 ≠ 0 ∧ (p - 1) ∣ (e - 1)
      · obtain ⟨hne, t, ht⟩ := hd
        have ht1 : t = 1 := by
          rcases t with _ | _ | t
          · rw [Nat.mul_zero] at ht; omega
          · rfl
          · exfalso
            have : (p - 1) * (t + 1 + 1) ≥ (p - 1) * 2 := Nat.mul_le_mul_left _ (by omega)
            omega
        subst ht1
        have hep : e = p := by omega
        rw [hep]
        have h1 : VG p (p : ℚ) 1 := by
          have := VG.primePow (p := p) 1
          simpa using this
        have := h1.mul (VG_bernoulli' hp3 (p - 1))
        simpa using this
      · have hk : e - 1 = 0 ∨ ¬ (p - 1) ∣ (e - 1) := by tauto
        have := (VG.natCast (p := p) e).mul (VG_bernoulli'_zero hp3 hk)
        simpa using this
  · have := (VG_two_mul hs).mul (VG_bernoulli' hp3 e)
    simpa using this

/-- `locMoment s e - locMoment 0 e = 2 s B'_e` has `v_p ≥ 1` for `e ≤ p - 2`. -/
lemma VG_locMoment_sub [Fact p.Prime] (hp3 : 3 ≤ p) {s : ℚ} (hs : VG p s 1) {e : ℕ}
    (he : e + 2 ≤ p) : VG p (locMoment s e - locMoment 0 e) 1 := by
  have heq : locMoment s e - locMoment 0 e = 2 * s * bernoulli' e := by
    unfold locMoment; ring
  rw [heq]
  have := (VG_two_mul hs).mul (VG_bernoulli'_small hp3 he)
  simpa using this

end Zeta32.PrimeEdge

end

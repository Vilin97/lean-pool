/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Arith.Outer.Entries

/-! the proof notes section 8.2, Lemma 9: the three kinds of residue classes and their class costs.

The poles `j ∈ [1, 5n]` are regrouped by `c = (j-1) mod p` (the class of `j` is `c+1 mod p`),
each class
listed in decreasing `j`: `jn c t = c + 1 + p (Ccl c - 1 - t)`.  Along a class the node weight
`wv` is
nondecreasing in `t` (`wv_step`).  For `7n < 3p` and `p ≤ 5n` the class cost
`Scl c = Σ_{k < Ccl c} min(wv(jn c k) + 2k, 0)` satisfies
* `c + 1 = p` (`ρ = 0`): `Scl c ≥ -4`;
* `c + 1 ≤ n` (`1 ≤ ρ ≤ n`): `Scl c ≥ -[c < 5n - 2p]`;
* `n < c + 1 < p` (`n < ρ < p`): `Scl c ≥ -4 [c < 5n - p]`.

The regrouping (`Ccl`, `jn`, `regroup`) is adapted from
dtq1997/li2-half-irrationality@d5d8206:Li2Unified/Modular/Base/DecayMediumAssembly.lean
and the finite indicator sums from .../Base/MediumClassCounts.lean. -/

public section

open Polynomial
open scoped BigOperators
namespace Zeta32.Outer
noncomputable section

section Regroup
variable (p K : ℕ)

-- adapted from Li2Unified/Modular/Base/DecayMediumAssembly.lean
/-- Number of indices at most `K` in the residue class represented by `c + 1`. -/
def Ccl (c : ℕ) : ℕ := if c + 1 ≤ K then (K - (c+1))/p + 1 else 0

/-- Descending enumeration of the residue class represented by `c + 1`. -/
@[expose]
def jn (c t : ℕ) : ℕ := c + 1 + p * (Ccl p K c - 1 - t)

lemma Ccl_pos {c : ℕ} {t : ℕ} (ht : t < Ccl p K c) : c + 1 ≤ K := by
  unfold Ccl at ht; split_ifs at ht with h
  · exact h
  · omega

lemma jn_le {c t : ℕ} (ht : t < Ccl p K c) : jn p K c t ≤ K := by
  have hc := Ccl_pos p K ht
  have hC : Ccl p K c = (K - (c+1))/p + 1 := by simp [Ccl, hc]
  unfold jn
  have h2 : p * ((K - (c+1))/p) ≤ K - (c+1) := Nat.mul_div_le _ _
  generalize (K - (c+1))/p = g at hC h2
  have h1 : Ccl p K c - 1 - t ≤ g := by omega
  have h3 := Nat.mul_le_mul_left p h1
  omega

lemma regroup_aux {j : ℕ} (hp : 0 < p) (hj1 : 1 ≤ j) (hj2 : j ≤ K) :
    (j-1) % p < p ∧ (j-1)/p < Ccl p K ((j-1) % p) ∧
      jn p K ((j-1) % p) (Ccl p K ((j-1) % p) - 1 - (j-1)/p) = j := by
  have hdm := Nat.div_add_mod (j-1) p
  have hr := Nat.mod_lt (j-1) hp
  generalize (j-1) % p = r at hdm hr ⊢
  generalize hq : (j-1)/p = q at hdm ⊢
  generalize hP : p * q = P at hdm
  have hc : r + 1 ≤ K := by omega
  have hC : Ccl p K r = (K - (r+1))/p + 1 := by simp [Ccl, hc]
  have hqg : q ≤ (K - (r+1))/p := by
    apply (Nat.le_div_iff_mul_le hp).mpr
    rw [mul_comm, hP]; omega
  generalize (K - (r+1))/p = g at hC hqg
  refine ⟨hr, by omega, ?_⟩
  unfold jn
  rw [hC, show g + 1 - 1 - (g + 1 - 1 - q) = q by omega, hP]
  omega

lemma regroup_inv {c t : ℕ} (hp : 0 < p) (hc : c < p) :
    (jn p K c t - 1) % p = c ∧ (jn p K c t - 1) / p = Ccl p K c - 1 - t := by
  have e : jn p K c t - 1 = c + p * (Ccl p K c - 1 - t) := by unfold jn; omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc, Nat.add_mul_div_left _ _ hp,
    Nat.div_eq_of_lt hc, zero_add]
  exact ⟨rfl, rfl⟩

theorem regroup {R : Type*} [AddCommMonoid R] (hp : 0 < p) (F : ℕ → R) :
    ∑ j ∈ Finset.Icc 1 K, F j =
      ∑ c ∈ Finset.range p, ∑ t ∈ Finset.range (Ccl p K c), F (jn p K c t) := by
  rw [← Finset.sum_sigma (Finset.range p) (fun c => Finset.range (Ccl p K c))
    (fun x => F (jn p K x.1 x.2))]
  refine Finset.sum_bij' (fun j _ => ⟨(j-1) % p, Ccl p K ((j-1) % p) - 1 - (j-1)/p⟩)
    (fun x _ => jn p K x.1 x.2) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    obtain ⟨h1, h2, -⟩ := regroup_aux p K hp hj1 hj2
    simp only [Finset.mem_sigma, Finset.mem_range]
    refine ⟨h1, ?_⟩
    generalize Ccl p K ((j-1) % p) = Cv at h2 ⊢
    generalize (j-1)/p = q at h2 ⊢
    omega
  · rintro ⟨c, t⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    simp only [Finset.mem_Icc]
    exact ⟨by unfold jn; omega, jn_le p K hx.2⟩
  · intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    exact (regroup_aux p K hp hj1 hj2).2.2
  · rintro ⟨c, t⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    obtain ⟨hmod, hdiv⟩ := regroup_inv p K (t := t) hp hx.1
    simp only [hmod, hdiv]
    congr 1
    omega
  · intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    rw [(regroup_aux p K hp hj1 hj2).2.2]

lemma Ccl_eq_succ {c : ℕ} (hc : c + 1 ≤ K) : Ccl p K c = (K - (c+1))/p + 1 := by
  simp [Ccl, hc]

lemma jn_eq {c t C : ℕ} (hC : Ccl p K c = C) : jn p K c t = c + 1 + p * (C - 1 - t) := by
  unfold jn; rw [hC]

end Regroup

/-! ## Node weights along a class -/

lemma wv_step {n p j d : ℕ} (hp : 0 < p) (hnj : n < j) (hK : j + p * d ≤ 5 * n) :
    wv n p (j + p*d) ≤ wv n p j := by
  unfold wv
  rw [ite_eq_right (show ¬ (j + p*d ≤ n) by omega), ite_eq_right (show ¬ (j ≤ n) by omega)]
  have e1 : (j + p*d - 1)/p = (j-1)/p + d := by
    rw [show j + p*d - 1 = (j-1) + p*d by omega, Nat.add_mul_div_left _ _ hp]
  have e2 : (j + p*d - 1 - n)/p = (j-1-n)/p + d := by
    rw [show j + p*d - 1 - n = (j-1-n) + p*d by omega, Nat.add_mul_div_left _ _ hp]
  have e3 : (5*n - j)/p = (5*n - (j + p*d))/p + d := by
    rw [show 5*n - j = (5*n - (j + p*d)) + p*d by omega, Nat.add_mul_div_left _ _ hp]
  rw [e1, e2, e3]
  have hb : betaWt p (j + p*d) ≤ betaWt p j := by
    unfold betaWt
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; simp
    · have h1 : ¬ (j + p*d < p) := by
        have : p ≤ p * d := Nat.le_mul_of_pos_right p hd
        omega
      rw [ite_eq_right h1]
      have hdv : (p ∣ j + p*d) ↔ p ∣ j := Nat.dvd_add_left (dvd_mul_right p d)
      by_cases hj : j < p
      · rw [ite_eq_left hj]; split_ifs <;> norm_num
      · rw [ite_eq_right hj]
        by_cases hpj : p ∣ j
        · rw [ite_eq_left (hdv.mpr hpj), ite_eq_left hpj]
        · rw [ite_eq_right (fun h => hpj (hdv.mp h)), ite_eq_right hpj]
  push_cast
  linarith

lemma betaWt_class {p c m : ℕ} (hc : c < p) :
    betaWt p (c + 1 + p*m) = if m = 0 ∧ c + 1 < p then 0 else if c + 1 = p then -2 else -3 := by
  unfold betaWt
  have hdv : (p ∣ c + 1 + p*m) ↔ c + 1 = p := by
    rw [Nat.dvd_add_left (dvd_mul_right p m)]
    constructor
    · intro h
      exact le_antisymm (by omega) (Nat.le_of_dvd (by omega) h)
    · intro h; rw [h]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [mul_zero, add_zero, true_and]
    by_cases h : c + 1 < p
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
      have : c + 1 = p := by omega
      rw [ite_eq_left (by rw [this]), ite_eq_left this]
  · have h1 : ¬ (c + 1 + p*m < p) := by
      have : p ≤ p * m := Nat.le_mul_of_pos_right p hm
      omega
    rw [ite_eq_right h1, ite_eq_right (show ¬ (m = 0 ∧ c + 1 < p) by omega)]
    by_cases h : c + 1 = p
    · rw [ite_eq_left (hdv.mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (hdv.mp h')), ite_eq_right h]

lemma wv_class {n p c m : ℕ} (hp : 0 < p) (hnp : n < p) (hc : c < p)
    (hm : c + 1 + p * m ≤ 5 * n) (hj : n < c + 1 + p * m) :
    wv n p (c+1+p*m) =
      ((if c < n then 5 else 1) : ℚ) - (Ccl p (5*n) c : ℚ) + betaWt p (c+1+p*m) := by
  have hcK : c + 1 ≤ 5*n := le_trans (Nat.le_add_right _ _) hm
  rw [Ccl_eq_succ p (5*n) hcK]
  unfold wv
  rw [ite_eq_right (by omega)]
  have e1 : (c + 1 + p*m - 1)/p = m := by
    rw [show c + 1 + p*m - 1 = c + p*m by omega, Nat.add_mul_div_left _ _ hp,
      Nat.div_eq_of_lt hc, zero_add]
  have e3 : (5*n - (c+1+p*m))/p = (5*n - (c+1))/p - m := by
    rw [show 5*n - (c+1+p*m) = (5*n - (c+1)) - p*m by omega]
    exact Nat.sub_mul_div _ _ _
  have hmle : m ≤ (5*n - (c+1))/p := by
    apply (Nat.le_div_iff_mul_le hp).mpr
    rw [mul_comm]; omega
  rw [e1, e3, Nat.cast_sub hmle]
  by_cases hcn : c < n
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0; omega
      · exact ⟨m - 1, by omega⟩
    have e2 : (c + 1 + p*(m'+1) - 1 - n)/p = m' := by
      rw [show c + 1 + p*(m'+1) - 1 - n = (p + c - n) + p*m' by rw [mul_add]; omega,
        Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (by omega), zero_add]
    rw [e2, ite_eq_left hcn]
    push_cast
    ring
  · have e2 : (c + 1 + p*m - 1 - n)/p = m := by
      rw [show c + 1 + p*m - 1 - n = (c - n) + p*m by omega,
        Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (by omega), zero_add]
    rw [e2, ite_eq_right hcn]
    push_cast
    ring

lemma wv_cancelled {n p j : ℕ} (hj : j ≤ n) : wv n p j = 15 * (n:ℚ) + 1 := by
  unfold wv; rw [ite_eq_left hj]

/-! ## Class costs -/

/-- The Newton-form class cost of `rank_one_GV`. -/
@[expose]
def Scl (n p c : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (Ccl p (5*n) c), min (wv n p (jn p (5*n) c k) + 2 * k) 0

lemma wv_jn {n p c C t : ℕ} (hp : 0 < p) (hnp : n < p) (hc : c < p) (hC : Ccl p (5 * n) c = C)
    (ht : t < C) (hj : n < c + 1 + p * (C - 1 - t)) :
    wv n p (jn p (5*n) c t) =
      ((if c < n then 5 else 1) : ℚ) - (C : ℚ) + betaWt p (c + 1 + p*(C-1-t)) := by
  have hle := jn_le p (5*n) (t := t) (c := c) (by rw [hC]; exact ht)
  rw [jn_eq p (5*n) hC] at hle ⊢
  rw [wv_class hp hnp hc hle hj, hC]

section ClassCosts
variable {n p c : ℕ}

/-- Class `ρ = 0` (`c + 1 = p`): the `L ≤ 2` nodes `kp` all have weight `-1 - L`. -/
lemma Scl_zero (h73 : 7 * n < 3 * p) (hp5 : p ≤ 5 * n) (hc : c + 1 = p) : -4 ≤ Scl n p c := by
  have hp : 0 < p := by omega
  have hnp : n < p := by omega
  have hcp : c < p := by omega
  have hcK : c + 1 ≤ 5*n := by omega
  have hcn : ¬ c < n := by omega
  have hC := Ccl_eq_succ p (5*n) hcK
  have hq : (5*n - (c+1))/p ≤ 1 := by
    apply Nat.lt_succ_iff.mp
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    omega
  have hdm := Nat.div_mul_le_self (5*n - (c+1)) p
  generalize (5*n - (c+1))/p = q at hC hq hdm
  unfold Scl
  obtain rfl | rfl : q = 0 ∨ q = 1 := by omega
  · rw [hC]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [wv_jn hp hnp hcp hC (t := 0) (by norm_num) (by omega), betaWt_class hcp]
    simp only [ite_eq_right hcn, hc]
    norm_num
  · rw [hC]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [wv_jn hp hnp hcp hC (t := 0) (by norm_num) (by omega),
      wv_jn hp hnp hcp hC (t := 1) (by norm_num) (by omega), betaWt_class hcp,
      betaWt_class hcp]
    simp only [ite_eq_right hcn, hc]
    norm_num

/-- Class `1 ≤ ρ ≤ n` (`c + 1 ≤ n`): the node `ρ` is cancelled, the `T ≤ 2` others have weight
`1 - T`. -/
lemma Scl_low (h73 : 7 * n < 3 * p) (hc : c + 1 ≤ n) :
    -(if c < 5*n - 2*p then (1:ℚ) else 0) ≤ Scl n p c := by
  have hp : 0 < p := by omega
  have hnp : n < p := by omega
  have hcp : c < p := by omega
  have hcK : c + 1 ≤ 5*n := by omega
  have hcn : c < n := by omega
  have hcp' : c + 1 ≠ p := by omega
  have hC := Ccl_eq_succ p (5*n) hcK
  have hq : (5*n - (c+1))/p ≤ 2 := by
    apply Nat.lt_succ_iff.mp
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    omega
  have hdm := Nat.div_mul_le_self (5*n - (c+1)) p
  have hind : (0:ℚ) ≤ (if c < 5*n - 2*p then (1:ℚ) else 0) := by split_ifs <;> norm_num
  generalize (5*n - (c+1))/p = q at hC hq hdm
  have hbig : ∀ k : ℕ, min (15 * (n:ℚ) + 1 + 2 * (k:ℚ)) 0 = 0 := fun k => by
    apply min_eq_right; positivity
  unfold Scl
  obtain rfl | rfl | rfl : q = 0 ∨ q = 1 ∨ q = 2 := by omega
  · have hj0 : jn p (5*n) c 0 = c + 1 := by rw [jn_eq p (5*n) hC]; simp
    rw [hC]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hj0, wv_cancelled hc, hbig]
    linarith
  · have hj1 : jn p (5*n) c 1 = c + 1 := by rw [jn_eq p (5*n) hC]; simp
    rw [hC]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [wv_jn hp hnp hcp hC (t := 0) (by norm_num) (by omega), betaWt_class hcp, hj1,
      wv_cancelled hc, hbig]
    simp only [ite_eq_left hcn, hcp', ite_false]
    norm_num
    linarith
  · have hj2 : jn p (5*n) c 2 = c + 1 := by rw [jn_eq p (5*n) hC]; simp
    have hlt : c < 5*n - 2*p := by omega
    rw [hC]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [wv_jn hp hnp hcp hC (t := 0) (by norm_num) (by omega),
      wv_jn hp hnp hcp hC (t := 1) (by norm_num) (by omega), betaWt_class hcp,
      betaWt_class hcp, hj2, wv_cancelled hc, hbig]
    simp only [ite_eq_left hcn, hcp', ite_false, ite_eq_left hlt]
    norm_num

/-- Class `n < ρ < p`: `T ≤ 1` nodes of weight `-T - 3` and the node `ρ < p` of weight `-T`. -/
lemma Scl_high (h73 : 7 * n < 3 * p) (hp5 : p ≤ 5 * n) (hc1 : n < c + 1) (hc2 : c + 1 < p) :
    -4 * (if c < 5*n - p then (1:ℚ) else 0) ≤ Scl n p c := by
  have hp : 0 < p := by omega
  have hnp : n < p := by omega
  have hcp : c < p := by omega
  have hcK : c + 1 ≤ 5*n := by omega
  have hcn : ¬ c < n := by omega
  have hcp' : c + 1 ≠ p := by omega
  have hC := Ccl_eq_succ p (5*n) hcK
  have hq : (5*n - (c+1))/p ≤ 1 := by
    apply Nat.lt_succ_iff.mp
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    omega
  have hdm := Nat.div_mul_le_self (5*n - (c+1)) p
  have hind : (0:ℚ) ≤ (if c < 5*n - p then (1:ℚ) else 0) := by split_ifs <;> norm_num
  generalize (5*n - (c+1))/p = q at hC hq hdm
  unfold Scl
  obtain rfl | rfl : q = 0 ∨ q = 1 := by omega
  · rw [hC]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [wv_jn hp hnp hcp hC (t := 0) (by norm_num) (by omega), betaWt_class hcp]
    simp only [ite_eq_right hcn, hc2, and_true, ite_eq_left]
    norm_num
    split_ifs <;> norm_num
  · have hlt : c < 5*n - p := by omega
    rw [hC]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [wv_jn hp hnp hcp hC (t := 0) (by norm_num) (by omega),
      wv_jn hp hnp hcp hC (t := 1) (by norm_num) (by omega), betaWt_class hcp,
      betaWt_class hcp]
    simp only [ite_eq_right hcn, ite_eq_left hlt, hcp', ite_false, hc2, and_true]
    norm_num

end ClassCosts

end
end Zeta32.Outer

end

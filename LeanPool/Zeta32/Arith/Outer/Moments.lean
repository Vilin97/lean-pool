/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Family
public import LeanPool.Zeta32.Arith.Local.Val

/-! the proof notes section 4, Lemma 5: the p-adic size of the moments `U_r(t^e) = (e+1)B_e +
2rB_{e+1}`
(`v_p ≥ -1` always, `p`-integral for `e ≤ p-3`, von Staudt-Clausen), and of the pole constants
`H_j^{(e)}` and `β_j` (`v_p(β_j) ≥ 0` for `j < p`, `≥ -2` for `p ∣ j`, `≥ -3` otherwise, `j <
p²`). -/

public section

open Zeta32.Arith.Local

open Polynomial
open scoped BigOperators
namespace Zeta32.Outer
noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
lemma VG_of_not_dvd_den {r : ℚ} (hr : ¬ p ∣ r.den) : VG p r 0 := by
  right
  unfold padicValRat
  rw [padicValNat.eq_zero_of_not_dvd hr]
  simp

lemma VG_inv_prime {q : ℕ} (hq : q.Prime) : VG p (1 / (q:ℚ)) (if q = p then -1 else 0) := by
  have hq0 : (q:ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  right
  rw [one_div, padicValRat.inv]
  split_ifs with h
  · subst h
    rw [padicValRat.self hq.one_lt]
    norm_num
  · have hnd : ¬ p ∣ q := fun hd => h ((Nat.prime_dvd_prime_iff_eq hp.out hq).mp hd).symm
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd]
    norm_num

/-- von Staudt-Clausen, in `VG` form: `B_{2k} = z - Σ_{(q-1) ∣ 2k} 1/q`. -/
lemma bernoulli_even_VG (k : ℕ) :
    VG p (bernoulli (2*k)) (if (p - 1) ∣ 2*k then -1 else 0) := by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  have he : bernoulli (2*k) = (z:ℚ) -
      ∑ q ∈ Finset.range (2 * k + 2) with q.Prime ∧ q - 1 ∣ 2 * k, (1:ℚ) / q := by
    rw [hz]; ring
  rw [he]
  apply (VG.intCast (p := p) z |>.mono (by split_ifs <;> norm_num)).sub
  apply VG.sum
  intro q hq
  obtain ⟨-, hqp, hqd⟩ := by simpa using hq
  refine (VG_inv_prime (p := p) hqp).mono ?_
  by_cases h1 : (p - 1) ∣ 2*k
  · rw [ite_eq_left h1]; split_ifs <;> norm_num
  · rw [ite_eq_right h1]
    have h2 : q ≠ p := fun h => h1 (h ▸ hqd)
    rw [ite_eq_right h2]

lemma bernoulli'_VG (m : ℕ) : VG p (bernoulli' m) (-1) := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | hodd
  · rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0; change m = 0 at hk; subst hk; rw [bernoulli'_zero]; exact VG.one.mono (by norm_num)
    · have hm : m = 2 * k := by omega
      rw [hm, ← bernoulli_eq_bernoulli'_of_ne_one (by omega)]
      exact (bernoulli_even_VG k).mono (by split_ifs <;> norm_num)
  · rcases Nat.lt_or_ge 1 m with h1 | h1
    · rw [bernoulli'_eq_zero_of_odd hodd h1]; exact VG.zero _
    · have hm : m = 1 := by obtain ⟨k, hk⟩ := hodd; omega
      subst hm
      rw [bernoulli'_one]
      have h2 := VG_inv_prime (p := p) Nat.prime_two
      push_cast at h2
      exact h2.mono (by split_ifs <;> norm_num)

lemma bernoulli'_VG_small (hp2 : p ≠ 2) {m : ℕ} (hm : m < p - 1) : VG p (bernoulli' m) 0 := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | hodd
  · rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0; change m = 0 at hk; subst hk; rw [bernoulli'_zero]; exact VG.one
    · have hm2 : m = 2 * k := by omega
      rw [hm2, ← bernoulli_eq_bernoulli'_of_ne_one (by omega)]
      have hnd : ¬ (p - 1) ∣ 2 * k := fun hd => by
        have := Nat.le_of_dvd (by omega) hd
        omega
      simpa [hnd] using bernoulli_even_VG (p := p) k
  · rcases Nat.lt_or_ge 1 m with h1 | h1
    · rw [bernoulli'_eq_zero_of_odd hodd h1]; exact VG.zero _
    · have hm : m = 1 := by obtain ⟨k, hk⟩ := hodd; omega
      subst hm
      rw [bernoulli'_one]
      have h2 := VG_inv_prime (p := p) Nat.prime_two
      push_cast at h2
      simpa [show (2:ℕ) ≠ p from fun h => hp2 h.symm] using h2

omit hp in
lemma two_VG : VG p (2:ℚ) 0 := by exact_mod_cast VG.natCast (p := p) 2

lemma moment_VG {r : ℚ} (hr : VG p r 0) (e : ℕ) : VG p (moment r e) (-1) := by
  unfold moment
  have h1 := (VG.natCast (p := p) (e+1)).mul (bernoulli'_VG (p := p) e)
  have h2 := ((two_VG (p := p)).mul hr).mul (bernoulli'_VG (p := p) (e+1))
  simp only [zero_add] at h1 h2
  exact h1.add h2

lemma moment_VG_small (hp2 : p ≠ 2) {r : ℚ} (hr : VG p r 0) {e : ℕ} (he : e + 3 ≤ p) :
    VG p (moment r e) 0 := by
  unfold moment
  have h1 := (VG.natCast (p := p) (e+1)).mul (bernoulli'_VG_small (p := p) hp2 (m := e) (by omega))
  have h2 := ((two_VG (p := p)).mul hr).mul
    (bernoulli'_VG_small (p := p) hp2 (m := e+1) (by omega))
  simp only [add_zero] at h1 h2
  exact h1.add h2

/-! ## Harmonic sums and the pole constants -/

lemma inv_pow_VG {a e : ℕ} (ha : 1 ≤ a) (hap : a < p ^ 2) :
    VG p (1 / (a:ℚ)^e) (-(e:ℚ)) := by
  have hlog : Nat.log p a ≤ 1 := Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) hap)
  have h := (VG.inv_nat (p := p) ha (le_refl a)).pow e
  rw [one_div, ← inv_pow]
  refine h.mono ?_
  have : ((Nat.log p a : ℕ) : ℚ) ≤ 1 := by exact_mod_cast hlog
  have he : (0:ℚ) ≤ e := Nat.cast_nonneg e
  nlinarith

lemma inv_pow_VG_small {a e : ℕ} (ha : 1 ≤ a) (hap : a < p) :
    VG p (1 / (a:ℚ)^e) 0 := by
  have hlog : Nat.log p a = 0 := Nat.log_of_lt hap
  have h := (VG.inv_nat (p := p) ha (le_refl a)).pow e
  rw [one_div, ← inv_pow]
  simpa [hlog] using h

lemma H_VG {e j : ℕ} (hj : j < p ^ 2) : VG p (H e j) (-(e:ℚ)) := by
  unfold H
  apply VG.sum
  intro a ha
  obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
  exact inv_pow_VG ha1 (by omega)

lemma H_VG_small {e j : ℕ} (hj : j < p) : VG p (H e j) 0 := by
  unfold H
  apply VG.sum
  intro a ha
  obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
  exact inv_pow_VG_small ha1 (by omega)

/-- The weight of the constant `min(v_p(2j), v_p(β_j))` in the proof notes, Lemma 5. -/
@[expose]
def betaWt (p j : ℕ) : ℚ := if j < p then 0 else if p ∣ j then -2 else -3

lemma nat_VG_dvd (j : ℕ) (hj : 0 < j) : VG p (j:ℚ) (if p ∣ j then 1 else 0) := by
  split_ifs with h
  · right
    rw [padicValRat.of_nat]
    exact_mod_cast one_le_padicValNat_of_dvd (by omega) h
  · exact VG.natCast j

lemma beta_VG {r : ℚ} (hr : VG p r 0) {j : ℕ} (hj : j < p ^ 2) :
    VG p (beta r j) (betaWt p j) := by
  unfold beta betaWt
  have h2r : VG p (2*r) 0 := by simpa using (two_VG (p := p)).mul hr
  split_ifs with hjp hpj
  · have h3 := H_VG_small (p := p) (e := 3) hjp
    have h2 := H_VG_small (p := p) (e := 2) hjp
    have t2 : VG p (2 * (j:ℚ) * H 3 j) 0 := by
      simpa using ((two_VG (p := p)).mul (VG.natCast j)).mul h3
    have t3 : VG p (2 * r * (j:ℚ) * H 2 j) 0 := by
      simpa using (h2r.mul (VG.natCast j)).mul h2
    exact (h2r.sub t2).add t3
  · have hj0 : 0 < j := Nat.pos_of_ne_zero (fun h => by subst h; exact hjp hp.out.pos)
    have hjv : VG p (j:ℚ) 1 := by simpa [hpj] using nat_VG_dvd (p := p) j hj0
    have h3 := H_VG (p := p) (e := 3) hj
    have h2 := H_VG (p := p) (e := 2) hj
    have t2 : VG p (2 * (j:ℚ) * H 3 j) (-2) := by
      have := ((two_VG (p := p)).mul hjv).mul h3
      exact this.mono (by norm_num)
    have t3 : VG p (2 * r * (j:ℚ) * H 2 j) (-2) := by
      have := (h2r.mul hjv).mul h2
      exact this.mono (by norm_num)
    exact ((h2r.mono (by norm_num)).sub t2).add t3
  · have h3 := H_VG (p := p) (e := 3) hj
    have h2 := H_VG (p := p) (e := 2) hj
    have t2 : VG p (2 * (j:ℚ) * H 3 j) (-3) := by
      have := ((two_VG (p := p)).mul (VG.natCast j)).mul h3
      exact this.mono (by norm_num)
    have t3 : VG p (2 * r * (j:ℚ) * H 2 j) (-3) := by
      have := (h2r.mul (VG.natCast j)).mul h2
      exact this.mono (by norm_num)
    exact ((h2r.mono (by norm_num)).sub t2).add t3

/-- `GV` of the linear pole value `2jX + β_j`. -/
lemma poleValue_GV {r : ℚ} (hr : VG p r 0) {j : ℕ} (hj0 : 0 < j) (hj : j < p ^ 2) :
    GV p (C (2 * (j:ℚ)) * X + C (beta r j)) (betaWt p j) := by
  have hb := beta_VG (p := p) hr hj
  have h2j : VG p (2 * (j:ℚ)) (betaWt p j) := by
    have := (two_VG (p := p)).mul (nat_VG_dvd (p := p) j hj0)
    refine this.mono ?_
    unfold betaWt
    split_ifs <;> norm_num
  have hX : GV p (C (2 * (j:ℚ)) * X) (betaWt p j) := by
    simpa using (GV.C h2j).mul (GV.X (p := p))
  exact hX.add (GV.C hb)

end
end Zeta32.Outer

end

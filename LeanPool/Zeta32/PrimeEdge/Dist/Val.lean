/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.PrimeEdge.Dist.Basic

/-! `p`-adic estimates for S2b-1.

* `dist_VG_bernoulli_B` : `v_p(B'_k) ≥ -1` (von Staudt–Clausen);
* `dist_VG_locMoment` : `v_p(V(u^e)) ≥ -1`, and `V(1) = 2 s`;
* `GV_divByMonic_mprod` : division by `∏ (u + m)` keeps the Gauss valuation;
* `VG_locValue` : Lemma 3 type bound `v_p(locValue s R M) ≥ c - 1` if `GV R c`, `M ⊆ [0, p)`;
* `VG_locPoly_tate` : `v_p(locPoly s F) ≥ 0` if `v_p(F_e) ≥ e` and `v_p(s) ≥ 1`;
* `H_split` : `H_e(j) = p^{-e} H_e(⌊j/p⌋) + ∑_{a ≤ j, p ∤ a} a^{-e}`. -/

public section

open Polynomial
open scoped BigOperators
namespace Zeta32.PrimeEdge

open Zeta32.Arith.Local

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

lemma VG_inv_prime {q : ℕ} (hq : q.Prime) : VG p ((q : ℚ)⁻¹) (-1) := by
  apply VG.inv
  have h : ¬ ((p : ℤ) ^ 2 ∣ (q : ℤ)) := by
    intro h
    have h' : p ^ 2 ∣ q := by exact_mod_cast h
    have hp1 := hp.out.one_lt
    rcases hq.eq_one_or_self_of_dvd _ h' with h1 | h1
    · have : p ^ 2 > 1 := Nat.one_lt_pow two_ne_zero hp1
      omega
    · have hpq : p ∣ q := (dvd_pow_self p two_ne_zero).trans h'
      rcases hq.eq_one_or_self_of_dvd _ hpq with h2 | h2
      · omega
      · rw [← h2] at h1
        nlinarith
  have h3 : padicValRat p ((q : ℤ) : ℚ) ≤ 1 := padicValRat_int_le_one h
  rw [Int.cast_natCast] at h3
  exact_mod_cast h3

/-- **von Staudt–Clausen**: `v_p(B'_k) ≥ -1`. -/
lemma dist_VG_bernoulli_B (k : ℕ) : VG p (bernoulli' k) (-1) := by
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | hodd
  · rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; change k = 0 at hm; subst hm
      rw [bernoulli'_zero]; exact (VG.one (p := p)).mono (by norm_num)
    · have hk : k = 2 * m := by omega
      rw [hk, ← bernoulli_eq_bernoulli'_of_ne_one (by omega)]
      obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen (k := m)
      have heq : bernoulli (2 * m) = (z : ℚ) - ∑ q ∈ Finset.range (2 * m + 2) with
          q.Prime ∧ (q - 1) ∣ 2 * m, (1 : ℚ) / q := by rw [hz]; ring
      rw [heq]
      refine VG.sub ((VG.intCast (p := p) z).mono (by norm_num)) (VG.sum _ fun q hq => ?_)
      rw [Finset.mem_filter] at hq
      rw [one_div]; exact VG_inv_prime hq.2.1
  · rcases Nat.lt_or_ge 1 k with h1 | h1
    · rw [bernoulli'_eq_zero_of_odd hodd h1]; exact VG.zero _
    · have : k = 1 := by obtain ⟨j, hj⟩ := hodd; omega
      subst this
      rw [bernoulli'_one]
      have := VG_inv_prime (p := p) Nat.prime_two
      simpa [one_div] using this

lemma dist_VG_locMoment {s : ℚ} (hs : VG p s 0) (e : ℕ) : VG p (locMoment s e) (-1) := by
  unfold locMoment
  refine VG.add ?_ ?_
  · have := (VG.natCast (p := p) e).mul (dist_VG_bernoulli_B (p := p) (e - 1))
    simpa using this
  · have := ((VG.natCast (p := p) 2).mul hs).mul (dist_VG_bernoulli_B (p := p) e)
    simpa using this

lemma locMoment_zero (s : ℚ) : locMoment s 0 = 2 * s := by
  simp [locMoment]

lemma GV_divByMonic_X_add_C {R : ℚ[X]} {c : ℚ} (hR : GV p R c) (a : ℕ) :
    GV p (R /ₘ (X + C (a : ℚ))) c := fun n => by
  rw [show X + C (a : ℚ) = X - C (-(a : ℚ)) by rw [C_neg, sub_neg_eq_add],
    coeff_divByMonic_X_sub_C]
  refine VG.sum _ fun i _ => ?_
  have := ((VG.natCast (p := p) a).neg.pow (i - (n + 1))).mul (hR i)
  simpa using this

lemma divByMonic_X_add_C_mul (R : ℚ[X]) (a : ℚ) {g : ℚ[X]} (hg : g.Monic) :
    R /ₘ ((X + C a) * g) = (R /ₘ (X + C a)) /ₘ g := by
  by_cases hg1 : g = 1
  · subst hg1; simp
  set f := X + C a with hf
  have hfm : f.Monic := monic_X_add_C a
  have h1 := modByMonic_add_div R f
  have h2 := modByMonic_add_div (R /ₘ f) g
  refine (div_modByMonic_unique ((R /ₘ f) /ₘ g) (f * ((R /ₘ f) %ₘ g) + R %ₘ f)
    (hfm.mul hg) ⟨?_, ?_⟩).1
  · linear_combination f * h2 + h1
  · have hr1 : R %ₘ f = C (R.eval (-a)) := by
      rw [hf, show X + C a = X - C (-a) by rw [C_neg, sub_neg_eq_add],
        modByMonic_X_sub_C_eq_C_eval]
    rw [hr1]
    refine degree_lt_degree ?_
    rw [natDegree_add_C, hfm.natDegree_mul hg, natDegree_X_add_C]
    refine lt_of_le_of_lt natDegree_mul_le ?_
    rw [natDegree_X_add_C]
    have := natDegree_modByMonic_lt (R /ₘ f) hg hg1
    omega

lemma GV_divByMonic_mprod {R : ℚ[X]} {c : ℚ} (hR : GV p R c) (M : Finset ℕ) :
    GV p (R /ₘ mprod M) c := by
  classical
  induction M using Finset.induction_on generalizing R with
  | empty => simpa [mprod] using hR
  | insert a M ha ih =>
    have hins : mprod (insert a M) = (X + C (a : ℚ)) * mprod M := Finset.prod_insert ha
    rw [hins, divByMonic_X_add_C_mul _ _ (mprod_monic M)]
    exact ih (GV_divByMonic_X_add_C hR a)

lemma VG_eval_GV {R : ℚ[X]} {c z : ℚ} (hR : GV p R c) (hz : VG p z 0) : VG p (R.eval z) c := by
  rw [eval_eq_sum, Polynomial.sum]
  refine VG.sum _ fun n _ => ?_
  have := (hR n).mul (hz.pow n)
  simpa using this

lemma VG_locPoly {s : ℚ} (hs : VG p s 0) {Q : ℚ[X]} {c : ℚ} (hQ : GV p Q c) :
    VG p (locPoly s Q) (c - 1) := by
  unfold locPoly
  rw [Polynomial.sum]
  refine VG.sum _ fun e _ => ?_
  have := (hQ e).mul (dist_VG_locMoment hs e)
  simpa [sub_eq_add_neg] using this

lemma int_not_dvd_of_lt {m m' : ℕ} (hm : m < p) (hm' : m' < p) (hne : m' ≠ m) :
    ¬ (p : ℤ) ∣ ((m' : ℤ) - m) := by
  intro h
  have h1 : ((m' : ℤ) : ZMod p) = ((m : ℤ) : ZMod p) := (zmod_eq_iff_dvd (p := p)).mpr h
  have h2 : (m' : ZMod p) = (m : ZMod p) := by exact_mod_cast h1
  rw [ZMod.natCast_eq_natCast_iff'] at h2
  rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hm'] at h2
  exact hne h2

/-- Near-pole denominators are units. -/
lemma VG_denom_inv (M : Finset ℕ) (hM : ∀ m ∈ M, m < p) {m : ℕ} (hm : m ∈ M) :
    VG p (∏ m' ∈ M.erase m, ((m' : ℚ) - m))⁻¹ 0 := by
  have hne : ∀ m' ∈ M.erase m, ((m' : ℚ) - m) ≠ 0 := fun m' hm' =>
    sub_ne_zero.mpr (by exact_mod_cast (Finset.mem_erase.mp hm').1)
  refine (VG.inv (r := 0)  ?_).mono (by norm_num)
  rw [padicValRat_finset_prod _ _ hne]
  have : ∀ m' ∈ M.erase m, padicValRat p ((m' : ℚ) - m) = 0 := by
    intro m' hm'
    rw [Finset.mem_erase] at hm'
    rw [show ((m' : ℚ) - m) = (((m' : ℤ) - m : ℤ) : ℚ) by push_cast; ring]
    exact padicValRat_int_eq_zero (int_not_dvd_of_lt (hM m hm) (hM m' hm'.2) hm'.1)
  rw [Finset.sum_eq_zero this]
  simp

lemma VG_inv_pow_of_not_dvd {a : ℕ} (ha : ¬ p ∣ a) (e : ℕ) : VG p (1 / (a : ℚ) ^ e) 0 := by
  have ha0 : a ≠ 0 := fun h => ha (h ▸ dvd_zero p)
  rw [one_div]
  refine (VG.inv (r := 0)  ?_).mono (by norm_num)
  have h : padicValRat p ((a : ℚ) ^ e) = 0 := by
    rw [padicValRat.pow, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd ha]
    simp
  rw [h]; simp

lemma VG_H {m : ℕ} (hm : m < p) (e : ℕ) : VG p (Zeta32.H e m) 0 := by
  unfold Zeta32.H
  refine VG.sum _ fun a ha => VG_inv_pow_of_not_dvd ?_ e
  rw [Finset.mem_Icc] at ha
  exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)

lemma dist_VG_locPole {s : ℚ} (hs : VG p s 0) {m : ℕ} (hm : m < p) : VG p (locPole s m) 0 := by
  unfold locPole
  refine VG.sub ?_ ?_
  · have := (VG.natCast (p := p) 2).mul (VG_H (p := p) hm 3)
    simpa using this
  · have := ((VG.natCast (p := p) 2).mul hs).mul (VG_H (p := p) hm 2)
    simpa using this

/-- **Local integrality (Lemma 3 type)**: `v_p(locValue s R M) ≥ c - 1`. -/
theorem VG_locValue {s : ℚ} (hs : VG p s 0) (M : Finset ℕ) (hM : ∀ m ∈ M, m < p)
    {R : ℚ[X]} {c : ℚ} (hR : GV p R c) : VG p (locValue s R M) (c - 1) := by
  unfold locValue
  refine VG.add (VG_locPoly hs (GV_divByMonic_mprod hR M)) (VG.sum _ fun m hm => ?_)
  have h1 := VG_eval_GV hR (z := -(m : ℚ)) (VG.natCast (p := p) m).neg
  have h2 := VG_denom_inv M hM hm
  have h3 := dist_VG_locPole hs (hM m hm)
  have := (h1.mul h2).mul h3
  rw [div_eq_mul_inv]
  exact this.mono (by linarith)

/-- `v_p(locPoly s F) ≥ 0` if `v_p(F_e) ≥ e` and `v_p(s) ≥ 1`. -/
theorem VG_locPoly_tate {s : ℚ} (hs : VG p s 1) {F : ℚ[X]} (hF : ∀ e, VG p (F.coeff e) e) :
    VG p (locPoly s F) 0 := by
  unfold locPoly
  rw [Polynomial.sum]
  refine VG.sum _ fun e _ => ?_
  rcases Nat.eq_zero_or_pos e with h0 | hpos
  · subst h0
    rw [locMoment_zero]
    have := (hF 0).mul ((VG.natCast (p := p) 2).mul hs)
    simpa using this.mono (by norm_num)
  · have := (hF e).mul (dist_VG_locMoment (hs.mono (by norm_num)) e)
    refine this.mono ?_
    have : (1 : ℚ) ≤ e := by exact_mod_cast hpos
    linarith

/-- `H_e(j) = p^{-e} H_e(⌊j/p⌋) + ∑_{a ≤ j, p ∤ a} a^{-e}`. -/
lemma H_split (e j : ℕ) :
    Zeta32.H e j = ((p : ℚ) ^ e)⁻¹ * Zeta32.H e (j / p) +
      ∑ a ∈ (Finset.Icc 1 j).filter (fun a => ¬ p ∣ a), 1 / (a : ℚ) ^ e := by
  have hp0 : 0 < p := hp.out.pos
  unfold Zeta32.H
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 j) (fun a => p ∣ a)]
  congr 1
  have himg : (Finset.Icc 1 j).filter (fun a => p ∣ a) =
      (Finset.Icc 1 (j / p)).image (fun a' => p * a') := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨a', rfl⟩⟩
      refine ⟨a', ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos a' with h | h
        · subst h; simp at h1
        · exact h
      · exact (Nat.le_div_iff_mul_le hp0).mpr (by rw [mul_comm]; exact h2)
    · rintro ⟨a', ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_right p a'⟩
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp0.ne' (by omega))
      · calc p * a' ≤ p * (j / p) := Nat.mul_le_mul_left _ h2
          _ ≤ j := Nat.mul_div_le j p
  rw [himg, Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hp0 h), Finset.mul_sum]
  refine Finset.sum_congr rfl fun a' _ => ?_
  push_cast
  rw [mul_pow]
  field_simp

lemma VG_sum_not_dvd (e j : ℕ) :
    VG p (∑ a ∈ (Finset.Icc 1 j).filter (fun a => ¬ p ∣ a), 1 / (a : ℚ) ^ e) 0 :=
  VG.sum _ fun _ ha => VG_inv_pow_of_not_dvd (Finset.mem_filter.mp ha).2 e

/-- **Near-pole cancellation**: `V(1/(t+j)) - p^{-3} V^loc(1/(u + ⌊j/p⌋))` is integral. -/
theorem VG_near_cancel {r : ℚ} (hr : VG p r 0) (j : ℕ) :
    VG p (locPole r j - ((p : ℚ) ^ 3)⁻¹ * locPole (r * p) (j / p)) 0 := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have key : locPole r j - ((p : ℚ) ^ 3)⁻¹ * locPole (r * p) (j / p) =
      2 * (∑ a ∈ (Finset.Icc 1 j).filter (fun a => ¬ p ∣ a), 1 / (a : ℚ) ^ 3) -
        2 * r * (∑ a ∈ (Finset.Icc 1 j).filter (fun a => ¬ p ∣ a), 1 / (a : ℚ) ^ 2) := by
    unfold locPole
    rw [H_split (p := p) 3 j, H_split (p := p) 2 j]
    field_simp
    ring
  rw [key]
  refine VG.sub ?_ ?_
  · have := (VG.natCast (p := p) 2).mul (VG_sum_not_dvd (p := p) 3 j)
    simpa using this
  · have := ((VG.natCast (p := p) 2).mul hr).mul (VG_sum_not_dvd (p := p) 2 j)
    simpa using this

end

end Zeta32.PrimeEdge

end

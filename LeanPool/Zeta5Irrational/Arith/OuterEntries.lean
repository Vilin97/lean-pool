/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Arith.OuterBasis
import LeanPool.Zeta5Irrational.Arith.IntPoly
import LeanPool.Zeta5Irrational.Arith.OuterEntry
import LeanPool.Zeta5Irrational.Arith.PoleVal
import Mathlib.Data.Rat.Star
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # Outer range: entry bounds

Helper lemmas (memberships, root counts, zero-class valuations).
-/

public section

open Finset Polynomial

namespace Zeta5Irrational

variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}

/-- The entry roots `6·[1..N] + rows`. -/
@[expose]
def entryO (hm : 2 * m + 1 = p) (n : ℕ) (cs : Fin (m + 1)) (is : ℕ) (ct : Fin (m + 1)) (it : ℕ) :
    Multiset ℤ :=
  6 • ((Icc 1 (3 * n)).val.map fun j : ℕ => (j : ℤ)) + rootsO hm n cs is + rootsO hm n ct it

variable (hm : 2 * m + 1 = p) (n : ℕ)

lemma mem_entryO_small {cs ct : Fin (m + 1)} {is it : ℕ} {k : ℕ} (hk : k ∈ Icc 1 (3 * n)) :
    (k : ℤ) ∈ entryO hm n cs is ct it := by
  unfold entryO
  refine Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inl ?_)))
  rw [Multiset.mem_nsmul_of_ne_zero (by norm_num)]
  exact Multiset.mem_map.mpr ⟨k, hk, rfl⟩

lemma mem_rootsO_other {c : Fin (m + 1)} {i j : ℕ} (hj : j ∈ tailO n) (hc : jc hm j ≠ c) :
    (j : ℤ) ∈ rootsO hm n c i := by
  unfold rootsO
  refine Multiset.mem_add.mpr (Or.inl (Multiset.mem_map.mpr ⟨j, ?_, rfl⟩))
  exact Finset.mem_val.mpr (Finset.mem_filter.mpr ⟨hj, hc⟩)

lemma mem_rootsO_big {c : Fin (m + 1)} {i j : ℕ} (hi : nbC hm n c ≤ i) (hj : j ∈ bigC hm n c) :
    (j : ℤ) ∈ rootsO hm n c i := by
  unfold rootsO
  rw [ite_eq_right (by omega)]
  refine Multiset.mem_add.mpr (Or.inr (Multiset.mem_add.mpr (Or.inl ?_)))
  exact Multiset.mem_map.mpr ⟨j, Finset.mem_val.mpr hj, rfl⟩

lemma mem_entryO_left {cs ct : Fin (m + 1)} {is it : ℕ} {γ : ℤ} (h : γ ∈ rootsO hm n cs is) :
    γ ∈ entryO hm n cs is ct it := by
  unfold entryO
  exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr h)))

lemma mem_entryO_right {cs ct : Fin (m + 1)} {is it : ℕ} {γ : ℤ} (h : γ ∈ rootsO hm n ct it) :
    γ ∈ entryO hm n cs is ct it := by
  unfold entryO
  exact Multiset.mem_add.mpr (Or.inr h)

/-- Count of roots in the class of `c` in a row of class `c`. -/
lemma count_rootsO (c : Fin (m + 1)) (i : ℕ) (x : ZMod p)
    (hx : x ^ 2 = ((((c : ℕ) : ℤ) : ZMod p)) ^ 2) :
    i ≤ ((rootsO hm n c i).filter fun γ : ℤ => ((γ : ZMod p)) ^ 2 = x ^ 2).card := by
  have hcx : ((((c : ℕ) : ℤ) : ZMod p)) ^ 2 = x ^ 2 := hx.symm
  unfold rootsO
  rw [Multiset.filter_add, Multiset.card_add]
  split_ifs with h
  · rw [card_filter_replicate, ite_eq_left hcx]; omega
  · rw [Multiset.filter_add, Multiset.card_add, card_filter_replicate, ite_eq_left hcx]
    have hbig :
      ((bigC hm n c).val.map fun j : ℕ => (j : ℤ)).filter
          (fun γ : ℤ => ((γ : ZMod p)) ^ 2 = x ^ 2) =
        (bigC hm n c).val.map fun j : ℕ => (j : ℤ) := by
      refine Multiset.filter_eq_self.mpr fun γ hγ => ?_
      obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hγ
      have hj' : j ∈ bigC hm n c := Finset.mem_val.mp hj
      have hjc : jc hm j = c := (Finset.mem_filter.mp (Finset.mem_filter.mp hj').1).2
      rw [hx, sq_jc hm j, hjc]
    rw [hbig, Multiset.card_map, Finset.card_val]
    have : nbC hm n c = (bigC hm n c).card := rfl
    omega

/-- The valuation of `∏ (γ² - j²)` for `p ∣ j`: two per root divisible by `p`. -/
lemma VG_prod_sq_sub_zero (M : Multiset ℤ) {j : ℤ} (hj : (p : ℤ) ∣ j) :
    VG p ((M.map fun γ : ℤ => (γ : ℚ) ^ 2 - (j : ℚ) ^ 2).prod)
      (2 * (M.filter fun γ : ℤ => (p : ℤ) ∣ γ).card) := by
  induction M using Multiset.induction_on with
  | empty => right; simp
  | cons a M ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.filter_cons]
    split_ifs with h
    · rw [Multiset.card_add, Multiset.card_singleton]
      have h1 : VG p ((a : ℚ) ^ 2 - (j : ℚ) ^ 2) 2 := by
        rw [show (a : ℚ) ^ 2 - (j : ℚ) ^ 2 = ((a - j : ℤ) : ℚ) * ((a + j : ℤ) : ℚ) by
            push_cast;
            ring]
        have := (VG_int_one (p := p) (dvd_sub h hj)).mul (VG_int_one (p := p) (dvd_add h hj))
        simpa [one_add_one_eq_two] using this
      convert h1.mul ih using 1; push_cast; ring
    · rw [zero_add]
      have h1 : VG p ((a : ℚ) ^ 2 - (j : ℚ) ^ 2) 0 := by
        have := VG.intCast (p := p) (a ^ 2 - j ^ 2); push_cast at this; exact this
      simpa using h1.mul ih

/-- Denominator for `p ∣ j`: at most two per other multiple of `p`. -/
lemma padicValRat_den_zero_le {K j : ℕ} (hj : j ∈ Icc 1 K) (hK : 2 * K < p ^ 2)
    (hj0 : (p : ℤ) ∣ (j : ℤ)) :
    (padicValRat p (∏ i ∈ (Icc 1 K).erase j, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2)) : ℚ) ≤
      2 * (((Icc 1 K).erase j).filter fun i : ℕ => (p : ℤ) ∣ (i : ℤ)).card := by
  have hne : ∀ i ∈ (Icc 1 K).erase j, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) ≠ 0 := by
    intro i hi
    have hij := (Finset.mem_erase.mp hi).1
    have : (i : ℚ) ≠ j := by exact_mod_cast hij
    intro h
    have h2 : ((i : ℚ) - j) * ((i : ℚ) + j) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact this (by linarith)
    · have : (0 : ℚ) ≤ i := by positivity
      have : (1 : ℚ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
      linarith
  rw [padicValRat_finset_prod _ _ hne]
  push_cast
  have hrhs :
    (2 * ((((Icc 1 K).erase j).filter fun i : ℕ => (p : ℤ) ∣ (i : ℤ)).card : ℚ)) =
      ∑ i ∈ (Icc 1 K).erase j, (if (p : ℤ) ∣ (i : ℤ) then (2 : ℚ) else 0) := by
    rw [Finset.card_filter]; push_cast; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> norm_num
  rw [hrhs]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' := Finset.mem_erase.mp hi
  have hiK := (Finset.mem_Icc.mp hi'.2)
  have hjK := (Finset.mem_Icc.mp hj)
  rw [show ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) = (((i - j) * (i + j) : ℤ) : ℚ) by push_cast; ring]
  have hz : ((i : ℤ) - j) * ((i : ℤ) + j) ≠ 0 := by
    have := hne i hi
    intro h; apply this;
    rw [show ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) = (((i - j) * (i + j) : ℤ) : ℚ) by
    push_cast; ring, h];
    simp
  have hz1 := (mul_ne_zero_iff.mp hz).1
  have hz2 := (mul_ne_zero_iff.mp hz).2
  split_ifs with hc
  · rw [padicValRat.of_int, padicValInt.mul hz1 hz2]
    have hle : ∀ z : ℤ, z ≠ 0 → |z| ≤ 2 * K → padicValInt p z ≤ 1 := by
      intro z hz0 hzK
      have :=
        padicValRat_int_le_one (p := p) (z := z)
          (fun hd => by
            have h1 := Int.natAbs_dvd_natAbs.mpr hd
            rw [Int.natAbs_pow, Int.natAbs_natCast] at h1
            have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hz0) h1
            have h3 : (z.natAbs : ℤ) ≤ 2 * K := by rw [Int.natCast_natAbs]; exact hzK
            omega)
      rw [padicValRat.of_int] at this; exact_mod_cast this
    have hb1 := hle _ hz1 (by rw [abs_le]; constructor <;> omega)
    have hb2 := hle _ hz2 (by rw [abs_le]; constructor <;> omega)
    push_cast
    have : ((padicValInt p ((i : ℤ) - j) : ℕ) : ℚ) ≤ 1 := by exact_mod_cast hb1
    have : ((padicValInt p ((i : ℤ) + j) : ℕ) : ℚ) ≤ 1 := by exact_mod_cast hb2
    linarith
  · have hnd : ¬(p : ℤ) ∣ ((i : ℤ) - j) * ((i : ℤ) + j) := by
      intro hd
      rcases Int.Prime.dvd_mul' hp.out hd with h1 | h1
      · exact hc (by have := dvd_add h1 hj0; simpa using this)
      · exact hc (by have := dvd_sub h1 hj0; simpa using this)
    rw [padicValRat_int_eq_zero hnd]; simp

/-- Residue bound for a nonzero class. -/
lemma VG_res_class (hp3 : 3 ≤ p) {K : ℕ} (hK : 2 * K < p ^ 2) (M : Multiset ℤ) {j : ℕ}
    (hj : j ∈ Icc 1 K) (hj0 : ¬(p : ℤ) ∣ (j : ℤ)) :
    VG p (res K (tpol M) j)
      (((M.filter fun γ : ℤ => ((γ : ZMod p)) ^ 2 = ((j : ℤ) : ZMod p) ^ 2).card : ℚ) -
        (((Icc 1 K).erase j).filter fun i : ℕ =>
            ((i : ℤ) : ZMod p) ^ 2 = ((j : ℤ) : ZMod p) ^ 2).card) := by
  rw [res_tpol hj, div_eq_mul_inv]
  have hden : ∏ i ∈ (Icc 1 K).erase j, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
    have hij := (Finset.mem_erase.mp hi).1
    have : (i : ℚ) ≠ j := by exact_mod_cast hij
    intro h
    have h2 : ((i : ℚ) - j) * ((i : ℚ) + j) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact this (by linarith)
    · have : (0 : ℚ) ≤ i := by positivity
      have : (1 : ℚ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
      linarith
  have h1 := VG_prod_sq_sub (p := p) M (j : ℤ)
  have h2 := VG.inv (p := p) hden (padicValRat_den_le hp3 hj hK hj0)
  push_cast at h1
  simpa [sub_eq_add_neg] using h1.mul h2

/-- Divided differences of integral polynomials are integral. -/
lemma eval_sub_eval_int {S : ℚ[X]} (hS : GV p S 0) {u v : ℚ} (hu : VG p u 0) (hv : VG p v 0) :
    ∃ T : ℚ, S.eval u - S.eval v = (u - v) * T ∧ VG p T 0 := by
  refine
    ⟨∑ k ∈ range (S.natDegree + 1), S.coeff k * ∑ i ∈ range k, u ^ i * v ^ (k - 1 - i), ?_, ?_⟩
  · rw [eval_eq_sum_range, eval_eq_sum_range, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := Commute.geom_sum₂_mul (Commute.all u v) k
    rw [← mul_sub, ← this]; ring
  · refine VG.sum _ fun k _ => ?_
    have : VG p (∑ i ∈ range k, u ^ i * v ^ (k - 1 - i)) 0 :=
      VG.sum _ fun i _ => by simpa using (hu.pow i).mul (hv.pow (k - 1 - i))
    simpa using (hS k).mul this

omit hp in
lemma GV_tpol (M : Multiset ℤ) : GV p (tpol M) 0 := by
  rw [← tpolZ_map_Q]; intro k;
  rw [coeff_map]; exact VG.intCast _

lemma sq_ne_of_ne {i j : ℕ} (h : i ≠ j) : (i : ℚ) ^ 2 - (j : ℚ) ^ 2 ≠ 0 := by
  intro h2
  have h3 : ((i : ℚ) - j) * ((i : ℚ) + j) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact h (by exact_mod_cast (sub_eq_zero.mp h4))
  · have : (0 : ℚ) ≤ i := by positivity
    have : (0 : ℚ) ≤ j := by positivity
    have hi : (i : ℚ) = 0 := by linarith
    have hj : (j : ℚ) = 0 := by linarith
    exact h (by exact_mod_cast hi.trans hj.symm)

/-- **The pairing lemma**: two remaining poles `a, p - a` give an integral contribution. -/
theorem pair_GV (hp3 : 3 ≤ p) {K : ℕ} (M : Multiset ℤ) {a : ℕ} (ha1 : 1 ≤ a) (hap : a < p)
    (hne : a ≠ p - a) (haK : a ≤ K) (hbK : p - a ≤ K)
    (hroots : ∀ i ∈ Icc 1 K, i ≠ a → i ≠ p - a → (i : ℤ) ∈ M)
    (hres : VG p (res K (tpol M) (p - a)) (-1)) :
    GV p (C (res K (tpol M) a) * poleValue a + C (res K (tpol M) (p - a)) * poleValue (p - a))
      0 := by
  set b := p - a with hb
  set W := ((Icc 1 K).erase a).erase b with hW
  set ρ : ℕ → ℚ := fun i => -(i : ℚ) ^ 2 with hρ
  have hinj : Set.InjOn ρ W := by
    intro i _ j _ h
    simp only [hρ, neg_inj] at h
    have := (sq_ne_of_ne (i := i) (j := j))
    by_contra hij; exact this hij (by rw [h]; ring)
  have hroot : ∀ x ∈ W.image ρ, (tpol M).eval x = 0 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' := Finset.mem_erase.mp hi
    have hi'' := Finset.mem_erase.mp hi'.2
    rw [eval_tpol]
    apply Multiset.prod_eq_zero
    exact Multiset.mem_map.mpr ⟨i, hroots i hi''.2 hi''.1 hi'.1, by simp [hρ]⟩
  have hsqv : ∀ i : ℕ, VG p (-(i : ℚ) ^ 2) 0 := fun i => by
    have := (VG.natCast (p := p) (i ^ 2)).neg; push_cast at this; exact this
  obtain ⟨S, hS, hNum⟩ :=
    factor_roots (W.image ρ)
      (fun x hx => by
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        exact hsqv i)
      (GV_tpol M) hroot
  rw [Finset.prod_image hinj] at hNum
  have haIcc : a ∈ Icc 1 K := Finset.mem_Icc.mpr ⟨ha1, haK⟩
  have hbIcc : b ∈ Icc 1 K := Finset.mem_Icc.mpr ⟨by omega, hbK⟩
  have hPW : ∀ j : ℕ, j ∉ W → ∏ i ∈ W, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) ≠ 0 → True := fun _ _ _ =>
    trivial
  have hWne : ∀ j, j = a ∨ j = b → ∏ i ∈ W, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) ≠ 0 := by
    intro j hj
    refine Finset.prod_ne_zero_iff.mpr fun i hi => sq_ne_of_ne ?_
    have hi' := Finset.mem_erase.mp hi
    have hi'' := Finset.mem_erase.mp hi'.2
    rcases hj with rfl | rfl
    · exact hi''.1
    · exact hi'.1
  have hNumEval :
    ∀ j : ℕ,
      (tpol M).eval (-(j : ℚ) ^ 2) =
        (∏ i ∈ W, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2)) * S.eval (-(j : ℚ) ^ 2) := by
    intro j
    rw [hNum, eval_mul, eval_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [hρ]; ring
  have hEa : (Icc 1 K).erase a = insert b W := by
    rw [hW, Finset.insert_erase (Finset.mem_erase.mpr ⟨Ne.symm hne, hbIcc⟩)]
  have hEb : (Icc 1 K).erase b = insert a W := by
    rw [hW, Finset.erase_right_comm, Finset.insert_erase (Finset.mem_erase.mpr ⟨hne, haIcc⟩)]
  have hbW : b ∉ W := by simp [hW]
  have haW : a ∉ W := by simp [hW]
  have hres_a : res K (tpol M) a = S.eval (-(a : ℚ) ^ 2) / ((b : ℚ) ^ 2 - (a : ℚ) ^ 2) := by
    unfold res
    rw [eval_derivative_D haIcc, hEa, Finset.prod_insert hbW, hNumEval]
    field_simp [hWne a (Or.inl rfl), sq_ne_of_ne (Ne.symm hne)]
  have hres_b : res K (tpol M) b = S.eval (-(b : ℚ) ^ 2) / ((a : ℚ) ^ 2 - (b : ℚ) ^ 2) := by
    unfold res
    rw [eval_derivative_D hbIcc, hEb, Finset.prod_insert haW, hNumEval]
    field_simp [hWne b (Or.inr rfl), sq_ne_of_ne hne]
  obtain ⟨T, hT, hTv⟩ :=
    eval_sub_eval_int hS (u := -(a : ℚ) ^ 2) (v := -(b : ℚ) ^ 2) (hsqv a) (hsqv b)
  have hsum : res K (tpol M) a + res K (tpol M) b = T := by
    rw [hres_a, hres_b]
    have hab : (b : ℚ) ^ 2 - (a : ℚ) ^ 2 ≠ 0 := sq_ne_of_ne (Ne.symm hne)
    have hba : (a : ℚ) ^ 2 - (b : ℚ) ^ 2 ≠ 0 := sq_ne_of_ne hne
    have key : S.eval (-(a : ℚ) ^ 2) - S.eval (-(b : ℚ) ^ 2) = ((b : ℚ) ^ 2 - (a : ℚ) ^ 2) * T :=
      by rw [hT]; ring
    rw [div_add_div _ _ hab hba, div_eq_iff (mul_ne_zero hab hba)]
    linear_combination ((a : ℚ) ^ 2 - (b : ℚ) ^ 2) * key
  have hsplit :
    C (res K (tpol M) a) * poleValue a + C (res K (tpol M) b) * poleValue b =
      C T * poleValue a + C (res K (tpol M) b) * (poleValue b - poleValue a) :=
    by rw [← hsum, C_add]; ring
  rw [hsplit]
  have hPa := GV_poleValue_lt hp3 ha1 hap
  have hcong := GV_poleValue_congr hp3 ha1 hap
  exact ((GV.C_mul hTv hPa).mono (by norm_num)).add ((GV.C_mul hres hcong).mono (by norm_num))

end Zeta5Irrational

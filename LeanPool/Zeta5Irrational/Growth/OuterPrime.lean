/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Growth.TailPrime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Data.Rat.Star
import Mathlib.Data.Int.Star
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Ring.Basic

import Mathlib.Algebra.Order.Floor.Semifield

/-! # The outer range: class counts

For a nonzero class `c`, the number of class members in `(X, Y]` is `SX p Y c - SX p X c`.
-/

public section

open Finset

namespace Zeta5Irrational

variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}

lemma jc_eq_iff (hm : 2 * m + 1 = p) (j : ℕ) (c : Fin (m + 1)) :
    jc hm j = c ↔
      ((j : ℤ) : ZMod p) = (((c : ℕ) : ℤ) : ZMod p) ∨
        ((j : ℤ) : ZMod p) = -(((c : ℕ) : ℤ) : ZMod p) := by
  unfold jc
  constructor
  · intro h
    rcases ccls_spec hm ((j : ℤ) : ZMod p) with h1 | h1 <;> rw [h] at h1
    · left; exact h1.symm
    · right; rw [h1]; ring
  · intro h
    refine (ccls_unique hm _ c ?_).symm
    rcases h with h | h
    · left; exact h.symm
    · right; rw [h]; ring

lemma neg_ne_self_zmod (hm : 2 * m + 1 = p) {x : ZMod p} (hx : x ≠ 0) : x ≠ -x := by
  intro h
  have h2 : (2 : ZMod p) * x = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact two_ne_zero_zmod hm h3
  · exact hx h3

lemma card_class (hm : 2 * m + 1 = p) {c : Fin (m + 1)} (hc : c ≠ 0) (X : ℕ) :
    ((Icc 1 X).filter fun j => jc hm j = c).card = SX p X (((c : ℕ) : ℤ) : ZMod p) := by
  have hc0 : (((c : ℕ) : ℤ) : ZMod p) ≠ 0 := by
    intro h
    apply hc
    have := (ccls_eq_zero_iff hm _).mpr h
    rw [ccls_self hm c] at this
    exact this
  unfold SX
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_union, jc_eq_iff hm]
    tauto
  · rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact neg_ne_self_zmod hm hc0 (h1.2.symm.trans h2.2)

lemma card_class_Ioc (hm : 2 * m + 1 = p) {c : Fin (m + 1)} (hc : c ≠ 0) {X Y : ℕ} (hXY : X ≤ Y) :
    ((Icc (X + 1) Y).filter fun j => jc hm j = c).card =
      SX p Y (((c : ℕ) : ℤ) : ZMod p) - SX p X (((c : ℕ) : ℤ) : ZMod p) := by
  rw [← card_class hm hc, ← card_class hm hc]
  have hsplit :
    (Icc 1 Y).filter (fun j => jc hm j = c) =
      (Icc 1 X).filter (fun j => jc hm j = c) ∪ (Icc (X + 1) Y).filter (fun j => jc hm j = c) :=
    by ext j; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj :
    Disjoint ((Icc 1 X).filter (fun j => jc hm j = c))
      ((Icc (X + 1) Y).filter (fun j => jc hm j = c)) := by
    rw [Finset.disjoint_left]; intro j h1 h2
    simp only [Finset.mem_filter, Finset.mem_Icc] at h1 h2; omega
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  omega

/-- The per-class outer weight sum `G_q(a, δ)`. -/
@[expose] noncomputable def GO (q a d : ℕ) : ℚ :=
  ∑ i ∈ range (2 * q + a - 2), min 0 ((i : ℚ) + 3 * d - ((2 * q + a : ℕ) + 4 : ℚ) / 2)

section

variable (hm : 2 * m + 1 = p) {n : ℕ} (hn : 1 ≤ n) (hout : 40 * n < 3 * p)

include hm hn hout in
omit hp in
lemma three_n_le_m : 3 * n ≤ m := by omega

include hm in
lemma SX_small {X : ℕ} (hX : X < p) {c : ℕ} (hc1 : 1 ≤ c) (hcm : c ≤ m) :
    SX p X (((c : ℕ) : ℤ) : ZMod p) = aCnt p X c := by
  rw [SX_class hm hc1 hcm, Nat.div_eq_of_lt hX, Nat.mod_eq_of_lt hX]; ring

include hn hout in
lemma class_data {c : Fin (m + 1)} (hc : c ≠ 0) :
    LoC hm n c = 2 * (40 * n / p) + aCnt p (40 * n % p) c - aCnt p (3 * n) c ∧
      nbC hm n c = 2 * (40 * n / p) + aCnt p (40 * n % p) c - 2 ∧
        ellC hm n c = 2 * (40 * n / p) + aCnt p (40 * n % p) c ∧ delC n c = aCnt p (3 * n) c := by
  have hc1 : 1 ≤ (c : ℕ) := by
    rcases Nat.eq_zero_or_pos (c : ℕ) with h | h
    · exact absurd (Fin.ext h) hc
    · exact h
  have hcm := Nat.lt_succ_iff.mp c.isLt
  have h3m := three_n_le_m hm hn hout
  have hN : 3 * n < p := by omega
  have hK := SX_class hm hc1 hcm (40 * n)
  have hNs := SX_small hm hN hc1 hcm
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold LoC tailC tailO
    rw [card_class_Ioc hm hc (by omega), hK, hNs]
  · unfold nbC bigC tailC tailO
    rw [Finset.filter_filter]
    rcases le_or_gt p (40 * n) with hpK | hpK
    · have e :
        (Icc (3 * n + 1) (40 * n)).filter (fun j => jc hm j = c ∧ p < j) =
          (Icc (p + 1) (40 * n)).filter (fun j => jc hm j = c) :=
        by ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
      rw [e, card_class_Ioc hm hc hpK, hK, SX_class hm hc1 hcm p, Nat.div_self (by omega),
        Nat.mod_self]
      unfold aCnt; split_ifs <;> omega
    · have e : (Icc (3 * n + 1) (40 * n)).filter (fun j => jc hm j = c ∧ p < j) = ∅ := by
        ext j;
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
      rw [e, Finset.card_empty, Nat.div_eq_of_lt hpK]
      unfold aCnt; split_ifs <;> omega
  · unfold ellC; rw [card_class hm hc, hK]
  · unfold delC aCnt; split_ifs <;> omega

include hn hout in
lemma sum_wO_class {c : Fin (m + 1)} (hc : c ≠ 0) :
    ∑ i ∈ range (LoC hm n c), wO hm n c i =
      GO (40 * n / p) (aCnt p (40 * n % p) c) (aCnt p (3 * n) c) := by
  obtain ⟨hL, hnb, hl, hd⟩ := class_data hm hn hout hc
  have hδ : aCnt p (3 * n) c ≤ 1 := by
    have := three_n_le_m hm hn hout
    have hcm := Nat.lt_succ_iff.mp c.isLt
    unfold aCnt; split_ifs <;> omega
  have hsub : nbC hm n c ≤ LoC hm n c := by rw [hL, hnb]; omega
  rw [← Finset.sum_range_add_sum_Ico _ hsub]
  have h0 : ∑ i ∈ Ico (nbC hm n c) (LoC hm n c), wO hm n c i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    unfold wO; rw [ite_eq_right hc, ite_eq_right (by have := (Finset.mem_Ico.mp hi).1; omega)]
  rw [h0, add_zero, hnb]
  unfold GO
  refine Finset.sum_congr rfl fun i hi => ?_
  unfold wO
  rw [ite_eq_right hc, ite_eq_left (by rw [hnb]; exact Finset.mem_range.mp hi), hl, hd]

include hn hout in
lemma sum_wO_zero : -4 ≤ ∑ i ∈ range (LoC hm n 0), wO hm n 0 i := by
  have hL : LoC hm n 0 ≤ 2 := by
    unfold LoC tailC tailO
    have hsub : (Icc (3 * n + 1) (40 * n)).filter (fun j => jc hm j = 0) ⊆ {p, 2 * p} := by
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_filter.mp hj
      have hdvd : p ∣ j := by exact_mod_cast (jc_eq_zero_iff hm j).mp hj2
      obtain ⟨t, rfl⟩ := hdvd
      have := Finset.mem_Icc.mp hj1
      have ht1 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h | h
        · subst h; omega
        · exact h
      have ht3 : t < 3 := by
        by_contra h; rw [not_lt] at h
        have : p * 3 ≤ p * t := Nat.mul_le_mul_left _ h
        omega
      interval_cases t <;> simp [mul_comm]
    exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
  have : ∀ i, -2 ≤ wO hm n 0 i := by
    intro i; unfold wO; rw [ite_eq_left rfl];
    split_ifs <;> norm_num
  calc
    (-4 : ℚ) ≤ ∑ _i ∈ range (LoC hm n 0), (-2 : ℚ) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have : (LoC hm n 0 : ℚ) ≤ 2 := by exact_mod_cast hL
      linarith
    _ ≤ _ := Finset.sum_le_sum fun i _ => this i

end

/-- The class-function coefficients of the outer range. -/
@[expose] noncomputable def bGO (q : ℕ) (i j : Fin 3) : ℝ :=
  bcoef (fun a => bcoef (fun b => (GO q a b : ℝ)) j) i

/-- **The continuous outer function** (in the variable `x = K/p`). -/
@[expose] noncomputable def Eout (x : ℝ) : ℝ :=
  -2 * (37 / 40 * x) * (⌊x⌋₊ : ℝ) + 2 * Jc (37 / 40 * x) -
      2 * ∑ i, ∑ j, bGO ⌊x⌋₊ i j * ccount (Int.fract x) (Int.fract (3 / 40 * x)) i j +
    max 0 (13 / 10 * x - 2)

/-- The additive error of the outer bound. -/
@[expose] noncomputable def Cout (n p : ℕ) : ℝ :=
  5 * ∑ i, ∑ j, |bGO (40 * n / p) i j| + 11

section

variable {n : ℕ} (hn : 33 ≤ n) (hodd : 2 * (p / 2) + 1 = p) (hp7 : 7 ≤ p) (hout : 40 * n < 3 * p)
  (hle : p ≤ 2 * (37 * n)) (hsq : 2 * (40 * n) < p ^ 2)

include hn hodd hp7 hout hle hsq in
omit hle in
/-- **The outer per-prime bound.** -/
theorem outer_Lp_le : -(Lp n p : ℝ) ≤ (p : ℝ) * Eout (40 * n / p) + Cout n p := by
  have hp0 : 0 < p := by omega
  have hpR0 : (0 : ℝ) < p := by exact_mod_cast hp0
  have hN : 3 * n < p := by omega
  have hOK : OuterOK n p := ⟨hodd, hp7, hout, hsq, hN⟩
  have hLp : Lp n p = vSK n p + ⌊WO n p⌋ := by
    unfold Lp Mcut;
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hOK]
  set m := p / 2 with hmdef
  have hWO :
    WO n p =
      2 * ∑ c, ∑ i ∈ range (LoC hodd n c), wO hodd n c i -
        ((37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) : ℕ) : ℚ) := by
    unfold WO;
    rw [dite_eq_left hp.out, dite_eq_left hodd]
      -- the class sum
  have hsplit :
    ∑ c, ∑ i ∈ range (LoC hodd n c), wO hodd n c i =
      ∑ i ∈ range (LoC hodd n 0), wO hodd n 0 i +
        ∑ c ∈ Icc 1 m, GO (40 * n / p) (aCnt p (40 * n % p) c) (aCnt p (3 * n) c) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (m + 1)))]
    congr 1
    rw [Finset.sum_congr rfl fun c hc =>
        sum_wO_class hodd (by omega) hout (Finset.mem_erase.mp hc).1]
    exact
      sum_erase_zero_eq_Icc (fun c => GO (40 * n / p) (aCnt p (40 * n % p) c) (aCnt p (3 * n) c))
  have hZ :=
    sum_wO_zero hodd (n := n) (by omega)
      hout
        -- the continuous class sum
  have hcs :=
    class_sum_approx hodd (Nat.mod_lt (40 * n) hp0) (Nat.mod_lt (3 * n) hp0)
      (fun a b => (GO (40 * n / p) a b : ℝ))
  rw [Nat.mod_eq_of_lt hN] at hcs
  rw [abs_le] at hcs
  have hcsQ :
    ((∑ c ∈ Icc 1 m, GO (40 * n / p) (aCnt p (40 * n % p) c) (aCnt p (3 * n) c) : ℚ) : ℝ) =
      ∑ c ∈ Icc 1 m, (GO (40 * n / p) (aCnt p (40 * n % p) c) (aCnt p (3 * n) c) : ℝ) := by
    push_cast;
    rfl
      -- the rank loss
  have hr :
    ((37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) : ℕ) : ℝ) ≤
      (p : ℝ) * max (0 : ℝ) (13 / 10 * (40 * (n : ℝ) / (p : ℝ)) - 2) + 2 := by
    have e :
      (p : ℝ) * max (0 : ℝ) (13 / 10 * (40 * (n : ℝ) / (p : ℝ)) - 2) =
        max 0 (52 * (n : ℝ) - 2 * p) :=
      by rw [mul_max_of_nonneg _ _ hpR0.le, mul_zero]; congr 1; field_simp; ring
    rw [e]
    have hm0 := le_max_left (0 : ℝ) (52 * n - 2 * p)
    have hm1 := le_max_right (0 : ℝ) (52 * n - 2 * p)
    rcases Nat.lt_or_ge (37 * n) (((2 * p + 22 * n - 3) - (37 * n - 1))) with h | h
    · rw [Nat.sub_eq_zero_of_le h.le]; push_cast; linarith
    · have hR : 37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) ≤ 52 * n + 2 - 2 * p := by omega
      rcases le_or_gt (52 * n + 2) (2 * p) with h5 | h5
      · have : 37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) = 0 := by omega
        rw [this]; push_cast; linarith
      · have h2 := (Nat.cast_le (α := ℝ)).mpr hR
        have h6 : ((52 * n + 2 - 2 * p : ℕ) : ℝ) = 52 * (n : ℝ) + 2 - 2 * p := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [h6] at h2
        linarith
          -- `v_p(S_K)`
  have hv :=
    neg_vSK_le (p := p) (n := n) (by omega) (by omega) (by nlinarith) (by nlinarith) 1000
      (by omega)
  rw [Nat.div_eq_of_lt hN] at hv
  rw [layer_eq hp0] at hv
        -- the target
  have hx : (40 * n / p : ℝ) = ((40 * n : ℕ) : ℝ) / (p : ℕ) := by push_cast; ring
  have hfl : ⌊(40 * n / p : ℝ)⌋₊ = 40 * n / p := by rw [hx, Nat.floor_div_eq_div]
  have hfK : Int.fract ((40 * n / p : ℝ)) = ((40 * n % p : ℕ) : ℝ) / p := by
    rw [hx];
    exact Int.fract_div_natCast_eq_div_natCast_mod
  have hfN : Int.fract ((3 : ℝ) / 40 * (40 * n / p)) = ((3 * n : ℕ) : ℝ) / p := by
    rw [show (3 : ℝ) / 40 * (40 * n / p) = ((3 * n : ℕ) : ℝ) / (p : ℕ) by push_cast; ring,
      Int.fract_div_natCast_eq_div_natCast_mod, Nat.mod_eq_of_lt hN]
  have hu : ((37 * n : ℕ) : ℝ) / p = 37 / 40 * (40 * n / p) := by push_cast; ring
  rw [hu] at hv
  have e1 : ((37 * n : ℕ) : ℝ) = (p : ℝ) * (37 / 40 * (40 * n / p)) := by push_cast; field_simp
  rw [e1] at hv
  have hfl2 : ((40 * n / p : ℕ) : ℝ) = (⌊(40 * n / p : ℝ)⌋₊ : ℝ) := by rw [hfl]
  unfold Eout Cout
  rw [hfl, hfK, hfN]
  have hflo := Int.lt_floor_add_one (WO n p)
  have hfloR : ((WO n p : ℚ) : ℝ) < ((⌊WO n p⌋ : ℤ) : ℝ) + 1 := by exact_mod_cast hflo
  have hWOR :
    ((WO n p : ℚ) : ℝ) =
      2 *
          (((∑ i ∈ range (LoC hodd n 0), wO hodd n 0 i : ℚ) : ℝ) +
            ∑ c ∈ Icc 1 m, (GO (40 * n / p) (aCnt p (40 * n % p) c) (aCnt p (3 * n) c) : ℝ)) -
        ((37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) : ℕ) : ℝ) :=
    by rw [hWO, hsplit]; push_cast; ring
  push_cast at hWOR
  rw [hLp]
  push_cast
  have hZR : (-4 : ℝ) ≤ ((∑ i ∈ range (LoC hodd n 0), wO hodd n 0 i : ℚ) : ℝ) := by
    exact_mod_cast hZ
  push_cast at hZR
  have hb :
    ∀ i j,
      bcoef (fun a => bcoef (fun b => (GO (40 * n / p) a b : ℝ)) j) i = bGO (40 * n / p) i j :=
    fun i j => rfl
  simp only [hb] at hcs
  push_cast at hcs
  linarith [hcs.1]

end

end Zeta5Irrational

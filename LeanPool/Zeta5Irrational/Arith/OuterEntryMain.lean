/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Arith.OuterEntries
public import LeanPool.Zeta5Irrational.Arith.OuterFrame
import LeanPool.Zeta5Irrational.Arith.MomentVal
import LeanPool.Zeta5Irrational.Arith.OuterEntry
import LeanPool.Zeta5Irrational.Arith.PoleVal
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # Outer range: the entry theorem
-/

public section

open Finset Polynomial

namespace Zeta5Irrational

variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}

/-- The `μ`-part below `2p - 3` of an integral polynomial is integral. -/
lemma VG_μpoly_sub_μGe (hp5 : 5 ≤ p) {Q : ℚ[X]} (hQ : GV p Q 0) : VG p (μpoly Q - μGe p Q) 0 := by
  have e : μpoly Q = ∑ e ∈ range (Q.natDegree + 1), Q.coeff e * μmono e := by
    unfold μpoly;
    rw [Polynomial.sum_over_range]; intro n; simp
  rw [e, μGe, ← Finset.sum_sub_distrib]
  refine VG.sum _ fun e _ => ?_
  split_ifs with h
  · simp [VG.zero]
  · simpa using (hQ e).mul (VG_μmono_int hp5 (by omega))

omit hp in
/-- `μ_X` minus its high part, expanded. -/
lemma μX_sub_μGe (K : ℕ) (P : ℚ[X]) :
    μX K P - C (μGe p (P /ₘ D K)) =
      C (μpoly (P /ₘ D K) - μGe p (P /ₘ D K)) + ∑ j ∈ Icc 1 K, C (res K P j) * poleValue j :=
  by unfold μX res; rw [map_sub]; ring

variable (hm : 2 * m + 1 = p) (n : ℕ)

lemma entryO_eq (cs : Fin (m + 1)) (is : ℕ) (ct : Fin (m + 1)) (it : ℕ) :
    D (3 * n) ^ 6 * (tpolZ (rootsO hm n cs is)).map (Int.castRingHom ℚ) *
        (tpolZ (rootsO hm n ct it)).map (Int.castRingHom ℚ) =
      tpol (entryO hm n cs is ct it) :=
  by rw [tpolZ_map_Q, tpolZ_map_Q, D_eq_tpol, ← tpol_nsmul, ← tpol_add, ← tpol_add]; rfl

/-- The integral numerator quotient. -/
lemma GV_entry_quot (cs : Fin (m + 1)) (is : ℕ) (ct : Fin (m + 1)) (it : ℕ) :
    GV p (tpol (entryO hm n cs is ct it) /ₘ D (40 * n)) 0 := by
  rw [← tpolZ_map_Q];
  exact GV_divByMonic_D _ _

/-- Residues vanish at poles `j ≤ N` and at tail poles outside the common class. -/
lemma res_entry_zero {cs ct : Fin (m + 1)} {is it : ℕ} {j : ℕ} (hj : j ∈ Icc 1 (40 * n))
    (h : j ≤ 3 * n ∨ jc hm j ≠ cs ∨ jc hm j ≠ ct) :
    res (40 * n) (tpol (entryO hm n cs is ct it)) j = 0 := by
  have hj' := Finset.mem_Icc.mp hj
  rcases h with h | h | h
  · exact res_tpol_eq_zero hj (mem_entryO_small hm n (Finset.mem_Icc.mpr ⟨hj'.1, h⟩)) rfl
  · by_cases hN : j ≤ 3 * n
    · exact res_tpol_eq_zero hj (mem_entryO_small hm n (Finset.mem_Icc.mpr ⟨hj'.1, hN⟩)) rfl
    · exact
        res_tpol_eq_zero hj
          (mem_entryO_left hm n (mem_rootsO_other hm n (Finset.mem_Icc.mpr ⟨by omega, hj'.2⟩) h))
          rfl
  · by_cases hN : j ≤ 3 * n
    · exact res_tpol_eq_zero hj (mem_entryO_small hm n (Finset.mem_Icc.mpr ⟨hj'.1, hN⟩)) rfl
    · exact
        res_tpol_eq_zero hj
          (mem_entryO_right hm n (mem_rootsO_other hm n (Finset.mem_Icc.mpr ⟨by omega, hj'.2⟩) h))
          rfl

/-- The pole sum reduces to the tail poles of the common class. -/
lemma pole_sum_reduce (c : Fin (m + 1)) (is it : ℕ) :
    ∑ j ∈ Icc 1 (40 * n), C (res (40 * n) (tpol (entryO hm n c is c it)) j) * poleValue j =
      ∑ j ∈ tailC hm n c, C (res (40 * n) (tpol (entryO hm n c is c it)) j) * poleValue j := by
  symm
  apply Finset.sum_subset
  · intro j hj
    have := (Finset.mem_filter.mp hj).1
    unfold tailO at this
    exact
      Finset.mem_Icc.mpr
        ⟨by have := (Finset.mem_Icc.mp this).1; omega, (Finset.mem_Icc.mp this).2⟩
  · intro j hj hjn
    rw [res_entry_zero hm n hj, C_0, zero_mul]
    by_contra h
    push Not at h
    apply hjn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hj).2⟩, h.2.1⟩

lemma pole_sum_cross {cs ct : Fin (m + 1)} (hc : cs ≠ ct) (is it : ℕ) :
    ∑ j ∈ Icc 1 (40 * n), C (res (40 * n) (tpol (entryO hm n cs is ct it)) j) * poleValue j = 0 :=
  by
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [res_entry_zero hm n hj, C_0, zero_mul]
  by_cases h : jc hm j = cs
  · right; right; rw [h]; exact hc
  · right; left; exact h

/-- `ℓ(c) = #{j ≤ K : j ≡ ±c}`. -/
@[expose] def ellC (c : Fin (m + 1)) : ℕ :=
  ((Icc 1 (40 * n)).filter fun j => jc hm j = c).card

/-- `δ(c) = [c ≤ N]`. -/
@[expose] def delC (c : Fin (m + 1)) : ℕ :=
  if (c : ℕ) ≤ 3 * n then 1 else 0

/-- The outer weights (4.12). -/
@[expose] noncomputable def wO (c : Fin (m + 1)) (i : ℕ) : ℚ :=
  if c = 0 then (if i < nbC hm n 0 then -2 else if nbC hm n 0 = 0 then -1 / 2 else 0)
  else
    (if i < nbC hm n c then min 0 ((i : ℚ) + 3 * delC n c - ((ellC hm n c : ℚ) + 4) / 2) else 0)

lemma wO_nonpos (c : Fin (m + 1)) (i : ℕ) : wO hm n c i ≤ 0 := by
  unfold wO;
  split_ifs <;>
    first
    | exact min_le_left _ _
    | norm_num

lemma jc_eq_zero_iff (j : ℕ) : jc hm j = 0 ↔ (p : ℤ) ∣ (j : ℤ) := by
  unfold jc;
  rw [ccls_eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Denominator count for a nonzero class. -/
lemma den_count {c : Fin (m + 1)} {j : ℕ} (hj : j ∈ Icc 1 (40 * n)) (hjc : jc hm j = c) :
    (((Icc 1 (40 * n)).erase j).filter fun i : ℕ =>
          ((i : ℤ) : ZMod p) ^ 2 = ((j : ℤ) : ZMod p) ^ 2).card =
      ellC hm n c - 1 := by
  have e :
    (((Icc 1 (40 * n)).erase j).filter fun i : ℕ =>
        ((i : ℤ) : ZMod p) ^ 2 = ((j : ℤ) : ZMod p) ^ 2) =
      ((Icc 1 (40 * n)).filter fun i => jc hm i = c).erase j := by
    rw [Finset.filter_erase]
    congr 1
    ext i
    simp only [Finset.mem_filter, sq_eq_iff_ccls hm]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.trans hjc⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.trans hjc.symm⟩
  rw [e, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hj, hjc⟩)]
  rfl

/-- Numerator count for a nonzero class. -/
lemma num_count {c : Fin (m + 1)} (hc0 : c ≠ 0) {is it : ℕ} {j : ℕ} (hjc : jc hm j = c) :
    6 * delC n c + is + it ≤
      ((entryO hm n c is c it).filter fun γ : ℤ =>
          ((γ : ZMod p)) ^ 2 = ((j : ℤ) : ZMod p) ^ 2).card := by
  have hx : ((j : ℤ) : ZMod p) ^ 2 = ((((c : ℕ) : ℤ) : ZMod p)) ^ 2 := by rw [sq_jc hm j, hjc]
  unfold entryO
  rw [Multiset.filter_add, Multiset.filter_add, Multiset.card_add, Multiset.card_add]
  have h1 := count_rootsO hm n c is _ hx
  have h2 := count_rootsO hm n c it _ hx
  have h3 :
    6 * delC n c ≤
      ((6 • ((Icc 1 (3 * n)).val.map fun j : ℕ => (j : ℤ))).filter fun γ : ℤ =>
          ((γ : ZMod p)) ^ 2 = ((j : ℤ) : ZMod p) ^ 2).card := by
    unfold delC
    split_ifs with hc
    · rw [Multiset.filter_nsmul, Multiset.card_nsmul]
      have :
        1 ≤
          (((Icc 1 (3 * n)).val.map fun j : ℕ => (j : ℤ)).filter fun γ : ℤ =>
              ((γ : ZMod p)) ^ 2 = ((j : ℤ) : ZMod p) ^ 2).card := by
        apply Multiset.card_pos_iff_exists_mem.mpr
        refine
          ⟨((c : ℕ) : ℤ), Multiset.mem_filter.mpr ⟨Multiset.mem_map.mpr ⟨c, ?_, rfl⟩, hx.symm⟩⟩
        have : (c : ℕ) ≠ 0 := fun h => hc0 (Fin.ext h)
        exact Finset.mem_val.mpr (Finset.mem_Icc.mpr ⟨by omega, hc⟩)
      omega
    · omega
  omega

lemma ellC_pos {c : Fin (m + 1)} {j : ℕ} (hj : j ∈ Icc 1 (40 * n)) (hjc : jc hm j = c) :
    1 ≤ ellC hm n c :=
  Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hjc⟩⟩

lemma mem_Icc_of_tailC {c : Fin (m + 1)} {j : ℕ} (hj : j ∈ tailC hm n c) : j ∈ Icc 1 (40 * n) := by
  have := Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1
  exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩

/-- Residue bound on a nonzero class. -/
lemma VG_res_entry (hp3 : 3 ≤ p) (hK : 2 * (40 * n) < p ^ 2) {c : Fin (m + 1)} (hc0 : c ≠ 0)
    {is it : ℕ} {j : ℕ} (hj : j ∈ tailC hm n c) :
    VG p (res (40 * n) (tpol (entryO hm n c is c it)) j)
      ((6 * delC n c + is + it : ℕ) - ((ellC hm n c : ℚ) - 1)) := by
  have hjc : jc hm j = c := (Finset.mem_filter.mp hj).2
  have hjI := mem_Icc_of_tailC hm n hj
  have hj0 : ¬(p : ℤ) ∣ (j : ℤ) := fun h => hc0 (hjc ▸ (jc_eq_zero_iff hm j).mpr h)
  have h := VG_res_class hp3 hK (entryO hm n c is c it) hjI hj0
  rw [den_count hm n hjI hjc] at h
  refine h.mono ?_
  have h1 := num_count hm n hc0 (is := is) (it := it) hjc
  have h2 := ellC_pos hm n hjI hjc
  push_cast [h2]
  have :
    ((6 * delC n c + is + it : ℕ) : ℚ) ≤
      ((entryO hm n c is c it).filter fun γ : ℤ =>
          ((γ : ZMod p)) ^ 2 = ((j : ℤ) : ZMod p) ^ 2).card :=
    by exact_mod_cast h1
  push_cast at this
  linarith

/-- **Case (a)**: both rows below `nb`. -/
lemma pole_case_a (hp3 : 3 ≤ p) (hK : 2 * (40 * n) < p ^ 2) {c : Fin (m + 1)} (hc0 : c ≠ 0)
    {is it : ℕ} (his : is < nbC hm n c) (hit : it < nbC hm n c) :
    GV p (∑ j ∈ tailC hm n c, C (res (40 * n) (tpol (entryO hm n c is c it)) j) * poleValue j)
      (wO hm n c is + wO hm n c it) := by
  refine GV.sum _ fun j hj => ?_
  have hjI := mem_Icc_of_tailC hm n hj
  have hjI' := Finset.mem_Icc.mp hjI
  have hPV := GV_poleValue_sq hp3 hjI'.1 (by nlinarith)
  refine (GV.C_mul (VG_res_entry hm n hp3 hK hc0 hj) hPV).mono ?_
  unfold wO
  rw [ite_eq_right hc0, ite_eq_right hc0, ite_eq_left his, ite_eq_left hit]
  have e1 := min_le_right (0 : ℚ) ((is : ℚ) + 3 * delC n c - ((ellC hm n c : ℚ) + 4) / 2)
  have e2 := min_le_right (0 : ℚ) ((it : ℚ) + 3 * delC n c - ((ellC hm n c : ℚ) + 4) / 2)
  push_cast
  linarith

lemma count_rootsO_zero (i : ℕ) : i ≤ ((rootsO hm n 0 i).filter fun γ : ℤ => (p : ℤ) ∣ γ).card := by
  unfold rootsO
  rw [Multiset.filter_add, Multiset.card_add]
  have hz : (p : ℤ) ∣ (((0 : Fin (m + 1)) : ℕ) : ℤ) := by simp
  split_ifs with h
  · rw [card_filter_replicate, ite_eq_left hz]; omega
  · rw [Multiset.filter_add, Multiset.card_add, card_filter_replicate, ite_eq_left hz]
    have hbig :
      ((bigC hm n 0).val.map fun j : ℕ => (j : ℤ)).filter (fun γ : ℤ => (p : ℤ) ∣ γ) =
        (bigC hm n 0).val.map fun j : ℕ => (j : ℤ) := by
      refine Multiset.filter_eq_self.mpr fun γ hγ => ?_
      obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hγ
      have hj' : j ∈ bigC hm n 0 := Finset.mem_val.mp hj
      exact (jc_eq_zero_iff hm j).mp (Finset.mem_filter.mp (Finset.mem_filter.mp hj').1).2
    rw [hbig, Multiset.card_map, Finset.card_val]
    have : nbC hm n 0 = (bigC hm n 0).card := rfl
    omega

/-- Multiples of `p` up to `K` are `p` and the big zero-class poles. -/
lemma mult_count (hpN : 3 * n < p) :
    ((Icc 1 (40 * n)).filter fun i : ℕ => (p : ℤ) ∣ (i : ℤ)).card ≤ nbC hm n 0 + 1 := by
  have hsub : ((Icc 1 (40 * n)).filter fun i : ℕ => (p : ℤ) ∣ (i : ℤ)) ⊆ insert p (bigC hm n 0) :=
  by
    intro i hi
    rw [Finset.mem_filter, Finset.mem_Icc] at hi
    rw [Finset.mem_insert]
    by_cases hip : i ≤ p
    · left
      have hd : p ∣ i := by exact_mod_cast hi.2
      have := Nat.le_of_dvd (by omega) hd
      omega
    · right
      refine
        Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨?_, (jc_eq_zero_iff hm i).mpr hi.2⟩, by omega⟩
      unfold tailO; exact Finset.mem_Icc.mpr ⟨by omega, hi.1.2⟩
  have := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le p (bigC hm n 0)
  have : nbC hm n 0 = (bigC hm n 0).card := rfl
  omega

lemma nbC_zero_le (hK3 : 40 * n < 3 * p) : nbC hm n 0 ≤ 1 := by
  have hsub : bigC hm n 0 ⊆ {2 * p} := by
    intro j hj
    have h1 := Finset.mem_filter.mp hj
    have h2 := Finset.mem_filter.mp h1.1
    have h3 := Finset.mem_Icc.mp h2.1
    have hd : p ∣ j := by exact_mod_cast (jc_eq_zero_iff hm j).mp h2.2
    obtain ⟨k, rfl⟩ := hd
    have hk1 : 1 < k := by by_contra h; rw [not_lt] at h; interval_cases k <;> omega
    have hk3 : k < 3 := by
      by_contra h; rw [not_lt] at h
      have : p * 3 ≤ p * k := Nat.mul_le_mul_left _ h
      omega
    rw [Finset.mem_singleton]
    interval_cases k; ring
  have := Finset.card_le_card hsub
  rw [Finset.card_singleton] at this
  exact this

/-- **Zero class.** -/
lemma pole_case_zero (hp7 : 7 ≤ p) (hK3 : 40 * n < 3 * p) (hK : 2 * (40 * n) < p ^ 2)
    (hpN : 3 * n < p) (is it : ℕ) :
    GV p (∑ j ∈ tailC hm n 0, C (res (40 * n) (tpol (entryO hm n 0 is 0 it)) j) * poleValue j)
      (wO hm n 0 is + wO hm n 0 it) := by
  have hnb := nbC_zero_le hm n hK3
  refine GV.sum _ fun j hj => ?_
  have hjI := mem_Icc_of_tailC hm n hj
  have hjI' := Finset.mem_Icc.mp hjI
  have hjc : jc hm j = 0 := (Finset.mem_filter.mp hj).2
  have hpj : (p : ℤ) ∣ (j : ℤ) := (jc_eq_zero_iff hm j).mp hjc
  obtain ⟨k, hk⟩ : ∃ k, j = p * k := by exact_mod_cast hpj
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk; omega
    · exact h
  have hkp : k < p := by
    by_contra h; rw [not_lt] at h
    have : p * p ≤ p * k := Nat.mul_le_mul_left _ h
    nlinarith
  have hPV : GV p (poleValue j) (-1) := by
    rw [hk];
    exact
      GV_poleValue_mul (by omega) hk1
        hkp
          -- residue bound
  have hden : ∏ i ∈ (Icc 1 (40 * n)).erase j, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => sq_ne_of_ne (Finset.mem_erase.mp hi).1
  have hnum := VG_prod_sq_sub_zero (p := p) (entryO hm n 0 is 0 it) hpj
  have hdv := VG.inv (p := p) hden (padicValRat_den_zero_le hjI hK hpj)
  have hres :
    VG p (res (40 * n) (tpol (entryO hm n 0 is 0 it)) j) (2 * (is + it : ℚ) - 2 * nbC hm n 0) := by
    rw [res_tpol hjI, div_eq_mul_inv]
    refine (hnum.mul hdv).mono ?_
    have hc1 : (is + it : ℕ) ≤ ((entryO hm n 0 is 0 it).filter fun γ : ℤ => (p : ℤ) ∣ γ).card := by
      unfold entryO
      rw [Multiset.filter_add, Multiset.filter_add, Multiset.card_add, Multiset.card_add]
      have := count_rootsO_zero hm n is
      have := count_rootsO_zero hm n it
      omega
    have hc2 :
      (((Icc 1 (40 * n)).erase j).filter fun i : ℕ => (p : ℤ) ∣ (i : ℤ)).card ≤ nbC hm n 0 := by
      have h1 := mult_count hm n hpN
      rw [Finset.filter_erase] at *
      rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hjI, hpj⟩)]
      omega
    have e1 :
      ((is + it : ℕ) : ℚ) ≤
        (((entryO hm n 0 is 0 it).filter fun γ : ℤ => (p : ℤ) ∣ γ).card : ℚ) :=
      by exact_mod_cast hc1
    have e2 :
      ((((Icc 1 (40 * n)).erase j).filter fun i : ℕ => (p : ℤ) ∣ (i : ℤ)).card : ℚ) ≤
        nbC hm n 0 :=
      by exact_mod_cast hc2
    push_cast at e1 ⊢
    linarith
  refine (GV.C_mul hres hPV).mono ?_
  unfold wO
  rw [ite_eq_left rfl, ite_eq_left rfl]
  interval_cases h : nbC hm n 0
  · simp
    have : (0 : ℚ) ≤ is := by positivity
    have : (0 : ℚ) ≤ it := by positivity
    linarith
  · by_cases h1 : is < 1 <;> by_cases h2 : it < 1
    · rw [ite_eq_left h1, ite_eq_left h2]; push_cast; have : is = 0 := by omega
      have : it = 0 := by omega
      subst_vars; norm_num
    · rw [ite_eq_left h1, ite_eq_right h2, ite_eq_right (by norm_num)]
      have : (1 : ℚ) ≤ it := by exact_mod_cast (by omega : 1 ≤ it)
      have : (0 : ℚ) ≤ is := by positivity
      push_cast; linarith
    · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right (by norm_num)]
      have : (1 : ℚ) ≤ is := by exact_mod_cast (by omega : 1 ≤ is)
      have : (0 : ℚ) ≤ it := by positivity
      push_cast; linarith
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (by norm_num)]
      have : (1 : ℚ) ≤ is := by exact_mod_cast (by omega : 1 ≤ is)
      have : (1 : ℚ) ≤ it := by exact_mod_cast (by omega : 1 ≤ it)
      push_cast; linarith

lemma jc_small {i : ℕ} (hi : i < p) :
    ((jc hm i : ℕ) = i ∧ i ≤ m) ∨ ((jc hm i : ℕ) = p - i ∧ m < i) := by
  have hv : (((i : ℤ) : ZMod p)).val = i := by
    rw [Int.cast_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  unfold jc ccls
  split_ifs with h
  · left; rw [hv] at h; exact ⟨by simp [Nat.mod_eq_of_lt hi], h⟩
  · right; rw [hv] at h; exact ⟨by simp [Nat.mod_eq_of_lt hi], by omega⟩

lemma jc_small_eq {c : Fin (m + 1)} {i : ℕ} (hi : i < p) (h : jc hm i = c) : i = c ∨ i = p - c := by
  have hc := c.isLt
  rcases jc_small hm hi with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h] at h1 <;> omega

/-- Class members up to `K`: the big ones plus at most the two small ones. -/
lemma ellC_le (hpN : 3 * n < p) {c : Fin (m + 1)} (hc0 : c ≠ 0) :
    ellC hm n c ≤ nbC hm n c + ((Icc 1 (40 * n)).filter fun i => jc hm i = c ∧ i < p).card := by
  have hsub :
    ((Icc 1 (40 * n)).filter fun j => jc hm j = c) ⊆
      bigC hm n c ∪ ((Icc 1 (40 * n)).filter fun i => jc hm i = c ∧ i < p) := by
    intro i hi
    obtain ⟨hiI, hic⟩ := Finset.mem_filter.mp hi
    have hiI' := Finset.mem_Icc.mp hiI
    rw [Finset.mem_union]
    by_cases hip : i < p
    · right; exact Finset.mem_filter.mpr ⟨hiI, hic, hip⟩
    · left
      have hne : i ≠ p := by
        intro hh; rw [hh] at hic
        exact hc0 (hic ▸ (jc_eq_zero_iff hm p).mpr dvd_rfl)
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, hic⟩, by omega⟩
      unfold tailO; exact Finset.mem_Icc.mpr ⟨by omega, hiI'.2⟩
  have := Finset.card_le_card hsub
  have :=
    Finset.card_union_le (bigC hm n c) ((Icc 1 (40 * n)).filter fun i => jc hm i = c ∧ i < p)
  unfold ellC nbC
  omega

lemma small_sub {c : Fin (m + 1)} :
    ((Icc 1 (40 * n)).filter fun i => jc hm i = c ∧ i < p) ⊆ {(c : ℕ), p - c} := by
  intro i hi
  obtain ⟨_, hic, hip⟩ := Finset.mem_filter.mp hi
  rcases jc_small_eq hm hip hic with h | h <;> simp [h]

lemma small_card_le {c : Fin (m + 1)} :
    ((Icc 1 (40 * n)).filter fun i => jc hm i = c ∧ i < p).card ≤ 2 :=
  (Finset.card_le_card (small_sub hm n)).trans (Finset.card_le_two)

/-- **Case (b)**: one row at or above `nb`; the pole sum is integral. -/
lemma pole_case_b (hp3 : 3 ≤ p) (hK : 2 * (40 * n) < p ^ 2) (hpN : 3 * n < p) {c : Fin (m + 1)}
    (hc0 : c ≠ 0) {is it : ℕ} (his : nbC hm n c ≤ is) :
    GV p (∑ j ∈ tailC hm n c, C (res (40 * n) (tpol (entryO hm n c is c it)) j) * poleValue j)
      0 := by
  have hcm := c.isLt
  have hc1 : 1 ≤ (c : ℕ) := by
    rcases Nat.eq_zero_or_pos (c : ℕ) with h | h
    · exact absurd (Fin.ext h) hc0
    · exact h
  have hℓ := ellC_le hm n hpN hc0
  have hS2 := small_card_le hm n (c := c)
  set Sm := (Icc 1 (40 * n)).filter fun i => jc hm i = c ∧ i < p with hSm
    -- big poles have zero residue
  have hbig : ∀ j ∈ tailC hm n c, ¬j < p → res (40 * n) (tpol (entryO hm n c is c it)) j = 0 := by
    intro j hj hjp
    have hjc : jc hm j = c := (Finset.mem_filter.mp hj).2
    have hne : j ≠ p := by
      intro hh; rw [hh] at hjc
      exact hc0 (hjc ▸ (jc_eq_zero_iff hm p).mpr dvd_rfl)
    have hjb : j ∈ bigC hm n c := Finset.mem_filter.mpr ⟨hj, by omega⟩
    exact
      res_tpol_eq_zero (mem_Icc_of_tailC hm n hj)
        (mem_entryO_left hm n (mem_rootsO_big hm n his hjb)) rfl
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun j => j < p)]
  rw [Finset.sum_eq_zero (s := (tailC hm n c).filter fun j => ¬j < p)
      (fun j hj => by
        have := Finset.mem_filter.mp hj
        rw [hbig j this.1 this.2, C_0, zero_mul]),
    add_zero]
    -- individual small-pole bound
  have hind :
    ∀ j ∈ (tailC hm n c).filter (fun j => j < p),
      (0 : ℚ) ≤ ((6 * delC n c + is + it : ℕ) : ℚ) - ((ellC hm n c : ℚ) - 1) →
        GV p (C (res (40 * n) (tpol (entryO hm n c is c it)) j) * poleValue j) 0 := by
    intro j hj h0
    have hj' := Finset.mem_filter.mp hj
    have hjI' := Finset.mem_Icc.mp (mem_Icc_of_tailC hm n hj'.1)
    refine
      (GV.C_mul (VG_res_entry hm n hp3 hK hc0 hj'.1) (GV_poleValue_lt hp3 hjI'.1 hj'.2)).mono ?_
    linarith
  by_cases hδ : delC n c = 1
  · refine GV.sum _ fun j hj => hind j hj ?_
    have : (ellC hm n c : ℚ) ≤ nbC hm n c + 2 := by
      exact_mod_cast (by omega : ellC hm n c ≤ nbC hm n c + 2)
    have : (nbC hm n c : ℚ) ≤ is := by exact_mod_cast his
    rw [hδ]; push_cast; linarith
  have hcN : 3 * n < (c : ℕ) := by unfold delC at hδ; split_ifs at hδ with h <;> omega
  have hδ0 : delC n c = 0 := by
    unfold delC;
    rw [ite_eq_right (by omega)]
      -- small class members all lie in the tail
  have hSmT : Sm ⊆ (tailC hm n c).filter (fun j => j < p) := by
    intro i hi
    obtain ⟨hiI, hic, hip⟩ := Finset.mem_filter.mp hi
    have hiI' := Finset.mem_Icc.mp hiI
    have : 3 * n < i := by rcases jc_small_eq hm hip hic with h | h <;> omega
    have hiT : i ∈ tailO n := by unfold tailO; exact Finset.mem_Icc.mpr ⟨by omega, hiI'.2⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hiT, hic⟩, hip⟩
  have hTSm : (tailC hm n c).filter (fun j => j < p) ⊆ Sm := by
    intro i hi
    have h1 := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨mem_Icc_of_tailC hm n h1.1, (Finset.mem_filter.mp h1.1).2, h1.2⟩
  have hTeq : (tailC hm n c).filter (fun j => j < p) = Sm := Finset.Subset.antisymm hTSm hSmT
  by_cases hS1 : Sm.card ≤ 1
  · refine GV.sum _ fun j hj => hind j hj ?_
    have : (ellC hm n c : ℚ) ≤ nbC hm n c + 1 := by
      exact_mod_cast (by omega : ellC hm n c ≤ nbC hm n c + 1)
    have : (nbC hm n c : ℚ) ≤ is := by exact_mod_cast his
    push_cast;
    linarith
      -- the pair case
  have hSeq : Sm = {(c : ℕ), p - c} :=
    Finset.eq_of_subset_of_card_le (small_sub hm n) ((Finset.card_le_two).trans (by omega))
  have hcne : (c : ℕ) ≠ p - c := by omega
  have hmemc : (c : ℕ) ∈ Sm := by rw [hSeq]; simp
  have hmemb : p - (c : ℕ) ∈ Sm := by rw [hSeq]; simp
  have hcK := (Finset.mem_Icc.mp (Finset.mem_filter.mp hmemc).1).2
  have hbK := (Finset.mem_Icc.mp (Finset.mem_filter.mp hmemb).1).2
  rw [hTeq, hSeq, Finset.sum_pair hcne]
  refine pair_GV hp3 _ hc1 (by omega) hcne hcK hbK ?_ ?_
  · intro i hi hia hib
    have hi' := Finset.mem_Icc.mp hi
    by_cases hiN : i ≤ 3 * n
    · exact mem_entryO_small hm n (Finset.mem_Icc.mpr ⟨hi'.1, hiN⟩)
    have hiT : i ∈ tailO n := by unfold tailO; exact Finset.mem_Icc.mpr ⟨by omega, hi'.2⟩
    by_cases hic : jc hm i = c
    · refine mem_entryO_left hm n (mem_rootsO_big hm n his ?_)
      have hne : i ≠ p := by
        intro hh; rw [hh] at hic
        exact hc0 (hic ▸ (jc_eq_zero_iff hm p).mpr dvd_rfl)
      have hip : ¬i < p := fun hip =>
        by
        rcases jc_small_eq hm hip hic with h | h
        · exact hia h
        · exact hib h
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hiT, hic⟩, by omega⟩
    · exact mem_entryO_left hm n (mem_rootsO_other hm n hiT hic)
  · have hjb : p - (c : ℕ) ∈ tailC hm n c := (Finset.mem_filter.mp (hSmT hmemb)).1
    refine (VG_res_entry hm n hp3 hK hc0 hjb).mono ?_
    have : (ellC hm n c : ℚ) ≤ nbC hm n c + 2 := by
      exact_mod_cast (by omega : ellC hm n c ≤ nbC hm n c + 2)
    have : (nbC hm n c : ℚ) ≤ is := by exact_mod_cast his
    push_cast; linarith

lemma entryO_comm (c : Fin (m + 1)) (is it : ℕ) : entryO hm n c is c it = entryO hm n c it c is :=
  by unfold entryO; rw [add_right_comm]

/-- **The outer entry theorem.** -/
theorem outer_entry (hp7 : 7 ≤ p) (hK3 : 40 * n < 3 * p) (hK : 2 * (40 * n) < p ^ 2)
    (hpN : 3 * n < p) (cs : Fin (m + 1)) (is : ℕ) (ct : Fin (m + 1)) (it : ℕ) :
    GV p
      (μX (40 * n) (tpol (entryO hm n cs is ct it)) -
        C (μGe p (tpol (entryO hm n cs is ct it) /ₘ D (40 * n))))
      (wO hm n cs is + wO hm n ct it) := by
  have hp3 : 3 ≤ p := by omega
  have hw := add_nonpos (wO_nonpos hm n cs is) (wO_nonpos hm n ct it)
  rw [μX_sub_μGe]
  refine GV.add ((GV.C (VG_μpoly_sub_μGe (by omega) (GV_entry_quot hm n cs is ct it))).mono hw) ?_
  by_cases hc : cs = ct
  · subst hc
    rw [pole_sum_reduce]
    by_cases hc0 : cs = 0
    · subst hc0; exact pole_case_zero hm n hp7 hK3 hK hpN is it
    by_cases his : nbC hm n cs ≤ is
    · exact (pole_case_b hm n hp3 hK hpN hc0 his).mono hw
    by_cases hit : nbC hm n cs ≤ it
    · rw [entryO_comm]; exact (pole_case_b hm n hp3 hK hpN hc0 hit).mono hw
    exact pole_case_a hm n hp3 hK hc0 (by omega) (by omega)
  · rw [pole_sum_cross hm n hc]; exact (GV.zero _).mono hw

/-- **The outer-range bound** `v^G(Δ) ≥ 2 ∑ w − r`. -/
theorem outer_bound (hp7 : 7 ≤ p) (hK3 : 40 * n < 3 * p) (hK : 2 * (40 * n) < p ^ 2)
    (hpN : 3 * n < p) :
    GV p (Δ n)
      (2 * ∑ c, ∑ i ∈ range (LoC hm n c), wO hm n c i -
        ((37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) : ℕ) : ℚ)) := by
  classical
  have hcard : Fintype.card (Σ c : Fin (m + 1), Fin (LoC hm n c)) = 37 * n := by
    rw [Fintype.card_sigma]; simpa using sum_LoC hm n
  set e : (Σ c : Fin (m + 1), Fin (LoC hm n c)) ≃ Fin (37 * n) := Fintype.equivFinOfCardEq hcard
  have h :=
    outer_frame (p := p) (by omega) n (fun a => tpolZ (rootsO hm n (e.symm a).1 (e.symm a).2))
      (fun a => (natDegree_tpolZ _).trans_lt (card_rootsO hm n _ (e.symm a).2.isLt))
      (fun c : Fin (m + 1) => γO (p := p) c)
      (fun a b hab => sq_injective hm (by simpa [γO] using hab)) (LoC hm n)
      (fun a => (e.symm a).1) (fun a => (e.symm a).2) (fun a => (e.symm a).2.isLt)
      (fun a b h1 h2 => by
        apply e.symm.injective
        exact Sigma.ext h1 (by rw [Fin.heq_ext_iff (by rw [h1])]; exact h2))
      (fun a => rootsO_map_ZMod hm n _ _) (fun a => wO hm n (e.symm a).1 (e.symm a).2)
      (fun a => wO_nonpos hm n _ _)
      (fun a b => by
        rw [entryO_eq]
        exact outer_entry hm n hp7 hK3 hK hpN _ _ _ _)
  have hsum :
    ∑ a, wO hm n (e.symm a).1 (e.symm a).2 = ∑ c, ∑ i ∈ range (LoC hm n c), wO hm n c i := by
    rw [Equiv.sum_comp e.symm (fun s => wO hm n s.1 s.2), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun c _ => ?_
    exact Fin.sum_univ_eq_sum_range (fun i => wO hm n c i) _
  rw [hsum] at h
  exact h

end Zeta5Irrational

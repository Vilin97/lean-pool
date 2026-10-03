/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Arith.Val
public import LeanPool.Zeta5Irrational.Construction
import LeanPool.Zeta5Irrational.Arith.DirectBound
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF

/-! # Valuations of the pole values `μ_X(1/(t + j²)) = j⁴(X - H⁽⁵⁾_j) - 1/4 + 1/(2j)`
-/

public section

open Finset Polynomial

namespace Zeta5Irrational

variable {p : ℕ} [hp : Fact p.Prime]

/-- `v_p(1/u) ≥ -e` if `v_p(u) ≤ e`. -/
lemma VG_inv_nat_le {u : ℕ} (hu : u ≠ 0) {e : ℕ} (he : padicValNat p u ≤ e) :
    VG p ((u : ℚ)⁻¹) (-(e : ℚ)) := by
  refine VG.inv (by exact_mod_cast hu) ?_
  rw [padicValRat.of_nat]; exact_mod_cast he

omit hp in
lemma padicValNat_lt_p {u : ℕ} (hu : 1 ≤ u) (hup : u < p) : padicValNat p u = 0 :=
  padicValNat.eq_zero_of_not_dvd fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)

lemma padicValNat_lt_sq {u : ℕ} (hu : 1 ≤ u) (hup : u < p ^ 2) : padicValNat p u ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have : p ^ 2 ∣ u := (padicValNat_dvd_iff_le (by omega)).mpr h
  exact absurd (Nat.le_of_dvd (by omega) this) (by omega)

lemma VG_H5_lt {j : ℕ} (hj : j < p) : VG p (H5 j) 0 := by
  unfold H5
  refine VG.sum _ fun u hu => ?_
  have hu' := Finset.mem_Icc.mp hu
  rw [one_div, show ((u : ℚ) ^ 5) = ((u ^ 5 : ℕ) : ℚ) by push_cast; ring]
  refine (VG_inv_nat_le (e := 0) (pow_ne_zero _ (by omega)) ?_).mono (by norm_num)
  rw [padicValNat.pow (p := p) u 5, padicValNat_lt_p hu'.1 (by omega)]

lemma VG_quarter (hp3 : 3 ≤ p) : VG p (1 / 4 : ℚ) 0 := by
  rw [one_div, show (4 : ℚ) = ((4 : ℕ) : ℚ) by norm_num]
  refine (VG_inv_nat_le (e := 0) (by norm_num) ?_).mono (by norm_num)
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.pow (p := p) 2 2]
  have := Fact.mk Nat.prime_two
  rw [padicValNat_primes (p := p) (q := 2) (by omega)]

lemma VG_inv_2j (hp3 : 3 ≤ p) {j e : ℕ} (hj : 1 ≤ j) (he : padicValNat p j ≤ e) :
    VG p (1 / (2 * (j : ℚ))) (-(e : ℚ)) := by
  rw [one_div, show (2 * (j : ℚ)) = ((2 * j : ℕ) : ℚ) by push_cast; ring]
  refine VG_inv_nat_le (by omega) ?_
  have := Fact.mk Nat.prime_two
  rw [padicValNat.mul (by norm_num) (by omega), padicValNat_primes (p := p) (q := 2) (by omega)]
  omega

/-- Integral pole values for `1 ≤ j < p`. -/
lemma GV_poleValue_lt (hp3 : 3 ≤ p) {j : ℕ} (hj : 1 ≤ j) (hjp : j < p) : GV p (poleValue j) 0 := by
  unfold poleValue
  have h1 : GV p (C ((j : ℚ) ^ 4) * (X - C (H5 j))) 0 := by
    have := GV.C_mul (VG.natCast (p := p) (j ^ 4)) (GV.X.sub (GV.C (VG_H5_lt hjp)))
    simpa using this
  refine (h1.sub (GV.C (VG_quarter hp3))).add (GV.C ?_)
  have := VG_inv_2j hp3 hj (e := 0) (by rw [padicValNat_lt_p hj hjp])
  simpa using this

/-- Pole values `≥ -5` for `1 ≤ j < p²`. -/
lemma GV_poleValue_sq (hp3 : 3 ≤ p) {j : ℕ} (hj : 1 ≤ j) (hjp : j < p ^ 2) :
    GV p (poleValue j) (-5) := by
  unfold poleValue
  have h1 : GV p (C ((j : ℚ) ^ 4) * (X - C (H5 j))) (-5) := by
    have :=
      GV.C_mul (VG.natCast (p := p) (j ^ 4)) ((GV.X.mono (by norm_num)).sub (GV.C (VG_H5 hjp)))
    simpa using this
  refine (h1.sub ((GV.C (VG_quarter hp3)).mono (by norm_num))).add (GV.C ?_)
  exact (VG_inv_2j hp3 hj (e := 1) (padicValNat_lt_sq hj hjp)).mono (by norm_num)

/-- Pole values `≥ -1` for `j = p k`, `1 ≤ k < p`. -/
lemma GV_poleValue_mul (hp3 : 3 ≤ p) {k : ℕ} (hk : 1 ≤ k) (hkp : k < p) :
    GV p (poleValue (p * k)) (-1) := by
  have hj : 1 ≤ p * k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hjp : p * k < p ^ 2 := by rw [sq]; exact Nat.mul_lt_mul_of_pos_left hkp (by omega)
  unfold poleValue
  have h4 : VG p (((p * k : ℕ) : ℚ) ^ 4) 4 := by
    right
    rw [padicValRat.pow, padicValRat.of_nat, padicValNat.mul (by omega) (by omega),
      padicValNat_self, padicValNat_lt_p hk hkp];
    norm_num
  have h1 : GV p (C (((p * k : ℕ) : ℚ) ^ 4) * (X - C (H5 (p * k)))) (-1) := by
    have := GV.C_mul h4 ((GV.X.mono (by norm_num)).sub (GV.C (VG_H5 hjp)))
    refine this.mono (by norm_num)
  refine (h1.sub ((GV.C (VG_quarter hp3)).mono (by norm_num))).add (GV.C ?_)
  exact VG_inv_2j hp3 hj (e := 1) (padicValNat_lt_sq hj hjp)

lemma VG_int_dvd_one {z : ℤ} (h : (p : ℤ) ∣ z) : VG p (z : ℚ) 1 :=
  VG_int_one h

/-- `1/(p-u)⁵ + 1/u⁵ ≡ 0 (mod p)`. -/
lemma VG_pair (_hp3 : 3 ≤ p) {u : ℕ} (hu : 1 ≤ u) (hup : u < p) :
    VG p (1 / ((p : ℚ) - u) ^ 5 + 1 / (u : ℚ) ^ 5) 1 := by
  have hpu : ((p : ℚ) - u) = ((p - u : ℕ) : ℚ) := by push_cast [Nat.cast_sub hup.le]; ring
  have hne1 : ((p - u : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : p - u ≠ 0)
  have hne2 : (u : ℚ) ≠ 0 := by exact_mod_cast (by omega : u ≠ 0)
  rw [hpu, div_add_div _ _ (pow_ne_zero _ hne1) (pow_ne_zero _ hne2), div_eq_mul_inv]
  have hnum : VG p (1 * (u : ℚ) ^ 5 + ((p - u : ℕ) : ℚ) ^ 5 * 1) 1 := by
    have :=
      VG_int_one (p := p) (z := (u : ℤ) ^ 5 + ((p : ℤ) - u) ^ 5)
        (by
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast
          rw [ZMod.natCast_self]; ring)
    convert this using 1
    push_cast [Nat.cast_sub hup.le]; ring
  have hden : VG p (((p - u : ℕ) : ℚ) ^ 5 * (u : ℚ) ^ 5)⁻¹ 0 := by
    rw [show ((p - u : ℕ) : ℚ) ^ 5 * (u : ℚ) ^ 5 = (((p - u) ^ 5 * u ^ 5 : ℕ) : ℚ) by
        push_cast;
        ring]
    have hA : (p - u) ^ 5 ≠ 0 := pow_ne_zero _ (by omega)
    have hB : u ^ 5 ≠ 0 := pow_ne_zero _ (by omega)
    refine (VG_inv_nat_le (e := 0) (mul_ne_zero hA hB) ?_).mono (by norm_num)
    rw [padicValNat.mul hA hB, padicValNat.pow (p := p) _ 5, padicValNat.pow (p := p) _ 5,
      padicValNat_lt_p (by omega) (by omega), padicValNat_lt_p hu hup]
  simpa using hnum.mul hden

/-- `H⁽⁵⁾_{p-1} ≡ 0 (mod p)`. -/
lemma VG_H5_pm1 (hp3 : 3 ≤ p) : VG p (H5 (p - 1)) 1 := by
  have h2 : 2 * H5 (p - 1) = ∑ u ∈ Icc 1 (p - 1), (1 / ((p : ℚ) - u) ^ 5 + 1 / (u : ℚ) ^ 5) := by
    unfold H5
    rw [Finset.sum_add_distrib, two_mul]
    congr 1
    apply Finset.sum_nbij' (fun u => p - u) (fun u => p - u)
    · intro u hu; simp only [Finset.mem_Icc] at hu ⊢
      omega
    · intro u hu; simp only [Finset.mem_Icc] at hu ⊢
      omega
    · intro u hu; simp only [Finset.mem_Icc] at hu
      omega
    · intro u hu; simp only [Finset.mem_Icc] at hu
      omega
    · intro u hu
      simp only [Finset.mem_Icc] at hu
      push_cast [Nat.cast_sub (show u ≤ p by omega)]; ring_nf
  have hsum : VG p (2 * H5 (p - 1)) 1 := by
    rw [h2];
    exact
      VG.sum _ fun u hu =>
        VG_pair hp3 (Finset.mem_Icc.mp hu).1 (by have := (Finset.mem_Icc.mp hu).2; omega)
  have hhalf : VG p ((1 / 2 : ℚ)) 0 := by
    rw [one_div, show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num]
    have := Fact.mk Nat.prime_two
    refine (VG_inv_nat_le (e := 0) (by norm_num) ?_).mono (by norm_num)
    rw [padicValNat_primes (p := p) (q := 2) (by omega)]
  have := hhalf.mul hsum
  rw [show 1 / 2 * (2 * H5 (p - 1)) = H5 (p - 1) by ring] at this
  simpa using this

lemma H5_succ' {j : ℕ} (hj : 1 ≤ j) : H5 j = H5 (j - 1) + 1 / (j : ℚ) ^ 5 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  unfold H5
  rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]

omit hp in
lemma H5_split {c : ℕ} (hc : 1 ≤ c) (hcp : c < p) :
    H5 (p - 1) = H5 (p - c) + ∑ u ∈ Icc 1 (c - 1), 1 / ((p : ℚ) - u) ^ 5 := by
  unfold H5
  rw [show Icc 1 (p - 1) = Ioc 0 (p - 1) from Finset.Icc_add_one_left_eq_Ioc 0 _,
    show Icc 1 (p - c) = Ioc 0 (p - c) from Finset.Icc_add_one_left_eq_Ioc 0 _]
  have h :=
    Finset.sum_Ioc_consecutive (fun k : ℕ => 1 / (k : ℚ) ^ 5) (Nat.zero_le (p - c))
      (show p - c ≤ p - 1 by omega)
  rw [← h]
  congr 1
  apply Finset.sum_nbij' (fun k => p - k) (fun u => p - u)
  · intro k hk; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢; omega
  · intro u hu; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hu ⊢; omega
  · intro k hk; simp only [Finset.mem_Ioc] at hk; omega
  · intro u hu; simp only [Finset.mem_Icc] at hu; omega
  · intro k hk
    simp only [Finset.mem_Ioc] at hk
    push_cast [Nat.cast_sub (show k ≤ p by omega)]
    ring_nf

/-- **The congruence** `poleValue (p - c) ≡ poleValue c (mod p)` for `1 ≤ c < p`. -/
theorem GV_poleValue_congr (hp3 : 3 ≤ p) {c : ℕ} (hc : 1 ≤ c) (hcp : c < p) :
    GV p (poleValue (p - c) - poleValue c) 1 := by
  set d := p - c with hd
  have hdq : (d : ℚ) = p - c := by rw [hd]; push_cast [Nat.cast_sub hcp.le]; ring
  have hc0 : (c : ℚ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  set S' := ∑ u ∈ Icc 1 (c - 1), 1 / ((p : ℚ) - u) ^ 5 with hS'
  set Sc := ∑ u ∈ Icc 1 (c - 1), 1 / (u : ℚ) ^ 5 with hSc
  have hHd : H5 d = H5 (p - 1) - S' := by rw [H5_split hc hcp]; ring
  have hHc : H5 c = Sc + 1 / (c : ℚ) ^ 5 := by rw [H5_succ' hc]; rfl
  set κ : ℚ :=
    -(d : ℚ) ^ 4 * H5 d + (c : ℚ) ^ 4 * H5 c + (1 / (2 * (d : ℚ)) - 1 / (2 * (c : ℚ))) with hκ
  have hκ' :
    κ =
      -(d : ℚ) ^ 4 * H5 (p - 1) + ((d : ℚ) ^ 4 - (c : ℚ) ^ 4) * S' +
          (c : ℚ) ^ 4 * ∑ u ∈ Icc 1 (c - 1), (1 / ((p : ℚ) - u) ^ 5 + 1 / (u : ℚ) ^ 5) +
        (1 / (2 * (c : ℚ)) + 1 / (2 * (d : ℚ))) := by
    rw [hκ, hHd, hHc, Finset.sum_add_distrib, ← hS', ← hSc]
    field_simp
    ring
  have hdiff : poleValue d - poleValue c = C ((d : ℚ) ^ 4 - (c : ℚ) ^ 4) * X + C κ := by
    unfold poleValue
    rw [hκ]
    ext n
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_C, coeff_X, mul_sub]
    split_ifs <;> ring
  rw [hdiff]
  have hd4 : VG p ((d : ℚ) ^ 4 - (c : ℚ) ^ 4) 1 := by
    have :=
      VG_int_one (p := p) (z := (d : ℤ) ^ 4 - (c : ℤ) ^ 4)
        (by
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast
          rw [hd, Nat.cast_sub hcp.le, ZMod.natCast_self]; ring)
    simpa using this
  refine (by simpa using GV.C_mul hd4 (GV.X (p := p)) : GV p _ 1).add (GV.C ?_)
  rw [hκ']
  have t1 : VG p (-(d : ℚ) ^ 4 * H5 (p - 1)) 1 := by
    have := ((VG.natCast (p := p) (d ^ 4)).mul (VG_H5_pm1 hp3)).neg
    rw [show -(d : ℚ) ^ 4 * H5 (p - 1) = -(((d ^ 4 : ℕ) : ℚ) * H5 (p - 1)) by push_cast; ring]
    simpa using this
  refine ((t1.add ?_).add ?_).add ?_
  · refine (hd4.mul (VG.sum (r := 0) _ fun u hu => ?_)).mono (by norm_num)
    have hu' := Finset.mem_Icc.mp hu
    have hu2 : u < p := by omega
    rw [show ((p : ℚ) - u) = ((p - u : ℕ) : ℚ) by
        push_cast [Nat.cast_sub (show u ≤ p by omega)];
        ring,
      one_div, show (((p - u : ℕ) : ℚ) ^ 5) = (((p - u) ^ 5 : ℕ) : ℚ) by push_cast; ring]
    refine
      (VG_inv_nat_le (e := 0) (pow_ne_zero _ (Nat.sub_ne_zero_of_lt hu2)) ?_).mono (by norm_num)
    rw [padicValNat.pow (p := p) _ 5,
      padicValNat_lt_p (Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hu2))
        (Nat.sub_lt (by omega) (by omega))]
  · have :=
      (VG.natCast (p := p) (c ^ 4)).mul
        (VG.sum (r := 1) _ fun u hu =>
          VG_pair hp3 (Finset.mem_Icc.mp hu).1
            (lt_of_le_of_lt (Finset.mem_Icc.mp hu).2 (lt_of_le_of_lt (Nat.sub_le c 1) hcp)))
    simpa using this
  · have e : 1 / (2 * (c : ℚ)) + 1 / (2 * (d : ℚ)) = (p : ℚ) * (1 / (2 * (c * d : ℕ) : ℚ)) := by
      push_cast; rw [hdq]
      have : ((p : ℚ) - c) ≠ 0 := by rw [← hdq]; exact hd0
      field_simp; ring
    rw [e]
    have hp1 : VG p (p : ℚ) 1 := by simpa using VG.primePow (p := p) 1
    refine
      (hp1.mul
            (VG_inv_2j (e := 0) hp3
              (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))) ?_)).mono
        (by norm_num)
    rw [padicValNat.mul (by omega) (by omega), padicValNat_lt_p hc hcp,
      padicValNat_lt_p (by omega) (by omega)]

end Zeta5Irrational

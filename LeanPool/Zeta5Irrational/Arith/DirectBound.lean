/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Arith.PoleFun
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.Basic

/-! # The direct valuation bound for `τ_X`

For `g = κ ∏_{ζ ∈ Z} (x - ζ) / ∏_{r ∈ Pl} (x - r)` with `p ≥ 5`, poles in the same residue class
differing by exactly one power of `p`, harmonic indices `< p²` and polynomial part of degree
`< p² - 1`:

`v_p^G(τ_X(g)) ≥ min_c (e_c - ℓ_c) - 4`,

where `e_c` (resp. `ℓ_c`) is the number of zeros (resp. poles) in the class `c` mod `p`.
This replaces the `p`-adic distribution formula of the paper (Lemmas 3.1–3.2).
-/

public section

open Finset Polynomial

namespace Zeta5Irrational

variable {p : ℕ} [hp : Fact p.Prime]

/-- The numerator `κ ∏_{ζ ∈ Z} (x - ζ)`. -/
@[expose] noncomputable def numOf (κ : ℚ) (Z : Multiset ℤ) : ℚ[X] :=
  C κ * (Z.map fun ζ : ℤ => X - C (ζ : ℚ)).prod

/-- Number of zeros in the class `c`. -/
@[expose] def cnt (p : ℕ) (Z : Multiset ℤ) (c : ZMod p) : ℕ :=
  (Z.filter fun ζ : ℤ => (ζ : ZMod p) = c).card

/-- Poles in the class `c`. -/
@[expose] def plc (p : ℕ) (Pl : Finset ℤ) (c : ZMod p) : Finset ℤ :=
  Pl.filter fun r : ℤ => (r : ZMod p) = c

/-! ### Integer valuations -/

lemma zmod_eq_iff_dvd {a b : ℤ} : (a : ZMod p) = b ↔ (p : ℤ) ∣ a - b := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact sub_eq_zero.symm

lemma VG_int_one {z : ℤ} (h : (p : ℤ) ∣ z) : VG p (z : ℚ) 1 := by
  by_cases hz : z = 0
  · left; simp [hz]
  right
  rw [padicValRat.of_int]
  have := (padicValInt_dvd_iff (p := p) 1 z).mp (by simpa using h)
  rcases this with h | h
  · exact absurd h hz
  · exact_mod_cast h

lemma padicValRat_int_eq_zero {z : ℤ} (h : ¬(p : ℤ) ∣ z) : padicValRat p (z : ℚ) = 0 := by
  rw [padicValRat.of_int]
  have hz : z ≠ 0 := fun h' => h (h' ▸ dvd_zero _)
  by_contra hne
  have h1 : 1 ≤ padicValInt p z := Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne)
  exact h (by simpa using (padicValInt_dvd_iff (p := p) 1 z).mpr (Or.inr h1))

lemma padicValRat_int_le_one {z : ℤ} (h2 : ¬(p : ℤ) ^ 2 ∣ z) : padicValRat p (z : ℚ) ≤ 1 := by
  rw [padicValRat.of_int]
  by_contra hne
  rw [not_le] at hne
  have : 2 ≤ padicValInt p z := by exact_mod_cast hne
  have hz : z ≠ 0 := by rintro rfl; simp at hne
  exact h2 ((padicValInt_dvd_iff (p := p) 2 z).mpr (Or.inr this))

lemma padicValRat_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
    induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValRat.mul (hf a (mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (mem_insert_of_mem hi)),
      ih fun i hi => hf i (mem_insert_of_mem hi)]

lemma VG.multiset_prod (s : Multiset ℚ) (b : ℚ → ℚ) (h : ∀ q ∈ s, VG p q (b q)) :
    VG p s.prod (s.map b).sum := by
  induction s using Multiset.induction_on with
  | empty => right; simp
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
    exact
      (h a (Multiset.mem_cons_self _ _)).mul (ih fun q hq => h q (Multiset.mem_cons_of_mem hq))

/-! ### The harmonic numbers -/

lemma VG_H5 {m : ℕ} (hm : m < p ^ 2) : VG p (H5 m) (-5) := by
  unfold H5
  refine VG.sum _ fun v hv => ?_
  rw [Finset.mem_Icc] at hv
  rw [one_div]
  apply VG.inv (pow_ne_zero _ (by exact_mod_cast (by omega : v ≠ 0)))
  rw [show ((v : ℚ) ^ 5) = ((v ^ 5 : ℕ) : ℚ) by push_cast; ring, padicValRat.of_nat,
    padicValNat.pow (p := p) v 5]
  have : padicValNat p v ≤ 1 := by
    by_contra hne
    rw [not_le] at hne
    have h2 : p ^ 2 ∣ v := (padicValNat_dvd_iff_le (by omega)).mpr hne
    exact absurd (Nat.le_of_dvd (by omega) h2) (by omega)
  push_cast
  have h3 : (padicValRat p (v : ℚ) : ℚ) ≤ 1 := by rw [padicValRat.of_nat]; exact_mod_cast this
  linarith

/-! ### Residues -/

lemma eval_numOf (κ : ℚ) (Z : Multiset ℤ) (x : ℚ) :
    (numOf κ Z).eval x = κ * (Z.map fun ζ : ℤ => x - (ζ : ℚ)).prod := by
  unfold numOf
  rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
  congr 2
  exact Multiset.map_congr rfl fun ζ _ => by simp

lemma VG_prod_sub (Z : Multiset ℤ) (x : ℤ) :
    VG p ((Z.map fun ζ : ℤ => (x : ℚ) - (ζ : ℚ)).prod) (cnt p Z (x : ZMod p)) := by
  induction Z using Multiset.induction_on with
  | empty => right; simp [cnt]
  | cons a Z ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    unfold cnt at ih ⊢
    rw [Multiset.filter_cons]
    split_ifs with h
    · rw [Multiset.card_add, Multiset.card_singleton]
      have h1 : VG p ((x : ℚ) - (a : ℚ)) 1 := by
        have := VG_int_one (p := p) ((zmod_eq_iff_dvd (p := p)).mp h.symm)
        simpa using this
      convert h1.mul ih using 1; push_cast; ring
    · rw [zero_add]
      have h1 : VG p ((x : ℚ) - (a : ℚ)) 0 := by simpa using VG.intCast (p := p) (x - a)
      simpa using h1.mul ih

lemma VG_eval_numOf (κ : ℚ) (hκ : VG p κ 0) (Z : Multiset ℤ) (x : ℤ) :
    VG p ((numOf κ Z).eval (x : ℚ)) (cnt p Z (x : ZMod p)) := by
  rw [eval_numOf]
  simpa using hκ.mul (VG_prod_sub Z x)

/-- Poles in the same class differ by exactly one power of `p`. -/
@[expose] def Sep (p : ℕ) (Pl : Finset ℤ) : Prop :=
  ∀ r ∈ Pl, ∀ s ∈ Pl, r ≠ s → (r : ZMod p) = s → ¬(p : ℤ) ^ 2 ∣ r - s

lemma padicValRat_denom_le (Pl : Finset ℤ) (hsep : Sep p Pl) {r : ℤ} (hr : r ∈ Pl) :
    (padicValRat p (∏ s ∈ Pl.erase r, ((r : ℚ) - s)) : ℚ) ≤ (plc p Pl r).card - 1 := by
  rw [padicValRat_finset_prod _ _
      (fun s hs => by
        rw [Finset.mem_erase] at hs
        exact sub_ne_zero.mpr (by exact_mod_cast hs.1.symm))]
  have hterm :
    ∀ s ∈ Pl.erase r, (padicValRat p ((r : ℚ) - s) : ℚ) ≤ if (s : ZMod p) = r then 1 else 0 := by
    intro s hs
    rw [Finset.mem_erase] at hs
    have e : ((r : ℚ) - s) = ((r - s : ℤ) : ℚ) := by push_cast; ring
    rw [e]
    split_ifs with h
    · exact_mod_cast padicValRat_int_le_one (hsep r hr s hs.2 (Ne.symm hs.1) h.symm)
    · rw [padicValRat_int_eq_zero
          (fun hd =>
            h ((zmod_eq_iff_dvd (p := p)).mpr (by rw [← neg_sub]; exact (dvd_neg).mpr hd)))]
      simp
  push_cast
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_one]
  have hcard : ((Pl.erase r).filter fun s : ℤ => (s : ZMod p) = r) = (plc p Pl r).erase r := by
    unfold plc; rw [Finset.filter_erase]
  rw [hcard, Finset.card_erase_of_mem (by unfold plc; simp [hr])]
  have : 1 ≤ (plc p Pl r).card := Finset.card_pos.mpr ⟨r, by unfold plc; simp [hr]⟩
  push_cast [this]
  linarith

/-- **Residue bound**: `v_p(res_r) ≥ e_c - ℓ_c + 1` for the class `c` of `r`. -/
theorem VG_res (κ : ℚ) (hκ : VG p κ 0) (Z : Multiset ℤ) (Pl : Finset ℤ) (hsep : Sep p Pl) {r : ℤ}
    (hr : r ∈ Pl) : VG p (resP (numOf κ Z) Pl r) ((cnt p Z r : ℚ) - (plc p Pl r).card + 1) := by
  unfold resP
  rw [div_eq_mul_inv]
  have hD : ∏ s ∈ Pl.erase r, ((r : ℚ) - s) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun s hs =>
      by
      rw [Finset.mem_erase] at hs
      exact sub_ne_zero.mpr (by exact_mod_cast hs.1.symm)
  have h1 := VG_eval_numOf κ hκ Z r
  have h2 := VG.inv (p := p) hD (padicValRat_denom_le Pl hsep hr)
  convert h1.mul h2 using 1
  ring

end Zeta5Irrational

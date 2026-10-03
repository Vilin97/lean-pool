/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.Basic

/-! # A small `p`-adic valuation toolkit on `ℚ` and `ℚ[X]`

* `VG p q r` : `q = 0 ∨ r ≤ v_p(q)` (with a rational lower bound `r`);
* `GV p f r` : every coefficient of `f ∈ ℚ[X]` satisfies `VG p · r` (Gauss valuation bound);
* `det_GV` : if `M i j` has Gauss valuation `≥ ρ i + κ j`, then `det M` has `≥ ∑ ρ + ∑ κ`.
-/

public section

open Finset Polynomial

namespace Zeta5Irrational

variable {p : ℕ}

/-- `v_p(q) ≥ r` (vacuous for `q = 0`). -/
@[expose] def VG (p : ℕ) (q : ℚ) (r : ℚ) : Prop :=
  q = 0 ∨ r ≤ (padicValRat p q : ℚ)

namespace VG

lemma zero (r : ℚ) : VG p 0 r :=
  Or.inl rfl

lemma mono {q r s : ℚ} (h : VG p q r) (hs : s ≤ r) : VG p q s :=
  h.imp id fun h => hs.trans h

lemma neg {q r : ℚ} (h : VG p q r) : VG p (-q) r := by
  rcases h with h | h
  · left; simp [h]
  · right; rwa [padicValRat.neg]

lemma add [Fact p.Prime] {q q' r : ℚ} (h : VG p q r) (h' : VG p q' r) : VG p (q + q') r := by
  by_cases hq : q = 0
  · simpa [hq] using h'
  by_cases hq' : q' = 0
  · simpa [hq'] using h
  by_cases hs : q + q' = 0
  · exact Or.inl hs
  right
  have h1 := h.resolve_left hq
  have h2 := h'.resolve_left hq'
  have := padicValRat.min_le_padicValRat_add (p := p) hs
  have h3 : (min (padicValRat p q) (padicValRat p q') : ℚ) ≤ padicValRat p (q + q') := by
    exact_mod_cast this
  exact (le_min h1 h2).trans h3

lemma sub [Fact p.Prime] {q q' r : ℚ} (h : VG p q r) (h' : VG p q' r) : VG p (q - q') r := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

lemma mul [Fact p.Prime] {q q' r r' : ℚ} (h : VG p q r) (h' : VG p q' r') :
    VG p (q * q') (r + r') := by
  by_cases hq : q = 0
  · left; simp [hq]
  by_cases hq' : q' = 0
  · left; simp [hq']
  right
  rw [padicValRat.mul hq hq']
  push_cast
  exact add_le_add (h.resolve_left hq) (h'.resolve_left hq')

lemma sum [Fact p.Prime] {ι : Type*} (s : Finset ι) {f : ι → ℚ} {r : ℚ}
    (h : ∀ i ∈ s, VG p (f i) r) : VG p (∑ i ∈ s, f i) r := by
  classical
    induction s using Finset.induction_on with
  | empty => exact zero r
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact
      (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma prod [Fact p.Prime] {ι : Type*} (s : Finset ι) {f : ι → ℚ} {r : ι → ℚ}
    (h : ∀ i ∈ s, VG p (f i) (r i)) : VG p (∏ i ∈ s, f i) (∑ i ∈ s, r i) := by
  classical
    induction s using Finset.induction_on with
  | empty => right; simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact
      (h a (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma intCast (z : ℤ) : VG p (z : ℚ) 0 := by
  by_cases hz : z = 0
  · left; simp [hz]
  right
  rw [padicValRat.of_int]
  exact_mod_cast Nat.zero_le _

lemma natCast (n : ℕ) : VG p (n : ℚ) 0 := by exact_mod_cast intCast (p := p) (n : ℤ)

lemma one : VG p 1 0 := by exact_mod_cast natCast (p := p) 1

lemma inv [Fact p.Prime] {q r : ℚ} (_h : q ≠ 0) (hv : (padicValRat p q : ℚ) ≤ r) :
    VG p q⁻¹ (-r) := by
  right
  rw [padicValRat.inv]
  push_cast
  linarith

lemma of_eq {q : ℚ} (r : ℚ) (h : q ≠ 0 → r ≤ (padicValRat p q : ℚ)) : VG p q r := by
  by_cases hq : q = 0
  · exact Or.inl hq
  · exact Or.inr (h hq)

/-- `v_p(p^k) = k`. -/
lemma primePow [hp : Fact p.Prime] (k : ℤ) : VG p ((p : ℚ) ^ k) k := by
  right
  have : padicValRat p ((p : ℚ) ^ k) = k := by
    rw [padicValRat.zpow _, padicValRat.self hp.out.one_lt, mul_one]
  rw [this]

lemma zpow_mul [Fact p.Prime] {q r : ℚ} (k : ℤ) (h : VG p q r) : VG p ((p : ℚ) ^ k * q) (k + r) :=
  (primePow k).mul h

lemma pow [Fact p.Prime] {q r : ℚ} (h : VG p q r) (n : ℕ) : VG p (q ^ n) (n * r) := by
  induction n with
  | zero => right; simp
  | succ n ih => rw [pow_succ]; convert ih.mul h using 1; push_cast; ring

/-- A lower bound on the valuation of `1 / j` for `1 ≤ j ≤ n`. -/
lemma inv_nat [hp : Fact p.Prime] {j n : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) :
    VG p ((j : ℚ)⁻¹) (-(Nat.log p n : ℚ)) := by
  apply inv (by exact_mod_cast (by omega : j ≠ 0))
  rw [padicValRat.of_nat]
  have h1 : padicValNat p j ≤ Nat.log p j := by
    rcases Nat.eq_zero_or_pos (padicValNat p j) with h | h
    · rw [h]; exact Nat.zero_le _
    · have hdvd : p ^ padicValNat p j ∣ j := pow_padicValNat_dvd
      exact Nat.le_log_of_pow_le hp.out.one_lt (Nat.le_of_dvd (by omega) hdvd)
  have h2 : Nat.log p j ≤ Nat.log p n := Nat.log_mono_right hjn
  exact_mod_cast h1.trans h2

end VG

/-- Gauss valuation bound for polynomials in `X`. -/
@[expose] def GV (p : ℕ) (f : ℚ[X]) (r : ℚ) : Prop :=
  ∀ n, VG p (f.coeff n) r

namespace GV

lemma zero (r : ℚ) : GV p 0 r := fun n => by simpa using VG.zero (p := p) r

lemma mono {f : ℚ[X]} {r s : ℚ} (h : GV p f r) (hs : s ≤ r) : GV p f s := fun n => (h n).mono hs

lemma add [Fact p.Prime] {f g : ℚ[X]} {r : ℚ} (hf : GV p f r) (hg : GV p g r) : GV p (f + g) r :=
  fun n => by rw [coeff_add]; exact (hf n).add (hg n)

lemma neg {f : ℚ[X]} {r : ℚ} (hf : GV p f r) : GV p (-f) r := fun n => by
  rw [coeff_neg];
  exact (hf n).neg

lemma sub [Fact p.Prime] {f g : ℚ[X]} {r : ℚ} (hf : GV p f r) (hg : GV p g r) : GV p (f - g) r :=
  fun n => by rw [coeff_sub]; exact (hf n).sub (hg n)

lemma C {q r : ℚ} (h : VG p q r) : GV p (Polynomial.C q) r := fun n =>
  by
  rw [coeff_C]; split_ifs
  · exact h
  · exact VG.zero r

lemma X : GV p (X : ℚ[X]) 0 := fun n => by
  rw [coeff_X]; split_ifs
  · exact VG.one
  · exact VG.zero 0

lemma mul [Fact p.Prime] {f g : ℚ[X]} {r s : ℚ} (hf : GV p f r) (hg : GV p g s) :
    GV p (f * g) (r + s) := fun n => by
  rw [coeff_mul]
  exact VG.sum _ fun x _ => (hf x.1).mul (hg x.2)

lemma C_mul [Fact p.Prime] {q r s : ℚ} {f : ℚ[X]} (hq : VG p q r) (hf : GV p f s) :
    GV p (Polynomial.C q * f) (r + s) :=
  (C hq).mul hf

lemma sum [Fact p.Prime] {ι : Type*} (s : Finset ι) {f : ι → ℚ[X]} {r : ℚ}
    (h : ∀ i ∈ s, GV p (f i) r) : GV p (∑ i ∈ s, f i) r := fun n => by
  rw [finsetSum_coeff];
  exact VG.sum s fun i hi => h i hi n

lemma prod [Fact p.Prime] {ι : Type*} (s : Finset ι) {f : ι → ℚ[X]} {r : ι → ℚ}
    (h : ∀ i ∈ s, GV p (f i) (r i)) : GV p (∏ i ∈ s, f i) (∑ i ∈ s, r i) := by
  classical
    induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    simpa using C (p := p) (VG.one (p := p))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact
      (h a (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end GV

/-- **Determinant bound with row and column weights.** -/
theorem det_GV [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℚ[X])
    (ρ κ : ι → ℚ) (h : ∀ i j, GV p (M i j) (ρ i + κ j)) : GV p M.det (∑ i, ρ i + ∑ j, κ j) := by
  rw [Matrix.det_apply]
  refine GV.sum _ fun σ _ => ?_
  have hprod : GV p (∏ i, M (σ i) i) (∑ i, (ρ (σ i) + κ i)) := GV.prod _ fun i _ => h (σ i) i
  have e : ∑ i, (ρ (σ i) + κ i) = ∑ i, ρ i + ∑ j, κ j := by
    rw [Finset.sum_add_distrib, Equiv.sum_comp σ ρ]
  rw [e] at hprod
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]; exact hprod
  · rw [hs, Units.neg_smul, one_smul]; exact hprod.neg

end Zeta5Irrational

/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Arith.PoleFun
public import LeanPool.Zeta5Irrational.Degree
import LeanPool.Zeta5Irrational.PartialFractions
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Int.Star
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF

/-! # The pullback identity (3.1): `μ_X(R) = τ_X(x⁵ R(-x²))`

With `PlK K = {±1, …, ±K}` and `pull K P = (-1)^K x⁵ P(-x²)` we have
`μX K P = tauX (pull K P) (PlK K)` (`μX_eq_tauX`), since
`x⁵ P(-x²) / D_K(-x²) = pull K P / ∏_{r ∈ PlK K} (x - r)`.
-/

public section

open Finset Polynomial

namespace Zeta5Irrational

/-! ### Linearity of `τ` -/

lemma tau_add (P Q : ℚ[X]) : tau (P + Q) = tau P + tau Q := by
  unfold tau
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id,
    derivative_add, Lb_add]
  ring

lemma tau_C_mul (c : ℚ) (P : ℚ[X]) : tau (C c * P) = c * tau P := by
  unfold tau
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id,
    derivative_C_mul, Lb_C_mul]
  ring

lemma tau_neg (P : ℚ[X]) : tau (-P) = -tau P := by
  rw [show -P = C (-1) * P by simp, tau_C_mul];
  ring

lemma tau_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    tau (∑ i ∈ s, f i) = ∑ i ∈ s, tau (f i) := by
  classical
    induction s using Finset.induction_on with
  | empty => simp [tau, Lb]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, tau_add, ih]

lemma tau_X_pow (n : ℕ) : tau (X ^ n) = (n.descFactorial 3 : ℚ) * _root_.bernoulli (n - 3) / 24 :=
  by
  unfold tau
  rw [iterate_derivative_X_pow_eq_smul, Lb_smul, Lb_X_pow]

lemma tau_X_pow_odd (e : ℕ) : tau (C ((-1 : ℚ) ^ e) * X ^ (2 * e + 5)) = μmono e := by
  rw [tau_C_mul, tau_X_pow, μmono]
  rw [show 2 * e + 5 - 3 = 2 * e + 2 by omega,
    show (2 * e + 5).descFactorial 3 = (2 * e + 5) * (2 * e + 4) * (2 * e + 3) by
      simp [Nat.descFactorial]; ring]
  push_cast
  ring

/-- `τ(x⁵ Q(-x²)) = μ(Q)`. -/
lemma tau_pull_poly (Q : ℚ[X]) : tau (X ^ 5 * Q.comp (-X ^ 2)) = μpoly Q := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [add_comp, mul_add, tau_add, hP, hQ]
    unfold μpoly
    rw [Polynomial.sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring)]
  | monomial e a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp]
    have : X ^ 5 * (C a * (-X ^ 2) ^ e) = C a * (C ((-1 : ℚ) ^ e) * X ^ (2 * e + 5)) := by
      rw [neg_pow, ← pow_mul, map_pow, map_neg, map_one]; ring
    rw [this, tau_C_mul, tau_X_pow_odd]
    unfold μpoly
    rw [C_mul_X_pow_eq_monomial, Polynomial.sum_monomial_index _ _ (by simp)]

lemma tau_cubic (a : ℚ) : tau (-X ^ 3 - C a * X) = -1 / 4 := by
  rw [sub_eq_add_neg, tau_add, tau_neg, tau_neg, tau_C_mul, tau_X_pow,
    show (X : ℚ[X]) = X ^ 1 by ring, tau_X_pow]
  simp [Nat.descFactorial, _root_.bernoulli_zero]
  norm_num

/-! ### The pole set `{±1, …, ±K}` -/

/-- The poles `±1, …, ±K` in the variable `x`. -/
@[expose] def PlK (K : ℕ) : Finset ℤ :=
  (Icc 1 K).image (fun j : ℕ => (j : ℤ)) ∪ (Icc 1 K).image (fun j : ℕ => -(j : ℤ))

lemma PlK_disjoint (K : ℕ) :
    Disjoint ((Icc 1 K).image (fun j : ℕ => (j : ℤ))) ((Icc 1 K).image (fun j : ℕ => -(j : ℤ))) :=
  by
  rw [Finset.disjoint_left]
  intro r h1 h2
  rw [Finset.mem_image] at h1 h2
  obtain ⟨a, ha, rfl⟩ := h1
  obtain ⟨b, hb, hab⟩ := h2
  rw [Finset.mem_Icc] at ha hb
  omega

lemma sum_PlK {M : Type*} [AddCommMonoid M] (K : ℕ) (f : ℤ → M) :
    ∑ r ∈ PlK K, f r = ∑ j ∈ Icc 1 K, (f j + f (-j)) := by
  rw [PlK, Finset.sum_union (PlK_disjoint K),
    Finset.sum_image (fun a _ b _ h => by exact_mod_cast h),
    Finset.sum_image (fun a _ b _ h => by simpa using h), Finset.sum_add_distrib]

lemma prod_PlK {M : Type*} [CommMonoid M] (K : ℕ) (f : ℤ → M) :
    ∏ r ∈ PlK K, f r = ∏ j ∈ Icc 1 K, (f j * f (-j)) := by
  rw [PlK, Finset.prod_union (PlK_disjoint K),
    Finset.prod_image (fun a _ b _ h => by exact_mod_cast h),
    Finset.prod_image (fun a _ b _ h => by simpa using h), Finset.prod_mul_distrib]

lemma X_add_C_comp_neg_sq (a : ℚ) : (X + C a).comp (-X ^ 2) = -X ^ 2 + C a := by simp

lemma piPl_PlK (K : ℕ) : piPl (PlK K) = C ((-1 : ℚ) ^ K) * (D K).comp (-X ^ 2) := by
  unfold piPl D
  rw [prod_PlK, Polynomial.prod_comp,
    show C ((-1 : ℚ) ^ K) = ∏ j ∈ Icc 1 K, C (-1 : ℚ) by
      rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel, map_pow],
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [X_add_C_comp_neg_sq]
  push_cast
  rw [C_neg, C_pow, map_neg, map_one]
  ring

/-- `pull K P = (-1)^K x⁵ P(-x²)`. -/
@[expose] noncomputable def pull (K : ℕ) (P : ℚ[X]) : ℚ[X] :=
  C ((-1 : ℚ) ^ K) * X ^ 5 * P.comp (-X ^ 2)

lemma card_PlK (K : ℕ) : (PlK K).card = 2 * K := by
  rw [PlK, Finset.card_union_of_disjoint (PlK_disjoint K),
    Finset.card_image_of_injective _ (fun a b h => by exact_mod_cast h),
    Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  simp; ring

/-- The cofactor `B_j = (-1)^K ∏_{i ≠ j} (i² - x²)`. -/
noncomputable def Bj (K j : ℕ) : ℚ[X] :=
  C ((-1 : ℚ) ^ K) * (∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2))).comp (-X ^ 2)

lemma piPl_eq_Bj {K j : ℕ} (hj : j ∈ Icc 1 K) :
    piPl (PlK K) = (-X ^ 2 + C ((j : ℚ) ^ 2)) * Bj K j := by
  rw [piPl_PlK, Bj, D, ← Finset.mul_prod_erase _ _ hj, mul_comp, X_add_C_comp_neg_sq]; ring

lemma natDegree_Bj_le {K j : ℕ} (hj : j ∈ Icc 1 K) : (Bj K j).natDegree ≤ 2 * (K - 1) := by
  unfold Bj
  refine (natDegree_C_mul_le _ _).trans ?_
  refine natDegree_comp_le.trans ?_
  have h1 : (∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2))).natDegree ≤ K - 1 := by
    refine (natDegree_prod_le _ _).trans ?_
    refine
      (Finset.sum_le_sum fun (i : ℕ) _ => (natDegree_X_add_C (((i : ℕ) : ℚ) ^ 2)).le).trans ?_
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    rw [Finset.card_erase_of_mem hj]; simp
  have h2 : (-X ^ 2 : ℚ[X]).natDegree = 2 := by rw [natDegree_neg, natDegree_X_pow]
  rw [h2]; omega

/-- The polynomial part of the pulled-back function. -/
theorem polyPart_pull (K : ℕ) (P : ℚ[X]) :
    polyPart (pull K P) (PlK K) =
      X ^ 5 * (P /ₘ D K).comp (-X ^ 2) +
        ∑ j ∈ Icc 1 K, C (res K P j) * (-X ^ 3 - C ((j : ℚ) ^ 2) * X) := by
  unfold polyPart
  refine
    (div_modByMonic_unique _ (∑ j ∈ Icc 1 K, C (res K P j) * (C ((j : ℚ) ^ 4) * X * Bj K j))
        (piPl_monic _) ⟨?_, ?_⟩).1
  · have hP := modByMonic_add_div P (D K)
    rw [modByMonic_eq_sum_res] at hP
    conv_rhs => rw [pull, ← hP]
    rw [add_comp, mul_comp, Polynomial.sum_comp, piPl_PlK]
    simp only [mul_comp, C_comp, mul_add, Finset.mul_sum]
    have hj :
      ∀ j ∈ Icc 1 K,
        C ((-1 : ℚ) ^ K) * X ^ 5 *
            (C (res K P j) * (∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2))).comp (-X ^ 2)) =
          C (res K P j) * (C ((j : ℚ) ^ 4) * X * Bj K j) +
            C ((-1 : ℚ) ^ K) * (D K).comp (-X ^ 2) *
              (C (res K P j) * (-X ^ 3 - C ((j : ℚ) ^ 2) * X)) := by
      intro j hjK
      have := piPl_eq_Bj hjK
      rw [piPl_PlK] at this
      rw [this, Bj]
      have e : (C ((j : ℚ) ^ 4) : ℚ[X]) = C ((j : ℚ) ^ 2) * C ((j : ℚ) ^ 2) := by
        rw [← C_mul];
        ring_nf
      rw [e]; ring
    rw [Finset.sum_congr rfl hj, Finset.sum_add_distrib]
    ring
  · rw [degree_eq_natDegree (piPl_monic _).ne_zero, natDegree_piPl, card_PlK]
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp
    · refine (degree_le_natDegree).trans_lt ?_
      have :
        (∑ j ∈ Icc 1 K, C (res K P j) * (C ((j : ℚ) ^ 4) * X * Bj K j)).natDegree ≤ 2 * K - 1 := by
        refine natDegree_sum_le_of_forall_le _ _ fun j hjK => ?_
        refine (natDegree_C_mul_le _ _).trans ?_
        refine (natDegree_mul_le).trans ?_
        refine
          (Nat.add_le_add ((natDegree_C_mul_le _ _).trans natDegree_X_le)
                (natDegree_Bj_le hjK)).trans
            ?_
        omega
      exact_mod_cast (Nat.lt_of_le_of_lt this (by omega))

lemma prod_erase_eq_derivative (Pl : Finset ℤ) {r : ℤ} (hr : r ∈ Pl) :
    ∏ s ∈ Pl.erase r, ((r : ℚ) - s) = (derivative (piPl Pl)).eval (r : ℚ) := by
  have h := Lagrange.eval_nodal_derivative_eval_node_eq (s := Pl) (v := fun s : ℤ => (s : ℚ)) hr
  rw [show piPl Pl = Lagrange.nodal Pl (fun s : ℤ => (s : ℚ)) from rfl, h, Lagrange.eval_nodal]

lemma resP_pull (K : ℕ) (P : ℚ[X]) {r : ℤ} (hr : r ∈ PlK K) (hr0 : r ≠ 0) :
    resP (pull K P) (PlK K) r =
      -((r : ℚ) ^ 4 / 2) * (P.eval (-(r : ℚ) ^ 2) / (derivative (D K)).eval (-(r : ℚ) ^ 2)) := by
  unfold resP
  rw [prod_erase_eq_derivative _ hr, piPl_PlK, derivative_C_mul, derivative_comp, eval_mul,
    eval_C, eval_mul, eval_comp, pull, eval_mul, eval_mul, eval_C, eval_pow, eval_X, eval_comp]
  simp only [derivative_neg, derivative_X_pow, eval_neg, eval_mul, eval_C, eval_pow, eval_X]
  have hr0' : (r : ℚ) ≠ 0 := by exact_mod_cast hr0
  have hK : ((-1 : ℚ) ^ K) ≠ 0 := pow_ne_zero _ (by norm_num)
  by_cases hD : (derivative (D K)).eval (-(r : ℚ) ^ 2) = 0
  · rw [hD]; simp
  · field_simp
    norm_num
    ring

lemma dd_nat (j : ℕ) : dd (j : ℤ) = j := by simp [dd]

lemma dd_neg {j : ℕ} (hj : 1 ≤ j) : dd (-(j : ℤ)) = j - 1 := by
  unfold dd
  rw [ite_eq_right (by omega)]
  omega

lemma H5_succ_eq {j : ℕ} (hj : 1 ≤ j) : H5 j = H5 (j - 1) + 1 / (j : ℚ) ^ 5 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  unfold H5
  rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]

/--
**The pullback identity (3.1)**: `μ_X(P / D_K) = τ_X((-1)^K x⁵ P(-x²) / ∏_{r ∈ PlK} (x - r))`. -/
theorem μX_eq_tauX (K : ℕ) (P : ℚ[X]) : μX K P = tauX (pull K P) (PlK K) := by
  unfold μX tauX
  rw [polyPart_pull, tau_add, tau_pull_poly, tau_sum, sum_PlK]
  simp only [tau_C_mul, tau_cubic]
  rw [map_add, map_sum, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjP : (j : ℤ) ∈ PlK K := by
    rw [PlK, Finset.mem_union]; left;
    exact Finset.mem_image_of_mem _ hj
  have hjN : -(j : ℤ) ∈ PlK K := by
    rw [PlK, Finset.mem_union]; right;
    exact Finset.mem_image_of_mem _ hj
  rw [resP_pull K P hjP (by omega), resP_pull K P hjN (by omega), dd_nat, dd_neg hj1]
  have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  unfold poleValue res
  rw [H5_succ_eq hj1]
  push_cast
  ext n
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_C, coeff_X]
  split_ifs <;>
    first
    | omega
    | (field_simp; ring)

end Zeta5Irrational

/-
Copyright (c) 2026 jjaassoonn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jjaassoonn
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Positivity of generating-function coefficients (Theorem 1)

This file formalizes Theorem 1 of the Chebyshev-quotient / Demazure-multiplicity
paper: the coefficients of the generating function attached to a partition are
eventually positive, built from a Chebyshev-type polynomial recurrence and a
Dyck-path model.
-/

namespace Biswal.Theorem1

/-! ## Core Definitions -/

/-- The Chebyshev-type polynomial sequence `P n` over a commutative ring, defined by
`P 0 = P 1 = 1` and `P (n + 2) = P (n + 1) - X * P n`. -/
noncomputable def polyP (R : Type*) [CommRing R] : ℕ → Polynomial R
  | 0 => 1
  | 1 => 1
  | (n + 2) => polyP R (n + 1) - Polynomial.X * polyP R n

theorem polyP_zero (R : Type*) [CommRing R] : polyP R 0 = 1 := rfl

theorem polyP_one (R : Type*) [CommRing R] : polyP R 1 = 1 := rfl

theorem polyP_succ_succ (R : Type*) [CommRing R] (n : ℕ) :
    polyP R (n + 2) = polyP R (n + 1) - Polynomial.X * polyP R n := rfl

/-- The partition polynomial of `ξ`: the product of `polyP R` over the parts of `ξ`. -/
noncomputable def partitionPoly (R : Type*) [CommRing R] {s : ℕ}
    (ξ : Nat.Partition s) : Polynomial R :=
  (ξ.parts.map (polyP R)).prod

/-- The number of parts of `ξ` equal to `m`. -/
def countMaxParts (m : ℕ) {s : ℕ} (ξ : Nat.Partition s) : ℕ :=
  Multiset.count m ξ.parts

/-- The generating function attached to `ξ` with parameters `m` and `n`, as a power series. -/
noncomputable def genFun (K : Type*) [Field K] (m n : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) : PowerSeries K :=
  let n₁ := n / m
  let n₀ := n % m
  (↑(polyP K (m - n₀ - 1) * partitionPoly K ξ) : PowerSeries K) *
    ((↑(polyP K m) : PowerSeries K) ^ (n₁ + 1))⁻¹

/-- The `r`-th coefficient of the generating function `genFun K m n ξ`. -/
noncomputable def genFunCoeff (K : Type*) [Field K] (m n r : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) : K :=
  (PowerSeries.coeff r) (genFun K m n ξ)

/-! ## Basic Properties of polyP -/

lemma polyP_constantCoeff (R : Type*) [CommRing R] (n : ℕ) :
    (polyP R n).coeff 0 = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 | 1 => simp [polyP]
    | n + 2 =>
      simp [polyP] at ih ⊢
      simp_all

lemma polyP_coe_constantCoeff_ne_zero (K : Type*) [Field K] (m : ℕ) :
    PowerSeries.constantCoeff (↑(polyP K m) : PowerSeries K) ≠ 0 := by
  simp [polyP_constantCoeff]

lemma polyP_coe_pow_constantCoeff_ne_zero (K : Type*) [Field K] (m k : ℕ) :
    PowerSeries.constantCoeff ((↑(polyP K m) : PowerSeries K) ^ k) ≠ 0 := by
  rw [map_pow]
  exact pow_ne_zero _ (polyP_coe_constantCoeff_ne_zero K m)

lemma partitionPoly_eq_one_of_parts_le_one (K : Type*) [Field K] {s : ℕ}
    (ξ : Nat.Partition s) (h : ∀ i ∈ ξ.parts, i ≤ 1) :
    partitionPoly K ξ = 1 := by
  have h₁ : ∀ i ∈ ξ.parts, (polyP K i : Polynomial K) = 1 := by
    intro i hi
    rw [show i = 1 from by
      have := h i hi
      have := ξ.parts_pos hi
      omega, polyP_one]
  unfold partitionPoly
  rw [Multiset.map_congr rfl (fun x hx => h₁ x hx)]
  simp

private lemma partitionPoly_split_aux (K : Type*) [CommRing K] (m : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) :
    (ξ.parts.map (polyP K)).prod =
      polyP K m ^ Multiset.count m ξ.parts *
        ((ξ.parts.filter (fun x => ¬(x = m))).map (polyP K)).prod := by
  conv_lhs => rw [show ξ.parts = Multiset.filter (fun x => x = m) ξ.parts +
    Multiset.filter (fun x => ¬(x = m)) ξ.parts from
    (Multiset.filter_add_not (fun x => x = m) ξ.parts).symm]
  rw [Multiset.map_add, Multiset.prod_add, Multiset.filter_eq', Multiset.map_replicate,
    Multiset.prod_replicate]

lemma partitionPoly_split (K : Type*) [CommRing K] (m : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) :
    ∃ Q : Polynomial K,
      partitionPoly K ξ = polyP K m ^ countMaxParts m ξ * Q :=
  ⟨_, partitionPoly_split_aux K m ξ⟩

private lemma poly_mul_pow_inv_cancel (K : Type*) [Field K]
    (A P : Polynomial K) (t e : ℕ) (hte : e ≤ t)
    (hP : PowerSeries.constantCoeff (↑P : PowerSeries K) ≠ 0) :
    (↑A : PowerSeries K) * (↑P : PowerSeries K) ^ t *
      ((↑P : PowerSeries K) ^ e)⁻¹ =
    ↑(A * P ^ (t - e)) := by
  have hPe : PowerSeries.constantCoeff ((↑P : PowerSeries K) ^ e) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ hP
  conv_lhs => rw [show t = (t - e) + e from (Nat.sub_add_cancel hte).symm]
  rw [pow_add, mul_assoc (↑A : PowerSeries K) _ _, mul_assoc _ ((↑P : PowerSeries K) ^ e) _,
    PowerSeries.mul_inv_cancel _ hPe, mul_one, Polynomial.coe_mul, Polynomial.coe_pow]

lemma genFun_is_poly_coe (K : Type*) [Field K]
    (m n : ℕ) {s : ℕ} (ξ : Nat.Partition s) (_hm : 2 ≤ m) (_h_parts : ∀ i ∈ ξ.parts, i ≤ m)
    (h_t : n / m + 1 ≤ countMaxParts m ξ) :
    ∃ P : Polynomial K, genFun K m n ξ = ↑P := by
  obtain ⟨Q, hQ⟩ := partitionPoly_split K m ξ
  refine ⟨polyP K (m - n % m - 1) * Q * polyP K m ^ (countMaxParts m ξ - (n / m + 1)), ?_⟩
  unfold genFun
  simp only
  rw [hQ, show polyP K (m - n % m - 1) * (polyP K m ^ countMaxParts m ξ * Q) =
      (polyP K (m - n % m - 1) * Q) * polyP K m ^ countMaxParts m ξ from by ring,
    Polynomial.coe_mul, Polynomial.coe_pow]
  exact poly_mul_pow_inv_cancel K (polyP K (m - n % m - 1) * Q) (polyP K m)
    (countMaxParts m ξ) (n / m + 1) h_t (polyP_coe_constantCoeff_ne_zero K m)

lemma poly_coe_eventually_zero (K : Type*) [Field K] (P : Polynomial K) :
    ∀ r, P.natDegree < r → (PowerSeries.coeff r) (↑P : PowerSeries K) = 0 :=
  fun r h => by simp [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt h]

/-- The product of `polyP K` over the parts of `ξ` that are not equal to `m`. -/
noncomputable def nonMaxPartsPoly (K : Type*) [CommRing K] (m : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) : Polynomial K :=
  ((ξ.parts.filter (· ≠ m)).map (polyP K)).prod

private lemma partitionPoly_split_concrete (K : Type*) [CommRing K] (m : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) :
    partitionPoly K ξ = polyP K m ^ countMaxParts m ξ * nonMaxPartsPoly K m ξ := by
  simp only [partitionPoly, nonMaxPartsPoly, countMaxParts]
  conv_lhs => rw [(Multiset.filter_add_not (· = m) ξ.parts).symm]
  rw [Multiset.map_add, Multiset.prod_add, Multiset.filter_eq', Multiset.map_replicate,
    Multiset.prod_replicate]

lemma polyP_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) :
    Polynomial.map f (polyP R n) = polyP S n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 | 1 => simp [polyP]
    | n + 2 => simp_all [polyP]

private lemma numerator_with_factored_partition
    (m n : ℕ) {s : ℕ} (ξ : Nat.Partition s) (Q : Polynomial ℚ)
    (hQ : partitionPoly ℚ ξ = polyP ℚ m ^ countMaxParts m ξ * Q) :
    ↑(polyP ℚ (m - n % m - 1) * partitionPoly ℚ ξ) =
      ↑(polyP ℚ (m - n % m - 1) * Q) * (↑(polyP ℚ m) : PowerSeries ℚ) ^ countMaxParts m ξ := by
  rw [hQ]
  simp only [Polynomial.coe_mul, Polynomial.coe_pow]
  ring

private lemma pow_cancel_eq_inv_remaining (φ : PowerSeries ℚ) (t k : ℕ)
    (hφ : PowerSeries.constantCoeff φ ≠ 0) (ht : t ≤ k) :
    φ ^ t * (φ ^ k)⁻¹ = (φ ^ (k - t))⁻¹ := by
  have h1 : φ ^ k = φ ^ t * φ ^ (k - t) := by
    rw [← pow_add, Nat.add_sub_cancel' ht]
  have h2 : (φ ^ k)⁻¹ = (φ ^ (k - t))⁻¹ * (φ ^ t)⁻¹ := by
    rw [h1, PowerSeries.mul_inv_rev]
  have h5 : φ ^ t * (φ ^ t)⁻¹ = 1 := by
    apply PowerSeries.mul_inv_cancel
    rw [map_pow]
    exact pow_ne_zero _ hφ
  grind

private lemma genFun_rewrite_with_split
    (m n : ℕ) {s : ℕ} (ξ : Nat.Partition s) (_hm : 2 ≤ m) (h_t : countMaxParts m ξ ≤ n / m)
    (Q : Polynomial ℚ) (hQ : partitionPoly ℚ ξ = polyP ℚ m ^ countMaxParts m ξ * Q) :
    genFun ℚ m n ξ = ↑(polyP ℚ (m - n % m - 1) * Q) *
      ((↑(polyP ℚ m) : PowerSeries ℚ) ^ (n / m + 1 - countMaxParts m ξ))⁻¹ := by
  let B := (↑(polyP ℚ m) : PowerSeries ℚ)
  unfold genFun
  simp only []
  rw [numerator_with_factored_partition m n ξ Q hQ]
  have hB : PowerSeries.constantCoeff B ≠ 0 := polyP_coe_constantCoeff_ne_zero ℚ m
  conv_lhs => rw [mul_assoc]
  rw [pow_cancel_eq_inv_remaining B (countMaxParts m ξ) (n / m + 1) hB (by omega)]

private lemma second_factor_pos
    (m : ℕ) {s : ℕ} (ξ : Nat.Partition s) (_hm : 2 ≤ m) (h_parts : ∀ i ∈ ξ.parts, i ≤ m) (ρ : ℝ)
    (h_pos : ∀ j : ℕ, j < m →
      0 < Polynomial.eval ρ (Polynomial.map (algebraMap ℚ ℝ) (polyP ℚ j))) :
    0 < Polynomial.eval ρ
      (Polynomial.map (algebraMap ℚ ℝ) (nonMaxPartsPoly ℚ m ξ)) := by
  unfold nonMaxPartsPoly
  rw [Polynomial.map_multiset_prod, Polynomial.eval_multiset_prod, Multiset.map_map,
    Multiset.map_map]
  apply Multiset.prod_pos
  intro a ha
  rw [Multiset.mem_map] at ha
  obtain ⟨i, hi_mem, rfl⟩ := ha
  simp only [Function.comp]
  obtain ⟨hi_parts, hi_ne⟩ := Multiset.mem_filter.mp hi_mem
  exact h_pos i (lt_of_le_of_ne (h_parts i hi_parts) hi_ne)

lemma genFun_as_rational_fraction_with_pos_numerator
    (m n : ℕ) {s : ℕ} (ξ : Nat.Partition s) (hm : 2 ≤ m) (h_parts : ∀ i ∈ ξ.parts, i ≤ m)
    (h_t : countMaxParts m ξ ≤ n / m) :
    ∃ (A : Polynomial ℚ) (k : ℕ), 0 < k ∧
      genFun ℚ m n ξ = ↑A *
        ((↑(polyP ℚ m) : PowerSeries ℚ) ^ k)⁻¹ ∧
      (∀ (ρ : ℝ), 0 < ρ →
        Polynomial.eval ρ (Polynomial.map (algebraMap ℚ ℝ) (polyP ℚ m)) = 0 →
        (∀ j : ℕ, j < m →
          0 < Polynomial.eval ρ
            (Polynomial.map (algebraMap ℚ ℝ) (polyP ℚ j))) →
        0 < Polynomial.eval ρ (Polynomial.map (algebraMap ℚ ℝ) A)) := by
  set A := polyP ℚ (m - n % m - 1) * nonMaxPartsPoly ℚ m ξ
  set k := n / m + 1 - countMaxParts m ξ
  refine ⟨A, k, ?_, ?_, ?_⟩
  · omega
  · exact genFun_rewrite_with_split m n ξ hm h_t _ (partitionPoly_split_concrete ℚ m ξ)
  · intro ρ _hρ_pos _hρ_root h_pos_j
    rw [Polynomial.map_mul, Polynomial.eval_mul]
    exact mul_pos (h_pos_j (m - n % m - 1) (by omega)) (second_factor_pos m ξ hm h_parts ρ h_pos_j)

lemma coeff_rational_fraction_eq_proper_part
    (A D : Polynomial ℚ) (_hD : PowerSeries.constantCoeff (↑D : PowerSeries ℚ) ≠ 0) :
    ∃ (S R : Polynomial ℚ) (N : ℕ),
      (↑A : PowerSeries ℚ) * ((↑D : PowerSeries ℚ))⁻¹ =
        ↑S + ↑R * ((↑D : PowerSeries ℚ))⁻¹ ∧
      ∀ r, N < r →
        (PowerSeries.coeff r) ((↑A : PowerSeries ℚ) * ((↑D : PowerSeries ℚ))⁻¹) =
        (PowerSeries.coeff r) ((↑R : PowerSeries ℚ) * ((↑D : PowerSeries ℚ))⁻¹) := by
  exact ⟨0, A, 0, by simp, fun r _ => by simp_all⟩

/-! ## Trigonometric and Chebyshev Lemmas -/

private lemma angle_pos_lt_pi (m : ℕ) (hm : 2 ≤ m) (j : ℕ) (hj : j < m) :
    0 < (↑j + 1) * (Real.pi / (↑m + 1)) ∧
    (↑j + 1) * (Real.pi / (↑m + 1)) < Real.pi := by
  refine ⟨by positivity, ?_⟩
  have h₅₅ : ((j : ℝ) + 1) / ((m : ℝ) + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith [show (j : ℝ) < m from by exact_mod_cast hj]
  calc
    ((j : ℝ) + 1) * (Real.pi / ((m : ℝ) + 1)) = (((j : ℝ) + 1) / ((m : ℝ) + 1)) * Real.pi := by ring
    _ < 1 * Real.pi := by gcongr
    _ = Real.pi := by ring

private lemma sin_pi_div_succ_pos (m : ℕ) (hm : 2 ≤ m) :
    0 < Real.sin (Real.pi / (↑m + 1)) := by
  have h := angle_pos_lt_pi m hm 0 (by omega)
  simp only [Nat.cast_zero, zero_add, one_mul] at h
  exact Real.sin_pos_of_pos_of_lt_pi h.1 h.2

private lemma chebyshev_S_eval_pos_at_cos (m : ℕ) (hm : 2 ≤ m) (j : ℕ) (hj : j < m) :
    0 < Polynomial.eval (2 * Real.cos (Real.pi / (↑m + 1)))
      (Polynomial.Chebyshev.S ℝ ↑j) := by
  set θ := Real.pi / (↑m + 1) with hθ_def
  have hcheb := Polynomial.Chebyshev.S_two_mul_real_cos θ (↑j : ℤ)
  have hsin_θ : 0 < Real.sin θ := sin_pi_div_succ_pos m hm
  have ⟨hangle_pos, hangle_lt⟩ := angle_pos_lt_pi m hm j hj
  have hsin_jθ : 0 < Real.sin ((↑j + 1) * θ) := Real.sin_pos_of_pos_of_lt_pi hangle_pos hangle_lt
  have hprod : 0 < Polynomial.eval (2 * Real.cos θ) (Polynomial.Chebyshev.S ℝ ↑j) * Real.sin θ := by
    rw [hcheb]
    exact hsin_jθ
  exact (mul_pos_iff.mp hprod).elim (fun h => h.1)
    (fun h => absurd hsin_θ (not_lt.mpr (le_of_lt h.2)))

private lemma polyP_eval_eq_chebyshev_S (n : ℕ) (y : ℝ) (hy : y ≠ 0) :
    Polynomial.eval (1 / y ^ 2) (polyP ℝ n) =
      (1 / y ^ n) * Polynomial.eval y (Polynomial.Chebyshev.S ℝ ↑n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [polyP, Polynomial.Chebyshev.S_zero]
    | 1 =>
      simp [polyP, Polynomial.Chebyshev.S_one]
      field_simp [hy]
    | k + 2 =>
      simp [polyP, Polynomial.Chebyshev.S_add_two] at ih ⊢
      simp_all
      field_simp [hy, pow_add, pow_one, pow_mul, mul_assoc] at *
      ring_nf at *

/-! ## Root Analysis -/

lemma polyP_roots_positive (m : ℕ) (hm : 2 ≤ m) :
    ∃ (ρ : ℝ), 0 < ρ ∧
      Polynomial.eval ρ (Polynomial.map (algebraMap ℚ ℝ) (polyP ℚ m)) = 0 ∧
      (∀ j : ℕ, j < m →
        0 < Polynomial.eval ρ
          (Polynomial.map (algebraMap ℚ ℝ) (polyP ℚ j))) := by
  set y₀ := 2 * Real.cos (Real.pi / (↑m + 1))
  set ρ := 1 / y₀ ^ 2
  have hcos : (0 : ℝ) < Real.cos (Real.pi / (↑m + 1)) := by
    have h₁ : (m : ℝ) ≥ 2 := by exact_mod_cast hm
    have h_pos : 0 < Real.pi / (↑m + 1 : ℝ) := div_pos Real.pi_pos (by positivity)
    have h_lt : Real.pi / (↑m + 1 : ℝ) < Real.pi / 2 := by
      calc Real.pi / (↑m + 1) ≤ Real.pi / 3 :=
            div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) (by positivity) (by linarith)
        _ < Real.pi / 2 := by linarith [Real.pi_pos]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, h_lt⟩
  have hy₀_pos : 0 < y₀ := by positivity
  have hy₀_ne : y₀ ≠ 0 := hy₀_pos.ne'
  refine ⟨ρ, by positivity, ?_, ?_⟩
  · have : Polynomial.eval y₀ (Polynomial.Chebyshev.S ℝ ↑m) = 0 := by
      have h_formula := Polynomial.Chebyshev.S_two_mul_real_cos (Real.pi / (↑m + 1)) (↑m : ℤ)
      rw [show (↑(↑m : ℤ) + 1) * (Real.pi / (↑m + 1)) = Real.pi from by
        have : (m : ℝ) + 1 ≠ 0 := by positivity
        field_simp
        push_cast
        ring, Real.sin_pi] at h_formula
      exact (mul_eq_zero.mp h_formula).resolve_right (ne_of_gt (sin_pi_div_succ_pos m hm))
    rw [polyP_map (algebraMap ℚ ℝ), polyP_eval_eq_chebyshev_S m y₀ hy₀_ne, this]
    ring
  · intro j hj
    rw [polyP_map (algebraMap ℚ ℝ), polyP_eval_eq_chebyshev_S j y₀ hy₀_ne]
    exact mul_pos (by positivity) (chebyshev_S_eval_pos_at_cos m hm j hj)

lemma remainder_positive_at_roots
    (A D S R : Polynomial ℚ) (hdiv : (↑A : PowerSeries ℚ) * ((↑D : PowerSeries ℚ))⁻¹ =
        ↑S + ↑R * ((↑D : PowerSeries ℚ))⁻¹)
    (hD_ne : PowerSeries.constantCoeff (↑D : PowerSeries ℚ) ≠ 0)
    (ρ : ℝ) (hρ : Polynomial.eval ρ (Polynomial.map (algebraMap ℚ ℝ) D) = 0)
    (hA : 0 < Polynomial.eval ρ (Polynomial.map (algebraMap ℚ ℝ) A)) :
    0 < Polynomial.eval ρ (Polynomial.map (algebraMap ℚ ℝ) R) := by
  have h_main : (↑A : PowerSeries ℚ) = (S * D + R : Polynomial ℚ) := by
    have key := congr_arg (· * (↑D : PowerSeries ℚ)) hdiv
    simp only [add_mul, mul_assoc, PowerSeries.inv_mul_cancel _ hD_ne, mul_one] at key
    simp only [Polynomial.coe_add, Polynomial.coe_mul] at key ⊢
    exact key
  have h_poly : A = S * D + R := by exact_mod_cast h_main
  linarith [show Polynomial.eval ρ (Polynomial.map (algebraMap ℚ ℝ) A) =
    Polynomial.eval ρ (Polynomial.map (algebraMap ℚ ℝ) R) by
    rw [h_poly, Polynomial.map_add, Polynomial.map_mul, Polynomial.eval_add,
      Polynomial.eval_mul, hρ, mul_zero, zero_add]]

lemma pos_coeff_transfer_R_to_Q
    (f : PowerSeries ℚ) (N : ℕ) (h : ∀ r, N < r →
      (0 : ℝ) < (PowerSeries.coeff r) ((PowerSeries.map (algebraMap ℚ ℝ)) f)) :
    ∀ r, N < r → (0 : ℚ) < (PowerSeries.coeff r) f :=
  fun r hr => by
    have := h r hr
    rw [PowerSeries.coeff_map, eq_ratCast] at this
    exact_mod_cast this

lemma map_algebraMap_inv_comm
    (f : PowerSeries ℚ) (hf : PowerSeries.constantCoeff f ≠ 0) :
    (PowerSeries.map (algebraMap ℚ ℝ)) f⁻¹ =
    ((PowerSeries.map (algebraMap ℚ ℝ)) f)⁻¹ := by
  have hf' : PowerSeries.constantCoeff ((PowerSeries.map (algebraMap ℚ ℝ)) f) ≠ 0 := by
    simp [show PowerSeries.constantCoeff ((PowerSeries.map (algebraMap ℚ ℝ)) f) =
      (algebraMap ℚ ℝ) (PowerSeries.constantCoeff f) from rfl, hf]
  exact (PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hf')).mul_right_cancel
    ((by rw [← map_mul, PowerSeries.inv_mul_cancel f hf, map_one] :
      (PowerSeries.map (algebraMap ℚ ℝ)) f⁻¹ * (PowerSeries.map (algebraMap ℚ ℝ)) f = 1).trans
    (PowerSeries.inv_mul_cancel _ hf').symm)

lemma polyP_ne_zero (m : ℕ) : polyP ℝ m ≠ 0 :=
  fun h => one_ne_zero ((polyP_constantCoeff ℝ m).symm.trans (by rw [h, Polynomial.coeff_zero]))

lemma polyP_natDegree_le (n : ℕ) : (polyP ℝ n).natDegree ≤ n / 2 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 | 1 => simp [polyP]
    | n + 2 =>
      have h1 := ih (n + 1) (by omega)
      have h2 := ih n (by omega)
      have hX : (Polynomial.X * polyP ℝ n).natDegree ≤ 1 + n / 2 := by
        calc (Polynomial.X * polyP ℝ n).natDegree
            ≤ (Polynomial.X : Polynomial ℝ).natDegree + (polyP ℝ n).natDegree :=
              Polynomial.natDegree_mul_le
          _ ≤ 1 + n / 2 := by linarith [Polynomial.natDegree_X_le (R := ℝ)]
      change (polyP ℝ (n + 1) - Polynomial.X * polyP ℝ n).natDegree ≤ (n + 2) / 2
      calc (polyP ℝ (n + 1) - Polynomial.X * polyP ℝ n).natDegree
          ≤ max (polyP ℝ (n + 1)).natDegree (Polynomial.X * polyP ℝ n).natDegree :=
            Polynomial.natDegree_sub_le _ _
        _ ≤ max ((n + 1) / 2) (1 + n / 2) :=
            max_le_max h1 hX
        _ ≤ (n + 2) / 2 := by omega

lemma polyP_chebyshev_rescale (n : ℕ) (z : ℝ) (hz : z ≠ 0) :
    (2 * z) ^ n * Polynomial.eval (1 / (4 * z ^ 2)) (polyP ℝ n) =
    Polynomial.eval z (Polynomial.Chebyshev.U ℝ ↑n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 | 1 => norm_num [polyP]
    | (n + 2) =>
      have h₁ := ih n
      have h₂ := ih (n + 1)
      have h₃ : n < n + 2 := by omega
      have h₄ : n + 1 < n + 2 := by omega
      simp [polyP] at *
      simp_all [pow_add, pow_one, pow_two, mul_assoc]
      field_simp [hz, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X] at *
      ring_nf at *
      norm_num at *
      simp_all
      ring_nf at *
      norm_num at *
      field_simp [hz] at *
      ring_nf at *
      norm_num at *
      linarith

lemma angle_lt_pi_div_two (m k : ℕ) (_hm : 2 ≤ m) (hk_bound : 2 * k < m + 1) :
    ↑k * Real.pi / (↑m + 1) < Real.pi / 2 := by
  have : (k : ℝ) < ((m : ℝ) + 1) / 2 := by
    linarith [show (2 : ℝ) * k < m + 1 from by exact_mod_cast hk_bound]
  calc (k : ℝ) * Real.pi / (m + 1) = (k : ℝ) * (Real.pi / (m + 1)) := by ring
    _ < ((m + 1 : ℝ) / 2) * (Real.pi / (m + 1)) := by gcongr
    _ = Real.pi / 2 := by field_simp

lemma cos_angle_pos (m : ℕ) (hm : 2 ≤ m) (j : Fin (m / 2)) :
    0 < Real.cos ((↑(j : ℕ) + 1) * Real.pi / (↑m + 1)) := by
  apply Real.cos_pos_of_mem_Ioo
  refine ⟨by linarith [Real.pi_pos,
    show (0 : ℝ) ≤ (↑(j : ℕ) + 1) * Real.pi / (↑m + 1) from by positivity], ?_⟩
  exact_mod_cast angle_lt_pi_div_two m (↑j + 1) hm (by omega)

lemma angle_pos (m : ℕ) (_hm : 2 ≤ m) (j : Fin (m / 2)) :
    0 < (↑(j : ℕ) + 1) * Real.pi / (↑m + 1) := by positivity

lemma angle_lt_pi (m : ℕ) (hm : 2 ≤ m) (j : Fin (m / 2)) :
    (↑(j : ℕ) + 1) * Real.pi / (↑m + 1) < Real.pi := by
  have h₁ : (↑(j : ℕ) + 1 : ℝ) / (↑m + 1 : ℝ) < 1 := by
    rw [div_lt_one (by positivity)]
    exact_mod_cast (show (j : ℕ) + 1 < m + 1 by omega)
  calc (↑(j : ℕ) + 1 : ℝ) * Real.pi / (↑m + 1 : ℝ)
      = ((↑(j : ℕ) + 1 : ℝ) / (↑m + 1 : ℝ)) * Real.pi := by ring
    _ < 1 * Real.pi := by gcongr
    _ = Real.pi := one_mul _

lemma candidate_is_root (m : ℕ) (hm : 2 ≤ m) (j : Fin (m / 2)) :
    (polyP ℝ m).IsRoot (1 / (4 * Real.cos ((↑(j : ℕ) + 1) * Real.pi / (↑m + 1)) ^ 2)) := by
  set θ := (↑(j : ℕ) + 1) * Real.pi / (↑m + 1) with hθ_def
  set z := Real.cos θ with hz_def
  have hz_pos : 0 < z := cos_angle_pos m hm j
  have hz_ne : z ≠ 0 := hz_pos.ne'
  have hsin_pos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi (angle_pos m hm j) (angle_lt_pi m hm j)
  have hsin_ne : Real.sin θ ≠ 0 := hsin_pos.ne'
  rw [Polynomial.IsRoot.def]
  have h_rescale := polyP_chebyshev_rescale m z hz_ne
  have h2z_pos : 0 < 2 * z := by linarith
  have h2z_pow_ne : (2 * z) ^ m ≠ 0 := pow_ne_zero _ (ne_of_gt h2z_pos)
  suffices h_U_zero : Polynomial.eval z (Polynomial.Chebyshev.U ℝ ↑m) = 0 by
    rw [h_U_zero] at h_rescale
    exact mul_right_cancel₀ h2z_pow_ne (by linarith)
  have h_SU : Polynomial.eval z (Polynomial.Chebyshev.U ℝ ↑m) =
      Polynomial.eval (2 * z) (Polynomial.Chebyshev.S ℝ ↑m) := by
    rw [← Polynomial.Chebyshev.S_comp_two_mul_X]
    simp [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_ofNat]
  rw [h_SU]
  have h_trig := Polynomial.Chebyshev.S_two_mul_real_cos θ (↑m : ℤ)
  simp only [Int.cast_natCast] at h_trig
  have h_sin_zero :
      Real.sin ((↑m + 1 : ℝ) * ((↑(j : ℕ) + 1) * Real.pi / (↑m + 1))) = 0 := by
    rw [show (↑m + 1 : ℝ) * ((↑(j : ℕ) + 1) * Real.pi / (↑m + 1))
          = (↑(j : ℕ) + 1 : ℝ) * Real.pi from by
        field_simp [show (m : ℝ) + 1 ≠ 0 from by positivity],
      show (↑(j : ℕ) + 1 : ℝ) * Real.pi = (↑((j : ℕ) + 1) : ℤ) * Real.pi from by norm_cast]
    exact Real.sin_int_mul_pi _
  rw [h_sin_zero] at h_trig
  rw [hz_def]
  exact (mul_eq_zero.mp h_trig).resolve_right hsin_ne

lemma angle_strict_mono (m k_ρ k_x : ℕ) (_hm : 2 ≤ m) (hk_lt : k_ρ < k_x) :
    ↑k_ρ * Real.pi / (↑m + 1) < ↑k_x * Real.pi / (↑m + 1) := by
  nlinarith [show (k_ρ : ℝ) < (k_x : ℝ) from by norm_cast,
             show (0 : ℝ) < Real.pi / ((↑m : ℝ) + 1) from by positivity,
             show (k_ρ : ℝ) * Real.pi / ((↑m : ℝ) + 1)
               = (k_ρ : ℝ) * (Real.pi / ((↑m : ℝ) + 1)) from by ring,
             show (k_x : ℝ) * Real.pi / ((↑m : ℝ) + 1)
               = (k_x : ℝ) * (Real.pi / ((↑m : ℝ) + 1)) from by ring]

lemma candidate_strictMono (m : ℕ) (hm : 2 ≤ m) :
    StrictMono (fun j : Fin (m / 2) =>
      1 / (4 * Real.cos ((↑(j : ℕ) + 1) * Real.pi / (↑m + 1)) ^ 2)) := by
  intro j k hjk
  simp only
  have h_angle_lt : (↑(j : ℕ) + 1) * Real.pi / (↑m + 1) < (↑(k : ℕ) + 1) * Real.pi / (↑m + 1) := by
    have := angle_strict_mono m (↑j + 1) (↑k + 1) hm (by omega)
    push_cast at this ⊢
    exact this
  have hcos_j := cos_angle_pos m hm j
  have hcos_k := cos_angle_pos m hm k
  have h_cos_lt := Real.strictAntiOn_cos
    (⟨le_of_lt (angle_pos m hm j), le_of_lt (angle_lt_pi m hm j)⟩ : _ ∈ Set.Icc 0 Real.pi)
    (⟨le_of_lt (angle_pos m hm k), le_of_lt (angle_lt_pi m hm k)⟩ : _ ∈ Set.Icc 0 Real.pi)
    h_angle_lt
  have h_sq_lt : Real.cos ((↑(k : ℕ) + 1) * Real.pi / (↑m + 1)) ^ 2 <
      Real.cos ((↑(j : ℕ) + 1) * Real.pi / (↑m + 1)) ^ 2 := by
    rwa [sq_lt_sq₀ (le_of_lt hcos_k) (le_of_lt hcos_j)]
  exact one_div_lt_one_div_of_lt (by positivity) (by linarith)

/-! ## Coprimality and Splitting -/

lemma bezout_core (ρ : ℝ) (hρ_pos : 0 < ρ) (s : ℝ) (hs_pos : 0 < s) (Q : Polynomial ℝ) :
    Polynomial.C (1 / s) * ((Polynomial.X - Polynomial.C ρ) * Q + Polynomial.C s) +
    Polynomial.C (ρ / s) * Q * (-Polynomial.C (1 / ρ) * (Polynomial.X - Polynomial.C ρ)) = 1 := by
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hρ_ne : ρ ≠ 0 := ne_of_gt hρ_pos
  have hC_combine : Polynomial.C (ρ / s) * Polynomial.C (1 / ρ) = Polynomial.C (1 / s) := by
    rw [← Polynomial.C_mul]
    congr 1
    field_simp
  have hC_one : Polynomial.C (1 / s) * Polynomial.C s = 1 := by
    rw [← Polynomial.C_mul, one_div_mul_cancel hs_ne, map_one]
  calc Polynomial.C (1 / s) * ((Polynomial.X - Polynomial.C ρ) * Q + Polynomial.C s) +
    Polynomial.C (ρ / s) * Q * (-Polynomial.C (1 / ρ) * (Polynomial.X - Polynomial.C ρ))
      = Polynomial.C (1 / s) * ((Polynomial.X - Polynomial.C ρ) * Q)
          + Polynomial.C (1 / s) * Polynomial.C s +
        -(Polynomial.C (ρ / s) * Polynomial.C (1 / ρ)) * ((Polynomial.X - Polynomial.C ρ) * Q) := by
          ring
    _ = Polynomial.C (1 / s) * ((Polynomial.X - Polynomial.C ρ) * Q) + 1 +
        -(Polynomial.C (1 / s)) * ((Polynomial.X - Polynomial.C ρ) * Q) := by
          rw [hC_one, hC_combine]
    _ = 1 := by ring

lemma isCoprime_of_eval_pos (ρ : ℝ) (hρ_pos : 0 < ρ) (S : Polynomial ℝ)
    (hS_pos : 0 < Polynomial.eval ρ S) :
    IsCoprime S (Polynomial.X - Polynomial.C ρ) := by
  obtain ⟨Q, hQ⟩ : ∃ Q, S - Polynomial.C (Polynomial.eval ρ S) =
      (Polynomial.X - Polynomial.C ρ) * Q := by
    obtain ⟨Q, hQ⟩ := (Polynomial.dvd_iff_isRoot.mpr (by simp) :
      (Polynomial.X - Polynomial.C ρ) ∣ (S - Polynomial.C (Polynomial.eval ρ S)))
    exact ⟨Q, hQ⟩
  have hS_eq : S = (Polynomial.X - Polynomial.C ρ) * Q + Polynomial.C (Polynomial.eval ρ S) := by
    rwa [sub_eq_iff_eq_add] at hQ
  have hbez := bezout_core ρ hρ_pos (Polynomial.eval ρ S) hS_pos Q
  rw [← hS_eq] at hbez
  refine ⟨Polynomial.C (1 / Polynomial.eval ρ S),
    -(Polynomial.C (ρ / Polynomial.eval ρ S) * Q * Polynomial.C (1/ρ)), ?_⟩
  convert hbez using 1
  ring

lemma prod_linear_factors_dvd {p : Polynomial ℝ} {d : ℕ}
    (_hp : p ≠ 0) (r : Fin d → ℝ) (hr_pos : ∀ j, 0 < r j) (hr_mono : StrictMono r)
    (hr_root : ∀ j, p.IsRoot (r j)) (h_dvd : ∀ j, (Polynomial.X - Polynomial.C (r j)) ∣ p) :
    (∏ j : Fin d, (Polynomial.X - Polynomial.C (r j))) ∣ p := by
  induction d with
  | zero => exact one_dvd p
  | succ d ih =>
    rw [Fin.prod_univ_castSucc]
    set g := ∏ j : Fin d, (Polynomial.X - Polynomial.C (r (Fin.castSucc j)))
    set L := Polynomial.X - Polynomial.C (r (Fin.last d))
    apply IsCoprime.mul_dvd
    · apply isCoprime_of_eval_pos
      · exact hr_pos (Fin.last d)
      · rw [Polynomial.eval_prod]
        exact Finset.prod_pos fun j _ => by
          simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
          linarith [hr_mono (Fin.castSucc_lt_last j)]
    · exact ih (r ∘ Fin.castSucc)
        (fun j => hr_pos (Fin.castSucc j))
        (hr_mono.comp Fin.strictMono_castSucc)
        (fun j => hr_root (Fin.castSucc j))
        (fun j => h_dvd (Fin.castSucc j))
    · exact h_dvd (Fin.last d)

lemma splits_of_distinct_pos_roots_and_deg_le {p : Polynomial ℝ} {d : ℕ}
    (hp : p ≠ 0) (hdeg : p.natDegree ≤ d)
    (r : Fin d → ℝ) (hr_pos : ∀ j, 0 < r j) (hr_mono : StrictMono r)
    (hr_root : ∀ j, p.IsRoot (r j)) : p.Splits := by
  have h_prod_dvd : (∏ j : Fin d, (Polynomial.X - Polynomial.C (r j))) ∣ p :=
    prod_linear_factors_dvd hp r hr_pos hr_mono hr_root
      (fun j => Polynomial.dvd_iff_isRoot.mpr (hr_root j))
  obtain ⟨q, hpq⟩ := h_prod_dvd
  have hg_ne : (∏ j : Fin d, (Polynomial.X - Polynomial.C (r j))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => Polynomial.X_sub_C_ne_zero (r j)
  have hq_ne : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hpq
    exact hp hpq
  have hdeg_g : (∏ j : Fin d, (Polynomial.X - Polynomial.C (r j))).natDegree = d := by
    trans (∑ j : Fin d, (Polynomial.X - Polynomial.C (r j)).natDegree)
    · exact Polynomial.natDegree_prod _ _ (fun j _ => Polynomial.X_sub_C_ne_zero (r j))
    · simp
  have hdeg_pq : p.natDegree = d + q.natDegree := by
    rw [hpq, Polynomial.natDegree_mul hg_ne hq_ne, hdeg_g]
  have hq_const : q = Polynomial.C (q.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero (by omega)
  have hg_splits : (∏ j : Fin d, (Polynomial.X - Polynomial.C (r j))).Splits := by
    apply Polynomial.Splits.prod
    intro j _
    exact Polynomial.Splits.X_sub_C (r j)
  rw [hpq, hq_const, mul_comm]
  exact hg_splits.C_mul _

lemma polyP_root_to_chebyshev_root (m : ℕ) (r : ℝ) (hr_pos : 0 < r)
    (hr_root : Polynomial.eval r (polyP ℝ m) = 0) :
    let z := 1 / (2 * Real.sqrt r)
    0 < z ∧ Polynomial.eval z (Polynomial.Chebyshev.U ℝ ↑m) = 0 := by
  set z := 1 / (2 * Real.sqrt r)
  refine ⟨by positivity, ?_⟩
  have hz : z ≠ 0 := ne_of_gt (by positivity)
  have hrescale := polyP_chebyshev_rescale m z hz
  rw [show 1 / (4 * z ^ 2) = r from by grind, hr_root, mul_zero] at hrescale
  exact hrescale.symm

lemma cos_pos_angle_bound (m : ℕ) (hm : 2 ≤ m) (j : ℕ) (hj : j < m)
    (hcos_pos : 0 < Real.cos ((↑j + 1) * Real.pi / (↑m + 1))) :
    2 * (j + 1) < m + 1 := by
  have h₂ : (j + 1 : ℝ) * Real.pi / (m + 1 : ℝ) < Real.pi / 2 := by
    by_contra h
    have h₃ : Real.cos ((j + 1 : ℝ) * Real.pi / (m + 1 : ℝ)) ≤ 0 := by
      have h₄ : (j + 1 : ℝ) * Real.pi / (m + 1 : ℝ) ≤ Real.pi := by
        have h₅ : (j : ℝ) + 1 ≤ (m : ℝ) := by norm_cast
        calc
          (j + 1 : ℝ) * Real.pi / (m + 1 : ℝ) ≤ (m : ℝ) * Real.pi / (m + 1 : ℝ) := by gcongr
          _ ≤ Real.pi := by
            have h₆ : (m : ℝ) / (m + 1 : ℝ) ≤ 1 := by
              apply (div_le_one (by positivity)).mpr
              norm_cast
              omega
            calc
              (m : ℝ) * Real.pi / (m + 1 : ℝ) = ((m : ℝ) / (m + 1 : ℝ)) * Real.pi := by ring
              _ ≤ 1 * Real.pi := by gcongr
              _ = Real.pi := by ring
      apply Real.cos_nonpos_of_pi_div_two_le_of_le
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    linarith
  have h₃ : 2 * (j + 1 : ℝ) < (m + 1 : ℝ) := by
    have h₄ : (j + 1 : ℝ) * Real.pi < (Real.pi / 2) * (m + 1 : ℝ) := by
      calc
        (j + 1 : ℝ) * Real.pi = ((j + 1 : ℝ) * Real.pi / (m + 1 : ℝ)) * (m + 1 : ℝ) := by
          field_simp
        _ < (Real.pi / 2) * (m + 1 : ℝ) := by gcongr
    nlinarith [Real.pi_gt_three]
  norm_cast at h₃ ⊢

lemma chebyshev_root_parametrize (m : ℕ) (hm : 2 ≤ m) (z : ℝ) (hz_pos : 0 < z)
    (hz_root : Polynomial.eval z (Polynomial.Chebyshev.U ℝ ↑m) = 0) :
    ∃ k : ℕ, 1 ≤ k ∧ 2 * k < m + 1 ∧
    z = Real.cos (↑k * Real.pi / (↑m + 1)) := by
  have hU_ne : Polynomial.Chebyshev.U ℝ ↑m ≠ 0 :=
    Polynomial.Chebyshev.U_ne_zero ℝ ↑m (by omega)
  have hz_mem : z ∈ (Polynomial.Chebyshev.U ℝ ↑m).roots := by
    rwa [Polynomial.mem_roots hU_ne, Polynomial.IsRoot]
  rw [Polynomial.Chebyshev.roots_U_real] at hz_mem
  simp only [Finset.mem_val, Finset.mem_image, Finset.mem_range] at hz_mem
  obtain ⟨j, hj_lt, hj_eq⟩ := hz_mem
  refine ⟨j + 1, Nat.succ_le_succ (Nat.zero_le j), ?_, ?_⟩
  · exact cos_pos_angle_bound m hm j hj_lt (hj_eq ▸ hz_pos)
  · rw [show (↑(j + 1) : ℝ) = ↑j + 1 from by
      push_cast
      ring]
    exact hj_eq.symm

lemma polyP_root_parametrize (m : ℕ) (hm : 2 ≤ m) (r : ℝ) (hr_pos : 0 < r)
    (hr_root : Polynomial.eval r (polyP ℝ m) = 0) :
    ∃ k : ℕ, 1 ≤ k ∧ 2 * k < m + 1 ∧
    1 / (2 * Real.sqrt r) = Real.cos (↑k * Real.pi / (↑m + 1)) := by
  have ⟨hz_pos, hz_root⟩ := polyP_root_to_chebyshev_root m r hr_pos hr_root
  exact chebyshev_root_parametrize m hm _ hz_pos hz_root

lemma candidate_lt_m (m k : ℕ) (_hm : 2 ≤ m) (hk : 2 ≤ k) (hk_bound : 2 * k < m + 1) :
    (m + 1) / k < m := by
  by_contra h
  push Not at h
  have h₁ := Nat.div_mul_le_self (m + 1) k
  have h₂ : m * k ≤ (m + 1) / k * k := Nat.mul_le_mul_right k h
  nlinarith

lemma nat_ineq_div_mul (m k : ℕ) (hk : 2 ≤ k) :
    m + 1 < ((m + 1) / k + 1) * k := by
  calc m + 1 < (m + 1) / k * k + k := by
        apply Nat.lt_div_mul_add
        omega
    _ = ((m + 1) / k + 1) * k := by ring_nf

lemma angle_gt_pi (m k : ℕ) (hm : 2 ≤ m) (hk : 2 ≤ k) (_hk_bound : 2 * k < m + 1) :
    Real.pi < (↑((m + 1) / k) + 1) * (↑k * Real.pi / (↑m + 1)) := by
  have hm1_pos : (0 : ℝ) < ↑m + 1 := by positivity
  have hpi := Real.pi_pos
  rw [show (↑((m + 1) / k) + 1) * (↑k * Real.pi / (↑m + 1)) =
    Real.pi * ((↑((m + 1) / k) + 1) * ↑k / (↑m + 1)) by ring]
  rw [lt_mul_iff_one_lt_right hpi]
  rw [one_lt_div hm1_pos]
  have h := nat_ineq_div_mul m k hk
  have h' : (↑(m + 1) : ℝ) < ↑(((m + 1) / k + 1) * k) := Nat.cast_lt.mpr h
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h'
  linarith

lemma angle_lt_two_pi (m k : ℕ) (hm : 2 ≤ m) (hk : 2 ≤ k) (hk_bound : 2 * k < m + 1) :
    (↑((m + 1) / k) + 1) * (↑k * Real.pi / (↑m + 1)) < 2 * Real.pi := by
  have h₁ := Nat.div_mul_le_self (m + 1) k
  have h₂ : (↑((m + 1) / k) + 1 : ℝ) * (↑k : ℝ) < 2 * (↑m + 1 : ℝ) := by
    have : (↑(((m + 1) / k) * k) : ℝ) ≤ (↑(m + 1) : ℝ) := by exact_mod_cast h₁
    have : (↑k : ℝ) < (↑m + 1 : ℝ) := by exact_mod_cast (show k < m + 1 by omega)
    push_cast at *
    nlinarith
  rw [show (↑((m + 1) / k) + 1 : ℝ) * (↑k * Real.pi / (↑m + 1)) =
    ((↑((m + 1) / k) + 1 : ℝ) * ↑k) * (Real.pi / (↑m + 1)) from by ring]
  calc ((↑((m + 1) / k) + 1 : ℝ) * ↑k) * (Real.pi / (↑m + 1))
      < (2 * (↑m + 1 : ℝ)) * (Real.pi / (↑m + 1)) := by gcongr
    _ = 2 * Real.pi := by field_simp

lemma sin_nonpos_of_pi_lt_lt_two_pi (θ : ℝ) (h1 : Real.pi < θ) (h2 : θ < 2 * Real.pi) :
    Real.sin θ ≤ 0 := by
  have h1 := Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < θ - Real.pi) (by linarith)
  have h2 := Real.sin_add_pi (θ - Real.pi)
  simp only [sub_add_cancel] at h2
  linarith

lemma polyP_eval_nonpos_at_bad_index (m k j₀ : ℕ) (hm : 2 ≤ m)
    (hk : 2 ≤ k) (hk_bound : 2 * k < m + 1) (_hj₀ : j₀ < m) (r : ℝ) (hr_pos : 0 < r)
    (hr_param : 1 / (2 * Real.sqrt r) = Real.cos (↑k * Real.pi / (↑m + 1)))
    (h_sin : Real.sin ((↑j₀ + 1) * (↑k * Real.pi / (↑m + 1))) ≤ 0) :
    Polynomial.eval r (polyP ℝ j₀) ≤ 0 := by
  set θ := ↑k * Real.pi / (↑m + 1) with hθ_def
  have h₁ : (0 : ℝ) < ↑k * Real.pi / (↑m + 1) := by positivity
  have h₂ := angle_lt_pi_div_two m k (by omega) hk_bound
  have hcos_pos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, h₂⟩
  have hcos_ne : Real.cos θ ≠ 0 := ne_of_gt hcos_pos
  have hr_eq : r = 1 / (4 * Real.cos θ ^ 2) := by grind
  have hrescale := polyP_chebyshev_rescale j₀ (Real.cos θ) hcos_ne
  rw [hr_eq]
  have hU := Polynomial.Chebyshev.U_real_cos θ (↑j₀)
  have hsin_pos : 0 < Real.sin θ := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    have : (k : ℝ) / ((m : ℝ) + 1) < 1 := by
      rw [div_lt_one (by positivity)]
      exact_mod_cast (show k < m + 1 by omega)
    calc (k : ℝ) * Real.pi / (↑m + 1) = (k / (↑m + 1)) * Real.pi := by ring
      _ < 1 * Real.pi := by gcongr
      _ = Real.pi := one_mul _
  have h2cos_pos : 0 < (2 * Real.cos θ) ^ j₀ := by positivity
  have hprod_pos : 0 < (2 * Real.cos θ) ^ j₀ * Real.sin θ := mul_pos h2cos_pos hsin_pos
  simp only [Int.cast_natCast] at hU
  have key : (2 * Real.cos θ) ^ j₀ *
      Polynomial.eval (1 / (4 * Real.cos θ ^ 2)) (polyP ℝ j₀) *
      Real.sin θ = Real.sin ((↑j₀ + 1) * θ) := by
    nlinarith [hrescale, hU]
  nlinarith [h_sin, key, hprod_pos]

lemma polyP_roots_pos (m : ℕ) (_hm : 2 ≤ m) (x : ℝ)
    (hx : Polynomial.eval x (polyP ℝ m) = 0) : 0 < x := by
  by_contra h₅
  suffices ∀ (n : ℕ), Polynomial.eval x (polyP ℝ n) > 0 by linarith [this m]
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 | 1 => simp [polyP]
    | n + 2 =>
      simp [polyP, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X] at ih ⊢
      nlinarith [sq_nonneg (x + 1), ih (n + 1) (by omega), ih n (by omega)]

lemma root_index_eq_one (m : ℕ) (hm : 2 ≤ m) (ρ : ℝ) (hρ_pos : 0 < ρ)
    (hρ_lower : ∀ j : ℕ, j < m → 0 < Polynomial.eval ρ (polyP ℝ j))
    (k : ℕ) (hk_pos : 1 ≤ k) (hk_bound : 2 * k < m + 1)
    (hρ_param : 1 / (2 * Real.sqrt ρ) = Real.cos (↑k * Real.pi / (↑m + 1))) :
    k = 1 := by
  by_contra hk_ne
  have hk_ge : 2 ≤ k := by omega
  have ⟨j₀, hj₀_lt, hj₀_sin⟩ : ∃ j₀ : ℕ, j₀ < m ∧
      Real.sin ((↑j₀ + 1) * (↑k * Real.pi / (↑m + 1))) ≤ 0 :=
    ⟨(m + 1) / k, candidate_lt_m m k hm hk_ge hk_bound,
     sin_nonpos_of_pi_lt_lt_two_pi _ (angle_gt_pi m k hm hk_ge hk_bound)
       (angle_lt_two_pi m k hm hk_ge hk_bound)⟩
  have hle := polyP_eval_nonpos_at_bad_index m k j₀ hm hk_ge hk_bound hj₀_lt
    ρ hρ_pos hρ_param hj₀_sin
  linarith [hρ_lower j₀ hj₀_lt]

lemma sqrt_from_param (ρ : ℝ) (c : ℝ) (_hρ : 0 < ρ) (hc : 0 < c) (h : 1 / (2 * Real.sqrt ρ) = c) :
    Real.sqrt ρ = 1 / (2 * c) := by
  grind

lemma cos_pos_from_param (ρ : ℝ) (c : ℝ) (hρ : 0 < ρ) (h : 1 / (2 * Real.sqrt ρ) = c) :
    0 < c :=
  h ▸ by positivity

lemma root_comparison (m : ℕ) (hm : 2 ≤ m) (ρ x : ℝ) (hρ_pos : 0 < ρ) (hx_pos : 0 < x)
    (k_ρ k_x : ℕ) (hk_ρ_pos : 1 ≤ k_ρ) (_hk_ρ_bound : 2 * k_ρ < m + 1)
    (_hk_x_pos : 1 ≤ k_x) (hk_x_bound : 2 * k_x < m + 1)
    (hρ_param : 1 / (2 * Real.sqrt ρ) = Real.cos (↑k_ρ * Real.pi / (↑m + 1)))
    (hx_param : 1 / (2 * Real.sqrt x) = Real.cos (↑k_x * Real.pi / (↑m + 1))) (hk_lt : k_ρ < k_x) :
    ρ < x := by
  have h_angle_order := angle_strict_mono m k_ρ k_x hm hk_lt
  have h_angle_ρ_nn : 0 ≤ ↑k_ρ * Real.pi / (↑m + 1) := by positivity
  have h_angle_x_le_pi : ↑k_x * Real.pi / (↑m + 1) ≤ Real.pi :=
    le_of_lt (lt_of_lt_of_le (angle_lt_pi_div_two m k_x hm hk_x_bound)
      (div_le_self (le_of_lt Real.pi_pos) one_le_two))
  have h_cos_lt := Real.cos_lt_cos_of_nonneg_of_le_pi h_angle_ρ_nn h_angle_x_le_pi h_angle_order
  have h_cρ_pos := cos_pos_from_param ρ _ hρ_pos hρ_param
  have h_cx_pos := cos_pos_from_param x _ hx_pos hx_param
  have h_sqrt_ρ := sqrt_from_param ρ _ hρ_pos h_cρ_pos hρ_param
  have h_sqrt_x := sqrt_from_param x _ hx_pos h_cx_pos hx_param
  have h_sqrt_lt : Real.sqrt ρ < Real.sqrt x := by
    rw [h_sqrt_ρ, h_sqrt_x]
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  exact (Real.sqrt_lt_sqrt_iff (le_of_lt hρ_pos)).mp h_sqrt_lt

lemma root_is_smallest (m : ℕ) (hm : 2 ≤ m) (ρ : ℝ) (hρ_pos : 0 < ρ)
    (hρ_root : Polynomial.eval ρ (polyP ℝ m) = 0)
    (hρ_lower : ∀ j : ℕ, j < m → 0 < Polynomial.eval ρ (polyP ℝ j))
    (x : ℝ) (hx_root : Polynomial.eval x (polyP ℝ m) = 0) (hx_ne : x ≠ ρ) :
    ρ < x := by
  have hx_pos : 0 < x := polyP_roots_pos m hm x hx_root
  obtain ⟨k_ρ, hk_ρ_pos, hk_ρ_bound, hρ_param⟩ := polyP_root_parametrize m hm ρ hρ_pos hρ_root
  have hk_ρ_eq : k_ρ = 1 := root_index_eq_one m hm ρ hρ_pos hρ_lower k_ρ
    hk_ρ_pos hk_ρ_bound hρ_param
  subst hk_ρ_eq
  obtain ⟨k_x, hk_x_pos, hk_x_bound, hx_param⟩ := polyP_root_parametrize m hm x hx_pos hx_root
  have hk_x_ne : k_x ≠ 1 := by
    intro h
    subst h
    have h_eq : 1 / (2 * Real.sqrt x) = 1 / (2 * Real.sqrt ρ) := by rw [hx_param, hρ_param]
    have h_sqrt : Real.sqrt x = Real.sqrt ρ := by
      field_simp at h_eq
      linarith
    exact hx_ne ((Real.sqrt_inj (le_of_lt hx_pos) (le_of_lt hρ_pos)).mp h_sqrt)
  exact root_comparison m hm ρ x hρ_pos hx_pos 1 k_x hk_ρ_pos hk_ρ_bound hk_x_pos hk_x_bound
    hρ_param hx_param (by omega)

lemma L_eval_at_rho (ρ : ℝ) (hρ : 0 < ρ) :
    Polynomial.eval ρ (1 - Polynomial.C (1/ρ) * Polynomial.X : Polynomial ℝ) = 0 := by
  simp [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  field_simp [hρ.ne']
  ring

lemma eval_deriv_eq_neg_inv_rho_mul_eval_S (m : ℕ) (ρ : ℝ) (hρ_pos : 0 < ρ) (S : Polynomial ℝ)
    (hfact : polyP ℝ m = (1 - Polynomial.C (1 / ρ) * Polynomial.X) * S) :
    Polynomial.eval ρ (Polynomial.derivative (polyP ℝ m)) = -(1/ρ) * Polynomial.eval ρ S := by
  rw [hfact, Polynomial.derivative_mul]
  have h₁ : Polynomial.derivative (1 - Polynomial.C (1/ρ) * Polynomial.X : Polynomial ℝ)
      = -Polynomial.C (1/ρ) := by
    simp [Polynomial.derivative_sub, Polynomial.derivative_one]
  have h₂ : Polynomial.eval ρ (1 - Polynomial.C (1/ρ) * Polynomial.X : Polynomial ℝ) = 0 :=
    L_eval_at_rho ρ hρ_pos
  simp only [Polynomial.eval_add, Polynomial.eval_mul, h₁, h₂,
    Polynomial.eval_neg, Polynomial.eval_C]
  ring

/-! ## Derivative Convolution Identity -/

lemma polyP_neg_deriv_base_two (R : Type*) [CommRing R] :
    -Polynomial.derivative (polyP R 2) =
    ∑ j ∈ Finset.range 1, polyP R j * polyP R (0 - j) := by
  simp [polyP, mul_one, Polynomial.derivative_sub, Polynomial.derivative_one,
    Polynomial.derivative_X]

lemma polyP_neg_deriv_base_three (R : Type*) [CommRing R] :
    -Polynomial.derivative (polyP R 3) =
    ∑ j ∈ Finset.range 2, polyP R j * polyP R (1 - j) := by
  simp [polyP, Polynomial.derivative_sub, Polynomial.derivative_one,
    Polynomial.derivative_X, Finset.sum_range_succ]

lemma polyP_deriv_recurrence (R : Type*) [CommRing R] (n : ℕ) :
    Polynomial.derivative (polyP R (n + 2)) =
    Polynomial.derivative (polyP R (n + 1)) - polyP R n -
    Polynomial.X * Polynomial.derivative (polyP R n) := by
  calc Polynomial.derivative (polyP R (n + 2))
      = Polynomial.derivative (polyP R (n + 1) - Polynomial.X * polyP R n) := rfl
    _ = Polynomial.derivative (polyP R (n + 1)) -
        (1 * polyP R n + Polynomial.X * Polynomial.derivative (polyP R n)) := by
      rw [Polynomial.derivative_sub, Polynomial.derivative_mul]
      simp [Polynomial.derivative_X]
    _ = Polynomial.derivative (polyP R (n + 1)) - polyP R n -
        Polynomial.X * Polynomial.derivative (polyP R n) := by ring_nf

lemma inner_sum_recurrence (R : Type*) [CommRing R] (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), polyP R j * polyP R (n + 2 - j) =
    ∑ j ∈ Finset.range (n + 1), polyP R j * polyP R (n + 1 - j) -
    Polynomial.X * ∑ j ∈ Finset.range (n + 1), polyP R j * polyP R (n - j) := by
  have h1 : ∑ j ∈ Finset.range (n + 1), polyP R j * polyP R (n + 2 - j) =
    ∑ j ∈ Finset.range (n + 1), (polyP R j * polyP R (n + 1 - j) -
      Polynomial.X * (polyP R j * polyP R (n - j))) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ n := by
      simp [Finset.mem_range] at hj
      omega
    rw [show n + 2 - j = (n - j) + 2 from by omega, show n + 1 - j = (n - j) + 1 from by omega]
    simp only [polyP]
    ring
  rw [h1, Finset.sum_sub_distrib, Finset.mul_sum]

lemma convolution_sum_step (R : Type*) [CommRing R] (n : ℕ) :
    ∑ j ∈ Finset.range (n + 3), polyP R j * polyP R (n + 2 - j) =
    ∑ j ∈ Finset.range (n + 2), polyP R j * polyP R (n + 1 - j) +
    polyP R (n + 2) -
    Polynomial.X * ∑ j ∈ Finset.range (n + 1), polyP R j * polyP R (n - j) := by
  rw [Finset.sum_range_succ]
  simp only [show polyP R (n + 2 - (n + 2)) = polyP R 0 from by congr 1; omega,
             show polyP R 0 = (1 : Polynomial R) from rfl, mul_one]
  rw [Finset.sum_range_succ]
  simp only [show polyP R (n + 2 - (n + 1)) = polyP R 1 from by congr 1; omega,
             show polyP R 1 = (1 : Polynomial R) from rfl, mul_one]
  rw [inner_sum_recurrence]
  conv_rhs => rw [Finset.sum_range_succ]
  simp only [show polyP R (n + 1 - (n + 1)) = polyP R 0 from by congr 1; omega,
             show polyP R 0 = (1 : Polynomial R) from rfl, mul_one]
  ring

lemma polyP_neg_deriv_eq_convolution (R : Type*) [CommRing R] (n : ℕ) (hn : 2 ≤ n) :
    -Polynomial.derivative (polyP R n) =
    ∑ j ∈ Finset.range (n - 1), polyP R j * polyP R (n - 2 - j) := by
  have key : ∀ k, 2 ≤ k → -Polynomial.derivative (polyP R k) =
      ∑ j ∈ Finset.range (k - 1), polyP R j * polyP R (k - 2 - j) := by
    intro k hk
    induction k using Nat.strongRecOn with
    | _ k ih =>
    obtain ⟨k, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    match k with
    | 0 => exact polyP_neg_deriv_base_two R
    | 1 => exact polyP_neg_deriv_base_three R
    | k + 2 =>
      have ih1 := ih (k + 3) (by omega) (by omega)
      have ih2 := ih (k + 2) (by omega) (by omega)
      have hderiv := polyP_deriv_recurrence R (k + 2)
      have hconv := convolution_sum_step R k
      simp only [show k + 3 - 1 = k + 2 from by omega,
                  show k + 3 - 2 = k + 1 from by omega,
                  show k + 2 - 1 = k + 1 from by omega,
                  show k + 2 - 2 = k from by omega] at ih1 ih2
      change -Polynomial.derivative (polyP R (k + 4)) =
        ∑ j ∈ Finset.range (k + 3), polyP R j * polyP R (k + 2 - j)
      change Polynomial.derivative (polyP R (k + 4)) =
        Polynomial.derivative (polyP R (k + 3)) - polyP R (k + 2) -
        Polynomial.X * Polynomial.derivative (polyP R (k + 2)) at hderiv
      rw [hconv, ← ih1, ← ih2]
      linear_combination -hderiv
  exact key n hn

lemma eval_deriv_polyP_neg (m : ℕ) (hm : 2 ≤ m) (ρ : ℝ) (_hρ_pos : 0 < ρ)
    (hρ_lower : ∀ j : ℕ, j < m → 0 < Polynomial.eval ρ (polyP ℝ j)) :
    Polynomial.eval ρ (Polynomial.derivative (polyP ℝ m)) < 0 := by
  have hconv := polyP_neg_deriv_eq_convolution ℝ m hm
  have heval : Polynomial.eval ρ (-Polynomial.derivative (polyP ℝ m)) =
      ∑ j ∈ Finset.range (m - 1),
        Polynomial.eval ρ (polyP ℝ j) * Polynomial.eval ρ (polyP ℝ (m - 2 - j)) := by
    rw [hconv, Polynomial.eval_finsetSum]
    congr 1
    ext j
    exact Polynomial.eval_mul
  rw [Polynomial.eval_neg] at heval
  have hpos : 0 < ∑ j ∈ Finset.range (m - 1),
      Polynomial.eval ρ (polyP ℝ j) * Polynomial.eval ρ (polyP ℝ (m - 2 - j)) := by
    apply Finset.sum_pos
    · intro j hj
      rw [Finset.mem_range] at hj
      exact mul_pos (hρ_lower j (by omega)) (hρ_lower _ (by omega : m - 2 - j < m))
    · rw [Finset.nonempty_range_iff]
      omega
  linarith

lemma rho_not_root_of_S (m : ℕ) (hm : 2 ≤ m) (ρ : ℝ) (hρ_pos : 0 < ρ)
    (_hρ_root : Polynomial.eval ρ (polyP ℝ m) = 0)
    (hρ_lower : ∀ j : ℕ, j < m → 0 < Polynomial.eval ρ (polyP ℝ j)) (S : Polynomial ℝ)
    (hfact : polyP ℝ m = (1 - Polynomial.C (1/ρ) * Polynomial.X) * S) :
    Polynomial.eval ρ S ≠ 0 := by
  have hderiv := eval_deriv_eq_neg_inv_rho_mul_eval_S m ρ hρ_pos S hfact
  have hderiv_neg := eval_deriv_polyP_neg m hm ρ hρ_pos hρ_lower
  intro h
  rw [h, mul_zero] at hderiv
  linarith

lemma S_constantCoeff_from_fact (m : ℕ) (ρ : ℝ) (S : Polynomial ℝ)
    (hfact : polyP ℝ m = (1 - Polynomial.C (1 / ρ) * Polynomial.X) * S) :
    S.coeff 0 = 1 := by
  have h₁ : (polyP ℝ m).coeff 0 = 1 := polyP_constantCoeff ℝ m
  simp [hfact, Polynomial.coeff_mul, Polynomial.coeff_sub, Polynomial.coeff_one] at h₁
  linarith

lemma S_splits (m : ℕ) (hm : 2 ≤ m) (ρ : ℝ) (S : Polynomial ℝ)
    (hfact : polyP ℝ m = (1 - Polynomial.C (1 / ρ) * Polynomial.X) * S) :
    S.Splits := by
  have : (polyP ℝ m).Splits :=
    splits_of_distinct_pos_roots_and_deg_le (polyP_ne_zero m) (polyP_natDegree_le m)
      (fun j => 1 / (4 * Real.cos ((↑(j : ℕ) + 1) * Real.pi / (↑m + 1)) ^ 2))
      (fun j => by
        have := cos_angle_pos m hm j
        positivity)
      (candidate_strictMono m hm) (fun j => candidate_is_root m hm j)
  exact Polynomial.Splits.of_dvd this (polyP_ne_zero m)
    ⟨1 - Polynomial.C (1/ρ) * Polynomial.X, hfact.symm ▸ mul_comm _ _⟩

lemma eval_pos_from_splits_and_roots_gt
    (S : Polynomial ℝ) (ρ : ℝ) (hρ_pos : 0 < ρ) (_hS_ne : S ≠ 0) (_hS_splits : S.Splits)
    (hS_eval_zero : Polynomial.eval 0 S = 1)
    (hS_roots_gt : ∀ x : ℝ, Polynomial.eval x S = 0 → ρ < x) :
    0 < Polynomial.eval ρ S := by
  by_contra h
  have h₁ : Polynomial.eval ρ S ≤ 0 := by linarith
  have h₂ : ContinuousOn (fun x : ℝ => Polynomial.eval x S) (Set.Icc 0 ρ) := by
    apply Polynomial.continuousOn
  obtain ⟨y, hy, hy'⟩ : ∃ y ∈ Set.Icc 0 ρ, Polynomial.eval y S = 0 := by
    apply intermediate_value_Icc' (by linarith) h₂
    exact ⟨by simp_all, by simp_all⟩
  linarith [hS_roots_gt y hy', hy.2]

lemma roots_of_S_gt_rho_v2 (m : ℕ) (hm : 2 ≤ m) (ρ : ℝ) (hρ_pos : 0 < ρ)
    (hρ_root : Polynomial.eval ρ (polyP ℝ m) = 0)
    (hρ_lower : ∀ j : ℕ, j < m → 0 < Polynomial.eval ρ (polyP ℝ j)) (S : Polynomial ℝ)
    (hfact : polyP ℝ m = (1 - Polynomial.C (1/ρ) * Polynomial.X) * S)
    (x : ℝ) (hx : Polynomial.eval x S = 0) : ρ < x := by
  have hx_root : Polynomial.eval x (polyP ℝ m) = 0 := by
    rw [hfact, Polynomial.eval_mul, hx, mul_zero]
  have hx_ne : x ≠ ρ := by
    intro h
    have := rho_not_root_of_S m hm ρ hρ_pos hρ_root hρ_lower S hfact
    rw [← h] at this
    exact this hx
  exact root_is_smallest m hm ρ hρ_pos hρ_root hρ_lower x hx_root hx_ne

lemma S_eval_pos (m : ℕ) (hm : 2 ≤ m) (ρ : ℝ) (hρ_pos : 0 < ρ)
    (hρ_root : Polynomial.eval ρ (polyP ℝ m) = 0)
    (hρ_lower : ∀ j : ℕ, j < m → 0 < Polynomial.eval ρ (polyP ℝ j)) (S : Polynomial ℝ)
    (hfact : polyP ℝ m = (1 - Polynomial.C (1/ρ) * Polynomial.X) * S) :
    0 < Polynomial.eval ρ S :=
  eval_pos_from_splits_and_roots_gt S ρ hρ_pos
    (by intro h
        have := S_constantCoeff_from_fact m ρ S hfact
        rw [h, Polynomial.coeff_zero] at this
        exact one_ne_zero this.symm)
    (S_splits m hm ρ S hfact)
    (by rw [← Polynomial.coeff_zero_eq_eval_zero]; exact S_constantCoeff_from_fact m ρ S hfact)
    (roots_of_S_gt_rho_v2 m hm ρ hρ_pos hρ_root hρ_lower S hfact)

lemma L_constantCoeff (ρ : ℝ) :
    (1 - Polynomial.C (1/ρ) * Polynomial.X : Polynomial ℝ).coeff 0 = 1 := by
  simp

lemma L_eq_neg_C_mul (ρ : ℝ) (hρ : 0 < ρ) :
    1 - Polynomial.C (1 / ρ) * Polynomial.X =
    -Polynomial.C (1 / ρ) * (Polynomial.X - Polynomial.C ρ) := by
  apply Polynomial.funext
  intro x
  simp
  field_simp [hρ.ne']
  ring

/-! ## Factorization and Power Series Decomposition -/

lemma polyP_factor_at_root (m : ℕ) (hm : 2 ≤ m) (ρ : ℝ) (hρ_pos : 0 < ρ)
    (hρ_root : Polynomial.eval ρ (polyP ℝ m) = 0)
    (hρ_lower : ∀ j : ℕ, j < m → 0 < Polynomial.eval ρ (polyP ℝ j)) :
    ∃ (S : Polynomial ℝ),
      polyP ℝ m = (1 - Polynomial.C (1/ρ) * Polynomial.X) * S ∧
      0 < Polynomial.eval ρ S ∧
      IsCoprime (1 - Polynomial.C (1/ρ) * Polynomial.X) S ∧
      Polynomial.eval 0 S = 1 ∧
      (∀ x : ℝ, Polynomial.eval x S = 0 → ρ < x) ∧
      S.Splits := by
  have hlin : (1 - Polynomial.C (1/ρ) * Polynomial.X) ∣ polyP ℝ m := by
    rw [L_eq_neg_C_mul ρ hρ_pos, IsUnit.mul_left_dvd]
    · rwa [Polynomial.dvd_iff_isRoot]
    · exact (Polynomial.isUnit_C.mpr ((isUnit_iff_ne_zero.mpr
        (div_ne_zero one_ne_zero (ne_of_gt hρ_pos))))).neg
  obtain ⟨S, hS⟩ := hlin
  refine ⟨S, hS, ?_, ?_, ?_, ?_, ?_⟩
  · exact S_eval_pos m hm ρ hρ_pos hρ_root hρ_lower S hS
  · have hS_pos := S_eval_pos m hm ρ hρ_pos hρ_root hρ_lower S hS
    have hunit : IsUnit (-Polynomial.C (1 / ρ) : Polynomial ℝ) :=
      (Polynomial.isUnit_C.mpr
        (isUnit_iff_ne_zero.mpr (div_ne_zero one_ne_zero (ne_of_gt hρ_pos)))).neg
    rw [L_eq_neg_C_mul ρ hρ_pos]
    exact (isCoprime_mul_unit_left_left hunit _ _).mpr
      (isCoprime_of_eval_pos ρ hρ_pos S hS_pos).symm
  · rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact S_constantCoeff_from_fact m ρ S hS
  · exact roots_of_S_gt_rho_v2 m hm ρ hρ_pos hρ_root hρ_lower S hS
  · exact S_splits m hm ρ S hS

lemma coe_pow_constantCoeff_ne_zero (p : Polynomial ℝ) (k : ℕ) (hp : p.coeff 0 = 1) :
    PowerSeries.constantCoeff ((↑p : PowerSeries ℝ) ^ k) ≠ 0 := by
  simp [map_pow, hp]

lemma bezout_lift_to_ps (L S a b : Polynomial ℝ) (k : ℕ) (hbez : a * L ^ k + b * S ^ k = 1) :
    (↑a : PowerSeries ℝ) * (↑L : PowerSeries ℝ) ^ k +
    (↑b : PowerSeries ℝ) * (↑S : PowerSeries ℝ) ^ k = 1 := by
  calc (↑a : PowerSeries ℝ) * (↑L : PowerSeries ℝ) ^ k +
      (↑b : PowerSeries ℝ) * (↑S : PowerSeries ℝ) ^ k
      = (↑(a * L ^ k + b * S ^ k) : PowerSeries ℝ) := by
        simp [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_pow]
    _ = ↑(1 : Polynomial ℝ) := by rw [hbez]
    _ = 1 := by simp [Polynomial.coe_one]

lemma ps_decomp_core
    (R_rem : PowerSeries ℝ) (Lk Sk : PowerSeries ℝ) (hLk : PowerSeries.constantCoeff Lk ≠ 0)
    (hSk : PowerSeries.constantCoeff Sk ≠ 0) (a_ps b_ps : PowerSeries ℝ)
    (hbez : a_ps * Lk + b_ps * Sk = 1) :
    R_rem * (Lk * Sk)⁻¹ =
      R_rem * b_ps * Lk⁻¹ + R_rem * a_ps * Sk⁻¹ := by
  rw [PowerSeries.mul_inv_rev]
  have h1 : Sk * Sk⁻¹ = 1 := PowerSeries.mul_inv_cancel Sk hSk
  have h2 : Lk * Lk⁻¹ = 1 := PowerSeries.mul_inv_cancel Lk hLk
  have h3 : (a_ps * Lk + b_ps * Sk) * (Sk⁻¹ * Lk⁻¹) = Sk⁻¹ * Lk⁻¹ := by
    rw [hbez, one_mul]
  grind

lemma ps_decomp (R_rem : Polynomial ℝ) (k : ℕ) (_hk : 0 < k) (L S : Polynomial ℝ)
    (hL_const : L.coeff 0 = 1) (hS_const : S.coeff 0 = 1) (a b : Polynomial ℝ)
    (hbez : a * L ^ k + b * S ^ k = 1) (P : Polynomial ℝ) (hP : P = L * S) :
    (↑R_rem : PowerSeries ℝ) * ((↑P : PowerSeries ℝ) ^ k)⁻¹ =
      (↑(R_rem * b) : PowerSeries ℝ) * ((↑L : PowerSeries ℝ) ^ k)⁻¹ +
      (↑(R_rem * a) : PowerSeries ℝ) * ((↑S : PowerSeries ℝ) ^ k)⁻¹ := by
  have hLk_ne : PowerSeries.constantCoeff ((↑L : PowerSeries ℝ) ^ k) ≠ 0 :=
    coe_pow_constantCoeff_ne_zero L k hL_const
  have hSk_ne : PowerSeries.constantCoeff ((↑S : PowerSeries ℝ) ^ k) ≠ 0 :=
    coe_pow_constantCoeff_ne_zero S k hS_const
  have hbez_ps : (↑a : PowerSeries ℝ) * (↑L : PowerSeries ℝ) ^ k +
      (↑b : PowerSeries ℝ) * (↑S : PowerSeries ℝ) ^ k = 1 :=
    bezout_lift_to_ps L S a b k hbez
  rw [show (↑P : PowerSeries ℝ) ^ k = (↑L : PowerSeries ℝ) ^ k * (↑S : PowerSeries ℝ) ^ k
    from by rw [hP, Polynomial.coe_mul, mul_pow]]
  rw [ps_decomp_core (↑R_rem : PowerSeries ℝ)
    ((↑L : PowerSeries ℝ) ^ k) ((↑S : PowerSeries ℝ) ^ k)
    hLk_ne hSk_ne (↑a : PowerSeries ℝ) (↑b : PowerSeries ℝ) hbez_ps]
  simp only [Polynomial.coe_mul]

lemma bezout_eval_at_root (L S a b : Polynomial ℝ) (k : ℕ) (hk : 0 < k)
    (ρ : ℝ) (hL_zero : Polynomial.eval ρ L = 0) (hbez : a * L ^ k + b * S ^ k = 1) :
    Polynomial.eval ρ b * (Polynomial.eval ρ S) ^ k = 1 := by
  have h₁ : Polynomial.eval ρ a * (Polynomial.eval ρ L) ^ k +
      Polynomial.eval ρ b * (Polynomial.eval ρ S) ^ k = 1 := by
    have := congr_arg (Polynomial.eval ρ) hbez
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_one] at this
    exact this
  rw [hL_zero, zero_pow (by omega), mul_zero, zero_add] at h₁
  exact h₁

lemma bezout_fraction_split (m : ℕ) (_hm : 2 ≤ m) (R_rem : Polynomial ℝ) (k : ℕ) (hk : 0 < k)
    (ρ : ℝ) (hρ_pos : 0 < ρ) (hR_pos : 0 < Polynomial.eval ρ R_rem) (S : Polynomial ℝ)
    (hfact : polyP ℝ m = (1 - Polynomial.C (1 / ρ) * Polynomial.X) * S)
    (hS_pos : 0 < Polynomial.eval ρ S)
    (hCop : IsCoprime (1 - Polynomial.C (1 / ρ) * Polynomial.X) S) :
    ∃ (N_poly M_poly : Polynomial ℝ),
      let L : Polynomial ℝ := 1 - Polynomial.C (1/ρ) * Polynomial.X
      (↑R_rem : PowerSeries ℝ) * ((↑(polyP ℝ m) : PowerSeries ℝ) ^ k)⁻¹ =
        (↑N_poly : PowerSeries ℝ) * ((↑L : PowerSeries ℝ) ^ k)⁻¹ +
        (↑M_poly : PowerSeries ℝ) * ((↑S : PowerSeries ℝ) ^ k)⁻¹ ∧
      0 < Polynomial.eval ρ N_poly := by
  set L : Polynomial ℝ := 1 - Polynomial.C (1/ρ) * Polynomial.X with hL_def
  obtain ⟨a, b, hab⟩ := (hCop.pow : IsCoprime (L ^ k) (S ^ k))
  refine ⟨R_rem * b, R_rem * a, ?_, ?_⟩
  · exact ps_decomp R_rem k hk L S (L_constantCoeff ρ)
      (S_constantCoeff_from_fact m ρ S hfact) a b hab (polyP ℝ m) hfact
  · have hbS : Polynomial.eval ρ b * (Polynomial.eval ρ S) ^ k = 1 :=
      bezout_eval_at_root L S a b k hk ρ (L_eval_at_rho ρ hρ_pos) hab
    have hSk_pos : (Polynomial.eval ρ S) ^ k > 0 := pow_pos hS_pos k
    have hb_pos : 0 < Polynomial.eval ρ b := by
      by_contra h
      push Not at h
      have : Polynomial.eval ρ b * (Polynomial.eval ρ S) ^ k ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h (le_of_lt hSk_pos)
      linarith
    rw [Polynomial.eval_mul]
    exact mul_pos hR_pos hb_pos

lemma L_coe_eq_rescale_one_sub_X (ρ : ℝ) :
    let L : Polynomial ℝ := 1 - Polynomial.C (1/ρ) * Polynomial.X
    (↑L : PowerSeries ℝ) = PowerSeries.rescale (1/ρ) (1 - PowerSeries.X) := by
  intro L
  have h1 : (↑L : PowerSeries ℝ) = 1 - PowerSeries.C (1 / ρ) * PowerSeries.X := by
    simp [L, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_X]
  have h2 : PowerSeries.rescale (1 / ρ) (1 - PowerSeries.X)
      = 1 - PowerSeries.C (1 / ρ) * PowerSeries.X := by
    ext n
    simp [map_sub, map_one]
  grind

lemma one_sub_X_pow_constantCoeff_ne_zero (k : ℕ) :
    PowerSeries.constantCoeff ((1 - PowerSeries.X : PowerSeries ℝ) ^ k) ≠ 0 := by
  simp [map_pow]

lemma inv_one_sub_pow_eq_invOneSubPow (k : ℕ) :
    ((1 - PowerSeries.X : PowerSeries ℝ) ^ k)⁻¹ =
      ↑(PowerSeries.invOneSubPow ℝ k) := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one (one_sub_X_pow_constantCoeff_ne_zero k)]
  have h := PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val
    (S := ℝ) (d := 0) (e := k)
  simp [PowerSeries.invOneSubPow_zero] at h
  rwa [mul_comm]

lemma rescale_inv (a : ℝ) (f : PowerSeries ℝ) (hf : PowerSeries.constantCoeff f ≠ 0) :
    PowerSeries.rescale a (f⁻¹) = (PowerSeries.rescale a f)⁻¹ := by
  have hrf : PowerSeries.constantCoeff (PowerSeries.rescale a f) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale]
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
  rw [eq_comm, PowerSeries.inv_eq_iff_mul_eq_one hrf, ← map_mul, mul_comm,
    PowerSeries.mul_inv_cancel f hf, map_one]

lemma inv_L_pow_coeff (ρ : ℝ) (hρ_pos : 0 < ρ) (k : ℕ) (hk : 0 < k) (r : ℕ) :
    let L : Polynomial ℝ := 1 - Polynomial.C (1/ρ) * Polynomial.X
    (PowerSeries.coeff r) (((↑L : PowerSeries ℝ) ^ k)⁻¹) =
      ((k - 1 + r).choose (k - 1) : ℝ) * (1/ρ) ^ r := by
  intro L
  have _hρ_ne : ρ ≠ 0 := ne_of_gt hρ_pos
  have hL : (↑L : PowerSeries ℝ) = PowerSeries.rescale (1/ρ) (1 - PowerSeries.X) :=
    L_coe_eq_rescale_one_sub_X ρ
  have hLk : (↑L : PowerSeries ℝ) ^ k = PowerSeries.rescale (1/ρ) ((1 - PowerSeries.X) ^ k) := by
    rw [hL, map_pow]
  have hcc : PowerSeries.constantCoeff ((1 - PowerSeries.X : PowerSeries ℝ) ^ k) ≠ 0 :=
    one_sub_X_pow_constantCoeff_ne_zero k
  have hinv : ((1 - PowerSeries.X : PowerSeries ℝ) ^ k)⁻¹ = ↑(PowerSeries.invOneSubPow ℝ k) :=
    inv_one_sub_pow_eq_invOneSubPow k
  have hmain : ((↑L : PowerSeries ℝ) ^ k)⁻¹ =
      PowerSeries.rescale (1/ρ) (↑(PowerSeries.invOneSubPow ℝ k)) := by
    rw [hLk, ← rescale_inv _ _ hcc, hinv]
  rw [hmain, PowerSeries.coeff_rescale,
      PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℝ k hk,
      PowerSeries.coeff_mk]
  ring

lemma sum_le_pow_mul_sum (q : Polynomial ℝ) (hd : 1 ≤ q.natDegree) (x : ℝ) (hx : 1 ≤ x) :
    ∑ i ∈ Finset.range q.natDegree, |q.coeff i| * x ^ i ≤
    x ^ (q.natDegree - 1) * ∑ i ∈ Finset.range q.natDegree, |q.coeff i| := by
  calc ∑ i ∈ Finset.range q.natDegree, |q.coeff i| * x ^ i
      ≤ ∑ i ∈ Finset.range q.natDegree, |q.coeff i| * x ^ (q.natDegree - 1) :=
        Finset.sum_le_sum fun i hi => by
          have h₁ : i < q.natDegree := Finset.mem_range.mp hi
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by linarith) (by omega)) (abs_nonneg _)
    _ = x ^ (q.natDegree - 1) * ∑ i ∈ Finset.range q.natDegree, |q.coeff i| := by
        rw [Finset.mul_sum]
        congr 1
        ext i
        ring

lemma abs_sum_le_pow_mul_sum_abs (q : Polynomial ℝ) (hd : 1 ≤ q.natDegree) (x : ℝ) (hx : 1 ≤ x) :
    |∑ i ∈ Finset.range q.natDegree, q.coeff i * x ^ i| ≤
    x ^ (q.natDegree - 1) * ∑ i ∈ Finset.range q.natDegree, |q.coeff i| := by
  calc |∑ i ∈ Finset.range q.natDegree, q.coeff i * x ^ i|
      ≤ ∑ i ∈ Finset.range q.natDegree, |q.coeff i * x ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range q.natDegree, |q.coeff i| * x ^ i :=
        Finset.sum_congr rfl fun i _ => by
          rw [abs_mul, abs_of_nonneg (pow_nonneg (le_trans zero_le_one hx) i)]
    _ ≤ x ^ (q.natDegree - 1) * ∑ i ∈ Finset.range q.natDegree, |q.coeff i| :=
        sum_le_pow_mul_sum q hd x hx

lemma poly_eval_lower_bound (q : Polynomial ℝ) (hd : 1 ≤ q.natDegree) (x : ℝ) (hx : 1 ≤ x) :
    x ^ (q.natDegree - 1) * (q.leadingCoeff * x -
      ∑ i ∈ Finset.range q.natDegree, |q.coeff i|) ≤ q.eval x := by
  rw [show q.eval x = (∑ i ∈ Finset.range q.natDegree, q.coeff i * x ^ i) +
      q.leadingCoeff * x ^ q.natDegree from by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, Polynomial.coeff_natDegree]]
  have hx_nonneg : 0 ≤ x ^ (q.natDegree - 1) := pow_nonneg (le_trans zero_le_one hx) _
  have hd1 : q.natDegree - 1 + 1 = q.natDegree := by omega
  rw [show x ^ q.natDegree = x ^ (q.natDegree - 1) * x from by conv_lhs => rw [← hd1, pow_succ]]
  nlinarith [show -(x ^ (q.natDegree - 1) * ∑ i ∈ Finset.range q.natDegree, |q.coeff i|) ≤
      ∑ i ∈ Finset.range q.natDegree, q.coeff i * x ^ i from
    (neg_le_neg (abs_sum_le_pow_mul_sum_abs q hd x hx)).trans (neg_abs_le _)]

lemma poly_eventually_pos_nat (q : Polynomial ℝ) (hq : 0 < q.leadingCoeff) :
    ∃ N : ℕ, ∀ r : ℕ, N < r → 0 < q.eval (r : ℝ) := by
  by_cases hd : q.natDegree = 0
  · refine ⟨0, fun r _ => ?_⟩
    rw [Polynomial.eq_C_of_natDegree_eq_zero hd, Polynomial.eval_C]
    rwa [Polynomial.leadingCoeff, hd] at hq
  · push Not at hd
    have hd1 : 1 ≤ q.natDegree := Nat.one_le_iff_ne_zero.mpr hd
    set S := ∑ i ∈ Finset.range q.natDegree, |q.coeff i| with hS_def
    obtain ⟨N, hN⟩ := exists_nat_gt (S / q.leadingCoeff)
    refine ⟨N, fun r hr => ?_⟩
    have hr_pos : (0 : ℝ) < r := by
      norm_cast
      omega
    have hr_ge_one : (1 : ℝ) ≤ r := by
      norm_cast
      omega
    have hbound := poly_eval_lower_bound q hd1 r hr_ge_one
    suffices h : 0 < (r : ℝ) ^ (q.natDegree - 1) * (q.leadingCoeff * r - S) from
      lt_of_lt_of_le h hbound
    apply mul_pos
    · exact pow_pos hr_pos _
    · have hSr : S / q.leadingCoeff < r := by
        calc S / q.leadingCoeff < N := hN
          _ < r := by exact_mod_cast hr
      rw [sub_pos]
      rwa [div_lt_iff₀ hq, mul_comm] at hSr

/-! ## Hilbert Polynomial and Eventual Positivity -/

/-- The polynomial `N_poly` rescaled by `ρ`, i.e. `N_poly.comp (C ρ * X)`. -/
noncomputable def nScaled (ρ : ℝ) (N_poly : Polynomial ℝ) : Polynomial ℝ :=
  N_poly.comp (Polynomial.C ρ * Polynomial.X)

lemma N_scaled_coe_eq_rescale (ρ : ℝ) (N_poly : Polynomial ℝ) :
    (↑(nScaled ρ N_poly) : PowerSeries ℝ) =
    (PowerSeries.rescale ρ) (↑N_poly : PowerSeries ℝ) := by
  have h_main : ∀ (n : ℕ), (Polynomial.coeff (N_poly.comp (Polynomial.C ρ * Polynomial.X)) n : ℝ)
      = (ρ : ℝ) ^ n * Polynomial.coeff N_poly n := by
    intro n
    induction N_poly using Polynomial.induction_on' with
    | add p q hp hq =>
      simp [Polynomial.add_comp, hp, hq]
      ring
    | monomial k a =>
      simp only [Polynomial.monomial_comp, Polynomial.C_mul_X_eq_monomial,
                 Polynomial.monomial_pow, Polynomial.coeff_C_mul,
                 Polynomial.coeff_monomial, one_mul]
      split_ifs with h
      · subst h
        ring
      · simp
  ext n
  simp [nScaled, PowerSeries.coeff_rescale, h_main]

lemma N_scaled_eval_one (ρ : ℝ) (N_poly : Polynomial ℝ) :
    (nScaled ρ N_poly).eval 1 = N_poly.eval ρ := by
  simp [nScaled, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

lemma rescale_rho_L_eq_one_sub_X (ρ : ℝ) (hρ : 0 < ρ) :
    let L : Polynomial ℝ := 1 - Polynomial.C (1/ρ) * Polynomial.X
    (PowerSeries.rescale ρ) (↑L : PowerSeries ℝ) = 1 - PowerSeries.X := by
  intro L
  rw [L_coe_eq_rescale_one_sub_X, PowerSeries.rescale_rescale,
    one_div_mul_cancel (ne_of_gt hρ),
    show PowerSeries.rescale (1 : ℝ) = RingHom.id _ from PowerSeries.rescale_one]
  simp

lemma degree_smul_preHilbertPoly (p : Polynomial ℝ) (d i : ℕ) (hi : i ∈ p.support) :
    (p.coeff i • Polynomial.preHilbertPoly ℝ d i).degree = ↑d := by
  have h_coeff : p.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  have h_preHilbert_nonzero : Polynomial.preHilbertPoly ℝ d i ≠ 0 := by
    intro h
    have : (Polynomial.preHilbertPoly ℝ d i).leadingCoeff = 0 := by simp [h]
    rw [Polynomial.leadingCoeff_preHilbertPoly] at this
    exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)) this
  rw [show p.coeff i • Polynomial.preHilbertPoly ℝ d i =
      Polynomial.C (p.coeff i) * Polynomial.preHilbertPoly ℝ d i from
    by simp [Polynomial.smul_eq_C_mul]]
  rw [Polynomial.degree_C_mul h_coeff, Polynomial.degree_eq_natDegree h_preHilbert_nonzero,
    Polynomial.natDegree_preHilbertPoly]

lemma hilbertPoly_succ_leadingCoeff_sum (p : Polynomial ℝ) (d : ℕ)
    (h_nonzero : ∑ i ∈ p.support, p.coeff i ≠ 0) :
    (∑ i ∈ p.support, (p.coeff i • Polynomial.preHilbertPoly ℝ d i)).leadingCoeff =
    ∑ i ∈ p.support, p.coeff i * ((d.factorial : ℝ)⁻¹) := by
  have h_deg : ∀ k ∈ p.support,
      (p.coeff k • Polynomial.preHilbertPoly ℝ d k).degree = ↑d :=
    fun k hk => degree_smul_preHilbertPoly p d k hk
  have h_lc : ∀ k ∈ p.support,
      (p.coeff k • Polynomial.preHilbertPoly ℝ d k).leadingCoeff =
      p.coeff k * ((d.factorial : ℝ)⁻¹) :=
    fun k hk => by
      have h₁ : (p.coeff k • Polynomial.preHilbertPoly ℝ d k).leadingCoeff =
          (p.coeff k : ℝ) • (Polynomial.preHilbertPoly ℝ d k).leadingCoeff := by
        rw [Polynomial.leadingCoeff_smul_of_smul_regular]
        exact fun x => by aesop
      rw [h₁, Polynomial.leadingCoeff_preHilbertPoly, smul_eq_mul]
  have h_ne : ∑ k ∈ p.support,
      (p.coeff k • Polynomial.preHilbertPoly ℝ d k).leadingCoeff ≠ 0 := by
    rw [Finset.sum_congr rfl h_lc, show ∑ i ∈ p.support, p.coeff i * (d.factorial : ℝ)⁻¹ =
        (∑ i ∈ p.support, p.coeff i) * (d.factorial : ℝ)⁻¹ from by rw [← Finset.sum_mul]]
    exact mul_ne_zero h_nonzero (inv_ne_zero (by positivity))
  rw [Polynomial.leadingCoeff_sum_of_degree_eq h_deg h_ne]
  exact Finset.sum_congr rfl h_lc

lemma hilbertPoly_succ_leadingCoeff (p : Polynomial ℝ) (d : ℕ)
    (hp : p.eval 1 ≠ 0) :
    (p.hilbertPoly (d + 1)).leadingCoeff = p.eval 1 * ((d.factorial : ℝ)⁻¹) := by
  rw [Polynomial.hilbertPoly_succ]
  have h_eval_one : p.eval 1 = ∑ i ∈ p.support, p.coeff i := by
    rw [Polynomial.eval_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by simp
  have h_sum_ne : ∑ i ∈ p.support, p.coeff i ≠ 0 := by rwa [← h_eval_one]
  rw [hilbertPoly_succ_leadingCoeff_sum p d h_sum_ne, ← Finset.sum_mul, h_eval_one]

lemma hilbertPoly_pos_leadingCoeff (ρ : ℝ) (_hρ : 0 < ρ) (k : ℕ) (hk : 0 < k)
    (N_poly : Polynomial ℝ) (hN_pos : 0 < Polynomial.eval ρ N_poly) :
    0 < ((nScaled ρ N_poly).hilbertPoly k).leadingCoeff := by
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
  rw [hilbertPoly_succ_leadingCoeff]
  · apply mul_pos
    · rw [N_scaled_eval_one]
      exact hN_pos
    · positivity
  · rw [N_scaled_eval_one]
    exact ne_of_gt hN_pos

lemma scaled_coeff_is_eventually_poly
    (ρ : ℝ) (hρ_pos : 0 < ρ) (k : ℕ) (hk : 0 < k) (N_poly : Polynomial ℝ)
    (hN_pos : 0 < Polynomial.eval ρ N_poly) :
    let L : Polynomial ℝ := 1 - Polynomial.C (1/ρ) * Polynomial.X
    ∃ (q : Polynomial ℝ) (N₀ : ℕ),
      0 < q.leadingCoeff ∧
      ∀ r : ℕ, N₀ < r →
        ρ ^ r * (PowerSeries.coeff r)
          ((↑N_poly : PowerSeries ℝ) * ((↑L : PowerSeries ℝ) ^ k)⁻¹) =
        q.eval (r : ℝ) := by
  intro L
  refine ⟨(nScaled ρ N_poly).hilbertPoly k, (nScaled ρ N_poly).natDegree,
    hilbertPoly_pos_leadingCoeff ρ hρ_pos k hk N_poly hN_pos, ?_⟩
  intro r hr
  have h1 : ρ ^ r * (PowerSeries.coeff r)
      ((↑N_poly : PowerSeries ℝ) * ((↑L : PowerSeries ℝ) ^ k)⁻¹) =
    (PowerSeries.coeff r)
      ((PowerSeries.rescale ρ) ((↑N_poly : PowerSeries ℝ) * ((↑L : PowerSeries ℝ) ^ k)⁻¹)) := by
    rw [PowerSeries.coeff_rescale]
  rw [h1, map_mul, ← N_scaled_coe_eq_rescale]
  have hL_cc : PowerSeries.constantCoeff ((↑L : PowerSeries ℝ) ^ k) ≠ 0 :=
    coe_pow_constantCoeff_ne_zero _ k (L_constantCoeff ρ)
  rw [rescale_inv ρ _ hL_cc, map_pow, rescale_rho_L_eq_one_sub_X ρ hρ_pos,
      inv_one_sub_pow_eq_invOneSubPow k]
  exact Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval k hr

lemma L_part_eventually_pos
    (ρ : ℝ) (hρ_pos : 0 < ρ) (k : ℕ) (hk : 0 < k) (N_poly : Polynomial ℝ)
    (hN_pos : 0 < Polynomial.eval ρ N_poly) :
    let L : Polynomial ℝ := 1 - Polynomial.C (1/ρ) * Polynomial.X
    ∃ N, ∀ r, N < r →
      (0 : ℝ) < (PowerSeries.coeff r)
        ((↑N_poly : PowerSeries ℝ) * ((↑L : PowerSeries ℝ) ^ k)⁻¹) := by
  intro L
  obtain ⟨q, N₀, hq_pos, hq_eq⟩ := scaled_coeff_is_eventually_poly ρ hρ_pos k hk N_poly hN_pos
  obtain ⟨N₁, hN₁⟩ := poly_eventually_pos_nat q hq_pos
  refine ⟨max N₀ N₁, fun r hr => ?_⟩
  have hr₀ : N₀ < r := lt_of_le_of_lt (le_max_left _ _) hr
  have hr₁ : N₁ < r := lt_of_le_of_lt (le_max_right _ _) hr
  have hqr : 0 < q.eval (r : ℝ) := hN₁ r hr₁
  have hρr : (0 : ℝ) < ρ ^ r := pow_pos hρ_pos r
  rw [← hq_eq r hr₀] at hqr
  exact (mul_pos_iff.mp hqr).elim (fun ⟨_, hb⟩ => hb)
    (fun ⟨ha', _⟩ => absurd ha' (not_lt_of_gt hρr))

/-! ## Coefficient Bounds and Asymptotic Analysis -/

section finset_lemmas
open Finset

lemma S_eq_one_of_deg_zero_const_one (S : Polynomial ℝ) (hS_const_coeff : Polynomial.eval 0 S = 1)
    (hS_deg : S.natDegree = 0) :
    S = 1 := by
  rw [Polynomial.eq_C_of_natDegree_eq_zero hS_deg]
  simp [Polynomial.coeff_zero_eq_eval_zero, hS_const_coeff]

lemma S_part_eventually_zero_of_const
    (M_poly S : Polynomial ℝ) (k : ℕ) (_hk : 0 < k) (hS_const_coeff : Polynomial.eval 0 S = 1)
    (hS_deg : S.natDegree = 0) :
    ∃ N, ∀ r, N < r →
      (PowerSeries.coeff r)
        ((↑M_poly : PowerSeries ℝ) * ((↑S : PowerSeries ℝ) ^ k)⁻¹) = 0 := by
  have hS1 : S = 1 := S_eq_one_of_deg_zero_const_one S hS_const_coeff hS_deg
  subst hS1
  simp only [Polynomial.coe_one, one_pow, inv_one, mul_one]
  exact ⟨M_poly.natDegree, fun r hr => poly_coe_eventually_zero ℝ M_poly r hr⟩

lemma inv_one_pow_coeff_bound (k : ℕ) (_hk : 0 < k) (ρ₁ : ℝ) (hρ₁_pos : 0 < ρ₁) :
    ∃ (C : ℝ) (D : ℕ), 0 < C ∧
      ∀ r, |(PowerSeries.coeff r) ((↑(1 : Polynomial ℝ) : PowerSeries ℝ) ^ k)⁻¹| ≤
        C * (↑r + 1) ^ D * (1/ρ₁) ^ r := by
  have h₁ : ((↑(1 : Polynomial ℝ) : PowerSeries ℝ) ^ k)⁻¹ = 1 := by simp
  refine ⟨1, 0, one_pos, fun r => ?_⟩
  rw [h₁, PowerSeries.coeff_one]
  split_ifs with hr
  · subst hr
    rw [abs_one]
    norm_num
  · rw [abs_zero]
    positivity

lemma coeff_bound_strengthened
    (f : PowerSeries ℝ) (C : ℝ) (D : ℕ) (q : ℝ) (hC : 0 < C) (hq : 0 < q)
    (hbound : ∀ r, |(PowerSeries.coeff r) f| ≤ C * (↑r + 1) ^ D * q ^ r)
    (r i j : ℕ) (hij : i + j = r) :
    |(PowerSeries.coeff j) f| ≤ C * (↑r + 1) ^ D * q ^ r * q⁻¹ ^ i := by
  have h2 : (↑j + 1 : ℝ) ^ D ≤ (↑r + 1 : ℝ) ^ D :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast by omega) D
  calc |(PowerSeries.coeff j) f|
      ≤ C * (↑j + 1) ^ D * q ^ j := hbound j
    _ = C * (↑j + 1) ^ D * (q ^ r * q⁻¹ ^ i) := by
        rw [show q ^ j = q ^ r * q⁻¹ ^ i from by
          rw [inv_pow, ← hij, pow_add]
          field_simp [(pow_pos hq i).ne']]
    _ ≤ C * (↑r + 1) ^ D * (q ^ r * q⁻¹ ^ i) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left h2 (le_of_lt hC)
        · exact mul_nonneg (pow_nonneg (le_of_lt hq) _)
            (pow_nonneg (inv_nonneg.mpr (le_of_lt hq)) _)
    _ = C * (↑r + 1) ^ D * q ^ r * q⁻¹ ^ i := by ring

lemma antidiag_term_bound
    (P : Polynomial ℝ) (f : PowerSeries ℝ) (C : ℝ) (D : ℕ) (q : ℝ) (hC : 0 < C) (hq : 0 < q)
    (hbound : ∀ r, |(PowerSeries.coeff r) f| ≤ C * (↑r + 1) ^ D * q ^ r)
    (r i j : ℕ) (hij : i + j = r) :
    |P.coeff i| * |(PowerSeries.coeff j) f| ≤
      |P.coeff i| * (C * (↑r + 1) ^ D * q ^ r * q⁻¹ ^ i) := by
  apply mul_le_mul_of_nonneg_left
  · exact coeff_bound_strengthened f C D q hC hq hbound r i j hij
  · exact abs_nonneg _

lemma antidiag_sum_eq_range_sum
    (P : Polynomial ℝ) (C : ℝ) (D : ℕ) (q : ℝ) (r : ℕ) :
    ∑ p ∈ Finset.antidiagonal r, |P.coeff p.1| * (C * (↑r + 1) ^ D * q ^ r * q⁻¹ ^ p.1) =
      C * (↑r + 1) ^ D * q ^ r *
        ∑ i ∈ Finset.range (r + 1), |P.coeff i| * q⁻¹ ^ i := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  congr 1
  ext i
  ring

lemma sum_eq_of_natDegree_lt
    (P : Polynomial ℝ) (q : ℝ) (r : ℕ) (h : P.natDegree + 1 < r + 1) :
    ∑ i ∈ Finset.range (r + 1), |P.coeff i| * q⁻¹ ^ i =
      ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| * q⁻¹ ^ i := by
  conv_lhs =>
    rw [show r + 1 = (P.natDegree + 1) + (r - P.natDegree) from by omega,
      Finset.sum_range_add]
  suffices ∑ x ∈ Finset.range (r - P.natDegree),
      |P.coeff (P.natDegree + 1 + x)| * q⁻¹ ^ (P.natDegree + 1 + x) = 0 by
    rw [this, add_zero]
  apply Finset.sum_eq_zero
  intro x _
  have : P.coeff (P.natDegree + 1 + x) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [this, abs_zero, zero_mul]

lemma antidiag_sum_bound
    (P : Polynomial ℝ) (f : PowerSeries ℝ) (C : ℝ) (D : ℕ) (q : ℝ) (hC : 0 < C) (hq : 0 < q)
    (hbound : ∀ r, |(PowerSeries.coeff r) f| ≤ C * (↑r + 1) ^ D * q ^ r) (r : ℕ) :
    ∑ p ∈ Finset.antidiagonal r, |P.coeff p.1| * |(PowerSeries.coeff p.2) f| ≤
      C * (∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| * q⁻¹ ^ i) *
      (↑r + 1) ^ D * q ^ r := by
  have step1 : ∑ p ∈ Finset.antidiagonal r, |P.coeff p.1| * |(PowerSeries.coeff p.2) f| ≤
      ∑ p ∈ Finset.antidiagonal r, |P.coeff p.1| * (C * (↑r + 1) ^ D * q ^ r * q⁻¹ ^ p.1) := by
    apply Finset.sum_le_sum
    intro p hp
    have hij : p.1 + p.2 = r := Finset.mem_antidiagonal.mp hp
    exact antidiag_term_bound P f C D q hC hq hbound r p.1 p.2 hij
  have step2 : ∑ p ∈ Finset.antidiagonal r, |P.coeff p.1| * (C * (↑r + 1) ^ D * q ^ r * q⁻¹ ^ p.1) =
      C * (↑r + 1) ^ D * q ^ r *
        ∑ i ∈ Finset.range (r + 1), |P.coeff i| * q⁻¹ ^ i :=
    antidiag_sum_eq_range_sum P C D q r
  have step3 : ∑ i ∈ Finset.range (r + 1), |P.coeff i| * q⁻¹ ^ i ≤
      ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| * q⁻¹ ^ i := by
    rcases le_or_gt (r + 1) (P.natDegree + 1) with h | h
    · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
        (fun i _ _ => mul_nonneg (abs_nonneg _) (pow_nonneg (inv_nonneg.mpr (le_of_lt hq)) _))
    · exact le_of_eq (sum_eq_of_natDegree_lt P q r h)
  calc ∑ p ∈ Finset.antidiagonal r, |P.coeff p.1| * |(PowerSeries.coeff p.2) f|
      ≤ ∑ p ∈ Finset.antidiagonal r, |P.coeff p.1| * (C * (↑r + 1) ^ D * q ^ r * q⁻¹ ^ p.1) := step1
    _ = C * (↑r + 1) ^ D * q ^ r *
        ∑ i ∈ Finset.range (r + 1), |P.coeff i| * q⁻¹ ^ i := step2
    _ ≤ C * (↑r + 1) ^ D * q ^ r *
        ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| * q⁻¹ ^ i := by
        apply mul_le_mul_of_nonneg_left step3
        apply mul_nonneg
        · apply mul_nonneg
          · exact le_of_lt hC
          · exact pow_nonneg (by positivity) D
        · exact pow_nonneg (le_of_lt hq) r
    _ = C * (∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| * q⁻¹ ^ i) *
        (↑r + 1) ^ D * q ^ r := by ring

lemma poly_mul_coeff_bound
    (P : Polynomial ℝ) (f : PowerSeries ℝ) (C : ℝ) (D : ℕ) (q : ℝ) (hC : 0 < C) (hq : 0 < q)
    (hbound : ∀ r, |(PowerSeries.coeff r) f| ≤ C * (↑r + 1) ^ D * q ^ r) (r : ℕ) :
    |(PowerSeries.coeff r) ((↑P : PowerSeries ℝ) * f)| ≤
      C * (∑ i ∈ range (P.natDegree + 1), |P.coeff i| * q⁻¹ ^ i) *
      (↑r + 1) ^ D * q ^ r := by
  rw [PowerSeries.coeff_mul]
  calc |∑ p ∈ antidiagonal r, (PowerSeries.coeff p.1) ↑P * (PowerSeries.coeff p.2) f|
      ≤ ∑ p ∈ antidiagonal r, |(PowerSeries.coeff p.1) ↑P * (PowerSeries.coeff p.2) f| :=
        abs_sum_le_sum_abs _ _
    _ = ∑ p ∈ antidiagonal r, |P.coeff p.1| * |(PowerSeries.coeff p.2) f| := by
        congr 1
        ext p
        rw [abs_mul, Polynomial.coeff_coe]
    _ ≤ C * (∑ i ∈ range (P.natDegree + 1), |P.coeff i| * q⁻¹ ^ i) *
        (↑r + 1) ^ D * q ^ r :=
        antidiag_sum_bound P f C D q hC hq hbound r

lemma poly_mul_preserves_bound
    (P : Polynomial ℝ) (f : PowerSeries ℝ) (C : ℝ) (D : ℕ) (q : ℝ) (hC : 0 < C) (hq : 0 < q)
    (hbound : ∀ r, |(PowerSeries.coeff r) f| ≤ C * (↑r + 1) ^ D * q ^ r) :
    ∃ (C' : ℝ) (D' : ℕ), 0 < C' ∧
      ∀ r, |(PowerSeries.coeff r) ((↑P : PowerSeries ℝ) * f)| ≤
        C' * (↑r + 1) ^ D' * q ^ r := by
  set M := ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| * q⁻¹ ^ i
  refine ⟨C * (M + 1), D, ?_, ?_⟩
  · exact mul_pos hC (by linarith [show 0 ≤ M from Finset.sum_nonneg (fun i _ => by positivity)])
  · intro r
    calc |(PowerSeries.coeff r) ((↑P : PowerSeries ℝ) * f)|
        ≤ C * M * (↑r + 1) ^ D * q ^ r := poly_mul_coeff_bound P f C D q hC hq hbound r
      _ ≤ C * (M + 1) * (↑r + 1) ^ D * q ^ r := by
          apply mul_le_mul_of_nonneg_right
          · apply mul_le_mul_of_nonneg_right
            · apply mul_le_mul_of_nonneg_left
              · linarith
              · exact le_of_lt hC
            · positivity
          · positivity

lemma choose_le_pow_succ_core (n r : ℕ) :
    ((n + r).choose n : ℝ) ≤ (↑r + 1) ^ n := by
  induction n with
  | zero => simp [Nat.choose_zero_right]
  | succ n ih =>
    have h_rec : (n + 1 : ℕ) * (n + 1 + r).choose (n + 1) = (n + 1 + r) * (n + r).choose n := by
      have := Nat.add_one_mul_choose_eq (n + r) n
      simp [add_assoc, add_comm] at this ⊢
      ring_nf at this ⊢
      omega
    have h_pos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have h₁ : ((n + 1 : ℕ) : ℝ) * ((n + 1 + r).choose (n + 1) : ℝ) =
        ((n + 1 + r : ℕ) : ℝ) * ((n + r).choose n : ℝ) := by norm_cast
    have h₂ : ((n + 1 + r : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * (↑r + 1 : ℝ) := by
      push_cast
      nlinarith
    have h₃ : ((n + 1 + r : ℕ) : ℝ) * ((n + r).choose n : ℝ) ≤
        ((n + 1 : ℕ) : ℝ) * (↑r + 1 : ℝ) * ((n + r).choose n : ℝ) := by nlinarith
    have h₄ : ((n + 1 : ℕ) : ℝ) * ((n + 1 + r).choose (n + 1) : ℝ) ≤
        ((n + 1 : ℕ) : ℝ) * (↑r + 1 : ℝ) * ((n + r).choose n : ℝ) := by linarith
    have h₅ : ((n + 1 + r).choose (n + 1) : ℝ) ≤ (↑r + 1) * ((n + r).choose n : ℝ) := by
      calc ((n + 1 + r).choose (n + 1) : ℝ)
          = ((n + 1 : ℕ) : ℝ) * ((n + 1 + r).choose (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
            field_simp [h_pos.ne']
        _ ≤ ((n + 1 : ℕ) : ℝ) * (↑r + 1) * ((n + r).choose n : ℝ) / ((n + 1 : ℕ) : ℝ) := by gcongr
        _ = (↑r + 1) * ((n + r).choose n : ℝ) := by field_simp [h_pos.ne']
    calc ((n + 1 + r).choose (n + 1) : ℝ)
        ≤ (↑r + 1) * ((n + r).choose n : ℝ) := h₅
      _ ≤ (↑r + 1) * (↑r + 1) ^ n := by nlinarith
      _ = (↑r + 1) ^ (n + 1) := by ring

lemma cauchy_summand_bound
    (C₁ C₂ : ℝ) (D₁ D₂ : ℕ) (q : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hq : 0 ≤ q)
    (r r₁ r₂ : ℕ) (hr : r₁ + r₂ = r) (b₁ b₂ : ℝ) (hb₁ : |b₁| ≤ C₁ * (↑r₁ + 1) ^ D₁ * q ^ r₁)
    (hb₂ : |b₂| ≤ C₂ * (↑r₂ + 1) ^ D₂ * q ^ r₂) :
    |b₁ * b₂| ≤ C₁ * C₂ * (↑r + 1) ^ (D₁ + D₂) * q ^ r := by
  rw [abs_mul]
  have h₁ : |b₁| * |b₂| ≤ (C₁ * (↑r₁ + 1 : ℝ) ^ D₁ * q ^ r₁) * (C₂ * (↑r₂ + 1 : ℝ) ^ D₂ * q ^ r₂) :=
    mul_le_mul hb₁ hb₂ (abs_nonneg _) (by positivity)
  calc |b₁| * |b₂|
      ≤ (C₁ * (↑r₁ + 1 : ℝ) ^ D₁ * q ^ r₁) * (C₂ * (↑r₂ + 1 : ℝ) ^ D₂ * q ^ r₂) := h₁
    _ = C₁ * C₂ * ((↑r₁ + 1 : ℝ) ^ D₁ * (↑r₂ + 1 : ℝ) ^ D₂) * (q ^ r₁ * q ^ r₂) := by ring
    _ ≤ C₁ * C₂ * (↑r + 1 : ℝ) ^ (D₁ + D₂) * q ^ r := by
        rw [← pow_add q, hr]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq r)
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC₁ hC₂)
        calc (↑r₁ + 1 : ℝ) ^ D₁ * (↑r₂ + 1 : ℝ) ^ D₂
            ≤ (↑r + 1 : ℝ) ^ D₁ * (↑r + 1 : ℝ) ^ D₂ := by
              gcongr
              · exact_mod_cast by omega
              · exact_mod_cast by omega
          _ = (↑r + 1 : ℝ) ^ (D₁ + D₂) := by rw [← pow_add]

lemma cauchy_product_bound
    (f₁ f₂ : PowerSeries ℝ) (C₁ C₂ : ℝ) (D₁ D₂ : ℕ) (q : ℝ)
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hq : 0 < q)
    (hf₁ : ∀ r, |(PowerSeries.coeff r) f₁| ≤ C₁ * (↑r + 1) ^ D₁ * q ^ r)
    (hf₂ : ∀ r, |(PowerSeries.coeff r) f₂| ≤ C₂ * (↑r + 1) ^ D₂ * q ^ r) :
    ∀ r, |(PowerSeries.coeff r) (f₁ * f₂)| ≤ C₁ * C₂ * (↑r + 1) ^ (D₁ + D₂ + 1) * q ^ r := by
  intro r
  rw [PowerSeries.coeff_mul]
  have hbound : ∀ p ∈ Finset.antidiagonal r,
      |(PowerSeries.coeff p.1) f₁ * (PowerSeries.coeff p.2) f₂| ≤
        C₁ * C₂ * (↑r + 1) ^ (D₁ + D₂) * q ^ r := by
    intro p hp
    have hmem := Finset.mem_antidiagonal.mp hp
    exact cauchy_summand_bound C₁ C₂ D₁ D₂ q (le_of_lt hC₁) (le_of_lt hC₂)
      (le_of_lt hq) r p.1 p.2 hmem _ _ (hf₁ p.1) (hf₂ p.2)
  calc |∑ p ∈ Finset.antidiagonal r, (PowerSeries.coeff p.1) f₁ * (PowerSeries.coeff p.2) f₂|
      ≤ ∑ p ∈ Finset.antidiagonal r, |(PowerSeries.coeff p.1) f₁ * (PowerSeries.coeff p.2) f₂| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Finset.antidiagonal r).card • (C₁ * C₂ * (↑r + 1) ^ (D₁ + D₂) * q ^ r) :=
        Finset.sum_le_card_nsmul _ _ _ hbound
    _ = (r + 1) • (C₁ * C₂ * (↑r + 1) ^ (D₁ + D₂) * q ^ r) := by rw [Finset.Nat.card_antidiagonal]
    _ = C₁ * C₂ * (↑r + 1) ^ (D₁ + D₂ + 1) * q ^ r := by
        rw [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, pow_succ']
        ring

lemma ps_mul_coeff_bound
    (f₁ f₂ : PowerSeries ℝ) (C₁ C₂ : ℝ) (D₁ D₂ : ℕ) (q : ℝ)
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hq : 0 < q)
    (hf₁ : ∀ r, |(PowerSeries.coeff r) f₁| ≤ C₁ * (↑r + 1) ^ D₁ * q ^ r)
    (hf₂ : ∀ r, |(PowerSeries.coeff r) f₂| ≤ C₂ * (↑r + 1) ^ D₂ * q ^ r) :
    ∃ (C' : ℝ) (D' : ℕ), 0 < C' ∧
      ∀ r, |(PowerSeries.coeff r) (f₁ * f₂)| ≤ C' * (↑r + 1) ^ D' * q ^ r :=
  ⟨C₁ * C₂, D₁ + D₂ + 1, mul_pos hC₁ hC₂,
    cauchy_product_bound f₁ f₂ C₁ C₂ D₁ D₂ q hC₁ hC₂ hq hf₁ hf₂⟩

lemma single_factor_inv_pow_bound
    (α : ℝ) (ρ₁ : ℝ) (k : ℕ) (hα_pos : 0 < α) (hρ₁_pos : 0 < ρ₁) (hk : 0 < k) (hα_ge : ρ₁ ≤ α) :
    let L : Polynomial ℝ := 1 - Polynomial.C (1/α) * Polynomial.X
    ∀ r, |(PowerSeries.coeff r) (((↑L : PowerSeries ℝ) ^ k)⁻¹)| ≤
      (↑r + 1) ^ (k - 1) * (1/ρ₁) ^ r := by
  intro L r
  rw [inv_L_pow_coeff α hα_pos k hk r]
  rw [abs_of_nonneg (mul_nonneg (by positivity) (pow_nonneg (by positivity) r))]
  exact mul_le_mul
    (choose_le_pow_succ_core (k - 1) r)
    (pow_le_pow_left₀ (by positivity) (by rw [div_le_div_iff₀ hα_pos hρ₁_pos]; linarith) r)
    (pow_nonneg (by positivity) r)
    (by positivity)

lemma base_case_bound (k : ℕ) (ρ₁ : ℝ) (_hk : 0 < k) (hρ₁_pos : 0 < ρ₁) :
    ∃ (C : ℝ) (D : ℕ), 0 < C ∧
      ∀ r, |(PowerSeries.coeff r)
        ((Multiset.map (fun α =>
          (((↑(1 - Polynomial.C (1/α) * Polynomial.X : Polynomial ℝ) : PowerSeries ℝ) ^ k)⁻¹))
          (0 : Multiset ℝ)).prod)| ≤
        C * (↑r + 1) ^ D * (1/ρ₁) ^ r := by
  refine ⟨1, 0, by norm_num, fun r => ?_⟩
  have h₁ : (Multiset.map (fun α =>
    (((↑(1 - Polynomial.C (1 / α) * Polynomial.X : Polynomial ℝ) : PowerSeries ℝ) ^ k)⁻¹))
    (0 : Multiset ℝ)).prod = 1 := by
    simp [Multiset.prod_zero]
  rw [h₁]
  have h₂ : (PowerSeries.coeff r (1 : PowerSeries ℝ)) = if r = 0 then 1 else 0 := by
    simp [PowerSeries.coeff_one]
  rw [h₂]
  split_ifs with h₃
  · simp [h₃, abs_of_nonneg]
  · rw [abs_zero]
    positivity

lemma multiset_prod_inv_bound
    (roots : Multiset ℝ) (k : ℕ) (ρ₁ : ℝ) (hk : 0 < k) (hρ₁_pos : 0 < ρ₁)
    (hroots_pos : ∀ α ∈ roots, (0 : ℝ) < α) (hroots_ge : ∀ α ∈ roots, ρ₁ ≤ α) :
    let F := (roots.map (fun α =>
      (((↑(1 - Polynomial.C (1/α) * Polynomial.X : Polynomial ℝ) : PowerSeries ℝ) ^ k)⁻¹))).prod
    ∃ (C : ℝ) (D : ℕ), 0 < C ∧
      ∀ r, |(PowerSeries.coeff r) F| ≤ C * (↑r + 1) ^ D * (1/ρ₁) ^ r := by
  intro F
  induction roots using Multiset.induction_on with
  | empty =>
    exact base_case_bound k ρ₁ hk hρ₁_pos
  | cons a s ih =>
    have ha_pos : (0 : ℝ) < a := hroots_pos a (Multiset.mem_cons_self a s)
    have ha_ge : ρ₁ ≤ a := hroots_ge a (Multiset.mem_cons_self a s)
    have hs_pos : ∀ α ∈ s, (0 : ℝ) < α := fun α hα =>
      hroots_pos α (Multiset.mem_cons_of_mem hα)
    have hs_ge : ∀ α ∈ s, ρ₁ ≤ α := fun α hα =>
      hroots_ge α (Multiset.mem_cons_of_mem hα)
    obtain ⟨C_s, D_s, hC_s, hbound_s⟩ := ih hs_pos hs_ge
    have hbound_a := single_factor_inv_pow_bound a ρ₁ k ha_pos hρ₁_pos hk ha_ge
    simp only at hbound_a
    have hbound_a' : ∀ r, |(PowerSeries.coeff r)
        (((↑(1 - Polynomial.C (1/a) * Polynomial.X : Polynomial ℝ) : PowerSeries ℝ) ^ k)⁻¹)| ≤
        1 * (↑r + 1) ^ (k - 1) * (1/ρ₁) ^ r := by
      intro r
      simp only [one_mul]
      exact hbound_a r
    have hq_pos : (0 : ℝ) < 1 / ρ₁ := by positivity
    obtain ⟨C', D', hC', hbound'⟩ := ps_mul_coeff_bound _ _ 1 C_s (k - 1) D_s (1/ρ₁)
      one_pos hC_s hq_pos hbound_a' hbound_s
    refine ⟨C', D', hC', ?_⟩
    intro r
    change |(PowerSeries.coeff r) (Multiset.map (fun α =>
      (((↑(1 - Polynomial.C (1/α) * Polynomial.X : Polynomial ℝ) : PowerSeries ℝ) ^ k)⁻¹))
      (a ::ₘ s)).prod| ≤ _
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact hbound' r

lemma X_sub_C_eq_neg_C_mul_L (α : ℝ) (hα : 0 < α) :
    Polynomial.X - Polynomial.C α =
    -Polynomial.C α * (1 - Polynomial.C (1 / α) * Polynomial.X : Polynomial ℝ) := by
  apply Polynomial.funext
  intro x
  simp
  field_simp [hα.ne']
  ring

lemma prod_X_sub_C_eq_scalar_mul_prod_L (roots : Multiset ℝ) (hroots : ∀ α ∈ roots, (0 : ℝ) < α) :
    (roots.map (fun α => Polynomial.X - Polynomial.C α)).prod =
    (roots.map (fun α => -Polynomial.C α)).prod *
    (roots.map (fun α => (1 - Polynomial.C (1/α) * Polynomial.X : Polynomial ℝ))).prod := by
  conv_lhs =>
    rw [show roots.map (fun α => Polynomial.X - Polynomial.C α) =
        roots.map (fun α =>
          -Polynomial.C α * (1 - Polynomial.C (1/α) * Polynomial.X : Polynomial ℝ))
      from Multiset.map_congr rfl (fun α hα => X_sub_C_eq_neg_C_mul_L α (hroots α hα))]
  exact Multiset.prod_map_mul

lemma prod_neg_C_eq_C_prod_neg (roots : Multiset ℝ) :
    (roots.map (fun α => -Polynomial.C α)).prod =
    Polynomial.C ((roots.map Neg.neg).prod) := by
  have h2 : (roots.map (fun α => Polynomial.C (-α))).prod
      = Polynomial.C ((roots.map Neg.neg).prod) := by
    induction roots using Multiset.induction with
    | empty => simp
    | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      rw [ih]
      simp [map_neg, map_mul]
  rw [show (roots.map (fun α => -Polynomial.C α)) = (roots.map (fun α => Polynomial.C (-α))) from
    Multiset.map_congr rfl (fun x _ => by simp)]
  exact h2

lemma leadingCoeff_mul_prod_neg_roots_eq_one (S : Polynomial ℝ) (_hS_ne : S ≠ 0)
    (hS_splits : S.Splits) (hS_const : Polynomial.eval 0 S = 1) :
    S.leadingCoeff * (S.roots.map Neg.neg).prod = 1 := by
  rw [show (S.roots.map Neg.neg).prod = (-1) ^ S.natDegree * S.roots.prod from
    by rw [Multiset.prod_map_neg, hS_splits.natDegree_eq_card_roots]]
  have h1 := hS_splits.coeff_zero_eq_leadingCoeff_mul_prod_roots
  rw [Polynomial.coeff_zero_eq_eval_zero, hS_const] at h1
  linarith [h1]

lemma splits_poly_eq_prod_L
    (S : Polynomial ℝ) (hS_ne : S ≠ 0) (hS_splits : S.Splits) (hS_const : Polynomial.eval 0 S = 1)
    (hroots_pos : ∀ x ∈ S.roots, (0 : ℝ) < x) :
    S = (S.roots.map (fun α => (1 - Polynomial.C (1/α) * Polynomial.X : Polynomial ℝ))).prod := by
  have h1 := hS_splits.eq_prod_roots
  have h2 := prod_X_sub_C_eq_scalar_mul_prod_L S.roots hroots_pos
  have h3 : Polynomial.C S.leadingCoeff * (S.roots.map (fun α => -Polynomial.C α)).prod = 1 := by
    rw [prod_neg_C_eq_C_prod_neg, ← map_mul,
      leadingCoeff_mul_prod_neg_roots_eq_one S hS_ne hS_splits hS_const, Polynomial.C_1]
  rw [h2, ← mul_assoc, h3, one_mul] at h1
  exact h1

lemma coe_pow_eq_prod_coe_pow
    (S : Polynomial ℝ)
    (hS_eq : S = (S.roots.map
      (fun α => (1 - Polynomial.C (1 / α) * Polynomial.X : Polynomial ℝ))).prod)
    (k : ℕ) :
    (↑S : PowerSeries ℝ) ^ k =
      (S.roots.map (fun α =>
        ((↑(1 - Polynomial.C (1/α) * Polynomial.X : Polynomial ℝ) :
          PowerSeries ℝ) ^ k))).prod := by
  conv_lhs => rw [hS_eq]
  change Polynomial.coeToPowerSeries.ringHom ((S.roots.map _).prod) ^ k = _
  rw [map_multiset_prod Polynomial.coeToPowerSeries.ringHom]
  simp [Multiset.map_map, Polynomial.coeToPowerSeries.ringHom_apply, Multiset.prod_map_pow]

lemma inv_prod_eq_prod_inv_of_roots
    (roots : Multiset ℝ) (k : ℕ) :
    (roots.map (fun α =>
      ((↑(1 - Polynomial.C (1/α) * Polynomial.X : Polynomial ℝ) :
        PowerSeries ℝ) ^ k))).prod⁻¹ =
    (roots.map (fun α =>
      (((↑(1 - Polynomial.C (1/α) * Polynomial.X : Polynomial ℝ) :
        PowerSeries ℝ) ^ k)⁻¹))).prod := by
  induction roots using Multiset.induction_on with
  | empty =>
    simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [PowerSeries.mul_inv_rev, ih, mul_comm]

lemma splits_inv_pow_eq_multiset_prod
    (S : Polynomial ℝ) (k : ℕ) (_hk : 0 < k) (hS_ne : S ≠ 0) (hS_splits : S.Splits)
    (hS_const : Polynomial.eval 0 S = 1) (hroots_pos : ∀ x ∈ S.roots, (0 : ℝ) < x) :
    0 < S.natDegree →
    ∃ (P : Polynomial ℝ),
      ((↑S : PowerSeries ℝ) ^ k)⁻¹ = (↑P : PowerSeries ℝ) *
        (S.roots.map (fun α =>
          (((↑(1 - Polynomial.C (1/α) * Polynomial.X : Polynomial ℝ) :
            PowerSeries ℝ) ^ k)⁻¹))).prod := by
  intro _hdeg
  refine ⟨1, ?_⟩
  simp only [Polynomial.coe_one, one_mul]
  rw [coe_pow_eq_prod_coe_pow S
    (splits_poly_eq_prod_L S hS_ne hS_splits hS_const hroots_pos) k]
  rw [inv_prod_eq_prod_inv_of_roots S.roots k]

lemma inv_splits_pow_coeff_bound
    (S : Polynomial ℝ) (k : ℕ) (hk : 0 < k) (hS_ne : S ≠ 0) (hS_splits : S.Splits)
    (hS_const : Polynomial.eval 0 S = 1) (ρ₁ : ℝ) (hρ₁_pos : 0 < ρ₁)
    (hρ₁_le : ∀ x : ℝ, Polynomial.eval x S = 0 → ρ₁ ≤ x) :
    ∃ (C : ℝ) (D : ℕ), 0 < C ∧
      ∀ r, |(PowerSeries.coeff r) ((↑S : PowerSeries ℝ) ^ k)⁻¹| ≤
        C * (↑r + 1) ^ D * (1/ρ₁) ^ r := by
  by_cases hS_deg : S.natDegree = 0
  · have hS_one : S = 1 := S_eq_one_of_deg_zero_const_one S hS_const hS_deg
    subst hS_one
    exact inv_one_pow_coeff_bound k hk ρ₁ hρ₁_pos
  · have hS_deg_pos : 0 < S.natDegree := Nat.pos_of_ne_zero hS_deg
    have hroots_pos : ∀ α ∈ S.roots, (0 : ℝ) < α := by
      intro α hα
      have : Polynomial.eval α S = 0 := by
        rwa [Polynomial.mem_roots hS_ne] at hα
      linarith [hρ₁_le α this]
    have hroots_ge : ∀ α ∈ S.roots, ρ₁ ≤ α := by
      intro α hα
      exact hρ₁_le α (by rwa [Polynomial.mem_roots hS_ne] at hα)
    obtain ⟨P, hP_eq⟩ := splits_inv_pow_eq_multiset_prod S k hk hS_ne hS_splits hS_const
      hroots_pos hS_deg_pos
    obtain ⟨C_prod, D_prod, hC_prod, hprod_bound⟩ :=
      multiset_prod_inv_bound S.roots k ρ₁ hk hρ₁_pos hroots_pos hroots_ge
    rw [hP_eq]
    exact poly_mul_preserves_bound P _ C_prod D_prod (1/ρ₁) hC_prod (by positivity) hprod_bound

lemma eval_eq_zero_of_mem_roots_toFinset
    (S : Polynomial ℝ) (hS_ne : S ≠ 0) {x : ℝ} (hx : x ∈ S.roots.toFinset) :
    Polynomial.eval x S = 0 :=
  (Polynomial.mem_roots hS_ne).mp (Multiset.mem_toFinset.mp hx)

lemma exists_min_root_gt
    (S : Polynomial ℝ) (ρ : ℝ) (hρ_pos : 0 < ρ) (hS_ne : S ≠ 0) (hS_splits : S.Splits)
    (hS_nconst : 0 < S.natDegree) (hS_roots_larger : ∀ x : ℝ, Polynomial.eval x S = 0 → ρ < x) :
    ∃ ρ₁ : ℝ, ρ < ρ₁ ∧ 0 < ρ₁ ∧
      (∀ x : ℝ, Polynomial.eval x S = 0 → ρ₁ ≤ x) := by
  have hne : S.roots.toFinset.Nonempty := by
    obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp (by
      rw [← hS_splits.natDegree_eq_card_roots]
      exact hS_nconst)
    exact ⟨x, Multiset.mem_toFinset.mpr hx⟩
  refine ⟨S.roots.toFinset.min' hne, ?_, ?_, ?_⟩
  · exact hS_roots_larger _ (eval_eq_zero_of_mem_roots_toFinset S hS_ne (Finset.min'_mem _ hne))
  · exact lt_trans hρ_pos
      (hS_roots_larger _ (eval_eq_zero_of_mem_roots_toFinset S hS_ne (Finset.min'_mem _ hne)))
  · intro x hx
    exact Finset.min'_le _ _ (Multiset.mem_toFinset.mpr (by
      rw [Polynomial.mem_roots]
      · simp_all
      · simp_all))

lemma S_part_coeff_bound
    (ρ : ℝ) (hρ_pos : 0 < ρ) (k : ℕ) (hk : 0 < k) (M_poly S : Polynomial ℝ)
    (hS_pos : 0 < Polynomial.eval ρ S) (hS_const : Polynomial.eval 0 S = 1)
    (hS_roots_larger : ∀ x : ℝ, Polynomial.eval x S = 0 → ρ < x) (hS_splits : S.Splits)
    (hS_nconst : 0 < S.natDegree) :
    ∃ (C : ℝ) (D : ℕ) (ρ₂ : ℝ), 0 < C ∧ ρ < ρ₂ ∧
      ∀ r, |(PowerSeries.coeff r)
        ((↑M_poly : PowerSeries ℝ) * ((↑S : PowerSeries ℝ) ^ k)⁻¹)| ≤
        C * (↑r + 1) ^ D * (1/ρ₂) ^ r := by
  have hS_ne : S ≠ 0 := by
    rintro rfl
    simp at hS_pos
  obtain ⟨ρ₁, hρ_lt_ρ₁, hρ₁_pos, hρ₁_le⟩ :=
    exists_min_root_gt S ρ hρ_pos hS_ne hS_splits hS_nconst hS_roots_larger
  obtain ⟨C₁, D₁, hC₁, hbound₁⟩ :=
    inv_splits_pow_coeff_bound S k hk hS_ne hS_splits hS_const ρ₁ hρ₁_pos hρ₁_le
  have hq_pos : (0 : ℝ) < 1 / ρ₁ := by positivity
  obtain ⟨C₂, D₂, hC₂, hbound₂⟩ :=
    poly_mul_preserves_bound M_poly _ C₁ D₁ (1/ρ₁) hC₁ hq_pos hbound₁
  set ρ₂ := (ρ + ρ₁) / 2 with hρ₂_def
  have hρ₂_pos : 0 < ρ₂ := by positivity
  have hρ_lt_ρ₂ : ρ < ρ₂ := by linarith
  have hρ₂_lt_ρ₁ : ρ₂ < ρ₁ := by linarith
  refine ⟨C₂, D₂, ρ₂, hC₂, hρ_lt_ρ₂, ?_⟩
  intro r
  have h_base_le : (1 : ℝ) / ρ₁ ≤ 1 / ρ₂ := by
    rw [div_le_div_iff₀ hρ₁_pos hρ₂_pos]
    linarith
  calc |(PowerSeries.coeff r) ((↑M_poly : PowerSeries ℝ) * ((↑S : PowerSeries ℝ) ^ k)⁻¹)|
      ≤ C₂ * (↑r + 1) ^ D₂ * (1 / ρ₁) ^ r := hbound₂ r
    _ ≤ C₂ * (↑r + 1) ^ D₂ * (1 / ρ₂) ^ r := by
        apply mul_le_mul_of_nonneg_left
        · exact pow_le_pow_left₀ (le_of_lt hq_pos) h_base_le r
        · positivity

end finset_lemmas

lemma poly_eq_of_eventually_eq (q₁ q₂ : Polynomial ℝ) (N : ℕ)
    (h : ∀ r : ℕ, N < r → q₁.eval (r : ℝ) = q₂.eval (r : ℝ)) :
    q₁ = q₂ := by
  have h₁ : q₁ - q₂ = 0 := by
    by_contra h₅
    have : {x : ℝ | (q₁ - q₂).eval x = 0}.Infinite := by
      apply Set.Infinite.mono (s := Set.range fun r : ℕ => ((N + r + 1 : ℕ) : ℝ))
      · intro x hx
        rcases hx with ⟨r, rfl⟩
        simp only [Set.mem_setOf_eq, Polynomial.eval_sub]
        linarith [h (N + r + 1) (by omega : N < N + r + 1)]
      · exact Set.infinite_range_of_injective (fun r₁ r₂ h₉ => by simp_all [add_assoc])
    exact this.not_finite (Polynomial.finite_setOf_isRoot (by simp_all))
  exact eq_of_sub_eq_zero (by simpa using h₁)

theorem scaled_coeff_poly_degree_ge
    (ρ : ℝ) (hρ_pos : 0 < ρ) (k : ℕ) (hk : 0 < k) (N_poly : Polynomial ℝ)
    (hN_pos : 0 < Polynomial.eval ρ N_poly) (q : Polynomial ℝ) (N₀ : ℕ)
    (_hq_lc : 0 < q.leadingCoeff) (hq_eq : ∀ r : ℕ, N₀ < r →
        ρ ^ r * (PowerSeries.coeff r)
          ((↑N_poly : PowerSeries ℝ) *
            ((↑(1 - Polynomial.C (1/ρ) * Polynomial.X : Polynomial ℝ) : PowerSeries ℝ) ^ k)⁻¹) =
        q.eval (r : ℝ)) :
    k - 1 ≤ q.natDegree := by
  set Q := (nScaled ρ N_poly).hilbertPoly k with _
  have hQ_lc : 0 < Q.leadingCoeff :=
    hilbertPoly_pos_leadingCoeff ρ hρ_pos k hk N_poly hN_pos
  have hQ_ne : Q ≠ 0 := by
    intro h
    rw [h, Polynomial.leadingCoeff_zero] at hQ_lc
    exact lt_irrefl 0 hQ_lc
  have hq_eq_Q : q = Q := by
    apply poly_eq_of_eventually_eq q Q (max N₀ (nScaled ρ N_poly).natDegree)
    intro r hr
    have hr_N₀ : N₀ < r := lt_of_le_of_lt (le_max_left _ _) hr
    have hr_deg : (nScaled ρ N_poly).natDegree < r :=
      lt_of_le_of_lt (le_max_right _ _) hr
    rw [← hq_eq r hr_N₀]
    rw [show ρ ^ r * (PowerSeries.coeff r)
        ((↑N_poly : PowerSeries ℝ) *
          ((↑(1 - Polynomial.C (1/ρ) * Polynomial.X : Polynomial ℝ) : PowerSeries ℝ) ^ k)⁻¹) =
        (PowerSeries.coeff r) ((↑(nScaled ρ N_poly) : PowerSeries ℝ) *
          (↑(PowerSeries.invOneSubPow ℝ k) : PowerSeries ℝ)) from by
      rw [← PowerSeries.coeff_rescale, map_mul, ← N_scaled_coe_eq_rescale,
        rescale_inv _ _ (by
          have : PowerSeries.constantCoeff
              ((↑(1 - Polynomial.C (1/ρ) * Polynomial.X : Polynomial ℝ) : PowerSeries ℝ)) = 1 := by
            simp
          simp [map_pow]), map_pow,
        rescale_rho_L_eq_one_sub_X ρ hρ_pos, inv_one_sub_pow_eq_invOneSubPow]]
    exact Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval k hr_deg
  have hroot : Polynomial.rootMultiplicity 1 (nScaled ρ N_poly) = 0 := by
    rw [Polynomial.rootMultiplicity_eq_zero]
    simp only [Polynomial.IsRoot]
    rw [N_scaled_eval_one]
    linarith
  have hQ_deg : Q.natDegree = k - 1 := by
    have := Polynomial.natDegree_hilbertPoly_of_ne_zero hQ_ne
    rw [hroot, Nat.sub_zero] at this
    exact this
  rw [hq_eq_Q, hQ_deg]

lemma divide_by_rho_pow (ρ : ℝ) (hρ : 0 < ρ) (c : ℝ) (d r : ℕ) (x : ℝ)
    (h : c * (r : ℝ) ^ d ≤ ρ ^ r * x) :
    c * (r : ℝ) ^ d * (1/ρ) ^ r ≤ x := by
  have h_pos : 0 < (ρ : ℝ) ^ r := by positivity
  have h_div : c * (r : ℝ) ^ d / (ρ : ℝ) ^ r ≤ x := by
    rw [div_le_iff₀ h_pos]
    linarith
  rw [one_div, inv_pow, ← div_eq_mul_inv]
  exact h_div

lemma poly_lower_bound_at_point (q : Polynomial ℝ) (hq : 0 < q.leadingCoeff)
    (hdeg : 1 ≤ q.natDegree) (d : ℕ) (hd : d ≤ q.natDegree) (x : ℝ) (hx : 1 ≤ x)
    (hxS : 2 * (∑ i ∈ Finset.range q.natDegree, |q.coeff i|) / q.leadingCoeff < x) :
    q.leadingCoeff / 2 * x ^ d ≤ q.eval x := by
  set S := ∑ i ∈ Finset.range q.natDegree, |q.coeff i|
  set lc := q.leadingCoeff
  have h1 := poly_eval_lower_bound q hdeg x hx
  have h2 : lc * x / 2 ≤ lc * x - S := by
    have : 2 * S < lc * x := by
      rw [div_lt_iff₀ hq] at hxS
      linarith
    linarith
  have h3 : x ^ (q.natDegree - 1) * (lc * x / 2) = lc / 2 * x ^ q.natDegree := by
    have : q.natDegree - 1 + 1 = q.natDegree := by omega
    calc x ^ (q.natDegree - 1) * (lc * x / 2)
        = (x ^ (q.natDegree - 1) * x) * (lc / 2) := by ring
      _ = x ^ q.natDegree * (lc / 2) := by rw [← pow_succ, this]
      _ = lc / 2 * x ^ q.natDegree := by ring
  have h4 : x ^ d ≤ x ^ q.natDegree := pow_le_pow_right₀ hx hd
  have h5 : lc / 2 * x ^ d ≤ lc / 2 * x ^ q.natDegree :=
    mul_le_mul_of_nonneg_left h4 (le_of_lt (half_pos hq))
  have hx_pow_pos : (0 : ℝ) ≤ x ^ (q.natDegree - 1) :=
    pow_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one hx)) _
  have h6 : x ^ (q.natDegree - 1) * (lc * x / 2) ≤ x ^ (q.natDegree - 1) * (lc * x - S) :=
    mul_le_mul_of_nonneg_left h2 hx_pow_pos
  calc lc / 2 * x ^ d ≤ lc / 2 * x ^ q.natDegree := h5
    _ = x ^ (q.natDegree - 1) * (lc * x / 2) := h3.symm
    _ ≤ x ^ (q.natDegree - 1) * (lc * x - S) := h6
    _ ≤ q.eval x := h1

lemma poly_eventually_lower_bound_of_deg_ge_one (q : Polynomial ℝ) (hq : 0 < q.leadingCoeff)
    (hdeg : 1 ≤ q.natDegree) (d : ℕ) (hd : d ≤ q.natDegree) :
    ∃ (c : ℝ) (N : ℕ), 0 < c ∧
      ∀ r : ℕ, N < r → c * (r : ℝ) ^ d ≤ q.eval (r : ℝ) := by
  set S := ∑ i ∈ Finset.range q.natDegree, |q.coeff i|
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max (2 * S / q.leadingCoeff) 0)
  refine ⟨q.leadingCoeff / 2, N₀, half_pos hq, fun r hr => ?_⟩
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by
    have : (0 : ℝ) < ↑N₀ := by
      calc (0 : ℝ) ≤ max (2 * S / q.leadingCoeff) 0 := le_max_right _ _
      _ < ↑N₀ := hN₀
    have : 0 < r := by omega
    exact Nat.one_le_cast.mpr this
  have hrS : 2 * S / q.leadingCoeff < (r : ℝ) := by
    calc 2 * S / q.leadingCoeff ≤ max (2 * S / q.leadingCoeff) 0 := le_max_left _ _
    _ < ↑N₀ := hN₀
    _ < ↑r := by exact_mod_cast hr
  exact poly_lower_bound_at_point q hq hdeg d hd (r : ℝ) hr1 hrS

lemma poly_eventually_lower_bound (q : Polynomial ℝ) (hq : 0 < q.leadingCoeff)
    (d : ℕ) (hd : d ≤ q.natDegree) :
    ∃ (c : ℝ) (N : ℕ), 0 < c ∧
      ∀ r : ℕ, N < r → c * (r : ℝ) ^ d ≤ q.eval (r : ℝ) := by
  by_cases hdeg : q.natDegree = 0
  · have hd0 : d = 0 := Nat.eq_zero_of_le_zero (hdeg ▸ hd)
    subst hd0
    have heval : ∀ x : ℝ, q.eval x = q.leadingCoeff := by
      intro x
      conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]
      rw [Polynomial.eval_C, Polynomial.leadingCoeff, hdeg]
    exact ⟨q.leadingCoeff / 2, 0, half_pos hq, fun r _ => by
      simp only [pow_zero, mul_one]
      linarith [heval (r : ℝ)]⟩
  · exact poly_eventually_lower_bound_of_deg_ge_one q hq
      (Nat.one_le_iff_ne_zero.mpr hdeg) d hd

lemma L_part_coeff_lower_bound
    (ρ : ℝ) (hρ_pos : 0 < ρ) (k : ℕ) (hk : 0 < k) (N_poly : Polynomial ℝ)
    (hN_pos : 0 < Polynomial.eval ρ N_poly) :
    let L : Polynomial ℝ := 1 - Polynomial.C (1/ρ) * Polynomial.X
    ∃ (c : ℝ) (N : ℕ), 0 < c ∧
      ∀ r, N < r →
        c * (↑r) ^ (k - 1) * (1/ρ) ^ r ≤
        (PowerSeries.coeff r)
          ((↑N_poly : PowerSeries ℝ) * ((↑L : PowerSeries ℝ) ^ k)⁻¹) := by
  intro L
  obtain ⟨q, N₀, hq_lc, hq_eq⟩ := scaled_coeff_is_eventually_poly ρ hρ_pos k hk N_poly hN_pos
  have hq_deg : k - 1 ≤ q.natDegree :=
    scaled_coeff_poly_degree_ge ρ hρ_pos k hk N_poly hN_pos q N₀ hq_lc hq_eq
  obtain ⟨c, N₁, hc_pos, hc_bound⟩ := poly_eventually_lower_bound q hq_lc (k - 1) hq_deg
  refine ⟨c, max N₀ N₁, hc_pos, fun r hr => ?_⟩
  have hr0 : N₀ < r := lt_of_le_of_lt (le_max_left _ _) hr
  have hr1 : N₁ < r := lt_of_le_of_lt (le_max_right _ _) hr
  have h_scaled := hq_eq r hr0
  have h_poly_bound := hc_bound r hr1
  have h_combined : c * (r : ℝ) ^ (k - 1) ≤ ρ ^ r *
    (PowerSeries.coeff r) ((↑N_poly : PowerSeries ℝ) * ((↑L : PowerSeries ℝ) ^ k)⁻¹) := by
    rw [h_scaled]
    exact h_poly_bound
  exact divide_by_rho_pow ρ hρ_pos c (k - 1) r _ h_combined

lemma bound_transfer
    (C c : ℝ) (D E r : ℕ) (ρ ρ₂ : ℝ) (hρ_pos : 0 < ρ) (hρ₂_pos : 0 < ρ₂)
    (h : C * (↑r + 1) ^ D * (ρ / ρ₂) ^ r < c * (↑r) ^ E) :
    C * (↑r + 1) ^ D * (1 / ρ₂) ^ r < c * (↑r) ^ E * (1 / ρ) ^ r := by
  have h_key : (ρ / ρ₂ : ℝ) ^ r * (1 / ρ : ℝ) ^ r = (1 / ρ₂ : ℝ) ^ r := by
    rw [← mul_pow]
    congr 1
    field_simp
  have : C * (↑r + 1 : ℝ) ^ D * (1 / ρ₂ : ℝ) ^ r =
      C * (↑r + 1 : ℝ) ^ D * (ρ / ρ₂ : ℝ) ^ r * (1 / ρ : ℝ) ^ r := by
    rw [show C * (↑r + 1 : ℝ) ^ D * (ρ / ρ₂ : ℝ) ^ r * (1 / ρ : ℝ) ^ r =
        C * (↑r + 1 : ℝ) ^ D * ((ρ / ρ₂ : ℝ) ^ r * (1 / ρ : ℝ) ^ r) from by ring, h_key]
  rw [this]
  exact mul_lt_mul_of_pos_right h (by positivity)

lemma tendsto_add_one_pow_mul_geometric
    (D : ℕ) (q : ℝ) (hq_pos : 0 ≤ q) (hq_lt : q < 1) :
    Filter.Tendsto (fun r : ℕ => (↑r + 1) ^ D * q ^ r) Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · apply Filter.Eventually.of_forall
    intro r
    apply mul_nonneg
    · positivity
    · positivity
  · rw [Filter.eventually_atTop]
    exact ⟨1, fun r hr => by
      calc (↑r + 1) ^ D * q ^ r
          ≤ (2 * ↑r) ^ D * q ^ r := by
            apply mul_le_mul_of_nonneg_right
            · gcongr
              have : (r : ℝ) ≥ 1 := by exact_mod_cast hr
              linarith
            · positivity
        _ = 2 ^ D * (↑r ^ D * q ^ r) := by ring⟩
  · have h := tendsto_pow_const_mul_const_pow_of_lt_one D hq_pos hq_lt
    have : (2 : ℝ) ^ D * 0 = 0 := by ring
    rw [← this]
    exact Filter.Tendsto.const_mul _ h

lemma poly_geometric_eventually_lt
    (C c : ℝ) (_hC : 0 < C) (hc : 0 < c) (D E : ℕ) (q : ℝ) (hq_pos : 0 < q) (hq_lt : q < 1) :
    ∃ N : ℕ, ∀ r : ℕ, N < r →
      C * (↑r + 1) ^ D * q ^ r < c * (↑r) ^ E := by
  have htend := tendsto_add_one_pow_mul_geometric D q (le_of_lt hq_pos) hq_lt
  have htend_scaled : Filter.Tendsto (fun r : ℕ => C * ((↑r + 1) ^ D * q ^ r))
      Filter.atTop (nhds (C * 0)) :=
    htend.const_mul C
  rw [mul_zero] at htend_scaled
  have hev := (tendsto_order.mp htend_scaled).2 c hc
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N₁, hN₁⟩ := hev
  use N₁
  intro r hr
  have hr_ge : N₁ ≤ r := le_of_lt hr
  have hbound := hN₁ r hr_ge
  have hr_one : (1 : ℝ) ≤ (↑r : ℝ) := by
    norm_cast
    omega
  have hone_le_rpow : (1 : ℝ) ≤ (↑r : ℝ) ^ E := one_le_pow₀ hr_one
  calc C * (↑r + 1) ^ D * q ^ r
      = C * ((↑r + 1) ^ D * q ^ r) := by ring
    _ < c := hbound
    _ = c * 1 := by ring
    _ ≤ c * (↑r : ℝ) ^ E := mul_le_mul_of_nonneg_left hone_le_rpow (le_of_lt hc)

lemma S_part_eventually_dominated
    (ρ : ℝ) (hρ_pos : 0 < ρ) (k : ℕ) (hk : 0 < k) (N_poly M_poly : Polynomial ℝ) (S : Polynomial ℝ)
    (hN_pos : 0 < Polynomial.eval ρ N_poly) (hS_pos : 0 < Polynomial.eval ρ S)
    (hS_const : Polynomial.eval 0 S = 1)
    (hS_roots_larger : ∀ x : ℝ, Polynomial.eval x S = 0 → ρ < x) (hS_splits : S.Splits) :
    let L : Polynomial ℝ := 1 - Polynomial.C (1/ρ) * Polynomial.X
    ∃ N, ∀ r, N < r →
      |((PowerSeries.coeff r)
        ((↑M_poly : PowerSeries ℝ) * ((↑S : PowerSeries ℝ) ^ k)⁻¹))| <
      (PowerSeries.coeff r)
        ((↑N_poly : PowerSeries ℝ) * ((↑L : PowerSeries ℝ) ^ k)⁻¹) := by
  intro L
  by_cases hS_deg : S.natDegree = 0
  · obtain ⟨N₁, hN₁⟩ := S_part_eventually_zero_of_const M_poly S k hk hS_const hS_deg
    obtain ⟨N₂, hN₂⟩ := L_part_eventually_pos ρ hρ_pos k hk N_poly hN_pos
    exact ⟨max N₁ N₂, fun r hr => by
      rw [hN₁ r (lt_of_le_of_lt (le_max_left _ _) hr), abs_zero]
      exact hN₂ r (lt_of_le_of_lt (le_max_right _ _) hr)⟩
  · have hS_nconst : 0 < S.natDegree := Nat.pos_of_ne_zero hS_deg
    obtain ⟨C_S, D_S, ρ₂, hC_pos, hρ₂_gt, hbound⟩ :=
      S_part_coeff_bound ρ hρ_pos k hk M_poly S hS_pos hS_const hS_roots_larger hS_splits hS_nconst
    obtain ⟨c_L, N_L, hc_pos, hlower⟩ :=
      L_part_coeff_lower_bound ρ hρ_pos k hk N_poly hN_pos
    have hq : ρ / ρ₂ < 1 := (div_lt_one (lt_trans hρ_pos hρ₂_gt)).mpr hρ₂_gt
    have hq_pos : 0 < ρ / ρ₂ := div_pos hρ_pos (lt_trans hρ_pos hρ₂_gt)
    obtain ⟨N_cmp, hN_cmp⟩ := poly_geometric_eventually_lt
      C_S c_L hC_pos hc_pos D_S (k - 1) (ρ / ρ₂) hq_pos hq
    exact ⟨max N_L N_cmp, fun r hr => by
      have hr_L : N_L < r := lt_of_le_of_lt (le_max_left _ _) hr
      have hr_cmp : N_cmp < r := lt_of_le_of_lt (le_max_right _ _) hr
      calc |((PowerSeries.coeff r)
              ((↑M_poly : PowerSeries ℝ) * ((↑S : PowerSeries ℝ) ^ k)⁻¹))|
          ≤ C_S * (↑r + 1) ^ D_S * (1 / ρ₂) ^ r := hbound r
        _ < c_L * ↑r ^ (k - 1) * (1 / ρ) ^ r :=
            bound_transfer C_S c_L D_S (k - 1) r ρ ρ₂ hρ_pos
              (lt_trans hρ_pos hρ₂_gt) (hN_cmp r hr_cmp)
        _ ≤ (PowerSeries.coeff r)
              ((↑N_poly : PowerSeries ℝ) * ((↑L : PowerSeries ℝ) ^ k)⁻¹) := hlower r hr_L⟩

lemma sum_parts_eventually_pos
    (ρ : ℝ) (hρ_pos : 0 < ρ) (k : ℕ) (hk : 0 < k) (N_poly M_poly : Polynomial ℝ) (S : Polynomial ℝ)
    (hN_pos : 0 < Polynomial.eval ρ N_poly) (hS_pos : 0 < Polynomial.eval ρ S)
    (hS_const : Polynomial.eval 0 S = 1)
    (hS_roots_larger : ∀ x : ℝ, Polynomial.eval x S = 0 → ρ < x) (hS_splits : S.Splits) :
    let L : Polynomial ℝ := 1 - Polynomial.C (1/ρ) * Polynomial.X
    ∃ N, ∀ r, N < r →
      (0 : ℝ) < (PowerSeries.coeff r)
        ((↑N_poly : PowerSeries ℝ) * ((↑L : PowerSeries ℝ) ^ k)⁻¹ +
         (↑M_poly : PowerSeries ℝ) * ((↑S : PowerSeries ℝ) ^ k)⁻¹) := by
  intro L
  obtain ⟨N₁, hN₁⟩ := L_part_eventually_pos ρ hρ_pos k hk N_poly hN_pos
  obtain ⟨N₂, hN₂⟩ := S_part_eventually_dominated ρ hρ_pos k hk N_poly M_poly S
    hN_pos hS_pos hS_const hS_roots_larger hS_splits
  exact ⟨max N₁ N₂, fun r hr => by
    rw [map_add]
    linarith [hN₁ r (lt_of_le_of_lt (le_max_left _ _) hr),
              neg_lt_of_abs_lt (hN₂ r (lt_of_le_of_lt (le_max_right _ _) hr))]⟩

lemma proper_fraction_coeff_pos_over_R
    (m : ℕ) (hm : 2 ≤ m) (R_rem : Polynomial ℝ) (k : ℕ) (hk : 0 < k) (ρ : ℝ) (hρ_pos : 0 < ρ)
    (hρ_root : Polynomial.eval ρ (polyP ℝ m) = 0)
    (hρ_lower : ∀ j : ℕ, j < m → 0 < Polynomial.eval ρ (polyP ℝ j))
    (hR_pos : 0 < Polynomial.eval ρ R_rem) :
    ∃ N, ∀ r, N < r →
      (0 : ℝ) < (PowerSeries.coeff r)
        ((↑R_rem : PowerSeries ℝ) *
          ((↑(polyP ℝ m) : PowerSeries ℝ) ^ k)⁻¹) := by
  obtain ⟨S, hfact, hS_pos, hCop, hS_const, hS_roots, hS_splits⟩ :=
    polyP_factor_at_root m hm ρ hρ_pos hρ_root hρ_lower
  obtain ⟨N_poly, M_poly, hdecomp, hN_pos⟩ :=
    bezout_fraction_split m hm R_rem k hk ρ hρ_pos hR_pos S hfact hS_pos hCop
  obtain ⟨N₀, hN₀⟩ :=
    sum_parts_eventually_pos ρ hρ_pos k hk N_poly M_poly S
      hN_pos hS_pos hS_const hS_roots hS_splits
  exact ⟨N₀, fun r hr => by
    rw [hdecomp]
    exact hN₀ r hr⟩

lemma map_genFun_comm (R_poly : Polynomial ℚ) (m k : ℕ) :
    (PowerSeries.map (algebraMap ℚ ℝ))
      ((↑R_poly : PowerSeries ℚ) * ((↑(polyP ℚ m) : PowerSeries ℚ) ^ k)⁻¹) =
    (↑(Polynomial.map (algebraMap ℚ ℝ) R_poly) : PowerSeries ℝ) *
      ((↑(polyP ℝ m) : PowerSeries ℝ) ^ k)⁻¹ := by
  rw [map_mul]
  congr 1
  · rw [← Polynomial.polynomial_map_coe]
  · rw [map_algebraMap_inv_comm _ (polyP_coe_pow_constantCoeff_ne_zero ℚ m k)]
    congr 1
    rw [map_pow]
    congr 1
    rw [← Polynomial.polynomial_map_coe, polyP_map]

lemma proper_fraction_coeff_eventually_pos
    (m : ℕ) (hm : 2 ≤ m) (R_poly : Polynomial ℚ) (k : ℕ) (hk : 0 < k)
    (hR_pos_at_root : ∀ (ρ : ℝ), 0 < ρ →
      Polynomial.eval ρ (Polynomial.map (algebraMap ℚ ℝ) (polyP ℚ m)) = 0 →
      (∀ j : ℕ, j < m →
        0 < Polynomial.eval ρ
          (Polynomial.map (algebraMap ℚ ℝ) (polyP ℚ j))) →
      0 < Polynomial.eval ρ (Polynomial.map (algebraMap ℚ ℝ) R_poly)) :
    ∃ N, ∀ r, N < r →
      0 < (PowerSeries.coeff r)
        ((↑R_poly : PowerSeries ℚ) *
          ((↑(polyP ℚ m) : PowerSeries ℚ) ^ k)⁻¹) := by
  obtain ⟨ρ, hρ_pos, hρ_root, hρ_lower⟩ := polyP_roots_positive m hm
  have hR_pos := hR_pos_at_root ρ hρ_pos hρ_root hρ_lower
  have hρ_root_R : Polynomial.eval ρ (polyP ℝ m) = 0 := by
    rwa [← polyP_map (algebraMap ℚ ℝ)]
  have hρ_lower_R : ∀ j : ℕ, j < m → 0 < Polynomial.eval ρ (polyP ℝ j) := by
    intro j hj
    rw [← polyP_map (algebraMap ℚ ℝ)]
    exact hρ_lower j hj
  have hR_pos_R : 0 < Polynomial.eval ρ (Polynomial.map (algebraMap ℚ ℝ) R_poly) := hR_pos
  obtain ⟨N, hN⟩ := proper_fraction_coeff_pos_over_R m hm
    (Polynomial.map (algebraMap ℚ ℝ) R_poly) k hk ρ hρ_pos hρ_root_R hρ_lower_R hR_pos_R
  refine ⟨N, fun r hr => ?_⟩
  apply (pos_coeff_transfer_R_to_Q _ N _ r hr)
  intro r' hr'
  rw [map_genFun_comm]
  exact hN r' hr'

/-! ## Main Theorems -/

theorem genFun_eq_one_of_m_eq_one (K : Type*) [Field K]
    (n : ℕ) {s : ℕ} (ξ : Nat.Partition s) (h_parts : ∀ i ∈ ξ.parts, i ≤ 1) :
    genFun K 1 n ξ = 1 := by
  have h_partition : partitionPoly K ξ = 1 :=
    partitionPoly_eq_one_of_parts_le_one K ξ h_parts
  have h_coe : (↑(polyP K 1) : PowerSeries K) = 1 := by
    simp [show polyP K 1 = (1 : Polynomial K) from rfl, Polynomial.coe_one]
  have h_inv : ((1 : PowerSeries K) ^ (n / 1 + 1))⁻¹ = 1 := by simp
  simp only [genFun, Nat.mod_one, Nat.sub_zero, Nat.sub_self, polyP_zero,
    h_partition, h_coe, h_inv, mul_one, Polynomial.coe_one]

theorem genFun_is_polynomial (K : Type*) [Field K]
    (m n : ℕ) {s : ℕ} (ξ : Nat.Partition s) (hm : 2 ≤ m) (h_parts : ∀ i ∈ ξ.parts, i ≤ m)
    (h_t : n / m + 1 ≤ countMaxParts m ξ) :
    ∃ N, ∀ r, N < r → genFunCoeff K m n r ξ = 0 := by
  obtain ⟨P, hP⟩ := genFun_is_poly_coe K m n ξ hm h_parts h_t
  exact ⟨P.natDegree, fun r hr => by
    simp only [genFunCoeff, hP]
    exact poly_coe_eventually_zero K P r hr⟩

theorem genFun_coeff_eventually_pos
    (m n : ℕ) {s : ℕ} (ξ : Nat.Partition s) (hm : 2 ≤ m) (h_parts : ∀ i ∈ ξ.parts, i ≤ m)
    (h_t : countMaxParts m ξ ≤ n / m) :
    ∃ N, ∀ r, N < r → 0 < genFunCoeff ℚ m n r ξ := by
  obtain ⟨A, k, hk, hgenFun, hA_pos_at_roots⟩ :=
    genFun_as_rational_fraction_with_pos_numerator m n ξ hm h_parts h_t
  have hpow_coe : (↑(polyP ℚ m) : PowerSeries ℚ) ^ k =
      ↑(polyP ℚ m ^ k) := by
    rw [Polynomial.coe_pow]
  have hD_ne : PowerSeries.constantCoeff
      (↑(polyP ℚ m ^ k) : PowerSeries ℚ) ≠ 0 := by
    rw [← hpow_coe]
    exact polyP_coe_pow_constantCoeff_ne_zero ℚ m k
  have hgenFun' : genFun ℚ m n ξ = ↑A *
      (↑(polyP ℚ m ^ k) : PowerSeries ℚ)⁻¹ := by
    rw [hgenFun, hpow_coe]
  obtain ⟨S, R, N₁, hdiv, hcoeff_eq⟩ :=
    coeff_rational_fraction_eq_proper_part A (polyP ℚ m ^ k) hD_ne
  have hR_pos : ∀ (ρ : ℝ), 0 < ρ →
      Polynomial.eval ρ (Polynomial.map (algebraMap ℚ ℝ) (polyP ℚ m)) = 0 →
      (∀ j : ℕ, j < m →
        0 < Polynomial.eval ρ
          (Polynomial.map (algebraMap ℚ ℝ) (polyP ℚ j))) →
      0 < Polynomial.eval ρ (Polynomial.map (algebraMap ℚ ℝ) R) := by
    intro ρ hρ_pos hρ_root hρ_other
    have hA_pos : 0 < Polynomial.eval ρ (Polynomial.map (algebraMap ℚ ℝ) A) :=
      hA_pos_at_roots ρ hρ_pos hρ_root hρ_other
    exact remainder_positive_at_roots A (polyP ℚ m ^ k) S R hdiv hD_ne ρ
      (by simp [Polynomial.map_pow, Polynomial.eval_pow, hρ_root, zero_pow hk.ne'])
      hA_pos
  obtain ⟨N₂, hN₂⟩ := proper_fraction_coeff_eventually_pos m hm R k hk hR_pos
  refine ⟨max N₁ N₂, fun r hr => ?_⟩
  simp only [genFunCoeff, hgenFun']
  rw [hcoeff_eq r (by omega)]
  rw [← hpow_coe] at hcoeff_eq ⊢
  exact hN₂ r (by omega)

end Biswal.Theorem1

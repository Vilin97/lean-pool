/-
Copyright (c) 2026 jjaassoonn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jjaassoonn
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Combinatorial coefficient formulas and nonnegativity (Theorems 2 and 3)

This file formalizes Theorems 2 and 3 of the Chebyshev-quotient /
Demazure-multiplicity paper: explicit Cauchy-product and matrix-inverse formulas
for the generating-function coefficients and their nonnegativity via a
Dyck-path counting model.
-/

namespace Biswal.Theorem23

/-! ## Definition 1: Chebyshev-type polynomials -/

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

/-! ## Definition 2: Partition polynomial -/

/-- The partition polynomial of `ξ`: the product of `polyP R` over the parts of `ξ`. -/
noncomputable def partitionPoly (R : Type*) [CommRing R] {s : ℕ}
    (ξ : Nat.Partition s) : Polynomial R :=
  (ξ.parts.map (polyP R)).prod

/-! ## Definition 3: Generating function -/

/-- The generating function attached to `ξ` with parameters `m` and `μ`, as a power series. -/
noncomputable def genFun (K : Type*) [Field K] (m μ : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) : PowerSeries K :=
  let μ₁ := μ / m
  let μ₀ := μ % m
  (↑(polyP K (m - μ₀ - 1) * partitionPoly K ξ) : PowerSeries K) *
    ((↑(polyP K m) : PowerSeries K) ^ (μ₁ + 1))⁻¹

/-- The `r`-th coefficient of the generating function `genFun K m μ ξ`. -/
noncomputable def genFunCoeff (K : Type*) [Field K] (m μ r : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) : K :=
  (PowerSeries.coeff r) (genFun K m μ ξ)

/-! ## Definition 4: Count of maximal parts -/

/-- The number of parts of `ξ` equal to `m`. -/
def countMaxParts (m : ℕ) {s : ℕ} (ξ : Nat.Partition s) : ℕ :=
  Multiset.count m ξ.parts

/-! ## Definition 5: Reduced parameters -/

/-- The multiset of parts of `ξ` strictly less than `m`. -/
def nonMaxParts (m : ℕ) {s : ℕ} (ξ : Nat.Partition s) : Multiset ℕ :=
  ξ.parts.filter (· < m)

/-- The product of `polyP K` over the parts of `ξ` strictly less than `m`. -/
noncomputable def nonMaxPartsPoly (K : Type*) [CommRing K] (m : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) : Polynomial K :=
  ((nonMaxParts m ξ).map (polyP K)).prod

/-- The multiset of reduced indices `m - μ % m - 1` prepended to the non-maximal parts of `ξ`. -/
def alphaMultiset (m μ : ℕ) {s : ℕ} (ξ : Nat.Partition s) : Multiset ℕ :=
  (m - μ % m - 1) ::ₘ nonMaxParts m ξ

/-- The reduced exponent `μ / m + 1 - countMaxParts m ξ`. -/
def reducedK (m μ : ℕ) {s : ℕ} (ξ : Nat.Partition s) : ℕ :=
  μ / m + 1 - countMaxParts m ξ

/-- The number of entries in `alphaMultiset m μ ξ`. -/
def alphaCount (m μ : ℕ) {s : ℕ} (ξ : Nat.Partition s) : ℕ :=
  Multiset.card (alphaMultiset m μ ξ)

/-- The product of `polyP K` over the entries of `alphaMultiset m μ ξ`. -/
noncomputable def alphaProd (K : Type*) [CommRing K] (m μ : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) : Polynomial K :=
  ((alphaMultiset m μ ξ).map (polyP K)).prod

/-- The entries of `alphaMultiset m μ ξ` as a list. -/
noncomputable def alphaValues (m μ : ℕ) {s : ℕ} (ξ : Nat.Partition s) : List ℕ :=
  (alphaMultiset m μ ξ).toList

/-! ## Basic properties of polyP -/

lemma polyP_constantCoeff (R : Type*) [CommRing R] (n : ℕ) :
    (polyP R n).coeff 0 = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 | 1 => simp [polyP]
    | n + 2 =>
      simp [polyP, ih (n + 1) (by omega), ih n (by omega)]

lemma polyP_coe_constantCoeff_ne_zero (K : Type*) [Field K] (m : ℕ) :
    PowerSeries.constantCoeff (↑(polyP K m) : PowerSeries K) ≠ 0 := by
  simp [polyP_constantCoeff]

lemma polyP_coe_pow_constantCoeff_ne_zero (K : Type*) [Field K] (m k : ℕ) :
    PowerSeries.constantCoeff ((↑(polyP K m) : PowerSeries K) ^ k) ≠ 0 := by
  rw [map_pow]
  exact pow_ne_zero _ (polyP_coe_constantCoeff_ne_zero K m)

/-! ## Definition 6: Coefficients of 1/p_m(x) -/

/-- The `u`-th coefficient of the power-series inverse `1 / polyP K m`. -/
noncomputable def bCoeff (K : Type*) [Field K] (m u : ℕ) : K :=
  (PowerSeries.coeff u) ((↑(polyP K m) : PowerSeries K)⁻¹)

/-! ## Definition 7: Coefficients of p_a · p_b / p_m -/

/-- The `u`-th coefficient of the power series `polyP K a * polyP K b / polyP K m`. -/
noncomputable def dCoeff (K : Type*) [Field K] (m a b u : ℕ) : K :=
  (PowerSeries.coeff u)
    ((↑(polyP K a * polyP K b) : PowerSeries K) *
      ((↑(polyP K m) : PowerSeries K))⁻¹)

/-! ## Reduced form of the generating function -/

lemma partitionPoly_eq_pow_mul_nonMax (K : Type*) [CommRing K] (m : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) (h_parts : ∀ i ∈ ξ.parts, i ≤ m) :
    partitionPoly K ξ = polyP K m ^ countMaxParts m ξ * nonMaxPartsPoly K m ξ := by
  unfold partitionPoly nonMaxPartsPoly nonMaxParts countMaxParts
  conv_lhs =>
    rw [show ξ.parts = Multiset.filter (fun x => x = m) ξ.parts +
      Multiset.filter (fun x => ¬(x = m)) ξ.parts from
      (Multiset.filter_add_not (fun x => x = m) ξ.parts).symm]
  rw [Multiset.map_add, Multiset.prod_add, Multiset.filter_eq', Multiset.map_replicate,
    Multiset.prod_replicate,
    Multiset.filter_congr fun x hx =>
      ⟨fun h => Nat.lt_of_le_of_ne (h_parts x hx) h, fun h => Nat.ne_of_lt h⟩]

lemma alphaProd_eq_mul_nonMax (K : Type*) [CommRing K] (m μ : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) :
    alphaProd K m μ ξ = polyP K (m - μ % m - 1) * nonMaxPartsPoly K m ξ := by
  simp only [alphaProd, alphaMultiset, nonMaxPartsPoly, Multiset.map_cons, Multiset.prod_cons]

lemma ps_inv_pow_eq (K : Type*) [Field K] (φ : PowerSeries K) (k : ℕ) :
    (φ ^ k)⁻¹ = φ⁻¹ ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, PowerSeries.mul_inv_rev, ih, mul_comm, pow_succ]

lemma pow_mul_pow_inv_cancel (K : Type*) [Field K] (P : PowerSeries K) (t e : ℕ)
    (hte : t ≤ e) (hP : PowerSeries.constantCoeff P ≠ 0) :
    P ^ t * (P ^ e)⁻¹ = (P ^ (e - t))⁻¹ := by
  rw [ps_inv_pow_eq K P e, ps_inv_pow_eq K P (e - t),
    show e = t + (e - t) from (Nat.add_sub_cancel' hte).symm, pow_add, ← mul_assoc,
    show P ^ t * P⁻¹ ^ t = 1 from by
      rw [← ps_inv_pow_eq K P t]
      exact PowerSeries.mul_inv_cancel _ (by
        rw [map_pow]
        exact pow_ne_zero _ hP),
    one_mul]
  congr 1
  omega

theorem genFun_eq_reduced (K : Type*) [Field K] (m μ : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) (_hm : 2 ≤ m) (h_parts : ∀ i ∈ ξ.parts, i ≤ m)
    (hk : countMaxParts m ξ ≤ μ / m + 1) :
    genFun K m μ ξ =
      (↑(alphaProd K m μ ξ) : PowerSeries K) *
        ((↑(polyP K m) : PowerSeries K) ^ reducedK m μ ξ)⁻¹ := by
  unfold genFun
  simp only
  rw [partitionPoly_eq_pow_mul_nonMax K m ξ h_parts,
    show polyP K (m - μ % m - 1) * (polyP K m ^ countMaxParts m ξ * nonMaxPartsPoly K m ξ) =
      alphaProd K m μ ξ * polyP K m ^ countMaxParts m ξ from by
        rw [alphaProd_eq_mul_nonMax]
        ring,
    Polynomial.coe_mul, Polynomial.coe_pow, mul_assoc,
    pow_mul_pow_inv_cancel K (↑(polyP K m) : PowerSeries K)
      (countMaxParts m ξ) (μ / m + 1) hk (polyP_coe_constantCoeff_ne_zero K m)]
  rfl

/-! ## Coefficient formula for polyP -/

private lemma polyP_coeff_base (R : Type*) [CommRing R] (n : ℕ) (hn : n ≤ 1) (j : ℕ) :
    (polyP R n).coeff j = (-1 : R) ^ j * (Nat.choose (n - j) j : ℕ) := by
  interval_cases n <;> cases j with
  | zero => simp [polyP]
  | succ j => simp [polyP, Polynomial.coeff_one, pow_succ]

private lemma polyP_coeff_step_pos (R : Type*) [CommRing R] (m : ℕ) (j : ℕ) (hj : 1 ≤ j) :
    (-1 : R) ^ j * (Nat.choose (m + 1 - j) j : ℕ) -
    (-1 : R) ^ (j - 1) * (Nat.choose (m - (j - 1)) (j - 1) : ℕ) =
    (-1 : R) ^ j * (Nat.choose (m + 2 - j) j : ℕ) := by
  by_cases hjm : j ≤ m + 1
  · have h1 : m + 1 - j + 1 = m + 2 - j := by omega
    have h2 : j - 1 + 1 = j := by omega
    have h3 : m - (j - 1) = m + 1 - j := by omega
    have h4 : (m + 1 - j).choose j + (m + 1 - j).choose (j - 1) = (m + 2 - j).choose j := by
      grind only [Nat.choose_eq_choose_pred_add]
    have h5 : (-1 : R) ^ j * (Nat.choose (m + 1 - j) j : ℕ) -
        (-1 : R) ^ (j - 1) * (Nat.choose (m - (j - 1)) (j - 1) : ℕ) =
        (-1 : R) ^ j * (Nat.choose (m + 1 - j) j + Nat.choose (m + 1 - j) (j - 1) : ℕ) := by
      grind
    rw [h5]
    congr 1
    exact congrArg Nat.cast h4
  · simp only [show m + 1 - j = 0 by omega, show m + 2 - j = 0 by omega,
      show m - (j - 1) = 0 by omega,
      Nat.choose_eq_zero_iff.mpr (by omega : 0 < j),
      Nat.choose_eq_zero_iff.mpr (by omega : 0 < j - 1),
      Nat.cast_zero, mul_zero, sub_self]

theorem polyP_coeff (R : Type*) [CommRing R] (n j : ℕ) :
    (polyP R n).coeff j = (-1 : R) ^ j * (Nat.choose (n - j) j : ℕ) := by
  revert j
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 | 1 => exact polyP_coeff_base R _ (by omega)
    | m + 2 =>
      intro j
      match j with
      | 0 => simp [polyP_constantCoeff]
      | j + 1 =>
        rw [show polyP R (m + 2) = polyP R (m + 1) - Polynomial.X * polyP R m from rfl,
          Polynomial.coeff_sub, Polynomial.coeff_X_mul,
          ih (m + 1) (by omega) (j + 1), ih m (by omega) j,
          show m + 1 - (j + 1) = m - j by omega,
          show m + 2 - (j + 1) = m + 1 - j by omega]
        have key := polyP_coeff_step_pos R m (j + 1) (by omega)
        simp only [Nat.add_sub_cancel,
          show m + 1 - (j + 1) = m - j by omega,
          show m + 2 - (j + 1) = m + 1 - j by omega] at key
        exact key

theorem D_coeff_mk (K : Type*) [Field K] (m a b : ℕ) :
    (↑(polyP K a * polyP K b) : PowerSeries K) * ((↑(polyP K m) : PowerSeries K))⁻¹ =
      PowerSeries.mk (dCoeff K m a b) := by
  ext n
  simp [dCoeff, PowerSeries.coeff_mk]

/-! ## Theorem 2: Cauchy product form -/

theorem thm_comb_cauchy (K : Type*) [Field K] (m μ : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) (hm : 2 ≤ m) (h_parts : ∀ i ∈ ξ.parts, i ≤ m)
    (hk : countMaxParts m ξ ≤ μ / m + 1) (r : ℕ) :
    genFunCoeff K m μ r ξ =
      (PowerSeries.coeff r)
        ((↑(alphaProd K m μ ξ) : PowerSeries K) *
          ((↑(polyP K m) : PowerSeries K)⁻¹) ^ reducedK m μ ξ) := by
  unfold genFunCoeff
  rw [genFun_eq_reduced K m μ ξ hm h_parts hk, ps_inv_pow_eq]

/-! ## Theorem 2: Explicit summation formula -/

private lemma list_prod_map_eq_fin_prod (αs : List ℕ) :
    (αs.map (polyP ℚ)).prod = ∏ i : Fin αs.length, polyP ℚ (αs.getD i.val 0) := by
  simp

private lemma alphaProd_eq_fin_prod (m μ : ℕ) {s : ℕ} (ξ : Nat.Partition s) :
    let αs := alphaValues m μ ξ
    let L1 := αs.length
    alphaProd ℚ m μ ξ = ∏ i : Fin L1, polyP ℚ (αs.getD i.val 0) := by
  simp only [alphaProd, alphaValues]
  rw [← Multiset.prod_map_toList]
  exact list_prod_map_eq_fin_prod _

private lemma coe_finset_prod_eq_prod_coe (n : ℕ) (f : Fin n → Polynomial ℚ) :
    (↑(∏ i : Fin n, f i) : PowerSeries ℚ) = ∏ i : Fin n, (↑(f i) : PowerSeries ℚ) :=
  map_prod Polynomial.coeToPowerSeries.ringHom f Finset.univ

private lemma inner_prod_eq (αs : List ℕ) (m k : ℕ) (f : Fin (αs.length + k) → ℕ) :
    let L1 := αs.length
    (∏ j : Fin (L1 + k),
      (PowerSeries.coeff (f j))
        (Fin.addCases
          (fun i : Fin L1 => (↑(polyP ℚ (αs.getD i.val 0)) : PowerSeries ℚ))
          (fun _ : Fin k => ((↑(polyP ℚ m) : PowerSeries ℚ)⁻¹))
          j)) =
    (∏ i : Fin L1,
      ((-1 : ℚ) ^ (f (Fin.castAdd k i)) *
        ↑(Nat.choose (αs.getD i.val 0 - f (Fin.castAdd k i))
                      (f (Fin.castAdd k i))))) *
    (∏ ν : Fin k,
      bCoeff ℚ m (f (Fin.natAdd L1 ν))) := by
  intro L1
  rw [Fin.prod_univ_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [Fin.addCases_left, Polynomial.coeff_coe]
    exact polyP_coeff ℚ _ _
  · apply Finset.prod_congr rfl
    intro i _
    rw [Fin.addCases_right]
    rfl

private lemma coeff_fin_prod_eq_antidiag_sum' (n r : ℕ) (F : Fin n → PowerSeries ℚ) :
    (PowerSeries.coeff r) (∏ j : Fin n, F j) =
      ∑ f ∈ Finset.Nat.antidiagonalTuple n r,
        ∏ j : Fin n, (PowerSeries.coeff (f j)) (F j) := by
  rw [PowerSeries.coeff_prod F r Finset.univ]
  exact Finset.sum_equiv Finsupp.equivFunOnFinite
    (fun l => ⟨fun h => by simp_all [Finset.Nat.mem_antidiagonalTuple],
              fun h => by simp_all [Finset.Nat.mem_antidiagonalTuple]⟩)
    fun l _ => by congr 1

lemma cauchy_product_as_fin_prod (m μ : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) (r : ℕ) :
    let αs := alphaValues m μ ξ
    let L1 := αs.length
    let k := reducedK m μ ξ
    (PowerSeries.coeff r)
      ((↑(alphaProd ℚ m μ ξ) : PowerSeries ℚ) *
        ((↑(polyP ℚ m) : PowerSeries ℚ)⁻¹) ^ k) =
    ∑ f ∈ Finset.Nat.antidiagonalTuple (L1 + k) r,
      (∏ i : Fin L1,
        ((-1 : ℚ) ^ (f (Fin.castAdd k i)) *
          ↑(Nat.choose (αs.getD i.val 0 - f (Fin.castAdd k i))
                        (f (Fin.castAdd k i))))) *
      (∏ ν : Fin k,
        bCoeff ℚ m (f (Fin.natAdd L1 ν))) := by
  intro αs L1 k
  rw [alphaProd_eq_fin_prod m μ ξ, coe_finset_prod_eq_prod_coe _ _]
  let F : Fin (L1 + k) → PowerSeries ℚ :=
    Fin.addCases
      (fun i : Fin L1 => (↑(polyP ℚ (αs.getD i.val 0)) : PowerSeries ℚ))
      (fun _ : Fin k => ((↑(polyP ℚ m) : PowerSeries ℚ)⁻¹))
  have hmerge : (∏ i : Fin L1, (↑(polyP ℚ (αs.getD i.val 0)) : PowerSeries ℚ)) *
      ((↑(polyP ℚ m) : PowerSeries ℚ)⁻¹) ^ k = ∏ j : Fin (L1 + k), F j := by
    simp only [F, Fin.prod_univ_add]
    congr 1
    · exact Finset.prod_congr rfl fun i _ => by simp [Fin.addCases_left]
    · rw [show ((↑(polyP ℚ m) : PowerSeries ℚ)⁻¹) ^ k =
        ∏ _ν : Fin k, ((↑(polyP ℚ m) : PowerSeries ℚ)⁻¹) from (Fin.prod_const k _).symm]
      exact Finset.prod_congr rfl fun i _ => by simp [Fin.addCases_right]
  rw [hmerge, coeff_fin_prod_eq_antidiag_sum' (L1 + k) r F]
  exact Finset.sum_congr rfl fun f _ => inner_prod_eq αs m k f

theorem thm_comb (m μ : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) (hm : 2 ≤ m) (h_parts : ∀ i ∈ ξ.parts, i ≤ m)
    (hk : countMaxParts m ξ ≤ μ / m + 1) (r : ℕ) :
    let αs := alphaValues m μ ξ
    let L1 := αs.length
    let k := reducedK m μ ξ
    genFunCoeff ℚ m μ r ξ =
      ∑ f ∈ Finset.Nat.antidiagonalTuple (L1 + k) r,
        (∏ i : Fin L1,
          ((-1 : ℚ) ^ (f (Fin.castAdd k i)) *
            ↑(Nat.choose (αs.getD i.val 0 - f (Fin.castAdd k i))
                          (f (Fin.castAdd k i))))) *
        (∏ ν : Fin k,
          bCoeff ℚ m (f (Fin.natAdd L1 ν))) := by
  intro αs L1 k
  rw [thm_comb_cauchy ℚ m μ ξ hm h_parts hk r]
  exact cauchy_product_as_fin_prod m μ ξ r

/-! ## Theorem 3: Part (i) - Factorization -/

lemma coe_prod_mul_inv_pow_eq_prod (m k : ℕ)
    (pairs : Fin k → ℕ × ℕ) :
    (↑(∏ ν : Fin k, (polyP ℚ (pairs ν).1 * polyP ℚ (pairs ν).2)) : PowerSeries ℚ) *
        ((↑(polyP ℚ m) : PowerSeries ℚ)⁻¹) ^ k =
      ∏ ν : Fin k, ((↑(polyP ℚ (pairs ν).1 * polyP ℚ (pairs ν).2) : PowerSeries ℚ) *
        ((↑(polyP ℚ m) : PowerSeries ℚ))⁻¹) := by
  rw [show (↑(∏ ν : Fin k, (polyP ℚ (pairs ν).1 * polyP ℚ (pairs ν).2)) : PowerSeries ℚ) =
        ∏ ν : Fin k, (↑(polyP ℚ (pairs ν).1 * polyP ℚ (pairs ν).2) : PowerSeries ℚ) from by
      rw [← Polynomial.coeToPowerSeries.ringHom_apply]
      simp only [map_prod, Polynomial.coeToPowerSeries.ringHom_apply],
    show ((↑(polyP ℚ m) : PowerSeries ℚ)⁻¹) ^ k =
        ∏ _ν : Fin k, ((↑(polyP ℚ m) : PowerSeries ℚ)⁻¹) from (Fin.prod_const k _).symm]
  exact Finset.prod_mul_distrib.symm

theorem thm_manifest_factorization (m μ : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) (hm : 2 ≤ m) (h_parts : ∀ i ∈ ξ.parts, i ≤ m)
    (hk_nonneg : countMaxParts m ξ ≤ μ / m + 1)
    (k : ℕ) (hk_eq : k = reducedK m μ ξ)
    (pairs : Fin k → ℕ × ℕ)
    (h_bound : ∀ ν, (pairs ν).1 ≤ m - 1 ∧ (pairs ν).2 ≤ m - 1 ∧
                     (pairs ν).1 + (pairs ν).2 ≤ m - 1)
    (h_factor : alphaProd ℚ m μ ξ =
      ∏ ν : Fin k, (polyP ℚ (pairs ν).1 * polyP ℚ (pairs ν).2)) :
    genFun ℚ m μ ξ =
      ∏ ν : Fin k,
        PowerSeries.mk (dCoeff ℚ m (pairs ν).1 (pairs ν).2) := by
  rw [genFun_eq_reduced ℚ m μ ξ hm h_parts hk_nonneg, h_factor]
  subst hk_eq
  rw [ps_inv_pow_eq ℚ (↑(polyP ℚ m)) (reducedK m μ ξ),
    coe_prod_mul_inv_pow_eq_prod m (reducedK m μ ξ) pairs]
  congr 1
  ext ν : 1
  exact D_coeff_mk ℚ m (pairs ν).1 (pairs ν).2

/-! ## Theorem 3: Part (i), coefficient form -/

lemma coeff_prod_mk_eq_sum_antidiag (k r : ℕ) (g : Fin k → ℕ → ℚ) :
    (PowerSeries.coeff r) (∏ ν : Fin k, PowerSeries.mk (g ν)) =
      ∑ f ∈ Finset.Nat.antidiagonalTuple k r,
        ∏ ν : Fin k, g ν (f ν) := by
  rw [coeff_fin_prod_eq_antidiag_sum' k r (fun ν => PowerSeries.mk (g ν))]
  simp_rw [PowerSeries.coeff_mk]

theorem thm_manifest_coeff_formula (m μ : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) (hm : 2 ≤ m) (h_parts : ∀ i ∈ ξ.parts, i ≤ m)
    (hk_nonneg : countMaxParts m ξ ≤ μ / m + 1)
    (k : ℕ) (hk_eq : k = reducedK m μ ξ)
    (pairs : Fin k → ℕ × ℕ)
    (h_bound : ∀ ν, (pairs ν).1 ≤ m - 1 ∧ (pairs ν).2 ≤ m - 1 ∧
                     (pairs ν).1 + (pairs ν).2 ≤ m - 1)
    (h_factor : alphaProd ℚ m μ ξ =
      ∏ ν : Fin k, (polyP ℚ (pairs ν).1 * polyP ℚ (pairs ν).2))
    (r : ℕ) :
    genFunCoeff ℚ m μ r ξ =
      ∑ f ∈ Finset.Nat.antidiagonalTuple k r,
        ∏ ν : Fin k, dCoeff ℚ m (pairs ν).1 (pairs ν).2 (f ν) := by
  unfold genFunCoeff
  rw [thm_manifest_factorization m μ ξ hm h_parts hk_nonneg k hk_eq pairs h_bound h_factor]
  exact coeff_prod_mk_eq_sum_antidiag k r (fun ν => dCoeff ℚ m (pairs ν).1 (pairs ν).2)

/-! ## Theorem 3: Part (ii) - Nonnegativity of dCoeff -/

lemma polyP_map_intCast (n : ℕ) :
    polyP ℚ n = Polynomial.map (Int.castRingHom ℚ) (polyP ℤ n) := by
  ext j
  simp [Polynomial.coeff_map, polyP_coeff]

lemma polyP_coe_int_constantCoeff (m : ℕ) :
    PowerSeries.constantCoeff (↑(polyP ℤ m) : PowerSeries ℤ) = 1 := by
  simp [polyP_constantCoeff]

lemma polyP_map_coe_eq (m : ℕ) :
    (PowerSeries.map (Int.castRingHom ℚ)) (↑(polyP ℤ m) : PowerSeries ℤ) =
    (↑(polyP ℚ m) : PowerSeries ℚ) := by
  rw [polyP_map_intCast m]
  exact Polynomial.polynomial_map_coe.symm

lemma polyP_inv_map_eq (m : ℕ) :
    (PowerSeries.map (Int.castRingHom ℚ))
      ((↑(polyP ℤ m) : PowerSeries ℤ).invOfUnit 1) =
    (↑(polyP ℚ m) : PowerSeries ℚ)⁻¹ := by
  rw [PowerSeries.eq_inv_iff_mul_eq_one (polyP_coe_constantCoeff_ne_zero ℚ m), mul_comm,
    ← polyP_map_coe_eq, ← map_mul, PowerSeries.mul_invOfUnit _ 1 (by
      rw [Units.val_one]
      exact polyP_coe_int_constantCoeff m), map_one]

lemma polyP_inv_coeff_is_int (m u : ℕ) :
    ∃ z : ℤ, (PowerSeries.coeff u) ((↑(polyP ℚ m) : PowerSeries ℚ)⁻¹) = ↑z := by
  rw [← polyP_inv_map_eq m, PowerSeries.coeff_map]
  exact ⟨_, rfl⟩

lemma polyP_prod_coeff_is_int (a b u : ℕ) :
    ∃ z : ℤ, (PowerSeries.coeff u) (↑(polyP ℚ a * polyP ℚ b) : PowerSeries ℚ) = ↑z := by
  set p := polyP ℤ a * polyP ℤ b
  refine ⟨p.coeff u, ?_⟩
  rw [show (↑(polyP ℚ a * polyP ℚ b) : PowerSeries ℚ) =
      (↑(Polynomial.map (Int.castRingHom ℚ) p) : PowerSeries ℚ) from by
    congr 1
    rw [Polynomial.map_mul, ← polyP_map_intCast a, ← polyP_map_intCast b]]
  simp

lemma sum_int_cast_of_each_int {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, ∃ z : ℤ, f i = ↑z) :
    ∃ z : ℤ, ∑ i ∈ s, f i = ↑z := by
  induction s using Finset.cons_induction with
  | empty => exact ⟨0, by simp⟩
  | cons a s ha ih =>
    obtain ⟨z₁, hz₁⟩ := hf a (Finset.mem_cons_self a s)
    obtain ⟨z₂, hz₂⟩ := ih (fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi)))
    exact ⟨z₁ + z₂, by rw [Finset.sum_cons, hz₁, hz₂, Int.cast_add]⟩

lemma int_coeff_mul_int_coeff (α β : PowerSeries ℚ)
    (hα : ∀ n, ∃ z : ℤ, (PowerSeries.coeff n) α = ↑z)
    (hβ : ∀ n, ∃ z : ℤ, (PowerSeries.coeff n) β = ↑z)
    (u : ℕ) :
    ∃ z : ℤ, (PowerSeries.coeff u) (α * β) = ↑z := by
  rw [PowerSeries.coeff_mul]
  exact sum_int_cast_of_each_int _ _ fun p _ =>
    let ⟨z₁, hz₁⟩ := hα p.1
    let ⟨z₂, hz₂⟩ := hβ p.2
    ⟨z₁ * z₂, by rw [hz₁, hz₂, Int.cast_mul]⟩

lemma D_coeff_is_int (m a b u : ℕ) :
    ∃ z : ℤ, dCoeff ℚ m a b u = ↑z :=
  int_coeff_mul_int_coeff _ _
    (fun n => polyP_prod_coeff_is_int a b n)
    (fun n => polyP_inv_coeff_is_int m n)
    u

/-! ### Transfer matrix decomposition (Steps 2-7 of the proof) -/

/-- The tridiagonal transfer matrix with `1` on the diagonal, `-1` on the
superdiagonal, and `-X` on the subdiagonal, whose inverse encodes the path counts. -/
noncomputable def stripMatrix (m : ℕ) : Matrix (Fin m) (Fin m) (PowerSeries ℚ) :=
  fun i j =>
    if i = j then 1
    else if j.val = i.val + 1 then -1
    else if i.val = j.val + 1 then -(PowerSeries.X : PowerSeries ℚ)
    else 0

/-! #### Helper lemmas for stripMatrix_det -/

private lemma stripMatrix_submatrix_last_last (n : ℕ) :
    (stripMatrix (n + 2)).submatrix (Fin.last (n + 1)).succAbove (Fin.last (n + 1)).succAbove =
      stripMatrix (n + 1) := by
  ext i j
  simp [Matrix.submatrix, stripMatrix, Fin.succAbove_last]

private lemma submatrix_last_col_zero (n : ℕ) (j₀ : Fin (n + 2)) (hj₀ : j₀.val = n)
    (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    ((stripMatrix (n + 2)).submatrix
      (Fin.last (n + 1)).succAbove
      j₀.succAbove) i (Fin.last n) = 0 := by
  simp only [Matrix.submatrix_apply, stripMatrix]
  have hi_lt := Fin.val_lt_last hi
  have hcol : (j₀.succAbove (Fin.last n)).val = n + 1 := by simp [Fin.succAbove, Fin.lt_def, hj₀]
  split_ifs <;> simp_all [Fin.ext_iff, Fin.succAbove_last, Fin.val_castSucc]
  omega

private lemma stripMatrix_val_eq (m₁ m₂ : ℕ) (r₁ : Fin m₁) (c₁ : Fin m₁) (r₂ : Fin m₂) (c₂ : Fin m₂)
    (hr : r₁.val = r₂.val) (hc : c₁.val = c₂.val) :
    stripMatrix m₁ r₁ c₁ = stripMatrix m₂ r₂ c₂ := by
  unfold stripMatrix
  simp only [Fin.ext_iff, hr, hc]

private lemma double_submatrix_eq_stripMatrix (n : ℕ) (j₀ : Fin (n + 2)) (hj₀ : j₀.val = n) :
    (((stripMatrix (n + 2)).submatrix
      (Fin.last (n + 1)).succAbove
      j₀.succAbove).submatrix
      (Fin.last n).succAbove
      (Fin.last n).succAbove) = stripMatrix n := by
  rw [Matrix.submatrix_submatrix]
  funext i j
  simp only [Matrix.submatrix_apply, Function.comp_apply]
  exact stripMatrix_val_eq (n + 2) n _ _ i j
    (by simp [Fin.succAbove_last, Fin.val_castSucc])
    (by simp only [Fin.succAbove_last]
        have : j.castSucc.castSucc < j₀ := by
          rw [Fin.lt_def]
          simp [Fin.val_castSucc]
          omega
        simp only [Fin.succAbove, this, ite_true, Fin.val_castSucc])

private lemma neg_one_pow_double (n : ℕ) : (-1 : PowerSeries ℚ) ^ (n + n) = 1 :=
  Even.neg_one_pow ⟨n, rfl⟩

private lemma stripMatrix_minor_subdiag_det (n : ℕ) :
    ((stripMatrix (n + 2)).submatrix
      (Fin.last (n + 1)).succAbove
      (⟨n, by omega⟩ : Fin (n + 2)).succAbove).det =
    -(stripMatrix n).det := by
  rw [Matrix.det_succ_column _ (Fin.last n),
    Finset.sum_eq_single_of_mem (Fin.last n) (Finset.mem_univ _) fun b _ hb => by
      rw [submatrix_last_col_zero n ⟨n, by omega⟩ rfl b hb, mul_zero, zero_mul]]
  simp only [Fin.val_last]
  rw [neg_one_pow_double,
    show ((stripMatrix (n + 2)).submatrix (Fin.last (n + 1)).succAbove
      (⟨n, by omega⟩ : Fin (n + 2)).succAbove) (Fin.last n) (Fin.last n) = -1 from
      by simp [Matrix.submatrix, stripMatrix, Fin.succAbove, Fin.last],
    double_submatrix_eq_stripMatrix n ⟨n, by omega⟩ rfl]
  ring

private lemma laplace_expansion_two_terms (n : ℕ) (j₀ : Fin (n + 2)) (hj₀ : j₀.val = n) :
    ∑ j : Fin (n + 2),
      (-1 : PowerSeries ℚ) ^ ((Fin.last (n + 1) : ℕ) + (j : ℕ)) *
        stripMatrix (n + 2) (Fin.last (n + 1)) j *
        ((stripMatrix (n + 2)).submatrix
          (Fin.last (n + 1)).succAbove j.succAbove).det =
      (-1 : PowerSeries ℚ) ^ ((n + 1) + n) *
        (-(PowerSeries.X : PowerSeries ℚ)) *
        ((stripMatrix (n + 2)).submatrix
          (Fin.last (n + 1)).succAbove
          j₀.succAbove).det +
      (-1 : PowerSeries ℚ) ^ ((n + 1) + (n + 1)) *
        1 *
        ((stripMatrix (n + 2)).submatrix
          (Fin.last (n + 1)).succAbove
          (Fin.last (n + 1)).succAbove).det := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hj₀_eq : (Fin.last n).castSucc = j₀ :=
    Fin.ext (by simp [Fin.val_last, Fin.val_castSucc, hj₀])
  rw [show stripMatrix (n + 2) (Fin.last (n + 1)) ((Fin.last n).castSucc) =
      -(PowerSeries.X : PowerSeries ℚ) from by
    rw [hj₀_eq]
    simp only [stripMatrix, Fin.val_last]
    split_ifs <;> simp_all [Fin.ext_iff]
    omega,
    show stripMatrix (n + 2) (Fin.last (n + 1)) (Fin.last (n + 1)) = 1 from by
      simp [stripMatrix],
    hj₀_eq]
  rw [Finset.sum_eq_zero fun j _ => by
    rw [show stripMatrix (n + 2) (Fin.last (n + 1)) j.castSucc.castSucc = 0 from by
      simp only [stripMatrix, Fin.val_last]
      split_ifs <;> simp_all [Fin.ext_iff, Fin.val_castSucc] <;> omega,
      mul_zero, zero_mul]]
  simp only [zero_add, Fin.val_last, hj₀]

private lemma stripMatrix_det_recurrence (n : ℕ) :
    (stripMatrix (n + 2)).det =
      (stripMatrix (n + 1)).det - (PowerSeries.X : PowerSeries ℚ) * (stripMatrix n).det := by
  rw [Matrix.det_succ_row (stripMatrix (n + 2)) (Fin.last (n + 1)),
    laplace_expansion_two_terms n ⟨n, by omega⟩ rfl,
    stripMatrix_minor_subdiag_det, stripMatrix_submatrix_last_last,
    show (n + 1) + n = (n + n) + 1 by omega, pow_succ, neg_one_pow_double,
    neg_one_pow_double (n + 1)]
  ring

lemma stripMatrix_det (m : ℕ) :
    (stripMatrix m).det = ↑(polyP ℚ m) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => simp [Matrix.det_fin_zero, polyP]
    | 1 => simp [stripMatrix, polyP, Matrix.det_unique]
    | n + 2 =>
      rw [stripMatrix_det_recurrence n, ih (n + 1) (by omega), ih n (by omega)]
      simp only [polyP, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_X]

/-! #### Helper lemmas for stripMatrix_inv_entry (minor det and adjugate) -/

private lemma md_stripMatrix_zero_of_col_ge_row_plus_two (n : ℕ)
    (i j : Fin (n + 1)) (h : i.val + 2 ≤ j.val) :
    stripMatrix (n + 1) i j = 0 := by
  simp only [stripMatrix]
  split_ifs <;> simp_all [Fin.ext_iff]
  omega

private lemma md_minor_entry_zero_left_vs_rest (n : ℕ) (a j : Fin (n + 1))
    (haj : a.val ≤ j.val) (x y : Fin n)
    (hx : x.val < a.val) (hy : a.val ≤ y.val) :
    (stripMatrix (n + 1)) (j.succAbove x) (a.succAbove y) = 0 := by
  apply md_stripMatrix_zero_of_col_ge_row_plus_two
  simp only [Fin.succAbove, Fin.lt_def]
  split_ifs <;> simp_all [Fin.val_castSucc, Fin.val_succ] <;> omega

private lemma md_minor_left_block_det (n : ℕ) (a j : Fin (n + 1))
    (haj : a.val ≤ j.val) :
    (((stripMatrix (n + 1)).submatrix j.succAbove a.succAbove).toSquareBlockProp
      (fun x => x.val < a.val)).det =
    (stripMatrix a.val).det := by
  let e : {x : Fin n // x.val < a.val} ≃ Fin a.val :=
    ⟨fun ⟨x, hx⟩ => ⟨x.val, hx⟩, fun k => ⟨⟨k.val, by omega⟩, k.prop⟩,
     fun ⟨x, hx⟩ => by simp, fun k => by simp⟩
  rw [show (((stripMatrix (n + 1)).submatrix j.succAbove a.succAbove).toSquareBlockProp
      (fun x => x.val < a.val)) =
    (stripMatrix a.val).submatrix e e from by
      funext u v
      simp only [Matrix.submatrix_apply, Matrix.toSquareBlockProp_def, Matrix.of_apply]
      apply stripMatrix_val_eq
      · have : (↑u : Fin n).castSucc < j := by
          simp [Fin.lt_def, Fin.val_castSucc]
          omega
        simp [Fin.succAbove_of_castSucc_lt _ _ this, Fin.val_castSucc, e]
      · have : (↑v : Fin n).castSucc < a := by
          simp [Fin.lt_def, Fin.val_castSucc]
          omega
        simp [Fin.succAbove_of_castSucc_lt _ _ this, Fin.val_castSucc, e],
    Matrix.det_submatrix_equiv_self]

private def md_middleBlockEquivFlat (n : ℕ) (a j : Fin (n + 1)) :
    {y : {x : Fin n // ¬(x.val < a.val)} // y.val.val < j.val} ≃
    {x : Fin n // a.val ≤ x.val ∧ x.val < j.val} where
  toFun := fun ⟨⟨x, hx⟩, hy⟩ => ⟨x, ⟨Nat.le_of_not_lt hx, hy⟩⟩
  invFun := fun ⟨x, ⟨hge, hlt⟩⟩ => ⟨⟨x, Nat.not_lt_of_le hge⟩, hlt⟩
  left_inv := fun ⟨⟨x, hx⟩, hy⟩ => by simp
  right_inv := fun ⟨x, ⟨hge, hlt⟩⟩ => by simp

private lemma md_middle_block_upper_entry_zero (n : ℕ) (a j : Fin (n + 1))
    (x y : {z : Fin n // a.val ≤ z.val ∧ z.val < j.val})
    (hxy : x.val.val < y.val.val) :
    stripMatrix (n + 1) (j.succAbove x.val) (a.succAbove y.val) = 0 := by
  apply md_stripMatrix_zero_of_col_ge_row_plus_two
  rw [Fin.succAbove_of_castSucc_lt _ _
        (by simp only [Fin.lt_def, Fin.val_castSucc]; exact x.prop.2),
      Fin.succAbove_of_le_castSucc _ _
        (by simp only [Fin.le_def, Fin.val_castSucc]; exact y.prop.1)]
  simp [Fin.val_castSucc, Fin.val_succ]
  omega

private lemma md_middle_block_B_lower_triangular (n : ℕ) (a j : Fin (n + 1)) :
    let M := (stripMatrix (n + 1)).submatrix j.succAbove a.succAbove
    let B := (M.toSquareBlockProp (fun x => ¬(x.val < a.val))).toSquareBlockProp
      (fun x => x.val.val < j.val)
    B.BlockTriangular (⇑OrderDual.toDual) := by
  intro M _ p q hlt
  change stripMatrix (n + 1) (j.succAbove p.val.val) (a.succAbove q.val.val) = 0
  exact md_middle_block_upper_entry_zero n a j
    (md_middleBlockEquivFlat n a j p) (md_middleBlockEquivFlat n a j q)
    (OrderDual.toDual_lt_toDual.mp hlt)

private lemma md_middle_block_diag_entry (n : ℕ) (a j : Fin (n + 1))
    (x : {z : Fin n // a.val ≤ z.val ∧ z.val < j.val}) :
    stripMatrix (n + 1) (j.succAbove x.val) (a.succAbove x.val) = -1 := by
  simp [stripMatrix,
    Fin.succAbove_of_castSucc_lt j x.val
      (by simp only [Fin.lt_def, Fin.val_castSucc]; exact x.prop.2),
    Fin.succAbove_of_le_castSucc a x.val
      (by simp only [Fin.le_def, Fin.val_castSucc]; exact x.prop.1),
    Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]

private lemma md_nested_subtype_card (n : ℕ) (a j : Fin (n + 1)) :
    Fintype.card {y : {x : Fin n // ¬(x.val < a.val)} // y.val.val < j.val} =
      j.val - a.val := by
  rw [Fintype.card_congr (md_middleBlockEquivFlat n a j)]
  have : Fintype.card {x : Fin n // a.val ≤ x.val ∧ x.val < j.val} =
      Fintype.card {k : ℕ // k ∈ Finset.Ico a.val j.val} :=
    Fintype.card_congr {
      toFun := fun ⟨x, hx⟩ => ⟨x.val, Finset.mem_Ico.mpr ⟨hx.1, hx.2⟩⟩
      invFun := fun ⟨k, hk⟩ => ⟨⟨k, by
          have := (Finset.mem_Ico.mp hk).2
          have := j.isLt
          omega⟩,
        (Finset.mem_Ico.mp hk).1, (Finset.mem_Ico.mp hk).2⟩
      left_inv := fun ⟨x, hx⟩ => by simp_all
      right_inv := fun ⟨k, hk⟩ => by simp_all }
  rw [this]
  simp [Nat.card_Ico]

private lemma md_minor_middle_block_det (n : ℕ) (a j : Fin (n + 1)) :
    let M := (stripMatrix (n + 1)).submatrix j.succAbove a.succAbove
    ((M.toSquareBlockProp (fun x => ¬(x.val < a.val))).toSquareBlockProp
      (fun x => x.val.val < j.val)).det =
    (-1 : PowerSeries ℚ) ^ (j.val - a.val) := by
  intro M
  set B := (M.toSquareBlockProp (fun x => ¬(x.val < a.val))).toSquareBlockProp
    (fun x => x.val.val < j.val)
  rw [Matrix.det_of_lowerTriangular B (md_middle_block_B_lower_triangular n a j)]
  simp_rw [show ∀ i, B i i = -1 from fun w =>
    md_middle_block_diag_entry n a j (md_middleBlockEquivFlat n a j w)]
  rw [Finset.prod_const, Finset.card_univ, md_nested_subtype_card n a j]

private noncomputable def md_nestedSubtypeEquiv (n : ℕ) (a j : Fin (n + 1)) (haj : a.val ≤ j.val) :
    {x : {z : Fin n // ¬(z.val < a.val)} // ¬(x.val.val < j.val)} ≃
    {x : Fin n // j.val ≤ x.val} where
  toFun x := ⟨x.val.val, Nat.le_of_not_lt x.prop⟩
  invFun x := ⟨⟨x.val, fun h => Nat.not_le.mpr (Nat.lt_of_lt_of_le h haj) x.prop⟩,
    fun h => Nat.not_le.mpr h x.prop⟩
  left_inv x := by simp
  right_inv x := by simp

private noncomputable def md_finSubtypeEquiv (n : ℕ) (j : Fin (n + 1)) :
    {x : Fin n // j.val ≤ x.val} ≃ Fin (n - j.val) where
  toFun x := ⟨x.val.val - j.val, by omega⟩
  invFun y := ⟨⟨y.val + j.val, by omega⟩, by simp⟩
  left_inv x := by
    ext
    simp
    omega
  right_inv y := by
    ext
    simp

private noncomputable def md_rightBlockEquiv (n : ℕ) (a j : Fin (n + 1)) (haj : a.val ≤ j.val) :
    {x : {z : Fin n // ¬(z.val < a.val)} // ¬(x.val.val < j.val)} ≃
    Fin (n - j.val) :=
  (md_nestedSubtypeEquiv n a j haj).trans (md_finSubtypeEquiv n j)

private lemma md_rightBlockEquiv_symm_val (n : ℕ) (a j : Fin (n + 1)) (haj : a.val ≤ j.val)
    (i : Fin (n - j.val)) :
    ((md_rightBlockEquiv n a j haj).symm i).val.val.val = i.val + j.val := by
  simp [md_rightBlockEquiv, md_nestedSubtypeEquiv, md_finSubtypeEquiv]

private lemma md_stripMatrix_val_shift (m₁ m₂ : ℕ) (r₁ : Fin m₁) (c₁ : Fin m₁)
    (r₂ : Fin m₂) (c₂ : Fin m₂) (d : ℕ)
    (hr : r₁.val = r₂.val + d) (hc : c₁.val = c₂.val + d) :
    stripMatrix m₁ r₁ c₁ = stripMatrix m₂ r₂ c₂ := by
  simp only [stripMatrix, Fin.ext_iff, hr, hc]
  split_ifs <;> first | rfl | omega

private lemma md_right_block_entry_eq (n : ℕ) (a j : Fin (n + 1)) (haj : a.val ≤ j.val)
    (i k : Fin (n - j.val)) :
    let M := (stripMatrix (n + 1)).submatrix j.succAbove a.succAbove
    let rightBlock := (M.toSquareBlockProp (fun x => ¬(x.val < a.val))).toSquareBlockProp
      (fun x => ¬(x.val.val < j.val))
    rightBlock ((md_rightBlockEquiv n a j haj).symm i) ((md_rightBlockEquiv n a j haj).symm k) =
    stripMatrix (n - j.val) i k := by
  simp only
  rw [Matrix.toSquareBlockProp_def, Matrix.toSquareBlockProp_def]
  simp only [Matrix.of_apply, Matrix.submatrix_apply]
  apply md_stripMatrix_val_shift (n + 1) (n - j.val) _ _ i k (j.val + 1)
  all_goals
    rw [Fin.succAbove_of_le_castSucc _ _ (by
      simp only [Fin.le_def, Fin.val_castSucc]
      rw [md_rightBlockEquiv_symm_val]
      omega)]
    simp [Fin.val_succ, md_rightBlockEquiv_symm_val]
    omega

private lemma md_minor_right_block_det (n : ℕ) (a j : Fin (n + 1))
    (haj : a.val ≤ j.val) :
    let M := (stripMatrix (n + 1)).submatrix j.succAbove a.succAbove
    ((M.toSquareBlockProp (fun x => ¬(x.val < a.val))).toSquareBlockProp
      (fun x => ¬(x.val.val < j.val))).det =
    (stripMatrix (n - j.val)).det := by
  intro M
  rw [(Matrix.det_submatrix_equiv_self (md_rightBlockEquiv n a j haj).symm _).symm]
  congr 1
  funext i k
  simp only [Matrix.submatrix_apply]
  exact md_right_block_entry_eq n a j haj i k

private lemma md_rest_block_zero_middle_vs_right (n : ℕ) (a j : Fin (n + 1))
    (i : {x : Fin n // ¬(x.val < a.val)})
    (j' : {x : Fin n // ¬(x.val < a.val)})
    (hi : i.val.val < j.val) (hj' : ¬(j'.val.val < j.val)) :
    let M := (stripMatrix (n + 1)).submatrix j.succAbove a.succAbove
    (M.toSquareBlockProp (fun x => ¬(x.val < a.val))) i j' = 0 := by
  change (stripMatrix (n + 1)) (j.succAbove i.val) (a.succAbove j'.val) = 0
  apply md_stripMatrix_zero_of_col_ge_row_plus_two
  have h₁ : (j.succAbove i.val).val = i.val.val := by
    rw [Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def, Fin.val_castSucc]; exact hi)]
    simp [Fin.val_castSucc]
  have h₂ : (a.succAbove j'.val).val = j'.val.val + 1 := by
    rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def, Fin.val_castSucc]; omega)]
    simp [Fin.val_succ]
  omega

private lemma stripMatrix_minor_det (n : ℕ) (a j : Fin (n + 1))
    (haj : a.val ≤ j.val) :
    ((stripMatrix (n + 1)).submatrix j.succAbove a.succAbove).det =
      (-1) ^ (j.val - a.val) *
        (↑(polyP ℚ a.val) : PowerSeries ℚ) *
        (↑(polyP ℚ (n - j.val)) : PowerSeries ℚ) := by
  set M := (stripMatrix (n + 1)).submatrix j.succAbove a.succAbove with hM_def
  have hsplit1 := Matrix.twoBlockTriangular_det' M (fun x => x.val < a.val) (by
    intro i hi j' hj'
    simp only [hM_def, Matrix.submatrix_apply]
    exact md_minor_entry_zero_left_vs_rest n a j haj i j' hi (by omega))
  rw [hsplit1]
  set Rest := M.toSquareBlockProp (fun x => ¬(x.val < a.val)) with _
  have hsplit2 := Matrix.twoBlockTriangular_det' Rest (fun x => x.val.val < j.val) (by
    intro i hi j' hj'
    exact md_rest_block_zero_middle_vs_right n a j i j' hi hj')
  rw [hsplit2, md_minor_left_block_det n a j haj, stripMatrix_det a.val,
    md_minor_middle_block_det n a j, md_minor_right_block_det n a j haj,
    stripMatrix_det (n - j.val)]
  ring

private lemma stripMatrix_adjugate_entry (m : ℕ) (hm : 2 ≤ m) (a j : Fin m)
    (haj : a.val ≤ j.val) :
    (stripMatrix m).adjugate a j =
      (↑(polyP ℚ a.val) : PowerSeries ℚ) *
      (↑(polyP ℚ (m - 1 - j.val)) : PowerSeries ℚ) := by
  obtain ⟨n, hn⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  subst hn
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, stripMatrix_minor_det n a j haj,
    show n + 1 - 1 - j.val = n - j.val by omega,
    ← mul_assoc, ← mul_assoc, ← pow_add,
    show (j.val + a.val) + (j.val - a.val) = j.val + j.val by omega, neg_one_pow_double]
  ring

private lemma matrix_inv_entry_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) (PowerSeries ℚ))
    (hc : PowerSeries.constantCoeff A.det ≠ 0) (i j : Fin n) :
    A⁻¹ i j = A.det⁻¹ * A.adjugate i j := by
  have h_isUnit : IsUnit A.det :=
    ⟨⟨_, _, PowerSeries.mul_inv_cancel _ hc, PowerSeries.inv_mul_cancel _ hc⟩, rfl⟩
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
  congr 1
  rw [← h_isUnit.unit_spec, Ring.inverse_unit,
    PowerSeries.eq_inv_iff_mul_eq_one (by rwa [h_isUnit.unit_spec]), mul_comm,
    h_isUnit.unit_spec]
  exact_mod_cast h_isUnit.unit.mul_inv

lemma stripMatrix_inv_entry (m : ℕ) (hm : 2 ≤ m) (a j : Fin m)
    (haj : a.val ≤ j.val) :
    (stripMatrix m)⁻¹ a j =
      (↑(polyP ℚ a.val * polyP ℚ (m - 1 - j.val)) : PowerSeries ℚ) *
        ((↑(polyP ℚ m) : PowerSeries ℚ))⁻¹ := by
  rw [matrix_inv_entry_eq _ (by
      rw [stripMatrix_det]
      exact polyP_coe_constantCoeff_ne_zero ℚ m),
    stripMatrix_det, stripMatrix_adjugate_entry m hm a j haj, Polynomial.coe_mul]
  ring

lemma D_coeff_eq_matrix_inv_coeff (m a b u : ℕ) (hm : 2 ≤ m)
    (ha : a ≤ m - 1) (hb : b ≤ m - 1) (hab : a + b ≤ m - 1) :
    dCoeff ℚ m a b u =
      (PowerSeries.coeff u) ((stripMatrix m)⁻¹
        ⟨a, by omega⟩ ⟨m - 1 - b, by omega⟩) := by
  rw [stripMatrix_inv_entry m hm ⟨a, by omega⟩ ⟨m - 1 - b, by omega⟩ (by
    simp
    omega)]
  simp only [dCoeff, Nat.sub_sub_self hb]

/-! #### Helper lemmas for stripMatrix_inv_coeff_nonneg (lattice path) -/

/-- The number of length-`u` lattice paths in the Dyck-path model from row `i` that
reach `target`, used to express the nonnegative coefficients of the matrix inverse. -/
noncomputable def pathCount (m : ℕ) (target : Fin m) (i : Fin m) (u : ℕ) : ℕ :=
  match u with
  | 0 => if i.val ≤ target.val then 1 else 0
  | u + 1 =>
    (if h : i.val + 1 < m
     then pathCount m target ⟨i.val + 1, h⟩ (u + 1)
     else 0) +
    (if h : 0 < i.val
     then pathCount m target ⟨i.val - 1, by omega⟩ u
     else 0)
  termination_by (u, m - i.val)

/-- The generating power series whose `u`-th coefficient is `pathCount m target i u`. -/
noncomputable def pathCountVec (m : ℕ) (target : Fin m) (i : Fin m) : PowerSeries ℚ :=
  PowerSeries.mk (fun u => (pathCount m target i u : ℚ))

private lemma coeff_zero_case (m : ℕ) (target : Fin m) (i : Fin m) :
    (pathCount m target i 0 : ℚ) -
    (if h : i.val + 1 < m
     then (pathCount m target ⟨i.val + 1, h⟩ 0 : ℚ)
     else 0) =
    (if i = target then 1 else 0) := by
  simp only [pathCount]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

private lemma coeff_succ_case (m : ℕ) (target : Fin m) (i : Fin m) (u' : ℕ) :
    (pathCount m target i (u' + 1) : ℚ) -
    (if h : i.val + 1 < m
     then (pathCount m target ⟨i.val + 1, h⟩ (u' + 1) : ℚ)
     else 0) -
    (if h : 0 < i.val
     then (pathCount m target ⟨i.val - 1, by omega⟩ u' : ℚ)
     else 0) = 0 := by
  rw [pathCount]
  push_cast
  split_ifs <;> ring

private lemma rhs_coeff (m : ℕ) (target i : Fin m) (u : ℕ) :
    (PowerSeries.coeff u) ((Pi.single target (1 : PowerSeries ℚ) : Fin m → PowerSeries ℚ) i) =
    if i = target ∧ u = 0 then 1 else 0 := by
  simp only [Pi.single_apply]
  split_ifs with h1 h2 <;> simp_all [PowerSeries.coeff_one]

private lemma sum_stripMatrix_split (m : ℕ) (v : Fin m → PowerSeries ℚ) (i : Fin m) :
    ∑ j : Fin m, stripMatrix m i j * v j =
      ∑ j : Fin m, (if i = j then v j else 0) +
      ∑ j : Fin m, (if j.val = i.val + 1 then -(v j) else 0) +
      ∑ j : Fin m, (if i.val = j.val + 1 then -(PowerSeries.X * v j) else 0) := by
  simp only [Finset.sum_add_distrib.symm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [stripMatrix]
  by_cases h1 : i = j
  · simp [h1]
  · by_cases h2 : j.val = i.val + 1
    · simp [h1, h2]
      omega
    · by_cases h3 : i.val = j.val + 1
      · simp [h1, h3]
        simp_all
      · simp [h1, h2, h3]

private lemma sum_superdiag (m : ℕ) (v : Fin m → PowerSeries ℚ) (i : Fin m) :
    ∑ j : Fin m, (if j.val = i.val + 1 then -(v j) else 0) =
      if h : i.val + 1 < m then -(v ⟨i.val + 1, h⟩) else 0 := by
  by_cases hm : i.val + 1 < m
  · simp only [hm, dite_true]
    have : ∀ j : Fin m, (j.val = i.val + 1) = (j = ⟨i.val + 1, hm⟩) := by
      intro j
      simp [Fin.ext_iff]
    simp_rw [this]
    simp [Finset.sum_ite_eq', Finset.mem_univ]
  · simp only [hm, dite_false]
    exact Finset.sum_eq_zero fun j _ => if_neg (by omega)

private lemma sum_subdiag (m : ℕ) (v : Fin m → PowerSeries ℚ) (i : Fin m)
    (pf : 0 < i.val → i.val - 1 < m) :
    ∑ j : Fin m, (if i.val = j.val + 1 then -(PowerSeries.X * v j) else 0) =
      if h : 0 < i.val then -(PowerSeries.X * v ⟨i.val - 1, pf h⟩) else 0 := by
  by_cases h : 0 < i.val
  · simp only [h, dite_true]
    have : ∀ j : Fin m, (i.val = j.val + 1) = (j = ⟨i.val - 1, pf h⟩) := by
      intro j
      simp [Fin.ext_iff]
      omega
    simp_rw [this]
    exact Fintype.sum_ite_eq' ⟨i.val - 1, pf h⟩ (fun j => -(PowerSeries.X * v j))
  · simp only [h, dite_false]
    exact Fintype.sum_eq_zero _ fun j => if_neg (by omega)

private lemma mulVec_three_terms (m : ℕ) (v : Fin m → PowerSeries ℚ) (i : Fin m) :
    (stripMatrix m).mulVec v i =
      v i +
      (if h : i.val + 1 < m then -(v ⟨i.val + 1, h⟩) else 0) +
      (if h : 0 < i.val then -(PowerSeries.X * v ⟨i.val - 1, by omega⟩) else 0) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_stripMatrix_split, sum_superdiag,
    show ∑ j : Fin m, (if i = j then v j else 0) = v i from by
      rw [Finset.sum_ite_eq]
      simp [Finset.mem_univ],
    sum_subdiag m v i (by omega)]

private lemma coeff_three_terms_eq (m : ℕ) (target i : Fin m) (u : ℕ) :
    (PowerSeries.coeff u)
      (pathCountVec m target i +
       (if h : i.val + 1 < m then -(pathCountVec m target ⟨i.val + 1, h⟩) else 0) +
       (if h : 0 < i.val
        then -(PowerSeries.X * pathCountVec m target ⟨i.val - 1, by omega⟩)
        else 0)) =
      (pathCount m target i u : ℚ) -
      (if h : i.val + 1 < m
       then (pathCount m target ⟨i.val + 1, h⟩ u : ℚ)
       else 0) -
      (if h : 0 < i.val
       then if u = 0 then 0
            else (pathCount m target ⟨i.val - 1, by omega⟩ (u - 1) : ℚ)
       else 0) := by
  rw [map_add, map_add]
  rw [show (PowerSeries.coeff u) (pathCountVec m target i) = (pathCount m target i u : ℚ)
    from PowerSeries.coeff_mk _ _]
  conv_lhs => rw [show (PowerSeries.coeff u)
    (if h : i.val + 1 < m then -(pathCountVec m target ⟨i.val + 1, h⟩) else 0) =
    -(if h : i.val + 1 < m then (pathCount m target ⟨i.val + 1, h⟩ u : ℚ) else 0) from by
      split <;> simp [pathCountVec, PowerSeries.coeff_mk]]
  conv_lhs => rw [show (PowerSeries.coeff u)
    (if h : 0 < i.val
     then -(PowerSeries.X * pathCountVec m target ⟨i.val - 1, by omega⟩) else 0) =
    -(if h : 0 < i.val
      then if u = 0 then 0
           else (pathCount m target ⟨i.val - 1, by omega⟩ (u - 1) : ℚ) else 0) from by
      by_cases hi : 0 < i.val
      · simp only [hi, dite_true]
        cases u with
        | zero => simp
        | succ u' =>
          simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, map_neg,
            PowerSeries.coeff_succ_X_mul, pathCountVec, PowerSeries.coeff_mk]
      · simp only [hi, dite_false, neg_zero, map_zero]]
  ring

private lemma stripMatrix_mulVec_pathCountVec (m : ℕ) (target : Fin m) :
    (stripMatrix m).mulVec (pathCountVec m target) = Pi.single target 1 := by
  funext i
  apply PowerSeries.ext
  intro u
  rw [mulVec_three_terms, coeff_three_terms_eq, rhs_coeff]
  cases u with
  | zero =>
    simp only [and_true]
    rw [coeff_zero_case]
    split_ifs <;> simp_all
  | succ u' =>
    simp only [Nat.succ_ne_zero, and_false, ite_false, Nat.add_sub_cancel]
    rw [coeff_succ_case]

private lemma pathCountVec_eq_inv_entry (m : ℕ) (target : Fin m) (i : Fin m) :
    pathCountVec m target i = (stripMatrix m)⁻¹ i target := by
  have hne : PowerSeries.constantCoeff (R := ℚ) (stripMatrix m).det ≠ 0 := by
    rw [stripMatrix_det]
    exact polyP_coe_constantCoeff_ne_zero ℚ m
  have h := congr_fun (show (stripMatrix m)⁻¹.mulVec (Pi.single target 1) =
      pathCountVec m target from by
    rw [← stripMatrix_mulVec_pathCountVec m target, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ⟨⟨_, _, PowerSeries.mul_inv_cancel _ hne,
        PowerSeries.inv_mul_cancel _ hne⟩, rfl⟩,
      Matrix.one_mulVec]).symm i
  rwa [Matrix.mulVec_single_one] at h

lemma stripMatrix_inv_coeff_nonneg (m : ℕ) (_hm : 2 ≤ m)
    (a j : Fin m) (_haj : a.val ≤ j.val) (u : ℕ) :
    (0 : ℚ) ≤ (PowerSeries.coeff u) ((stripMatrix m)⁻¹ a j) := by
  rw [← pathCountVec_eq_inv_entry m j a]
  simp only [pathCountVec, PowerSeries.coeff_mk]
  exact Nat.cast_nonneg _

/-! ### Main theorem -/

theorem thm_manifest_D_nonneg (m a b u : ℕ) (hm : 2 ≤ m)
    (ha : a ≤ m - 1) (hb : b ≤ m - 1) (hab : a + b ≤ m - 1) :
    (0 : ℚ) ≤ dCoeff ℚ m a b u := by
  rw [D_coeff_eq_matrix_inv_coeff m a b u hm ha hb hab]
  exact stripMatrix_inv_coeff_nonneg m hm ⟨a, by omega⟩ ⟨m - 1 - b, by omega⟩
    (by simp; omega) u

lemma D_coeff_eq_nat_cast (m a b u : ℕ) (hm : 2 ≤ m)
    (ha : a ≤ m - 1) (hb : b ≤ m - 1) (hab : a + b ≤ m - 1) :
    ∃ (w : ℕ), dCoeff ℚ m a b u = ↑w := by
  obtain ⟨z, hz⟩ := D_coeff_is_int m a b u
  exact ⟨z.toNat, by
    rw [hz]
    exact_mod_cast (Int.toNat_of_nonneg (by
      exact_mod_cast hz ▸ thm_manifest_D_nonneg m a b u hm ha hb hab)).symm⟩

/-! ## Theorem 3: Part (iii) - Nonnegativity of all coefficients -/

theorem thm_manifest_coeff_nonneg (m μ : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) (hm : 2 ≤ m) (h_parts : ∀ i ∈ ξ.parts, i ≤ m)
    (hk_nonneg : countMaxParts m ξ ≤ μ / m + 1)
    (k : ℕ) (hk_eq : k = reducedK m μ ξ)
    (pairs : Fin k → ℕ × ℕ)
    (h_bound : ∀ ν, (pairs ν).1 ≤ m - 1 ∧ (pairs ν).2 ≤ m - 1 ∧
                     (pairs ν).1 + (pairs ν).2 ≤ m - 1)
    (h_factor : alphaProd ℚ m μ ξ =
      ∏ ν : Fin k, (polyP ℚ (pairs ν).1 * polyP ℚ (pairs ν).2))
    (r : ℕ) :
    (0 : ℚ) ≤ genFunCoeff ℚ m μ r ξ := by
  rw [thm_manifest_coeff_formula m μ ξ hm h_parts hk_nonneg k hk_eq pairs h_bound h_factor r]
  exact Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun ν _ =>
    thm_manifest_D_nonneg m _ _ _ hm (h_bound ν).1 (h_bound ν).2.1 (h_bound ν).2.2

end Biswal.Theorem23

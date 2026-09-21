/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.CapacityOrder
import LeanPool.BeyondBethe.BeyondBethe.Entropy
import Mathlib.Tactic

/-! # Capacity -/

open scoped BigOperators

namespace BeyondBethe

/-- A monomial with a natural exponent vector. -/
noncomputable def natMonomial
    {σ : Type*} [Fintype σ] (z : σ → ℝ) (E : σ → ℕ) : ℝ :=
  ∏ j, (z j) ^ (E j)

/-- A finite positive-coefficient polynomial presented by its list of
monomials. -/
noncomputable def finitePolynomial
    {κ σ : Type*} [Fintype κ] [Fintype σ]
    (c : κ → ℝ) (E : κ → σ → ℕ) (z : σ → ℝ) : ℝ :=
  ∑ e, c e * natMonomial z (E e)

/-- Barycenter of the exponent vectors under a distribution `θ`. -/
noncomputable def exponentMoment
    {κ σ : Type*} [Fintype κ]
    (θ : κ → ℝ) (E : κ → σ → ℕ) (j : σ) : ℝ :=
  ∑ e, θ e * (E e j : ℝ)

/-- Entropic objective on a positive coefficient representation. -/
noncomputable def entropyCapacityCertificate
    {κ : Type*} [Fintype κ] (θ c : κ → ℝ) : ℝ :=
  ∑ e, θ e * Real.log (c e / θ e)

theorem log_natMonomial
    {σ : Type*} [Fintype σ]
    {z : σ → ℝ} (hz : ∀ j, 0 < z j) (E : σ → ℕ) :
    Real.log (natMonomial z E) =
      ∑ j, (E j : ℝ) * Real.log (z j) := by
  rw [natMonomial, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro j _
    simpa using Real.log_pow (z j) (E j)
  · intro j _
    exact (pow_pos (hz j) _).ne'

theorem log_realMonomial
    {σ : Type*} [Fintype σ]
    {z α : σ → ℝ} (hz : ∀ j, 0 < z j) :
    Real.log (realMonomial z α) =
      ∑ j, α j * Real.log (z j) := by
  rw [realMonomial, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro j _
    exact Real.log_rpow (hz j) (α j)
  · intro j _
    exact (Real.rpow_pos_of_pos (hz j) _).ne'

theorem averaged_log_natMonomial
    {κ σ : Type*} [Fintype κ] [Fintype σ]
    (θ : κ → ℝ) (E : κ → σ → ℕ)
    {z : σ → ℝ} (hz : ∀ j, 0 < z j) :
    ∑ e, θ e * Real.log (natMonomial z (E e)) =
      ∑ j, exponentMoment θ E j * Real.log (z j) := by
  simp_rw [log_natMonomial hz]
  calc
    ∑ e, θ e * (∑ j, (E e j : ℝ) * Real.log (z j)) =
        ∑ e, ∑ j, (θ e * (E e j : ℝ)) * Real.log (z j) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ∑ j, ∑ e, (θ e * (E e j : ℝ)) * Real.log (z j) :=
      Finset.sum_comm
    _ = ∑ j, exponentMoment θ E j * Real.log (z j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [exponentMoment, Finset.sum_mul]

/-- The certificate-producing direction of paper Lemma 4, for a strictly
positive feasible distribution.  Unlike the reverse equality, this direction
uses only finite log-sum and has no convex-duality dependency. -/
theorem entropyCapacityCertificate_le_log_ratio
    {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]
    {θ c : κ → ℝ} {E : κ → σ → ℕ} {α z : σ → ℝ}
    (hθ : ∀ e, 0 < θ e) (hθsum : ∑ e, θ e = 1)
    (hc : ∀ e, 0 < c e) (hz : ∀ j, 0 < z j)
    (hmoment : ∀ j, exponentMoment θ E j = α j) :
    entropyCapacityCertificate θ c ≤
      Real.log (finitePolynomial c E z / realMonomial z α) := by
  let w : κ → ℝ := fun e ↦ c e * natMonomial z (E e)
  have hnatpos : ∀ e, 0 < natMonomial z (E e) := by
    intro e
    rw [natMonomial]
    exact Finset.prod_pos fun j _ ↦ pow_pos (hz j) _
  have hw : ∀ e, 0 < w e := fun e ↦ mul_pos (hc e) (hnatpos e)
  have hlogsum := log_sum_inequality hθ hθsum hw
  have hpoly : ∑ e, w e = finitePolynomial c E z := by
    rfl
  rw [hpoly] at hlogsum
  have hsplit : ∀ e,
      Real.log (w e / θ e) =
        Real.log (c e / θ e) + Real.log (natMonomial z (E e)) := by
    intro e
    dsimp [w]
    rw [Real.log_div (mul_ne_zero (hc e).ne' (hnatpos e).ne') (hθ e).ne',
      Real.log_mul (hc e).ne' (hnatpos e).ne',
      Real.log_div (hc e).ne' (hθ e).ne']
    ring
  simp_rw [hsplit, mul_add, Finset.sum_add_distrib] at hlogsum
  rw [averaged_log_natMonomial θ E hz] at hlogsum
  have hmomlog :
      ∑ j, exponentMoment θ E j * Real.log (z j) =
        Real.log (realMonomial z α) := by
    rw [log_realMonomial hz]
    apply Finset.sum_congr rfl
    intro j _
    rw [hmoment j]
  rw [hmomlog] at hlogsum
  have hpolypos : 0 < finitePolynomial c E z := by
    rw [← hpoly]
    exact Finset.sum_pos (fun e _ ↦ hw e) (by
      by_contra hempty
      have hzero : ∑ e, θ e = 0 := by
        rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
        simp
      linarith)
  have hmonopos : 0 < realMonomial z α := by
    rw [realMonomial]
    exact Finset.prod_pos fun j _ ↦ Real.rpow_pos_of_pos (hz j) _
  rw [Real.log_div hpolypos.ne' hmonopos.ne']
  rw [le_sub_iff_add_le]
  simpa [entropyCapacityCertificate, add_comm] using hlogsum

/-- Certificate-producing capacity inequality with zero witness weights
allowed.  This is the boundary form used by the clean-pair witness. -/
theorem entropyCapacityCertificate_le_log_ratio_nonnegative
    {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]
    {θ c : κ → ℝ} {E : κ → σ → ℕ} {α z : σ → ℝ}
    (hθ : ∀ e, 0 ≤ θ e) (hθsum : ∑ e, θ e = 1)
    (hc : ∀ e, 0 < c e) (hz : ∀ j, 0 < z j)
    (hmoment : ∀ j, exponentMoment θ E j = α j) :
    entropyCapacityCertificate θ c ≤
      Real.log (finitePolynomial c E z / realMonomial z α) := by
  let w : κ → ℝ := fun e ↦ c e * natMonomial z (E e)
  have hnatpos : ∀ e, 0 < natMonomial z (E e) := by
    intro e
    rw [natMonomial]
    exact Finset.prod_pos fun j _ ↦ pow_pos (hz j) _
  have hw : ∀ e, 0 < w e := fun e ↦ mul_pos (hc e) (hnatpos e)
  have hlogsum := log_sum_inequality_nonnegative hθ hθsum hw
  have hpoly : ∑ e, w e = finitePolynomial c E z := by
    rfl
  rw [hpoly] at hlogsum
  have hsplit : ∀ e,
      θ e * Real.log (w e / θ e) =
        θ e * Real.log (c e / θ e) +
          θ e * Real.log (natMonomial z (E e)) := by
    intro e
    by_cases hzero : θ e = 0
    · simp [hzero]
    · dsimp [w]
      rw [Real.log_div (mul_ne_zero (hc e).ne' (hnatpos e).ne') hzero,
        Real.log_mul (hc e).ne' (hnatpos e).ne',
        Real.log_div (hc e).ne' hzero]
      ring
  simp_rw [hsplit, Finset.sum_add_distrib] at hlogsum
  rw [averaged_log_natMonomial θ E hz] at hlogsum
  have hmomlog :
      ∑ j, exponentMoment θ E j * Real.log (z j) =
        Real.log (realMonomial z α) := by
    rw [log_realMonomial hz]
    apply Finset.sum_congr rfl
    intro j _
    rw [hmoment j]
  rw [hmomlog] at hlogsum
  have hpolypos : 0 < finitePolynomial c E z := by
    rw [← hpoly]
    exact Finset.sum_pos (fun e _ ↦ hw e) (by
      by_contra hempty
      have hzero : ∑ e, θ e = 0 := by
        rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
        simp
      linarith)
  have hmonopos : 0 < realMonomial z α := realMonomial_pos hz α
  rw [Real.log_div hpolypos.ne' hmonopos.ne']
  rw [le_sub_iff_add_le]
  simpa [entropyCapacityCertificate, add_comm] using hlogsum

/-- Capacity of a polynomial given by a finite coefficient/exponent list. -/
noncomputable def finitePolynomialCapacity
    {κ σ : Type*} [Fintype κ] [Fintype σ]
    (c : κ → ℝ) (E : κ → σ → ℕ) (α : σ → ℝ) : ℝ :=
  sInf {v : ℝ | ∃ z : σ → ℝ, (∀ j, 0 < z j) ∧
    v = finitePolynomial c E z / realMonomial z α}

theorem exp_entropyCapacityCertificate_le_finitePolynomialCapacity
    {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]
    {θ c : κ → ℝ} {E : κ → σ → ℕ} {α : σ → ℝ}
    (hθ : ∀ e, 0 ≤ θ e) (hθsum : ∑ e, θ e = 1)
    (hc : ∀ e, 0 < c e)
    (hmoment : ∀ j, exponentMoment θ E j = α j) :
    Real.exp (entropyCapacityCertificate θ c) ≤
      finitePolynomialCapacity c E α := by
  apply le_csInf
  · let one : σ → ℝ := fun _ ↦ 1
    exact ⟨finitePolynomial c E one / realMonomial one α,
      ⟨one, fun _ ↦ by norm_num, rfl⟩⟩
  · intro value hvalue
    obtain ⟨z, hz, rfl⟩ := hvalue
    have hlog := entropyCapacityCertificate_le_log_ratio_nonnegative
      hθ hθsum hc hz hmoment
    have hpolypos : 0 < finitePolynomial c E z := by
      rw [finitePolynomial]
      exact Finset.sum_pos (fun e _ ↦ mul_pos (hc e) (by
        rw [natMonomial]
        exact Finset.prod_pos fun j _ ↦ pow_pos (hz j) _))
        (by
          by_contra hempty
          have hzero : ∑ e, θ e = 0 := by
            rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
            simp
          linarith)
    have hratio : 0 < finitePolynomial c E z / realMonomial z α :=
      div_pos hpolypos (realMonomial_pos hz α)
    have hexp := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log hratio] at hexp
    exact hexp

theorem entropyCapacityCertificate_le_log_finitePolynomialCapacity
    {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]
    {θ c : κ → ℝ} {E : κ → σ → ℕ} {α : σ → ℝ}
    (hθ : ∀ e, 0 ≤ θ e) (hθsum : ∑ e, θ e = 1)
    (hc : ∀ e, 0 < c e)
    (hmoment : ∀ j, exponentMoment θ E j = α j) :
    entropyCapacityCertificate θ c ≤
      Real.log (finitePolynomialCapacity c E α) := by
  have hexp := exp_entropyCapacityCertificate_le_finitePolynomialCapacity
    hθ hθsum hc hmoment
  have hcap : 0 < finitePolynomialCapacity c E α :=
    (Real.exp_pos _).trans_le hexp
  have hlog := Real.log_le_log (Real.exp_pos _) hexp
  rw [Real.log_exp] at hlog
  exact hlog

noncomputable def supportCoefficient
    {σ : Type*} (p : MvPolynomial σ ℝ) (d : p.support) : ℝ :=
  p.coeff d

def supportExponent
    {σ : Type*} (p : MvPolynomial σ ℝ) (d : p.support) (j : σ) : ℕ :=
  d.1 j

theorem finitePolynomial_support_eq_eval
    {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) (z : σ → ℝ) :
    finitePolynomial (supportCoefficient p) (supportExponent p) z =
      p.eval z := by
  classical
  rw [finitePolynomial, MvPolynomial.eval_eq]
  calc
    (∑ d : p.support,
        supportCoefficient p d * natMonomial z (supportExponent p d)) =
        ∑ d ∈ p.support, p.coeff d * ∏ j, z j ^ d j := by
      simpa [supportCoefficient, supportExponent, natMonomial] using
        Finset.sum_coe_sort p.support
          (fun d ↦ p.coeff d * ∏ j, z j ^ d j)
    _ = ∑ d ∈ p.support,
        p.coeff d * ∏ i ∈ d.support, z i ^ d i := by
      apply Finset.sum_congr rfl
      intro d _
      congr 1
      change (∏ j, z j ^ d j) = d.prod (fun i e ↦ z i ^ e)
      exact (Finsupp.prod_fintype d (fun i e ↦ z i ^ e)
        (fun i ↦ pow_zero (z i))).symm

theorem finitePolynomialCapacity_support_eq_polynomialCapacity
    {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) (α : σ → ℝ) :
    finitePolynomialCapacity (supportCoefficient p) (supportExponent p) α =
      polynomialCapacity α p := by
  rw [finitePolynomialCapacity, polynomialCapacity]
  congr 1
  ext value
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, by rw [finitePolynomial_support_eq_eval]⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, by rw [finitePolynomial_support_eq_eval]⟩

/-- One-sided entropy certificate for an `MvPolynomial`, including boundary
witnesses with zero weights.  Unlike the reverse entropy-duality equality,
this theorem is proved directly from log-sum. -/
theorem supportEntropyCertificate_le_log_polynomialCapacity
    {σ : Type*} [Fintype σ]
    {p : MvPolynomial σ ℝ} {θ : p.support → ℝ} {α : σ → ℝ}
    (hθ : ∀ d, 0 ≤ θ d) (hθsum : ∑ d, θ d = 1)
    (hcoeff : ∀ d : p.support, 0 < p.coeff d)
    (hmoment : ∀ j,
      exponentMoment θ (supportExponent p) j = α j) :
    entropyCapacityCertificate θ (supportCoefficient p) ≤
      Real.log (polynomialCapacity α p) := by
  classical
  rw [← finitePolynomialCapacity_support_eq_polynomialCapacity]
  exact entropyCapacityCertificate_le_log_finitePolynomialCapacity
    hθ hθsum hcoeff hmoment

theorem finitePolynomial_nonneg
    {κ σ : Type*} [Fintype κ] [Fintype σ]
    {c : κ → ℝ} {E : κ → σ → ℕ} {z : σ → ℝ}
    (hc : ∀ e, 0 ≤ c e) (hz : ∀ j, 0 ≤ z j) :
    0 ≤ finitePolynomial c E z := by
  rw [finitePolynomial]
  exact Finset.sum_nonneg fun e _ ↦ mul_nonneg (hc e)
    (Finset.prod_nonneg fun j _ ↦ pow_nonneg (hz j) _)

/-- A nonnegative finite subpolynomial has no larger capacity than the full
polynomial.  This lets the sparse clean-pair witness ignore all unused
monomials. -/
theorem finitePolynomialCapacity_le_polynomialCapacity_of_eval_le
    {κ σ : Type*} [Fintype κ] [Fintype σ]
    {c : κ → ℝ} {E : κ → σ → ℕ} {α : σ → ℝ}
    {p : MvPolynomial σ ℝ}
    (hc : ∀ e, 0 ≤ c e)
    (heval : ∀ z : σ → ℝ, (∀ j, 0 ≤ z j) →
      finitePolynomial c E z ≤ p.eval z) :
    finitePolynomialCapacity c E α ≤ polynomialCapacity α p := by
  apply le_csInf
  · let one : σ → ℝ := fun _ ↦ 1
    exact ⟨p.eval one / realMonomial one α,
      ⟨one, fun _ ↦ by norm_num, rfl⟩⟩
  · intro value hvalue
    obtain ⟨z, hz, rfl⟩ := hvalue
    have hmono : 0 < realMonomial z α := realMonomial_pos hz α
    have hfinUpper : finitePolynomialCapacity c E α ≤
        finitePolynomial c E z / realMonomial z α := by
      apply csInf_le
      · exact ⟨0, fun value hvalue ↦ by
          obtain ⟨w, hw, rfl⟩ := hvalue
          exact div_nonneg
            (finitePolynomial_nonneg hc (fun j ↦ (hw j).le))
            (realMonomial_pos hw α).le⟩
      · exact ⟨z, hz, rfl⟩
    exact hfinUpper.trans
      (div_le_div_of_nonneg_right (heval z (fun j ↦ (hz j).le)) hmono.le)

end BeyondBethe

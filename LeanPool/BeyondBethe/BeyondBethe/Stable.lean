/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! # Stable -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

open MvPolynomial

/-- Real stability: the polynomial has no zero when every variable lies in
the open upper half-plane. -/
def IsRealStable
    {σ : Type*} (p : MvPolynomial σ ℝ) : Prop :=
  ∀ z : σ → ℂ, (∀ i, 0 < (z i).im) →
    p.eval₂ (algebraMap ℝ ℂ) z ≠ 0

/-- The source literature includes the zero polynomial among the stable
polynomials.  Keeping the nonzero notion above is convenient for evaluation
arguments, while this wrapper records the source convention whenever a
stability-preserving operator can annihilate its input. -/
def IsRealStableOrZero
    {σ : Type*} (p : MvPolynomial σ ℝ) : Prop :=
  p = 0 ∨ IsRealStable p

/-- Requires every real coefficient of the multivariate polynomial to be nonnegative. -/
def HasNonnegativeCoefficients
    {σ : Type*} (p : MvPolynomial σ ℝ) : Prop :=
  ∀ d, 0 ≤ p.coeff d

/-- Requires the real multivariate polynomial to have degree at most one in each variable. -/
def IsMultiaffine
    {σ : Type*} (p : MvPolynomial σ ℝ) : Prop :=
  ∀ i, p.degreeOf i ≤ 1

theorem IsRealStable.rename
    {σ τ : Type*} {p : MvPolynomial σ ℝ}
    (hp : IsRealStable p) (f : σ → τ) :
    IsRealStable (MvPolynomial.rename f p) := by
  intro z hz
  rw [MvPolynomial.eval₂_rename]
  exact hp (z ∘ f) (fun i ↦ hz (f i))

theorem IsRealStable.mul
    {σ : Type*} {p q : MvPolynomial σ ℝ}
    (hp : IsRealStable p) (hq : IsRealStable q) :
    IsRealStable (p * q) := by
  intro z hz
  simp only [eval₂_mul]
  exact mul_ne_zero (hp z hz) (hq z hz)

theorem IsRealStable.isRealStableOrZero
    {σ : Type*} {p : MvPolynomial σ ℝ} (hp : IsRealStable p) :
    IsRealStableOrZero p :=
  Or.inr hp

theorem IsRealStableOrZero.zero
    {σ : Type*} : IsRealStableOrZero (0 : MvPolynomial σ ℝ) :=
  Or.inl rfl

theorem IsRealStableOrZero.mul
    {σ : Type*} {p q : MvPolynomial σ ℝ}
    (hp : IsRealStableOrZero p) (hq : IsRealStableOrZero q) :
    IsRealStableOrZero (p * q) := by
  rcases hp with rfl | hp
  · simp [IsRealStableOrZero]
  rcases hq with rfl | hq
  · simp [IsRealStableOrZero]
  exact (hp.mul hq).isRealStableOrZero

/-- `z^α` for a real exponent vector. -/
noncomputable def realMonomial
    {σ : Type*} [Fintype σ] (z α : σ → ℝ) : ℝ :=
  ∏ i, (z i) ^ (α i)

/-- Capacity from paper (4). -/
noncomputable def polynomialCapacity
    {σ : Type*} [Fintype σ]
    (α : σ → ℝ) (p : MvPolynomial σ ℝ) : ℝ :=
  sInf {v : ℝ | ∃ z : σ → ℝ,
    (∀ i, 0 < z i) ∧
      v = p.eval z / realMonomial z α}

/-- Same-squarefree-monomial coefficient pairing used in paper Theorem 3. -/
noncomputable def coefficientInnerProduct
    {σ : Type*} (p q : MvPolynomial σ ℝ) : ℝ := by
  classical
  exact ∑ d ∈ p.support.filter (· ∈ q.support), p.coeff d * q.coeff d

/-- Boundary product in the multiaffine coefficient inequality. -/
noncomputable def stableBoundaryFactor
    {σ : Type*} [Fintype σ] (α : σ → ℝ) : ℝ :=
  ∏ i, (α i) ^ (α i) * (1 - α i) ^ (1 - α i)

/-- Exact interface to the multiaffine coefficient theorem of
Anari--Oveis Gharan.  Every hypothesis used in the paper is visible here. -/
def AnariOveisGharanStableCoefficient : Prop :=
  ∀ {σ : Type*} [Fintype σ]
    (p q : MvPolynomial σ ℝ) (d : ℕ) (α : σ → ℝ),
    HasNonnegativeCoefficients p →
    HasNonnegativeCoefficients q →
    IsMultiaffine p → IsMultiaffine q →
    IsRealStable p → IsRealStable q →
    p.IsHomogeneous d → q.IsHomogeneous d →
    (∀ i, 0 ≤ α i ∧ α i ≤ 1) →
    (∑ i, α i) = d →
    stableBoundaryFactor α *
        polynomialCapacity α p * polynomialCapacity α q
      ≤ coefficientInnerProduct p q

end BeyondBethe

/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.ResidueMinorSelection
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Nat.Find

/-!
# Correcting and normalizing a formal divisor tangent

This file supplies the first constructive part of the formal-divisor argument.
An invertible selected minor of the divisor-tangent matrix gives regular
correction coefficients which kill the selected rows of a transverse
derivative.  If one distinguished coordinate has positive order `a`, while
the divisor-tangent columns have order at least `a` there, characteristic zero
leaves a nonzero coefficient in degree `a - 1` after correction.  Taking the
least nonzero coefficient of the corrected vector then produces a common
power of `X` and a primitive normalized vector.

Every output is constructed from the displayed equations.  No residue-rank,
saturation, splitting, or left-inverse hypothesis is assumed.
-/

namespace Stafford38.GeometryFormalDivisorTangent

open Stafford38.GeometrySplitTangentMatrix
open Stafford38.GeometryResidueMinorSelection

noncomputable section

universe u v w

variable {k : Type u} [Field k]

/-! ## The first nonzero derivative coefficient -/

/-- Differentiating `X^(a+1) u` leaves the expected nonzero leading
coefficient in degree `a`. -/
theorem coeff_derivative_X_pow_succ_mul
    [CharZero k] (u : PowerSeries k) (a : ℕ) :
    PowerSeries.coeff a
        (PowerSeries.derivative
          ((PowerSeries.X : PowerSeries k) ^ (a + 1) * u)) =
      PowerSeries.constantCoeff u * ((a + 1 : ℕ) : k) := by
  rw [PowerSeries.coeff_derivative]
  congr 1
  simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply, Nat.add_comm] using
    (PowerSeries.coeff_X_pow_mul u (a + 1) 0)
  simp

/-- In characteristic zero the leading derivative coefficient above cannot
vanish when the leading coefficient of `u` is nonzero. -/
theorem coeff_derivative_X_pow_succ_mul_ne_zero
    [CharZero k] (u : PowerSeries k) (a : ℕ)
    (hu : PowerSeries.constantCoeff u ≠ 0) :
    PowerSeries.coeff a
        (PowerSeries.derivative
          ((PowerSeries.X : PowerSeries k) ^ (a + 1) * u)) ≠ 0 := by
  rw [coeff_derivative_X_pow_succ_mul]
  exact mul_ne_zero hu (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero a))

/-- The same leading-coefficient statement in the geometric indexing:
`q = X^a u` with `a > 0` has a nonzero derivative coefficient in degree
`a - 1`. -/
theorem coeff_derivative_X_pow_mul_ne_zero
    [CharZero k] (q u : PowerSeries k) (a : ℕ)
    (ha : 0 < a)
    (hq : q = (PowerSeries.X : PowerSeries k) ^ a * u)
    (hu : PowerSeries.constantCoeff u ≠ 0) :
    PowerSeries.coeff (a - 1) (PowerSeries.derivative q) ≠ 0 := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  simpa [hq] using coeff_derivative_X_pow_succ_mul_ne_zero u b hu

/-! ## Selected-minor correction -/

/-- Coefficients obtained by solving the selected square subsystem. -/
def correctionCoefficients
    {ι : Type v} {κ : Type w} [Fintype κ] [DecidableEq κ]
    (Z : Matrix ι κ (PowerSeries k)) (rows : κ ↪ ι)
    (v : ι → PowerSeries k) : κ → PowerSeries k :=
  ((selectedMinor Z rows)⁻¹).mulVec fun j => v (rows j)

/-- Subtract the divisor-tangent combination determined by the selected
minor. -/
def correctedVector
    {ι : Type v} {κ : Type w} [Fintype κ] [DecidableEq κ]
    (Z : Matrix ι κ (PowerSeries k)) (rows : κ ↪ ι)
    (v : ι → PowerSeries k) : ι → PowerSeries k :=
  fun i => v i - Z.mulVec (correctionCoefficients Z rows v) i

/-- A selected minor with nonzero residue determinant eliminates every
selected row exactly over the power-series ring. -/
theorem correctedVector_selectedRow_eq_zero
    {ι : Type v} {κ : Type w} [Fintype κ] [DecidableEq κ]
    (Z : Matrix ι κ (PowerSeries k)) (rows : κ ↪ ι)
    (v : ι → PowerSeries k)
    (hminor :
      PowerSeries.constantCoeff (selectedMinor Z rows).det ≠ 0) :
    ∀ j, correctedVector Z rows v (rows j) = 0 := by
  have hunit : IsUnit (selectedMinor Z rows).det := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    exact isUnit_iff_ne_zero.mpr hminor
  have hinv :
      selectedMinor Z rows * (selectedMinor Z rows)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hunit
  intro j
  have hsolve :
      (selectedMinor Z rows).mulVec (correctionCoefficients Z rows v) =
        fun a => v (rows a) := by
    rw [correctionCoefficients, Matrix.mulVec_mulVec, hinv]
    exact Matrix.one_mulVec _
  change v (rows j) -
      (selectedMinor Z rows).mulVec (correctionCoefficients Z rows v) j = 0
  rw [hsolve]
  exact sub_self _

/-! ## Primitive common-power normalization -/

/-- A vector with a displayed nonzero coefficient has a least common
`X`-order.  Dividing every component by that common power produces a
primitive vector: at least one component has nonzero constant coefficient.

No finiteness assumption on the coordinate type is needed; well-ordering of
the coefficient degree supplies the minimum. -/
theorem exists_primitive_commonPower_of_coeff_ne_zero
    {ι : Type v} (T : ι → PowerSeries k) (i₀ : ι) (bound : ℕ)
    (hcoeff : PowerSeries.coeff bound (T i₀) ≠ 0) :
    ∃ c : ℕ, c ≤ bound ∧
      ∃ B : ι → PowerSeries k,
        (∀ i, T i = (PowerSeries.X : PowerSeries k) ^ c * B i) ∧
        ∃ i, PowerSeries.constantCoeff (B i) ≠ 0 := by
  classical
  let p : ℕ → Prop := fun d => ∃ i, PowerSeries.coeff d (T i) ≠ 0
  have hp : ∃ d, p d := ⟨bound, i₀, hcoeff⟩
  let c : ℕ := Nat.find hp
  have hc_le : c ≤ bound := Nat.find_min' hp ⟨i₀, hcoeff⟩
  have hbelow : ∀ i m, m < c → PowerSeries.coeff m (T i) = 0 := by
    intro i m hm
    by_contra hne
    apply Nat.find_min hp (m := m)
    · simpa [c] using hm
    · exact ⟨i, hne⟩
  have hdvd : ∀ i, (PowerSeries.X : PowerSeries k) ^ c ∣ T i := by
    intro i
    exact PowerSeries.X_pow_dvd_iff.mpr fun m hm => hbelow i m hm
  choose B hB using hdvd
  refine ⟨c, hc_le, B, ?_, ?_⟩
  · intro i
    exact hB i
  · obtain ⟨i, hi⟩ := Nat.find_spec hp
    refine ⟨i, ?_⟩
    have hcoefficient :
        PowerSeries.coeff c (T i) =
          PowerSeries.constantCoeff (B i) := by
      rw [hB i]
      simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply, Nat.add_comm] using
        (PowerSeries.coeff_X_pow_mul (B i) c 0)
    rwa [hcoefficient] at hi

/-! ## The explicit normalized tangent matrix -/

/-- Columns of the formal tangent matrix: position, divisor tangents, and the
normalized transverse tangent. -/
abbrev FormalTangentColumn (κ : Type*) := Unit ⊕ (κ ⊕ Unit)

/-- Assemble the position, divisor-tangent, and normalized transverse columns
without making any rank assertion. -/
def formalTangentMatrix
    {ι : Type v} {κ : Type w}
    (q : ι → PowerSeries k) (Z : Matrix ι κ (PowerSeries k))
    (tau : ι → PowerSeries k) :
    Matrix ι (FormalTangentColumn κ) (PowerSeries k)
  | i, Sum.inl _ => q i
  | i, Sum.inr (Sum.inl j) => Z i j
  | i, Sum.inr (Sum.inr _) => tau i

/-- The chart row, selected divisor minor, and one primitive normalized entry
give an explicit pivot proof that the normalized tangent matrix has full
column rank after reduction modulo `X`. -/
theorem residue_formalTangentMatrix_mulVec_injective
    {ι : Type v} {κ : Type w} [Fintype κ] [DecidableEq κ]
    (q : ι → PowerSeries k) (Z : Matrix ι κ (PowerSeries k))
    (tau : ι → PowerSeries k) (rows : κ ↪ ι) (chart : ι)
    (hqchart : q chart = 1)
    (hZchart : ∀ j, Z chart j = 0)
    (htauchart : tau chart = 0)
    (htauselected : ∀ j, tau (rows j) = 0)
    (hminor :
      PowerSeries.constantCoeff (selectedMinor Z rows).det ≠ 0)
    (hprimitive : ∃ i, PowerSeries.constantCoeff (tau i) ≠ 0) :
    Function.Injective
      (residueMatrix (formalTangentMatrix q Z tau)).mulVec := by
  classical
  intro c₁ c₂ hc
  apply sub_eq_zero.mp
  let c : FormalTangentColumn κ → k := c₁ - c₂
  have hc₀ :
      (residueMatrix (formalTangentMatrix q Z tau)).mulVec c = 0 := by
    change (residueMatrix (formalTangentMatrix q Z tau)).mulVec (c₁ - c₂) = 0
    rw [Matrix.mulVec_sub, hc, sub_self]
  have hposition : c (Sum.inl ()) = 0 := by
    have hchart := congrFun hc₀ chart
    simpa [Matrix.mulVec, dotProduct, residueMatrix, formalTangentMatrix,
      hqchart, hZchart, htauchart] using hchart
  let zc : κ → k := fun j => c (Sum.inr (Sum.inl j))
  have hdivisor : (selectedMinor (residueMatrix Z) rows).mulVec zc = 0 := by
    funext j
    have hrow := congrFun hc₀ (rows j)
    simpa [Matrix.mulVec, dotProduct, selectedMinor, residueMatrix,
      formalTangentMatrix, zc, hposition, htauselected] using hrow
  have hminor_residue : (selectedMinor (residueMatrix Z) rows).det ≠ 0 := by
    rw [← constantCoeff_selectedMinor_det]
    exact hminor
  have hdivisor_zero : zc = 0 := by
    have hinjective :
        Function.Injective (selectedMinor (residueMatrix Z) rows).mulVec := by
      apply Matrix.mulVec_injective_iff_isUnit.mpr
      rw [Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.mpr hminor_residue
    apply hinjective
    simpa using hdivisor
  obtain ⟨pivot, hpivot⟩ := hprimitive
  have htransverse : c (Sum.inr (Sum.inr ())) = 0 := by
    have hp := congrFun hc₀ pivot
    have hz : ∀ j, c (Sum.inr (Sum.inl j)) = 0 := by
      intro j
      exact congrFun hdivisor_zero j
    simpa [Matrix.mulVec, dotProduct, residueMatrix, formalTangentMatrix,
      hposition, hz, hpivot] using hp
  have hc_zero : c = 0 := by
    funext column
    rcases column with (_ | (j | _))
    · exact hposition
    · exact congrFun hdivisor_zero j
    · exact htransverse
  simpa [c] using hc_zero

/-- The same explicit pivots construct a power-series left inverse for the
assembled tangent matrix; no splitting hypothesis is used. -/
theorem exists_formalTangentMatrix_leftInverse
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (q : ι → PowerSeries k) (Z : Matrix ι κ (PowerSeries k))
    (tau : ι → PowerSeries k) (rows : κ ↪ ι) (chart : ι)
    (hqchart : q chart = 1)
    (hZchart : ∀ j, Z chart j = 0)
    (htauchart : tau chart = 0)
    (htauselected : ∀ j, tau (rows j) = 0)
    (hminor :
      PowerSeries.constantCoeff (selectedMinor Z rows).det ≠ 0)
    (hprimitive : ∃ i, PowerSeries.constantCoeff (tau i) ≠ 0) :
    ∃ C : Matrix (FormalTangentColumn κ) ι (PowerSeries k),
      C * formalTangentMatrix q Z tau = 1 := by
  apply powerSeries_exists_leftInverse_of_residue_mulVec_injective
  exact residue_formalTangentMatrix_mulVec_injective
    q Z tau rows chart hqchart hZchart htauchart htauselected
      hminor hprimitive

/-! ## Combined formal-divisor producer -/

/-- The explicit correction-and-normalization block used in the formal
divisor tangent construction.

The selected minor constructs `lambda` and kills its selected rows.  The
distinguished coordinate equation and divisibility of the corresponding row
of `Z` guarantee that the correction cannot cancel the first nonzero
derivative coefficient.  Hence the corrected transverse derivative admits a
primitive common-power normalization of order at most `a - 1`.
-/
theorem exists_corrected_primitive_formalDivisorTangent
    [CharZero k]
    {ι : Type v} {κ : Type w} [Fintype κ] [DecidableEq κ]
    (q : ι → PowerSeries k)
    (Z : Matrix ι κ (PowerSeries k))
    (rows : κ ↪ ι) (zero : ι)
    (a : ℕ) (u₀ : PowerSeries k)
    (ha : 0 < a)
    (hqzero : q zero = (PowerSeries.X : PowerSeries k) ^ a * u₀)
    (hu₀ : PowerSeries.constantCoeff u₀ ≠ 0)
    (hZzero : ∀ j, ∃ w : PowerSeries k,
      Z zero j = (PowerSeries.X : PowerSeries k) ^ a * w)
    (hminor :
      PowerSeries.constantCoeff (selectedMinor Z rows).det ≠ 0) :
    ∃ (lambda : κ → PowerSeries k) (c : ℕ)
      (tau : ι → PowerSeries k),
      lambda = correctionCoefficients Z rows
        (fun i => PowerSeries.derivative (q i)) ∧
      (∀ j,
        PowerSeries.derivative (q (rows j)) =
          Z.mulVec lambda (rows j)) ∧
      (∀ j, tau (rows j) = 0) ∧
      c ≤ a - 1 ∧
      (∀ i,
        PowerSeries.derivative (q i) - Z.mulVec lambda i =
          (PowerSeries.X : PowerSeries k) ^ c * tau i) ∧
      ∃ i, PowerSeries.constantCoeff (tau i) ≠ 0 := by
  let v : ι → PowerSeries k := fun i => PowerSeries.derivative (q i)
  let lambda : κ → PowerSeries k := correctionCoefficients Z rows v
  let T : ι → PowerSeries k := correctedVector Z rows v
  have hselected : ∀ j, T (rows j) = 0 := by
    exact correctedVector_selectedRow_eq_zero Z rows v hminor
  have hderiv : PowerSeries.coeff (a - 1) (v zero) ≠ 0 := by
    exact coeff_derivative_X_pow_mul_ne_zero (q zero) u₀ a ha hqzero hu₀
  have hcombination :
      PowerSeries.coeff (a - 1) (Z.mulVec lambda zero) = 0 := by
    change PowerSeries.coeff (a - 1)
      (∑ j, Z zero j * lambda j) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    obtain ⟨w, hw⟩ := hZzero j
    rw [hw, mul_assoc]
    rw [PowerSeries.coeff_X_pow_mul']
    simp [Nat.not_le_of_gt (Nat.sub_lt ha Nat.zero_lt_one)]
  have hTcoeff : PowerSeries.coeff (a - 1) (T zero) ≠ 0 := by
    change PowerSeries.coeff (a - 1)
      (v zero - Z.mulVec lambda zero) ≠ 0
    rw [map_sub, hcombination, sub_zero]
    exact hderiv
  obtain ⟨c, hc, tau, hfactor, hprimitive⟩ :=
    exists_primitive_commonPower_of_coeff_ne_zero T zero (a - 1) hTcoeff
  refine ⟨lambda, c, tau, rfl, ?_, ?_, hc, ?_, hprimitive⟩
  · intro j
    have hz := hselected j
    change v (rows j) - Z.mulVec lambda (rows j) = 0 at hz
    exact sub_eq_zero.mp hz
  · intro j
    have hz : (PowerSeries.X : PowerSeries k) ^ c * tau (rows j) = 0 := by
      rw [← hfactor (rows j), hselected j]
    exact (mul_eq_zero.mp hz).resolve_left
      (pow_ne_zero c PowerSeries.X_ne_zero)
  · intro i
    exact hfactor i

/-- With an explicit affine chart row, the corrected primitive tangent above
assembles into a matrix whose residue columns are injective.  This is the
complete local formal-divisor producer: residue injectivity is a conclusion,
not an input. -/
theorem exists_formalDivisorTangent_residue_injective
    [CharZero k]
    {ι : Type v} {κ : Type w} [Fintype κ] [DecidableEq κ]
    (q : ι → PowerSeries k)
    (Z : Matrix ι κ (PowerSeries k))
    (rows : κ ↪ ι) (chart zero : ι)
    (a : ℕ) (u₀ : PowerSeries k)
    (hqchart : q chart = 1)
    (hZchart : ∀ j, Z chart j = 0)
    (ha : 0 < a)
    (hqzero : q zero = (PowerSeries.X : PowerSeries k) ^ a * u₀)
    (hu₀ : PowerSeries.constantCoeff u₀ ≠ 0)
    (hZzero : ∀ j, ∃ w : PowerSeries k,
      Z zero j = (PowerSeries.X : PowerSeries k) ^ a * w)
    (hminor :
      PowerSeries.constantCoeff (selectedMinor Z rows).det ≠ 0) :
    ∃ (lambda : κ → PowerSeries k) (c : ℕ)
      (tau : ι → PowerSeries k),
      lambda = correctionCoefficients Z rows
        (fun i => PowerSeries.derivative (q i)) ∧
      (∀ j,
        PowerSeries.derivative (q (rows j)) =
          Z.mulVec lambda (rows j)) ∧
      tau chart = 0 ∧
      (∀ j, tau (rows j) = 0) ∧
      c ≤ a - 1 ∧
      (∀ i,
        PowerSeries.derivative (q i) - Z.mulVec lambda i =
          (PowerSeries.X : PowerSeries k) ^ c * tau i) ∧
      (∃ i, PowerSeries.constantCoeff (tau i) ≠ 0) ∧
      Function.Injective
        (residueMatrix (formalTangentMatrix q Z tau)).mulVec := by
  obtain ⟨lambda, c, tau, hlambda, hselected, htauselected,
      hc, hfactor, hprimitive⟩ :=
    exists_corrected_primitive_formalDivisorTangent
      q Z rows zero a u₀ ha hqzero hu₀ hZzero hminor
  have hderivative_chart : PowerSeries.derivative (q chart) = 0 := by
    simp [hqchart]
  have hcombination_chart : Z.mulVec lambda chart = 0 := by
    simp [Matrix.mulVec, dotProduct, hZchart]
  have htauchart : tau chart = 0 := by
    have hz := hfactor chart
    rw [hderivative_chart, hcombination_chart, sub_zero] at hz
    have hproduct : (PowerSeries.X : PowerSeries k) ^ c * tau chart = 0 :=
      hz.symm
    exact (mul_eq_zero.mp hproduct).resolve_left
      (pow_ne_zero c PowerSeries.X_ne_zero)
  have hinjective : Function.Injective
      (residueMatrix (formalTangentMatrix q Z tau)).mulVec :=
    residue_formalTangentMatrix_mulVec_injective
      q Z tau rows chart hqchart hZchart htauchart htauselected
        hminor hprimitive
  exact ⟨lambda, c, tau, hlambda, hselected, htauchart, htauselected,
    hc, hfactor, hprimitive, hinjective⟩


end

end Stafford38.GeometryFormalDivisorTangent

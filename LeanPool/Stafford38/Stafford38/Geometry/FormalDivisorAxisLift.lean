/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Geometry.FormalDivisorTangent
public import LeanPool.Stafford38.Stafford38.Geometry.PowerSeriesTangentLimit


/-!
# The axis lift for a formal divisor tangent

This file completes the local power-series part of the formal-divisor
construction.  If the distinguished axis coordinate and every divisor-tangent
entry in that row vanish to order at least `b`, while the common factor removed
from the corrected transverse derivative has order at most `a - 1 < b - 1`,
then the normalized transverse tangent has zero axis residue.  Consequently
the pure axis covector annihilates every reduced tangent column.

The residue-rank theorem from `FormalDivisorTangent` supplies a power-series
left inverse.  Retraction correction then produces an exact annihilator whose
residue is the pure axis covector.  No normalization, projective divisor,
formal-chart construction, or global conormal-closure statement is made here.
-/

@[expose] public section

namespace Stafford38.GeometryFormalDivisorAxisLift

open Stafford38.GeometryFormalDivisorTangent
open Stafford38.GeometryPowerSeriesTangentLimit
open Stafford38.GeometryRetractionSpecialization
open Stafford38.GeometryResidueMinorSelection
open Stafford38.GeometrySplitTangentMatrix

noncomputable section

universe u v w

variable {k : Type u} [Field k]

/-! ## The strict axis-order calculation -/

/-- The factor removed from the corrected transverse derivative has strictly
smaller order than the axis row.  Therefore the normalized transverse tangent
still vanishes at the closed point in the axis coordinate. -/
theorem constantCoeff_normalizedTransverse_axis_eq_zero
    {ι : Type v} {κ : Type w} [Fintype κ]
    (q : ι → PowerSeries k)
    (Z : Matrix ι κ (PowerSeries k))
    (lambda : κ → PowerSeries k)
    (tau : ι → PowerSeries k)
    (axis : ι) (a b c : ℕ) (u₁ : PowerSeries k)
    (ha : 0 < a)
    (hab : a < b)
    (hc : c ≤ a - 1)
    (hqaxis : q axis = (PowerSeries.X : PowerSeries k) ^ b * u₁)
    (hZaxis : ∀ j, ∃ w : PowerSeries k,
      Z axis j = (PowerSeries.X : PowerSeries k) ^ b * w)
    (hfactor :
      PowerSeries.derivative (q axis) - Z.mulVec lambda axis =
        (PowerSeries.X : PowerSeries k) ^ c * tau axis) :
    PowerSeries.constantCoeff (tau axis) = 0 := by
  have hcb : c < b := by omega
  have hcsuccb : c + 1 < b := by omega
  have hderivative :
      PowerSeries.coeff c (PowerSeries.derivative (q axis)) = 0 := by
    rw [PowerSeries.coeff_derivative, hqaxis]
    rw [PowerSeries.coeff_X_pow_mul']
    simp [Nat.not_le_of_gt hcsuccb]
  have hcombination :
      PowerSeries.coeff c (Z.mulVec lambda axis) = 0 := by
    change PowerSeries.coeff c (∑ j, Z axis j * lambda j) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    obtain ⟨w, hw⟩ := hZaxis j
    rw [hw, mul_assoc]
    rw [PowerSeries.coeff_X_pow_mul']
    simp [Nat.not_le_of_gt hcb]
  have hcorrected :
      PowerSeries.coeff c
        (PowerSeries.derivative (q axis) - Z.mulVec lambda axis) = 0 := by
    rw [map_sub, hderivative, hcombination, sub_zero]
  have hnormalized :
      PowerSeries.coeff c
          ((PowerSeries.X : PowerSeries k) ^ c * tau axis) =
        PowerSeries.constantCoeff (tau axis) := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply, Nat.add_comm] using
      (PowerSeries.coeff_X_pow_mul (tau axis) c 0)
  rw [← hnormalized, ← hfactor]
  exact hcorrected

/-! ## The axis covector on the assembled tangent matrix -/

/-- Vanishing of the position, divisor, and normalized transverse entries in
the axis row gives residue-zero for every assembled tangent column. -/
theorem constantCoeff_formalTangentMatrix_axis_eq_zero
    {ι : Type v} {κ : Type w}
    (q : ι → PowerSeries k)
    (Z : Matrix ι κ (PowerSeries k))
    (tau : ι → PowerSeries k)
    (axis : ι) (b : ℕ) (u₁ : PowerSeries k)
    (hb : 0 < b)
    (hqaxis : q axis = (PowerSeries.X : PowerSeries k) ^ b * u₁)
    (hZaxis : ∀ j, ∃ w : PowerSeries k,
      Z axis j = (PowerSeries.X : PowerSeries k) ^ b * w)
    (htauaxis : PowerSeries.constantCoeff (tau axis) = 0) :
    ∀ column : FormalTangentColumn κ,
      PowerSeries.constantCoeff
        (formalTangentMatrix q Z tau axis column) = 0 := by
  intro column
  rcases column with (_ | (j | _))
  · rw [formalTangentMatrix, hqaxis]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
    simp [pow_succ]
  · rw [formalTangentMatrix]
    obtain ⟨w, hw⟩ := hZaxis j
    rw [hw]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
    simp [pow_succ]
  · simpa [formalTangentMatrix] using htauaxis

/-- The pure axis covector annihilates the residue of the assembled tangent
matrix. -/
theorem axisRow_residue_formalTangentMatrix_eq_zero
    {ι : Type v} {κ : Type w} [Fintype ι] [DecidableEq ι]
    (q : ι → PowerSeries k)
    (Z : Matrix ι κ (PowerSeries k))
    (tau : ι → PowerSeries k)
    (axis : ι)
    (haxis : ∀ column : FormalTangentColumn κ,
      PowerSeries.constantCoeff
        (formalTangentMatrix q Z tau axis column) = 0) :
    rowMul (axisRow (k := k) axis)
      (fun i column => PowerSeries.constantCoeff
        (formalTangentMatrix q Z tau i column)) = 0 := by
  funext column
  simp [rowMul, axisRow, haxis column]

/-! ## Complete local axis lift -/

/-- The complete local formal-divisor axis lift.

The correction and primitive normalization are constructed from the formal
chart data.  The strict axis-order hypotheses force the pure axis covector to
annihilate the reduced tangent matrix.  A left inverse derived from the same
matrix then gives an exact power-series annihilator specializing to that
covector.
-/
theorem exists_formalDivisorAxisLift
    [CharZero k]
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (q : ι → PowerSeries k)
    (Z : Matrix ι κ (PowerSeries k))
    (rows : κ ↪ ι) (chart zero axis : ι)
    (a b : ℕ) (u₀ u₁ : PowerSeries k)
    (hqchart : q chart = 1)
    (hZchart : ∀ j, Z chart j = 0)
    (ha : 0 < a)
    (hab : a < b)
    (hqzero : q zero = (PowerSeries.X : PowerSeries k) ^ a * u₀)
    (hu₀ : PowerSeries.constantCoeff u₀ ≠ 0)
    (hZzero : ∀ j, ∃ w : PowerSeries k,
      Z zero j = (PowerSeries.X : PowerSeries k) ^ a * w)
    (hqaxis : q axis = (PowerSeries.X : PowerSeries k) ^ b * u₁)
    (hZaxis : ∀ j, ∃ w : PowerSeries k,
      Z axis j = (PowerSeries.X : PowerSeries k) ^ b * w)
    (hminor :
      PowerSeries.constantCoeff (selectedMinor Z rows).det ≠ 0) :
    ∃ (lambda : κ → PowerSeries k) (c : ℕ)
      (tau : ι → PowerSeries k)
      (C : Matrix (FormalTangentColumn κ) ι (PowerSeries k))
      (ell : ι → PowerSeries k),
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
      PowerSeries.constantCoeff (tau axis) = 0 ∧
      (∀ column : FormalTangentColumn κ,
        PowerSeries.constantCoeff
          (formalTangentMatrix q Z tau axis column) = 0) ∧
      C * formalTangentMatrix q Z tau = 1 ∧
      rowMul ell (formalTangentMatrix q Z tau) = 0 ∧
      residueColumn ell = axisRow (k := k) axis := by
  obtain ⟨lambda, c, tau, hlambda, hselected, htauchart,
      htauselected, hc, hfactor, hprimitive, hinjective⟩ :=
    exists_formalDivisorTangent_residue_injective
      q Z rows chart zero a u₀ hqchart hZchart ha hqzero hu₀
        hZzero hminor
  have htauaxis : PowerSeries.constantCoeff (tau axis) = 0 :=
    constantCoeff_normalizedTransverse_axis_eq_zero
      q Z lambda tau axis a b c u₁ ha hab hc hqaxis hZaxis (hfactor axis)
  have hb : 0 < b := lt_trans ha hab
  have haxiscolumns : ∀ column : FormalTangentColumn κ,
      PowerSeries.constantCoeff
        (formalTangentMatrix q Z tau axis column) = 0 :=
    constantCoeff_formalTangentMatrix_axis_eq_zero
      q Z tau axis b u₁ hb hqaxis hZaxis htauaxis
  obtain ⟨C, hCB⟩ :=
    powerSeries_exists_leftInverse_of_residue_mulVec_injective
      (formalTangentMatrix q Z tau) hinjective
  let a₀ : ι → k := axisRow (k := k) axis
  let ell : ι → PowerSeries k :=
    annihilatorLift (constantColumn a₀)
      (formalTangentMatrix q Z tau) C
  have hresidueInput : residueColumn (constantColumn a₀) = a₀ :=
    residueColumn_constantColumn a₀
  have haxisRow :
      rowMul a₀
        (fun i column => PowerSeries.constantCoeff
          (formalTangentMatrix q Z tau i column)) = 0 :=
    axisRow_residue_formalTangentMatrix_eq_zero
      q Z tau axis haxiscolumns
  have hell :
      rowMul ell (formalTangentMatrix q Z tau) = 0 ∧
        residueColumn ell = a₀ := by
    simpa [ell] using
      (powerSeries_annihilatorLift_spec
        (constantColumn a₀) a₀ (formalTangentMatrix q Z tau) C
          hCB hresidueInput haxisRow)
  exact ⟨lambda, c, tau, C, ell, hlambda, hselected, htauchart,
    htauselected, hc, hfactor, hprimitive, htauaxis, haxiscolumns,
    hCB, hell.1, by simpa [a₀] using hell.2⟩


end

end Stafford38.GeometryFormalDivisorAxisLift

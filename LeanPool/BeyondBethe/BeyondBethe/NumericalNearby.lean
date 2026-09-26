/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.NumericalScales
public import Mathlib.Tactic

/-! # Numerical Nearby -/

@[expose] public section

namespace BeyondBethe

/-!
# The nearby-matrix step in certified optimization

An approximate KKT point for a rational input matrix is turned into an exact
KKT point for a nearby positive real matrix.  This file proves the sign and
normalization-sensitive comparison used to transfer the permanent estimate
back to the input matrix.
-/

/-- Matrix for which the proposed point and potentials satisfy the
multiplicative KKT equations exactly. -/
noncomputable def nearbyKKTMatrix
    {ι : Type*} (τ : ℝ) (X : Matrix ι ι ℝ) (r c : ι → ℝ) :
    Matrix ι ι ℝ :=
  fun i j ↦ Real.exp (r i + c j) *
    (X i j) ^ (1 + τ) * (1 - X i j)

/-- Coordinatewise approximate logarithmic KKT equations. -/
def HasApproximateLogKKT
    {ι : Type*} [Fintype ι]
    (ε τ : ℝ) (A X : Matrix ι ι ℝ) (r c : ι → ℝ) : Prop :=
  ∀ i j, abs (Real.log (A i j) -
    (r i + c j + (1 + τ) * Real.log (X i j) +
      Real.log (1 - X i j))) ≤ ε

theorem nearbyKKTMatrix_positive
    {ι : Type*} {τ : ℝ} {X : Matrix ι ι ℝ} {r c : ι → ℝ}
    (hXpos : ∀ i j, 0 < X i j)
    (hXlt : ∀ i j, X i j < 1) :
    Matrix.Positive (nearbyKKTMatrix τ X r c) := by
  intro i j
  exact mul_pos (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (hXpos i j) _))
    (sub_pos.mpr (hXlt i j))

theorem log_nearbyKKTMatrix
    {ι : Type*} {τ : ℝ} {X : Matrix ι ι ℝ} {r c : ι → ℝ}
    (hXpos : ∀ i j, 0 < X i j)
    (hXlt : ∀ i j, X i j < 1) (i j : ι) :
    Real.log (nearbyKKTMatrix τ X r c i j) =
      r i + c j + (1 + τ) * Real.log (X i j) +
        Real.log (1 - X i j) := by
  have hx := hXpos i j
  have hc : 0 < 1 - X i j := sub_pos.mpr (hXlt i j)
  rw [nearbyKKTMatrix,
    Real.log_mul
      (mul_ne_zero (Real.exp_pos _).ne'
        (Real.rpow_pos_of_pos hx _).ne') hc.ne',
    Real.log_mul (Real.exp_pos _).ne'
      (Real.rpow_pos_of_pos hx _).ne',
    Real.log_exp, Real.log_rpow hx]

theorem nearbyKKTMatrix_hasLogKKT
    {ι : Type*} [Fintype ι]
    {τ : ℝ} {X : Matrix ι ι ℝ} {r c : ι → ℝ}
    (hXpos : ∀ i j, 0 < X i j)
    (hXlt : ∀ i j, X i j < 1) :
    HasLogKKT τ (nearbyKKTMatrix τ X r c) X r c := by
  intro i j
  exact log_nearbyKKTMatrix hXpos hXlt i j

theorem approximateLogKKT_nearby_log_bounds
    {ι : Type*} [Fintype ι]
    {ε τ : ℝ} {A X : Matrix ι ι ℝ} {r c : ι → ℝ}
    (happrox : HasApproximateLogKKT ε τ A X r c)
    (hXpos : ∀ i j, 0 < X i j)
    (hXlt : ∀ i j, X i j < 1) (i j : ι) :
    Real.log (nearbyKKTMatrix τ X r c i j) - ε ≤
        Real.log (A i j) ∧
      Real.log (A i j) ≤
        Real.log (nearbyKKTMatrix τ X r c i j) + ε := by
  have h := (abs_le.mp (happrox i j))
  rw [← log_nearbyKKTMatrix hXpos hXlt i j] at h
  constructor <;> linarith

theorem approximateLogKKT_entrywise_comparison
    {ι : Type*} [Fintype ι]
    {ε τ : ℝ} {A X : Matrix ι ι ℝ} {r c : ι → ℝ}
    (hApos : Matrix.Positive A)
    (happrox : HasApproximateLogKKT ε τ A X r c)
    (hXpos : ∀ i j, 0 < X i j)
    (hXlt : ∀ i j, X i j < 1) (i j : ι) :
    Real.exp (-ε) * nearbyKKTMatrix τ X r c i j ≤ A i j ∧
      A i j ≤ Real.exp ε * nearbyKKTMatrix τ X r c i j := by
  have hnearPos := nearbyKKTMatrix_positive
    (τ := τ) (r := r) (c := c) hXpos hXlt i j
  obtain ⟨hlower, hupper⟩ := approximateLogKKT_nearby_log_bounds
    happrox hXpos hXlt i j
  have hlowerExp := Real.exp_le_exp.mpr hlower
  have hupperExp := Real.exp_le_exp.mpr hupper
  rw [Real.exp_sub, Real.exp_log hnearPos, Real.exp_log (hApos i j)] at hlowerExp
  rw [Real.exp_add, Real.exp_log hnearPos, Real.exp_log (hApos i j)] at hupperExp
  simpa [div_eq_mul_inv, Real.exp_neg, mul_comm] using
    And.intro hlowerExp hupperExp

theorem approximateLogKKT_permanent_comparison
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ε τ : ℝ} {A X : Matrix ι ι ℝ} {r c : ι → ℝ}
    (hApos : Matrix.Positive A)
    (happrox : HasApproximateLogKKT ε τ A X r c)
    (hXpos : ∀ i j, 0 < X i j)
    (hXlt : ∀ i j, X i j < 1) :
    (Real.exp (-ε)) ^ Fintype.card ι *
        Matrix.permanent (nearbyKKTMatrix τ X r c) ≤
      Matrix.permanent A ∧
      Matrix.permanent A ≤
        (Real.exp ε) ^ Fintype.card ι *
          Matrix.permanent (nearbyKKTMatrix τ X r c) := by
  let A' := nearbyKKTMatrix τ X r c
  have hA'pos : Matrix.Positive A' := nearbyKKTMatrix_positive hXpos hXlt
  have hlowerEntries : ∀ i j, Real.exp (-ε) * A' i j ≤ A i j :=
    fun i j ↦ (approximateLogKKT_entrywise_comparison hApos happrox
      hXpos hXlt i j).1
  have hupperEntries : ∀ i j, A i j ≤ Real.exp ε * A' i j :=
    fun i j ↦ (approximateLogKKT_entrywise_comparison hApos happrox
      hXpos hXlt i j).2
  have hA0 : Matrix.Nonnegative A := fun i j ↦ (hApos i j).le
  have hA'0 : Matrix.Nonnegative A' := fun i j ↦ (hA'pos i j).le
  constructor
  · rw [← Matrix.permanent_scale_real]
    exact Matrix.permanent_mono_real
      (fun i j ↦ mul_nonneg (Real.exp_pos _).le (hA'0 i j))
      hlowerEntries
  · rw [← Matrix.permanent_scale_real]
    exact Matrix.permanent_mono_real hA0 hupperEntries

/-- Row entropy is concave along a matrix segment. -/
theorem totalRowEntropy_segment_lower
    {ι : Type*} [Fintype ι]
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {X Y : Matrix ι ι ℝ}
    (hX : Matrix.Nonnegative X) (hY : Matrix.Nonnegative Y) :
    (1 - t) * totalRowEntropy X + t * totalRowEntropy Y ≤
      totalRowEntropy (matrixSegment t X Y) := by
  simp only [totalRowEntropy, shannonEntropy]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have hgap := negMulLog_segment_gap_nonneg ht0 ht1 (hX i j) (hY i j)
  dsimp only [matrixSegment]
  linarith

/-- Concavity of the entropy-regularized Bethe objective on the Birkhoff
polytope. -/
theorem regularizedBetheObjective_segment_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 1 < Fintype.card ι)
    {τ t : ℝ} (hτ : 0 ≤ τ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (A : Matrix ι ι ℝ) {X Y : Matrix ι ι ℝ}
    (hX : IsDoublyStochastic X) (hY : IsDoublyStochastic Y) :
    (1 - t) * regularizedBetheObjective τ A X +
        t * regularizedBetheObjective τ A Y ≤
      regularizedBetheObjective τ A (matrixSegment t X Y) := by
  have hbethe := betheObjective_segment_lower hcard A X Y hX hY ht0 ht1
  have hsegment : betheMatrixSegment t X Y = matrixSegment t X Y := by
    ext i j
    rfl
  rw [hsegment] at hbethe
  have hentropy := totalRowEntropy_segment_lower ht0 ht1
    hX.nonnegative hY.nonnegative
  have hscaled := mul_le_mul_of_nonneg_left hentropy hτ
  rw [regularizedBetheObjective, regularizedBetheObjective,
    regularizedBetheObjective]
  nlinarith

/-- The one-dimensional restriction of the regularized objective to any
Birkhoff segment is concave. -/
theorem regularizedBetheObjective_line_concave
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 1 < Fintype.card ι)
    {τ : ℝ} (hτ : 0 ≤ τ) (A : Matrix ι ι ℝ)
    {X Y : Matrix ι ι ℝ}
    (hX : IsDoublyStochastic X) (hY : IsDoublyStochastic Y) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun t ↦ regularizedBetheObjective τ A (matrixSegment t X Y)) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hsegX := matrixSegment_doublyStochastic hx.1 hx.2 hX hY
  have hsegY := matrixSegment_doublyStochastic hy.1 hy.2 hX hY
  have hb1 : b ≤ 1 := by linarith
  have hmain := regularizedBetheObjective_segment_lower hcard hτ hb hb1 A
    hsegX hsegY
  have hweight : 1 - b = a := by linarith
  have hnested : matrixSegment b (matrixSegment x X Y)
      (matrixSegment y X Y) = matrixSegment (a * x + b * y) X Y := by
    ext i j
    dsimp only [matrixSegment]
    rw [hweight]
    linear_combination (X i j) * hab
  simpa only [smul_eq_mul, hweight, hnested] using hmain

/-- First-order upper support inequality for the regularized objective. -/
theorem regularizedBetheObjective_sub_le_gradient
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 1 < Fintype.card ι)
    {τ : ℝ} (hτ : 0 ≤ τ) {A X Y : Matrix ι ι ℝ}
    (hX : IsDoublyStochastic X) (hY : IsDoublyStochastic Y)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i)) :
    regularizedBetheObjective τ A Y - regularizedBetheObjective τ A X ≤
      ∑ i, ∑ j, regularizedBetheGradient τ A X i j * (Y i j - X i j) := by
  have hderiv : HasDerivAt
      (fun t ↦ regularizedBetheObjective τ A (matrixSegment t X Y))
      (∑ i, ∑ j, regularizedBetheGradient τ A X i j *
        (Y i j - X i j)) 0 := by
    have hbase := hasDerivAt_regularizedBetheObjective_line
      (τ := τ) (A := A) (X := X)
      (D := fun i j ↦ Y i j - X i j) hXint
    convert hbase using 1
    funext t
    congr 1
    ext i j
    dsimp only [matrixSegment, linearMatrixPerturb]
    ring
  have hconc := regularizedBetheObjective_line_concave
    hcard hτ A hX hY
  have hslope := hconc.slope_le_of_hasDerivAt
    (Set.mem_Icc.mpr ⟨le_rfl, by norm_num⟩)
    (Set.mem_Icc.mpr ⟨by norm_num, le_rfl⟩)
    (by norm_num : (0 : ℝ) < 1) hderiv
  have hzero : matrixSegment 0 X Y = X := by
    ext i j
    simp [matrixSegment]
  have hone : matrixSegment 1 X Y = Y := by
    ext i j
    simp [matrixSegment]
  simpa [slope, hzero, hone] using hslope

/-- Exact logarithmic KKT equations are sufficient for global optimality of
the regularized objective. -/
theorem regularizedBetheObjective_le_of_logKKT
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 1 < Fintype.card ι)
    {τ : ℝ} (hτ : 0 ≤ τ) {A X : Matrix ι ι ℝ}
    (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    {r c : ι → ℝ} (hKKT : HasLogKKT τ A X r c) :
    ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective τ A Y ≤
        regularizedBetheObjective τ A X := by
  intro Y hY
  have hsupport := regularizedBetheObjective_sub_le_gradient
    (A := A) hcard hτ hX hY hXint
  have hgrad : ∀ i j, regularizedBetheGradient τ A X i j =
      r i + c j - (2 + τ) := by
    intro i j
    specialize hKKT i j
    dsimp only [regularizedBetheGradient]
    linarith
  have hzero :
      ∑ i, ∑ j, regularizedBetheGradient τ A X i j *
          (Y i j - X i j) = 0 := by
    simp_rw [hgrad]
    have hpot := rowColumnPotential_sum_eq hY hX
      (fun i ↦ r i - (2 + τ)) c
    have hpot' :
        (∑ i, ∑ j, (r i + c j - (2 + τ)) * Y i j) =
          ∑ i, ∑ j, (r i + c j - (2 + τ)) * X i j := by
      convert hpot using 1 <;>
        apply Finset.sum_congr rfl <;> intro i _ <;>
        apply Finset.sum_congr rfl <;> intro j _ <;> ring
    calc
      (∑ i, ∑ j, (r i + c j - (2 + τ)) * (Y i j - X i j)) =
          (∑ i, ∑ j, (r i + c j - (2 + τ)) * Y i j) -
            ∑ i, ∑ j, (r i + c j - (2 + τ)) * X i j := by
              simp_rw [mul_sub, Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr hpot'
  linarith

/-- The nearby KKT matrix makes the proposed interior doubly stochastic point
an exact regularized optimizer. -/
theorem nearbyKKTMatrix_exact_optimizer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 1 < Fintype.card ι)
    {τ : ℝ} (hτ : 0 ≤ τ) {X : Matrix ι ι ℝ}
    (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (r c : ι → ℝ) :
    ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective τ (nearbyKKTMatrix τ X r c) Y ≤
        regularizedBetheObjective τ (nearbyKKTMatrix τ X r c) X := by
  have hXpos : ∀ i j, 0 < X i j := fun i j ↦ (hXint i).2 j |>.1
  have hXlt : ∀ i j, X i j < 1 := fun i j ↦ (hXint i).2 j |>.2
  exact regularizedBetheObjective_le_of_logKKT hcard hτ hX hXint
    (nearbyKKTMatrix_hasLogKKT hXpos hXlt)

end BeyondBethe

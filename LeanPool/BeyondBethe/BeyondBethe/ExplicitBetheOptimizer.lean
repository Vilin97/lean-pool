/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.ExplicitOptimizerScales
import Mathlib.Tactic

/-! # Explicit Bethe Optimizer -/

namespace BeyondBethe

/-!
# The concrete rational regularized-Bethe optimizer

This file fixes every parameter of the rational threshold oracle and
bisection.  The exact real maximizer below appears only in correctness
proofs; the state and returned point are executable rational data.
-/

def explicitBetheOptimizerInitialState {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    BetheBisectionState (m * m + 1) :=
  initialBetheBisectionState (explicitRegularizationScale (m + 1)) A
    (explicitOptimizerPrecision A) (explicitOptimizerFloor A)
    (explicitOptimizerMix A) (explicitOptimizerInnerRadius A)

def explicitBetheOptimizerState {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    BetheBisectionState (m * m + 1) :=
  runBetheBisection (explicitRegularizationScale (m + 1)) A
    (explicitOptimizerPrecision A) (explicitOptimizerFloor A)
    (explicitOptimizerInnerRadius A) (explicitOptimizerBisectionSteps A)
    (explicitBetheOptimizerInitialState A)

/-- The default branch is unreachable on positive normalized inputs, but
keeps the algorithm total on every rational matrix. -/
def explicitBetheOptimizerPoint {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    Fin (m * m + 1) → ℚ :=
  (explicitBetheOptimizerState A).witness.getD 0

def explicitBetheOptimizerMatrix {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ :=
  betheAffineMatrixQ (epigraphBase (explicitBetheOptimizerPoint A))

def explicitBetheOptimizerGradient {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ :=
  directedNegativeGradientLowerMatrix
    (explicitRegularizationScale (m + 1)) A
    (explicitBetheOptimizerMatrix A) (explicitOptimizerPrecision A)

/-- Rational row potentials obtained by anchoring the directed negative
gradient at the first column. -/
def explicitBetheOptimizerRowPotential {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) : Fin (m + 1) → ℚ :=
  fun i ↦ -explicitBetheOptimizerGradient A i 0 +
    (2 + explicitRegularizationScale (m + 1))

/-- Rational column potentials, normalized to vanish at the first column. -/
def explicitBetheOptimizerColumnPotential {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) : Fin (m + 1) → ℚ :=
  fun j ↦ -(explicitBetheOptimizerGradient A 0 j -
    explicitBetheOptimizerGradient A 0 0)

theorem HasApproximateLogKKT.mono
    {ι : Type*} [Fintype ι] {ε ε' τ : ℝ}
    {A X : Matrix ι ι ℝ} {R C : ι → ℝ}
    (h : HasApproximateLogKKT ε τ A X R C) (hε : ε ≤ ε') :
    HasApproximateLogKKT ε' τ A X R C := by
  intro i j
  exact (h i j).trans hε

theorem explicitBetheOptimizerPoint_spec {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1) :
    BetheEpigraphOracleAccepted (explicitRegularizationScale (m + 1)) A
        (explicitOptimizerPrecision A) (explicitOptimizerFloor A)
        (explicitBetheOptimizerState A).high
        (explicitBetheOptimizerPoint A) ∧
      IsDoublyStochastic
        (fun i j ↦ ((explicitBetheOptimizerMatrix A i j : ℚ) : ℝ)) ∧
      (∀ i j, (explicitOptimizerFloor A : ℝ) ≤
        (explicitBetheOptimizerMatrix A i j : ℝ)) ∧
      ∃ X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ,
        IsDoublyStochastic X ∧
        (∀ Y, IsDoublyStochastic Y →
          regularizedBetheObjective
              (explicitRegularizationScale (m + 1) : ℝ)
              (fun i j ↦ (A i j : ℝ)) Y ≤
            regularizedBetheObjective
              (explicitRegularizationScale (m + 1) : ℝ)
              (fun i j ↦ (A i j : ℝ)) X) ∧
        regularizedBetheObjective
              (explicitRegularizationScale (m + 1) : ℝ)
              (fun i j ↦ (A i j : ℝ)) X -
            regularizedBetheObjective
              (explicitRegularizationScale (m + 1) : ℝ)
              (fun i j ↦ (A i j : ℝ))
              (fun i j ↦ ((explicitBetheOptimizerMatrix A i j : ℚ) : ℝ)) ≤
          (explicitOptimizerGap A : ℝ) := by
  let τ : ℚ := explicitRegularizationScale (m + 1)
  obtain ⟨X, hX, hmax⟩ := exists_regularizedBetheMaximizer
    (τ : ℝ) (fun i j ↦ (A i j : ℝ))
  have hτ0 : 0 < τ := explicitRegularizationScale_pos (by omega)
  have hτ1 : τ ≤ 1 := explicitRegularizationScale_le_one (by omega)
  have hrun := runBetheBisection_objective_gap hm hτ0 hτ1 hApos hAupper
    hX hmax (explicitOptimizerMix_pos A) (explicitOptimizerMix_le_one A)
    (explicitOptimizerFloor_pos A) (explicitOptimizerInnerRadius_pos A)
    (explicitOptimizerInnerRadius_spike A)
    (explicitOptimizerFloor_le_smoothedFloor A)
    (explicitOptimizerPrecision A) (explicitOptimizerBisectionSteps A)
  have hrun' : ∃ q : Fin (m * m + 1) → ℚ,
      (explicitBetheOptimizerState A).witness = some q ∧
      BetheEpigraphOracleAccepted τ A (explicitOptimizerPrecision A)
        (explicitOptimizerFloor A) (explicitBetheOptimizerState A).high q ∧
      IsDoublyStochastic (acceptedBetheMatrix q) ∧
      (∀ i j, (explicitOptimizerFloor A : ℝ) ≤ acceptedBetheMatrix q i j) ∧
      regularizedBetheObjective (τ : ℝ) (fun i j ↦ (A i j : ℝ)) X -
        regularizedBetheObjective (τ : ℝ) (fun i j ↦ (A i j : ℝ))
          (acceptedBetheMatrix q) ≤
        (betheSmoothingSlack A (explicitOptimizerMix A)
            (explicitOptimizerInnerRadius A) : ℝ) +
          (explicitOptimizerInitialWidth A /
              2 ^ explicitOptimizerBisectionSteps A : ℚ) +
          (betheObjectiveEvaluationError m
            (explicitOptimizerPrecision A) : ℝ) := by
    simpa only [τ, explicitBetheOptimizerState,
      explicitBetheOptimizerInitialState, explicitOptimizerInitialWidth]
      using hrun
  obtain ⟨q, hq, haccepted, hqDS, hqfloor, hqgap⟩ := hrun'
  have hpoint : explicitBetheOptimizerPoint A = q := by
    rw [explicitBetheOptimizerPoint, hq]
    rfl
  have hmatrixCast :
      (fun i j ↦ ((explicitBetheOptimizerMatrix A i j : ℚ) : ℝ)) =
        acceptedBetheMatrix q := by
    ext i j
    rw [explicitBetheOptimizerMatrix, hpoint]
    exact cast_betheAffineMatrixQ (epigraphBase q) i j
  have htotalQ := explicitOptimizerTotalObjectiveError_lt A
  have htotal :
      (betheSmoothingSlack A (explicitOptimizerMix A)
            (explicitOptimizerInnerRadius A) : ℝ) +
          (explicitOptimizerInitialWidth A /
              2 ^ explicitOptimizerBisectionSteps A : ℚ) +
          (betheObjectiveEvaluationError m
            (explicitOptimizerPrecision A) : ℝ) <
        (explicitOptimizerGap A : ℝ) := by
    exact_mod_cast htotalQ
  refine ⟨?_, ?_, ?_, X, hX, hmax, ?_⟩
  · simpa only [τ, hpoint] using haccepted
  · simpa only [hmatrixCast] using hqDS
  · intro i j
    change (explicitOptimizerFloor A : ℝ) ≤
      (fun a b ↦ ((explicitBetheOptimizerMatrix A a b : ℚ) : ℝ)) i j
    rw [hmatrixCast]
    exact hqfloor i j
  · rw [hmatrixCast]
    exact hqgap.trans htotal.le

/-- Any rational matrix satisfying the concrete optimizer's feasibility and
objective-gap specification yields the same anchored approximate logarithmic
KKT certificate.  This formulation separates the analytic argument from the
tie-breaking rule used by the executable separation oracle. -/
theorem hasApproximateLogKKT_of_explicitOptimizerSpec {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1)
    (Xq : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hY : IsDoublyStochastic (fun i j ↦ ((Xq i j : ℚ) : ℝ)))
    (hYlo : ∀ i j, (explicitOptimizerFloor A : ℝ) ≤ (Xq i j : ℝ))
    (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hX : IsDoublyStochastic X)
    (hmax : ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective
          (explicitRegularizationScale (m + 1) : ℝ)
          (fun i j ↦ (A i j : ℝ)) Y ≤
        regularizedBetheObjective
          (explicitRegularizationScale (m + 1) : ℝ)
          (fun i j ↦ (A i j : ℝ)) X)
    (hgap : regularizedBetheObjective
          (explicitRegularizationScale (m + 1) : ℝ)
          (fun i j ↦ (A i j : ℝ)) X -
        regularizedBetheObjective
          (explicitRegularizationScale (m + 1) : ℝ)
          (fun i j ↦ (A i j : ℝ))
          (fun i j ↦ ((Xq i j : ℚ) : ℝ)) ≤
        (explicitOptimizerGap A : ℝ)) :
    HasApproximateLogKKT (explicitKKTError : ℝ)
      (explicitRegularizationScale (m + 1) : ℝ)
      (fun i j ↦ (A i j : ℝ))
      (fun i j ↦ ((Xq i j : ℚ) : ℝ))
      (fun i ↦ (-directedNegativeGradientLowerMatrix
          (explicitRegularizationScale (m + 1)) A Xq
          (explicitOptimizerPrecision A) i 0 +
        (2 + explicitRegularizationScale (m + 1)) : ℚ))
      (fun j ↦ (-(directedNegativeGradientLowerMatrix
          (explicitRegularizationScale (m + 1)) A Xq
          (explicitOptimizerPrecision A) 0 j -
        directedNegativeGradientLowerMatrix
          (explicitRegularizationScale (m + 1)) A Xq
          (explicitOptimizerPrecision A) 0 0) : ℚ)) := by
  let τq : ℚ := explicitRegularizationScale (m + 1)
  let Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    fun i j ↦ (Xq i j : ℝ)
  let Gq := directedNegativeGradientLowerMatrix τq A Xq
    (explicitOptimizerPrecision A)
  let G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    fun i j ↦ (Gq i j : ℝ)
  have hτ0q : 0 < τq := explicitRegularizationScale_pos (by omega)
  have hτ1q : τq ≤ 1 := explicitRegularizationScale_le_one (by omega)
  have hτ0 : 0 < (τq : ℝ) := Rat.cast_pos.mpr hτ0q
  have hτ1 : (τq : ℝ) ≤ 1 := by exact_mod_cast hτ1q
  have hδq : 0 < explicitOptimizerFloor A := explicitOptimizerFloor_pos A
  have hδ : 0 < (explicitOptimizerFloor A : ℝ) := Rat.cast_pos.mpr hδq
  have hρ : 0 ≤ (explicitOptimizerRho A : ℝ) := by
    exact_mod_cast (explicitOptimizerRho_pos A).le
  have hY' : IsDoublyStochastic Y := by simpa only [Y] using hY
  have hYlo' : ∀ i j, (explicitOptimizerFloor A : ℝ) ≤ Y i j := by
    simpa only [Y] using hYlo
  have hYpos : ∀ i j, 0 < Y i j := by
    intro i j
    exact hδ.trans_le (hYlo' i j)
  have hYcomp : ∀ i j, (explicitOptimizerFloor A : ℝ) ≤ 1 - Y i j := by
    exact one_sub_entry_ge_of_common_floor (by simp; omega) hY' hYlo'
  have hYlt : ∀ i j, Y i j < 1 :=
    hY'.entry_lt_one_of_positive hYpos (by simp; omega)
  let δ0q : ℚ := numericalInteriorFloor (m + 1)
    (rationalMatrixEntryBitBound A) τq
  have hδle : explicitOptimizerFloor A ≤ δ0q := by
    rw [explicitOptimizerFloor]
    have hδ0 : 0 < δ0q := numericalInteriorFloor_pos _ _ _
    dsimp only [δ0q, τq] at hδ0 ⊢
    linarith
  have hoptimizerFloor : ∀ i j,
      (δ0q : ℝ) ≤ X i j ∧ (δ0q : ℝ) ≤ 1 - X i j := by
    exact regularizedOptimizer_meets_executable_floor (n := m + 1)
      (by omega) hτ0q hApos hAupper hX hmax
  have hδleR : (explicitOptimizerFloor A : ℝ) ≤ (δ0q : ℝ) := by
    exact_mod_cast hδle
  have hXlo : ∀ i j, (explicitOptimizerFloor A : ℝ) ≤ X i j := by
    intro i j
    exact hδleR.trans (hoptimizerFloor i j).1
  have hXcomp : ∀ i j, (explicitOptimizerFloor A : ℝ) ≤ 1 - X i j := by
    intro i j
    exact hδleR.trans (hoptimizerFloor i j).2
  have hAposR : Matrix.Positive (fun i j ↦ (A i j : ℝ)) := by
    intro i j
    exact Rat.cast_pos.mpr (hApos i j)
  have hXint : ∀ i, IsInteriorProbabilityVector (X i) :=
    regularizedBetheMaximizer_interior (by omega) hτ0 hAposR hX hmax
  have hXqpos : ∀ i j, 0 < Xq i j := by
    intro i j
    exact Rat.cast_pos.mp (by simpa only [Y] using hYpos i j)
  have hXqlt : ∀ i j, Xq i j < 1 := by
    intro i j
    have hij : (Xq i j : ℝ) < (1 : ℝ) := by
      simpa only [Y] using hYlt i j
    exact_mod_cast hij
  let evaluationError : ℝ :=
    (4 * (1 / 2 : ℚ) ^ explicitOptimizerPrecision A : ℚ)
  have heval : ∀ i j,
      abs (-regularizedBetheGradient (τq : ℝ)
          (fun a b ↦ (A a b : ℝ)) Y i j - G i j) ≤ evaluationError := by
    intro i j
    have hb := directedNegativeGradient_bounds hτ0q.le hτ1q
      (hApos i j) (hXqpos i j) (hXqlt i j)
      (explicitOptimizerPrecision A)
    have hexact :
        negativeRegularizedBetheGradientCoordinate (τq : ℝ)
            (A i j : ℝ) (Xq i j : ℝ) =
          -regularizedBetheGradient (τq : ℝ)
            (fun a b ↦ (A a b : ℝ)) Y i j := by
      rw [negativeRegularizedBetheGradientCoordinate_eq_neg]
      simp only [regularizedBetheGradient, Y]
    have hlower :
        (Gq i j : ℝ) ≤
          -regularizedBetheGradient (τq : ℝ)
            (fun a b ↦ (A a b : ℝ)) Y i j := by
      rw [← hexact]
      simpa only [Gq, directedNegativeGradientLowerMatrix, τq] using hb.1
    have hupper :
        -regularizedBetheGradient (τq : ℝ)
            (fun a b ↦ (A a b : ℝ)) Y i j ≤
          (directedNegativeGradientUpper τq (A i j) (Xq i j)
            (explicitOptimizerPrecision A) : ℝ) := by
      rw [← hexact]
      exact hb.2.1
    have hwidth :
        (directedNegativeGradientUpper τq (A i j) (Xq i j)
              (explicitOptimizerPrecision A) : ℝ) - (Gq i j : ℝ) ≤
          evaluationError := by
      simpa only [Gq, directedNegativeGradientLowerMatrix, τq, evaluationError,
        Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_one,
        Rat.cast_ofNat] using hb.2.2
    change abs (-regularizedBetheGradient (τq : ℝ)
      (fun a b ↦ (A a b : ℝ)) Y i j - (Gq i j : ℝ)) ≤ evaluationError
    rw [abs_of_nonneg (sub_nonneg.mpr hlower)]
    linarith
  have hscale :
      4 * (explicitOptimizerGap A : ℝ) ≤
        (τq : ℝ) * (explicitOptimizerRho A : ℝ) ^ 2 := by
    have hscaleQ := explicitOptimizerGap_scale A
    exact (by exact_mod_cast hscaleQ :
      4 * (explicitOptimizerGap A : ℝ) =
        (τq : ℝ) * (explicitOptimizerRho A : ℝ) ^ 2).le
  have hsmall := approximateLogKKT_of_objective_gap
    (ι := Fin (m + 1)) (by simp; omega)
    hτ0 hτ1 hρ hδ hscale hX hY' hmax
    (by simpa only [τq, Y] using hgap) hXint hXlo hYlo'
    hXcomp hYcomp heval (0 : Fin (m + 1)) (0 : Fin (m + 1))
  have hbudgetQ := explicitOptimizerKKTError_le A
  have hbudget :
      evaluationError + 4 *
          (evaluationError + 3 * (explicitOptimizerRho A : ℝ) /
            (explicitOptimizerFloor A : ℝ)) ≤
        (explicitKKTError : ℝ) := by
    have hbudgetR := (Rat.cast_le (K := ℝ)).mpr hbudgetQ
    norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
      Rat.cast_one, Rat.cast_ofNat] at hbudgetR
    dsimp only [evaluationError]
    norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_one,
      Rat.cast_ofNat]
    exact hbudgetR
  have hlarge := hsmall.mono hbudget
  simpa only [τq, Y, Gq, G, evaluationError,
    anchoredRowPotential,
    anchoredColumnPotential, Rat.cast_neg, Rat.cast_add, Rat.cast_sub,
    Rat.cast_ofNat] using hlarge

/-- The concrete rational matrix and anchored rational potentials satisfy the
fixed approximate logarithmic KKT equations. -/
theorem explicitBetheOptimizer_hasApproximateLogKKT {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1) :
    HasApproximateLogKKT (explicitKKTError : ℝ)
      (explicitRegularizationScale (m + 1) : ℝ)
      (fun i j ↦ (A i j : ℝ))
      (fun i j ↦ ((explicitBetheOptimizerMatrix A i j : ℚ) : ℝ))
      (fun i ↦ (explicitBetheOptimizerRowPotential A i : ℝ))
      (fun j ↦ (explicitBetheOptimizerColumnPotential A j : ℝ)) := by
  obtain ⟨_, hY, hYlo, X, hX, hmax, hgap⟩ :=
    explicitBetheOptimizerPoint_spec hm A hApos hAupper
  simpa only [explicitBetheOptimizerGradient,
    explicitBetheOptimizerRowPotential,
    explicitBetheOptimizerColumnPotential] using
    hasApproximateLogKKT_of_explicitOptimizerSpec hm A hApos hAupper
      (explicitBetheOptimizerMatrix A) hY hYlo X hX hmax hgap

end BeyondBethe

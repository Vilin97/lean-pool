/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.BetheEpigraph
import Mathlib.Tactic

/-! # Bethe Epigraph Feasibility -/

open scoped BigOperators

namespace BeyondBethe

/-!
# A complete executable oracle for the bounded Bethe epigraph

The oracle first enforces every entry floor exactly, then the rational height
cap, and only then invokes the directed elementary-function oracle.  This
ordering makes every logarithm query legal and leaves no domain condition as
an oracle hypothesis.
-/

/-- Normal of the upper bound on the last, epigraph-height coordinate. -/
def epigraphUpperNormal (d : ℕ) : Fin (d + 1) → ℚ :=
  Fin.snoc 0 1

theorem epigraphUpperNormal_ne_zero (d : ℕ) :
    epigraphUpperNormal d ≠ 0 := by
  intro hzero
  have h := congrFun hzero (Fin.last d)
  norm_num [epigraphUpperNormal] at h

theorem epigraphUpperNormal_dot_displacement {d : ℕ}
    (z : Fin (d + 1) → ℝ) (q : Fin (d + 1) → ℚ) :
    finiteDot (fun k ↦ (epigraphUpperNormal d k : ℝ))
        (fun k ↦ z k - (q k : ℝ)) =
      epigraphHeight z - (epigraphHeight q : ℚ) := by
  rw [finiteDot, Fin.sum_univ_castSucc]
  simp [epigraphUpperNormal, epigraphHeight]

/-- Complete rational oracle for a height-bounded, floor-truncated Bethe
epigraph. -/
def betheBoundedEpigraphOracle {m : ℕ}
    (τ : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (δ upper : ℚ) : RationalCentralOracle (m * m + 1) :=
  fun E ↦
    match firstBetheFloorViolationAll δ (epigraphBase E.center) with
    | some ij => .cut (betheFloorCutNormal ij.1 ij.2)
    | none =>
        if upper < epigraphHeight E.center then
          .cut (epigraphUpperNormal (m * m))
        else
          directedEpigraphOracle
            (betheDirectedEpigraphData τ A p)
            (16 * (1 / 2 : ℚ) ^ p) (m * m) E

/-- Exact rational facts obtained whenever the complete oracle accepts. -/
def BetheEpigraphOracleAccepted {m : ℕ}
    (τ : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (δ upper : ℚ) (q : Fin (m * m + 1) → ℚ) : Prop :=
  (∀ i j, δ ≤ betheAffineMatrixQ (epigraphBase q) i j) ∧
    epigraphHeight q ≤ upper ∧
    (betheDirectedEpigraphData τ A p).lower (epigraphBase q) ≤
      epigraphHeight q + (16 * (1 / 2 : ℚ) ^ p) * (m * m)

/-- Full rational objective-evaluation loss charged on acceptance. -/
def betheObjectiveEvaluationError (m p : ℕ) : ℚ :=
  16 * (1 / 2 : ℚ) ^ p * (m * m) +
    3 * (m + 1) ^ 2 * (1 / 2 : ℚ) ^ p

theorem betheObjectiveEvaluationError_nonneg (m p : ℕ) :
    0 ≤ betheObjectiveEvaluationError m p := by
  rw [betheObjectiveEvaluationError]
  positivity

/-- Real matrix encoded by the base coordinates of an accepted epigraph
point. -/
def acceptedBetheMatrix {m : ℕ} (q : Fin (m * m + 1) → ℚ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  birkhoffAffineMap
    (vectorToSquareMatrix (fun k ↦ ((epigraphBase q k : ℚ) : ℝ)))

/-- The exact floor tests and affine recovery identities make every accepted
matrix doubly stochastic. -/
theorem BetheEpigraphOracleAccepted_doublyStochastic {m : ℕ}
    {τ : ℚ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    {p : ℕ} {δ upper : ℚ} (hδ : 0 ≤ δ)
    {q : Fin (m * m + 1) → ℚ}
    (haccepted : BetheEpigraphOracleAccepted τ A p δ upper q) :
    IsDoublyStochastic (acceptedBetheMatrix q) := by
  refine ⟨?_, birkhoffAffineMap_row_sum _, birkhoffAffineMap_col_sum _⟩
  intro i j
  have hfloorQ := haccepted.1 i j
  have hfloor : (δ : ℝ) ≤ acceptedBetheMatrix q i j := by
    change (δ : ℝ) ≤ birkhoffAffineMap
      (vectorToSquareMatrix (fun k ↦ ((epigraphBase q k : ℚ) : ℝ))) i j
    rw [← cast_betheAffineMatrixQ (epigraphBase q) i j]
    exact_mod_cast hfloorQ
  exact (Rat.cast_nonneg.mpr hδ).trans hfloor

theorem BetheEpigraphOracleAccepted_entry_floor {m : ℕ}
    {τ : ℚ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    {p : ℕ} {δ upper : ℚ}
    {q : Fin (m * m + 1) → ℚ}
    (haccepted : BetheEpigraphOracleAccepted τ A p δ upper q) :
    ∀ i j, (δ : ℝ) ≤ acceptedBetheMatrix q i j := by
  intro i j
  change (δ : ℝ) ≤ birkhoffAffineMap
    (vectorToSquareMatrix (fun k ↦ ((epigraphBase q k : ℚ) : ℝ))) i j
  rw [← cast_betheAffineMatrixQ (epigraphBase q) i j]
  exact_mod_cast haccepted.1 i j

/-- Every cut returned by the complete executable oracle is valid for the
exact bounded epigraph. -/
theorem betheBoundedEpigraphOracle_valid {m : ℕ} (hm : 0 < m)
    {τ : ℚ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hA : ∀ i j, 0 < A i j)
    {δ : ℚ} (hδ : 0 < δ) (p : ℕ) (upper : ℚ) :
    RationalCentralOracleValid
      (BetheEpigraphTarget (τ : ℝ) (fun i j ↦ (A i j : ℝ))
        (δ : ℝ) (upper : ℝ))
      (betheBoundedEpigraphOracle τ A p δ upper) := by
  intro E a hresponse
  rw [betheBoundedEpigraphOracle] at hresponse
  split at hresponse <;> rename_i hfloorScan
  · rename_i ij
    cases hresponse
    refine ⟨betheFloorCutNormal_ne_zero hm ij.1 ij.2, ?_⟩
    intro z hz
    have hbelow : betheAffineMatrixQ (epigraphBase E.center)
        ij.1 ij.2 < δ := by
      apply firstBetheFloorViolation_is_below
      simpa only [firstBetheFloorViolationAll] using! hfloorScan
    have htargetFloor : (δ : ℝ) ≤
        birkhoffAffineMap
          (vectorToSquareMatrix (epigraphBase z)) ij.1 ij.2 := by
      simpa only [BetheEpigraphTarget] using! hz.1 ij.1 ij.2
    have hcut := betheFloorCut_valid hbelow htargetFloor
    rw [finiteDot, Fin.sum_univ_castSucc] at hcut ⊢
    simpa [rationalCenterReal, epigraphBase] using! hcut.le
  · split at hresponse <;> rename_i hheight
    · cases hresponse
      refine ⟨epigraphUpperNormal_ne_zero (m * m), ?_⟩
      intro z hz
      have hdot := epigraphUpperNormal_dot_displacement z E.center
      rw [show finiteDot
          (fun i ↦ (epigraphUpperNormal (m * m) i : ℝ))
          (fun i ↦ z i - rationalCenterReal E i) =
          epigraphHeight z - (epigraphHeight E.center : ℚ) by
        simpa only [rationalCenterReal] using! hdot]
      have hzUpper : epigraphHeight z ≤ (upper : ℝ) := by
        simpa only [BetheEpigraphTarget] using! hz.2.2
      have hheightReal : (upper : ℝ) <
          ((epigraphHeight E.center : ℚ) : ℝ) := by
        exact_mod_cast hheight
      linarith
    · have hqueryFloor : ∀ i j, δ ≤
          betheAffineMatrixQ (epigraphBase E.center) i j :=
        (firstBetheFloorViolationAll_eq_none_iff δ
          (epigraphBase E.center)).mp hfloorScan
      refine ⟨directedEpigraphOracle_cut_ne_zero
        (betheDirectedEpigraphData τ A p)
        (16 * (1 / 2 : ℚ) ^ p) (m * m) E hresponse, ?_⟩
      intro z hz
      exact (betheDirectedEpigraphOracle_cut_valid hm hτ0 hτ1 hA hδ
        (upper := (upper : ℝ)) p E hqueryFloor hresponse hz).2.le

/-- Acceptance of the complete oracle certifies every rational test in its
three branches. -/
theorem betheBoundedEpigraphOracle_acceptsOnly {m : ℕ}
    (τ : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (δ upper : ℚ) :
    RationalCentralOracleAcceptsOnly
      (BetheEpigraphOracleAccepted τ A p δ upper)
      (betheBoundedEpigraphOracle τ A p δ upper) := by
  intro E hresponse
  rw [betheBoundedEpigraphOracle] at hresponse
  split at hresponse <;> rename_i hfloorScan
  · contradiction
  · split at hresponse <;> rename_i hheight
    · contradiction
    · rw [directedEpigraphOracle] at hresponse
      split at hresponse <;> rename_i hnonlinear
      · contradiction
      · cases hresponse
        refine ⟨
          (firstBetheFloorViolationAll_eq_none_iff δ
            (epigraphBase E.center)).mp hfloorScan,
          not_lt.mp hheight, ?_⟩
        exact not_lt.mp hnonlinear

/-- Acceptance controls the exact negative objective, not merely its directed
lower endpoint.  The first error term is the safety margin in the nonlinear
cut test; the second is the full width of the directed objective interval.
Keeping both terms explicit prevents a one-sided-evaluation gap in the weak
optimization proof. -/
theorem BetheEpigraphOracleAccepted_exact_objective_upper {m : ℕ}
    (hm : 0 < m) {τ : ℚ}
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hA : ∀ i j, 0 < A i j)
    {p : ℕ} {δ upper : ℚ} (hδ : 0 < δ)
    {q : Fin (m * m + 1) → ℚ}
    (haccepted : BetheEpigraphOracleAccepted τ A p δ upper q) :
    affineNegativeObjective (τ : ℝ) (fun i j ↦ (A i j : ℝ))
        (vectorToSquareMatrix
          (fun k ↦ ((epigraphBase q k : ℚ) : ℝ))) ≤
      ((epigraphHeight q : ℚ) : ℝ) +
        ((16 * (1 / 2 : ℚ) ^ p * (m * m) : ℚ) : ℝ) +
        3 * ((m + 1 : ℕ) : ℝ) ^ 2 *
      (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by
  let y : Fin (m * m) → ℚ := epigraphBase q
  let Xq : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ :=
    betheAffineMatrixQ y
  have hfloor : ∀ i j, δ ≤ Xq i j := by
    simpa only [Xq, y] using! haccepted.1
  have hX0 : ∀ i j, 0 < Xq i j := fun i j ↦
    hδ.trans_le (hfloor i j)
  have hinterior := birkhoffAffineMap_interior hm hδ
    (Y := vectorToSquareMatrix y) (by
      simpa only [Xq, betheAffineMatrixQ] using! hfloor)
  have hX1 : ∀ i j, Xq i j < 1 := by
    intro i j
    have h := (hinterior.2 i).2 j |>.2
    change ((Xq i j : ℚ) : ℝ) < 1 at h
    exact_mod_cast h
  have hbounds := directedNegativeObjective_bounds hτ0 hτ1 hA hX0 hX1 p
  have hlowerAcceptedQ :
      directedNegativeObjectiveLower τ A Xq p ≤
        epigraphHeight q + 16 * (1 / 2 : ℚ) ^ p * (m * m) := by
    simpa only [BetheEpigraphOracleAccepted,
      betheDirectedEpigraphData, Xq, y] using! haccepted.2.2
  have hlowerAccepted :
      (directedNegativeObjectiveLower τ A Xq p : ℝ) ≤
        ((epigraphHeight q : ℚ) : ℝ) +
          ((16 * (1 / 2 : ℚ) ^ p * (m * m) : ℚ) : ℝ) := by
    exact_mod_cast hlowerAcceptedQ
  have hcast :
      birkhoffAffineMap
          (vectorToSquareMatrix
            (fun k ↦ ((epigraphBase q k : ℚ) : ℝ))) =
        fun i j ↦ ((Xq i j : ℚ) : ℝ) := by
    ext i j
    symm
    simpa only [Xq, y] using! cast_betheAffineMatrixQ y i j
  unfold affineNegativeObjective
  rw [hcast]
  linarith [hbounds.2.1, hbounds.2.2]

theorem BetheEpigraphOracleAccepted_exact_objective_upper_compact {m : ℕ}
    (hm : 0 < m) {τ : ℚ}
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hA : ∀ i j, 0 < A i j)
    {p : ℕ} {δ upper : ℚ} (hδ : 0 < δ)
    {q : Fin (m * m + 1) → ℚ}
    (haccepted : BetheEpigraphOracleAccepted τ A p δ upper q) :
    affineNegativeObjective (τ : ℝ) (fun i j ↦ (A i j : ℝ))
        (vectorToSquareMatrix
          (fun k ↦ ((epigraphBase q k : ℚ) : ℝ))) ≤
      ((epigraphHeight q : ℚ) : ℝ) +
        (betheObjectiveEvaluationError m p : ℝ) := by
  have h := BetheEpigraphOracleAccepted_exact_objective_upper
    hm hτ0 hτ1 hA hδ haccepted
  rw [betheObjectiveEvaluationError]
  norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast, Nat.cast_add,
    Nat.cast_one, Nat.cast_mul, Nat.cast_pow] at h ⊢
  linarith

end BeyondBethe

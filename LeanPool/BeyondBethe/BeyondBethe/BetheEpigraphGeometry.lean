/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.BetheEpigraphFeasibility
import LeanPool.BeyondBethe.BeyondBethe.ExecutableInterior
import LeanPool.BeyondBethe.BeyondBethe.ApproximateKKT
import Mathlib.Tactic

/-! # Bethe Epigraph Geometry -/

open scoped BigOperators

namespace BeyondBethe

/-!
# Explicit geometry of the truncated Bethe epigraph

This file supplies the quantitative geometry needed by the rational
ellipsoid routine.  In particular, it records an ordinary binary-input range
bound and exact formulas for one-coordinate perturbations in the flattened
Birkhoff affine coordinates.
-/

/-- A polynomially encoded global range for the regularized objective on the
Birkhoff polytope of a normalized positive rational matrix. -/
def rationalRegularizedObjectiveRange {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) : ℚ :=
  n * rationalMatrixEntryBitBound A + 3 * n ^ 2

theorem rationalRegularizedObjectiveRange_nonneg {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    0 ≤ rationalRegularizedObjectiveRange A := by
  rw [rationalRegularizedObjectiveRange]
  positivity

/-- The displayed rational range bounds the difference between the objective
at any two doubly stochastic matrices. -/
theorem regularizedBetheObjective_sub_le_rationalRange
    {n : ℕ} (hn : 1 ≤ n) {τ : ℚ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    {A : Matrix (Fin n) (Fin n) ℚ}
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1)
    {X Z : Matrix (Fin n) (Fin n) ℝ}
    (hX : IsDoublyStochastic X) (hZ : IsDoublyStochastic Z) :
    regularizedBetheObjective (τ : ℝ) (fun i j ↦ (A i j : ℝ)) X -
        regularizedBetheObjective (τ : ℝ) (fun i j ↦ (A i j : ℝ)) Z ≤
      (rationalRegularizedObjectiveRange A : ℝ) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  let B := rationalMatrixEntryBitBound A
  let m : ℚ := (1 / 2 : ℚ) ^ B
  have hmQ : 0 < m := by positivity
  have hm : 0 < (m : ℝ) := Rat.cast_pos.mpr hmQ
  have hAlower : ∀ i j, (m : ℝ) ≤ (A i j : ℝ) := by
    intro i j
    exact_mod_cast (matrix_dyadic_bitBound_lt_entry hApos i j).le
  have hAposR : Matrix.Positive (fun i j ↦ (A i j : ℝ)) := by
    intro i j
    exact Rat.cast_pos.mpr (hApos i j)
  have hAupperR : ∀ i j, (A i j : ℝ) ≤ 1 := by
    intro i j
    exact_mod_cast hAupper i j
  have hentropyX0 := totalRowEntropy_nonneg hX
  have hentropyZ0 := totalRowEntropy_nonneg hZ
  have hentropyX := totalRowEntropy_le hX
  have hlogn : Real.log n ≤ (n : ℝ) := by
    have hlog := log_natCast_le_natCast_mul_log_two hn
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
      norm_num at h
      exact h
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  have hentropyX' : totalRowEntropy X ≤ (n : ℝ) ^ 2 := by
    simp only [Fintype.card_fin] at hentropyX
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  have hbetheUpper := betheObjective_le_totalRowEntropy
    hAposR hAupperR hX
  have hbetheLower := betheObjective_lower_of_entry_lower hm hAlower hZ
  simp only [Fintype.card_fin] at hbetheLower
  have hτ0R : 0 ≤ (τ : ℝ) := Rat.cast_nonneg.mpr hτ0
  have hτ1R : (τ : ℝ) ≤ 1 := by exact_mod_cast hτ1
  have hregUpper :
      regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) X ≤ 2 * (n : ℝ) ^ 2 := by
    unfold regularizedBetheObjective
    have hτEntropy : (τ : ℝ) * totalRowEntropy X ≤ totalRowEntropy X :=
      mul_le_of_le_one_left hentropyX0 hτ1R
    linarith
  have hregLower :
      (n : ℝ) * Real.log (m : ℝ) - n ≤
        regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) Z := by
    unfold regularizedBetheObjective
    have hτEntropy : 0 ≤ (τ : ℝ) * totalRowEntropy Z :=
      mul_nonneg hτ0R hentropyZ0
    linarith
  have hlogm : Real.log (m : ℝ) = -(B : ℝ) * Real.log 2 := by
    simp only [m, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    rw [Real.log_pow]
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    ring
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h
    exact h
  have hB0 : 0 ≤ (B : ℝ) := by positivity
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [rationalRegularizedObjectiveRange]
  push_cast
  rw [hlogm] at hregLower
  nlinarith [mul_le_mul_of_nonneg_left hlog2 hB0]

/-- Explicit absolute bounds on the negative regularized objective.  These
give rational endpoints for bisection without evaluating a logarithm. -/
theorem negativeRegularizedBetheObjective_rational_bounds
    {n : ℕ} (hn : 1 ≤ n) {τ : ℚ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    {A : Matrix (Fin n) (Fin n) ℚ}
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1)
    {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : IsDoublyStochastic X) :
    ((-(2 * n ^ 2 : ℚ) : ℚ) : ℝ) ≤
        -regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) X ∧
      -regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) X ≤
        ((n * rationalMatrixEntryBitBound A + n : ℕ) : ℝ) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  let B := rationalMatrixEntryBitBound A
  let a : ℚ := (1 / 2 : ℚ) ^ B
  have haQ : 0 < a := by positivity
  have ha : 0 < (a : ℝ) := Rat.cast_pos.mpr haQ
  have hAlower : ∀ i j, (a : ℝ) ≤ (A i j : ℝ) := by
    intro i j
    exact_mod_cast (matrix_dyadic_bitBound_lt_entry hApos i j).le
  have hAposR : Matrix.Positive (fun i j ↦ (A i j : ℝ)) := by
    intro i j
    exact Rat.cast_pos.mpr (hApos i j)
  have hAupperR : ∀ i j, (A i j : ℝ) ≤ 1 := by
    intro i j
    exact_mod_cast hAupper i j
  have hentropy0 := totalRowEntropy_nonneg hX
  have hentropy := totalRowEntropy_le hX
  have hlogn : Real.log n ≤ (n : ℝ) := by
    have hlog := log_natCast_le_natCast_mul_log_two hn
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
      norm_num at h
      exact h
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  have hentropy' : totalRowEntropy X ≤ (n : ℝ) ^ 2 := by
    simp only [Fintype.card_fin] at hentropy
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  have hbetheUpper := betheObjective_le_totalRowEntropy
    hAposR hAupperR hX
  have hbetheLower := betheObjective_lower_of_entry_lower ha hAlower hX
  simp only [Fintype.card_fin] at hbetheLower
  have hτ0R : 0 ≤ (τ : ℝ) := Rat.cast_nonneg.mpr hτ0
  have hτ1R : (τ : ℝ) ≤ 1 := by exact_mod_cast hτ1
  have hregUpper :
      regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) X ≤ 2 * (n : ℝ) ^ 2 := by
    unfold regularizedBetheObjective
    have hτEntropy : (τ : ℝ) * totalRowEntropy X ≤ totalRowEntropy X :=
      mul_le_of_le_one_left hentropy0 hτ1R
    linarith
  have hregLower :
      (n : ℝ) * Real.log (a : ℝ) - n ≤
        regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) X := by
    unfold regularizedBetheObjective
    have hτEntropy : 0 ≤ (τ : ℝ) * totalRowEntropy X :=
      mul_nonneg hτ0R hentropy0
    linarith
  have hloga : Real.log (a : ℝ) = -(B : ℝ) * Real.log 2 := by
    simp only [a, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    rw [Real.log_pow]
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    ring
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h
    exact h
  have hB0 : 0 ≤ (B : ℝ) := by positivity
  rw [hloga] at hregLower
  constructor
  · push_cast
    linarith
  · push_cast
    nlinarith [mul_le_mul_of_nonneg_left hlog2 hB0]

/-- A vector with a single nonzero coordinate. -/
def coordinateSpike {d : ℕ} {R : Type*} [Zero R]
    (k : Fin d) (r : R) : Fin d → R :=
  fun i ↦ if i = k then r else 0

@[simp] theorem coordinateSpike_apply_self {d : ℕ} {R : Type*} [Zero R]
    (k : Fin d) (r : R) : coordinateSpike k r k = r := by
  simp [coordinateSpike]

theorem vectorL1_coordinateSpike {d : ℕ} (k : Fin d) (r : ℝ) :
    vectorL1 (coordinateSpike k r) = abs r := by
  classical
  rw [vectorL1, Finset.sum_eq_single k]
  · simp [coordinateSpike]
  · intro b _ hbk
    simp [coordinateSpike, hbk]
  · simp

/-- Package a base vector and a height into one epigraph point. -/
def epigraphPoint {d : ℕ} {R : Type*}
    (y : Fin d → R) (s : R) : Fin (d + 1) → R :=
  Fin.snoc y s

@[simp] theorem epigraphBase_epigraphPoint {d : ℕ} {R : Type*}
    (y : Fin d → R) (s : R) : epigraphBase (epigraphPoint y s) = y := by
  ext i
  simp [epigraphBase, epigraphPoint]

@[simp] theorem epigraphHeight_epigraphPoint {d : ℕ} {R : Type*}
    (y : Fin d → R) (s : R) : epigraphHeight (epigraphPoint y s) = s := by
  simp [epigraphHeight, epigraphPoint]

/-- Adding one flattened-coordinate spike changes the recovered full matrix
by at most the spike magnitude in every entry. -/
theorem birkhoffAffineMap_vector_spike_abs_sub_le
    {m : ℕ} (y : Fin (m * m) → ℝ) (k : Fin (m * m)) (r : ℝ)
    (i j : Fin (m + 1)) :
    abs (birkhoffAffineMap
          (vectorToSquareMatrix (fun l ↦ y l + coordinateSpike k r l)) i j -
        birkhoffAffineMap (vectorToSquareMatrix y) i j) ≤ abs r := by
  have hmap := birkhoffAffineMap_abs_sub_le_l1
    (vectorToSquareMatrix (fun l ↦ y l + coordinateSpike k r l))
    (vectorToSquareMatrix y) i j
  apply hmap.trans_eq
  change matrixL1
      (fun i j ↦
        vectorToSquareMatrix (fun l ↦ y l + coordinateSpike k r l) i j -
          vectorToSquareMatrix y i j) = abs r
  rw [← vectorL1_squareMatrixToVector
    (fun i j ↦
      vectorToSquareMatrix (fun l ↦ y l + coordinateSpike k r l) i j -
        vectorToSquareMatrix y i j)]
  have hvec : squareMatrixToVector
      (fun i j ↦
        vectorToSquareMatrix (fun l ↦ y l + coordinateSpike k r l) i j -
          vectorToSquareMatrix y i j) = coordinateSpike k r := by
    ext l
    change (y (finProdFinEquiv (finProdFinEquiv.symm l)) +
        coordinateSpike k r (finProdFinEquiv (finProdFinEquiv.symm l))) -
      y (finProdFinEquiv (finProdFinEquiv.symm l)) = coordinateSpike k r l
    rw [Equiv.apply_symm_apply]
    ring
  rw [hvec, vectorL1_coordinateSpike]

/-- Real upper-left coordinates of the Birkhoff barycenter. -/
noncomputable def uniformAffineCoordinatesReal (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun _ _ ↦ 1 / (m + 1)

@[simp] theorem birkhoffAffineMap_uniformAffineCoordinatesReal
    (m : ℕ) (i j : Fin (m + 1)) :
    birkhoffAffineMap (uniformAffineCoordinatesReal m) i j = 1 / (m + 1) := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;>
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · simp [uniformAffineCoordinatesReal]
    field_simp
    ring
  · simp [uniformAffineCoordinatesReal]
    field_simp
    ring
  · simp [uniformAffineCoordinatesReal]
    field_simp
    ring
  · simp [uniformAffineCoordinatesReal]

/-- A one-coordinate affine perturbation of the barycenter remains doubly
stochastic as long as its magnitude is at most the uniform entry. -/
theorem uniformAffineSpike_doublyStochastic
    {m : ℕ} (hm : 0 < m) (k : Fin (m * m)) {q : ℝ}
    (hq : abs q ≤ 1 / (m + 1 : ℝ)) :
    IsDoublyStochastic
      (birkhoffAffineMap
        (vectorToSquareMatrix
          (fun l ↦ squareMatrixToVector (uniformAffineCoordinatesReal m) l +
            coordinateSpike k q l))) := by
  let Zbase := vectorToSquareMatrix
    (fun l ↦ squareMatrixToVector (uniformAffineCoordinatesReal m) l +
      coordinateSpike k q l)
  have hu : 0 < 1 / (m + 1 : ℝ) := by positivity
  have hnonneg : Matrix.Nonnegative (birkhoffAffineMap Zbase) := by
    intro i j
    have hclose := birkhoffAffineMap_vector_spike_abs_sub_le
      (squareMatrixToVector (uniformAffineCoordinatesReal m)) k q i j
    rw [vectorToSquareMatrix_squareMatrixToVector,
      birkhoffAffineMap_uniformAffineCoordinatesReal] at hclose
    have hlower := (abs_le.mp hclose).1
    dsimp only [Zbase]
    linarith
  exact ⟨hnonneg, birkhoffAffineMap_row_sum Zbase,
    birkhoffAffineMap_col_sum Zbase⟩

/-- Mixing an exact feasible point with a perturbed barycenter supplies all
three facts needed for the epigraph geometry: feasibility, a quantitative
entry floor, and an objective upper bound obtained from concavity and the
global range. -/
theorem smoothedUniformSpike_properties
    {m : ℕ} (hm : 0 < m) {τ : ℚ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1)
    {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hX : IsDoublyStochastic X) {δ0 : ℝ}
    (hXfloor : ∀ i j, δ0 ≤ X i j)
    {mix : ℝ} (hmix0 : 0 ≤ mix) (hmix1 : mix ≤ 1)
    (k : Fin (m * m)) {q : ℝ}
    (hq : abs q ≤ 1 / (m + 1 : ℝ)) :
    let Zbase := vectorToSquareMatrix
      (fun l ↦ squareMatrixToVector (uniformAffineCoordinatesReal m) l +
        coordinateSpike k q l)
    let Ybase := fun i j ↦
      (1 - mix) * birkhoffAffineCoordinates X i j + mix * Zbase i j
    IsDoublyStochastic (birkhoffAffineMap Ybase) ∧
      (∀ i j, (1 - mix) * δ0 ≤ birkhoffAffineMap Ybase i j) ∧
      affineNegativeObjective (τ : ℝ) (fun i j ↦ (A i j : ℝ)) Ybase ≤
        -regularizedBetheObjective (τ : ℝ)
            (fun i j ↦ (A i j : ℝ)) X +
          mix * (rationalRegularizedObjectiveRange A : ℝ) := by
  let Zbase := vectorToSquareMatrix
    (fun l ↦ squareMatrixToVector (uniformAffineCoordinatesReal m) l +
      coordinateSpike k q l)
  let Ybase := fun i j ↦
    (1 - mix) * birkhoffAffineCoordinates X i j + mix * Zbase i j
  have hZ : IsDoublyStochastic (birkhoffAffineMap Zbase) := by
    simpa only [Zbase] using! uniformAffineSpike_doublyStochastic hm k hq
  have hrecover : birkhoffAffineMap (birkhoffAffineCoordinates X) = X :=
    birkhoffAffineMap_coordinates_of_unit_sums X hX.row_sum hX.col_sum
  have hmap : birkhoffAffineMap Ybase =
      matrixSegment mix X (birkhoffAffineMap Zbase) := by
    rw [show Ybase = fun i j ↦
        (1 - mix) * birkhoffAffineCoordinates X i j + mix * Zbase i j by rfl,
      birkhoffAffineMap_affineCombination, hrecover]
    rfl
  have hmixDS := matrixSegment_doublyStochastic hmix0 hmix1 hX hZ
  have hfloor : ∀ i j,
      (1 - mix) * δ0 ≤ birkhoffAffineMap Ybase i j := by
    intro i j
    rw [hmap]
    dsimp only [matrixSegment]
    have hweight0 : 0 ≤ 1 - mix := sub_nonneg.mpr hmix1
    have hleft := mul_le_mul_of_nonneg_left (hXfloor i j) hweight0
    have hright : 0 ≤ mix * birkhoffAffineMap Zbase i j :=
      mul_nonneg hmix0 (hZ.nonnegative i j)
    linarith
  have hconc := regularizedBetheObjective_segment_lower
    (show 1 < Fintype.card (Fin (m + 1)) by simp; omega)
    (Rat.cast_nonneg.mpr hτ0) hmix0 hmix1
    (fun i j ↦ (A i j : ℝ)) hX hZ
  have hrange := regularizedBetheObjective_sub_le_rationalRange
    (show 1 ≤ m + 1 by omega) hτ0 hτ1 hApos hAupper hX hZ
  refine ⟨by rwa [hmap], hfloor, ?_⟩
  unfold affineNegativeObjective
  rw [hmap]
  nlinarith

/-- The unperturbed affine-coordinate center obtained by mixing `X` with the
Birkhoff barycenter. -/
noncomputable def smoothedUniformAffineBase {m : ℕ}
    (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (mix : ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j ↦ (1 - mix) * birkhoffAffineCoordinates X i j +
    mix * uniformAffineCoordinatesReal m i j

/-- Multiplying a barycenter spike by the mixing weight produces exactly the
corresponding spike in the flattened mixed coordinates. -/
theorem squareMatrixToVector_smoothedUniformSpike_of_mul
    {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (mix : ℝ) (k : Fin (m * m)) (q r : ℝ) (hqr : mix * q = r) :
    let Zbase := vectorToSquareMatrix
      (fun l ↦ squareMatrixToVector (uniformAffineCoordinatesReal m) l +
        coordinateSpike k q l)
    let Ybase := fun i j ↦
      (1 - mix) * birkhoffAffineCoordinates X i j + mix * Zbase i j
    squareMatrixToVector Ybase =
      fun l ↦ squareMatrixToVector (smoothedUniformAffineBase X mix) l +
        coordinateSpike k r l := by
  dsimp only
  ext l
  simp only [squareMatrixToVector, vectorToSquareMatrix]
  rw [show ((finProdFinEquiv.symm l).1,
      (finProdFinEquiv.symm l).2) = finProdFinEquiv.symm l by rfl,
    Equiv.apply_symm_apply]
  have hspike : mix * coordinateSpike k q l = coordinateSpike k r l := by
    by_cases hlk : l = k
    · subst l
      simp only [coordinateSpike_apply_self]
      exact hqr
    · simp [coordinateSpike, hlk]
  simp only [smoothedUniformAffineBase]
  rw [mul_add, hspike]
  ring

/-- A base-coordinate spike leaves the epigraph height unchanged. -/
theorem epigraphPoint_add_baseSpike {d : ℕ}
    (y : Fin d → ℝ) (s : ℝ) (k : Fin d) (r : ℝ) :
    (fun i ↦ epigraphPoint y s i +
      if i = k.castSucc then r else 0) =
      epigraphPoint (fun l ↦ y l + coordinateSpike k r l) s := by
  ext i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;>
    simp [epigraphPoint, coordinateSpike, k.castSucc_ne_last,
      Ne.symm k.castSucc_ne_last]

/-- A negative base-coordinate spike leaves the epigraph height unchanged. -/
theorem epigraphPoint_sub_baseSpike {d : ℕ}
    (y : Fin d → ℝ) (s : ℝ) (k : Fin d) (r : ℝ) :
    (fun i ↦ epigraphPoint y s i -
      if i = k.castSucc then r else 0) =
      epigraphPoint (fun l ↦ y l - coordinateSpike k r l) s := by
  ext i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;>
    simp [epigraphPoint, coordinateSpike, k.castSucc_ne_last,
      Ne.symm k.castSucc_ne_last]

/-- A spike in the last coordinate changes only the epigraph height. -/
theorem epigraphPoint_add_heightSpike {d : ℕ}
    (y : Fin d → ℝ) (s r : ℝ) :
    (fun i ↦ epigraphPoint y s i +
      if i = Fin.last d then r else 0) = epigraphPoint y (s + r) := by
  ext i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> simp [epigraphPoint]

/-- A negative spike in the last coordinate changes only the epigraph
height. -/
theorem epigraphPoint_sub_heightSpike {d : ℕ}
    (y : Fin d → ℝ) (s r : ℝ) :
    (fun i ↦ epigraphPoint y s i -
      if i = Fin.last d then r else 0) = epigraphPoint y (s - r) := by
  ext i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> simp [epigraphPoint]

/-- Convert the three smoothing conclusions into membership in a bounded
Bethe epigraph at an arbitrary admissible height. -/
theorem smoothedUniformSpike_mem_epigraph
    {m : ℕ} (hm : 0 < m) {τ : ℚ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1)
    {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hX : IsDoublyStochastic X) {δ0 : ℝ}
    (hXfloor : ∀ i j, δ0 ≤ X i j)
    {mix : ℝ} (hmix0 : 0 ≤ mix) (hmix1 : mix ≤ 1)
    (k : Fin (m * m)) {q : ℝ}
    (hq : abs q ≤ 1 / (m + 1 : ℝ))
    {δ s upper : ℝ} (hδ : δ ≤ (1 - mix) * δ0)
    (hobjective :
      -regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) X +
        mix * (rationalRegularizedObjectiveRange A : ℝ) ≤ s)
    (hsupper : s ≤ upper) :
    let Zbase := vectorToSquareMatrix
      (fun l ↦ squareMatrixToVector (uniformAffineCoordinatesReal m) l +
        coordinateSpike k q l)
    let Ybase := fun i j ↦
      (1 - mix) * birkhoffAffineCoordinates X i j + mix * Zbase i j
    BetheEpigraphTarget (τ : ℝ) (fun i j ↦ (A i j : ℝ)) δ upper
      (epigraphPoint (squareMatrixToVector Ybase) s) := by
  dsimp only
  have hproperties := smoothedUniformSpike_properties hm hτ0 hτ1
    hApos hAupper hX hXfloor hmix0 hmix1 k hq
  simp only [BetheEpigraphTarget, epigraphBase_epigraphPoint,
    epigraphHeight_epigraphPoint,
    vectorToSquareMatrix_squareMatrixToVector]
  constructor
  · intro i j
    convert! hδ.trans (hproperties.2.1 i j) using 1
    exact congrArg (fun B : Matrix (Fin m) (Fin m) ℝ => birkhoffAffineMap B i j)
      (vectorToSquareMatrix_squareMatrixToVector _)
  · constructor
    · convert! hproperties.2.2.trans hobjective using 1
      exact congrArg (affineNegativeObjective (τ : ℝ) (fun i j ↦ (A i j : ℝ)))
        (vectorToSquareMatrix_squareMatrixToVector _)
    · exact hsupper

/-- The truncated epigraph above a threshold with two radii of objective
slack contains a full coordinate cross.  This is the exact inner-region
statement used by the square-root-free ellipsoid termination theorem. -/
theorem BetheEpigraphTarget_smoothed_inner_cross
    {m : ℕ} (hm : 0 < m) {τ : ℚ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1)
    {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hX : IsDoublyStochastic X) {δ0 : ℝ}
    (hXfloor : ∀ i j, δ0 ≤ X i j)
    {mix r : ℝ} (hmix0 : 0 < mix) (hmix1 : mix ≤ 1) (hr : 0 ≤ r)
    (hspike : r / mix ≤ 1 / (m + 1 : ℝ))
    {δ upper : ℝ} (hδ : δ ≤ (1 - mix) * δ0)
    (hslack :
      -regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) X +
        mix * (rationalRegularizedObjectiveRange A : ℝ) + 2 * r ≤ upper) :
    let ycenter := squareMatrixToVector (smoothedUniformAffineBase X mix)
    let zcenter := epigraphPoint ycenter (upper - r)
    (∀ k, BetheEpigraphTarget (τ : ℝ) (fun i j ↦ (A i j : ℝ))
      δ upper (fun i ↦ zcenter i + if i = k then r else 0)) ∧
    (∀ k, BetheEpigraphTarget (τ : ℝ) (fun i j ↦ (A i j : ℝ))
      δ upper (fun i ↦ zcenter i - if i = k then r else 0)) := by
  dsimp only
  have hmix0' : 0 ≤ mix := hmix0.le
  have hobjectiveCenter :
      -regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) X +
        mix * (rationalRegularizedObjectiveRange A : ℝ) ≤ upper - r := by
    linarith
  have hcenterUpper : upper - r ≤ upper := by linarith
  have hobjectiveLow :
      -regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) X +
        mix * (rationalRegularizedObjectiveRange A : ℝ) ≤ upper - 2 * r := by
    linarith
  have hlowUpper : upper - 2 * r ≤ upper := by linarith
  have hqplus : abs (r / mix) ≤ 1 / (m + 1 : ℝ) := by
    rw [abs_div, abs_of_nonneg hr, abs_of_pos hmix0]
    exact hspike
  have hqminus : abs (-r / mix) ≤ 1 / (m + 1 : ℝ) := by
    rw [abs_div, abs_neg, abs_of_nonneg hr, abs_of_pos hmix0]
    exact hspike
  let k0 : Fin (m * m) := ⟨0, Nat.mul_pos hm hm⟩
  constructor
  · intro k
    refine Fin.lastCases ?_ (fun k ↦ ?_) k
    · let Zbase := vectorToSquareMatrix
        (fun l ↦ squareMatrixToVector (uniformAffineCoordinatesReal m) l +
          coordinateSpike k0 0 l)
      let Ybase := fun i j ↦
        (1 - mix) * birkhoffAffineCoordinates X i j + mix * Zbase i j
      have hmem : BetheEpigraphTarget (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) δ upper
          (epigraphPoint (squareMatrixToVector Ybase) upper) := by
        simpa only [Zbase, Ybase] using!
          smoothedUniformSpike_mem_epigraph hm hτ0 hτ1 hApos hAupper
            hX hXfloor hmix0' hmix1 k0 (q := 0) (by
              simp; positivity) hδ
            (hobjectiveCenter.trans hcenterUpper) le_rfl
      have hvec : squareMatrixToVector Ybase =
          squareMatrixToVector (smoothedUniformAffineBase X mix) := by
        have h := squareMatrixToVector_smoothedUniformSpike_of_mul
          X mix k0 0 0 (by ring)
        calc
          squareMatrixToVector Ybase =
              fun l ↦ squareMatrixToVector
                  (smoothedUniformAffineBase X mix) l +
                coordinateSpike k0 0 l := by
            simpa only [Zbase, Ybase] using! h
          _ = squareMatrixToVector (smoothedUniformAffineBase X mix) := by
            ext l
            simp [coordinateSpike]
      rw [epigraphPoint_add_heightSpike, show upper - r + r = upper by ring,
        ← hvec]
      exact hmem
    · let q := r / mix
      let Zbase := vectorToSquareMatrix
        (fun l ↦ squareMatrixToVector (uniformAffineCoordinatesReal m) l +
          coordinateSpike k q l)
      let Ybase := fun i j ↦
        (1 - mix) * birkhoffAffineCoordinates X i j + mix * Zbase i j
      have hmul : mix * q = r := by
        dsimp only [q]
        field_simp [hmix0.ne']
      have hmem : BetheEpigraphTarget (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) δ upper
          (epigraphPoint (squareMatrixToVector Ybase) (upper - r)) := by
        simpa only [Zbase, Ybase, q] using!
          smoothedUniformSpike_mem_epigraph hm hτ0 hτ1 hApos hAupper
            hX hXfloor hmix0' hmix1 k hqplus hδ
            hobjectiveCenter hcenterUpper
      have hvec : squareMatrixToVector Ybase =
          fun l ↦ squareMatrixToVector (smoothedUniformAffineBase X mix) l +
            coordinateSpike k r l := by
        simpa only [Zbase, Ybase, q] using!
          squareMatrixToVector_smoothedUniformSpike_of_mul
            X mix k q r hmul
      rw [epigraphPoint_add_baseSpike, ← hvec]
      exact hmem
  · intro k
    refine Fin.lastCases ?_ (fun k ↦ ?_) k
    · let Zbase := vectorToSquareMatrix
        (fun l ↦ squareMatrixToVector (uniformAffineCoordinatesReal m) l +
          coordinateSpike k0 0 l)
      let Ybase := fun i j ↦
        (1 - mix) * birkhoffAffineCoordinates X i j + mix * Zbase i j
      have hmem : BetheEpigraphTarget (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) δ upper
          (epigraphPoint (squareMatrixToVector Ybase) (upper - 2 * r)) := by
        simpa only [Zbase, Ybase] using!
          smoothedUniformSpike_mem_epigraph hm hτ0 hτ1 hApos hAupper
            hX hXfloor hmix0' hmix1 k0 (q := 0) (by
              simp; positivity) hδ hobjectiveLow hlowUpper
      have hvec : squareMatrixToVector Ybase =
          squareMatrixToVector (smoothedUniformAffineBase X mix) := by
        have h := squareMatrixToVector_smoothedUniformSpike_of_mul
          X mix k0 0 0 (by ring)
        calc
          squareMatrixToVector Ybase =
              fun l ↦ squareMatrixToVector
                  (smoothedUniformAffineBase X mix) l +
                coordinateSpike k0 0 l := by
            simpa only [Zbase, Ybase] using! h
          _ = squareMatrixToVector (smoothedUniformAffineBase X mix) := by
            ext l
            simp [coordinateSpike]
      rw [epigraphPoint_sub_heightSpike,
        show upper - r - r = upper - 2 * r by ring, ← hvec]
      exact hmem
    · let q := -r / mix
      let Zbase := vectorToSquareMatrix
        (fun l ↦ squareMatrixToVector (uniformAffineCoordinatesReal m) l +
          coordinateSpike k q l)
      let Ybase := fun i j ↦
        (1 - mix) * birkhoffAffineCoordinates X i j + mix * Zbase i j
      have hmul : mix * q = -r := by
        dsimp only [q]
        field_simp [hmix0.ne']
      have hmem : BetheEpigraphTarget (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) δ upper
          (epigraphPoint (squareMatrixToVector Ybase) (upper - r)) := by
        simpa only [Zbase, Ybase, q] using!
          smoothedUniformSpike_mem_epigraph hm hτ0 hτ1 hApos hAupper
            hX hXfloor hmix0' hmix1 k hqminus hδ
            hobjectiveCenter hcenterUpper
      have hvec : squareMatrixToVector Ybase =
          fun l ↦ squareMatrixToVector (smoothedUniformAffineBase X mix) l +
            coordinateSpike k (-r) l := by
        simpa only [Zbase, Ybase, q] using!
          squareMatrixToVector_smoothedUniformSpike_of_mul
            X mix k q (-r) hmul
      have hspikeNeg :
          (fun l ↦ squareMatrixToVector (smoothedUniformAffineBase X mix) l -
            coordinateSpike k r l) =
          fun l ↦ squareMatrixToVector (smoothedUniformAffineBase X mix) l +
            coordinateSpike k (-r) l := by
        ext l
        by_cases hlk : l = k
        · subst l
          simp [coordinateSpike]
          ring
        · simp [coordinateSpike, hlk]
      rw [epigraphPoint_sub_baseSpike, hspikeNeg, ← hvec]
      exact hmem

/-- A coordinatewise bound controls the Euclidean square norm with a
square-root-free radius. -/
theorem finiteNormSq_le_dimension_sq_of_abs_le
    {d : ℕ} (hd : 0 < d) {C : ℝ} (hC : 0 ≤ C)
    (x : Fin d → ℝ) (hx : ∀ i, abs (x i) ≤ C) :
    finiteNormSq x ≤ ((d : ℝ) * C) ^ 2 := by
  have hterm : ∀ i, x i ^ 2 ≤ C ^ 2 := by
    intro i
    have habs := hx i
    have hlower := (abs_le.mp habs).1
    have hupper := (abs_le.mp habs).2
    nlinarith
  rw [finiteNormSq, finiteDot]
  calc
    (∑ i, x i * x i) ≤ ∑ _i : Fin d, C ^ 2 :=
      Finset.sum_le_sum fun i _ ↦ by simpa [pow_two] using! hterm i
    _ = (d : ℝ) * C ^ 2 := by simp
    _ ≤ ((d : ℝ) * C) ^ 2 := by
      have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
      nlinarith [sq_nonneg C]

/-- Every flattened base coordinate of a nonnegatively truncated epigraph
point lies in the unit interval. -/
theorem BetheEpigraphTarget_epigraphBase_abs_le_one
    {m : ℕ} {τ : ℝ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    {δ upper : ℝ} (hδ : 0 ≤ δ) {z : Fin (m * m + 1) → ℝ}
    (hz : BetheEpigraphTarget τ A δ upper z) (l : Fin (m * m)) :
    abs (epigraphBase z l) ≤ 1 := by
  let ij := finProdFinEquiv.symm l
  let X := birkhoffAffineMap (vectorToSquareMatrix (epigraphBase z))
  have hX := BetheEpigraphTarget_doublyStochastic hδ hz
  have hentry0 : 0 ≤ X ij.1.castSucc ij.2.castSucc :=
    hX.nonnegative _ _
  have hentry1 : X ij.1.castSucc ij.2.castSucc ≤ 1 :=
    hX.entry_le_one _ _
  have hcoordinate : X ij.1.castSucc ij.2.castSucc = epigraphBase z l := by
    simp only [X, birkhoffAffineMap_castSucc_castSucc, vectorToSquareMatrix, ij]
    rw [show ((finProdFinEquiv.symm l).1,
      (finProdFinEquiv.symm l).2) = finProdFinEquiv.symm l by rfl,
      Equiv.apply_symm_apply]
  rw [← hcoordinate, abs_of_nonneg hentry0]
  exact hentry1

/-- A coordinate cross in the truncated epigraph is contained in an explicit
ball centered at zero.  The center of the cross may depend on the exact
optimizer, but the containing ball depends only on the rational height and
radius supplied to the algorithm. -/
theorem BetheEpigraphTarget_inner_cross_outer_zero
    {m : ℕ} (hm : 0 < m)
    {τ : ℝ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    {δ upper r : ℝ} (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (ycenter : Fin (m * m) → ℝ)
    (hplus : ∀ k, BetheEpigraphTarget τ A δ upper
      (fun i ↦ epigraphPoint ycenter (upper - r) i +
        if i = k then r else 0))
    (hminus : ∀ k, BetheEpigraphTarget τ A δ upper
      (fun i ↦ epigraphPoint ycenter (upper - r) i -
        if i = k then r else 0)) :
    let C := 1 + abs upper + 2 * r
    (∀ k, finiteNormSq
      (fun i ↦ epigraphPoint ycenter (upper - r) i +
        if i = k then r else 0) ≤
          (((m * m + 1 : ℕ) : ℝ) * C) ^ 2) ∧
    (∀ k, finiteNormSq
      (fun i ↦ epigraphPoint ycenter (upper - r) i -
        if i = k then r else 0) ≤
          (((m * m + 1 : ℕ) : ℝ) * C) ^ 2) := by
  dsimp only
  let C : ℝ := 1 + abs upper + 2 * r
  have hC : 0 ≤ C := by
    dsimp only [C]
    linarith [abs_nonneg upper]
  have honeC : (1 : ℝ) ≤ C := by
    dsimp only [C]
    linarith [abs_nonneg upper]
  constructor
  · intro k
    apply finiteNormSq_le_dimension_sq_of_abs_le (by omega) hC
    intro i
    refine Fin.lastCases ?_ (fun l ↦ ?_) i
    · by_cases hk : Fin.last (m * m) = k
      · have hvalue :
            epigraphPoint ycenter (upper - r) (Fin.last (m * m)) +
                (if Fin.last (m * m) = k then r else 0) = upper := by
          subst k
          simp [epigraphPoint]
        rw [hvalue]
        dsimp only [C]
        linarith [abs_nonneg upper]
      · have htriangle : abs (upper - r) ≤ abs upper + r := by
          calc
            abs (upper - r) ≤ abs upper + abs r := abs_sub upper r
            _ = abs upper + r := by rw [abs_of_nonneg hr]
        simp only [epigraphPoint, Fin.snoc_last, ite_eq_right hk, add_zero]
        exact htriangle.trans (by dsimp only [C]; linarith)
    · have hbase := BetheEpigraphTarget_epigraphBase_abs_le_one hδ
        (hplus k) l
      simpa only [epigraphBase] using! hbase.trans honeC
  · intro k
    apply finiteNormSq_le_dimension_sq_of_abs_le (by omega) hC
    intro i
    refine Fin.lastCases ?_ (fun l ↦ ?_) i
    · by_cases hk : Fin.last (m * m) = k
      · have htriangle : abs (upper - 2 * r) ≤ abs upper + 2 * r := by
          calc
            abs (upper - 2 * r) ≤ abs upper + abs (2 * r) :=
              abs_sub upper (2 * r)
            _ = abs upper + 2 * r := by rw [abs_of_nonneg (mul_nonneg (by norm_num) hr)]
        have hvalue :
            epigraphPoint ycenter (upper - r) (Fin.last (m * m)) -
                (if Fin.last (m * m) = k then r else 0) =
              upper - 2 * r := by
          subst k
          simp [epigraphPoint]
          ring
        rw [hvalue]
        exact htriangle.trans (by dsimp only [C]; linarith)
      · have htriangle : abs (upper - r) ≤ abs upper + r := by
          calc
            abs (upper - r) ≤ abs upper + abs r := abs_sub upper r
            _ = abs upper + r := by rw [abs_of_nonneg hr]
        simp only [epigraphPoint, Fin.snoc_last, ite_eq_right hk, sub_zero]
        exact htriangle.trans (by dsimp only [C]; linarith)
    · have hbase := BetheEpigraphTarget_epigraphBase_abs_le_one hδ
        (hminus k) l
      simpa only [epigraphBase] using! hbase.trans honeC

end BeyondBethe

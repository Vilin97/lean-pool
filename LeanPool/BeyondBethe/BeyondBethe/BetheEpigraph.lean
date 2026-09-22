/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.RationalEpigraphOracle
import LeanPool.BeyondBethe.BeyondBethe.WeakSeparation
import Mathlib.Tactic

/-! # Bethe Epigraph -/

open scoped BigOperators

namespace BeyondBethe

/-!
# The concrete directed Bethe epigraph data

The upper-left `m`-by-`m` affine coordinates are flattened into `m^2`
rational coordinates.  This file connects the already certified directed
objective and gradient evaluations to the generic rational epigraph oracle.
-/

def squareMatrixToVector {m : ℕ} {R : Type*}
    (Y : Matrix (Fin m) (Fin m) R) : Fin (m * m) → R :=
  fun k ↦
    let ij := finProdFinEquiv.symm k
    Y ij.1 ij.2

def vectorToSquareMatrix {m : ℕ} {R : Type*}
    (y : Fin (m * m) → R) : Matrix (Fin m) (Fin m) R :=
  fun i j ↦ y (finProdFinEquiv (i, j))

@[simp] theorem vectorToSquareMatrix_squareMatrixToVector
    {m : ℕ} {R : Type*} (Y : Matrix (Fin m) (Fin m) R) :
    vectorToSquareMatrix (squareMatrixToVector Y) = Y := by
  ext i j
  simp [vectorToSquareMatrix, squareMatrixToVector]

@[simp] theorem squareMatrixToVector_vectorToSquareMatrix
    {m : ℕ} {R : Type*} (y : Fin (m * m) → R) :
    squareMatrixToVector (vectorToSquareMatrix y) = y := by
  ext k
  change y (finProdFinEquiv (finProdFinEquiv.symm k)) = y k
  rw [Equiv.apply_symm_apply]

theorem squareMatrixToVector_injective {m : ℕ} {R : Type*} :
    Function.Injective (@squareMatrixToVector m R) := by
  intro Y Z h
  calc
    Y = vectorToSquareMatrix (squareMatrixToVector Y) :=
      (vectorToSquareMatrix_squareMatrixToVector Y).symm
    _ = vectorToSquareMatrix (squareMatrixToVector Z) := by rw [h]
    _ = Z := vectorToSquareMatrix_squareMatrixToVector Z

theorem sum_squareMatrixToVector {m : ℕ} {R : Type*} [AddCommMonoid R]
    (Y : Matrix (Fin m) (Fin m) R) :
    (∑ k, squareMatrixToVector Y k) = ∑ i, ∑ j, Y i j := by
  calc
    (∑ k, squareMatrixToVector Y k) =
        ∑ ij : Fin m × Fin m,
          squareMatrixToVector Y (finProdFinEquiv ij) :=
      (finProdFinEquiv.sum_comp (squareMatrixToVector Y)).symm
    _ = ∑ ij : Fin m × Fin m, Y ij.1 ij.2 := by
      apply Finset.sum_congr rfl
      intro ij _
      simp [squareMatrixToVector]
    _ = ∑ i, ∑ j, Y i j := Fintype.sum_prod_type _

theorem finiteDot_squareMatrixToVector {m : ℕ} {R : Type*} [CommSemiring R]
    (G D : Matrix (Fin m) (Fin m) R) :
    finiteDot (squareMatrixToVector G) (squareMatrixToVector D) =
      matrixPairing G D := by
  change (∑ k, squareMatrixToVector
      (fun i j ↦ G i j * D i j) k) = ∑ i, ∑ j, G i j * D i j
  exact sum_squareMatrixToVector (fun i j => G i j * D i j)

theorem vectorL1_squareMatrixToVector {m : ℕ}
    (D : Matrix (Fin m) (Fin m) ℝ) :
    vectorL1 (squareMatrixToVector D) = matrixL1 D := by
  change (∑ k, squareMatrixToVector
      (fun i j ↦ abs (D i j)) k) = ∑ i, ∑ j, abs (D i j)
  exact sum_squareMatrixToVector (fun i j => abs (D i j))

/-- Rational affine matrix represented by a flattened epigraph base point. -/
def betheAffineMatrixQ {m : ℕ} (y : Fin (m * m) → ℚ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ :=
  birkhoffAffineMap (vectorToSquareMatrix y)

/-- Concrete directed value and affine-gradient endpoints. -/
def betheDirectedEpigraphData {m : ℕ}
    (τ : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) (p : ℕ) :
    DirectedEpigraphData (m * m) where
  lower y := directedNegativeObjectiveLower τ A (betheAffineMatrixQ y) p
  gradient y := squareMatrixToVector
    (affinePullbackGradient
      (directedNegativeGradientLowerMatrix τ A (betheAffineMatrixQ y) p))

theorem cast_vectorToSquareMatrix {m : ℕ}
    (y : Fin (m * m) → ℚ) (i j : Fin m) :
    ((vectorToSquareMatrix y i j : ℚ) : ℝ) =
      vectorToSquareMatrix (fun k ↦ (y k : ℝ)) i j := by
  rfl

theorem cast_betheAffineMatrixQ {m : ℕ}
    (y : Fin (m * m) → ℚ) (i j : Fin (m + 1)) :
    ((betheAffineMatrixQ y i j : ℚ) : ℝ) =
      birkhoffAffineMap (vectorToSquareMatrix
        (fun k ↦ (y k : ℝ))) i j := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;>
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · simp [betheAffineMatrixQ, vectorToSquareMatrix]
  · simp [betheAffineMatrixQ, vectorToSquareMatrix]
  · simp [betheAffineMatrixQ, vectorToSquareMatrix]
  · simp [betheAffineMatrixQ, vectorToSquareMatrix]

/-- The stored rational value is a certified lower endpoint for the exact
negative regularized objective at every rational interior query. -/
theorem betheDirectedEpigraphData_lower {m : ℕ}
    {τ : ℚ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hA : ∀ i j, 0 < A i j)
    {y : Fin (m * m) → ℚ}
    (hX0 : ∀ i j, 0 < betheAffineMatrixQ y i j)
    (hX1 : ∀ i j, betheAffineMatrixQ y i j < 1) (p : ℕ) :
    ((betheDirectedEpigraphData τ A p).lower y : ℝ) ≤
      affineNegativeObjective (τ : ℝ)
        (fun i j ↦ (A i j : ℝ))
        (vectorToSquareMatrix (fun k ↦ (y k : ℝ))) := by
  have h := (directedNegativeObjective_bounds hτ0 hτ1 hA hX0 hX1 p).1
  simpa [betheDirectedEpigraphData, affineNegativeObjective,
    cast_betheAffineMatrixQ] using! h

/-- The flattened stored gradient has the same explicit coordinate error as
the affine pullback matrix. -/
theorem betheDirectedEpigraphData_gradient_error {m : ℕ}
    {τ : ℚ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hA : ∀ i j, 0 < A i j)
    {y : Fin (m * m) → ℚ}
    (hX0 : ∀ i j, 0 < betheAffineMatrixQ y i j)
    (hX1 : ∀ i j, betheAffineMatrixQ y i j < 1) (p : ℕ)
    (k : Fin (m * m)) :
    abs ((((betheDirectedEpigraphData τ A p).gradient y k : ℚ) : ℝ) -
      squareMatrixToVector
        (affinePullbackGradient
          (negativeGradientMatrix (τ : ℝ)
            (fun i j ↦ (A i j : ℝ))
            (fun i j ↦ ((betheAffineMatrixQ y i j : ℚ) : ℝ)))) k) ≤
      16 * (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by
  let ij := finProdFinEquiv.symm k
  simpa [betheDirectedEpigraphData, squareMatrixToVector, ij,
    affinePullbackGradient, abs_sub_comm] using!
    directedAffineGradient_error hτ0 hτ1 hA hX0 hX1 p ij.1 ij.2

/-- Exact bounded epigraph body in flattened affine coordinates. -/
def BetheEpigraphTarget {m : ℕ}
    (τ : ℝ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (δ upper : ℝ) (z : Fin (m * m + 1) → ℝ) : Prop :=
  let Y := vectorToSquareMatrix (epigraphBase z)
  let X := birkhoffAffineMap Y
  (∀ i j, δ ≤ X i j) ∧
    affineNegativeObjective τ A Y ≤ epigraphHeight z ∧
    epigraphHeight z ≤ upper

theorem BetheEpigraphTarget_doublyStochastic {m : ℕ}
    {τ : ℝ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    {δ upper : ℝ} (hδ : 0 ≤ δ) {z : Fin (m * m + 1) → ℝ}
    (hz : BetheEpigraphTarget τ A δ upper z) :
    IsDoublyStochastic
      (birkhoffAffineMap (vectorToSquareMatrix (epigraphBase z))) := by
  let Y := vectorToSquareMatrix (epigraphBase z)
  let X := birkhoffAffineMap Y
  have hfloor : ∀ i j, δ ≤ X i j := by
    simpa only [BetheEpigraphTarget, Y, X] using! hz.1
  refine ⟨fun i j ↦ hδ.trans (hfloor i j), ?_, ?_⟩
  · exact birkhoffAffineMap_row_sum Y
  · exact birkhoffAffineMap_col_sum Y

/-- On the truncated rational domain, the concrete directed nonlinear oracle
returns only valid strict cuts for the exact Bethe epigraph. -/
theorem betheDirectedEpigraphOracle_cut_valid {m : ℕ} (hm : 0 < m)
    {τ : ℚ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hA : ∀ i j, 0 < A i j)
    {δ : ℚ} (hδ : 0 < δ) {upper : ℝ} (p : ℕ)
    (E : RationalEllipsoidState (m * m + 1))
    (hqueryFloor : ∀ i j, δ ≤
      betheAffineMatrixQ (epigraphBase E.center) i j)
    {a : Fin (m * m + 1) → ℚ}
    (hresponse : directedEpigraphOracle
      (betheDirectedEpigraphData τ A p)
      (16 * (1 / 2 : ℚ) ^ p) (m * m) E = .cut a)
    {z : Fin (m * m + 1) → ℝ}
    (hz : BetheEpigraphTarget (τ : ℝ)
      (fun i j ↦ (A i j : ℝ)) (δ : ℝ) upper z) :
    a ≠ 0 ∧ finiteDot (fun i ↦ (a i : ℝ))
      (fun i ↦ z i - rationalCenterReal E i) < 0 := by
  let yq : Fin (m * m) → ℚ := epigraphBase E.center
  let Yq : Matrix (Fin m) (Fin m) ℚ := vectorToSquareMatrix yq
  let Xq : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ :=
    birkhoffAffineMap Yq
  let Y : Matrix (Fin m) (Fin m) ℝ :=
    vectorToSquareMatrix (epigraphBase z)
  let X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    birkhoffAffineMap Y
  have hqueryFloor' : ∀ i j, δ ≤ Xq i j := by
    simpa only [Xq, Yq, yq, betheAffineMatrixQ] using! hqueryFloor
  have hquery := birkhoffAffineMap_interior hm hδ hqueryFloor'
  have hXqDS := hquery.1
  have hXqInt := hquery.2
  have hXq0 : ∀ i j, 0 < Xq i j := by
    intro i j
    exact hδ.trans_le (hqueryFloor' i j)
  have hXq1 : ∀ i j, Xq i j < 1 := by
    intro i j
    have h := (hXqInt i).2 j |>.2
    change ((Xq i j : ℚ) : ℝ) < 1 at h
    exact_mod_cast h
  have hδreal : 0 ≤ (δ : ℝ) := Rat.cast_nonneg.mpr hδ.le
  have hXDS : IsDoublyStochastic X := by
    simpa only [X, Y] using!
      BetheEpigraphTarget_doublyStochastic hδreal hz
  have htargetFloor : ∀ i j, (δ : ℝ) ≤ X i j := by
    simpa only [BetheEpigraphTarget, X, Y] using! hz.1
  have htargetEpigraph :
      affineNegativeObjective (τ : ℝ) (fun i j ↦ (A i j : ℝ)) Y ≤
        epigraphHeight z := by
    simpa only [BetheEpigraphTarget, X, Y] using! hz.2.1
  let YqR : Matrix (Fin m) (Fin m) ℝ :=
    fun i j ↦ (Yq i j : ℝ)
  let Gm : Matrix (Fin m) (Fin m) ℝ :=
    affinePullbackGradient
      (negativeGradientMatrix (τ : ℝ) (fun i j ↦ (A i j : ℝ))
        (fun i j ↦ (Xq i j : ℝ)))
  let Gv : Fin (m * m) → ℝ := squareMatrixToVector Gm
  have hcastXq : birkhoffAffineMap YqR =
      (fun i j ↦ (Xq i j : ℝ)) := by
    ext i j
    symm
    simpa only [Xq, Yq, YqR, yq] using! cast_betheAffineMatrixQ yq i j
  have hsupportMatrix := affineNegativeObjective_support hm
    (Rat.cast_nonneg.mpr hτ0)
    (A := fun i j ↦ (A i j : ℝ))
    (Y := YqR) (Z := Y)
    (by rw [hcastXq]; exact hXqDS)
    hXDS
    (by rw [hcastXq]; exact hXqInt)
  have hsupport :
      affineNegativeObjective (τ : ℝ) (fun i j ↦ (A i j : ℝ)) YqR +
          finiteDot Gv
            (fun k ↦ epigraphBase z k - (yq k : ℝ)) ≤
        affineNegativeObjective (τ : ℝ) (fun i j ↦ (A i j : ℝ)) Y := by
    have hDvec :
        (fun k ↦ epigraphBase z k - (yq k : ℝ)) =
          squareMatrixToVector (fun i j ↦ Y i j - YqR i j) := by
      ext k
      have hk : finProdFinEquiv (finProdFinEquiv.symm k) = k :=
        Equiv.apply_symm_apply finProdFinEquiv k
      change epigraphBase z k - (yq k : ℝ) =
        epigraphBase z (finProdFinEquiv (finProdFinEquiv.symm k)) -
          (yq (finProdFinEquiv (finProdFinEquiv.symm k)) : ℝ)
      rw [hk]
    rw [hDvec, finiteDot_squareMatrixToVector Gm
      (fun i j => Y i j - YqR i j)]
    simpa only [Gm, hcastXq] using! hsupportMatrix
  have hlower := betheDirectedEpigraphData_lower hτ0 hτ1 hA
    (by simpa only [Xq, yq, betheAffineMatrixQ] using! hXq0)
    (by simpa only [Xq, yq, betheAffineMatrixQ] using! hXq1) p
  have hgradient : ∀ k,
      abs ((((betheDirectedEpigraphData τ A p).gradient yq k : ℚ) : ℝ) -
        Gv k) ≤ 16 * (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by
    intro k
    simpa only [Gv, Gm, Xq, yq, betheAffineMatrixQ] using!
      betheDirectedEpigraphData_gradient_error hτ0 hτ1 hA hXq0 hXq1 p k
  have hD : vectorL1 (fun k ↦ epigraphBase z k - (yq k : ℝ)) ≤
      (m * m : ℝ) := by
    rw [vectorL1]
    calc
      (∑ k, abs (epigraphBase z k - (yq k : ℝ))) ≤ ∑ _k : Fin (m * m), 1 := by
        apply Finset.sum_le_sum
        intro k _
        let ij := finProdFinEquiv.symm k
        have hk : finProdFinEquiv ij = k := by
          simpa only [ij] using! Equiv.apply_symm_apply finProdFinEquiv k
        have hz0 : 0 ≤ epigraphBase z k := by
          have := hXDS.nonnegative ij.1.castSucc ij.2.castSucc
          simp only [X, Y, birkhoffAffineMap_castSucc_castSucc,
            vectorToSquareMatrix] at this
          rwa [hk] at this
        have hz1 : epigraphBase z k ≤ 1 := by
          have := hXDS.entry_le_one ij.1.castSucc ij.2.castSucc
          simp only [X, Y, birkhoffAffineMap_castSucc_castSucc,
            vectorToSquareMatrix] at this
          rwa [hk] at this
        have hq0 : 0 ≤ (yq k : ℝ) := by
          have := hXqDS.nonnegative ij.1.castSucc ij.2.castSucc
          simp only [Xq, Yq, birkhoffAffineMap_castSucc_castSucc,
            vectorToSquareMatrix] at this
          rwa [hk] at this
        have hq1 : (yq k : ℝ) ≤ 1 := by
          have := hXqDS.entry_le_one ij.1.castSucc ij.2.castSucc
          simp only [Xq, Yq, birkhoffAffineMap_castSucc_castSucc,
            vectorToSquareMatrix] at this
          rwa [hk] at this
        rw [abs_le]
        constructor <;> linarith
      _ = (m * m : ℝ) := by simp
  apply directedEpigraphOracle_cut_valid
    (data := betheDirectedEpigraphData τ A p)
    (he := by positivity) E hresponse
    (fY := affineNegativeObjective (τ : ℝ)
      (fun i j ↦ (A i j : ℝ)) YqR)
    (fZ := affineNegativeObjective (τ : ℝ)
      (fun i j ↦ (A i j : ℝ)) Y)
    (G := Gv) (z := z)
  · simpa only [yq] using! hsupport
  · simpa only [yq, YqR] using! hlower
  · simpa only [yq, Rat.cast_mul, Rat.cast_pow, Rat.cast_div,
      Rat.cast_one, Rat.cast_ofNat] using! hgradient
  · norm_num only [Rat.cast_mul, Rat.cast_natCast]
    simpa only [yq] using! hD
  · exact htargetEpigraph

/-- Matrix covector selecting one full Birkhoff coordinate. -/
def matrixEntryCovector {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) ℚ :=
  fun a b ↦ if a = i ∧ b = j then 1 else 0

/-- Normal for the exact lower-floor inequality at one recovered Birkhoff
entry.  The last epigraph coordinate is zero. -/
def betheFloorCutNormal {m : ℕ} (i j : Fin (m + 1)) :
    Fin (m * m + 1) → ℚ :=
  Fin.snoc (fun k ↦
    -squareMatrixToVector
      (affinePullbackGradient (matrixEntryCovector i j)) k) 0

@[simp] theorem betheFloorCutNormal_castSucc {m : ℕ}
    (i j : Fin (m + 1)) (k : Fin (m * m)) :
    betheFloorCutNormal i j k.castSucc =
      -squareMatrixToVector
        (affinePullbackGradient (matrixEntryCovector i j)) k := by
  simp [betheFloorCutNormal]

@[simp] theorem betheFloorCutNormal_last {m : ℕ}
    (i j : Fin (m + 1)) :
    betheFloorCutNormal i j (Fin.last (m * m)) = 0 := by
  simp [betheFloorCutNormal]

theorem affinePullback_entryCovector_ne_zero {m : ℕ} (hm : 0 < m)
    (i j : Fin (m + 1)) :
    affinePullbackGradient (matrixEntryCovector i j) ≠ 0 := by
  let k0 : Fin m := ⟨0, hm⟩
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;>
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · intro hzero
    have h := congrFun (congrFun hzero k0) k0
    simp [affinePullbackGradient, matrixEntryCovector] at h
  · intro hzero
    have h := congrFun (congrFun hzero k0) j
    have hne : Fin.last m ≠ j.castSucc := (Fin.castSucc_ne_last j).symm
    simp [affinePullbackGradient, matrixEntryCovector, hne] at h
  · intro hzero
    have h := congrFun (congrFun hzero i) k0
    have hne : Fin.last m ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
    simp [affinePullbackGradient, matrixEntryCovector, hne] at h
  · intro hzero
    have h := congrFun (congrFun hzero i) j
    have hnei : Fin.last m ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
    have hnej : Fin.last m ≠ j.castSucc := (Fin.castSucc_ne_last j).symm
    simp [affinePullbackGradient, matrixEntryCovector, hnei, hnej] at h

theorem betheFloorCutNormal_ne_zero {m : ℕ} (hm : 0 < m)
    (i j : Fin (m + 1)) : betheFloorCutNormal i j ≠ 0 := by
  intro hzero
  apply affinePullback_entryCovector_ne_zero hm i j
  have hvec : squareMatrixToVector
      (affinePullbackGradient (matrixEntryCovector i j)) = 0 := by
    ext k
    have h := congrFun hzero k.castSucc
    rw [betheFloorCutNormal_castSucc] at h
    simp only [Pi.zero_apply] at h
    exact neg_eq_zero.mp h
  exact squareMatrixToVector_injective hvec

/-- Fixed deterministic order of all recovered matrix entries. -/
def fullMatrixEntryList (m : ℕ) : List (Fin (m + 1) × Fin (m + 1)) :=
  (List.ofFn fun i : Fin (m + 1) ↦ i).flatMap fun i ↦
    (List.ofFn fun j : Fin (m + 1) ↦ j).map fun j ↦ (i, j)

theorem mem_fullMatrixEntryList (m : ℕ) (i j : Fin (m + 1)) :
    (i, j) ∈ fullMatrixEntryList m := by
  rw [fullMatrixEntryList, List.mem_flatMap]
  refine ⟨i, (List.mem_ofFn).2 ⟨i, rfl⟩, ?_⟩
  rw [List.mem_map]
  exact ⟨j, (List.mem_ofFn).2 ⟨j, rfl⟩, rfl⟩

def firstBetheFloorViolation {m : ℕ} (δ : ℚ)
    (y : Fin (m * m) → ℚ) :
    List (Fin (m + 1) × Fin (m + 1)) →
      Option (Fin (m + 1) × Fin (m + 1))
  | [] => none
  | ij :: entries =>
      if betheAffineMatrixQ y ij.1 ij.2 < δ then some ij
      else firstBetheFloorViolation δ y entries

def firstBetheFloorViolationAll {m : ℕ} (δ : ℚ)
    (y : Fin (m * m) → ℚ) : Option (Fin (m + 1) × Fin (m + 1)) :=
  firstBetheFloorViolation δ y (fullMatrixEntryList m)

theorem firstBetheFloorViolation_is_below {m : ℕ} {δ : ℚ}
    {y : Fin (m * m) → ℚ}
    {entries : List (Fin (m + 1) × Fin (m + 1))} {ij}
    (hfind : firstBetheFloorViolation δ y entries = some ij) :
    betheAffineMatrixQ y ij.1 ij.2 < δ := by
  induction entries with
  | nil => simp [firstBetheFloorViolation] at hfind
  | cons ab entries ih =>
      rw [firstBetheFloorViolation] at hfind
      split at hfind <;> rename_i htest
      · cases hfind
        exact htest
      · exact ih hfind

theorem firstBetheFloorViolation_eq_none_iff {m : ℕ} (δ : ℚ)
    (y : Fin (m * m) → ℚ)
    (entries : List (Fin (m + 1) × Fin (m + 1))) :
    firstBetheFloorViolation δ y entries = none ↔
      ∀ ij ∈ entries, δ ≤ betheAffineMatrixQ y ij.1 ij.2 := by
  induction entries with
  | nil => simp [firstBetheFloorViolation]
  | cons ab entries ih =>
      rw [firstBetheFloorViolation]
      split <;> rename_i htest
      · constructor
        · intro hnone
          contradiction
        · intro hall
          exact ((not_lt_of_ge (hall ab (by simp))) htest).elim
      · rw [ih]
        have hab : δ ≤ betheAffineMatrixQ y ab.1 ab.2 := not_lt.mp htest
        simp [hab]

theorem firstBetheFloorViolationAll_eq_none_iff {m : ℕ} (δ : ℚ)
    (y : Fin (m * m) → ℚ) :
    firstBetheFloorViolationAll δ y = none ↔
      ∀ i j, δ ≤ betheAffineMatrixQ y i j := by
  rw [firstBetheFloorViolationAll,
    firstBetheFloorViolation_eq_none_iff]
  constructor
  · intro h i j
    exact h (i, j) (mem_fullMatrixEntryList m i j)
  · intro h ij _
    exact h ij.1 ij.2

theorem matrixPairing_entryCovector {n : ℕ} (i j : Fin n)
    (D : Matrix (Fin n) (Fin n) ℝ) :
    matrixPairing (fun a b ↦ (matrixEntryCovector i j a b : ℝ)) D = D i j := by
  unfold matrixPairing
  have hrow : ∀ a : Fin n,
      (∑ b, (matrixEntryCovector i j a b : ℝ) * D a b) =
        if a = i then D i j else 0 := by
    intro a
    by_cases hai : a = i
    · subst a
      simp only [if_true]
      calc
        (∑ b, (matrixEntryCovector i j i b : ℝ) * D i b) =
            (matrixEntryCovector i j i j : ℝ) * D i j := by
          apply Finset.sum_eq_single j
          · intro b _ hbj
            simp [matrixEntryCovector, hbj]
          · simp
        _ = D i j := by simp [matrixEntryCovector]
    · simp [matrixEntryCovector, hai]
  simp_rw [hrow]
  simp

/-- A detected floor violation gives a strict cut for every target point
whose recovered matrix satisfies the floor. -/
theorem betheFloorCut_valid {m : ℕ} {δ : ℚ}
    {y : Fin (m * m) → ℚ} {i j : Fin (m + 1)}
    (hbelow : betheAffineMatrixQ y i j < δ)
    {z : Fin (m * m + 1) → ℝ}
    (hfloor : (δ : ℝ) ≤
      birkhoffAffineMap (vectorToSquareMatrix (epigraphBase z)) i j) :
    finiteDot (fun k ↦ (betheFloorCutNormal i j k : ℝ))
      (fun k ↦ z k -
        (((Fin.snoc y (0 : ℚ) : Fin (m * m + 1) → ℚ) k : ℚ) : ℝ)) < 0 := by
  let Yq : Matrix (Fin m) (Fin m) ℝ :=
    vectorToSquareMatrix (fun k ↦ (y k : ℝ))
  let Y : Matrix (Fin m) (Fin m) ℝ :=
    vectorToSquareMatrix (epigraphBase z)
  let Gq : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    fun a b ↦ (matrixEntryCovector i j a b : ℝ)
  have hadjoint := matrixPairing_affineMap_sub Gq Yq Y
  have hentry :
      birkhoffAffineMap Y i j - birkhoffAffineMap Yq i j =
        matrixPairing
          (affinePullbackGradient Gq) (fun a b ↦ Y a b - Yq a b) := by
    rw [← hadjoint]
    exact (matrixPairing_entryCovector i j
      (fun a b => birkhoffAffineMap Y a b - birkhoffAffineMap Yq a b)).symm
  have hqueryCast : birkhoffAffineMap Yq i j =
      (betheAffineMatrixQ y i j : ℝ) := by
    symm
    exact cast_betheAffineMatrixQ y i j
  have hstrict : 0 < birkhoffAffineMap Y i j - birkhoffAffineMap Yq i j := by
    rw [hqueryCast]
    have hbelowR : (betheAffineMatrixQ y i j : ℝ) < (δ : ℝ) := by
      exact_mod_cast hbelow
    linarith
  have hpullCast :
      (fun a b ↦
        ((affinePullbackGradient (matrixEntryCovector i j) a b : ℚ) : ℝ)) =
        affinePullbackGradient Gq := by
    ext a b
    simp [Gq, affinePullbackGradient, matrixEntryCovector]
  have hnormalCast :
      (fun k ↦ ((-squareMatrixToVector
        (affinePullbackGradient (matrixEntryCovector i j)) k : ℚ) : ℝ)) =
      fun k ↦ -squareMatrixToVector (affinePullbackGradient Gq) k := by
    ext k
    rw [Rat.cast_neg]
    congr 1
    have hk := congrFun (congrArg squareMatrixToVector hpullCast) k
    exact hk
  have hdotBase :
      finiteDot
        (fun k ↦ ((-squareMatrixToVector
          (affinePullbackGradient (matrixEntryCovector i j)) k : ℚ) : ℝ))
        (fun k ↦ epigraphBase z k - (y k : ℝ)) =
      -matrixPairing (affinePullbackGradient Gq)
        (fun a b ↦ Y a b - Yq a b) := by
    have hDvec : (fun k ↦ epigraphBase z k - (y k : ℝ)) =
        squareMatrixToVector (fun a b ↦ Y a b - Yq a b) := by
      ext k
      have hk : finProdFinEquiv (finProdFinEquiv.symm k) = k :=
        Equiv.apply_symm_apply finProdFinEquiv k
      change epigraphBase z k - (y k : ℝ) =
        epigraphBase z (finProdFinEquiv (finProdFinEquiv.symm k)) -
          (y (finProdFinEquiv (finProdFinEquiv.symm k)) : ℝ)
      rw [hk]
    rw [hDvec, hnormalCast]
    rw [finiteDot]
    simp_rw [neg_mul, Finset.sum_neg_distrib]
    rw [← finiteDot, finiteDot_squareMatrixToVector
      (affinePullbackGradient Gq) (fun a b => Y a b - Yq a b)]
  rw [finiteDot, Fin.sum_univ_castSucc]
  simp only [betheFloorCutNormal_castSucc, betheFloorCutNormal_last,
    Rat.cast_neg, Rat.cast_zero, zero_mul, add_zero, Fin.snoc_last,
    Fin.snoc_castSucc]
  rw [finiteDot] at hdotBase
  norm_num only [Rat.cast_neg] at hdotBase
  simp only [epigraphBase] at hdotBase
  rw [hdotBase, ← hentry]
  linarith

end BeyondBethe

/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Analytic.LocalBiholomorph
import LeanPool.LocalComplexGeometry.Germs.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Complex rank in finite-dimensional coordinate spaces

This file defines the complex rank of a continuous complex-linear map and the
standard rank-`r` coordinate map from `ℂⁿ` to `ℂᵐ`.  The latter is a total
definition for arbitrary `n`, `m`, and `r`; its rank is exactly `r` when
`r ≤ n` and `r ≤ m`.
-/


namespace LocalComplexGeometry

noncomputable section

/-- The complex dimension of the range of a continuous complex-linear map. -/
def complexRank {n m : ℕ}
    (A : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) : ℕ :=
  Module.finrank ℂ (LinearMap.range A.toLinearMap)

/-- Complex rank is bounded by the dimension of the source. -/
theorem complexRank_le_source {n m : ℕ}
    (A : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) :
    complexRank A ≤ n := by
  change Module.finrank ℂ (LinearMap.range A.toLinearMap) ≤ n
  simpa only [Module.finrank_fin_fun] using
    (LinearMap.finrank_range_le A.toLinearMap)

/-- Complex rank is bounded by the dimension of the target. -/
theorem complexRank_le_target {n m : ℕ}
    (A : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) :
    complexRank A ≤ m := by
  change Module.finrank ℂ (LinearMap.range A.toLinearMap) ≤ m
  simpa only [Module.finrank_fin_fun] using
    (LinearMap.range A.toLinearMap).finrank_le

/-- The standard rank map: retain a coordinate precisely when its index is
available in the source and is strictly less than `r`, and put zero elsewhere. -/
def standardRankContinuousLinearMap (n m r : ℕ) :
    ComplexEuclidean n →L[ℂ] ComplexEuclidean m :=
  ContinuousLinearMap.pi fun j ↦
    if h : j.1 < n ∧ j.1 < r then
      ContinuousLinearMap.proj (R := ℂ) (i := ⟨j.1, h.1⟩)
    else 0

/-- The underlying function of `standardRankContinuousLinearMap`. -/
def standardRankMap (n m r : ℕ) :
    ComplexEuclidean n → ComplexEuclidean m :=
  standardRankContinuousLinearMap n m r

@[simp]
theorem standardRankContinuousLinearMap_apply (n m r : ℕ)
    (x : ComplexEuclidean n) (j : Fin m) :
    standardRankContinuousLinearMap n m r x j =
      if h : j.1 < n ∧ j.1 < r then x ⟨j.1, h.1⟩ else 0 := by
  simp only [standardRankContinuousLinearMap, ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl

@[simp]
theorem standardRankMap_apply (n m r : ℕ)
    (x : ComplexEuclidean n) (j : Fin m) :
    standardRankMap n m r x j =
      if h : j.1 < n ∧ j.1 < r then x ⟨j.1, h.1⟩ else 0 := by
  simp [standardRankMap]

/-- Restrict a coordinate vector to its first `r` coordinates. -/
def takeFirstContinuousLinearMap {n r : ℕ} (hrn : r ≤ n) :
    ComplexEuclidean n →L[ℂ] ComplexEuclidean r :=
  ContinuousLinearMap.pi fun j ↦
    ContinuousLinearMap.proj (R := ℂ) (i := Fin.castLE hrn j)

@[simp]
theorem takeFirstContinuousLinearMap_apply {n r : ℕ} (hrn : r ≤ n)
    (x : ComplexEuclidean n) (j : Fin r) :
    takeFirstContinuousLinearMap hrn x j = x (Fin.castLE hrn j) :=
  rfl

/-- Extend an `r`-tuple by zero to an `m`-tuple. -/
def includeFirstContinuousLinearMap (m r : ℕ) :
    ComplexEuclidean r →L[ℂ] ComplexEuclidean m :=
  ContinuousLinearMap.pi fun j ↦
    if h : j.1 < r then
      ContinuousLinearMap.proj (R := ℂ) (i := ⟨j.1, h⟩)
    else 0

@[simp]
theorem includeFirstContinuousLinearMap_apply (m r : ℕ)
    (x : ComplexEuclidean r) (j : Fin m) :
    includeFirstContinuousLinearMap m r x j =
      if h : j.1 < r then x ⟨j.1, h⟩ else 0 := by
  simp only [includeFirstContinuousLinearMap, ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl

/-- Restriction to the first `r` coordinates is onto when `r ≤ n`. -/
theorem takeFirstContinuousLinearMap_surjective {n r : ℕ} (hrn : r ≤ n) :
    Function.Surjective (takeFirstContinuousLinearMap hrn) := by
  intro y
  let x : ComplexEuclidean n := fun i ↦
    if h : i.1 < r then y ⟨i.1, h⟩ else 0
  refine ⟨x, ?_⟩
  funext j
  simp [x, takeFirstContinuousLinearMap_apply]

/-- Zero-extension of the first `r` coordinates is injective when `r ≤ m`. -/
theorem includeFirstContinuousLinearMap_injective {m r : ℕ} (hrm : r ≤ m) :
    Function.Injective (includeFirstContinuousLinearMap m r) := by
  intro x y hxy
  funext j
  have h := congrFun hxy (Fin.castLE hrm j)
  simpa using h

/-- Under `r ≤ n`, the standard map factors as restriction to `ℂʳ`
followed by zero-extension. -/
theorem standardRankContinuousLinearMap_eq_comp {n m r : ℕ} (hrn : r ≤ n) :
    standardRankContinuousLinearMap n m r =
      (includeFirstContinuousLinearMap m r).comp
        (takeFirstContinuousLinearMap hrn) := by
  ext x j
  by_cases hj : j.1 < r
  · have hjn : j.1 < n := lt_of_lt_of_le hj hrn
    simp [standardRankContinuousLinearMap_apply,
      includeFirstContinuousLinearMap_apply,
      takeFirstContinuousLinearMap_apply, hj, hjn]
  · simp [standardRankContinuousLinearMap_apply,
      includeFirstContinuousLinearMap_apply, hj]

/-- The standard coordinate map has complex rank `r` whenever `r` fits in
both source and target.  This includes the zero-dimensional cases. -/
theorem complexRank_standardRankContinuousLinearMap {n m r : ℕ}
    (hrn : r ≤ n) (hrm : r ≤ m) :
    complexRank (standardRankContinuousLinearMap n m r) = r := by
  rw [standardRankContinuousLinearMap_eq_comp hrn]
  unfold complexRank
  rw [ContinuousLinearMap.toLinearMap_comp]
  rw [LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (takeFirstContinuousLinearMap_surjective hrn))]
  rw [LinearMap.finrank_range_of_inj
    (includeFirstContinuousLinearMap_injective hrm)]
  exact Module.finrank_fin_fun ℂ

/-- The Fréchet derivative of the standard coordinate map is the standard
continuous linear map itself. -/
@[simp]
theorem fderiv_standardRankMap (n m r : ℕ) (x : ComplexEuclidean n) :
    fderiv ℂ (standardRankMap n m r) x =
      standardRankContinuousLinearMap n m r := by
  simpa only [standardRankMap] using
    (standardRankContinuousLinearMap n m r).fderiv

/-- Pointwise formulation of the exact-rank calculation. -/
theorem complexRank_fderiv_standardRankMap {n m r : ℕ}
    (hrn : r ≤ n) (hrm : r ≤ m) (x : ComplexEuclidean n) :
    complexRank (fderiv ℂ (standardRankMap n m r) x) = r := by
  rw [fderiv_standardRankMap]
  exact complexRank_standardRankContinuousLinearMap hrn hrm

end

end LocalComplexGeometry

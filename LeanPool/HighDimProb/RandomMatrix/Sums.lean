/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomMatrix.SelfAdjoint

/-!
# Finite sums of random matrices

This leaf keeps finite matrix sums as explicit pointwise sums over `Finset.univ`.
It is separate from concentration statements so later matrix Bernstein
infrastructure can reuse the sum vocabulary without importing tail statements.
-/

namespace HighDimProb

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Pointwise sum of a finite family of random matrices. -/
def randomMatrixSum {Omega : Type*} {I : Type*}
    [Fintype I] {m n : Nat} (A : I -> RandomMatrix Omega m n) :
    RandomMatrix Omega m n :=
  fun omega => Finset.univ.sum fun i : I => A i omega

@[simp]
theorem randomMatrixSum_apply {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} [Fintype I] {m n : Nat}
    (A : I -> RandomMatrix Omega m n) (omega : Omega) :
    randomMatrixSum A omega = Finset.univ.sum fun i : I => A i omega :=
  rfl

@[simp]
theorem randomMatrixSum_entry {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} [Fintype I] {m n : Nat}
    (A : I -> RandomMatrix Omega m n) (omega : Omega)
    (r : Fin m) (c : Fin n) :
    randomMatrixSum A omega r c = Finset.univ.sum fun i : I => A i omega r c := by
  simpa [randomMatrixSum] using
    Matrix.sum_apply r c Finset.univ (fun i : I => A i omega)

/-! ## Fin-indexed prefix and suffix cuts -/

/-- Deterministic prefix sum of a finite comparison-matrix family.

For `k : Fin (m + 1)`, this sums the terms with index strictly less than
`k`. The endpoint `k = Fin.last m` is the full sum. -/
def comparisonMatrixPrefixSum {m n : Nat}
    (K : Fin m -> Matrix (Fin n) (Fin n) Real) (k : Fin (m + 1)) :
    Matrix (Fin n) (Fin n) Real :=
  (Finset.univ.filter fun i : Fin m => (i : Nat) < (k : Nat)).sum fun i => K i

/-- Deterministic suffix sum of a finite comparison-matrix family.

For `k : Fin (m + 1)`, this sums the terms with index at least `k`.
The endpoint `k = 0` is the full sum and `k = Fin.last m` is zero. -/
def comparisonMatrixSuffixSum {m n : Nat}
    (K : Fin m -> Matrix (Fin n) (Fin n) Real) (k : Fin (m + 1)) :
    Matrix (Fin n) (Fin n) Real :=
  (Finset.univ.filter fun i : Fin m => (k : Nat) <= (i : Nat)).sum fun i => K i

/-- Pointwise random-matrix prefix sum over a finite `Fin m` family. -/
def randomMatrixPrefixSum {Omega : Type*}
    {m n : Nat} (A : Fin m -> RandomMatrix Omega n n) (k : Fin (m + 1)) :
    RandomMatrix Omega n n :=
  fun omega => comparisonMatrixPrefixSum (fun i => A i omega) k

/-- Pointwise random-matrix suffix sum over a finite `Fin m` family. -/
def randomMatrixSuffixSum {Omega : Type*}
    {m n : Nat} (A : Fin m -> RandomMatrix Omega n n) (k : Fin (m + 1)) :
    RandomMatrix Omega n n :=
  fun omega => comparisonMatrixSuffixSum (fun i => A i omega) k

@[simp]
theorem randomMatrixPrefixSum_apply {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (A : Fin m -> RandomMatrix Omega n n) (k : Fin (m + 1))
    (omega : Omega) :
    randomMatrixPrefixSum A k omega =
      comparisonMatrixPrefixSum (fun i => A i omega) k :=
  rfl

@[simp]
theorem randomMatrixSuffixSum_apply {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (A : Fin m -> RandomMatrix Omega n n) (k : Fin (m + 1))
    (omega : Omega) :
    randomMatrixSuffixSum A k omega =
      comparisonMatrixSuffixSum (fun i => A i omega) k :=
  rfl

private theorem finset_univ_filter_lt_succ_eq_insert {m : Nat} (i : Fin m) :
    (Finset.univ.filter fun j : Fin m => (j : Nat) < (i.succ : Fin (m + 1))) =
      insert i (Finset.univ.filter fun j : Fin m =>
        (j : Nat) < (i.castSucc : Fin (m + 1))) := by
  classical
  ext j
  by_cases hji : j = i
  · subst hji
    simp
  · have hneVal : (j : Nat) ≠ (i : Nat) := by
      intro h
      exact hji (Fin.ext h)
    constructor
    · intro hj
      have hjltSucc : (j : Nat) < (i.succ : Fin (m + 1)) := by
        simpa using hj
      have hjle : (j : Nat) <= (i : Nat) := Nat.lt_succ_iff.mp hjltSucc
      have hjlt : (j : Nat) < (i : Nat) := Nat.lt_of_le_of_ne hjle hneVal
      simpa [hji] using hjlt
    · intro hj
      have hmem :
          j ∈ Finset.univ.filter
            (fun j : Fin m => (j : Nat) < (i.castSucc : Fin (m + 1))) := by
        simpa [hji] using hj
      have hjlt : (j : Nat) < (i : Nat) := by
        simpa using hmem
      simpa using Nat.lt_trans hjlt (Nat.lt_succ_self _)

private theorem finset_univ_filter_le_castSucc_eq_insert {m : Nat} (i : Fin m) :
    (Finset.univ.filter fun j : Fin m => (i.castSucc : Fin (m + 1)) <= (j : Nat)) =
      insert i (Finset.univ.filter fun j : Fin m =>
        (i.succ : Fin (m + 1)) <= (j : Nat)) := by
  classical
  ext j
  by_cases hji : j = i
  · subst hji
    simp
  · have hneVal : (i : Nat) ≠ (j : Nat) := by
      intro h
      exact hji (Fin.ext h.symm)
    constructor
    · intro hj
      have hle : (i : Nat) <= (j : Nat) := by
        simpa using hj
      have hlt : (i : Nat) < (j : Nat) := Nat.lt_of_le_of_ne hle hneVal
      have hsucc : (i : Nat) + 1 <= (j : Nat) := Nat.succ_le_iff.mpr hlt
      simpa [hji] using hsucc
    · intro hj
      have hmem :
          j ∈ Finset.univ.filter
            (fun j : Fin m => (i.succ : Fin (m + 1)) <= (j : Nat)) := by
        simpa [hji] using hj
      have hsucc : (i : Nat) + 1 <= (j : Nat) := by
        simpa using hmem
      simpa using Nat.le_trans (Nat.le_succ _) hsucc

@[simp]
theorem comparisonMatrixPrefixSum_zero {m n : Nat}
    (K : Fin m -> Matrix (Fin n) (Fin n) Real) :
    comparisonMatrixPrefixSum K 0 = 0 := by
  simp [comparisonMatrixPrefixSum]

@[simp]
theorem comparisonMatrixPrefixSum_last {m n : Nat}
    (K : Fin m -> Matrix (Fin n) (Fin n) Real) :
    comparisonMatrixPrefixSum K (Fin.last m) =
      Finset.univ.sum fun i : Fin m => K i := by
  simp [comparisonMatrixPrefixSum]

theorem comparisonMatrixPrefixSum_succ {m n : Nat}
    (K : Fin m -> Matrix (Fin n) (Fin n) Real) (i : Fin m) :
    comparisonMatrixPrefixSum K i.succ =
      comparisonMatrixPrefixSum K i.castSucc + K i := by
  classical
  rw [comparisonMatrixPrefixSum, comparisonMatrixPrefixSum,
    finset_univ_filter_lt_succ_eq_insert]
  simp [add_comm]

@[simp]
theorem comparisonMatrixSuffixSum_zero {m n : Nat}
    (K : Fin m -> Matrix (Fin n) (Fin n) Real) :
    comparisonMatrixSuffixSum K 0 =
      Finset.univ.sum fun i : Fin m => K i := by
  simp [comparisonMatrixSuffixSum]

@[simp]
theorem comparisonMatrixSuffixSum_last {m n : Nat}
    (K : Fin m -> Matrix (Fin n) (Fin n) Real) :
    comparisonMatrixSuffixSum K (Fin.last m) = 0 := by
  simp [comparisonMatrixSuffixSum, Nat.not_le_of_gt]

theorem comparisonMatrixSuffixSum_succ {m n : Nat}
    (K : Fin m -> Matrix (Fin n) (Fin n) Real) (i : Fin m) :
    comparisonMatrixSuffixSum K i.castSucc =
      K i + comparisonMatrixSuffixSum K i.succ := by
  classical
  rw [comparisonMatrixSuffixSum, comparisonMatrixSuffixSum,
    finset_univ_filter_le_castSucc_eq_insert]
  simp

@[simp]
theorem randomMatrixPrefixSum_zero {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (A : Fin m -> RandomMatrix Omega n n) :
    randomMatrixPrefixSum A 0 = 0 := by
  funext omega
  simp [randomMatrixPrefixSum]

theorem randomMatrixPrefixSum_last {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (A : Fin m -> RandomMatrix Omega n n) :
    randomMatrixPrefixSum A (Fin.last m) = randomMatrixSum A := by
  funext omega
  simp [randomMatrixPrefixSum, randomMatrixSum]

theorem randomMatrixSum_eq_prefixSum_last {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (A : Fin m -> RandomMatrix Omega n n) :
    randomMatrixSum A = randomMatrixPrefixSum A (Fin.last m) :=
  (randomMatrixPrefixSum_last A).symm

theorem randomMatrixPrefixSum_succ {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (A : Fin m -> RandomMatrix Omega n n) (i : Fin m) :
    randomMatrixPrefixSum A i.succ =
      fun omega => randomMatrixPrefixSum A i.castSucc omega + A i omega := by
  funext omega
  exact comparisonMatrixPrefixSum_succ (fun j => A j omega) i

theorem randomMatrixSuffixSum_zero {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (A : Fin m -> RandomMatrix Omega n n) :
    randomMatrixSuffixSum A 0 = randomMatrixSum A := by
  funext omega
  simp [randomMatrixSuffixSum, randomMatrixSum]

@[simp]
theorem randomMatrixSuffixSum_last {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (A : Fin m -> RandomMatrix Omega n n) :
    randomMatrixSuffixSum A (Fin.last m) = 0 := by
  funext omega
  simp [randomMatrixSuffixSum]

theorem randomMatrixSuffixSum_succ {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (A : Fin m -> RandomMatrix Omega n n) (i : Fin m) :
    randomMatrixSuffixSum A i.castSucc =
      fun omega => A i omega + randomMatrixSuffixSum A i.succ omega := by
  funext omega
  exact comparisonMatrixSuffixSum_succ (fun j => A j omega) i

/-- Finite sums of matrix-valued random variables are matrix-valued random variables. -/
theorem isRandomMatrix_sum {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {I : Type*} [Fintype I] {m n : Nat}
    {A : I -> RandomMatrix Omega m n}
    (hA : forall i, IsRandomMatrix P (A i)) :
    IsRandomMatrix P (randomMatrixSum A) := by
  intro r c
  dsimp [IsRealRandomVariable, IsRandomVariable, matrixEntry]
  change Measurable fun omega => randomMatrixSum A omega r c
  simpa [Matrix.sum_apply] using
    Finset.measurable_sum Finset.univ fun i _ => hA i r c

/-- A finite sum of self-adjoint deterministic matrices is self-adjoint. -/
theorem isSelfAdjointMatrix_sum {I : Type*} [Fintype I] {n : Nat}
    {A : I -> Matrix (Fin n) (Fin n) Real}
    (hA : forall i, IsSelfAdjointMatrix (A i)) :
    IsSelfAdjointMatrix (Finset.univ.sum fun i : I => A i) := by
  apply Matrix.IsHermitian.ext
  intro r c
  calc
    star ((Finset.univ.sum fun i : I => A i) c r)
        = Finset.univ.sum fun i : I => star (A i c r) := by
          rw [Matrix.sum_apply]
          simp
    _ = Finset.univ.sum fun i : I => A i r c := by
          exact Finset.sum_congr rfl fun i _ => Matrix.IsHermitian.apply (hA i) r c
    _ = (Finset.univ.sum fun i : I => A i) r c := by
          rw [Matrix.sum_apply]

/-- A finite pointwise sum of self-adjoint random matrices is self-adjoint. -/
theorem randomSelfAdjointMatrix_sum {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {I : Type*} [Fintype I] {n : Nat}
    {A : I -> RandomMatrix Omega n n}
    (hA : forall i, RandomSelfAdjointMatrix P (A i)) :
    RandomSelfAdjointMatrix P (randomMatrixSum A) := by
  intro omega
  exact isSelfAdjointMatrix_sum fun i => hA i omega

end

end HighDimProb

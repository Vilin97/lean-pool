/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import LeanPool.HighDimProb.Expectation
import LeanPool.HighDimProb.Lp
import LeanPool.HighDimProb.RandomMatrix.Basic

/-!
# Entrywise matrix expectation vocabulary

Verified Wikipedia references:
* Expected value: https://en.wikipedia.org/wiki/Expected_value
* Random matrix: https://en.wikipedia.org/wiki/Random_matrix

Matrix-valued expectations are represented entrywise.  A small bridge theorem
connects this entrywise API to Mathlib's Bochner integral for the scoped L2
operator-norm matrix structure when the matrix concentration proof layer needs
operator-norm contraction.
-/

namespace HighDimProb

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- Entrywise expectation of a random matrix. -/
def matrixExpect {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (P : Measure Omega) (A : RandomMatrix Omega m n) :
    Matrix (Fin m) (Fin n) Real :=
  fun i j => expect P (matrixEntry A i j)

/-- Entrywise integrability predicate for random matrices. -/
def IntegrableRandomMatrix {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (P : Measure Omega) (A : RandomMatrix Omega m n) : Prop :=
  forall i : Fin m, forall j : Fin n,
    IntegrableRealRandomVariable P (matrixEntry A i j)

private def matrixToPiContinuousLinearEquiv {m n : Nat} :
    Matrix (Fin m) (Fin n) Real ≃L[Real] (Fin m -> Fin n -> Real) :=
  let e : Matrix (Fin m) (Fin n) Real ≃ₗ[Real] (Fin m -> Fin n -> Real) :=
    { toFun := fun A => fun i => fun j => A i j
      invFun := fun f => fun i => fun j => f i j
      left_inv := by intro A; rfl
      right_inv := by intro f; rfl
      map_add' := by intro A B; rfl
      map_smul' := by intro c A; rfl }
  e.toContinuousLinearEquiv

private def matrixEntryCLM {m n : Nat} (i : Fin m) (j : Fin n) :
    Matrix (Fin m) (Fin n) Real →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A : Matrix (Fin m) (Fin n) Real => A i j
      map_add' := by intro A B; rfl
      map_smul' := by intro c A; rfl }

private theorem integrable_matrix_of_integrableRandomMatrix {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {m n : Nat}
    {A : RandomMatrix Omega m n} (hA : IntegrableRandomMatrix P A) :
    Integrable A P := by
  let toPi := matrixToPiContinuousLinearEquiv (m := m) (n := n)
  have hRows : forall i : Fin m, Integrable (fun omega => A omega i) P := by
    intro i
    apply Integrable.of_eval
    intro j
    exact hA i j
  have hEntries :
      Integrable (fun omega => fun i : Fin m => fun j : Fin n => A omega i j) P :=
    Integrable.of_eval hRows
  have hPi : Integrable (fun omega => toPi (A omega)) P := by
    simpa [toPi, matrixToPiContinuousLinearEquiv] using hEntries
  have hMatrix : Integrable (fun omega => toPi.symm (toPi (A omega))) P :=
    (ContinuousLinearEquiv.integrable_comp_iff (L := toPi.symm)).2 hPi
  simpa using hMatrix

@[simp]
theorem matrixExpect_apply {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (P : Measure Omega) (A : RandomMatrix Omega m n) (i : Fin m) (j : Fin n) :
    matrixExpect P A i j = expect P (matrixEntry A i j) :=
  rfl

/--
For a Bochner-integrable random matrix using Mathlib's scoped L2 operator-norm
matrix instance, the existing entrywise `matrixExpect` agrees with the
Bochner integral.

This is a bridge theorem only: it does not redefine expectation and does not
infer entrywise integrability from boundedness.
-/
theorem matrixExpect_eq_integral_l2Operator {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} {A : RandomMatrix Omega m n}
    (hA : Integrable A P) :
    matrixExpect P A = ∫ omega, A omega ∂P := by
  ext i j
  let evalIJ := matrixEntryCLM (m := m) (n := n) i j
  calc
    matrixExpect P A i j = ∫ omega, A omega i j ∂P := rfl
    _ = evalIJ (∫ omega, A omega ∂P) := by
          rw [← evalIJ.integral_comp_comm hA]
          rfl
    _ = (∫ omega, A omega ∂P) i j := rfl

/--
The existing entrywise `matrixExpect` agrees with Mathlib's Bochner integral
for the scoped L2 operator-norm matrix structure.

This is the entrywise-integrability bridge used by expectation contraction.
It does not redefine expectation and does not infer entrywise integrability
from boundedness.
-/
theorem matrixExpect_eq_integral {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} {A : RandomMatrix Omega m n}
    (hA : IntegrableRandomMatrix P A) :
    matrixExpect P A = ∫ omega, A omega ∂P :=
  matrixExpect_eq_integral_l2Operator (P := P) (A := A)
    (integrable_matrix_of_integrableRandomMatrix (P := P) (A := A) hA)

/-- Entrywise centered random matrix `A - E A`. -/
def centeredRandomMatrix {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (P : Measure Omega) (A : RandomMatrix Omega m n) :
    RandomMatrix Omega m n :=
  fun omega i j => A omega i j - matrixExpect P A i j

@[simp]
theorem centeredRandomMatrix_apply {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (P : Measure Omega) (A : RandomMatrix Omega m n)
    (omega : Omega) (i : Fin m) (j : Fin n) :
    centeredRandomMatrix P A omega i j = A omega i j - matrixExpect P A i j :=
  rfl

/-- Centering a random matrix preserves entrywise measurability. -/
theorem isRandomMatrix_centeredRandomMatrix {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} {A : RandomMatrix Omega m n}
    (hA : IsRandomMatrix P A) :
    IsRandomMatrix P (centeredRandomMatrix P A) := by
  intro i j
  dsimp [IsRealRandomVariable, IsRandomVariable, matrixEntry, centeredRandomMatrix]
  exact (hA i j).sub measurable_const

/-- Centering a random matrix preserves entrywise integrability over a finite measure. -/
theorem integrableRandomMatrix_centeredRandomMatrix {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsFiniteMeasure P]
    {m n : Nat} {A : RandomMatrix Omega m n}
    (hA : IntegrableRandomMatrix P A) :
    IntegrableRandomMatrix P (centeredRandomMatrix P A) := by
  intro i j
  dsimp [IntegrableRealRandomVariable, IntegrableRandomVariable, matrixEntry,
    centeredRandomMatrix, matrixExpect, expect]
  exact (hA i j).sub (integrable_const _)

/-- Indexed family obtained by centering every random matrix in a family. -/
def centeredRandomMatrixFamily {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} {m n : Nat} (P : Measure Omega)
    (A : I -> RandomMatrix Omega m n) :
    I -> RandomMatrix Omega m n :=
  centeredRandomMatrix P ∘ A

@[simp]
theorem centeredRandomMatrixFamily_apply {Omega : Type*}
    [MeasurableSpace Omega] {I : Type*} {m n : Nat}
    (P : Measure Omega) (A : I -> RandomMatrix Omega m n) (i : I) :
    centeredRandomMatrixFamily P A i = centeredRandomMatrix P (A i) :=
  rfl

/--
Named centered rank-one random matrix adapter.

This packages `centeredRandomMatrix P (rankOneRandomMatrix X)` as a reusable
object-level API for covariance-style examples and Matrix Bernstein
prerequisites.
-/
def centeredRankOneRandomMatrix {Omega : Type*} [MeasurableSpace Omega]
    {n : Nat} (P : Measure Omega) (X : RandomVector Omega n) :
    RandomMatrix Omega n n :=
  centeredRandomMatrix P (rankOneRandomMatrix X)

@[simp]
theorem centeredRankOneRandomMatrix_apply {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (X : RandomVector Omega n) (omega : Omega) (i j : Fin n) :
    centeredRankOneRandomMatrix P X omega i j =
      X omega i * X omega j - matrixExpect P (rankOneRandomMatrix X) i j :=
  rfl

/--
Indexed family of centered rank-one random matrices.

This names the family-level adapter so public theorem statements and example
code can use a stable API instead of spelling out the inline family.
-/
def centeredRankOneRandomMatrixFamily {Omega : Type*}
    [MeasurableSpace Omega] {I : Type*} {n : Nat} (P : Measure Omega)
    (X : I -> RandomVector Omega n) :
    I -> RandomMatrix Omega n n :=
  centeredRandomMatrixFamily P (rankOneRandomMatrixFamily X)

@[simp]
theorem centeredRankOneRandomMatrixFamily_apply {Omega : Type*}
    [MeasurableSpace Omega] {I : Type*} {P : Measure Omega} {n : Nat}
    (X : I -> RandomVector Omega n) (i : I) :
    centeredRankOneRandomMatrixFamily P X i =
      centeredRankOneRandomMatrix P (X i) :=
  rfl

/-- The entrywise expectation of a centered integrable random matrix is zero. -/
theorem matrixExpect_centeredRandomMatrix {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P] {m n : Nat}
    {A : RandomMatrix Omega m n} (hA : IntegrableRandomMatrix P A) :
    matrixExpect P (centeredRandomMatrix P A) = 0 := by
  ext i j
  change
    (∫ omega, matrixEntry A i j omega -
      (∫ omega, matrixEntry A i j omega ∂P) ∂P) = 0
  rw [integral_sub (hA i j)
    (integrable_const (∫ omega, matrixEntry A i j omega ∂P))]
  rw [integral_const]
  rw [measureReal_def]
  rw [measure_univ]
  rw [ENNReal.toReal_one]
  rw [one_smul]
  rw [sub_self]

/--
Rank-one self outer products are entrywise integrable when every coordinate
product is explicitly integrable.

Formula reference: integrability is separate from measurability for Lebesgue
integration; see https://en.wikipedia.org/wiki/Lebesgue_integration .  This
bridge deliberately assumes product integrability and does not infer it from
random-vector measurability alone.
-/
theorem integrableRandomMatrix_rankOneRandomMatrix_of_integrable_products
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    {X : RandomVector Omega n}
    (hProd : forall i : Fin n, forall j : Fin n,
      IntegrableRealRandomVariable P (fun omega => X omega i * X omega j)) :
    IntegrableRandomMatrix P (rankOneRandomMatrix X) := by
  intro i j
  change IntegrableRealRandomVariable P (fun omega => X omega i * X omega j)
  exact hProd i j

/--
Square-moment coordinates give entrywise integrability of the rank-one
outer-product random matrix.

Formula reference: entries of the outer product are `X_i * X_j`; see
https://en.wikipedia.org/wiki/Outer_product .  The proof reuses Mathlib's
`MemLp.integrable_mul`, so the second-moment hypothesis is explicit rather than
hidden inside the random-vector measurability predicate.
-/
theorem integrableRandomMatrix_rankOneRandomMatrix_of_memLp_two
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    {X : RandomVector Omega n}
    (hX : forall i : Fin n, MemLpRealRandomVariable P (coord X i) 2) :
    IntegrableRandomMatrix P (rankOneRandomMatrix X) := by
  apply integrableRandomMatrix_rankOneRandomMatrix_of_integrable_products
  intro i j
  change Integrable ((coord X i) * (coord X j)) P
  exact (hX i).integrable_mul (hX j)

end

end HighDimProb

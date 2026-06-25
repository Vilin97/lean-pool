/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomMatrix.VarianceProxy
import LeanPool.HighDimProb.RandomMatrix.Assumptions

/-!
# Centered self-adjoint closure usage example

This examples-only file shows the deterministic closure step behind centered
random matrix summands. The public RandomMatrix API now proves that centering
preserves entrywise measurability, entrywise integrability, pointwise
self-adjointness, and zero entrywise expectation for integrable
self-adjoint families.
-/

namespace HighDimProb.Examples.RandomMatrix.CenteredSelfAdjointClosureUsage

open MeasureTheory

noncomputable section

/-- The public API supplies self-adjointness of centered summands. -/
theorem randomSelfAdjointMatrix_centeredRandomMatrix_example
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    {X : RandomMatrix Omega n n}
    (hX : RandomSelfAdjointMatrix P X) :
    RandomSelfAdjointMatrix P (centeredRandomMatrix P X) := by
  exact randomSelfAdjointMatrix_centeredRandomMatrix hX

/-- The public API supplies zero expectation of centered integrable summands. -/
theorem matrixExpect_centeredRandomMatrix_zero_example
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {n : Nat} {X : RandomMatrix Omega n n}
    (hInt : IntegrableRandomMatrix P X) :
    matrixExpect P (centeredRandomMatrix P X) = 0 := by
  exact matrixExpect_centeredRandomMatrix hInt

/-- Family version of the centered self-adjoint closure route. -/
theorem centeredRandomMatrix_family_centeredSelfAdjoint_example
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} {n : Nat}
    (X : I -> RandomMatrix Omega n n)
    (hSelfAdjoint : SelfAdjointRandomMatrixFamily P X)
    (hInt : forall i, IntegrableRandomMatrix P (X i)) :
    CenteredSelfAdjointRandomMatrixFamily P
      (centeredRandomMatrixFamily P X) := by
  exact centeredSelfAdjointRandomMatrixFamily_centeredRandomMatrixFamily
    hSelfAdjoint hInt

/-- Example-local assumption package for centered self-adjoint closure. -/
structure CenteredSelfAdjointClosureAssumptions {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {I : Type*} {n : Nat}
    (X : I -> RandomMatrix Omega n n) : Prop where
  selfAdjointFamily : SelfAdjointRandomMatrixFamily P X
  integrable : forall i, IntegrableRandomMatrix P (X i)

/-- The local assumption package supplies the Matrix Bernstein centered
self-adjoint family predicate for centered summands. -/
theorem centeredSelfAdjointFamily_of_closure_assumptions
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} {n : Nat}
    (X : I -> RandomMatrix Omega n n)
    (h : CenteredSelfAdjointClosureAssumptions (P := P) X) :
    CenteredSelfAdjointRandomMatrixFamily P
      (centeredRandomMatrixFamily P X) := by
  exact centeredSelfAdjointRandomMatrixFamily_centeredRandomMatrixFamily
    h.selfAdjointFamily h.integrable

end

end HighDimProb.Examples.RandomMatrix.CenteredSelfAdjointClosureUsage

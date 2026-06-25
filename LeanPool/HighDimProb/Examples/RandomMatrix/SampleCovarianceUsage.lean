/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomMatrix.Algebra
import LeanPool.HighDimProb.RandomMatrix.ConcentrationStatements

/-!
# Sample covariance usage example

This examples-only file records structural sample-covariance facts already
available from the RandomMatrix API. The centered bridge is an algebraic
deviation identity, not a concentration theorem.
-/

namespace HighDimProb.Examples.RandomMatrix.SampleCovarianceUsage

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Data matrix vocabulary for rows-as-samples examples. -/
abbrev DataMatrix (Omega : Type*) (m n : Nat) :=
  RandomMatrix Omega m n

/-- The Gram entry is the finite row sum already exposed by the core API. -/
theorem gramMatrixEntry_usage {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (A : DataMatrix Omega m n) (omega : Omega)
    (i j : Fin n) :
    gramMatrixEntry A i j omega =
      Finset.univ.sum fun k : Fin m => A omega k i * A omega k j := by
  rfl

/-- Sample covariance entries are normalized Gram entries. -/
theorem sampleCovarianceEntry_usage {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (A : DataMatrix Omega m n) (omega : Omega)
    (i j : Fin n) :
    sampleCovariance A omega i j =
      (1 / (m : Real)) *
        Finset.univ.sum fun k : Fin m => A omega k i * A omega k j := by
  rfl

/-- Existing API: the uncentered sample covariance is the normalized row
rank-one sum. -/
theorem sampleCovariance_rankOneSum_usage {Omega : Type*}
    [MeasurableSpace Omega] {m n : Nat} (A : DataMatrix Omega m n) :
    sampleCovariance A = normalizedSampleCovarianceRowRankOneSum A := by
  exact sampleCovariance_eq_normalized_rowRankOne_sum A

/-- Existing API: the centered sample covariance is the normalized centered row
rank-one sum under explicit row rank-one integrability. -/
theorem sampleCovariance_centeredRankOneSum_usage {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {m n : Nat}
    (A : DataMatrix Omega m n)
    (hInt : forall k : Fin m,
      IntegrableRandomMatrix P (rankOneRandomMatrix (rowVector A k))) :
    centeredRandomMatrix P (sampleCovariance A) =
      normalizedCenteredSampleCovarianceRowRankOneSum (P := P) A := by
  exact sampleCovariance_deviation_eq_normalized_centered_rowRankOne_sum A hInt

/-- Existing API: sample-covariance entries are measurable when the data matrix
is entrywise measurable. -/
theorem sampleCovarianceEntry_isRealRandomVariable_usage
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {m n : Nat} {A : DataMatrix Omega m n}
    (hA : IsRandomMatrix P A) (i j : Fin n) :
    IsRealRandomVariable P (sampleCovarianceEntry A i j) := by
  exact isRealRandomVariable_sampleCovarianceEntry hA i j

/-- Existing API: quadratic forms of the uncentered sample covariance are sums
of squared row projections. -/
theorem sampleCovariance_quadraticForm_usage {Omega : Type*}
    [MeasurableSpace Omega] {m n : Nat} (A : DataMatrix Omega m n)
    (x : Fin n -> Real) (omega : Omega) :
    quadraticForm (sampleCovariance A) x omega =
      (1 / (m : Real)) *
        Finset.univ.sum (fun k : Fin m => (rowDot A x k omega) ^ 2) := by
  exact quadraticForm_sampleCovariance_eq_scaled_sum_rowDot_sq A x omega

/-- Existing API: sample covariance has nonnegative quadratic forms. -/
theorem sampleCovariance_quadraticForm_nonneg_usage {Omega : Type*}
    [MeasurableSpace Omega] {m n : Nat} (A : DataMatrix Omega m n)
    (x : Fin n -> Real) (omega : Omega) :
    0 <= quadraticForm (sampleCovariance A) x omega := by
  exact quadraticForm_sampleCovariance_nonneg A x omega

/-- Existing API: sample covariance is pointwise PSD. -/
theorem sampleCovariance_psd_usage {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (A : DataMatrix Omega m n) (omega : Omega) :
    IsPSDMatrix (sampleCovariance A omega) := by
  exact isPSD_sampleCovariance A omega

/-- Existing API: sample covariance is a random PSD matrix. -/
theorem sampleCovariance_randomPSD_usage {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {m n : Nat}
    (A : DataMatrix Omega m n) :
    RandomPSDMatrix P (sampleCovariance A) := by
  exact randomPSDMatrix_sampleCovariance A

end

end HighDimProb.Examples.RandomMatrix.SampleCovarianceUsage

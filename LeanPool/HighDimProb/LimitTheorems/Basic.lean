/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Scalar

/-!
# Basic vocabulary for limit theorems

This module contains finite-sample scalar vocabulary used by weak-law
statements. It intentionally avoids independence and asymptotic theorem proofs.

Verified Wikipedia reference:
* Sample mean and covariance:
  https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/

namespace HighDimProb

open MeasureTheory
open scoped BigOperators

noncomputable section

/--
Finite sample sum indexed by `Fin n`.

Formula reference: sample means are built from finite sums of observations;
see https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
def sampleSum {Omega : Type*} {n : Nat}
    (X : Fin n -> RealRandomVariable Omega) : RealRandomVariable Omega :=
  fun omega => Finset.univ.sum fun i : Fin n => X i omega

/--
Finite sample mean indexed by `Fin n`, using Lean's total division when `n = 0`.

Formula reference: the sample mean is the normalized sum of sample values; see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
def sampleMean {Omega : Type*} {n : Nat}
    (X : Fin n -> RealRandomVariable Omega) : RealRandomVariable Omega :=
  fun omega => (1 / (n : Real)) * Finset.univ.sum fun i : Fin n => X i omega

/--
Sample mean centered around a specified scalar `mu`.

Formula reference: centered sample quantities subtract the reference mean from
the sample mean; see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
def sampleMeanCentered {Omega : Type*} {n : Nat}
    (X : Fin n -> RealRandomVariable Omega) (mu : Real) : RealRandomVariable Omega :=
  fun omega => sampleMean X omega - mu

/--
Formula reference: this unfolds the finite-sample sum formula; see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
@[simp]
theorem sampleSum_apply {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (X : Fin n -> RealRandomVariable Omega) (omega : Omega) :
    sampleSum X omega = Finset.univ.sum fun i : Fin n => X i omega :=
  rfl

/--
Formula reference: this unfolds the sample mean as `(1 / n)` times the finite
sum; see https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
@[simp]
theorem sampleMean_apply {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (X : Fin n -> RealRandomVariable Omega) (omega : Omega) :
    sampleMean X omega =
      (1 / (n : Real)) * Finset.univ.sum fun i : Fin n => X i omega :=
  rfl

/--
Formula reference: this unfolds the centered sample mean formula
`sampleMean X - mu`; see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
@[simp]
theorem sampleMeanCentered_apply {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (X : Fin n -> RealRandomVariable Omega) (mu : Real) (omega : Omega) :
    sampleMeanCentered X mu omega = sampleMean X omega - mu :=
  rfl

/--
A finite sample sum of real random variables is a real random variable.

Formula reference: finite sample sums are measurable random quantities used to
form sample means; see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
theorem isRealRandomVariable_sampleSum {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {n : Nat} {X : Fin n -> RealRandomVariable Omega}
    (hX : forall i : Fin n, IsRealRandomVariable P (X i)) :
    IsRealRandomVariable P (sampleSum X) := by
  dsimp [IsRealRandomVariable, IsRandomVariable, sampleSum]
  exact Finset.measurable_sum _ fun i _ => hX i

/--
A finite sample mean of real random variables is a real random variable.

Formula reference: this is the random-variable condition for the normalized
sample sum; see https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
theorem isRealRandomVariable_sampleMean {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {n : Nat} {X : Fin n -> RealRandomVariable Omega}
    (hX : forall i : Fin n, IsRealRandomVariable P (X i)) :
    IsRealRandomVariable P (sampleMean X) := by
  dsimp [IsRealRandomVariable, IsRandomVariable, sampleMean]
  exact (Finset.measurable_sum _ fun i _ => hX i).const_mul _

/--
A sample mean centered around a scalar is a real random variable.

Formula reference: centering subtracts a scalar reference mean from the sample
mean; see https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
theorem isRealRandomVariable_sampleMeanCentered {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {n : Nat} {X : Fin n -> RealRandomVariable Omega} {mu : Real}
    (hX : forall i : Fin n, IsRealRandomVariable P (X i)) :
    IsRealRandomVariable P (sampleMeanCentered X mu) := by
  dsimp [IsRealRandomVariable, IsRandomVariable, sampleMeanCentered]
  exact (isRealRandomVariable_sampleMean (P := P) (X := X) hX).sub measurable_const

/--
A finite sample sum of integrable real random variables is integrable.

Formula reference: sample means and sums are finite linear combinations of
sample variables; see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
theorem integrable_sampleSum {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {n : Nat} {X : Fin n -> RealRandomVariable Omega}
    (hX : forall i : Fin n, IntegrableRealRandomVariable P (X i)) :
    IntegrableRealRandomVariable P (sampleSum X) := by
  dsimp [IntegrableRealRandomVariable, IntegrableRandomVariable, sampleSum]
  exact integrable_finsetSum Finset.univ fun i _ => hX i

/--
A finite sample mean of integrable real random variables is integrable.

Formula reference: the sample mean is a finite normalized sum; see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
theorem integrable_sampleMean {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {n : Nat} {X : Fin n -> RealRandomVariable Omega}
    (hX : forall i : Fin n, IntegrableRealRandomVariable P (X i)) :
    IntegrableRealRandomVariable P (sampleMean X) := by
  dsimp [IntegrableRealRandomVariable, IntegrableRandomVariable, sampleMean]
  exact (integrable_finsetSum Finset.univ fun i _ => hX i).const_mul _

/--
Centering a finite sample mean around a scalar preserves integrability over finite measures.

Formula reference: this is the integrability analogue of subtracting a
reference mean from the sample mean; see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
theorem integrable_sampleMeanCentered {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsFiniteMeasure P] {n : Nat}
    {X : Fin n -> RealRandomVariable Omega} {mu : Real}
    (hX : forall i : Fin n, IntegrableRealRandomVariable P (X i)) :
    IntegrableRealRandomVariable P (sampleMeanCentered X mu) := by
  dsimp [IntegrableRealRandomVariable, IntegrableRandomVariable, sampleMeanCentered]
  exact (integrable_sampleMean (P := P) (X := X) hX).sub (integrable_const mu)

end

end HighDimProb

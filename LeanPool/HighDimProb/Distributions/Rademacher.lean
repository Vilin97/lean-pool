/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Concentration.MGF
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Canonical Rademacher variable

This file provides the minimal distribution-level atom needed before finite
Rademacher-sum and Hoeffding-style stages: the symmetric Rademacher variable on
`Bool`, with the uniform Bernoulli measure.

Verified Wikipedia reference:
* Rademacher distribution:
  https://en.wikipedia.org/wiki/Rademacher_distribution
-/

namespace HighDimProb

open MeasureTheory ProbabilityTheory

noncomputable section

/--
The symmetric Bernoulli PMF on `Bool`.

Formula reference: the Rademacher distribution assigns probability `1 / 2`
to each of `-1` and `+1`; see
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
def rademacherPMF : PMF Bool :=
  PMF.ofFintype
    (fun b => cond b ((1 / 2 : NNReal) : ENNReal) ((1 / 2 : NNReal) : ENNReal))
    (by
      rw [Fintype.sum_bool]
      simp only [cond_true, cond_false]
      rw [← ENNReal.coe_add]
      norm_num)

/--
The canonical probability measure for a symmetric Rademacher variable.

Formula reference: this is the measure-level version of the symmetric
two-point mass function on `{ -1, +1 }`; see
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
def rademacherMeasure : Measure Bool :=
  rademacherPMF.toMeasure

/--
Formula reference: the Rademacher PMF has total mass `1`, giving a probability
measure; see https://en.wikipedia.org/wiki/Rademacher_distribution
-/
instance instIsProbabilityMeasure_rademacherMeasure :
    IsProbabilityMeasure rademacherMeasure :=
  PMF.toMeasure.isProbabilityMeasure _

/--
The canonical Rademacher random variable on `Bool`: `true -> 1`, `false -> -1`.

Formula reference: a Rademacher variate takes values `+1` and `-1` with equal
probability; see https://en.wikipedia.org/wiki/Rademacher_distribution
-/
def rademacher : RealRandomVariable Bool :=
  fun b => if b then (1 : Real) else -1

/--
The canonical Rademacher variable is measurable.

Formula reference: measurability is the Lean-side random-variable condition
for the two-point Rademacher variate described at
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem isRealRandomVariable_rademacher :
    IsRealRandomVariable rademacherMeasure rademacher := by
  unfold IsRealRandomVariable IsRandomVariable rademacher
  fun_prop

/--
The canonical Rademacher variable is pointwise contained in `[-1, 1]`.

Formula reference: the support is exactly `{ -1, +1 }`, hence lies in
`[-1, 1]`; see https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem rademacher_mem_Icc (b : Bool) :
    Set.Icc (-1 : Real) 1 (rademacher b) := by
  have hval : Or (rademacher b = 1) (rademacher b = -1) := by
    cases b <;> simp [rademacher]
  rcases hval with hval | hval
  · rw [hval]
    constructor <;> norm_num
  · rw [hval]
    constructor <;> norm_num

/--
The canonical Rademacher variable has mean zero.

Formula reference: Wikipedia lists the Rademacher mean as `0`; see
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem integral_rademacher :
    MeasureTheory.integral rademacherMeasure rademacher = 0 := by
  unfold rademacherMeasure rademacherPMF rademacher
  rw [PMF.integral_eq_sum]
  simp [PMF.ofFintype_apply]

/--
The canonical symmetric Rademacher variable is centered subGaussian in the MGF
sense with scale `1`.

This uses Mathlib's bounded zero-mean MGF lemma with interval `[-1, 1]`.

Formula reference: Wikipedia lists the Rademacher MGF as `cosh(t)` and records
Rademacher-sum concentration inequalities; see
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem centeredSubGaussianMGF_rademacher :
    CenteredSubGaussianMGF rademacherMeasure rademacher 1 := by
  have hm : AEMeasurable rademacher rademacherMeasure := by
    exact isRealRandomVariable_rademacher.aemeasurable
  have hb :
      Filter.Eventually
        (fun b => Set.Icc (-1 : Real) 1 (rademacher b)) (ae rademacherMeasure) := by
    exact ae_of_all rademacherMeasure rademacher_mem_Icc
  have hsub :=
    ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (X := rademacher) (a := (-1 : Real)) (b := 1) hm hb integral_rademacher
  exact And.intro zero_lt_one (by
    convert hsub using 1
    ext
    norm_num [Real.norm_eq_abs]
    rfl)

/--
The canonical Rademacher variable satisfies the existing two-sided
subGaussian-tail predicate with scale `2`, by composition through the MGF
bridge.

Formula reference: Rademacher variables are the canonical bounded signs used
in Rademacher-sum concentration bounds; see
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem subGaussianTail_rademacher :
    SubGaussianTail rademacherMeasure rademacher 2 := by
  simpa using
    (subGaussianTail_of_centeredSubGaussianMGF
      isRealRandomVariable_rademacher centeredSubGaussianMGF_rademacher)

end

end HighDimProb

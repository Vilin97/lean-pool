/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Distributions.Rademacher
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProductMeasure

/-!
# Finite Rademacher families

This file provides the finite product probability space for independent
canonical Rademacher signs indexed by `Fin n`.

Verified Wikipedia reference:
* Rademacher distribution:
  https://en.wikipedia.org/wiki/Rademacher_distribution
-/

namespace HighDimProb

open MeasureTheory ProbabilityTheory

noncomputable section

/--
Product probability measure for `n` independent canonical Rademacher signs.

Formula reference: this is the finite independent product version of signs
taking `-1` and `+1` with probability `1 / 2`; see
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
def rademacherVectorMeasure (n : ℕ) : Measure (Fin n → Bool) :=
  Measure.pi fun _ : Fin n => rademacherMeasure

/--
Formula reference: each coordinate is a probability measure for a Rademacher
sign, so the finite product is a probability measure; see
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
instance instIsProbabilityMeasure_rademacherVectorMeasure (n : ℕ) :
    IsProbabilityMeasure (rademacherVectorMeasure n) := by
  unfold rademacherVectorMeasure
  infer_instance

/--
The PMF corresponding to the finite Rademacher product measure.

The measure, not the PMF, is the primary proof object because Mathlib's
coordinate-independence theorem is stated for `Measure.pi`.

Formula reference: this PMF packages independent Rademacher coordinates,
matching the sums of independent Rademacher variables discussed at
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
def rademacherVectorPMF (n : ℕ) : PMF (Fin n → Bool) :=
  (rademacherVectorMeasure n).toPMF

/--
The PMF representation induces the finite Rademacher product measure.

Formula reference: this identifies the PMF and measure views of the same
finite independent Rademacher family; see
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem rademacherVectorPMF_toMeasure (n : ℕ) :
    (rademacherVectorPMF n).toMeasure = rademacherVectorMeasure n := by
  unfold rademacherVectorPMF
  exact Measure.toPMF_toMeasure (rademacherVectorMeasure n)

/--
The `i`th coordinate Rademacher random variable on the finite product space.

Formula reference: each coordinate is one Rademacher variate, taking values
`-1` and `+1`; see https://en.wikipedia.org/wiki/Rademacher_distribution
-/
def rademacherCoord {n : ℕ} (i : Fin n) :
    RealRandomVariable (Fin n → Bool) :=
  fun ω => rademacher (ω i)

/--
The full coordinate Rademacher vector on the finite product space.

Formula reference: this is the vector of independent Rademacher signs used in
Rademacher-sum formulas; see
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
def rademacherVector (n : ℕ) : (Fin n → Bool) → Fin n → ℝ :=
  fun ω i => rademacher (ω i)

/--
Formula reference: coordinate evaluation recovers the corresponding
Rademacher sign; see https://en.wikipedia.org/wiki/Rademacher_distribution
-/
@[simp]
theorem rademacherVector_apply {n : ℕ} (ω : Fin n → Bool) (i : Fin n) :
    rademacherVector n ω i = rademacherCoord i ω :=
  rfl

/--
Every coordinate Rademacher variable is measurable.

Formula reference: each coordinate is a random variate with the Rademacher
distribution; see https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem isRealRandomVariable_rademacherCoord {n : ℕ} (i : Fin n) :
    IsRealRandomVariable (rademacherVectorMeasure n) (rademacherCoord i) := by
  unfold IsRealRandomVariable IsRandomVariable rademacherCoord rademacher
  fun_prop

/--
Coordinate Rademacher variables are pointwise contained in `[-1, 1]`.

Formula reference: the support of each Rademacher coordinate is `{ -1, +1 }`;
see https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem rademacherCoord_mem_Icc {n : ℕ} (i : Fin n) (ω : Fin n → Bool) :
    Set.Icc (-1 : ℝ) 1 (rademacherCoord i ω) :=
  rademacher_mem_Icc (ω i)

/--
Each coordinate Rademacher variable has mean zero.

Formula reference: Wikipedia lists the Rademacher mean as `0`; see
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem integral_rademacherCoord {n : ℕ} (i : Fin n) :
    MeasureTheory.integral (rademacherVectorMeasure n) (rademacherCoord i) = 0 := by
  unfold rademacherVectorMeasure rademacherCoord
  have hmp :
      MeasurePreserving
        (fun ω : Fin n → Bool => ω i)
        (Measure.pi fun _ : Fin n => rademacherMeasure)
        rademacherMeasure := by
    simpa using
      (measurePreserving_eval (fun _ : Fin n => rademacherMeasure) i)
  calc
    MeasureTheory.integral (Measure.pi fun _ : Fin n => rademacherMeasure)
        (fun ω : Fin n → Bool => rademacher (ω i))
        = MeasureTheory.integral
            (Measure.map (fun ω : Fin n → Bool => ω i)
              (Measure.pi fun _ : Fin n => rademacherMeasure))
            rademacher := by
          exact
            (MeasureTheory.integral_map
              (φ := fun ω : Fin n → Bool => ω i)
              (μ := Measure.pi fun _ : Fin n => rademacherMeasure)
              (f := rademacher) hmp.aemeasurable (by
                rw [hmp.map_eq]
                exact isRealRandomVariable_rademacher.aestronglyMeasurable)).symm
    _ = MeasureTheory.integral rademacherMeasure rademacher := by
          rw [hmp.map_eq]
    _ = 0 := integral_rademacher

/--
The finite coordinate Rademacher family is independent under the product measure.

Formula reference: this supplies the independence assumption behind
Rademacher-sum concentration inequalities; see
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem iIndepFun_rademacherCoord (n : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun i : Fin n => rademacherCoord i) (rademacherVectorMeasure n) := by
  unfold rademacherVectorMeasure rademacherCoord
  exact
    ProbabilityTheory.iIndepFun_pi
      (μ := fun _ : Fin n => rademacherMeasure)
      (X := fun _ : Fin n => rademacher)
      (fun _ => isRealRandomVariable_rademacher.aemeasurable)

end

end HighDimProb

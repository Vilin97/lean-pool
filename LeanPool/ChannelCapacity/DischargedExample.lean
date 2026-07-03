/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.ChannelCapacity.Discharged
import LeanPool.ChannelCapacity.Finite

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# ChannelCapacity.DischargedExample

Worked example for the discharged capacity theorem.

This file builds a concrete positive full-rank `Fin 2 → Fin 2` channel with counting-measure
reference, instantiates `Kernel.ContinuousPositiveDensity`, and applies
`exists_unique_capacity_achieving_prior_discharged`.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal NNReal

namespace ChannelCapacity.DischargedExample

private lemma threeQuarter_add_oneQuarter :
    (3 / 4 : ℝ≥0∞) + 1 / 4 = 1 := by
  have h : ((3 / 4 : ℝ≥0) + 1 / 4 : ℝ≥0) = 1 := by
    norm_num
  exact (by simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h)

private lemma oneQuarter_add_threeQuarter :
    (1 / 4 : ℝ≥0∞) + 3 / 4 = 1 := by
  simpa [add_comm] using threeQuarter_add_oneQuarter

/-- The two rows of the `2 × 2` channel as probability mass functions on `Fin 2`
(mass `3/4` on the matching output, `1/4` on the other). -/
noncomputable def twoByTwoRowPMF : Fin 2 → PMF (Fin 2)
  | 0 => PMF.ofFintype (fun
      | 0 => (3 / 4 : ℝ≥0∞)
      | _ => (1 / 4 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_two] using threeQuarter_add_oneQuarter)
  | _ => PMF.ofFintype (fun
      | 0 => (1 / 4 : ℝ≥0∞)
      | _ => (3 / 4 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_two] using oneQuarter_add_threeQuarter)

/-- The two channel rows as probability measures on `Fin 2`. -/
noncomputable def twoByTwoRows (i : Fin 2) : ProbabilityMeasure (Fin 2) :=
  ⟨(twoByTwoRowPMF i).toMeasure, by infer_instance⟩

@[simp]
lemma twoByTwoRows_apply_singleton (i j : Fin 2) :
    (twoByTwoRows i).toMeasure {j} = twoByTwoRowPMF i j := by
  simp [twoByTwoRows]

/-- The `2 × 2` Markov kernel whose rows are `twoByTwoRows`. -/
noncomputable def twoByTwoKernel : Kernel (Fin 2) (Fin 2) :=
  Kernel.ofFunOfCountable fun i => (twoByTwoRows i).toMeasure

@[simp]
lemma twoByTwoKernel_apply (i : Fin 2) :
    twoByTwoKernel i = (twoByTwoRows i).toMeasure := by
  rfl

lemma twoByTwoKernel_apply_singleton (i j : Fin 2) :
    twoByTwoKernel i {j} = twoByTwoRowPMF i j := by
  simp [twoByTwoKernel_apply, twoByTwoRows]

noncomputable instance twoByTwoKernel_isMarkov : IsMarkovKernel twoByTwoKernel := by
  constructor
  intro i
  change IsProbabilityMeasure ((twoByTwoRowPMF i).toMeasure)
  infer_instance

/-- The density of `twoByTwoKernel` with respect to the counting measure:
`3/4` on the diagonal and `1/4` off it. -/
noncomputable def twoByTwoDensity (i j : Fin 2) : NNReal :=
  if i = j then 3 / 4 else 1 / 4

@[simp]
lemma twoByTwoDensity_apply (i j : Fin 2) :
    (twoByTwoDensity i j : ℝ≥0∞) = twoByTwoRowPMF i j := by
  fin_cases i <;> fin_cases j <;> simp [twoByTwoDensity, twoByTwoRowPMF]

theorem twoByTwo_rowMatrixFullRank : Kernel.RowMatrixFullRank twoByTwoKernel := by
  intro w v hEq
  funext a
  fin_cases a
  · have h0 := congrFun hEq 0
    have h1 := congrFun hEq 1
    norm_num [Fin.sum_univ_two, twoByTwoKernel_apply_singleton, twoByTwoRowPMF] at h0 h1 ⊢
    nlinarith
  · have h0 := congrFun hEq 0
    have h1 := congrFun hEq 1
    norm_num [Fin.sum_univ_two, twoByTwoKernel_apply_singleton, twoByTwoRowPMF] at h0 h1 ⊢
    nlinarith

theorem twoByTwo_injectivePriorPushforward :
    Kernel.InjectivePriorPushforward twoByTwoKernel :=
  Kernel.injectivePriorPushforward_of_rowMatrixFullRank twoByTwoKernel twoByTwo_rowMatrixFullRank

/-- The `ContinuousPositiveDensity` witness for `twoByTwoKernel` over the counting measure. -/
noncomputable def twoByTwoContinuousPositiveDensity :
    Kernel.ContinuousPositiveDensity twoByTwoKernel Measure.count := by
  refine
    { density := twoByTwoDensity
      continuous_density := by
        fun_prop
      eq_withDensity := ?_
      density_pos := ?_
      mutualInformation_usc := ?_ }
  · intro i
    have hcount := ChannelCapacity.toMeasure_eq_count_withDensity (μ := twoByTwoRows i)
    simpa [twoByTwoRows, twoByTwoDensity_apply] using hcount
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [twoByTwoDensity]
  · exact (continuous_mutualInformation_of_finite (k := twoByTwoKernel)).upperSemicontinuous

example :
    ∃! p : ProbabilityMeasure (Fin 2),
      mutualInformation p twoByTwoKernel = channelCapacity twoByTwoKernel :=
  exists_unique_capacity_achieving_prior_discharged
    (k := twoByTwoKernel)
    (ν := Measure.count)
    twoByTwoContinuousPositiveDensity
    twoByTwo_injectivePriorPushforward

end ChannelCapacity.DischargedExample

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.ChannelCapacity.Capacity
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# ChannelCapacity.Counterexample

A finite counterexample showing that row separation does not imply injective prior pushforward.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal NNReal

namespace ChannelCapacity.Counterexample

/-- The probability measure induced by a probability mass function. -/
noncomputable def asProbabilityMeasure {α : Type*} [MeasurableSpace α] (p : PMF α) :
    ProbabilityMeasure α :=
  ⟨p.toMeasure, by infer_instance⟩

/-- The uniform probability measure supported on the three points `a`, `b`, and `c`. -/
noncomputable def uniformTriple {α : Type*} [MeasurableSpace α] (a b c : α) :
    ProbabilityMeasure α :=
  ProbabilityMeasure.convexCombination
    (MeasureTheory.diracProba a)
    (ProbabilityMeasure.convexCombination
      (MeasureTheory.diracProba b)
      (MeasureTheory.diracProba c)
      (1 / 2)
      (by
        have h : (1 : ℝ) / 2 ≤ 1 := by norm_num
        exact_mod_cast h))
    (1 / 3)
    (by
      have h : (1 : ℝ) / 3 ≤ 1 := by norm_num
      exact_mod_cast h)

private lemma permutationWeightSum :
    (1 / 2 : ℝ≥0∞) + 1 / 3 + 1 / 6 = 1 := by
  have h : ((1 / 2 : ℝ≥0) + 1 / 3 + 1 / 6 : ℝ≥0) = 1 := by
    norm_num
  exact (by simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h)

private lemma prior₁_case0 :
    (1 / 3 : ℝ≥0∞) * (1 / 2) + (1 - 1 / 3) * ((1 / 2) * (1 / 6) + (1 / 2) * (1 / 3)) =
      1 / 3 := by
  have h : ((1 / 3 : ℝ≥0) * (1 / 2) + ((1 : ℝ≥0) - 1 / 3) *
      ((1 / 2) * (1 / 6) + (1 / 2) * (1 / 3)) : ℝ≥0) = 1 / 3 := by
    apply NNReal.coe_injective
    simp
    norm_num
  exact (by simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h)

private lemma prior₁_case1 :
    (1 / 3 : ℝ≥0∞) * (1 / 3) + (1 - 1 / 3) * ((1 / 2) * (1 / 2) + (1 / 2) * (1 / 6)) =
      (1 - 1 / 3) * (1 / 2) := by
  have h : ((1 / 3 : ℝ≥0) * (1 / 3) + ((1 : ℝ≥0) - 1 / 3) *
      ((1 / 2) * (1 / 2) + (1 / 2) * (1 / 6)) : ℝ≥0) = ((1 : ℝ≥0) - 1 / 3) * (1 / 2) := by
    apply NNReal.coe_injective
    simp
    norm_num
  exact (by simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h)

private lemma prior₁_case2 :
    (1 / 3 : ℝ≥0∞) * (1 / 6) + (1 - 1 / 3) * ((1 / 2) * (1 / 3) + (1 / 2) * (1 / 2)) =
      (1 - 1 / 3) * (1 / 2) := by
  have h : ((1 / 3 : ℝ≥0) * (1 / 6) + ((1 : ℝ≥0) - 1 / 3) *
      ((1 / 2) * (1 / 3) + (1 / 2) * (1 / 2)) : ℝ≥0) = ((1 : ℝ≥0) - 1 / 3) * (1 / 2) := by
    apply NNReal.coe_injective
    simp
    norm_num
  exact (by simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h)

private lemma prior₂_case1 :
    (1 / 3 : ℝ≥0∞) * (1 / 6) + (1 - 1 / 3) * ((1 / 2) * (1 / 2) + (1 / 2) * (1 / 3)) =
      (1 - 1 / 3) * (1 / 2) := by
  have h : ((1 / 3 : ℝ≥0) * (1 / 6) + ((1 : ℝ≥0) - 1 / 3) *
      ((1 / 2) * (1 / 2) + (1 / 2) * (1 / 3)) : ℝ≥0) = ((1 : ℝ≥0) - 1 / 3) * (1 / 2) := by
    apply NNReal.coe_injective
    simp
    norm_num
  exact (by simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h)

private lemma prior₂_case2 :
    (1 / 3 : ℝ≥0∞) * (1 / 3) + (1 - 1 / 3) * ((1 / 2) * (1 / 6) + (1 / 2) * (1 / 2)) =
      (1 - 1 / 3) * (1 / 2) := by
  have h : ((1 / 3 : ℝ≥0) * (1 / 3) + ((1 : ℝ≥0) - 1 / 3) *
      ((1 / 2) * (1 / 6) + (1 / 2) * (1 / 2)) : ℝ≥0) = ((1 : ℝ≥0) - 1 / 3) * (1 / 2) := by
    apply NNReal.coe_injective
    simp
    norm_num
  exact (by simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h)

/-- The six rows of the channel, one for each permutation of the values `1/2, 1/3, 1/6`,
as probability mass functions on `Fin 3`. -/
noncomputable def rowPMF : Fin 6 → PMF (Fin 3)
  | 0 => PMF.ofFintype (fun
      | 0 => (1 / 2 : ℝ≥0∞)
      | 1 => (1 / 3 : ℝ≥0∞)
      | _ => (1 / 6 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_three, add_assoc] using permutationWeightSum)
  | 1 => PMF.ofFintype (fun
      | 0 => (1 / 2 : ℝ≥0∞)
      | 1 => (1 / 6 : ℝ≥0∞)
      | _ => (1 / 3 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_three, add_comm, add_left_comm, add_assoc] using permutationWeightSum)
  | 2 => PMF.ofFintype (fun
      | 0 => (1 / 3 : ℝ≥0∞)
      | 1 => (1 / 2 : ℝ≥0∞)
      | _ => (1 / 6 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_three, add_comm, add_left_comm, add_assoc] using permutationWeightSum)
  | 3 => PMF.ofFintype (fun
      | 0 => (1 / 6 : ℝ≥0∞)
      | 1 => (1 / 2 : ℝ≥0∞)
      | _ => (1 / 3 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_three, add_comm, add_left_comm, add_assoc] using permutationWeightSum)
  | 4 => PMF.ofFintype (fun
      | 0 => (1 / 3 : ℝ≥0∞)
      | 1 => (1 / 6 : ℝ≥0∞)
      | _ => (1 / 2 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_three, add_comm, add_left_comm, add_assoc] using permutationWeightSum)
  | _ => PMF.ofFintype (fun
      | 0 => (1 / 6 : ℝ≥0∞)
      | 1 => (1 / 3 : ℝ≥0∞)
      | _ => (1 / 2 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_three, add_comm, add_left_comm, add_assoc] using permutationWeightSum)

/-- The six channel rows as probability measures on `Fin 3`. -/
noncomputable def permutationRows : Fin 6 → ProbabilityMeasure (Fin 3) :=
  fun i => asProbabilityMeasure (rowPMF i)

@[simp]
lemma permutationRows_apply_singleton (i : Fin 6) (y : Fin 3) :
    (permutationRows i).toMeasure {y} = rowPMF i y := by
  simp [permutationRows, asProbabilityMeasure]

/-- The Markov kernel `Fin 6 → Fin 3` whose rows are the six permutation rows. -/
noncomputable def permutationKernel : Kernel (Fin 6) (Fin 3) :=
  Kernel.ofFunOfCountable fun i => (permutationRows i).toMeasure

@[simp]
lemma permutationKernel_apply (i : Fin 6) :
    permutationKernel i = (rowPMF i).toMeasure := by
  rfl

lemma permutationKernel_apply_singleton (i : Fin 6) (y : Fin 3) :
    permutationKernel i {y} = rowPMF i y := by
  simp [permutationKernel_apply]

noncomputable instance permutationKernel_isMarkov :
    IsMarkovKernel permutationKernel := by
  constructor
  intro i
  change IsProbabilityMeasure ((rowPMF i).toMeasure)
  infer_instance

/-- Pushing a point mass at `i` through the channel returns the `i`-th row.

This is `Kernel.priorPushforward_dirac` restated with `permutationRows i` in place of the
anonymous-constructor `⟨permutationKernel i, _⟩`. The two terms are definitionally equal, but the
latter is a `Subtype.mk` whose inferred type is `{μ // IsProbabilityMeasure μ}` rather than
`ProbabilityMeasure (Fin 3)`, which blocks any subsequent `rw`/`simp` from matching it. -/
private lemma priorPushforward_diracProba (i : Fin 6) :
    ChannelCapacity.Kernel.priorPushforward permutationKernel (MeasureTheory.diracProba i) =
      permutationRows i := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ChannelCapacity.Kernel.priorPushforward_dirac]
  rfl

/-- The first prior: uniform on the inputs `{0, 3, 4}`. -/
noncomputable def prior₁ : ProbabilityMeasure (Fin 6) :=
  uniformTriple 0 3 4

/-- The second prior: uniform on the inputs `{1, 2, 5}`. -/
noncomputable def prior₂ : ProbabilityMeasure (Fin 6) :=
  uniformTriple 1 2 5

/-- The uniform distribution on the output alphabet `Fin 3`. -/
noncomputable def uniformOutput : ProbabilityMeasure (Fin 3) :=
  uniformTriple 0 1 2

/-- The rational values of each channel row, matching `rowPMF` entrywise. -/
def rowCode : Fin 6 → Fin 3 → Rat
  | 0, 0 => 1 / 2
  | 0, 1 => 1 / 3
  | 0, _ => 1 / 6
  | 1, 0 => 1 / 2
  | 1, 1 => 1 / 6
  | 1, _ => 1 / 3
  | 2, 0 => 1 / 3
  | 2, 1 => 1 / 2
  | 2, _ => 1 / 6
  | 3, 0 => 1 / 6
  | 3, 1 => 1 / 2
  | 3, _ => 1 / 3
  | 4, 0 => 1 / 3
  | 4, 1 => 1 / 6
  | 4, _ => 1 / 2
  | _, 0 => 1 / 6
  | _, 1 => 1 / 3
  | _, _ => 1 / 2

lemma rowCode_injective : Function.Injective rowCode := by
  intro a b hab
  have h0 := congrFun hab 0
  have h1 := congrFun hab 1
  fin_cases a <;> fin_cases b <;>
    first
      | rfl
      | (exfalso; simp [rowCode] at h0 h1)

/-- The rational weight vector of `prior₁`: mass `1/3` on each of `0, 3, 4`. -/
def prior₁Code : Fin 6 → Rat
  | 0 => 1 / 3
  | 3 => 1 / 3
  | 4 => 1 / 3
  | _ => 0

/-- The rational weight vector of `prior₂`: mass `1/3` on each of `1, 2, 5`. -/
def prior₂Code : Fin 6 → Rat
  | 1 => 1 / 3
  | 2 => 1 / 3
  | 5 => 1 / 3
  | _ => 0

/-- The output weight vector obtained by pushing an input weight vector `w` through `rowCode`. -/
def outputCode (w : Fin 6 → Rat) : Fin 3 → Rat :=
  fun y => ∑ x, w x * rowCode x y

lemma priorCode_counterexample :
    prior₁Code ≠ prior₂Code ∧ outputCode prior₁Code = outputCode prior₂Code := by
  refine ⟨?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    revert h0
    simp only [prior₁Code, prior₂Code]
    norm_num
  · funext y
    fin_cases y
    all_goals simp [outputCode, Fin.sum_univ_six, prior₁Code, prior₂Code, rowCode]
    all_goals norm_num

lemma prior_ne : prior₁ ≠ prior₂ := by
  intro h
  have h0 := congrArg (fun p : ProbabilityMeasure (Fin 6) => p.toMeasure {0}) h
  simp [prior₁, prior₂, uniformTriple, ProbabilityMeasure.convexCombination_toMeasure,
    Measure.add_apply, Measure.smul_apply] at h0

lemma pushforward_prior₁ :
    ChannelCapacity.Kernel.priorPushforward permutationKernel prior₁ = uniformOutput := by
  change ChannelCapacity.Kernel.priorPushforward permutationKernel (uniformTriple 0 3 4) =
    uniformOutput
  rw [uniformTriple, ChannelCapacity.Kernel.priorPushforward_convexCombination,
    priorPushforward_diracProba,
    ChannelCapacity.Kernel.priorPushforward_convexCombination,
    priorPushforward_diracProba, priorPushforward_diracProba]
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro y
  have hs : MeasurableSet ({y} : Set (Fin 3)) := MeasurableSet.singleton y
  rw [uniformOutput, uniformTriple]
  repeat rw [ProbabilityMeasure.convexCombination_apply _ _ _ _ hs]
  fin_cases y
  · simp [rowPMF]
    simpa [one_div, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      prior₁_case0
  · simp [rowPMF]
    simpa [one_div, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      prior₁_case1
  · simp [rowPMF]
    simpa [one_div, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      prior₁_case2

lemma pushforward_prior₂ :
    ChannelCapacity.Kernel.priorPushforward permutationKernel prior₂ = uniformOutput := by
  change ChannelCapacity.Kernel.priorPushforward permutationKernel (uniformTriple 1 2 5) =
    uniformOutput
  rw [uniformTriple, ChannelCapacity.Kernel.priorPushforward_convexCombination,
    priorPushforward_diracProba,
    ChannelCapacity.Kernel.priorPushforward_convexCombination,
    priorPushforward_diracProba, priorPushforward_diracProba]
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro y
  have hs : MeasurableSet ({y} : Set (Fin 3)) := MeasurableSet.singleton y
  rw [uniformOutput, uniformTriple]
  repeat rw [ProbabilityMeasure.convexCombination_apply _ _ _ _ hs]
  fin_cases y
  · simp [rowPMF, add_comm]
    simpa [one_div, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      prior₁_case0
  · simp [rowPMF]
    simpa [one_div, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      prior₂_case1
  · simp [rowPMF]
    simpa [one_div, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      prior₂_case2

theorem permutationKernel_not_injectivePriorPushforward :
    ¬ ChannelCapacity.Kernel.InjectivePriorPushforward permutationKernel := by
  intro h
  exact prior_ne (h (pushforward_prior₁.trans pushforward_prior₂.symm))

lemma rowPMF_injective : Function.Injective rowPMF := by
  intro i j hij
  have h0 := congrArg (fun p : PMF (Fin 3) => p 0) hij
  have h1 := congrArg (fun p : PMF (Fin 3) => p 1) hij
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | (exfalso; simp [rowPMF, PMF.ofFintype_apply] at h0 h1)

example : ChannelCapacity.Kernel.RowSeparating permutationKernel := by
  intro i j hij hEq
  have hmeas : (rowPMF i).toMeasure = (rowPMF j).toMeasure := by
    simpa using hEq
  exact hij (rowPMF_injective (PMF.toMeasure_injective hmeas))

example :
    ¬ ChannelCapacity.Kernel.InjectivePriorPushforward permutationKernel :=
  permutationKernel_not_injectivePriorPushforward

example :
    ChannelCapacity.Kernel.priorPushforward permutationKernel prior₁ =
      ChannelCapacity.Kernel.priorPushforward permutationKernel prior₂ := by
  rw [pushforward_prior₁, pushforward_prior₂]

namespace Toy

/-- The identity kernel on `Fin 3`, used as a positive control with injective pushforward. -/
noncomputable def identityKernel : Kernel (Fin 3) (Fin 3) := Kernel.id

noncomputable instance : IsMarkovKernel identityKernel := by
  dsimp [identityKernel]
  infer_instance

example : ChannelCapacity.Kernel.InjectivePriorPushforward identityKernel :=
  ChannelCapacity.Kernel.id_injectivePriorPushforward

end Toy

end ChannelCapacity.Counterexample

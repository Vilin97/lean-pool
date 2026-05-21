/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import LeanPool.HopfieldNet.SpinState.Basic
set_option checkBinderAnnotations false
namespace HopfieldState

variable {n : ℕ} [Fact (n > 0)]
variable {α β γ : Type*}

open SpinState UpdateSeq
open NNReal ENNReal Finset MeasureTheory

/-- The energy of a Hopfield network state -/
noncomputable def hopfieldEnergy (weights : Fin n → Fin n → ℝ) (state : Fin n → SpinState) : ℝ :=
  -(1/2) * ∑ i, ∑ j, weights i j * (state i).toReal * (state j).toReal

/-- Energy difference from flipping a single neuron -/
def hopfieldEnergyDiff (weights : Fin n → Fin n → ℝ) (state : Fin n → SpinState) (i : Fin n) (new_state : SpinState) : ℝ :=
  -- Energy difference = E(state') - E(state)
  let old_value := state i
  let local_field := ∑ j, weights i j * (state j).toReal;
  -((new_state).toReal - (old_value).toReal) * local_field

/-- Update a single neuron in the state -/
def updateSingleNeuron (state : Fin n → SpinState) (i : Fin n) (new_state : SpinState) : Fin n → SpinState :=
  Function.update state i new_state

variable {n : ℕ} [h : Fact (n > 0)]
instance : Nonempty (Fin n) :=
  ⟨⟨0, by
  simp_all only [gt_iff_lt]
  exact h.out
  ⟩⟩

/-- Define the probability distribution for updating a single neuron in a Hopfield network -/
noncomputable def neuronUpdatePMF (weights : Fin n → Fin n → ℝ) (T : ℝ) (state : Fin n → SpinState) (i : Fin n) :
    PMF SpinState := by
  -- Convert energy differences to probabilities using Boltzmann distribution
  let probs : SpinState → ℝ≥0∞ := fun new_state =>
    ENNReal.ofReal (Real.exp (-hopfieldEnergyDiff weights state i new_state / T))

  -- Create a PMF using the ofFintype constructor (since SpinState is finite)
  -- First need to normalize the probabilities to sum to 1
  let total : ℝ≥0∞ := ∑ s : SpinState, probs s

  -- Handle case where temperature is so low that numerical precision issues occur
  by_cases h_total : total = 0
  · -- If total = 0 (extreme low temperature), use a deterministic update
    let deterministicState :=
      if 0 < ∑ j, weights i j * (state j).toReal then SpinState.up else SpinState.down
    exact PMF.pure deterministicState
  · -- Otherwise use normalized probabilities
    let norm_probs : SpinState → ℝ≥0∞ := fun s => probs s / total
    have h_sum_one : ∑ s : SpinState, norm_probs s = 1 := by
      -- Apply sum_div directly without the simp
      rw [Fintype.sum_congr norm_probs norm_probs (congrFun rfl)]
      have : ∑ s : SpinState, norm_probs s = total⁻¹ * ∑ s : SpinState, probs s := by
        simp_rw [norm_probs, ENNReal.div_eq_inv_mul, mul_sum]

      rw [this]
      have h_not_top : total ≠ ⊤ := by
        -- If total = 0, it can't also be ⊤ (infinity)
        exact fun h_top => by rw [h_top] at h_total; simp_all only [top_ne_zero, not_false_eq_true, sum_eq_top,
          mem_univ, ofReal_ne_top, and_false, exists_const, probs, total]
      exact ENNReal.inv_mul_cancel h_total h_not_top
    exact PMF.ofFintype norm_probs h_sum_one

/-- Perform a stochastic update of the Hopfield network according to temperature T -/
noncomputable def stochasticUpdate (weights : Fin n → Fin n → ℝ) (T : ℝ) (state : Fin n → SpinState) (i : Fin n) :
    PMF (Fin n → SpinState) :=
  -- Get PMF for the specific neuron
  let neuronPMF := neuronUpdatePMF weights T state i

  -- Map this to a PMF over the whole state
  PMF.map (fun new_spin => updateSingleNeuron state i new_spin) neuronPMF

/-- Run a single step of Gibbs sampling on the Hopfield network -/
noncomputable def gibbsSamplingStep (weights : Fin n → Fin n → ℝ) (T : ℝ) (state : Fin n → SpinState) :
    PMF (Fin n → SpinState) :=
  -- Select a random neuron to update
  let neuronPMF : PMF (Fin n) :=
    PMF.ofFintype (fun _ => 1 / n) (by
      rw [Finset.sum_const, Finset.card_univ, ENNReal.div_eq_inv_mul]
      -- Simplify the expression to get (n⁻¹ * n = 1)
      rw [@nsmul_eq_mul]
      rw [Fintype.card_fin, mul_comm _ ((n : ℝ≥0∞)⁻¹ * 1)]
      simp only [mul_one]
      apply ENNReal.inv_mul_cancel
      · apply Nat.cast_ne_zero.mpr
        exact Nat.ne_of_gt (Fact.out)
      · exact ENNReal.coe_ne_top)

  -- Bind the neuron selection with the stochastic update
  PMF.bind neuronPMF (fun i => stochasticUpdate weights T state i)

/-- Multiple steps of Gibbs sampling -/
noncomputable def gibbsSamplingSteps (weights : Fin n → Fin n → ℝ) (T : ℝ) (steps : ℕ) (state : Fin n → SpinState) :
    PMF (Fin n → SpinState) :=
  match steps with
  | 0 => PMF.pure state
  | steps+1 => PMF.bind (gibbsSamplingSteps weights T steps state)
                       (fun s => gibbsSamplingStep weights T s)

/-- Simulated annealing for Hopfield networks -/
noncomputable def simulatedAnnealing (weights : Fin n → Fin n → ℝ)
    (initial_temp : ℝ) (cooling_rate : ℝ) (steps : ℕ) (initial_state : Fin n → SpinState) :
    PMF (Fin n → SpinState) :=
  -- Define temperature schedule
  let temp_schedule : ℕ → ℝ := fun step => initial_temp * Real.exp (-cooling_rate * step)

  -- Helper function to perform one annealing step
  let step_fn : ℕ → (Fin n → SpinState) → PMF (Fin n → SpinState) :=
    fun step state => gibbsSamplingStep weights (temp_schedule step) state

  -- Recursive application of annealing steps
  let rec apply_steps (step : ℕ) (state : Fin n → SpinState) : PMF (Fin n → SpinState) :=
    if step >= steps then
      PMF.pure state
    else
      PMF.bind (step_fn step state) (apply_steps (step+1))
  termination_by steps - step
  decreasing_by
    have h : step < steps := by
      -- We know step is not >= steps because we're in the 'else' branch
      dsimp only
      simp_all only [ge_iff_le, not_le]
    rw [←Nat.sub_sub]
    exact Nat.sub_lt (Nat.sub_pos_of_lt h) Nat.zero_lt_one

  apply_steps 0 initial_state

/-- Probability of acceptance in Metropolis-Hastings algorithm -/
noncomputable def acceptanceProbability (weights : Fin n → Fin n → ℝ) (T : ℝ)
    (current_state : Fin n → SpinState) (proposed_state : Fin n → SpinState) : ℝ :=
  let energy_diff := hopfieldEnergy weights proposed_state - hopfieldEnergy weights current_state
  if energy_diff <= 0 then
    1.0  -- Always accept if energy decreases
  else
    Real.exp (-energy_diff / T)  -- Accept with probability e^(-ΔE/T) if energy increases

/-- Creates a PMF for the Metropolis Hastings acceptance decision -/
noncomputable def metropolisDecision (p : ℝ) : PMF Bool :=
  PMF.bernoulli (ENNReal.ofReal (min p 1)) (by exact_mod_cast min_le_right p 1)

/-- One step of the Metropolis-Hastings algorithm for Hopfield networks -/
noncomputable def metropolisHastingsStep (weights : Fin n → Fin n → ℝ) (T : ℝ) (state : Fin n → SpinState) :
    PMF (Fin n → SpinState) :=
  -- Select a random neuron to potentially flip
  let neuronPMF : PMF (Fin n) :=
    PMF.ofFintype (fun _ => 1 / (n : ℝ≥0∞)) (by
      rw [Finset.sum_const, Finset.card_univ]
      simp only [Fintype.card_fin n]
      rw [ENNReal.div_eq_inv_mul]
      simp only [mul_comm _ ((n : ℝ≥0∞)⁻¹), mul_one]
      rw [@nsmul_eq_mul]
      rw [@Nat.cast_comm]
      apply ENNReal.inv_mul_cancel
      · exact ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Fact.out)))
      · exact ENNReal.coe_ne_top)

  -- Create a proposed state by flipping the selected neuron
  let propose : Fin n → PMF (Fin n → SpinState) := fun i =>
    let flipped_state := updateSingleNeuron state i (if state i = up then down else up)
    let p := acceptanceProbability weights T state flipped_state

    -- Make acceptance decision
    PMF.bind (metropolisDecision p) (fun accept =>
      if accept then PMF.pure flipped_state else PMF.pure state)

  -- Combine neuron selection with state proposal
  PMF.bind neuronPMF propose

/-- Multiple steps of Metropolis-Hastings algorithm -/
noncomputable def metropolisHastingsSteps (weights : Fin n → Fin n → ℝ) (T : ℝ) (steps : ℕ) (state : Fin n → SpinState) :
    PMF (Fin n → SpinState) :=
  match steps with
  | 0 => PMF.pure state
  | steps+1 => PMF.bind (metropolisHastingsSteps weights T steps state)
                       (fun s => metropolisHastingsStep weights T s)

end HopfieldState

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketWeights
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.NatFactorial

/-!
# Weighted Energy
-/

@[expose] public section

noncomputable section

namespace EulerWeightedEnergy

open Finset EulerPacketWeights

theorem weight_hasDerivAt (ρ : ℝ → ℝ) (ρ' t : ℝ) (hρ : HasDerivAt ρ ρ' t)
    (hpos : 0 < ρ t) (n : ℕ) :
    HasDerivAt (fun s => weight (ρ s) n)
      ((ρ' / ρ t) * (n : ℝ) * weight (ρ t) n) t := by
  have he : ((n : ℝ) * (ρ t) ^ (n - 1) * ρ') / (n.factorial : ℝ) ^ 2 =
      (ρ' / ρ t) * (n : ℝ) * weight (ρ t) n := by
    cases n with
    | zero => simp
    | succ n =>
      simp only [weight, Nat.succ_sub_one, pow_succ, Nat.cast_add, Nat.cast_one]
      field_simp [hpos.ne', factorial_cast_ne_zero]
  exact ((hρ.pow n).div_const ((n.factorial : ℝ) ^ 2)).congr_deriv he

/-- Exact differentiation of the finite weighted Gevrey energy, including radius loss. -/
theorem finite_weighted_energy_hasDerivAt
    (ρ : ℝ → ℝ) (ρ' t : ℝ) (hρ : HasDerivAt ρ ρ' t) (hpos : 0 < ρ t)
    (E : ℕ → ℝ → ℝ) (E' : ℕ → ℝ) (N : ℕ)
    (hE : ∀ n ∈ range (N + 1), HasDerivAt (E n) (E' n) t) :
    HasDerivAt (fun s => ∑ n ∈ range (N + 1), weight (ρ s) n * E n s)
      ((∑ n ∈ range (N + 1), weight (ρ t) n * E' n) +
        (ρ' / ρ t) * ∑ n ∈ range (N + 1), (n : ℝ) * weight (ρ t) n * E n t) t := by
  have h : HasDerivAt (fun s => ∑ n ∈ range (N + 1), weight (ρ s) n * E n s)
      (∑ n ∈ range (N + 1), ((ρ' / ρ t) * (n : ℝ) * weight (ρ t) n * E n t +
        weight (ρ t) n * E' n)) t := by
    exact HasDerivAt.fun_sum (u := range (N + 1))
      (fun n hn => (weight_hasDerivAt ρ ρ' t hρ hpos n).fun_mul (hE n hn))
  apply h.congr_deriv
  rw [sum_add_distrib]
  simp only [mul_assoc, mul_sum]
  ring

end EulerWeightedEnergy

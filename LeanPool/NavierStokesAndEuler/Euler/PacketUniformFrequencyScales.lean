/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleSequence
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real

/-! Uniform frequency separation for polynomial source sizes. These
costs can be placed in the same finite list as the geometric and pressure
costs, so the starting stage is chosen only once. -/

@[expose] public section


noncomputable section

namespace EulerPacketUniformFrequencyScales

open Real Filter EulerPacketSourceScaleBounds
  EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence
open scoped Topology

/-- Parameter envelope, given by `C*((J+n : ℕ) : ℝ)^p*(scaleSequence J X n)^q * exp
(c*(scaleSequence J X n/((J-1+n : ℕ) : ℝ)^3))`. -/
def parameterEnvelope (J : ℕ) (C c : ℝ) (p q : ℕ) (X : ℝ) (n : ℕ) : ℝ :=
  C*((J+n : ℕ) : ℝ)^p*(scaleSequence J X n)^q *
    exp (c*(scaleSequence J X n/((J-1+n : ℕ) : ℝ)^3))

/-- Frequency cost spec, bundling `d`, `B`, `N`, `a` and the required compatibility proofs. -/
def frequencyCostSpec (A C c : ℝ) (hA : 0 < A) (hC : 0 < C)
    (p q N : ℕ) (θ : ℝ) (hθ : 0 < θ) : CostSpec where
  d := 1
  B := 3
  N := 2
  a := 2
  b := θ
  c := (N : ℝ)*c
  C := A*C^N
  p := p*N
  q := q*N
  d_le_two := by norm_num
  a_nonneg := by norm_num
  a_lt_B := by norm_num
  a_le_N := by norm_num
  b_pos := hθ
  C_pos := mul_pos hA (pow_pos hC N)

theorem frequencyCost_eq (J : ℕ) (A C c : ℝ) (hA : 0 < A) (hC : 0 < C)
    (p q N : ℕ) (θ : ℝ) (hθ : 0 < θ) (X : ℝ) (n : ℕ) :
    (frequencyCostSpec A C c hA hC p q N θ hθ).cost J (scaleSequence J X) n =
      A*(parameterEnvelope J C c p q X n)^N/(frequency J X n)^θ := by
  simp only [frequencyCostSpec,CostSpec.cost,monomialCost,parameterEnvelope,
    frequency,mul_pow,← pow_mul,← exp_mul,div_eq_mul_inv,← exp_neg,← exp_nat_mul]
  rw [mul_assoc (A*C^N),mul_assoc (A*C^N)]
  simp only [mul_assoc,← exp_add]
  congr 2
  norm_num only [rpow_ofNat]
  ring_nf

theorem guard_of_cost_le (J : ℕ) (A C c : ℝ) (hA : 0 < A) (hC : 0 < C)
    (p q N : ℕ) (θ : ℝ) (hθ : 0 < θ) (X : ℝ) (n : ℕ)
    (hcost : (frequencyCostSpec A C c hA hC p q N θ hθ).cost J (scaleSequence J X) n ≤ 1) :
    A*(parameterEnvelope J C c p q X n)^N ≤ (frequency J X n)^θ := by
  rw [frequencyCost_eq] at hcost
  exact (div_le_one (rpow_pos_of_pos (exp_pos _) θ)).mp hcost

theorem frequency_monotone (J : ℕ) (hJ : 2 ≤ J) (X : ℝ) (hX : 0 ≤ X) :
    Monotone (frequency J X) := by
  apply monotone_nat_of_le_succ
  intro n
  have hj : (2 : ℝ) ≤ (J+n : ℕ) := by exact_mod_cast (show 2 ≤ J+n by omega)
  have hjp : (0 : ℝ) < (J+n : ℕ) := by linarith only [hj]
  have hxall : ∀ m, 0 ≤ scaleSequence J X m := by
    intro m
    induction m with
    | zero => exact hX
    | succ m ih =>
      rw [scaleSequence_succ]
      exact mul_nonneg (sq_nonneg _) ih
  have hbase : ((J+n : ℕ) : ℝ)+1 ≤ ((J+n : ℕ) : ℝ)^2 := by
    nlinarith only [hj,sq_nonneg (((J+n : ℕ) : ℝ)-2)]
  have hp := pow_le_pow_left₀ (show 0 ≤ ((J+n : ℕ) : ℝ)+1 by positivity) hbase 2
  have hm := mul_le_mul_of_nonneg_left hp (hxall n)
  unfold frequency
  apply exp_le_exp.mpr
  rw [scaleSequence_succ]
  have hcast : ((J+(n+1) : ℕ) : ℝ)=((J+n : ℕ) : ℝ)+1 := by push_cast; ring
  rw [hcast]
  apply (div_le_div_iff₀ (pow_pos hjp 2) (by positivity)).mpr
  nlinarith only [hm]

theorem frequency_zero_tendsto_atTop (J : ℕ) (hJ : 1 ≤ J) :
    Tendsto (fun X : ℝ => frequency J X 0) atTop atTop := by
  have hj : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have h := tendsto_exp_atTop.comp
    ((tendsto_id : Tendsto (fun X : ℝ => X) atTop atTop).atTop_div_const (pow_pos hj 2))
  change Tendsto (fun X : ℝ => exp (X/(J : ℝ)^2)) atTop atTop
  exact h

theorem eventually_all_frequency (J : ℕ) (hJ : 2 ≤ J) (P : ℝ → Prop)
    (hP : ∀ᶠ k : ℝ in atTop, P k) :
    ∀ᶠ X : ℝ in atTop, ∀ n, P (frequency J X n) := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp hP
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    (frequency_zero_tendsto_atTop J (by omega)).eventually (eventually_ge_atTop K)] with X hX hf
  intro n
  exact hK _ (hf.trans (frequency_monotone J hJ X hX (Nat.zero_le n)))

end EulerPacketUniformFrequencyScales

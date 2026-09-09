/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketUniformScaleChoice
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketUniformScaleSums
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD

/-!
# Packet Finite Scale Choice
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace EulerPacketFiniteScaleChoice

open Real EulerPacketUniformScaleChoice EulerPacketUniformScaleSums

/-- Every finite collection of scale inequalities allows the same
choices of `J` and then `x₀`. Thus the source's different coefficient,
neighbor, time, and pressure-cost requirements can be imposed together. -/
theorem finite_source_uniform_small_sum_choice
    {ι : Type*} [Finite ι] (d B N : ι → ℕ) (a b c C p q : ι → ℝ)
    (haB : ∀ i, a i < B i) (haN : ∀ i, a i ≤ N i) (hb : ∀ i, 0 < b i) :
    ∃ J : ℕ, 3 ≤ J ∧ ∀ δ : ℝ, 0 < δ → ∃ X₀ : ℝ, 1 ≤ X₀ ∧
      ∀ x : ℕ → ℝ, X₀ ≤ x 0 →
        (∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) → ∀ i,
        (∑' n, exp (-(b i) * (x n / ((J + n : ℕ) : ℝ) ^ (a i)) +
          c i * (x n / ((J - d i + n : ℕ) : ℝ) ^ (B i)) +
          C i + p i * log ((J + n : ℕ) : ℝ) + q i * log (x n))) ≤ δ := by
  classical
  let := Fintype.ofFinite ι
  classical
  choose Ji hJi3 hJid hJiN hJiC using fun i =>
    exists_uniform_stage_choice (d i) (B i) (N i) (a i) (c i) (b i) (haB i) (hb i)
  let J := max 3 (Finset.univ.sup Ji)
  have hJ3 : 3 ≤ J := le_max_left _ _
  have hJ1 : 1 ≤ J := by omega
  have hJiLe (i : ι) : Ji i ≤ J :=
    (Finset.le_sup (f := Ji) (Finset.mem_univ i)).trans (le_max_right _ _)
  have hdJ (i : ι) : d i < J := lt_of_lt_of_le (hJid i) (hJiLe i)
  have hJN (i : ι) : (2 : ℝ) ^ (2 * N i + 3) ≤ (J : ℝ) ^ 2 := by
    exact (hJiN i).trans (pow_le_pow_left₀ (by positivity)
      (by exact_mod_cast hJiLe i) 2)
  have hcoeff (i : ι) (n : ℕ) :
      c i * (((J + n : ℕ) : ℝ) ^ (a i) / ((J - d i + n : ℕ) : ℝ) ^ (B i)) ≤ b i / 4 := by
    have hh := hJiC i (J - Ji i + n)
    have hj : Ji i + (J - Ji i + n) = J + n := by have hi := hJiLe i; omega
    have hp : Ji i - d i + (J - Ji i + n) = J - d i + n := by
      have hi := hJiLe i
      have hid := hJid i
      omega
    simpa only [hj, hp] using hh
  refine ⟨J, hJ3, ?_⟩
  intro δ hδ
  have hboth : ∀ᶠ X : ℝ in atTop, ∀ i : ι,
      (4 * (|C i| + |p i| + 2 * |q i|) / b i) ^ 2 * (J : ℝ) ^ (2 * N i + 2) ≤ X ∧
      exp (-(b i / 2) * (X / (J : ℝ) ^ N i)) /
        (1 - exp (-(b i / 2) * (X / (J : ℝ) ^ N i))) ≤ δ := by
    apply eventually_all.2
    intro i
    have hi := source_exponential_bound_tendsto_zero J (N i) hJ1 (b i / 2)
      (div_pos (hb i) (by norm_num))
    exact (eventually_ge_atTop _).and (hi.eventually_le_const hδ)
  obtain ⟨X, hX⟩ := eventually_atTop.1 hboth
  refine ⟨max 1 X, le_max_left _ _, ?_⟩
  intro x hx0 hx i
  have hx1 : 1 ≤ x 0 := (le_max_left 1 X).trans hx0
  have hall := hX (x 0) ((le_max_right 1 X).trans hx0) i
  exact (uniform_source_cost_tsum_bound J (d i) (B i) (N i) hJ1 (hdJ i) (hJN i)
    x hx1 hx (a i) (b i) (c i) (C i) (p i) (q i) (haN i) (hb i) (hcoeff i) hall.1).trans hall.2

end EulerPacketFiniteScaleChoice

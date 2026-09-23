/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

module

public import LeanPool.ExpChaotic.Dynamics

/-!
# Further statements from the paper

Theorem 4.3 and Corollary 4.4 follow from eventual covering of two prescribed nonzero
targets. Observation 5.2 follows from the exponential norm identity and the chain rule.
The sensitivity theorem uses the paper's Definition 2.3, with arbitrary positive constants
as in Exercise 8.7, and even holds at every sufficiently late time.

Part of Lasse Rempe's formalisation of Shen and Rempe-Gillen's exponential-map paper,
with generative AI assistance including Copilot, Claude, and particularly ChatGPT.
The initial proof architecture uses John Harrison's HOL Light formalisation.
See `LeanPool.ExpChaotic` for attribution and the upstream source.
-/

@[expose] public section

open Function Filter Set Metric

namespace ExponentialJuliaSetMisiurewicz

noncomputable section

/-- Every sufficiently late image of a nonempty open set meets the negative real axis. -/
theorem eventually_hits_negative_realAxis {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ z ∈ U, (expIterate n z).im = 0 ∧ (expIterate n z).re < 0 := by
  obtain ⟨N, hN⟩ := eventually_hits_nonzero hU hUne (w := -1) (by norm_num)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨z, hz, heq⟩ := hN n hn
  exact ⟨z, hz, by simp [heq]⟩

/-- **Theorem 4.3.** Infinitely many iterated images meet the negative real axis. -/
theorem infinitely_often_hits_negative_realAxis {U : Set ℂ}
    (hU : IsOpen U) (hUne : U.Nonempty) :
    {n : ℕ | ∃ z ∈ U, (expIterate n z).im = 0 ∧ (expIterate n z).re < 0}.Infinite := by
  obtain ⟨N, hN⟩ := eventually_hits_negative_realAxis hU hUne
  exact (Set.Ici_infinite N).mono (fun n hn => hN n hn)

/-- **Corollary 4.4 and Exercise 8.7.** The paper's spherical sensitivity condition holds
for every pair of positive constants, at every sufficiently late time. -/
theorem spherical_sensitive_dependence_paper {U : Set ℂ}
    (hU : IsOpen U) (hUne : U.Nonempty) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ z ∈ U, ∃ w ∈ U,
      ‖expIterate n z‖ ≤ R ∧ δ ≤ ‖expIterate n z - expIterate n w‖ := by
  let a : ℂ := (R / 2 : ℝ)
  let b : ℂ := (R / 2 + δ : ℝ)
  have ha : a ≠ 0 := by dsimp [a]; exact_mod_cast (ne_of_gt (half_pos hR))
  have hb : b ≠ 0 := by dsimp [b]; exact_mod_cast (ne_of_gt (by positivity : 0 < R / 2 + δ))
  obtain ⟨N₁, h₁⟩ := eventually_hits_nonzero hU hUne ha
  obtain ⟨N₂, h₂⟩ := eventually_hits_nonzero hU hUne hb
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  obtain ⟨z, hz, hza⟩ := h₁ n ((le_max_left _ _).trans hn)
  obtain ⟨w, hw, hwb⟩ := h₂ n ((le_max_right _ _).trans hn)
  refine ⟨z, hz, w, hw, ?_, ?_⟩
  · rw [hza]
    simpa [a, Complex.norm_real, abs_of_pos hR] using (half_le_self hR.le)
  · rw [hza, hwb]
    have hab : a - b = (-δ : ℝ) := by dsimp [a, b]; push_cast; ring
    simp [hab, Complex.norm_real, abs_of_pos hδ]

/-- **Observation 5.2, first clause.** Real parts tend to positive infinity
along escaping orbits. -/
theorem EscapesToInfinity.tendsto_re {z : ℂ} (hz : EscapesToInfinity z) :
    Tendsto (fun n => (expIterate n z).re) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro R
  obtain ⟨N, hN⟩ := hz (Real.exp R)
  refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  have h := hN (n + 1) (by omega)
  simpa only [expIterate_succ, Complex.norm_exp, Real.exp_le_exp] using h

/-- **Observation 5.2, second clause.** Derivative norms tend to infinity along escaping orbits.
After finitely many factors, every factor in the chain rule has norm at least two. -/
theorem EscapesToInfinity.tendsto_norm_deriv {z : ℂ} (hz : EscapesToInfinity z) :
    Tendsto (fun n => ‖deriv (expIterate n) z‖) atTop atTop := by
  obtain ⟨N, hN⟩ := hz 2
  have hd : 0 < ‖deriv (expIterate N) z‖ := norm_pos_iff.mpr (deriv_expIterate_ne_zero N z)
  have hgrowth : ∀ k : ℕ,
      ‖deriv (expIterate N) z‖ * 2 ^ k ≤ ‖deriv (expIterate (N + k)) z‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← Nat.add_assoc, deriv_expIterate_succ, norm_mul, pow_succ]
      calc
        ‖deriv (expIterate N) z‖ * (2 ^ k * 2)
            = (‖deriv (expIterate N) z‖ * 2 ^ k) * 2 := by ring
        _ ≤ ‖deriv (expIterate (N + k)) z‖ *
            ‖Complex.exp (expIterate (N + k) z)‖ :=
          mul_le_mul ih (by simpa only [← expIterate_succ] using hN (N + k + 1) (by omega))
            (by norm_num) (norm_nonneg _)
  have ht := tendsto_atTop_mono hgrowth
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_mul_atTop hd)
  exact (tendsto_add_atTop_iff_nat N).mp (by simpa only [Nat.add_comm] using ht)

end

end ExponentialJuliaSetMisiurewicz

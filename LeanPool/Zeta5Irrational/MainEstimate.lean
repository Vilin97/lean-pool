/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.RealBound
import LeanPool.Zeta5Irrational.Growth
import Mathlib.Tactic.ENatToNat
public import LeanPool.Zeta5Irrational.Construction
public import LeanPool.Zeta5Irrational.Zeta5
public import LeanPool.Zeta5Irrational.Constants
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # The main estimate (Theorem 2.1 of the paper)

The three inputs of Section 7 of "ζ(5) is irrational" (A. Fauzan, 2026), all proved:

* `degree_F`: `F_K` has degree `h = 37 n`, (2.9) (`Zeta5Irrational.Degree`).
* `real_bound`: a weakening of Proposition 6.3, `0 < F_K(ζ(5))` and
  `log F_K(ζ(5)) ≤ U K² + 27 K log K + 200 K` (`Zeta5Irrational.RealBound`),
  using `27` in place of the paper's `24`.
* `normalization`: positive rationals `m_K` with `m_K F_K ∈ ℤ[X]` (`integral_mN`) and
  `log m_K ≤ (A_eff + ε) K²` eventually (`growth_mN`), with `A_eff = 1.36 < -U`.

From these, `main_estimate` proves Theorem 2.1 with decay rate `c = -800 (A_eff + U) > 0` in
place of the paper's `139/5`. This suffices for the irrationality criterion.
-/

public section

open Polynomial Filter Topology

namespace Zeta5Irrational

/-- **(2.9)**: `F_K` has degree `h = 37 n` (proved in `Zeta5Irrational.Degree`). -/
theorem degree_F (n : ℕ) : (F n).natDegree = 37 * n :=
  natDegree_F n

/-- A weakening of **Proposition 6.3**, with `27 K log K` in place of `24 K log K`
(see `Zeta5Irrational.RealBound` for its decomposition). -/
theorem real_bound (n : ℕ) (hn : 0 < n) :
    0 < aeval zeta5 (F n) ∧
      Real.log (aeval zeta5 (F n)) ≤
        (U : ℝ) * Kr n ^ 2 + 27 * Kr n * Real.log (Kr n) + 200 * Kr n :=
  real_bound' n hn

/-- **Propositions 5.1 and 5.2** in the form proved here: a positive rational normalisation
`m_K` with `m_K F_K ∈ ℤ[X]` for all `n ≥ 1` (`integral_mN`), and for every `ε > 0`,
eventually `log m_K ≤ (A_eff + ε) K²` (`growth_mN`). -/
theorem normalization :
    ∃ m : ℕ → ℚ,
      (∀ n, 0 < m n) ∧
        (∀ᶠ n in atTop, ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) = C (m n) * F n) ∧
          ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, Real.log (m n) ≤ ((Aeff : ℝ) + ε) * Kr n ^ 2 :=
  ⟨mN, mN_pos, (eventually_ge_atTop 1).mono fun _ hn => integral_mN hn, growth_mN⟩

/-- The lower-order terms are eventually dominated: for every `δ > 0`,
`27 K log K + 200 K < δ K²` for all large `n` (with `K = 40 n`). -/
lemma eventually_lower_order (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, 27 * Kr n * Real.log (Kr n) + 200 * Kr n < δ * Kr n ^ 2 := by
  have hK : Tendsto Kr atTop atTop :=
    (tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num : (0 : ℝ) < 40)
  have h1 : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ δ / 108 * ‖x‖ :=
    Real.isLittleO_log_id_atTop.def (by positivity)
  have h2 : ∀ᶠ x : ℝ in atTop, 200 < δ / 4 * x := by
    have := (tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < δ / 4)).eventually_gt_atTop 200
    simpa using this
  have h3 : ∀ᶠ x : ℝ in atTop, (0 : ℝ) < x := eventually_gt_atTop 0
  filter_upwards [hK.eventually h1, hK.eventually h2, hK.eventually h3] with n h1 h2 h3
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos h3] at h1
  have h4 : Real.log (Kr n) ≤ δ / 108 * Kr n := le_trans (le_abs_self _) h1
  nlinarith [mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ 24 * Kr n)]

/-- **Theorem 2.1 of the paper**, with the decay rate `c = -800 (A_eff + U) > 0` instead of
`139/5`: for all large `n`, some positive rational multiple `Q_n` of `F_{40n}` is an integer
polynomial of degree `37 n` with `0 < Q_n(ζ(5)) < exp(-c n²)`. -/
theorem main_estimate :
    ∃ c : ℝ,
      0 < c ∧
        ∀ᶠ n in atTop,
          ∃ Q : ℤ[X],
            (∃ c' : ℚ, 0 < c' ∧ Q.map (Int.castRingHom ℚ) = C c' * F n) ∧
              Q.natDegree = 37 * n ∧
                0 < aeval zeta5 Q ∧ aeval zeta5 Q < Real.exp (-c * (n : ℝ) ^ 2) := by
  obtain ⟨m, hm_pos, hm_int, hm_log⟩ := normalization
  set δ : ℝ := -((Aeff : ℝ) + U) with hδ_def
  have hδ : 0 < δ := by
    have h : ((Aeff + U : ℚ) : ℝ) < 0 := by exact_mod_cast Aeff_margin
    push_cast at h
    rw [hδ_def]; linarith
  refine ⟨800 * δ, by positivity, ?_⟩
  filter_upwards [hm_int, hm_log (δ / 4) (by positivity),
    eventually_lower_order (δ / 4) (by positivity), eventually_gt_atTop 0] with n ⟨Q, hQ⟩ hlog
    hlow hn
  obtain ⟨hFpos, hFlog⟩ := real_bound n hn
  have hc : (0 : ℝ) < m n := by exact_mod_cast hm_pos n
  have hQeval : aeval zeta5 Q = (m n : ℝ) * aeval zeta5 (F n) := by
    rw [← aeval_map_algebraMap ℚ zeta5 Q]
    simp only [algebraMap_int_eq, hQ, map_mul, aeval_C]
    rfl
  refine ⟨Q, ⟨m n, hm_pos n, hQ⟩, ?_, ?_, ?_⟩
  · have h1 : (Q.map (Int.castRingHom ℚ)).natDegree = Q.natDegree :=
      natDegree_map_eq_of_injective (Int.cast_injective) Q
    rw [← h1, hQ, natDegree_C_mul (by exact_mod_cast (hm_pos n).ne'), degree_F]
  · rw [hQeval]; exact mul_pos hc hFpos
  · rw [hQeval, ← Real.log_lt_iff_lt_exp (mul_pos hc hFpos), Real.log_mul hc.ne' hFpos.ne']
    have hK2 : Kr n ^ 2 = 1600 * (n : ℝ) ^ 2 := by simp only [Kr]; ring
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    rw [hK2] at hlog hFlog hlow
    have : (U : ℝ) = -((Aeff : ℝ)) - δ := by rw [hδ_def]; ring
    rw [this] at hFlog
    nlinarith

end Zeta5Irrational

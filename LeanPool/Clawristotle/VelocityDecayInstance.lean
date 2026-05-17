/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.Defs

/-!
# Lorentz Force Component Bound

Proves `lorentz_component_bound`: each component of the Lorentz force (E + v x B)
is bounded by C * (1 + ||v||). Used by `CoulombSpatialTransport` for bounding
spatial transport integrands.
-/

open Matrix Finset BigOperators Real MeasureTheory

noncomputable section
namespace VML

/-- Bound on a Lorentz force component: |(E₀ + v × B₀)ᵢ| ≤ C·(1 + ‖v‖).
    Each cross product component is bilinear in v, B₀, hence linear in ‖v‖.
    Proved by Aristotle. -/
lemma lorentz_component_bound (E₀ B₀ : Fin 3 → ℝ) :
    ∃ CL : ℝ, 0 ≤ CL ∧ ∀ (v : Fin 3 → ℝ) (i : Fin 3),
      |(E₀ + cross v B₀) i| ≤ CL * (1 + ‖v‖) := by
  simp only [cross]
  use ‖E₀‖ + ∑ i, ‖B₀ i‖ * 3 + 1
  refine ⟨ by positivity, fun v i => ?_ ⟩
  fin_cases i <;> simp [ Fin.sum_univ_succ ] <;> ring_nf
  · have h_triangle :
          |E₀ 0 + (v 1 * B₀ 2 - v 2 * B₀ 1)| ≤ |E₀ 0| + |v 1 * B₀ 2| + |v 2 * B₀ 1| := by
      cases abs_cases (E₀ 0 + (v 1 * B₀ 2 - v 2 * B₀ 1) ) <;>
        cases abs_cases (E₀ 0) <;>
        cases abs_cases (v 1 * B₀ 2) <;>
        cases abs_cases (v 2 * B₀ 1) <;> linarith
    have h_triangle2 :
        |E₀ 0| ≤ ‖E₀‖ ∧ |v 1 * B₀ 2| ≤ ‖v‖ * |B₀ 2| ∧ |v 2 * B₀ 1| ≤ ‖v‖ * |B₀ 1| := by
      exact ⟨ by simpa using norm_le_pi_norm E₀ 0,
               by simpa [ abs_mul ] using
                 mul_le_mul_of_nonneg_right (norm_le_pi_norm v 1) (abs_nonneg _),
               by simpa [ abs_mul ] using
                 mul_le_mul_of_nonneg_right (norm_le_pi_norm v 2) (abs_nonneg _) ⟩
    -- `ring_nf` left the goal with `E₀ 0 + v 1 * B₀ 2 - v 2 * B₀ 1` (left-assoc);
    -- reassociate so the `|·|` term matches `h_triangle`.
    rw [add_sub_assoc]
    obtain ⟨h2a, h2b, h2c⟩ := h_triangle2
    nlinarith [ h_triangle, h2a, h2b, h2c, abs_nonneg (E₀ 0), abs_nonneg (v 1 * B₀ 2),
                abs_nonneg (v 2 * B₀ 1), abs_nonneg (B₀ 0), abs_nonneg (B₀ 1), abs_nonneg (B₀ 2),
                norm_nonneg E₀, norm_nonneg v, mul_nonneg (norm_nonneg E₀) (norm_nonneg v),
                mul_nonneg (abs_nonneg (B₀ 0)) (norm_nonneg v),
                mul_nonneg (abs_nonneg (B₀ 1)) (norm_nonneg v),
                mul_nonneg (abs_nonneg (B₀ 2)) (norm_nonneg v) ]
  · have h_triangle :
        |E₀ 1| ≤ ‖E₀‖ ∧ |v 2 * B₀ 0| ≤ ‖v‖ * |B₀ 0| ∧ |v 0 * B₀ 2| ≤ ‖v‖ * |B₀ 2| := by
      exact ⟨ by simpa using norm_le_pi_norm E₀ 1,
               by
                 rw [ abs_mul ]
                 exact mul_le_mul_of_nonneg_right (norm_le_pi_norm v 2) (abs_nonneg _),
               by
                 rw [ abs_mul ]
                 exact mul_le_mul_of_nonneg_right (norm_le_pi_norm v 0) (abs_nonneg _) ⟩
    exact abs_le.mpr ⟨
      by nlinarith [ abs_le.mp h_triangle.1, abs_le.mp h_triangle.2.1, abs_le.mp h_triangle.2.2,
                     abs_nonneg (B₀ 0), abs_nonneg (B₀ 1), abs_nonneg (B₀ 2), norm_nonneg v ],
      by nlinarith [ abs_le.mp h_triangle.1, abs_le.mp h_triangle.2.1, abs_le.mp h_triangle.2.2,
                     abs_nonneg (B₀ 0), abs_nonneg (B₀ 1), abs_nonneg (B₀ 2), norm_nonneg v ] ⟩
  · have h_triangle :
        abs (E₀ 2 + (v 0 * B₀ 1 - v 1 * B₀ 0)) ≤
          abs (E₀ 2) + abs (v 0 * B₀ 1) + abs (v 1 * B₀ 0) := by
      cases abs_cases (E₀ 2 + (v 0 * B₀ 1 - v 1 * B₀ 0) ) <;>
        cases abs_cases (E₀ 2) <;>
        cases abs_cases (v 0 * B₀ 1) <;>
        cases abs_cases (v 1 * B₀ 0) <;> linarith
    norm_num [ abs_mul ] at *
    rw [add_sub_assoc]
    nlinarith! [ h_triangle, abs_nonneg (E₀ 2), abs_nonneg (v 0), abs_nonneg (v 1),
                 abs_nonneg (B₀ 0), abs_nonneg (B₀ 1), abs_nonneg (B₀ 2), norm_nonneg v,
                 show ‖E₀‖ ≥ |E₀ 2| from norm_le_pi_norm E₀ 2,
                 show ‖v‖ ≥ |v 0| from norm_le_pi_norm v 0,
                 show ‖v‖ ≥ |v 1| from norm_le_pi_norm v 1,
                 mul_nonneg (norm_nonneg E₀) (norm_nonneg v),
                 mul_nonneg (abs_nonneg (B₀ 0)) (norm_nonneg v),
                 mul_nonneg (abs_nonneg (B₀ 1)) (norm_nonneg v),
                 mul_nonneg (abs_nonneg (B₀ 2)) (norm_nonneg v) ]


end VML

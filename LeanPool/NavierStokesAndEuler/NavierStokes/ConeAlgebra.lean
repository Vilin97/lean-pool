/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Exact algebra of the stress cone

This formalizes the square-root criterion and quadratic equivalence in Lemma 3.5
of the candidate manuscript, together with the normalized
factorization used in equation (11). It does not construct any stress profile.
-/

@[expose] public section


namespace NavierStokes.ConeAlgebra

/-- The lower root appearing in equation (10). -/
noncomputable def coneBound (P J : ℝ) : ℝ :=
  P + J ^ 2 / 4 - |J| * Real.sqrt ((P - 2) / 2 + J ^ 2 / 16)

/-- The discriminant term in the displayed root formula. -/
noncomputable def rootTerm (P J : ℝ) : ℝ :=
  |J| * Real.sqrt ((P - 2) / 2 + J ^ 2 / 16)

theorem rootTerm_nonneg (P J : ℝ) : 0 ≤ rootTerm P J := by
  exact mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)

theorem rootTerm_sq {P J : ℝ} (hP : 2 < P) :
    rootTerm P J ^ 2 = J ^ 2 * ((P - 2) / 2 + J ^ 2 / 16) := by
  have hrad : 0 ≤ (P - 2) / 2 + J ^ 2 / 16 := by nlinarith [sq_nonneg J]
  unfold rootTerm
  rw [mul_pow, sq_abs, Real.sq_sqrt hrad]

theorem boundary_polynomial (P J v : ℝ) :
    2 * (P - v) ^ 2 - (v - 2) * J ^ 2 =
      2 * v ^ 2 - (4 * P + J ^ 2) * v + 2 * P ^ 2 + 2 * J ^ 2 := by
  ring

theorem square_difference (P J v : ℝ) :
    (P + J ^ 2 / 4 - v) ^ 2 - J ^ 2 * ((P - 2) / 2 + J ^ 2 / 16) =
      (P - v) ^ 2 - (v - 2) * J ^ 2 / 2 := by
  ring

theorem rootTerm_ge_quarter {P J : ℝ} (hP : 2 < P) :
    J ^ 2 / 4 ≤ rootTerm P J := by
  have hsq := rootTerm_sq (J := J) hP
  have hr := rootTerm_nonneg P J
  have hJ := sq_nonneg J
  have hprod : 0 ≤ J ^ 2 * (P - 2) := mul_nonneg hJ (by linarith)
  nlinarith [sq_nonneg (rootTerm P J - J ^ 2 / 4)]

theorem coneBound_le_parameter {P J : ℝ} (hP : 2 < P) : coneBound P J ≤ P := by
  have h := rootTerm_ge_quarter (J := J) hP
  change P + J ^ 2 / 4 - rootTerm P J ≤ P
  linarith

/-- The lower root is strictly above two for every finite J and P > 2. -/
theorem coneBound_gt_two {P J : ℝ} (hP : 2 < P) : 2 < coneBound P J := by
  have hsq := rootTerm_sq (J := J) hP
  have hr := rootTerm_nonneg P J
  have hid := square_difference P J 2
  have hJ := sq_nonneg J
  have hpos : 0 < P + J ^ 2 / 4 - 2 := by linarith
  have hlt : rootTerm P J < P + J ^ 2 / 4 - 2 := by
    nlinarith [sq_pos_of_pos (show 0 < P - 2 by linarith)]
  change 2 < P + J ^ 2 / 4 - rootTerm P J
  linarith

/-- Lemma 3.5: the full square-root criterion is equivalent to the quadratic test. -/
theorem true_cone_iff {P J v : ℝ} (hv : 2 < v) :
    (2 < P ∧ v < coneBound P J) ↔
      (v < P ∧ (v - 2) * J ^ 2 < 2 * (P - v) ^ 2) := by
  constructor
  · rintro ⟨hP, hcone⟩
    have hvP : v < P := lt_of_lt_of_le hcone (coneBound_le_parameter hP)
    refine ⟨hvP, ?_⟩
    have hsq := rootTerm_sq (J := J) hP
    have hr := rootTerm_nonneg P J
    have hid := square_difference P J v
    have hlt : rootTerm P J < P + J ^ 2 / 4 - v := by
      change v < P + J ^ 2 / 4 - rootTerm P J at hcone
      linarith
    have hdiff := mul_pos (sub_pos.mpr hlt)
      (show 0 < P + J ^ 2 / 4 - v + rootTerm P J by linarith)
    nlinarith
  · rintro ⟨hvP, hquad⟩
    have hP : 2 < P := lt_trans hv hvP
    refine ⟨hP, ?_⟩
    have hsq := rootTerm_sq (J := J) hP
    have hr := rootTerm_nonneg P J
    have hid := square_difference P J v
    have hpos : 0 < P + J ^ 2 / 4 - v := by nlinarith [sq_nonneg J]
    have hlt : rootTerm P J < P + J ^ 2 / 4 - v := by nlinarith
    change v < P + J ^ 2 / 4 - rootTerm P J
    linarith

/-- At and below two, P > 2 alone implies the relaxed root inequality. -/
theorem relaxed_cone_of_le_two {P J v : ℝ} (hP : 2 < P) (hv : v ≤ 2) :
    v < coneBound P J := lt_of_le_of_lt hv (coneBound_gt_two hP)

/-- The exact factorization behind the limiting sufficient criterion (11). -/
theorem normalized_factorization (a b w : ℝ) (ha : a ≠ 0) :
    (a * (1 + (b / a) ^ 2) - 2) * (w + b / a) ^ 2 -
        2 * (1 - b * w / a) ^ 2 =
      (1 + (b / a) ^ 2) * ((a - 2) * w ^ 2 + 2 * b * w + b ^ 2 / a - 2) := by
  field_simp; ring

/-- Strict negativity in equation (11) gives strict negativity of its factored test. -/
theorem normalized_test_negative {a b w : ℝ} (ha : 0 < a)
    (hcriterion : 2 * b * w + b ^ 2 / a + (a - 2) * w ^ 2 < 2) :
    (a * (1 + (b / a) ^ 2) - 2) * (w + b / a) ^ 2 -
      2 * (1 - b * w / a) ^ 2 < 0 := by
  rw [normalized_factorization a b w (ne_of_gt ha)]
  exact mul_neg_of_pos_of_neg (by nlinarith [sq_nonneg (b / a)]) (by linarith)

/-- An explicit finite-amplitude sufficient condition, prior to taking any limit. -/
theorem finite_amplitude_cone {c j v p : ℝ} (hp : 0 < p)
    (hP : 2 < p * c) (hvP : v < p * c)
    (hscale : 4 * c * v < p * (2 * c ^ 2 - (v - 2) * j ^ 2)) :
    v < coneBound (p * c) (p * j) := by
  by_cases hv : 2 < v
  · apply ((true_cone_iff hv).mpr ⟨hvP, ?_⟩).2
    have hprod : 0 < p * (p * (2 * c ^ 2 - (v - 2) * j ^ 2) - 4 * c * v) :=
      mul_pos hp (sub_pos.mpr hscale)
    have hid : 2 * (p * c - v) ^ 2 - (v - 2) * (p * j) ^ 2 =
        p * (p * (2 * c ^ 2 - (v - 2) * j ^ 2) - 4 * c * v) + 2 * v ^ 2 := by
      ring
    nlinarith [sq_nonneg v]
  · exact relaxed_cone_of_le_two hP (le_of_not_gt hv)

/-- For fixed normalized parameters, a positive leading coefficient and strict
quadratic margin give the relaxed cone at every sufficiently large amplitude. -/
theorem sufficiently_large_amplitude_cone {c j v : ℝ} (hc : 0 < c)
    (hmargin : (v - 2) * j ^ 2 < 2 * c ^ 2) :
    ∃ p₀ : ℝ, ∀ p : ℝ, p₀ < p →
      2 < p * c ∧ v < coneBound (p * c) (p * j) := by
  let δ := 2 * c ^ 2 - (v - 2) * j ^ 2
  have hδ : 0 < δ := sub_pos.mpr hmargin
  let p₀ := max 0 (max (2 / c) (max (v / c) (4 * c * v / δ)))
  refine ⟨p₀, fun p hlarge => ?_⟩
  have h₀ : 0 ≤ p₀ := le_max_left _ _
  have h₂ : 2 / c ≤ p₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hᵥ : v / c ≤ p₀ :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hδbound : 4 * c * v / δ ≤ p₀ :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hP : 2 < p * c := (div_lt_iff₀ hc).mp (lt_of_le_of_lt h₂ hlarge)
  refine ⟨hP, finite_amplitude_cone (lt_of_le_of_lt h₀ hlarge) hP ?_ ?_⟩
  · exact (div_lt_iff₀ hc).mp (lt_of_le_of_lt hᵥ hlarge)
  · exact (div_lt_iff₀ hδ).mp (lt_of_le_of_lt hδbound hlarge)

/-- Equation (11) is sufficient at all sufficiently large positive stress
amplitudes for each fixed triple of parameters. -/
theorem equation_eleven_sufficient {a b w : ℝ} (ha : 0 < a)
    (hfirst : 0 < a - b * w)
    (hsecond : 2 * b * w + b ^ 2 / a + (a - 2) * w ^ 2 < 2) :
    ∃ p₀ : ℝ, ∀ p : ℝ, p₀ < p →
      2 < p * (1 - b * w / a) ∧ a * (1 + (b / a) ^ 2) <
        coneBound (p * (1 - b * w / a)) (p * (w + b / a)) := by
  apply sufficiently_large_amplitude_cone
  · apply sub_pos.mpr
    exact (div_lt_one ha).mpr (by linarith)
  · have h := normalized_test_negative ha hsecond
    linarith

end NavierStokes.ConeAlgebra

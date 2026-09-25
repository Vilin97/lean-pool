/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.ParameterizedBound

/-!
# Global Wronskian summation for Corvaja--Zannier Proposition 2

This file formalizes the exact real-arithmetic passage from the global
Wronskian divisor inequality to the numerical alternatives consumed by the
proved optimization stage.  The remaining geometric theorem must supply the
displayed summed Wronskian inequality; it is not assumed as an axiom or hidden
in a typeclass.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

/-- The real-arithmetic passage from the global Wronskian inequality to the
displayed gcd bound in Corvaja--Zannier Proposition 2. -/
theorem gcdBound_of_globalWronskianInequality
    (a b chi G heightOutside : ℝ) (h k : ℕ)
    (hn : 0 < h * k + h + k)
    (hGHeight : G ≤ a - heightOutside)
    (hWronskian :
      ((h * k : ℕ) : ℝ) * a - (k : ℝ) * (a + b) -
          (((h * k + h + k : ℕ) : ℝ) *
            (((h * k + h + k : ℕ) : ℝ) - 1) / 2) * chi ≤
        ((h * k + h + k : ℕ) : ℝ) * heightOutside) :
    G ≤
      (((h + 2 * k : ℕ) : ℝ) / ((h * k + h + k : ℕ) : ℝ)) * a +
      ((k : ℝ) / ((h * k + h + k : ℕ) : ℝ)) * b +
      (((((h * k + h + k : ℕ) : ℝ) - 1) / 2) * chi) := by
  let n : ℕ := h * k + h + k
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmain :
      (n : ℝ) * G ≤
        ((h + 2 * k : ℕ) : ℝ) * a + (k : ℝ) * b +
          (((n : ℝ) * ((n : ℝ) - 1) / 2) * chi) := by
    dsimp [n] at hnReal ⊢
    norm_num at hWronskian ⊢
    have hGScaled := mul_le_mul_of_nonneg_left hGHeight hnReal.le
    norm_num at hGScaled
    have hNegHeight :
        -(↑h * ↑k + ↑h + ↑k) * heightOutside ≤
          -(↑h * ↑k) * a + ↑k * (a + b) +
            ((↑h * ↑k + ↑h + ↑k) *
              (↑h * ↑k + ↑h + ↑k - 1) / 2) * chi := by
      linarith
    calc
      (↑h * ↑k + ↑h + ↑k) * G ≤
          (↑h * ↑k + ↑h + ↑k) * (a - heightOutside) := hGScaled
      _ = (↑h * ↑k + ↑h + ↑k) * a -
          (↑h * ↑k + ↑h + ↑k) * heightOutside := by ring
      _ ≤ (↑h * ↑k + ↑h + ↑k) * a +
          (-(↑h * ↑k) * a + ↑k * (a + b) +
            ((↑h * ↑k + ↑h + ↑k) *
              (↑h * ↑k + ↑h + ↑k - 1) / 2) * chi) :=
        by linarith
      _ = (↑h + 2 * ↑k) * a + ↑k * b +
          ((↑h * ↑k + ↑h + ↑k) *
            (↑h * ↑k + ↑h + ↑k - 1) / 2) * chi := by ring
  calc
    G ≤ (((h + 2 * k : ℕ) : ℝ) * a + (k : ℝ) * b +
          (((n : ℝ) * ((n : ℝ) - 1) / 2) * chi)) / (n : ℝ) := by
      apply (le_div_iff₀ hnReal).2
      simpa [mul_comm] using hmain
    _ =
        (((h + 2 * k : ℕ) : ℝ) / ((h * k + h + k : ℕ) : ℝ)) * a +
        ((k : ℝ) / ((h * k + h + k : ℕ) : ℝ)) * b +
        (((((h * k + h + k : ℕ) : ℝ) - 1) / 2) * chi) := by
      dsimp [n]
      field_simp [hnReal.ne']

/-- Proposition 2's numerical alternatives follow once the single outside
height comparison and the summed Wronskian inequality have been established
for every admissible parameter pair outside the degree alternative. -/
theorem propositionTwoNumericalAlternatives_of_globalWronskianInequality
    (a b p chi : ℕ) (G heightOutside : ℝ)
    (hGHeight : G ≤ (a : ℝ) - heightOutside)
    (hWronskian : ∀ h k : ℕ,
      PropositionTwoParametersAreAdmissible a b p h k →
      ¬(a ≤ k ∧ b ≤ h) →
      ((h * k : ℕ) : ℝ) * (a : ℝ) -
          (k : ℝ) * ((a : ℝ) + (b : ℝ)) -
          (((h * k + h + k : ℕ) : ℝ) *
            (((h * k + h + k : ℕ) : ℝ) - 1) / 2) * (chi : ℝ) ≤
        ((h * k + h + k : ℕ) : ℝ) * heightOutside) :
    PropositionTwoNumericalAlternatives a b p chi G := by
  intro h k hadmissible
  by_cases hdegree : a ≤ k ∧ b ≤ h
  · exact Or.inl hdegree
  · exact Or.inr <|
      gcdBound_of_globalWronskianInequality
        (a : ℝ) (b : ℝ) (chi : ℝ) G heightOutside h k
        hadmissible.1 hGHeight (hWronskian h k hadmissible hdegree)

end

end BGS.CorvajaZannier

/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith

/-! # Iterates Seven Flux Triangle

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

namespace AVenhance.Infra.Section4

/-- Triangle allocation preserves all seven actual flux contributions. -/
theorem iterate_seven_flux_triangle (B P C F₁ F₂ R S : ℝ) :
    |(B - P - C + F₁ + F₂) + R| + |S| ≤
      |B| + |P| + |C| + |F₁| + |F₂| + |R| + |S| := by
  have h₁ := abs_sub B P
  have h₂ := abs_sub (B - P) C
  have h₃ := abs_add_le (B - P - C) F₁
  have h₄ := abs_add_le (B - P - C + F₁) F₂
  have h₅ := abs_add_le (B - P - C + F₁ + F₂) R
  linarith only [h₁, h₂, h₃, h₄, h₅]

end AVenhance.Infra.Section4

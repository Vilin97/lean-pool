/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.WeightedTraceEquation

/-!
# The coset form of the middle-game trace equation

For a general point on a Markoff rotation fiber, the moving torus parameter is not a subgroup
element but an element of a multiplicative coset.  This module records the exact change of
variables from the weighted equation

`alpha * h + beta * h⁻¹ = k + k⁻¹`

to the paper's twisted equation

`g + (alpha * beta) * g⁻¹ = k + k⁻¹`,

where `g` ranges over the coset `alpha * H₁`.  In particular, this change of variables does not
turn the coset into a subgroup.  Any Corvaja--Zannier input used for an arbitrary starting point
must therefore cover these multiplicative cosets.
-/

namespace BGS.Markoff

variable {E : Type*} [Field E] [Fintype E]

/-- Regard a nonzero scalar as a unit. -/
def scalarUnit (alpha : E) (halpha : alpha ≠ 0) : Eˣ := Units.mk0 alpha halpha

/-- The left coset of `H` obtained by multiplying by the nonzero scalar `alpha`. -/
noncomputable def scaledLeftCoset
    (alpha : E) (halpha : alpha ≠ 0) (H : Subgroup Eˣ) : Finset Eˣ := by
  classical
  exact Finset.univ.image fun h : H ↦ scalarUnit alpha halpha * (h : Eˣ)

@[simp]
theorem mem_scaledLeftCoset_iff
    (alpha : E) (halpha : alpha ≠ 0) (H : Subgroup Eˣ) (g : Eˣ) :
    g ∈ scaledLeftCoset alpha halpha H ↔
      ∃ h : H, scalarUnit alpha halpha * (h : Eˣ) = g := by
  classical
  simp [scaledLeftCoset]

/-- Scale the left coordinate of a pair by `alpha`. -/
def scaleLeftPair
    (alpha : E) (halpha : alpha ≠ 0) (H₁ H₂ : Subgroup Eˣ) :
    H₁ × H₂ → Eˣ × H₂ :=
  fun h ↦ (scalarUnit alpha halpha * (h.1 : Eˣ), h.2)

omit [Fintype E] in
theorem scaleLeftPair_injective
    (alpha : E) (halpha : alpha ≠ 0) (H₁ H₂ : Subgroup Eˣ) :
    Function.Injective (scaleLeftPair alpha halpha H₁ H₂) := by
  intro x y hxy
  apply Prod.ext
  · apply Subtype.ext
    apply Units.ext
    have hfirst := congrArg (fun z : Eˣ × H₂ ↦ (z.1 : E)) hxy
    simpa [scaleLeftPair, scalarUnit] using
      (mul_left_cancel₀ halpha hfirst)
  · simpa [scaleLeftPair] using congrArg Prod.snd hxy

omit [Fintype E] in
/-- The weighted and coset equations agree pointwise after the change of variables
`g = alpha * h`. -/
theorem weightedSplitTorusTrace_eq_twistedUnitTrace_scaled
    (alpha beta : E) (halpha : alpha ≠ 0) (h : Eˣ) :
    weightedSplitTorusTrace alpha beta h =
      twistedUnitTrace (alpha * beta) (scalarUnit alpha halpha * h) := by
  simp only [weightedSplitTorusTrace, twistedUnitTrace, scalarUnit, Units.val_mul,
    Units.val_mk0, Units.val_inv_eq_inv_val]
  field_simp [halpha, Units.ne_zero h]

/-- The actual solution finset, transported to the multiplicative coset in the left variable. -/
noncomputable def cosetTraceEquationSolutionsOfWeights
    (alpha beta : E) (halpha : alpha ≠ 0) (H₁ H₂ : Subgroup Eˣ) :
    Finset (Eˣ × H₂) := by
  classical
  exact (weightedTraceEquationSolutions alpha beta H₁ H₂).image
    (scaleLeftPair alpha halpha H₁ H₂)

@[simp]
theorem mem_cosetTraceEquationSolutionsOfWeights_iff
    (alpha beta : E) (halpha : alpha ≠ 0) (H₁ H₂ : Subgroup Eˣ)
    (g : Eˣ × H₂) :
    g ∈ cosetTraceEquationSolutionsOfWeights alpha beta halpha H₁ H₂ ↔
      g.1 ∈ scaledLeftCoset alpha halpha H₁ ∧
        twistedUnitTrace (alpha * beta) g.1 = splitTorusTrace g.2 := by
  classical
  constructor
  · intro hg
    rw [cosetTraceEquationSolutionsOfWeights, Finset.mem_image] at hg
    obtain ⟨h, hh, rfl⟩ := hg
    constructor
    · exact (mem_scaledLeftCoset_iff alpha halpha H₁ _).2 ⟨h.1, rfl⟩
    · change twistedUnitTrace (alpha * beta)
          (scalarUnit alpha halpha * (h.1 : Eˣ)) = splitTorusTrace h.2
      rw [← weightedSplitTorusTrace_eq_twistedUnitTrace_scaled alpha beta halpha h.1]
      exact mem_weightedTraceEquationSolutions_iff.mp hh
  · rintro ⟨hcoset, hequation⟩
    obtain ⟨h₁, hh₁⟩ :=
      (mem_scaledLeftCoset_iff alpha halpha H₁ g.1).mp hcoset
    rw [cosetTraceEquationSolutionsOfWeights, Finset.mem_image]
    refine ⟨(h₁, g.2), ?_, ?_⟩
    · apply mem_weightedTraceEquationSolutions_iff.mpr
      rw [weightedSplitTorusTrace_eq_twistedUnitTrace_scaled alpha beta halpha h₁]
      simpa [hh₁] using hequation
    · exact Prod.ext hh₁ (Subtype.ext rfl)

/-- Scaling the left variable is injective, so the weighted subgroup equation and its exact
coset form have the same number of solutions. -/
theorem cosetTraceEquationSolutionsOfWeights_card
    (alpha beta : E) (halpha : alpha ≠ 0) (H₁ H₂ : Subgroup Eˣ) :
    (cosetTraceEquationSolutionsOfWeights alpha beta halpha H₁ H₂).card =
      (weightedTraceEquationSolutions alpha beta H₁ H₂).card := by
  classical
  exact Finset.card_image_of_injective _
    (scaleLeftPair_injective alpha halpha H₁ H₂)

end BGS.Markoff

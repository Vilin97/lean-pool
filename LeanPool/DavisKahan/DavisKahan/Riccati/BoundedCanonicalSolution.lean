/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedExistence

/-! # Bounded Canonical Solution -/

@[expose] public section

open TauCeti.DavisKahan.Angle


/-!
# Canonical local bounded Riccati solution

This leaf module packages the local bounded Riccati existence, uniqueness, and
sharp smaller-root estimate into one reusable theorem.  It also exposes a
noncomputable canonical solution selected from that unique contractive branch.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- Under the local interval/exterior spectral-gap hypothesis, there is a
unique contractive bounded Riccati solution, and it obeys the exact
smaller-root majorant. -/
theorem existsUnique_contractive_riccati_solution_of_spectrum_gap
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hA0spec : spectrum ℝ H.A0 ⊆ Set.Icc left right)
    (hA1spec : ∀ x ∈ spectrum ℝ H.A1,
      x ≤ left - d ∨ right + d ≤ x)
    (hsmall : 2 * ‖H.B01‖ < d) :
    ∃! X : E0 →L[ℂ] E1,
      SolvesRiccati H X ∧ ‖X‖ < 1 ∧
      ‖X‖ ≤
        2 * ‖H.B01‖ /
          (d + Real.sqrt (d ^ 2 - 4 * ‖H.B01‖ ^ 2)) := by
  obtain ⟨X, hX, hXc, hXbound⟩ :=
    exists_contractive_riccati_solution_of_spectrum_gap
      H hd hlr hA0spec hA1spec hsmall
  refine ⟨X, ⟨hX, hXc, hXbound⟩, ?_⟩
  intro Y hY
  exact unique_contractive_riccati_solution_of_spectrum_gap
    H hd hlr hA0spec hA1spec hsmall hY.1 hX hY.2.1 hXc

/-- The canonical locally selected contractive bounded Riccati solution. -/
noncomputable def canonicalContractiveRiccatiSolution
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hA0spec : spectrum ℝ H.A0 ⊆ Set.Icc left right)
    (hA1spec : ∀ x ∈ spectrum ℝ H.A1,
      x ≤ left - d ∨ right + d ≤ x)
    (hsmall : 2 * ‖H.B01‖ < d) : E0 →L[ℂ] E1 :=
  Classical.choose
    (existsUnique_contractive_riccati_solution_of_spectrum_gap
      H hd hlr hA0spec hA1spec hsmall).exists

/-- The canonical local solution satisfies the Riccati equation. -/
theorem canonicalContractiveRiccatiSolution_solves
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hA0spec : spectrum ℝ H.A0 ⊆ Set.Icc left right)
    (hA1spec : ∀ x ∈ spectrum ℝ H.A1,
      x ≤ left - d ∨ right + d ≤ x)
    (hsmall : 2 * ‖H.B01‖ < d) :
    SolvesRiccati H
      (canonicalContractiveRiccatiSolution
        H hd hlr hA0spec hA1spec hsmall) := by
  exact (Classical.choose_spec
    (existsUnique_contractive_riccati_solution_of_spectrum_gap
      H hd hlr hA0spec hA1spec hsmall).exists).1

/-- The canonical local solution is contractive. -/
theorem canonicalContractiveRiccatiSolution_norm_lt_one
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hA0spec : spectrum ℝ H.A0 ⊆ Set.Icc left right)
    (hA1spec : ∀ x ∈ spectrum ℝ H.A1,
      x ≤ left - d ∨ right + d ≤ x)
    (hsmall : 2 * ‖H.B01‖ < d) :
    ‖canonicalContractiveRiccatiSolution
        H hd hlr hA0spec hA1spec hsmall‖ < 1 := by
  exact (Classical.choose_spec
    (existsUnique_contractive_riccati_solution_of_spectrum_gap
      H hd hlr hA0spec hA1spec hsmall).exists).2.1

/-- The canonical local solution obeys the exact smaller-root bound. -/
theorem canonicalContractiveRiccatiSolution_norm_le_small_root
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hA0spec : spectrum ℝ H.A0 ⊆ Set.Icc left right)
    (hA1spec : ∀ x ∈ spectrum ℝ H.A1,
      x ≤ left - d ∨ right + d ≤ x)
    (hsmall : 2 * ‖H.B01‖ < d) :
    ‖canonicalContractiveRiccatiSolution
        H hd hlr hA0spec hA1spec hsmall‖ ≤
      2 * ‖H.B01‖ /
        (d + Real.sqrt (d ^ 2 - 4 * ‖H.B01‖ ^ 2)) := by
  exact (Classical.choose_spec
    (existsUnique_contractive_riccati_solution_of_spectrum_gap
      H hd hlr hA0spec hA1spec hsmall).exists).2.2

/-- Every contractive bounded Riccati solution under the same gap assumptions
is the canonical locally selected solution. -/
theorem eq_canonicalContractiveRiccatiSolution
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hA0spec : spectrum ℝ H.A0 ⊆ Set.Icc left right)
    (hA1spec : ∀ x ∈ spectrum ℝ H.A1,
      x ≤ left - d ∨ right + d ≤ x)
    (hsmall : 2 * ‖H.B01‖ < d)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati H X) (hXc : ‖X‖ < 1) :
    X = canonicalContractiveRiccatiSolution
      H hd hlr hA0spec hA1spec hsmall := by
  exact unique_contractive_riccati_solution_of_spectrum_gap
    H hd hlr hA0spec hA1spec hsmall hX
      (canonicalContractiveRiccatiSolution_solves
        H hd hlr hA0spec hA1spec hsmall)
      hXc
      (canonicalContractiveRiccatiSolution_norm_lt_one
        H hd hlr hA0spec hA1spec hsmall)

end DavisKahanExt
end TauCeti

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedCanonicalSolution
import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedReduction

/-! # Bounded Canonical Graph -/

open TauCeti.DavisKahan.Angle


/-!
# Canonical local bounded Riccati graph

This leaf module identifies the canonical local contractive Riccati solution
with the unique contractive reducing graph of the bounded self-adjoint block
operator.  It is the geometric bridge from the analytic fixed-point theory to
later graph rotation and block diagonalization, without constructing that
rotation here.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open scoped InnerProductSpace

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- The graph of the canonical local contractive Riccati solution reduces the
bounded self-adjoint block operator. -/
theorem canonicalContractiveRiccatiGraph_reduces
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hA0spec : spectrum ℝ H.A0 ⊆ Set.Icc left right)
    (hA1spec : ∀ x ∈ spectrum ℝ H.A1,
      x ≤ left - d ∨ right + d ≤ x)
    (hsmall : 2 * ‖H.B01‖ < d) :
    ContinuousLinearMap.Reduces (blockOperator H)
      (blockGraph
        (canonicalContractiveRiccatiSolution
          H hd hlr hA0spec hA1spec hsmall)) := by
  exact (blockGraph_reduces_iff_solvesRiccati H _).2
    (canonicalContractiveRiccatiSolution_solves
      H hd hlr hA0spec hA1spec hsmall)

/-- Any contractive reducing graph under the same local spectral assumptions
is the graph of the canonical Riccati solution. -/
theorem eq_canonicalContractiveRiccatiSolution_of_reduces
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hA0spec : spectrum ℝ H.A0 ⊆ Set.Icc left right)
    (hA1spec : ∀ x ∈ spectrum ℝ H.A1,
      x ≤ left - d ∨ right + d ≤ x)
    (hsmall : 2 * ‖H.B01‖ < d)
    {X : E0 →L[ℂ] E1}
    (hred : ContinuousLinearMap.Reduces (blockOperator H) (blockGraph X))
    (hXc : ‖X‖ < 1) :
    X = canonicalContractiveRiccatiSolution
      H hd hlr hA0spec hA1spec hsmall := by
  apply eq_canonicalContractiveRiccatiSolution
    H hd hlr hA0spec hA1spec hsmall
  · exact (blockGraph_reduces_iff_solvesRiccati H X).1 hred
  · exact hXc

/-- Under the local gap condition, the bounded block operator has a unique
contractive reducing graph, and its angular operator obeys the exact
smaller-root estimate. -/
theorem existsUnique_contractive_reducingGraph_of_spectrum_gap
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hA0spec : spectrum ℝ H.A0 ⊆ Set.Icc left right)
    (hA1spec : ∀ x ∈ spectrum ℝ H.A1,
      x ≤ left - d ∨ right + d ≤ x)
    (hsmall : 2 * ‖H.B01‖ < d) :
    ∃! X : E0 →L[ℂ] E1,
      ContinuousLinearMap.Reduces (blockOperator H) (blockGraph X) ∧
      ‖X‖ < 1 ∧
      ‖X‖ ≤
        2 * ‖H.B01‖ /
          (d + Real.sqrt (d ^ 2 - 4 * ‖H.B01‖ ^ 2)) := by
  let X := canonicalContractiveRiccatiSolution
    H hd hlr hA0spec hA1spec hsmall
  refine ⟨X, ?_, ?_⟩
  · exact ⟨
      canonicalContractiveRiccatiGraph_reduces
        H hd hlr hA0spec hA1spec hsmall,
      canonicalContractiveRiccatiSolution_norm_lt_one
        H hd hlr hA0spec hA1spec hsmall,
      canonicalContractiveRiccatiSolution_norm_le_small_root
        H hd hlr hA0spec hA1spec hsmall⟩
  · intro Y hY
    change Y = canonicalContractiveRiccatiSolution
      H hd hlr hA0spec hA1spec hsmall
    exact eq_canonicalContractiveRiccatiSolution_of_reduces
      H hd hlr hA0spec hA1spec hsmall hY.1 hY.2.1

end DavisKahanExt
end TauCeti

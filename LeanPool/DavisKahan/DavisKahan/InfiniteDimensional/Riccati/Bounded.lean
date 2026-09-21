/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedCanonicalGraph
import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedStability
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Riccati.BoundedSpectralEnclosure
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Bounded -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Public bounded Riccati theory

This facade integrates the proof-complete bounded Riccati leaves.  The basic
block definitions live in `BoundedBasic`; graph reduction, sharp local
existence and uniqueness, canonical graph selection, stability, unitary block
diagonalization, spectral transport, block-spectrum decomposition, and
conditional spectral enclosures are imported above.

The local gap theorems use the genuine spectra of the two diagonal blocks over
a complex Hilbert space.  Their majorant is stated in the algebraic smaller-root
form proved by the bounded existence and sharp-estimate leaves.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- A bounded angular graph reduces the self-adjoint block operator exactly
when the angular operator solves the bounded Riccati equation. -/
theorem graph_reduces_iff_solvesRiccati
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) :
    ContinuousLinearMap.Reduces (blockOperator H) (blockGraph X) ↔ SolvesRiccati H X :=
  blockGraph_reduces_iff_solvesRiccati H X

section Complex

variable {E0c : Type*} [NormedAddCommGroup E0c] [InnerProductSpace ℂ E0c]
  [CompleteSpace E0c]
variable {E1c : Type*} [NormedAddCommGroup E1c] [InnerProductSpace ℂ E1c]
  [CompleteSpace E1c]

/-- Existence of the locally selected contractive bounded Riccati solution
under a genuine interval/exterior spectral gap. -/
theorem exists_riccati_solution_of_gap
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0c) (E1 := E1c))
    {left right d : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hA0spec : spectrum ℝ H.A0 ⊆ Set.Icc left right)
    (hA1spec : ∀ x ∈ spectrum ℝ H.A1,
      x ≤ left - d ∨ right + d ≤ x)
    (hsmall : 2 * ‖H.B01‖ < d) :
    ∃ X : E0c →L[ℂ] E1c,
      SolvesRiccati H X ∧ ‖X‖ < 1 ∧
      ‖X‖ ≤
        2 * ‖H.B01‖ /
          (d + Real.sqrt (d ^ 2 - 4 * ‖H.B01‖ ^ 2)) :=
  exists_contractive_riccati_solution_of_spectrum_gap
    H hd hlr hA0spec hA1spec hsmall

/-- Sharp smaller-root estimate for a contractive bounded Riccati solution. -/
theorem norm_riccati_solution_le
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0c) (E1 := E1c))
    {left right d : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hA0spec : spectrum ℝ H.A0 ⊆ Set.Icc left right)
    (hA1spec : ∀ x ∈ spectrum ℝ H.A1,
      x ≤ left - d ∨ right + d ≤ x)
    (hsmall : 2 * ‖H.B01‖ < d)
    {X : E0c →L[ℂ] E1c} (hX : SolvesRiccati H X)
    (hXc : ‖X‖ < 1) :
    ‖X‖ ≤
      2 * ‖H.B01‖ /
        (d + Real.sqrt (d ^ 2 - 4 * ‖H.B01‖ ^ 2)) :=
  norm_riccati_solution_le_small_root_of_contractive_spectrum_gap
    H hd hlr hA0spec hA1spec hsmall hX hXc

/-- Uniqueness of the contractive bounded Riccati solution under the local
spectral-gap threshold. -/
theorem unique_contractive_riccati_solution
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0c) (E1 := E1c))
    {left right d : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hA0spec : spectrum ℝ H.A0 ⊆ Set.Icc left right)
    (hA1spec : ∀ x ∈ spectrum ℝ H.A1,
      x ≤ left - d ∨ right + d ≤ x)
    (hsmall : 2 * ‖H.B01‖ < d)
    {X Y : E0c →L[ℂ] E1c}
    (hX : SolvesRiccati H X) (hY : SolvesRiccati H Y)
    (hXc : ‖X‖ < 1) (hYc : ‖Y‖ < 1) :
    X = Y :=
  unique_contractive_riccati_solution_of_spectrum_gap
    H hd hlr hA0spec hA1spec hsmall hX hY hXc hYc

/-- Canonical unitary block diagonalization supplied by any bounded complex
Riccati solution. -/
theorem blockDiagonalization_of_riccati
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0c) (E1 := E1c))
    {X : E0c →L[ℂ] E1c} (hX : SolvesRiccati H X) :
    ∃ W Winv : WithLp 2 (E0c × E1c) →L[ℂ] WithLp 2 (E0c × E1c),
      ∃ D0 : E0c →L[ℂ] E0c, ∃ D1 : E1c →L[ℂ] E1c,
      TauCeti.LinearPMap.IsUnitaryOperator W ∧ TauCeti.LinearPMap.IsUnitaryOperator Winv ∧
      Winv ∘L W = ContinuousLinearMap.id ℂ (WithLp 2 (E0c × E1c)) ∧
      W ∘L Winv = ContinuousLinearMap.id ℂ (WithLp 2 (E0c × E1c)) ∧
      Winv ∘L blockOperator H ∘L W = blockDiagonalOperator D0 D1 :=
  complex_blockDiagonalization_of_riccati H hX

end Complex

end DavisKahanExt
end TauCeti

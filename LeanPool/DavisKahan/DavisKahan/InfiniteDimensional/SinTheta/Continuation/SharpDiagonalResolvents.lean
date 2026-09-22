/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.SharpSourceSpectrum
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.ResolventOperator
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Sharp Diagonal Resolvents -/

open TauCeti.DavisKahan.Sylvester

/-!
# Diagonal resolvent data for sharp off-diagonal continuation

The sharp block-resolvent argument needs more than diagonal spectral
inclusions: at each complex contour point it needs actual inverses of the two
diagonal shifted blocks, sharp inverse-distance norm bounds for those
inverses, and the pathwise cross-block norm estimates.

This leaf converts the finite interval/exterior source-spectrum data into
exactly that package.  It does not yet invert the full `2 × 2` block operator;
the subsequent Schur-complement leaf consumes the data proved here.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open Set
open scoped InnerProductSpace

universe v

section DiagonalResolventData

variable {Hspace : Type v} [NormedAddCommGroup Hspace]
  [InnerProductSpace ℂ Hspace] [CompleteSpace Hspace]

/-- Spectral inclusion in a set transfers a uniform distance bound on that set
to the real spectrum. -/
theorem spectralDistance_of_subset
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    
    (T : E →L[ℂ] E) {S : Set ℝ}
    (hT : realSpectrum T ⊆ S)
    (z : ℂ) (delta : ℝ)
    (hsep : ∀ lam ∈ S, delta ≤ ‖z - (lam : ℂ)‖) :
    ∀ lam ∈ realSpectrum T, delta ≤ ‖z - (lam : ℂ)‖ := by
  intro lam hlam
  exact hsep lam (hT hlam)

/-- A finite-gap configuration supplies both diagonal shifted inverses, their
sharp inverse-distance bounds, and both pathwise cross-block norm estimates.

The geometric assumptions `hsep0` and `hsep1` are deliberately stated on the
interval and exterior sets themselves.  A later contour-geometry leaf can
discharge them without reopening any operator theory. -/
theorem _root_.TauCeti.DavisKahan.Foundation.FiniteGapConfiguration.exists_operatorPath_diagonalResolventData
    (A K : Hspace →L[ℂ] Hspace)
    (U : Submodule ℂ Hspace) [U.HasOrthogonalProjection]
    [CompleteSpace U] [CompleteSpace (Uᗮ : Submodule ℂ Hspace)]
    (hU : A.Reduces U) (hK : Submodule.IsOffDiagonal U K)
    {d : ℝ} (hfinite : FiniteGapConfiguration A U d) :
    ∃ left right : ℝ, left ≤ right ∧
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ∀ hpath : (operatorPath A K t).IsSymmetric,
      ∀ z : ℂ, ∀ delta0 delta1 : ℝ,
        0 < delta0 → 0 < delta1 →
        (∀ lam ∈ Set.Icc left right,
          delta0 ≤ ‖z - (lam : ℂ)‖) →
        (∀ lam ∈ {x : ℝ | x ≤ left - d ∨ right + d ≤ x},
          delta1 ≤ ‖z - (lam : ℂ)‖) →
        let Ht := subspaceBlockOperatorData (operatorPath A K t) U hpath
        InResolventSet Ht.A0 z ∧
        ‖resolventOperator Ht.A0 z‖ ≤ delta0⁻¹ ∧
        InResolventSet Ht.A1 z ∧
        ‖resolventOperator Ht.A1 z‖ ≤ delta1⁻¹ ∧
        ‖Ht.B01‖ ≤ t * ‖K‖ ∧
        ‖Ht.B10‖ ≤ t * ‖K‖ := by
  obtain ⟨left, right, hlr, hdata⟩ :=
    hfinite.exists_operatorPath_block_enclosureData A K U hU hK
  refine ⟨left, right, hlr, ?_⟩
  intro t ht hpath z delta0 delta1 hdelta0 hdelta1 hsep0 hsep1
  let Ht := subspaceBlockOperatorData (operatorPath A K t) U hpath
  obtain ⟨hspec0, hspec1, hB01, hB10⟩ := hdata t ht hpath
  have hdiag0 := complex_inResolventSet_and_norm_resolvent_le_inv_distance
    Ht.A0 Ht.selfAdjoint0 z delta0 hdelta0
      (spectralDistance_of_subset Ht.A0 hspec0 z delta0 hsep0)
  have hdiag1 := complex_inResolventSet_and_norm_resolvent_le_inv_distance
    Ht.A1 Ht.selfAdjoint1 z delta1 hdelta1
      (spectralDistance_of_subset Ht.A1 hspec1 z delta1 hsep1)
  exact ⟨hdiag0.1, hdiag0.2, hdiag1.1, hdiag1.2, hB01, hB10⟩

end DiagonalResolventData

end DavisKahanExt
end TauCeti

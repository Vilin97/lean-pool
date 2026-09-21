/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.Main
import LeanPool.UniformSheafyTateDomains.AdicSpaces.SheafyRingEquivTransport

/-!
# Strong sheafiness of the weighted-parity algebra, in the Tate-extension vocabulary

[WP-paper] thm:parity-strongly-sheafy, final paragraph (eq:strong-sheafy-decomposition):

> "Finally, for auxiliary Tate variables V₁,…,Vₛ one has, isometrically,
>   𝒜⟨V₁,…,Vₛ⟩ ≅ ⊕̂^{c₀}_μ 𝒜_N⟨V₁,…,Vₛ⟩ e_μ.
> The finite heads remain affinoid, the retractions and perturbation lemma are
> unchanged, and the preceding proof applies verbatim. Therefore every finite Tate
> extension is sheafy."

The library realises the Tate extension `𝒜⟨V₁,…,Vₛ⟩` as
`restrictedMvPowerSeriesSubring s (WPA K w)` with the canonical
`mvTateAlgebraTopology'`, identifies it with the shifted-weight weighted-parity
algebra via `tateExtEquiv` (bicontinuous, W24b), and has already proved sheafiness
of the latter for every valid pair (`wp_stronglySheafy`). This file transports the
statement across the identification, so that strong sheafiness is stated on the
Tate-extension object itself. Combined with `weightedParity_not_stablyUniform`,
this makes "strongly sheafy does not imply stably uniform" fully formal.
-/

@[expose] public section

noncomputable section

namespace WeightedParity

open FiniteJetOver ValuationSpectrum TopologicalRing MvTateAlgebra
open scoped NormedField Valued

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {w : ℕ → ℕ}

/-- **A-L1 (uniformity bridge)**: the Tate extension `𝒜⟨V₁,…,Vₛ⟩` is complete for
the right uniformity of its canonical topology. Content: `mvTate_completeSpace`
(completeness at `mvTateUniformSpace`) transported across the identification of
the two uniform structures on a topological add group ([WP-paper] §8: the
`c₀`-sum is complete). -/
theorem wp_tateExt_completeSpace (s : ℕ) :
    letI := mvTateAlgebraTopology' (A := WPA K w) s
    haveI := mvTateAlgebraTopology'_isTopologicalRing (A := WPA K w) s
    @CompleteSpace ↥(restrictedMvPowerSeriesSubring s (WPA K w))
      (IsTopologicalAddGroup.rightUniformSpace _) := by
  exact mvTate_completeSpace (A := WPA K w) s inferInstance

/-- **Strong sheafiness, Tate-extension vocabulary** ([WP-paper]
thm:parity-strongly-sheafy via eq:strong-sheafy-decomposition): the project's
Tate extension `𝒜⟨V₁,…,Vₛ⟩` of the weighted-parity algebra, with its canonical
mv-Tate-algebra topology, is sheafy for every valid ring of integral elements. -/
theorem wp_tateExt_isSheafyComplete (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) (s : ℕ) :
    letI := mvTateAlgebraTopology' (A := WPA K w) s
    haveI := mvTate_isTateRing (A := WPA K w) s
    haveI := mvTate_t2Space (A := WPA K w) s
    haveI := mvTate_nonarchimedean (A := WPA K w) s
    haveI := mvTateAlgebraTopology'_isTopologicalRing (A := WPA K w) s
    haveI : @CompleteSpace ↥(restrictedMvPowerSeriesSubring s (WPA K w))
      (IsTopologicalAddGroup.rightUniformSpace _) := wp_tateExt_completeSpace (w := w) s
    IsSheafyComplete ↥(restrictedMvPowerSeriesSubring s (WPA K w)) := by
  letI := mvTateAlgebraTopology' (A := WPA K w) s
  haveI := mvTate_isTateRing (A := WPA K w) s
  haveI := mvTate_t2Space (A := WPA K w) s
  haveI := mvTate_nonarchimedean (A := WPA K w) s
  haveI := mvTateAlgebraTopology'_isTopologicalRing (A := WPA K w) s
  haveI : @CompleteSpace ↥(restrictedMvPowerSeriesSubring s (WPA K w))
      (IsTopologicalAddGroup.rightUniformSpace _) := wp_tateExt_completeSpace (w := w) s
  exact (isSheafyComplete_congr
    (A := ↥(restrictedMvPowerSeriesSubring s (WPA K w)))
    (B := WPA K (shiftWeight w s)) (tateExtEquiv s)
    (tateExtToWPA_continuous s) (tateExtEquiv_symm_continuous s)).mpr
    (wp_stronglySheafy ϖ hK₀ s)

/-- Layer 2: strong sheafiness of `𝒜⟨V₁,…,Vₛ⟩` over a base whose valuation ring is
a DVR (the uniformizer is chosen, not carried). -/
theorem wp_tateExt_isSheafyComplete_of_dvr [IsDiscreteValuationRing 𝒪[K]] (s : ℕ) :
    letI := mvTateAlgebraTopology' (A := WPA K w) s
    haveI := mvTate_isTateRing (A := WPA K w) s
    haveI := mvTate_t2Space (A := WPA K w) s
    haveI := mvTate_nonarchimedean (A := WPA K w) s
    haveI := mvTateAlgebraTopology'_isTopologicalRing (A := WPA K w) s
    haveI : @CompleteSpace ↥(restrictedMvPowerSeriesSubring s (WPA K w))
      (IsTopologicalAddGroup.rightUniformSpace _) := wp_tateExt_completeSpace (w := w) s
    IsSheafyComplete ↥(restrictedMvPowerSeriesSubring s (WPA K w)) := by
  exact wp_tateExt_isSheafyComplete (Uniformizer.ofDVR K)
    (FiniteJetOver.isNoetherianRing_unitBall K) s

end WeightedParity

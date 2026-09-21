/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetSheafTransfer
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetChart

/-!
# The finite-jet pinching algebra: headline theorems ([FJP] Theorem 1.3)

Source: [FJP] Theorem 1.3 (verbatim): "The Huber ring 𝒜 is a nonnoetherian uniform strongly
sheafy domain, but it is not stably uniform. More precisely, the rational localization
`𝒜⟨W/ϖ⟩ ≅ k⟨X,Q⟩/(Q²)`, `X = W/ϖ`, is strongly noetherian and sheafy, but is not uniform."

One conclusion per declaration (project statement-splitting rule). Strong sheafiness
([FJP] Cor 5.5) is the campaign's stretch goal M7 and is not asserted here.

`𝓐 = FiniteJet.JetA F` is the pinching algebra over `K = LaurentSeries F`
(`FiniteJetRings.lean`), with its maximal plus ring.
-/

namespace FiniteJet

variable (F : Type*) [Field F]

/-- **[FJP] Theorem 1.3 (sheafy)**: `(𝓐, 𝓐°)` is sheafy. -/
theorem finiteJet_isSheafy : ValuationSpectrum.IsSheafy (JetA F) :=
  isSheafy_JetA F

/-- **[FJP] Theorem 1.3 (uniform)**: 𝓐 is uniform. -/
theorem finiteJet_isUniform : TopologicalRing.IsUniform (JetA F) :=
  isUniform_JetA F

/-- **[FJP] Theorem 1.3 (domain)**: 𝓐 is an integral domain. -/
theorem finiteJet_isDomain : IsDomain (JetA F) :=
  inferInstance

/-- **[FJP] Theorem 1.3 (nonnoetherian)**: 𝓐 is not noetherian. -/
theorem finiteJet_not_noetherian : ¬ IsNoetherianRing (JetA F) :=
  not_isNoetherianRing_JetA F

/-- **[FJP] Theorem 1.3 (not stably uniform)**: 𝓐 is not stably uniform. -/
theorem finiteJet_not_stablyUniform : ¬ TopologicalRing.IsStablyUniform (JetA F) :=
  not_isStablyUniform_JetA F

end FiniteJet

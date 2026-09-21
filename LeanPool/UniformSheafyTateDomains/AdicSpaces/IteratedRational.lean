/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.PresheafTateStructure
import LeanPool.UniformSheafyTateDomains.AdicSpaces.TopologyComparison
import LeanPool.UniformSheafyTateDomains.AdicSpaces.CompletionLocalization
import LeanPool.UniformSheafyTateDomains.AdicSpaces.PresheafFunctoriality

/-!
# Iterated Rational Localization (Wedhorn Lemma 2.13): helpers

Helper lemmas about `canonicalMap` and `restrictionMapHom` that feed into the
iterated rational identification and the Laurent bridges. The Wedhorn
Example 6.38 machinery used to live here under the name `Example638`; that
block now lives in `«Adic spaces».Example638` (extracted to break the cycle
with `LaurentRefinement`).

## References
* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 2.13, Prop 8.7.
-/

namespace ValuationSpectrum

open UniformSpace

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]

section Helpers

variable [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]

/-- `D₀.canonicalMap D₀.s` is a unit in `presheafValue D₀`, because `D₀.s`
becomes a unit under `algebraMap A (Localization.Away D₀.s)` (definition of
localization) and `D₀.coeRingHom` preserves units. -/
theorem canonicalMap_s_isUnit (D₀ : RationalLocData A) :
    IsUnit (D₀.canonicalMap D₀.s) := by
  simp only [RationalLocData.canonicalMap, RingHom.coe_comp, Function.comp_apply]
  exact RingHom.isUnit_map D₀.coeRingHom
    (IsLocalization.Away.algebraMap_isUnit D₀.s)

omit [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A] in
/-- Compatibility: `restrictionMapHom D₀ D' hsub ∘ D₀.canonicalMap = D'.canonicalMap`.
Thin wrapper over the upstream `restrictionMapHom_canonicalMap_generic`
(`PresheafFunctoriality.lean`); the section's Tate/noetherian/T2/nonarch instances
are unused here and `omit`-ted. -/
theorem restrictionMapHom_canonicalMap (D₀ D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D₀.T D₀.s) (a : A) :
    restrictionMapHom D₀ D' h (D₀.canonicalMap a) = D'.canonicalMap a :=
  restrictionMapHom_canonicalMap_generic D₀ D' h a

end Helpers

-- DELETED 2026-06-11 (false orphan): the audit-pass-3 section held only
-- `presheafValue_eq_quotient_AlangleX_iterated`, a `sorry` whose own docstring
-- flagged it FALSE (b2_log #6: `MvPolynomial D.T A ⧸ (s·Xₜ − t)` = the *algebraic*
-- `A[1/s]`, but `presheafValue D` is its *completion* in the localization topology —
-- counterexample `A = ℤ` p-adic, `s = p`: RHS ≅ ℤ, LHS ≅ ℚ_p). It was referenced
-- nowhere, and the FAITHFUL Wedhorn-7.55/Example-6.38 comparison iso `presheafValue D
-- ≃+* C⧸ker` (Tate algebra `restrictedMvPowerSeriesSubring`, NOT `MvPolynomial`) has
-- since landed in `Example638.lean`/`MvTateAlgebraTopology.lean` (axiom-clean). Per the
-- quote-or-delete discipline (false + orphan + superseded), the dead stub is removed.

end ValuationSpectrum

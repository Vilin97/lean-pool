/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.Over.SheafyEndpoints
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.PowerBoundedIntegralElements
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.Over.StrongSheafy

/-!
# Comparator solution: [FJP] Theorem 1.1

Forwards each statement of `Challenge.lean` to the library's proof. This is the module
comparator rebuilds inside the sandbox, so it is deliberately tiny: the project itself is
already built, and only this file is treated as the untrusted submission.

The binder block is identical to the challenge's, so the two elaborate to the same type.

The statements are over a general base — an arbitrary complete ultrametric
nontrivially-normed field whose valuation ring is a DVR — and each forwards to the
`FiniteJetOver.*_of_dvr` layer-2 endpoint, which is what the paper's own `<lean>` references
for Theorem 1.1 cite.
-/

@[expose] public section

open FiniteJetOver ValuationSpectrum TopologicalRing MvTateAlgebra
open scoped NormedField Valued

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable [IsDiscreteValuationRing 𝒪[K]]

/-- **[FJP] Theorem 1.1 (sheafy)**. -/
theorem fjp_1_1_isSheafy : IsSheafy (JetA K) := isSheafy_JetA_of_dvr K

/-- **[FJP] Theorem 1.1 (uniform)**. -/
theorem fjp_1_1_isUniform : IsUniform (JetA K) := finiteJet_isUniform_of_dvr K

/-- **[FJP] Theorem 1.1 (domain)**. -/
theorem fjp_1_1_isDomain : IsDomain (JetA K) := finiteJet_isDomain K

/-- **[FJP] Theorem 1.1 (nonnoetherian)**. -/
theorem fjp_1_1_not_isNoetherianRing : ¬ IsNoetherianRing (JetA K) :=
  finiteJet_not_noetherian K

/-- **[FJP] Theorem 1.1 (`𝓐° = 𝓐₀`)**. -/
theorem fjp_1_1_powerBounded_eq_unitBall :
    powerBoundedSubring (JetA K) = (FiniteJet.unitBall (JetA K) : Set (JetA K)) :=
  finiteJet_powerBounded_eq_unitBall_of_dvr K

/-- **[FJP] Theorem 1.1 (strongly sheafy)**. -/
theorem fjp_1_1_stronglySheafy (n : ℕ) :
    letI := mvTateAlgebraTopology' (A := JetA K) n
    haveI := mvTate_isTateRing (A := JetA K) n
    haveI := mvTate_t2Space (A := JetA K) n
    haveI := mvTate_nonarchimedean (A := JetA K) n
    haveI := mvTateAlgebraTopology'_isTopologicalRing (A := JetA K) n
    haveI : @CompleteSpace ↥(restrictedMvPowerSeriesSubring n (JetA K))
      (IsTopologicalAddGroup.rightUniformSpace _) :=
        mvTate_completeSpace (A := JetA K) n inferInstance
    IsSheafyComplete ↥(restrictedMvPowerSeriesSubring n (JetA K)) :=
  finiteJet_tateExt_isSheafyComplete_of_dvr K n

/-- **[FJP] Theorem 1.1 (not stably uniform)**. -/
theorem fjp_1_1_not_isStablyUniform : ¬ IsStablyUniform (JetA K) :=
  finiteJet_not_stablyUniform_of_dvr K

/-- **[FJP] Theorem 1.1 (`𝓐°` is a ring of integral elements)**. -/
theorem fjp_1_1_powerBounded_isRingOfIntegralElements :
    IsRingOfIntegralElements ((ringPlus (JetA K) : Subring (JetA K))) := inferInstance

/-- **[FJP] Theorem 1.1 (the Tate extensions have a ring of integral elements)**. -/
theorem fjp_1_1_tateExt_powerBounded_isRingOfIntegralElements (n : ℕ) :
    letI := mvTateAlgebraTopology' (A := JetA K) n
    haveI := mvTate_isTateRing (A := JetA K) n
    haveI := mvTate_nonarchimedean (A := JetA K) n
    haveI := mvTateAlgebraTopology'_isTopologicalRing (A := JetA K) n
    IsRingOfIntegralElements
      (TopologicalRing.powerBoundedSubring.toSubring
        ↥(restrictedMvPowerSeriesSubring n (JetA K))) := by
  letI := mvTateAlgebraTopology' (A := JetA K) n
  haveI := mvTate_isTateRing (A := JetA K) n
  haveI := mvTate_nonarchimedean (A := JetA K) n
  haveI := mvTateAlgebraTopology'_isTopologicalRing (A := JetA K) n
  exact isRingOfIntegralElements_powerBoundedSubring

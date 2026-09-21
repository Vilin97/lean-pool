/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.Over.ExtendedSheafyTransport
import LeanPool.UniformSheafyTateDomains.AdicSpaces.SheafyRingEquivTransport

/-!
# Strong sheafiness of the finite-jet algebra over a general nonarchimedean base

Every finite Tate extension of `JetA K`, equipped with its canonical Tate-algebra topology,
is sheafy for every valid ring of integral elements. The core theorem applies to
a complete ultrametric field with a uniformizer and noetherian norm unit ball;
the `_of_dvr` endpoint supplies the last two hypotheses from a discrete
valuation ring structure on `𝒪[K]`.
-/

@[expose] public section

noncomputable section

namespace FiniteJetOver

open FiniteJet ValuationSpectrum TopologicalRing MvTateAlgebra
open scoped NormedField Valued

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The Tate extension of the finite-jet pinching algebra is complete for the right
uniformity of its canonical topology. -/
theorem finiteJet_tateExt_completeSpace (n : ℕ) :
    letI := mvTateAlgebraTopology' (A := JetA K) n
    haveI := mvTateAlgebraTopology'_isTopologicalRing (A := JetA K) n
    @CompleteSpace ↥(restrictedMvPowerSeriesSubring n (JetA K))
      (IsTopologicalAddGroup.rightUniformSpace _) := by
  exact mvTate_completeSpace (A := JetA K) n inferInstance

/-- Every finite Tate extension of the finite-jet pinching algebra is sheafy for every
valid ring of integral elements. -/
theorem finiteJet_tateExt_isSheafyComplete (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) (n : ℕ) :
    letI := mvTateAlgebraTopology' (A := JetA K) n
    haveI := mvTate_isTateRing (A := JetA K) n
    haveI := mvTate_t2Space (A := JetA K) n
    haveI := mvTate_nonarchimedean (A := JetA K) n
    haveI := mvTateAlgebraTopology'_isTopologicalRing (A := JetA K) n
    haveI : @CompleteSpace ↥(restrictedMvPowerSeriesSubring n (JetA K))
      (IsTopologicalAddGroup.rightUniformSpace _) := finiteJet_tateExt_completeSpace K n
    IsSheafyComplete ↥(restrictedMvPowerSeriesSubring n (JetA K)) := by
  let _i := mvTateAlgebraTopology' (A := JetA K) n
  have := mvTate_isTateRing (A := JetA K) n
  have := mvTate_t2Space (A := JetA K) n
  have := mvTate_nonarchimedean (A := JetA K) n
  have := mvTateAlgebraTopology'_isTopologicalRing (A := JetA K) n
  have : @CompleteSpace ↥(restrictedMvPowerSeriesSubring n (JetA K))
      (IsTopologicalAddGroup.rightUniformSpace _) := finiteJet_tateExt_completeSpace K n
  exact (isSheafyComplete_congr (UnitDiscExample.restrictedGaussEquiv (JetA K) n)
    (gaussToTate_continuous K n) (tateToGauss_continuous K n)).mp
    (ext_isSheafyComplete K n ϖ hK₀)

/-- Strong sheafiness over a base whose valuation ring is a discrete valuation ring. -/
theorem finiteJet_tateExt_isSheafyComplete_of_dvr [IsDiscreteValuationRing 𝒪[K]] (n : ℕ) :
    letI := mvTateAlgebraTopology' (A := JetA K) n
    haveI := mvTate_isTateRing (A := JetA K) n
    haveI := mvTate_t2Space (A := JetA K) n
    haveI := mvTate_nonarchimedean (A := JetA K) n
    haveI := mvTateAlgebraTopology'_isTopologicalRing (A := JetA K) n
    haveI : @CompleteSpace ↥(restrictedMvPowerSeriesSubring n (JetA K))
      (IsTopologicalAddGroup.rightUniformSpace _) := finiteJet_tateExt_completeSpace K n
    IsSheafyComplete ↥(restrictedMvPowerSeriesSubring n (JetA K)) := by
  exact finiteJet_tateExt_isSheafyComplete K (Uniformizer.ofDVR K)
    (isNoetherianRing_unitBall K) n

end FiniteJetOver

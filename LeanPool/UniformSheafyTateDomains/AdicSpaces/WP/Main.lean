/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.UniformDomain
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.Nonnoetherian
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.Sheafy
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.Chart
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.Reduced
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.HeadReduced
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.HeadReducedMaximal
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.GraphCompletedLocal

/-!
# The rationally stably reduced example — headline endpoints ([WP] thm 6.2)

The paper's example is the weight `w = id` instance of the weighted-parity
construction.  This file states the headline endpoints ([WP]
thm:rationally-reduced-example) at that weight, in two layers following the FJP-CDVF
convention: an explicit-uniformizer layer and a `[IsDiscreteValuationRing 𝒪[K]]`
layer (`Uniformizer.ofDVR`).

* (1) `𝒜` is a complete uniform Tate algebra, an integral domain, not noetherian,
  with `𝒜° = 𝒜₀`;
* (2) `(𝒜, 𝒜°)` is (strongly) sheafy;
* (3) `𝒜` is rationally stably reduced — CONDITIONAL on the quarantined
  head-reducedness input `HeadLocsReduced` (BGR 7.3.2/10 at the heads; its own
  sub-campaign);
* (4) the chart `ℬ = 𝒜⟨W/ϖ⟩` is an integral domain and not uniform; hence `𝒜` is
  not stably uniform, with a REDUCED witness.
-/

@[expose] public section

namespace WeightedParity

open FiniteJetOver ValuationSpectrum TopologicalRing

/-- The paper's weight: `w = id` ([WP] eq:parity-weight, `ω(ν) = ∑_{ν_n odd} n`). -/
def idWeight : ℕ → ℕ := fun n => n

theorem idWeight_pos : ∀ n, 1 ≤ n → 1 ≤ idWeight n := fun _ hn => hn

theorem idWeight_unbounded : ∀ M : ℕ, ∃ n : ℕ, 1 ≤ n ∧ M ≤ idWeight n := fun M =>
  ⟨M + 1, Nat.succ_le_succ (Nat.zero_le M), Nat.le_succ M⟩

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The weighted-parity algebra of the paper ([WP] eq:parity-algebra at `w = id`). -/
abbrev WPAid : Type _ := WPA K idWeight

/-! ### Layer 1: explicit uniformizer -/

variable {K} in
/-- [WP] thm 6.2 (1): `𝒜` is uniform. -/
theorem weightedParity_isUniform (ϖ : Uniformizer K) : IsUniform (WPAid K) :=
  isUniform_WPA ϖ

/-- [WP] thm 6.2 (1): `𝒜` is an integral domain. -/
theorem weightedParity_isDomain : IsDomain (WPAid K) := inferInstance

/-- [WP] thm 6.2 (1): `𝒜` is not noetherian. -/
theorem weightedParity_not_noetherian : ¬ IsNoetherianRing (WPAid K) :=
  not_isNoetherianRing_WPA K idWeight idWeight_pos

variable {K} in
/-- [WP] thm 6.2 (1): `𝒜° = 𝒜₀` (power-bounded = unit ball). -/
theorem weightedParity_powerBounded_eq_unitBall (ϖ : Uniformizer K) :
    powerBoundedSubring (WPAid K) =
      (FiniteJet.unitBall (WPAid K) : Set (WPAid K)) :=
  powerBoundedSubring_eq_unitBall ϖ

variable {K} in
/-- [WP] thm 6.2 (2): `(𝒜, 𝒜°)` is sheafy (every valid pair). -/
theorem weightedParity_isSheafyComplete (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsSheafyComplete (WPAid K) :=
  wp_isSheafyComplete ϖ hK₀

variable {K} in
/-- [WP] thm 6.2 (2): strong sheafiness — every Tate extension, every valid pair
(the shifted-weight family; see `tateExtEquiv` for the project-vocabulary bridge). -/
theorem weightedParity_stronglySheafy (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) (s : ℕ) :
    IsSheafyComplete (WPA K (shiftWeight idWeight s)) :=
  wp_stronglySheafy ϖ hK₀ s

variable {K} in
/-- [WP] thm 6.2 (3), conditional form: `𝒜` is rationally stably reduced, given the
quarantined head input (BGR 7.3.2/10 at the heads). -/
theorem weightedParity_chainReduced (hred : HeadLocsReduced K idWeight)
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) (n : ℕ) :
    ChainReduced (WPAid K) n :=
  chainReduced_WPA hred ϖ hK₀ n

variable {K} in
/-- [WP] thm 6.2 (3), unconditional form (HRW-6 assembly).  The head leaves are
discharged through the maximal-ideal route: the completed locals of the head at
maximals are reduced, and the graph model has the same completed locals
(`qHead_completedLocal_comparison'`, which uses Wedhorn 8.30 flatness — the one
remaining central input). -/
theorem weightedParity_chainReduced_unconditional (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) (n : ℕ) :
    ChainReduced (WPAid K) n :=
  haveI := ϖ.isDiscreteValuationRing hK₀
  chainReduced_WPA (headLocsReduced'' (w := idWeight) ϖ hK₀) ϖ hK₀ n

variable {K} in
/-- [WP] thm 6.2 (4): the chart `ℬ = 𝒜⟨W/ϖ⟩` is an integral domain. -/
theorem weightedParity_chart_isDomain (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsDomain (presheafValue (chartDatum (w := idWeight) ϖ)) :=
  isDomain_chart ϖ hK₀

variable {K} in
/-- [WP] thm 6.2 (4): the chart is not uniform. -/
theorem weightedParity_chart_not_isUniform (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    ¬ IsUniform (presheafValue (chartDatum (w := idWeight) ϖ)) :=
  not_isUniform_chart idWeight_unbounded ϖ hK₀

variable {K} in
/-- [WP] thm 6.2, "In particular": `𝒜` is not stably uniform. -/
theorem weightedParity_not_stablyUniform (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    ¬ IsStablyUniform (WPAid K) :=
  not_isStablyUniform_WPA idWeight_unbounded ϖ hK₀

/-! ### Layer 2: `[IsDiscreteValuationRing 𝒪[K]]` -/

section DVR

open scoped NormedField Valued

variable [IsDiscreteValuationRing 𝒪[K]]

theorem weightedParity_isUniform_of_dvr : IsUniform (WPAid K) :=
  weightedParity_isUniform (Uniformizer.ofDVR K)

theorem weightedParity_isSheafyComplete_of_dvr : IsSheafyComplete (WPAid K) :=
  weightedParity_isSheafyComplete (Uniformizer.ofDVR K)
    (FiniteJetOver.isNoetherianRing_unitBall K)

theorem weightedParity_stronglySheafy_of_dvr (s : ℕ) :
    IsSheafyComplete (WPA K (shiftWeight idWeight s)) :=
  weightedParity_stronglySheafy (Uniformizer.ofDVR K)
    (FiniteJetOver.isNoetherianRing_unitBall K) s

theorem weightedParity_chainReduced_of_dvr (hred : HeadLocsReduced K idWeight)
    (n : ℕ) : ChainReduced (WPAid K) n :=
  weightedParity_chainReduced hred (Uniformizer.ofDVR K)
    (FiniteJetOver.isNoetherianRing_unitBall K) n

theorem weightedParity_chainReduced_unconditional_of_dvr (n : ℕ) :
    ChainReduced (WPAid K) n :=
  weightedParity_chainReduced_unconditional (Uniformizer.ofDVR K)
    (FiniteJetOver.isNoetherianRing_unitBall K) n

theorem weightedParity_not_stablyUniform_of_dvr : ¬ IsStablyUniform (WPAid K) :=
  weightedParity_not_stablyUniform (Uniformizer.ofDVR K)
    (FiniteJetOver.isNoetherianRing_unitBall K)

end DVR

end WeightedParity

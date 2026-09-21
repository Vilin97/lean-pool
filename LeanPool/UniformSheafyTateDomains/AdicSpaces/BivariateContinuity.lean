/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.LaurentOverlap
import LeanPool.UniformSheafyTateDomains.AdicSpaces.TopologyComparison

/-!
# Bivariate continuity of `example638Bivariate_evalHom` / `_forwardHom`

This module proves the **bivariate analog** of
`tateEvalPresheafHom_continuous_canonical` (TopologyComparison.lean:2430) for
the overlap-shaped Wedhorn Example 6.39 setup, then derives the
quotient-lift continuity for `example638Bivariate_forwardHom`.

For a complete strongly noetherian Tate ring `B`, a pair of definition
`P : PairOfDefinition B` with `IsNoetherianRing P.A₀`, and an element
`b ∈ B`, the bivariate evaluation hom
`example638Bivariate_evalHom B P b : TateAlgebra₂ B →+* presheafValue
(overlapDatum B P b)` is continuous for the canonical bivariate Tate
topology on `TateAlgebra₂ B`. The proof structurally mirrors the
univariate `tateEvalPresheafHom_continuous_canonical`:

* `V ∈ nhds 0` contains an open subgroup `W` (presheafValue is nonarch).
* The bivariate power range `{canonicalMap(b)^(n 0) · invS^(n 1)}` is
  bounded — product of two bounded power families
  (`canonicalMap_b_isPowerBounded_in_overlap` and
  `invS_isPowerBounded_in_overlap`).
* Standard nhds-of-0 boundedness gives `U ∈ nhds 0` with bivRange · U ⊆ W.
* `canonicalMap` is continuous, so for some `N`, image `P.I^N ⊆ canonicalMap⁻¹(U)`.
* For `h ∈ tateAlgNhd₂ P_B N`, all bivariate coefficients lie in image
  `P.I^N`, so each `evalTerm₂` lies in W.
* Partial sums of `evalTerm₂` stay in `W` (subgroup); they tend to
  `example638Bivariate_evalHom h` (summable); `W` is closed (open
  subgroup) — so the tsum lies in `W ⊆ V`.

The quotient consequence is then derived via
`QuotientRing.isOpenQuotientMap_mk.isQuotientMap.continuous_iff`, using
that `example638Bivariate_forwardHom = Ideal.Quotient.lift _
(example638Bivariate_evalHom B P b) _`.

## Main results

* `tateEvalPresheafHom_bivariate_continuous_canonical` — direct
  continuity of `example638Bivariate_evalHom` for the canonical
  bivariate Tate topology, no hypothesis-discharge required.
* `example638Bivariate_forwardHom_continuous_canonical` — quotient-lift
  consequence: the forward hom factored through
  `bivariateOverlapIdeal b` is continuous for the bivariate overlap
  quotient topology.

These eliminate the `hcont_forward_overlap` residual hypothesis
previously required in `LaneAReverseRoundTrip.lean`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Proposition 6.18,
  Example 6.39.
-/

namespace ValuationSpectrum

open Filter Topology UniformSpace TateAlgebra

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]

/-- **Bivariate canonical-topology continuity of `example638Bivariate_evalHom`
(Wedhorn Prop 6.18 bivariate analog).**

Under the natural strongly-noetherian Tate setup on `B`, the bivariate
evaluation hom `example638Bivariate_evalHom B P b : TateAlgebra₂ B →+*
presheafValue (overlapDatum B P b)` (sending `X ↦ canonicalMap b` and
`Y ↦ invS`) is continuous for the canonical bivariate Tate topology
`instTopologicalSpaceTateAlgebra₂` on `TateAlgebra₂ B`. -/
theorem tateEvalPresheafHom_bivariate_continuous_canonical
    (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [PlusSubring B] [IsHuberRing B] [HasLocLiftPowerBounded B]
    [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    @Continuous _ _ instTopologicalSpaceTateAlgebra₂
      (inferInstance : TopologicalSpace (presheafValue (overlapDatum B P b)))
      (example638Bivariate_evalHom B P b) := by
  set hb_canon := canonicalMap_b_isPowerBounded_in_overlap B P b
  set hb_invS := invS_isPowerBounded_in_overlap B P b
  set D := overlapDatum B P b
  set f_canon := D.canonicalMap b
  set f_invS := invS D
  letI τ : TopologicalSpace ↥(TateAlgebra₂ B) := instTopologicalSpaceTateAlgebra₂
  apply continuous_of_continuousAt_zero (example638Bivariate_evalHom B P b).toAddMonoidHom
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro V hV
  obtain ⟨W, hWV⟩ := NonarchimedeanRing.is_nonarchimedean V hV
  have hW_open : IsOpen (W : Set (presheafValue D)) := W.isOpen
  have hW_closed : IsClosed (W : Set (presheafValue D)) :=
    AddSubgroup.isClosed_of_isOpen W.toAddSubgroup hW_open
  have hW_nhds : (W : Set (presheafValue D)) ∈ @nhds (presheafValue D) _ 0 :=
    hW_open.mem_nhds W.toAddSubgroup.zero_mem
  have hbiv_bdd : TopologicalRing.IsBounded
      (Set.range (fun n : Fin 2 →₀ ℕ => f_canon ^ (n 0) * f_invS ^ (n 1))) :=
    (hb_canon.mul hb_invS).subset (by
      rintro _ ⟨n, rfl⟩
      exact Set.mul_mem_mul ⟨n 0, rfl⟩ ⟨n 1, rfl⟩)
  obtain ⟨U, hU, hUW⟩ := hbiv_bdd (W : Set (presheafValue D)) hW_nhds
  have hcmU : D.canonicalMap ⁻¹' U ∈ @nhds B _ 0 :=
    (canonicalMap_continuous D).continuousAt.preimage_mem_nhds (by rwa [map_zero])
  let P_B := (IsTateRing.principalPair B).toPairOfDefinition
  obtain ⟨N, -, hN⟩ := P_B.hasBasis_nhds_zero.mem_iff.mp hcmU
  have hbasis : ((@nhds _ τ (0 : ↥(TateAlgebra₂ B))).HasBasis
      (fun _ : ℕ => True) fun n =>
        (TateAlgebra.tateAlgNhd₂ P_B n : Set ↥(TateAlgebra₂ B))) :=
    TateAlgebra.tateAlgBasis'₂.hasBasis_nhds_zero
  apply hbasis.mem_iff.mpr
  refine ⟨N, trivial, fun h hh => ?_⟩
  refine hWV ?_
  have hterm_mem : ∀ n : Fin 2 →₀ ℕ,
      TateAlgebraWedhorn.evalTerm₂ D.canonicalMap f_canon f_invS h n ∈
        (W : Set (presheafValue D)) := by
    intro n
    change D.canonicalMap (MvPowerSeries.coeff n h.val) *
      (f_canon ^ (n 0) * f_invS ^ (n 1)) ∈ (W : Set (presheafValue D))
    rw [mul_comm]
    apply hUW
    refine ⟨f_canon ^ (n 0) * f_invS ^ (n 1), ⟨n, rfl⟩,
      D.canonicalMap (MvPowerSeries.coeff n h.val), ?_, rfl⟩
    apply hN
    obtain ⟨b', hbI, hbeq⟩ := TateAlgebra.tateAlgNhd₂_coeff_mem P_B N hh n
    rw [← hbeq]
    exact ⟨b', hbI, rfl⟩
  have hhs : HasSum (TateAlgebraWedhorn.evalTerm₂ D.canonicalMap f_canon f_invS h)
      (example638Bivariate_evalHom B P b h) :=
    (TateAlgebraWedhorn.evalTerm₂_summable D.canonicalMap
      (canonicalMap_continuous D) f_canon f_invS hb_canon hb_invS h).hasSum
  refine hW_closed.mem_of_tendsto hhs <| Filter.Eventually.of_forall fun s => ?_
  exact W.toAddSubgroup.sum_mem fun k _ => hterm_mem k

/-- **Bivariate canonical-topology continuity of `example638Bivariate_forwardHom`
(Wedhorn Prop 6.18 + Example 6.39 quotient-lift).**

The forward hom `example638Bivariate_forwardHom B P b`, factored through
`bivariateOverlapIdeal b`, is continuous for the bivariate overlap
quotient topology `quotientBivariateOverlapIdealTopology b`. -/
theorem example638Bivariate_forwardHom_continuous_canonical
    (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [PlusSubring B] [IsHuberRing B] [HasLocLiftPowerBounded B]
    [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    @Continuous _ _
      (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      (inferInstance : TopologicalSpace (presheafValue (overlapDatum B P b)))
      (example638Bivariate_forwardHom B P b) := by
  letI τ : TopologicalSpace ↥(TateAlgebra₂ B) := instTopologicalSpaceTateAlgebra₂
  letI τQ : TopologicalSpace (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology b
  haveI hTR : IsTopologicalRing ↥(TateAlgebra₂ B) := instIsTopologicalRingTateAlgebra₂
  have hmk_qm : Topology.IsQuotientMap
      (Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b) :
        ↥(TateAlgebra₂ B) → ↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    (@QuotientRing.isOpenQuotientMap_mk ↥(TateAlgebra₂ B) τ
      (inferInstanceAs (CommRing ↥(TateAlgebra₂ B)))
      (TateAlgebra.bivariateOverlapIdeal b) hTR).isQuotientMap
  refine hmk_qm.continuous_iff.mpr ?_
  exact tateEvalPresheafHom_bivariate_continuous_canonical B P b

end ValuationSpectrum

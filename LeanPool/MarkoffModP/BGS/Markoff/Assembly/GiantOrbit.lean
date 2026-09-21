/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Assembly.MiddleGameThenEndgame
import LeanPool.MarkoffModP.BGS.Markoff.Assembly.Asymptotics
import LeanPool.MarkoffModP.BGS.Markoff.Opening.EveryOrbitLarge
import LeanPool.MarkoffModP.BGS.Markoff.Endgame.WeilFromGeneralHasse
import LeanPool.MarkoffModP.BGS.Markoff.Endgame.Nonsplit.HasseFromGeneral
import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.CorvajaZannierFromGeneral
import LeanPool.MarkoffModP.BGS.Markoff.Cage.EstimateFromPlane

/-!
# Assembly of the giant orbit

This file connects the selected split cage component to the original punctured
Markoff action, bounds the complement by the already-counted small-order set,
and assembles Theorem 1 first from explicit specialized estimates and then from
the reusable general Hasse--Weil interface.  The interface is inhabited in
`BGS.HasseWeil.GeneralBivariateAffineHasseWeil`; the parameter-free endpoint is
exported by `BGS.Markoff.Assembly.Unconditional`.
-/

namespace BGS.Markoff

open Filter

noncomputable section

/-- Regard a normalized punctured point as a point of the normalized surface. -/
def normalizedSurfaceOfPunctured
    {R : Type*} [CommRing R] (x : ↥(normalizedPuncturedSurface R)) :
    NormalizedMarkoffSurface R :=
  ⟨x.1, x.2.1⟩

/-- Normalization identifies the punctured component relation with the transported
component relation on normalized surface points. -/
theorem samePuncturedComponent_iff_sameNormalizedComponent
    {R : Type*} [Field R] [Invertible (3 : R)]
    (x y : PuncturedMarkoffSurface R) :
    SamePuncturedComponent x y ↔
      SameNormalizedComponent
        (normalizedSurfaceOfPunctured (puncturedNormalizationEquiv R x))
        (normalizedSurfaceOfPunctured (puncturedNormalizationEquiv R y)) := by
  have hx : (normalizationSurfaceEquiv R).symm
      (normalizedSurfaceOfPunctured (puncturedNormalizationEquiv R x)) = x.1 := by
    apply Subtype.ext
    exact (normalizationEquiv R).symm_apply_apply x.1.1
  have hy : (normalizationSurfaceEquiv R).symm
      (normalizedSurfaceOfPunctured (puncturedNormalizationEquiv R y)) = y.1 := by
    apply Subtype.ext
    exact (normalizationEquiv R).symm_apply_apply y.1.1
  rw [SameNormalizedComponent, hx, hy]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    exact congrArg Subtype.val hg
  · rintro ⟨g, hg⟩
    refine ⟨g, Subtype.ext hg⟩

private theorem exists_fullOrderBaseUnit (p : ℕ) [Fact p.Prime] :
    ∃ u : (ZMod p)ˣ, orderOf u = Nat.card (ZMod p)ˣ := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  exact ⟨u, orderOf_eq_card_of_forall_mem_zpowers hu⟩

/-- For every sufficiently large prime, an explicit split conic point supplies a
punctured base point in the selected cage. -/
theorem exists_normalizedPunctured_splitCagePoint
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)] (hpSeven : 7 ≤ p) :
    ∃ x : ↥(normalizedPuncturedSurface (ZMod p)),
      IsInSplitCage p (normalizedSurfaceOfPunctured x) := by
  obtain ⟨u, huOrder⟩ := exists_fullOrderBaseUnit p
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  have huSq : (u : ZMod p) ^ 2 ≠ 1 := by
    intro huSq
    have huDvd : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one <| by
      apply Units.ext
      exact huSq
    have huLe : orderOf u ≤ 2 := Nat.le_of_dvd (by norm_num) huDvd
    rw [huOrder, hcard] at huLe
    omega
  let point : NormalizedPoint (ZMod p) := splitFiberPoint u 1
  have hpointFiber : point ∈ normalizedFiber1 (splitTorusTrace u) :=
    splitFiberPoint_mem u 1 huSq
  have hrotation : rotationOrder (splitTorusTrace u) = p - 1 := by
    rw [rotationOrder_splitTorusTrace u huSq, huOrder, hcard]
  have hpointNe : point ≠ normalizedOrigin := by
    intro hzero
    have htraceZero : splitTorusTrace u = 0 := by
      have hfirst := congrArg NormalizedPoint.u1 hzero
      change splitTorusTrace u = (0 : ZMod p) at hfirst
      exact hfirst
    have hzeroOrder := rotationOrder_zero_le_four p
    rw [← htraceZero, hrotation] at hzeroOrder
    omega
  let x : ↥(normalizedPuncturedSurface (ZMod p)) :=
    ⟨point, hpointFiber.1, by simpa using hpointNe⟩
  refine ⟨x, .first, ?_⟩
  exact hrotation

/-- A ceiling buffer over a smaller real power is eventually bounded by any
strictly larger real power. -/
theorem eventually_natCeil_rpow_add_one_le_rpow
    {δ η : ℝ} (hδ : 0 < δ) (hδη : δ < η) :
    ∀ᶠ p : ℕ in atTop,
      ((Nat.ceil ((p : ℝ) ^ δ) + 1 : ℕ) : ℝ) ≤ (p : ℝ) ^ η := by
  have htwoEventually :
      ∀ᶠ p : ℕ in atTop, (2 : ℝ) * (p : ℝ) ^ (0 : ℝ) < (p : ℝ) ^ δ :=
    eventually_const_mul_rpow_lt_rpow (C := (2 : ℝ)) (a := (0 : ℝ))
      (b := δ) hδ
  have hdoubleEventually :
      ∀ᶠ p : ℕ in atTop, (2 : ℝ) * (p : ℝ) ^ δ < (p : ℝ) ^ η :=
    eventually_const_mul_rpow_lt_rpow (C := (2 : ℝ)) (a := δ)
      (b := η) hδη
  filter_upwards [htwoEventually, hdoubleEventually] with p htwo hdouble
  have hpPowTwo : (2 : ℝ) < (p : ℝ) ^ δ := by
    simpa using htwo
  have hceil : ((Nat.ceil ((p : ℝ) ^ δ) + 1 : ℕ) : ℝ) <
      (p : ℝ) ^ δ + 2 := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    have hceilBase := Nat.ceil_lt_add_one
      (Real.rpow_nonneg (Nat.cast_nonneg p) δ)
    linarith
  have haddDouble : (p : ℝ) ^ δ + 2 < 2 * (p : ℝ) ^ δ := by
    calc
      (p : ℝ) ^ δ + 2 < (p : ℝ) ^ δ + (p : ℝ) ^ δ :=
        by simpa [add_comm] using add_lt_add_left hpPowTwo ((p : ℝ) ^ δ)
      _ = 2 * (p : ℝ) ^ δ := by ring
  exact le_of_lt (hceil.trans (haddDouble.trans hdouble))

/-- If every point above the middle-game cutoff reaches a connected split cage,
then every point outside the chosen cage component has small maximal order. -/
theorem maximalCoordinateRotationOrder_le_rpow_of_not_same_splitCageComponent
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)] {δ : ℝ}
    (c x : NormalizedMarkoffSurface (ZMod p))
    (hescape : ∀ z : NormalizedMarkoffSurface (ZMod p),
      (p : ℝ) ^ δ < maximalCoordinateRotationOrder z.1 →
        ∃ y : NormalizedMarkoffSurface (ZMod p),
          SameNormalizedComponent z y ∧ IsInSplitCage p y)
    (hconnected : ∀ y : NormalizedMarkoffSurface (ZMod p),
      IsInSplitCage p y → SameNormalizedComponent c y)
    (hnot : ¬ SameNormalizedComponent c x) :
    (maximalCoordinateRotationOrder x.1 : ℝ) ≤ (p : ℝ) ^ δ := by
  by_contra hlarge
  obtain ⟨y, hxy, hyCage⟩ := hescape x (lt_of_not_ge hlarge)
  exact hnot (sameNormalizedComponent_trans (hconnected y hyCage)
    (sameNormalizedComponent_symm hxy))

private theorem three_ne_zero_zmod_of_prime_ne_three
    (p : ℕ) [Fact p.Prime] (hpThree : p ≠ 3) : (3 : ZMod p) ≠ 0 := by
  intro hzero
  have hpDvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hzero
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hpDvd with hpOne | hpEq
  · exact (Fact.out : p.Prime).ne_one hpOne
  · exact hpThree hpEq

/-- Intermediate assembly relative to a neutral weighted-trace
torsion-intersection bound and three specialized point-count estimates.

The public endpoint supplies the weighted-trace bound from the completed
Corvaja--Zannier theorem and derives the three point-count specializations from
the general affine Hasse--Weil theorem. -/
theorem eventually_hasGiantOrbit_of_specializedEstimates
    (hBound : ∀ (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)],
      WeightedTraceTorsionIntersectionBound p (quadraticFiniteField p))
    (splitCoefficient : ℕ)
    (hSplitWeil : WeightedSplitTraceWeilBoundAssumption splitCoefficient)
    (nonsplitCoefficient : ℕ)
    (hNonsplitWeil : SeededNonsplitTraceWeilBoundAssumption nonsplitCoefficient)
    (cageCoefficient : ℕ) (hCageEstimate : CageWitnessPointEstimate cageCoefficient) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ p0 : ℕ, ∀ (p : ℕ) (hpPrime : p.Prime), p0 ≤ p →
        HasGiantOrbitAt p hpPrime epsilon := by
  intro epsilon hEpsilon
  let δ : ℝ := min (epsilon / 10) (1 / 4)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (div_pos hEpsilon (by norm_num)) (by norm_num)
  have hδQuarter : δ ≤ (1 : ℝ) / 4 := min_le_right _ _
  have hδEpsilon : δ < epsilon / 5 := by
    have hδTen : δ ≤ epsilon / 10 := min_le_left _ _
    linarith
  obtain ⟨middleThreshold, hmiddle⟩ :=
    exists_threshold_middleGame_to_splitCage hBound splitCoefficient hSplitWeil
      nonsplitCoefficient hNonsplitWeil hδ hδQuarter
  obtain ⟨cageThreshold, hcage⟩ :=
    exists_threshold_splitCage_connected cageCoefficient hCageEstimate
  obtain ⟨boundThreshold, hboundThreshold⟩ :=
    eventually_atTop.mp
      (eventually_natCeil_rpow_add_one_le_rpow hδ hδEpsilon)
  obtain ⟨countThreshold, hcountThreshold⟩ :=
    eventually_atTop.mp (eventually_smallOrderPointBound_le_rpow hEpsilon)
  refine ⟨max (max (max middleThreshold cageThreshold) boundThreshold)
    (max countThreshold 7), ?_⟩
  intro p hpPrime hp
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hpMiddle : middleThreshold ≤ p := by omega
  have hpCage : cageThreshold ≤ p := by omega
  have hpBound : boundThreshold ≤ p := by omega
  have hpCount : countThreshold ≤ p := by omega
  have hpSeven : 7 ≤ p := by omega
  have hpTwo : p ≠ 2 := by omega
  have hpThree : p ≠ 3 := by omega
  letI : Invertible (3 : ZMod p) :=
    invertibleOfNonzero (three_ne_zero_zmod_of_prime_ne_three p hpThree)
  letI : Fintype (quadraticFiniteField p) := Fintype.ofFinite _
  obtain ⟨cNormalized, hcNormalizedCage⟩ :=
    exists_normalizedPunctured_splitCagePoint p hpSeven
  let c : PuncturedMarkoffSurface (ZMod p) :=
    (puncturedNormalizationEquiv (ZMod p)).symm cNormalized
  let bound : ℕ := Nat.ceil ((p : ℝ) ^ δ) + 1
  let bad := puncturedMarkoffPointsWithSmallFirstTwoRotationOrders p bound
  apply hasGiantOrbitAt_of_complement_subset_finset p hpPrime epsilon c bad
  · intro x hxOutside
    have hxNotComponent : ¬ SamePuncturedComponent c x := hxOutside.2
    let xNormalized := puncturedNormalizationEquiv (ZMod p) x
    let xSurface := normalizedSurfaceOfPunctured xNormalized
    have hxNotNormalized : ¬ SameNormalizedComponent
        (normalizedSurfaceOfPunctured cNormalized) xSurface := by
      intro hcx
      apply hxNotComponent
      apply (samePuncturedComponent_iff_sameNormalizedComponent c x).2
      simpa [c, xSurface, xNormalized] using hcx
    have hxMaxSmall : (maximalCoordinateRotationOrder xSurface.1 : ℝ) ≤
        (p : ℝ) ^ δ :=
      maximalCoordinateRotationOrder_le_rpow_of_not_same_splitCageComponent
        p (normalizedSurfaceOfPunctured cNormalized) xSurface
        (hmiddle p hpMiddle hpThree)
        (fun y hy => hcage p hpCage hpThree _ y hcNormalizedCage hy)
        hxNotNormalized
    have hfirstReal : (rotationOrder xSurface.1.u1 : ℝ) ≤ (p : ℝ) ^ δ := by
      have hfirstMax : (rotationOrder xSurface.1.u1 : ℝ) ≤
          maximalCoordinateRotationOrder xSurface.1 := by
        exact_mod_cast rotationOrder_first_le_maximalCoordinateRotationOrder xSurface.1
      exact hfirstMax.trans hxMaxSmall
    have hsecondReal : (rotationOrder xSurface.1.u2 : ℝ) ≤ (p : ℝ) ^ δ := by
      have hsecondMax : (rotationOrder xSurface.1.u2 : ℝ) ≤
          maximalCoordinateRotationOrder xSurface.1 := by
        exact_mod_cast rotationOrder_second_le_maximalCoordinateRotationOrder xSurface.1
      exact hsecondMax.trans hxMaxSmall
    have hfirstCeil : rotationOrder xSurface.1.u1 ≤ Nat.ceil ((p : ℝ) ^ δ) := by
      exact_mod_cast hfirstReal.trans (Nat.le_ceil ((p : ℝ) ^ δ))
    have hsecondCeil : rotationOrder xSurface.1.u2 ≤ Nat.ceil ((p : ℝ) ^ δ) := by
      exact_mod_cast hsecondReal.trans (Nat.le_ceil ((p : ℝ) ^ δ))
    have hfirstCeil' : rotationOrder (toNormalized x.1.1).u1 ≤
        Nat.ceil ((p : ℝ) ^ δ) := by
      simpa only [xSurface, xNormalized, normalizedSurfaceOfPunctured,
        puncturedNormalizationEquiv_coe] using hfirstCeil
    have hsecondCeil' : rotationOrder (toNormalized x.1.1).u2 ≤
        Nat.ceil ((p : ℝ) ^ δ) := by
      simpa only [xSurface, xNormalized, normalizedSurfaceOfPunctured,
        puncturedNormalizationEquiv_coe] using hsecondCeil
    change x ∈ puncturedMarkoffPointsWithSmallFirstTwoRotationOrders p bound
    rw [puncturedMarkoffPointsWithSmallFirstTwoRotationOrders,
      mem_originalPuncturedFinsetOfNormalized_iff,
      mem_normalizedPuncturedMarkoffPointsWithSmallFirstTwoRotationOrders_iff]
    exact ⟨by simpa [bound] using hfirstCeil',
      by simpa [bound] using hsecondCeil'⟩
  · have hbound : (bound : ℝ) ≤ (p : ℝ) ^ (epsilon / 5) := by
      exact hboundThreshold p hpBound
    calc
      (bad.card : ℝ) ≤ (2 * (2 + 2 * bound ^ 2) ^ 2 : ℕ) := by
        exact_mod_cast
          puncturedMarkoffPointsWithSmallFirstTwoRotationOrders_card_le hpTwo bound
      _ ≤ (p : ℝ) ^ epsilon := hcountThreshold p hpCount bound hbound

/-- Modular bound-injection form of Theorem 1.

It exposes the neutral weighted-trace torsion-intersection contract together
with the split, nonsplit, and cage point-count specializations. The public
endpoint below supplies these inputs from the completed Corvaja--Zannier
theorem and the remaining general affine Hasse--Weil input. -/
theorem theoremOneStatement_of_specializedEstimates
    (hBound : ∀ (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)],
      WeightedTraceTorsionIntersectionBound p (quadraticFiniteField p))
    (splitCoefficient : ℕ)
    (hSplitWeil : WeightedSplitTraceWeilBoundAssumption splitCoefficient)
    (nonsplitCoefficient : ℕ)
    (hNonsplitWeil : SeededNonsplitTraceWeilBoundAssumption nonsplitCoefficient)
    (cageCoefficient : ℕ) (hCageEstimate : CageWitnessPointEstimate cageCoefficient) :
    TheoremOneStatement := by
  apply theoremOneStatement_of_eventually_hasGiantOrbit
  exact eventually_hasGiantOrbit_of_specializedEstimates hBound splitCoefficient hSplitWeil
    nonsplitCoefficient hNonsplitWeil cageCoefficient hCageEstimate

/-- The near-final Theorem 1 assembly with Corvaja--Zannier discharged by the
in-repository theorem.  This intermediate adapter keeps the general affine
Hasse--Weil input explicit, together with its descended nonsplit adapter. -/
theorem theoremOneStatement_of_generalHasseWeil_and_nonsplitHasseAdapter
    (hHasse : BGS.External.GeneralBivariateAffineHasseWeilTheorem)
    (nonsplitCoefficient : ℕ)
    (hNonsplitWeil : SeededNonsplitTraceWeilBoundAssumption nonsplitCoefficient) :
    TheoremOneStatement := by
  classical
  obtain ⟨splitCoefficient, hSplitWeil⟩ :=
    exists_weightedSplitTraceWeilBoundAssumption_of_generalHasseWeil hHasse
  obtain ⟨cageCoefficient, _hcagePositive, hCageEstimate⟩ :=
    exists_cageWitnessPointEstimate_of_generalHasseWeil hHasse
  apply theoremOneStatement_of_specializedEstimates
    (fun p _ _ =>
      corvajaZannierWeightedTraceBound p (quadraticFiniteField p))
    splitCoefficient hSplitWeil nonsplitCoefficient hNonsplitWeil
    cageCoefficient hCageEstimate

/-- **BGS Theorem 1 with Corvaja--Zannier fully discharged.**

The in-repository Corvaja--Zannier theorem supplies the middle-game estimate.
This theorem is the general-interface assembly step; the parameter-free public
endpoint is `BGS.Markoff.theoremOneStatement`. -/
theorem theoremOneStatement_of_generalHasseWeil
    (hHasse : BGS.External.GeneralBivariateAffineHasseWeilTheorem) :
    TheoremOneStatement := by
  obtain ⟨nonsplitCoefficient, hNonsplitWeil⟩ :=
    exists_seededNonsplitTraceWeilBoundAssumption_of_generalHasseWeil hHasse
  exact theoremOneStatement_of_generalHasseWeil_and_nonsplitHasseAdapter
    hHasse nonsplitCoefficient hNonsplitWeil

end

end BGS.Markoff

/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Endgame.Parabolic
import LeanPool.MarkoffModP.BGS.Markoff.Opening.FiniteOrbit

/-!
# Large order in any coordinate reaches a maximal rotation

This packages the first-coordinate endgame with the normalized coordinate permutations and the
Markoff-component relation.
-/

namespace BGS.Markoff

noncomputable section

private theorem three_ne_zero_zmod_of_prime_ne_three
    (p : ℕ) [Fact p.Prime] (hpThree : p ≠ 3) : (3 : ZMod p) ≠ 0 := by
  intro hzero
  have hpDvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hzero
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hpDvd with hpOne | hpEq
  · exact (Fact.out : p.Prime).ne_one hpOne
  · exact hpThree hpEq

/-- A large first-coordinate rotation reaches a same-component point with maximal second
rotation. -/
theorem exists_threshold_sameComponent_maximalRotation_of_large_firstCoordinate
    (splitCoefficient : ℕ)
    (hSplitWeil : WeightedSplitTraceWeilBoundAssumption splitCoefficient)
    (nonsplitCoefficient : ℕ)
    (hNonsplitWeil : SeededNonsplitTraceWeilBoundAssumption nonsplitCoefficient)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] → ∀ hpThree : p ≠ 3,
      letI : Invertible (3 : ZMod p) :=
        invertibleOfNonzero (three_ne_zero_zmod_of_prime_ne_three p hpThree)
      ∀ x : NormalizedMarkoffSurface (ZMod p),
        (p : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤ rotationOrder x.1.u1 →
        ∃ y : NormalizedMarkoffSurface (ZMod p),
          SameNormalizedComponent x y ∧ rotationOrder y.1.u2 = p - 1 := by
  obtain ⟨threshold, hthreshold⟩ :=
    exists_threshold_point_with_maximal_secondRotation
      splitCoefficient hSplitWeil nonsplitCoefficient hNonsplitWeil hδ
  refine ⟨max threshold 5, ?_⟩
  intro p hp _ hpThree
  letI : Invertible (3 : ZMod p) :=
    invertibleOfNonzero (three_ne_zero_zmod_of_prime_ne_three p hpThree)
  intro x hlarge
  have hpThreshold : threshold ≤ p := (le_max_left threshold 5).trans hp
  let xf : ↥(normalizedFiber1 x.1.u1) := ⟨x.1, x.property, rfl⟩
  obtain ⟨n, hrotation⟩ := hthreshold p hpThreshold x.1.u1 xf hlarge
  let y := (normalizedRotate1Surface^[n]) x
  refine ⟨y, sameNormalizedComponent_iterate_normalizedRotate1Surface x n, ?_⟩
  rw [show y.1 = (normalizedRotate1^[n]) x.1 by
    exact coe_iterate_normalizedRotate1Surface x n]
  exact hrotation

/-- Published Proposition 10: if any coordinate rotation is large, the point is connected to
a point with a maximal split rotation. -/
theorem exists_threshold_sameComponent_maximalRotation_of_some_largeCoordinate
    (splitCoefficient : ℕ)
    (hSplitWeil : WeightedSplitTraceWeilBoundAssumption splitCoefficient)
    (nonsplitCoefficient : ℕ)
    (hNonsplitWeil : SeededNonsplitTraceWeilBoundAssumption nonsplitCoefficient)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] → ∀ hpThree : p ≠ 3,
      letI : Invertible (3 : ZMod p) :=
        invertibleOfNonzero (three_ne_zero_zmod_of_prime_ne_three p hpThree)
      ∀ x : NormalizedMarkoffSurface (ZMod p),
        ((p : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤ rotationOrder x.1.u1 ∨
          (p : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤ rotationOrder x.1.u2 ∨
          (p : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤ rotationOrder x.1.u3) →
        ∃ y : NormalizedMarkoffSurface (ZMod p),
          SameNormalizedComponent x y ∧ rotationOrder y.1.u2 = p - 1 := by
  obtain ⟨threshold, hfirst⟩ :=
    exists_threshold_sameComponent_maximalRotation_of_large_firstCoordinate
      splitCoefficient hSplitWeil nonsplitCoefficient hNonsplitWeil hδ
  refine ⟨threshold, ?_⟩
  intro p hp _ hpThree
  letI : Invertible (3 : ZMod p) :=
    invertibleOfNonzero (three_ne_zero_zmod_of_prime_ne_three p hpThree)
  intro x hlarge
  rcases hlarge with hfirstLarge | hsecondLarge | hthirdLarge
  · exact hfirst p hp hpThree x hfirstLarge
  · let x' := normalizedSwap12Surface x
    have hx' : SameNormalizedComponent x x' := sameNormalizedComponent_swap12Surface x
    have hlarge' :
        (p : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤ rotationOrder x'.1.u1 := by
      simpa [x', normalizedSwap12, coe_normalizedSwap12Surface] using hsecondLarge
    obtain ⟨y, hy, hyOrder⟩ := hfirst p hp hpThree x' hlarge'
    exact ⟨y, sameNormalizedComponent_trans hx' hy, hyOrder⟩
  · let x' := normalizedSwap12Surface (normalizedSwap23Surface x)
    have hx23 : SameNormalizedComponent x (normalizedSwap23Surface x) :=
      sameNormalizedComponent_swap23Surface x
    have hx12 : SameNormalizedComponent (normalizedSwap23Surface x) x' :=
      sameNormalizedComponent_swap12Surface (normalizedSwap23Surface x)
    have hlarge' :
        (p : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤ rotationOrder x'.1.u1 := by
      simpa [x', normalizedSwap12, normalizedSwap23, coe_normalizedSwap12Surface,
        coe_normalizedSwap23Surface] using hthirdLarge
    obtain ⟨y, hy, hyOrder⟩ := hfirst p hp hpThree x' hlarge'
    exact ⟨y, sameNormalizedComponent_trans
      (sameNormalizedComponent_trans hx23 hx12) hy, hyOrder⟩

end

end BGS.Markoff

/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.CoarseSupportTail

/-!
# Endgame and cage wrappers at the unified coarse support cutoff

The geometric endgame is unchanged.  This module feeds it the simultaneous
tenth-moment estimates proved in `CoarseSupportTail`, so every non-cubic
support condition follows from the single hypothesis `2^756 < p`.
-/

@[expose] public section

namespace BGS.Markoff

noncomputable section

/-- Above the unified support cutoff, a large first-coordinate rotation
reaches a maximal split rotation. -/
theorem exists_coarse_sameComponent_maximalRotation_of_large_firstCoordinate
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hp : 2 ^ 756 < p)
    (x : NormalizedMarkoffSurface (ZMod p))
    (hlarge : (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u1) :
    ∃ y : NormalizedMarkoffSurface (ZMod p),
      SameNormalizedComponent x y ∧ rotationOrder y.1.u2 = p - 1 := by
  let xf : ↑(normalizedFiber1 x.1.u1) := ⟨x.1, x.property, rfl⟩
  obtain ⟨n, hrotation⟩ :=
    exists_iterate_point_with_maximal_secondRotation_of_explicitInequalities
      p ((by norm_num : 5 ≤ 7).trans (seven_le_of_twoPow756_lt hp))
      x.1.u1 xf
      (fun orbitExponent orbitOrder hmul horder ↦
        coarse_endgamePrimitiveTrace_explicitInequality_of_card_sub_one
          hp hmul horder (by norm_num))
      (fun orbitExponent orbitOrder hmul horder ↦
        coarse_endgamePrimitiveTrace_explicitInequality_of_card_add_one
          hp hmul horder (by norm_num))
      (coarse_four_lt_rpow_five_div_six hp) hlarge
  let y := (normalizedRotate1Surface^[n]) x
  refine ⟨y, sameNormalizedComponent_iterate_normalizedRotate1Surface x n, ?_⟩
  rw [show y.1 = (normalizedRotate1^[n]) x.1 by
    exact coe_iterate_normalizedRotate1Surface x n]
  exact hrotation

/-- First-coordinate form of the coarse large-order-to-cage endgame. -/
theorem exists_coarse_sameComponent_splitCage_of_large_firstCoordinate
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hp : 2 ^ 756 < p)
    (x : NormalizedMarkoffSurface (ZMod p))
    (hlarge : (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u1) :
    ∃ y : NormalizedMarkoffSurface (ZMod p),
      SameNormalizedComponent x y ∧ IsInSplitCage p y := by
  obtain ⟨y, hxy, hyOrder⟩ :=
    exists_coarse_sameComponent_maximalRotation_of_large_firstCoordinate
      hp x hlarge
  exact ⟨y, hxy, .second, hyOrder⟩

/-- If one coordinate rotation is large, the point reaches the split cage. -/
theorem exists_coarse_sameComponent_splitCage_of_some_largeCoordinate
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hp : 2 ^ 756 < p)
    (x : NormalizedMarkoffSurface (ZMod p))
    (hlarge :
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u1 ∨
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u2 ∨
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u3) :
    ∃ y : NormalizedMarkoffSurface (ZMod p),
      SameNormalizedComponent x y ∧ IsInSplitCage p y := by
  rcases hlarge with hfirst | hsecond | hthird
  · exact
      exists_coarse_sameComponent_splitCage_of_large_firstCoordinate
        hp x hfirst
  · let x' := normalizedSwap12Surface x
    have hx' : SameNormalizedComponent x x' :=
      sameNormalizedComponent_swap12Surface x
    have hlarge' :
        (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x'.1.u1 := by
      simpa [x', normalizedSwap12, coe_normalizedSwap12Surface] using hsecond
    obtain ⟨y, hy, hyOrder⟩ :=
      exists_coarse_sameComponent_maximalRotation_of_large_firstCoordinate
        hp x' hlarge'
    exact ⟨y, sameNormalizedComponent_trans hx' hy, .second, hyOrder⟩
  · let x' := normalizedSwap12Surface (normalizedSwap23Surface x)
    have hx23 : SameNormalizedComponent x (normalizedSwap23Surface x) :=
      sameNormalizedComponent_swap23Surface x
    have hx12 : SameNormalizedComponent (normalizedSwap23Surface x) x' :=
      sameNormalizedComponent_swap12Surface (normalizedSwap23Surface x)
    have hlarge' :
        (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x'.1.u1 := by
      simpa [x', normalizedSwap12, normalizedSwap23,
        coe_normalizedSwap12Surface, coe_normalizedSwap23Surface] using hthird
    obtain ⟨y, hy, hyOrder⟩ :=
      exists_coarse_sameComponent_maximalRotation_of_large_firstCoordinate
        hp x' hlarge'
    exact ⟨y, sameNormalizedComponent_trans
      (sameNormalizedComponent_trans hx23 hx12) hy, .second, hyOrder⟩

/-- The selected split cage is connected above the unified support cutoff. -/
theorem coarse_splitCage_connected
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hp : 2 ^ 756 < p)
    (x y : NormalizedMarkoffSurface (ZMod p))
    (hx : IsInSplitCage p x) (hy : IsInSplitCage p y) :
    SameNormalizedComponent x y := by
  exact splitCage_connected_of_explicitInequality p
    (seven_le_of_twoPow756_lt hp)
    (coarse_cageWitness_explicitInequality hp (by norm_num))
    x y hx hy

/-- A large-order point lies in the component of any chosen cage base point. -/
theorem coarse_sameNormalizedComponent_of_largeOrder_to_splitCage
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hp : 2 ^ 756 < p)
    (base x : NormalizedMarkoffSurface (ZMod p))
    (hbase : IsInSplitCage p base)
    (hlarge :
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u1 ∨
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u2 ∨
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u3) :
    SameNormalizedComponent base x := by
  obtain ⟨y, hxy, hy⟩ :=
    exists_coarse_sameComponent_splitCage_of_some_largeCoordinate
      hp x hlarge
  exact sameNormalizedComponent_trans
    (coarse_splitCage_connected hp base y hbase hy)
    (sameNormalizedComponent_symm hxy)

end

end BGS.Markoff

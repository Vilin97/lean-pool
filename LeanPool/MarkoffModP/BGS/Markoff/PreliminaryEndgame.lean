/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.ExplicitEndgame
import LeanPool.MarkoffModP.BGS.Markoff.PreliminaryNumerics

/-!
# Endgame wrappers for the elementary preliminary route

The geometry and incidence estimates are the already proved explicit endgame
and cage theorems.  This file supplies them with the smaller preliminary-route
numerical certificates.
-/

namespace BGS.Markoff

noncomputable section

private theorem preliminaryCutoff_seven_le
    {p : ℕ} [Fact p.Prime]
    (hp : preliminaryStrongApproximationCutoff ≤ p) : 7 ≤ p := by
  have hpOne : (1 : ℝ) ≤ p := by
    exact_mod_cast (preliminaryCutoff_gt_one.trans_le hp).le
  have hrootLe : (p : ℝ) ^ (1 / 8 : ℝ) ≤ p := by
    simpa using
      Real.rpow_le_self_of_one_le hpOne (by norm_num : (1 / 8 : ℝ) ≤ 1)
  have hfiveRoot : (5 : ℝ) < (p : ℝ) ^ (1 / 8 : ℝ) :=
    preliminary_small_fixed_lt_rpow_one_div_eight hp (by norm_num)
  have hfive : 5 < p := by
    exact_mod_cast hfiveRoot.trans_le hrootLe
  have hpSix : p ≠ 6 := by
    intro hpEq
    subst p
    have hprime : Nat.Prime 6 := Fact.out
    norm_num at hprime
  omega

/-- At the elementary preliminary cutoff, a large first-coordinate rotation
reaches a maximal split rotation. -/
theorem exists_preliminary_sameComponent_maximalRotation_of_large_firstCoordinate
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hp : preliminaryStrongApproximationCutoff ≤ p)
    (x : NormalizedMarkoffSurface (ZMod p))
    (hlarge : (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u1) :
    ∃ y : NormalizedMarkoffSurface (ZMod p),
      SameNormalizedComponent x y ∧ rotationOrder y.1.u2 = p - 1 := by
  let xf : ↑(normalizedFiber1 x.1.u1) := ⟨x.1, x.property, rfl⟩
  obtain ⟨n, hrotation⟩ :=
    exists_iterate_point_with_maximal_secondRotation_of_explicitInequalities
      p ((by norm_num : 5 ≤ 7).trans (preliminaryCutoff_seven_le hp))
      x.1.u1 xf
      (fun orbitExponent orbitOrder hmul horder ↦
        preliminary_endgamePrimitiveTrace_explicitInequality_of_card_sub_one
          hp hmul horder (by norm_num))
      (fun orbitExponent orbitOrder hmul horder ↦
        preliminary_endgamePrimitiveTrace_explicitInequality_of_card_add_one
          hp hmul horder (by norm_num))
      (preliminary_four_lt_rpow_five_div_six hp) hlarge
  let y := (normalizedRotate1Surface^[n]) x
  refine ⟨y, sameNormalizedComponent_iterate_normalizedRotate1Surface x n, ?_⟩
  rw [show y.1 = (normalizedRotate1^[n]) x.1 by
    exact coe_iterate_normalizedRotate1Surface x n]
  exact hrotation

/-- First-coordinate form of the preliminary large-order-to-cage endgame. -/
theorem exists_preliminary_sameComponent_splitCage_of_large_firstCoordinate
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hp : preliminaryStrongApproximationCutoff ≤ p)
    (x : NormalizedMarkoffSurface (ZMod p))
    (hlarge : (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u1) :
    ∃ y : NormalizedMarkoffSurface (ZMod p),
      SameNormalizedComponent x y ∧ IsInSplitCage p y := by
  obtain ⟨y, hxy, hyOrder⟩ :=
    exists_preliminary_sameComponent_maximalRotation_of_large_firstCoordinate
      hp x hlarge
  exact ⟨y, hxy, .second, hyOrder⟩

/-- If one coordinate rotation is large, the point reaches the split cage. -/
theorem exists_preliminary_sameComponent_splitCage_of_some_largeCoordinate
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hp : preliminaryStrongApproximationCutoff ≤ p)
    (x : NormalizedMarkoffSurface (ZMod p))
    (hlarge :
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u1 ∨
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u2 ∨
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u3) :
    ∃ y : NormalizedMarkoffSurface (ZMod p),
      SameNormalizedComponent x y ∧ IsInSplitCage p y := by
  rcases hlarge with hfirst | hsecond | hthird
  · exact
      exists_preliminary_sameComponent_splitCage_of_large_firstCoordinate
        hp x hfirst
  · let x' := normalizedSwap12Surface x
    have hx' : SameNormalizedComponent x x' :=
      sameNormalizedComponent_swap12Surface x
    have hlarge' :
        (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x'.1.u1 := by
      simpa [x', normalizedSwap12, coe_normalizedSwap12Surface] using hsecond
    obtain ⟨y, hy, hyOrder⟩ :=
      exists_preliminary_sameComponent_maximalRotation_of_large_firstCoordinate
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
      exists_preliminary_sameComponent_maximalRotation_of_large_firstCoordinate
        hp x' hlarge'
    exact ⟨y, sameNormalizedComponent_trans
      (sameNormalizedComponent_trans hx23 hx12) hy, .second, hyOrder⟩

/-- The selected split cage is connected at the preliminary cutoff. -/
theorem preliminary_splitCage_connected
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hp : preliminaryStrongApproximationCutoff ≤ p)
    (x y : NormalizedMarkoffSurface (ZMod p))
    (hx : IsInSplitCage p x) (hy : IsInSplitCage p y) :
    SameNormalizedComponent x y := by
  exact splitCage_connected_of_explicitInequality p
    (preliminaryCutoff_seven_le hp)
    (preliminary_cageWitness_explicitInequality hp (by norm_num))
    x y hx hy

/-- A large-order point lies in the component of any chosen cage base point. -/
theorem preliminary_sameNormalizedComponent_of_largeOrder_to_splitCage
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hp : preliminaryStrongApproximationCutoff ≤ p)
    (base x : NormalizedMarkoffSurface (ZMod p))
    (hbase : IsInSplitCage p base)
    (hlarge :
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u1 ∨
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u2 ∨
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u3) :
    SameNormalizedComponent base x := by
  obtain ⟨y, hxy, hy⟩ :=
    exists_preliminary_sameComponent_splitCage_of_some_largeCoordinate
      hp x hlarge
  exact sameNormalizedComponent_trans
    (preliminary_splitCage_connected hp base y hbase hy)
    (sameNormalizedComponent_symm hxy)

end

end BGS.Markoff

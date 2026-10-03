/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.ExplicitEstimates
public import LeanPool.MarkoffModP.BGS.Markoff.ExplicitNumericCertificates
public import LeanPool.MarkoffModP.BGS.Markoff.Endgame.PrimitiveOrbitWiring
public import LeanPool.MarkoffModP.BGS.Markoff.Cage.Connectivity

/-!
# Explicit endgame and cage connectivity

This file separates the finite-prime endgame wiring from its closed numerical
certificates.  The structural lemmas below consume the exact primitive-trace
inequalities at a fixed prime; the final wrappers discharge those inequalities
from `explicitStrongApproximationCutoff`.
-/

@[expose] public section

namespace BGS.Markoff

noncomputable section

/-- The fixed-prime semisimple endgame.  Its only numerical inputs are the
two displayed primitive-trace inequalities, with the fixed coefficients `33`
and `34` already obtained from the coefficient-`8` affine Hasse--Weil bound. -/
theorem exists_iterate_nonparabolicPoint_with_maximal_secondRotation_of_explicitInequalities
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (x : ↑(normalizedFiber1 t))
    (hSplitExplicit : ∀ orbitExponent orbitOrder : ℕ,
      orbitExponent * orbitOrder = p - 1 →
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ orbitOrder →
      (orbitExponent : ℝ) * (((p - 1).divisors.card : ℕ) : ℝ) ^ 2 *
        ((33 : ℝ) * Real.sqrt (p : ℝ)) < p)
    (hNonsplitExplicit : ∀ orbitExponent orbitOrder : ℕ,
      orbitExponent * orbitOrder = p + 1 →
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ orbitOrder →
      (orbitExponent : ℝ) * (((p - 1).divisors.card : ℕ) : ℝ) ^ 2 *
        ((34 : ℝ) * Real.sqrt (p : ℝ)) < p)
    (hlarge : (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder t) :
    ∃ n : ℕ,
      rotationOrder
          (((normalizedRotate1^[n])
            (x : NormalizedPoint (ZMod p))).u2) = p - 1 := by
  have hpTwo : p ≠ 2 := by omega
  rcases exists_split_or_nonsplitFiberParameter p hpTwo t ht ht0 x with
      ⟨w, htrace, hw, s, hx⟩ | ⟨w, htrace, hw, s, hx⟩
  · have horder : rotationOrder t = orderOf w := by
      rw [← htrace, rotationOrder_splitTorusTrace w hw]
    have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
      rw [Nat.card_units, Nat.card_zmod]
    have hmul := Nat.div_mul_cancel (orderOf_dvd_natCard w)
    rw [hcard] at hmul
    have hexplicit := hSplitExplicit
      ((p - 1) / orderOf w) (orderOf w) hmul (by simpa [horder] using hlarge)
    obtain ⟨n, u, hcoordinate, huOrder⟩ :=
      exists_iterate_splitFiberPoint_with_primitive_secondTrace
        p 33 weightedSplitTraceWeilBoundAssumption_thirtyThree hpTwo w s hw
        (by simpa [htrace] using ht0)
        (complementaryExponent_pos w)
        (splitComplementaryExponent_cast_ne_zero p w)
        (complementaryExponent_dvd_natCard w) (by
          rw [hcard]
          exact hexplicit)
    have huSq : (u : ZMod p) ^ 2 ≠ 1 := by
      intro huPower
      have huDvd : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one <| by
        apply Units.ext
        exact huPower
      have huLe : orderOf u ≤ 2 := Nat.le_of_dvd (by norm_num) huDvd
      rw [huOrder, hcard] at huLe
      omega
    refine ⟨n, ?_⟩
    rw [← hx, hcoordinate, rotationOrder_splitTorusTrace u huSq, huOrder, hcard]
  · have horder : rotationOrder t = orderOf w := by
      rw [← htrace, rotationOrder_quadraticNormOneTrace p w hw]
    have hmul := Nat.div_mul_cancel (orderOf_dvd_natCard w)
    rw [quadraticNormOneTorus_natCard] at hmul
    have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
      rw [Nat.card_units, Nat.card_zmod]
    have hexplicit := hNonsplitExplicit
      ((p + 1) / orderOf w) (orderOf w) hmul (by simpa [horder] using hlarge)
    obtain ⟨n, u, hcoordinate, huOrder⟩ :=
      exists_iterate_quadraticNormFiberPoint_with_primitive_secondTrace
        p 34 seededNonsplitTraceWeilBoundAssumption_thirtyFour hpTwo
        t ht ht0 w htrace s
        (complementaryExponent_pos w)
        (nonsplitComplementaryExponent_cast_ne_zero p w)
        (complementaryExponent_dvd_natCard w) (by
          rw [quadraticNormOneTorus_natCard, hcard]
          exact hexplicit)
    have huSq : (u : ZMod p) ^ 2 ≠ 1 := by
      intro huPower
      have huDvd : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one <| by
        apply Units.ext
        exact huPower
      have huLe : orderOf u ≤ 2 := Nat.le_of_dvd (by norm_num) huDvd
      rw [huOrder, hcard] at huLe
      omega
    refine ⟨n, ?_⟩
    rw [← hx, hcoordinate, rotationOrder_splitTorusTrace u huSq, huOrder, hcard]

/-- Fixed-prime first-coordinate endgame, including the parabolic branch and
the trace-zero exclusion. -/
theorem exists_iterate_point_with_maximal_secondRotation_of_explicitInequalities
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (t : ZMod p) (x : ↑(normalizedFiber1 t))
    (hSplitExplicit : ∀ orbitExponent orbitOrder : ℕ,
      orbitExponent * orbitOrder = p - 1 →
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ orbitOrder →
      (orbitExponent : ℝ) * (((p - 1).divisors.card : ℕ) : ℝ) ^ 2 *
        ((33 : ℝ) * Real.sqrt (p : ℝ)) < p)
    (hNonsplitExplicit : ∀ orbitExponent orbitOrder : ℕ,
      orbitExponent * orbitOrder = p + 1 →
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ orbitOrder →
      (orbitExponent : ℝ) * (((p - 1).divisors.card : ℕ) : ℝ) ^ 2 *
        ((34 : ℝ) * Real.sqrt (p : ℝ)) < p)
    (hzero : 4 < (p : ℝ) ^ (5 / 6 : ℝ))
    (hlarge : (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder t) :
    ∃ n : ℕ,
      rotationOrder
          (((normalizedRotate1^[n])
            (x : NormalizedPoint (ZMod p))).u2) = p - 1 := by
  by_cases htParabolic : t ^ 2 = 4
  · exact exists_iterate_parabolicPoint_with_maximal_secondRotation
      p hpFive t htParabolic x
  · have ht0 : t ≠ 0 := by
      intro htZero
      subst t
      have horderSmall := rotationOrder_zero_le_four p
      have hlargeLe : (p : ℝ) ^ (5 / 6 : ℝ) ≤ 4 :=
        hlarge.trans (by exact_mod_cast horderSmall)
      exact (not_lt_of_ge hlargeLe) hzero
    exact exists_iterate_nonparabolicPoint_with_maximal_secondRotation_of_explicitInequalities
      p hpFive t htParabolic ht0 x hSplitExplicit hNonsplitExplicit hlarge

/-- The pointwise primitive cage relation converted into the fiber bridge
used by cage connectivity. -/
theorem exists_splitMaximalFiberBridge_of_explicitInequality
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (hexplicit :
      (((p - 1).divisors.card : ℕ) : ℝ) ^ 2 *
          ((100522 : ℝ) * Real.sqrt (p : ℝ)) < p)
    (axis other : NormalizedCoordinateAxis) (xi eta : ZMod p)
    (hxi : IsSplitMaximalTrace p xi) (heta : IsSplitMaximalTrace p eta) :
    ∃ middle : NormalizedCoordinateAxis, ∃ y : ZMod p,
      middle ≠ axis ∧ middle ≠ other ∧ IsSplitMaximalTrace p y ∧
        NormalizedFibersMeet
          (normalizedFiberAt axis xi) (normalizedFiberAt middle y) ∧
        NormalizedFibersMeet
          (normalizedFiberAt other eta) (normalizedFiberAt middle y) := by
  obtain ⟨u, huRelation, huOrder⟩ :=
    exists_primitive_cageMiddleUnit_of_explicitInequality
      100522 cageWitnessPointEstimate_oneHundredThousandFiveHundredTwentyTwo
      p hpFive axis other xi eta hxi heta (by
        have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
          rw [Nat.card_units, Nat.card_zmod]
        rw [hcard]
        exact hexplicit)
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  have huSq : (u : ZMod p) ^ 2 ≠ 1 := by
    intro huPower
    have huDvd : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one <| by
      apply Units.ext
      exact huPower
    have huLe : orderOf u ≤ 2 := Nat.le_of_dvd (by norm_num) huDvd
    rw [huOrder, hcard] at huLe
    omega
  refine ⟨cageBridgeAxis axis other, splitTorusTrace u,
    cageBridgeAxis_ne_left axis other, cageBridgeAxis_ne_right axis other, ?_,
    huRelation.1, huRelation.2⟩
  rw [IsSplitMaximalTrace, rotationOrder_splitTorusTrace u huSq, huOrder, hcard]

/-- Pointwise connectivity of the selected cage from its closed numerical
inequality. -/
theorem splitCage_connected_of_explicitInequality
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)] (hpSeven : 7 ≤ p)
    (hexplicit :
      (((p - 1).divisors.card : ℕ) : ℝ) ^ 2 *
          ((100522 : ℝ) * Real.sqrt (p : ℝ)) < p)
    (x y : NormalizedMarkoffSurface (ZMod p))
    (hxCage : IsInSplitCage p x) (hyCage : IsInSplitCage p y) :
    SameNormalizedComponent x y := by
  rcases hxCage with ⟨axis, hxi⟩
  rcases hyCage with ⟨other, heta⟩
  let xi := normalizedCoordinateAt axis x.1
  let eta := normalizedCoordinateAt other y.1
  obtain ⟨middle, z, hmiddleAxis, hmiddleOther, hzMax, hxMeet, hyMeet⟩ :=
    exists_splitMaximalFiberBridge_of_explicitInequality
      p (by omega) hexplicit axis other xi eta hxi heta
  rcases hxMeet with ⟨px, hpxAxis, hpxMiddle⟩
  rcases hyMeet with ⟨py, hpyOther, hpyMiddle⟩
  let pxs : NormalizedMarkoffSurface (ZMod p) :=
    ⟨px, isNormalizedMarkoff_of_mem_normalizedFiberAt hpxAxis⟩
  let pys : NormalizedMarkoffSurface (ZMod p) :=
    ⟨py, isNormalizedMarkoff_of_mem_normalizedFiberAt hpyOther⟩
  have hxFiber : x.1 ∈ normalizedFiberAt axis xi :=
    mem_normalizedFiberAt_coordinate axis x
  have hyFiber : y.1 ∈ normalizedFiberAt other eta :=
    mem_normalizedFiberAt_coordinate other y
  have hxpx : SameNormalizedComponent x pxs :=
    sameNormalizedComponent_of_mem_same_splitMaximalFiber
      p hpSeven axis xi hxi x pxs hxFiber hpxAxis
  have hpxpy : SameNormalizedComponent pxs pys :=
    sameNormalizedComponent_of_mem_same_splitMaximalFiber
      p hpSeven middle z hzMax pxs pys hpxMiddle hpyMiddle
  have hypy : SameNormalizedComponent y pys :=
    sameNormalizedComponent_of_mem_same_splitMaximalFiber
      p hpSeven other eta heta y pys hyFiber hpyOther
  exact sameNormalizedComponent_trans hxpx
    (sameNormalizedComponent_trans hpxpy (sameNormalizedComponent_symm hypy))

private theorem explicitCutoff_seven_le
    {p : ℕ} [Fact p.Prime]
    (hp : explicitStrongApproximationCutoff ≤ p) : 7 ≤ p := by
  have hpOne : (1 : ℝ) ≤ p := by
    exact_mod_cast (explicitCutoff_gt_one.trans_le hp).le
  have hrootLe : (p : ℝ) ^ (1 / 8 : ℝ) ≤ p := by
    simpa using Real.rpow_le_self_of_one_le hpOne (by norm_num : (1 / 8 : ℝ) ≤ 1)
  have hfiveRoot : (5 : ℝ) < (p : ℝ) ^ (1 / 8 : ℝ) :=
    small_fixed_lt_rpow_one_div_eight_of_explicitCutoff hp (by norm_num)
  have hfive : 5 < p := by
    exact_mod_cast hfiveRoot.trans_le hrootLe
  have hpSix : p ≠ 6 := by
    intro hpEq
    subst p
    have hprime : Nat.Prime 6 := Fact.out
    norm_num at hprime
  omega

/-- At the closed cutoff, the first-coordinate endgame reaches a maximal
split rotation with no residual numerical or geometric assumptions. -/
theorem exists_explicit_sameComponent_maximalRotation_of_large_firstCoordinate
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hp : explicitStrongApproximationCutoff ≤ p)
    (x : NormalizedMarkoffSurface (ZMod p))
    (hlarge : (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u1) :
    ∃ y : NormalizedMarkoffSurface (ZMod p),
      SameNormalizedComponent x y ∧ rotationOrder y.1.u2 = p - 1 := by
  let xf : ↑(normalizedFiber1 x.1.u1) := ⟨x.1, x.property, rfl⟩
  obtain ⟨n, hrotation⟩ :=
    exists_iterate_point_with_maximal_secondRotation_of_explicitInequalities
      p ((by norm_num : 5 ≤ 7).trans (explicitCutoff_seven_le hp)) x.1.u1 xf
      (fun orbitExponent orbitOrder hmul horder ↦
        explicit_endgamePrimitiveTrace_explicitInequality_of_card_sub_one
          hp hmul horder (by norm_num))
      (fun orbitExponent orbitOrder hmul horder ↦
        explicit_endgamePrimitiveTrace_explicitInequality_of_card_add_one
          hp hmul horder (by norm_num))
      (explicit_four_lt_rpow_five_div_six hp) hlarge
  let y := (normalizedRotate1Surface^[n]) x
  refine ⟨y, sameNormalizedComponent_iterate_normalizedRotate1Surface x n, ?_⟩
  rw [show y.1 = (normalizedRotate1^[n]) x.1 by
    exact coe_iterate_normalizedRotate1Surface x n]
  exact hrotation

/-- First-coordinate form of the explicit large-order-to-cage endgame. -/
theorem exists_explicit_sameComponent_splitCage_of_large_firstCoordinate
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hp : explicitStrongApproximationCutoff ≤ p)
    (x : NormalizedMarkoffSurface (ZMod p))
    (hlarge : (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u1) :
    ∃ y : NormalizedMarkoffSurface (ZMod p),
      SameNormalizedComponent x y ∧ IsInSplitCage p y := by
  obtain ⟨y, hxy, hyOrder⟩ :=
    exists_explicit_sameComponent_maximalRotation_of_large_firstCoordinate hp x hlarge
  exact ⟨y, hxy, .second, hyOrder⟩

/-- If one of the three coordinate rotations is explicitly large, the point
reaches the selected split cage. -/
theorem exists_explicit_sameComponent_splitCage_of_some_largeCoordinate
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hp : explicitStrongApproximationCutoff ≤ p)
    (x : NormalizedMarkoffSurface (ZMod p))
    (hlarge :
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u1 ∨
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u2 ∨
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u3) :
    ∃ y : NormalizedMarkoffSurface (ZMod p),
      SameNormalizedComponent x y ∧ IsInSplitCage p y := by
  rcases hlarge with hfirst | hsecond | hthird
  · exact exists_explicit_sameComponent_splitCage_of_large_firstCoordinate hp x hfirst
  · let x' := normalizedSwap12Surface x
    have hx' : SameNormalizedComponent x x' := sameNormalizedComponent_swap12Surface x
    have hlarge' :
        (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x'.1.u1 := by
      simpa [x', normalizedSwap12, coe_normalizedSwap12Surface] using hsecond
    obtain ⟨y, hy, hyOrder⟩ :=
      exists_explicit_sameComponent_maximalRotation_of_large_firstCoordinate hp x' hlarge'
    exact ⟨y, sameNormalizedComponent_trans hx' hy, .second, hyOrder⟩
  · let x' := normalizedSwap12Surface (normalizedSwap23Surface x)
    have hx23 : SameNormalizedComponent x (normalizedSwap23Surface x) :=
      sameNormalizedComponent_swap23Surface x
    have hx12 : SameNormalizedComponent (normalizedSwap23Surface x) x' :=
      sameNormalizedComponent_swap12Surface (normalizedSwap23Surface x)
    have hlarge' :
        (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x'.1.u1 := by
      simpa [x', normalizedSwap12, normalizedSwap23, coe_normalizedSwap12Surface,
        coe_normalizedSwap23Surface] using hthird
    obtain ⟨y, hy, hyOrder⟩ :=
      exists_explicit_sameComponent_maximalRotation_of_large_firstCoordinate hp x' hlarge'
    exact ⟨y, sameNormalizedComponent_trans
      (sameNormalizedComponent_trans hx23 hx12) hy, .second, hyOrder⟩

/-- The selected split cage is connected at the closed cutoff. -/
theorem explicit_splitCage_connected
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hp : explicitStrongApproximationCutoff ≤ p)
    (x y : NormalizedMarkoffSurface (ZMod p))
    (hx : IsInSplitCage p x) (hy : IsInSplitCage p y) :
    SameNormalizedComponent x y := by
  exact splitCage_connected_of_explicitInequality p (explicitCutoff_seven_le hp)
    (explicit_cageWitness_explicitInequality hp (by norm_num)) x y hx hy

/-- A large-order point is in the component of any chosen base point of the
selected split cage.  This is the endgame statement consumed by the maximal
bad-orbit argument. -/
theorem explicit_sameNormalizedComponent_of_largeOrder_to_splitCage
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hp : explicitStrongApproximationCutoff ≤ p)
    (base x : NormalizedMarkoffSurface (ZMod p))
    (hbase : IsInSplitCage p base)
    (hlarge :
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u1 ∨
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u2 ∨
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder x.1.u3) :
    SameNormalizedComponent base x := by
  obtain ⟨y, hxy, hy⟩ :=
    exists_explicit_sameComponent_splitCage_of_some_largeCoordinate hp x hlarge
  exact sameNormalizedComponent_trans
    (explicit_splitCage_connected hp base y hbase hy)
    (sameNormalizedComponent_symm hxy)

end

end BGS.Markoff

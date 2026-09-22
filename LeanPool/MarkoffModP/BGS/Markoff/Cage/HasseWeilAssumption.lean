/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.NumberTheory.OneSidedPrimitiveWitness
import LeanPool.MarkoffModP.BGS.Markoff.Incidence.NormalizedGraph

/-!
# Explicit Hasse--Weil interface for the cage

The external input is a point-count estimate on the actual finite set used by the cage
inclusion--exclusion.  Connectivity and primitive extraction are not assumed here.
-/

namespace BGS.Markoff

open Filter
open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

/-- The selected cage core consists of split-maximal normalized traces.  This is sufficient for
Theorem 1 because the endgame constructed in this repository always reaches order `p - 1`. -/
def IsSplitMaximalTrace (p : ℕ) [Fact p.Prime] (t : ZMod p) : Prop :=
  rotationOrder t = p - 1

/-- Choose an axis different from both prescribed axes. -/
def cageBridgeAxis : NormalizedCoordinateAxis → NormalizedCoordinateAxis →
    NormalizedCoordinateAxis
  | .first, .first => .second
  | .first, .second => .third
  | .first, .third => .second
  | .second, .first => .third
  | .second, .second => .first
  | .second, .third => .first
  | .third, .first => .second
  | .third, .second => .first
  | .third, .third => .first

theorem cageBridgeAxis_ne_left (axis other : NormalizedCoordinateAxis) :
    cageBridgeAxis axis other ≠ axis := by
  cases axis <;> cases other <;> decide

theorem cageBridgeAxis_ne_right (axis other : NormalizedCoordinateAxis) :
    cageBridgeAxis axis other ≠ other := by
  cases axis <;> cases other <;> decide

/-- Coordinate selected by an axis label. -/
def normalizedCoordinateAt (axis : NormalizedCoordinateAxis) {R : Type*}
    (x : NormalizedPoint R) : R :=
  match axis with
  | .first => x.u1
  | .second => x.u2
  | .third => x.u3

theorem mem_normalizedFiberAt_iff
    {R : Type*} [CommRing R] {axis : NormalizedCoordinateAxis}
    {t : R} {x : NormalizedPoint R} :
    x ∈ normalizedFiberAt axis t ↔
      IsNormalizedMarkoff x ∧ normalizedCoordinateAt axis x = t := by
  cases axis <;> rfl

/-- The concrete incidence condition counted by the cage fiber-product curve. -/
def CageMiddleTraceRelation
    (p : ℕ) [Fact p.Prime]
    (axis other : NormalizedCoordinateAxis) (xi eta : ZMod p)
    (u : (ZMod p)ˣ) : Prop :=
  NormalizedFibersMeet
      (normalizedFiberAt axis xi)
      (normalizedFiberAt (cageBridgeAxis axis other) (splitTorusTrace u)) ∧
    NormalizedFibersMeet
      (normalizedFiberAt other eta)
      (normalizedFiberAt (cageBridgeAxis axis other) (splitTorusTrace u))

/-- A pair of actual intersection witnesses over a common middle trace. -/
def CageMiddleWitnessPair
    (p : ℕ) [Fact p.Prime]
    (axis other : NormalizedCoordinateAxis) (xi eta : ZMod p) :=
  {z : NormalizedPoint (ZMod p) × NormalizedPoint (ZMod p) //
    z.1 ∈ normalizedFiberAt axis xi ∧
      z.2 ∈ normalizedFiberAt other eta ∧
        normalizedCoordinateAt (cageBridgeAxis axis other) z.1 =
          normalizedCoordinateAt (cageBridgeAxis axis other) z.2}

/-- The common middle coordinate of a witness pair. -/
def cageMiddleWitnessTrace
    {p : ℕ} [Fact p.Prime]
    {axis other : NormalizedCoordinateAxis} {xi eta : ZMod p}
    (z : CageMiddleWitnessPair p axis other xi eta) : ZMod p :=
  normalizedCoordinateAt (cageBridgeAxis axis other) z.1.1

/-- Witness-bearing solutions with the middle unit restricted to a power-map image. -/
abbrev cageMiddleWitnessPowerRangeSolutions
    (p : ℕ) [Fact p.Prime]
    (axis other : NormalizedCoordinateAxis) (xi eta : ZMod p) (d : ℕ) :=
  BGS.rightPowerTraceRangeSolutions
    (cageMiddleWitnessTrace (p := p) (axis := axis) (other := other)
      (xi := xi) (eta := eta))
    (splitTorusTrace : (ZMod p)ˣ → ZMod p) d

/-- Witness-bearing cage point-count target with the geometric component
multiplicity exposed.  The generic fiber product has multiplicity one, while
the diagonal degeneration can have a larger main term.  Requiring a single
positive multiplicity for all divisor ranges is exactly what Möbius inversion
needs; fixing it silently to one would make this statement false.

This is not an allowed external assumption: it must ultimately be derived
from the one general Hasse--Weil theorem. -/
def CageWitnessPointEstimate (coefficient : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p →
    ∀ (axis other : NormalizedCoordinateAxis) (xi eta : ZMod p),
      IsSplitMaximalTrace p xi → IsSplitMaximalTrace p eta →
      ∃ multiplicity : ℕ, 0 < multiplicity ∧
        ∀ d : ℕ, d ∣ Nat.card (ZMod p)ˣ → 0 < d →
          |(Nat.card (cageMiddleWitnessPowerRangeSolutions
              p axis other xi eta d) : ℝ) -
                (multiplicity : ℝ) * (p : ℝ) / d| ≤
            (coefficient : ℝ) * Real.sqrt (p : ℝ)

/-- The Hasse--Weil range estimates imply a primitive middle unit once the explicit divisor
error is smaller than the Möbius main term. -/
theorem exists_primitive_cageMiddleUnit_of_explicitInequality
    (coefficient : ℕ) (hHasse : CageWitnessPointEstimate coefficient)
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (axis other : NormalizedCoordinateAxis) (xi eta : ZMod p)
    (hxi : IsSplitMaximalTrace p xi) (heta : IsSplitMaximalTrace p eta)
    (hexplicit :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p) :
    ∃ u : (ZMod p)ˣ,
      CageMiddleTraceRelation p axis other xi eta u ∧
        orderOf u = Nat.card (ZMod p)ˣ := by
  let leftTrace : CageMiddleWitnessPair p axis other xi eta → ZMod p :=
    cageMiddleWitnessTrace
  let rightTrace : (ZMod p)ˣ → ZMod p := splitTorusTrace
  obtain ⟨multiplicity, hmultiplicity, hEstimate⟩ :=
    hHasse p hpFive axis other xi eta hxi heta
  have hRange : ∀ d : ℕ, d ∣ Nat.card (ZMod p)ˣ → 0 < d →
      |(Nat.card (BGS.rightPowerTraceRangeSolutions
          leftTrace rightTrace d) : ℝ) -
            (multiplicity : ℝ) * (p : ℝ) / d| ≤
        (coefficient : ℝ) * Real.sqrt (p : ℝ) := by
    intro d hdvd hd
    simpa [leftTrace, rightTrace, cageMiddleWitnessPowerRangeSolutions] using
      hEstimate d hdvd hd
  have hpositive :=
    divisorsError_lt_primitiveTraceMoebiusMainTerm_of_explicitInequality
      (Nat.card (ZMod p)ˣ) p 1 coefficient Nat.card_pos (by norm_num) (by
        simpa using hexplicit)
  let : Finite (CageMiddleWitnessPair p axis other xi eta) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  obtain ⟨z, hz⟩ :=
    BGS.rightTraceExactOrderSolutions_nonempty_of_divisorsError_lt_moebiusMain
      leftTrace rightTrace (fun d => (multiplicity : ℝ) * (p : ℝ) / d)
      ((coefficient : ℝ) * Real.sqrt (p : ℝ)) hRange (by
        have hmainPositive :
            0 < primitiveTraceMoebiusMainTerm
              (Nat.card (ZMod p)ˣ) p 1 :=
          lt_of_le_of_lt (by positivity) hpositive
        have hmultiplicityReal : (1 : ℝ) ≤ multiplicity := by
          exact_mod_cast hmultiplicity
        have hscale :
            primitiveTraceMoebiusMainTerm
                (Nat.card (ZMod p)ˣ) p 1 ≤
              (multiplicity : ℝ) *
                primitiveTraceMoebiusMainTerm
                  (Nat.card (ZMod p)ˣ) p 1 := by
          nlinarith
        calc
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
                ((coefficient : ℝ) * Real.sqrt (p : ℝ)) <
              primitiveTraceMoebiusMainTerm
                (Nat.card (ZMod p)ˣ) p 1 := hpositive
          _ ≤ (multiplicity : ℝ) *
                primitiveTraceMoebiusMainTerm
                  (Nat.card (ZMod p)ˣ) p 1 := hscale
          _ = ∑ x ∈ (Nat.card (ZMod p)ˣ).divisorsAntidiagonal,
                (μ x.fst : ℝ) *
                  ((multiplicity : ℝ) * (p : ℝ) / x.fst) := by
            simp only [primitiveTraceMoebiusMainTerm]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            ring)
  rcases z with ⟨w, u⟩
  have hz' := (BGS.mem_rightTraceExactOrderSolutions_iff
    leftTrace rightTrace (Nat.card (ZMod p)ˣ) (w, u)).mp hz
  refine ⟨u, ?_, hz'.2⟩
  rcases w with ⟨⟨firstPoint, secondPoint⟩, hfirst, hsecond, hcommon⟩
  let middle := cageBridgeAxis axis other
  have htrace : normalizedCoordinateAt middle firstPoint = splitTorusTrace u := by
    simpa [leftTrace, rightTrace, cageMiddleWitnessTrace, middle] using hz'.1
  have hfirstSurface : IsNormalizedMarkoff firstPoint := by
    cases axis <;> exact hfirst.1
  have hsecondSurface : IsNormalizedMarkoff secondPoint := by
    cases other <;> exact hsecond.1
  have hfirstMiddle : firstPoint ∈ normalizedFiberAt middle (splitTorusTrace u) := by
    exact mem_normalizedFiberAt_iff.mpr ⟨hfirstSurface, htrace⟩
  have hsecondTrace : normalizedCoordinateAt middle secondPoint = splitTorusTrace u :=
    hcommon.symm.trans htrace
  have hsecondMiddle : secondPoint ∈ normalizedFiberAt middle (splitTorusTrace u) := by
    exact mem_normalizedFiberAt_iff.mpr ⟨hsecondSurface, hsecondTrace⟩
  exact ⟨⟨firstPoint, hfirst, hfirstMiddle⟩,
    ⟨secondPoint, hsecond, hsecondMiddle⟩⟩

/-- Uniform large-prime form of the primitive cage bridge. -/
theorem exists_threshold_primitive_cageMiddleUnit
    (coefficient : ℕ) (hHasse : CageWitnessPointEstimate coefficient) :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
      ∀ (axis other : NormalizedCoordinateAxis) (xi eta : ZMod p),
        IsSplitMaximalTrace p xi → IsSplitMaximalTrace p eta →
        ∃ u : (ZMod p)ˣ,
          CageMiddleTraceRelation p axis other xi eta u ∧
            orderOf u = Nat.card (ZMod p)ˣ := by
  obtain ⟨threshold, hthreshold⟩ :=
    exists_threshold_endgamePrimitiveTrace_explicitInequality coefficient
      (show (0 : ℝ) < 1 / 4 by norm_num)
  refine ⟨max threshold 5, ?_⟩
  intro p hp _ axis other xi eta hxi heta
  have hpThreshold : threshold ≤ p := (le_max_left threshold 5).trans hp
  have hpOne : 1 ≤ p := by omega
  have hpOneReal : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpOne
  have honeLe : ((1 : ℕ) : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 2 - 1 / 4) := by
    simpa using (Real.one_le_rpow hpOneReal (show (0 : ℝ) ≤ 1 / 2 - 1 / 4 by norm_num))
  have hexplicit := hthreshold p hpThreshold 1 honeLe
  apply exists_primitive_cageMiddleUnit_of_explicitInequality
    coefficient hHasse p (by omega) axis other xi eta hxi heta
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  rw [hcard]
  simpa only [Nat.cast_one, one_mul] using hexplicit

/-- The primitive-incidence bridge derived from the Hasse--Weil count and Möbius inversion. -/
theorem exists_threshold_splitMaximalFiberBridge
    (coefficient : ℕ) (hHasse : CageWitnessPointEstimate coefficient) :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
      ∀ (axis other : NormalizedCoordinateAxis) (xi eta : ZMod p),
        IsSplitMaximalTrace p xi → IsSplitMaximalTrace p eta →
        ∃ middle : NormalizedCoordinateAxis, ∃ y : ZMod p,
          middle ≠ axis ∧ middle ≠ other ∧ IsSplitMaximalTrace p y ∧
            NormalizedFibersMeet
              (normalizedFiberAt axis xi) (normalizedFiberAt middle y) ∧
            NormalizedFibersMeet
              (normalizedFiberAt other eta) (normalizedFiberAt middle y) := by
  obtain ⟨threshold, hprimitive⟩ :=
    exists_threshold_primitive_cageMiddleUnit coefficient hHasse
  refine ⟨max threshold 5, ?_⟩
  intro p hp _ axis other xi eta hxi heta
  obtain ⟨u, huRelation, huOrder⟩ :=
    hprimitive p ((le_max_left threshold 5).trans hp) axis other xi eta hxi heta
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  have huSq : (u : ZMod p) ^ 2 ≠ 1 := by
    intro huPower
    have huDvd : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one <| by
      apply Units.ext
      exact huPower
    have huLe : orderOf u ≤ 2 := Nat.le_of_dvd (by norm_num) huDvd
    rw [huOrder, hcard] at huLe
    have hpFive : 5 ≤ p := (le_max_right threshold 5).trans hp
    omega
  refine ⟨cageBridgeAxis axis other, splitTorusTrace u,
    cageBridgeAxis_ne_left axis other, cageBridgeAxis_ne_right axis other, ?_,
    huRelation.1, huRelation.2⟩
  rw [IsSplitMaximalTrace, rotationOrder_splitTorusTrace u huSq, huOrder, hcard]

end

end BGS.Markoff

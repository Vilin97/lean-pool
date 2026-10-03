/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Solutions
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.ProperComparison.Core

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Corollaries of comparison

This file records elementary consequences of the comparison theorems.
-/

@[expose] public noncomputable section

namespace ViscositySolns

variable {n : Nat}

/--
Two comparison inequalities give equality on the domain.

In quantified mathematical form, if `u x ≤ v x` and `v x ≤ u x` for every
`x ∈ C`, then `u x = v x` for every `x ∈ C`.
-/
theorem eqOn_of_comparisonConclusions
    {C : Set (Point n)} {u v : Point n -> Real}
    (huv : ComparisonConclusionOn C u v)
    (hvu : ComparisonConclusionOn C v u) :
    Set.EqOn u v C := by
  intro x hx
  exact le_antisymm (huv x hx) (hvu x hx)

/--
Uniqueness of viscosity solutions once comparison has been proved in both
directions.

In quantified mathematical form, let `u` and `v` be viscosity solutions of the
same equation `F = 0` on `C`. If comparison gives `u x ≤ v x` for every
`x ∈ C` and also gives `v x ≤ u x` for every `x ∈ C`, then `u x = v x` for
every `x ∈ C`.
-/
theorem ViscositySolution.eqOn_of_comparisonConclusions
    {C : Set (Point n)} {F : Operator n} {u v : Point n -> Real}
    (_hu : ViscositySolution C F u)
    (_hv : ViscositySolution C F v)
    (huv : ComparisonConclusionOn C u v)
    (hvu : ComparisonConclusionOn C v u) :
    Set.EqOn u v C :=
  ViscositySolns.eqOn_of_comparisonConclusions huv hvu

end ViscositySolns

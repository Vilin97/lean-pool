/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesPositiveQTwo

/-! # Regularity -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# RHS regularity package for Chapter 3

This file records the Lean-facing form of the manuscript assumption
`g ∈ H^s(Q; R^d)` used by the deterministic right-hand-side estimates.
-/

/--
Note-facing `H^s` regularity for a vector right-hand side on one cube.

The current Besov development consumes this assumption through `L²`
membership and boundedness of the positive-order partial Besov seminorms.
-/
structure CubeVectorBesovHRegularity {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (g : Vec d → Vec d) : Prop where
  memLp : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q)
  partialSeminorms_bddAbove :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovPositiveVectorPartialSeminormTwo Q s N g)

theorem CubeVectorBesovHRegularity.of_exponent_le {d : ℕ}
    {Q : TriadicCube d} {s t : ℝ} {g : Vec d → Vec d}
    (hg : CubeVectorBesovHRegularity Q t g) (hst : s ≤ t) :
    CubeVectorBesovHRegularity Q s g where
  memLp := hg.memLp
  partialSeminorms_bddAbove :=
    cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_exponent_le
      Q g hst hg.partialSeminorms_bddAbove

end

end Homogenization

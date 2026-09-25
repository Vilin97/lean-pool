/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.HerbrandFunctionAtLowerIndex
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Basic.Real.Basic
/-!
# The real Herbrand function from integral lower groups

Between consecutive nonnegative integers, the function interpolates linearly
between the rational Herbrand values. On the negative half-line it is the
identity. Its slope on `(m, m + 1)` is `|G_(m+1)| / |G_0|`.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The piecewise-linear Herbrand function attached to the lower ramification
groups of a valuation subring. This definition itself does not require the
extension to be finite. -/
def herbrandFunction
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (s : ℝ) : ℝ :=
  if 0 ≤ s then
    let m := ⌊s⌋₊
    (herbrandFunctionAtLowerIndex K A m : ℝ) +
      (s - (m : ℝ)) *
        ((Nat.card (lowerRamificationGroup K A (m + 1)) : ℝ) /
          Nat.card (lowerRamificationGroup K A 0))
  else
    s

end ClassFieldTheory

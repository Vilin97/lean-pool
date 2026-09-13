/-
Copyright (c) 2026 Daniel Smania. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Smania
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset


/-!
# Burkholder majorants: basic definitions

Defines the conjugate exponent `q`, `pStar`, the Burkholder expression `v`, and
the sector parameters used to build the majorant.
-/

@[expose] public section

noncomputable section

namespace Majorants

/-- The conjugate exponent, with a harmless value at `p = 1`. -/
def q (p : ℝ) : ℝ := if p = 1 then 0 else p / (p - 1)

/-- `pStar = max p q`; in the main `p ≥ 2` regime this is just `p`. -/
def pStar (p : ℝ) : ℝ := max p (q p)

/-- The original Burkholder-type expression, written with `pStar`. -/
def v (p x y : ℝ) : ℝ :=
  Real.rpow (|((x + y) / 2)|) p
    - Real.rpow (|pStar p - 1|) p * Real.rpow (|((x - y) / 2)|) p

/-- The slope parameter separating the two smooth sectors in the first quadrant. -/
  def a (p : ℝ) : ℝ := 1 - 2 / (pStar p)

/-- Normalization constant for the affine-in-`y` sector formula. -/
  def alpha (p : ℝ) : ℝ :=  p* Real.rpow (pStar p/(pStar p - 1)) (1-p)


end Majorants

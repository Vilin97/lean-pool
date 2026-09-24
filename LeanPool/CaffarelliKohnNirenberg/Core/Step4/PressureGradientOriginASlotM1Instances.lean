/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginASlotHarmonic
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientForceP8
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientRegularity
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientForceSlices
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientInputsCentred

/-!
# The absolute coefficients of the far-force increment

On a clipped cell the prescribed spatial pressure gradient of `prop:bootstrap`
splits into a Riesz field driven by the localized divergence source, the
gradient of the harmonic pressure part, the gradient of the *second force
potential* `p₈` of `eq:pk`, and a Riesz field driven by the centred source
correction.  This file fixes the absolute coefficients that the third summand
costs.

Display (3.5) bounds the classical gradient of `p₈,η` on the inner ball of a
collar of radius `ρ` by the `L¹` size of the force on that collar, with the
coefficient `400·c·cutoffGradientConstant·ρ⁻³`, in which the numeral
`400 = (3/20)⁻²` is the separation of `lem:cutoff`.  At the collar radii
`(R₀ − R₁)/2` of the two parameter triples of `prop:bootstrap` the scale
factor `ρ⁻³` is at most `128³`, and the cell volume contributes one further
factor `4π/3 ≤ 5`.  The three constants recorded here are the scale-free part
of that coefficient, its collar-uniform value, and the Calderón–Zygmund
threshold at which the affine slot pays for the increment.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

noncomputable section
namespace CKN.Core.Step4

/-! ### The absolute coefficients -/

/-- The scale-free part of the far-force gradient coefficient of display (3.5):
the numeral `400 = (3/20)⁻²` of the separation of `lem:cutoff`, the order-one
constant of `eq:har-Ck`, and the cutoff gradient constant. -/
def originASlotForceIncrementConstant : ℝ :=
  400 * sliceForcePotentialConstant * cutoffGradientConstant

/-- The far-force gradient coefficient at collar radii at least `1/128`, where
the scale factor `ρ⁻³` of display (3.5) is at most `128³`. -/
def originASlotForceIncrementCoefficient : ℝ :=
  originASlotForceIncrementConstant * (128 : ℝ) ^ 3

/-- The absolute Calderón–Zygmund threshold at which the affine slot pays for
the far-force increment: the coefficient of display (3.5) times the cell-volume
factor `4π/3 ≤ 5`. -/
def originASlotForceIncrementThreshold : ℝ :=
  5 * originASlotForceIncrementCoefficient

end CKN.Core.Step4

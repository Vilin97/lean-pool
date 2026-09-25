/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardLocalInterpolation
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardSourceMaximal
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardScaleWeight
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyPStoppingRecursion
public import LeanPool.QuadraticCarleson.QuadraticCarleson.NonstandardThresholdAlgebra

/-!
# Summation of the actual nonstandard good collection

This file performs the scale-parameter optimization left after the concrete
nonstandard physical `L²` and local-average pairing estimates. The numerical
weight used below is the source weight

`((s + 1)^2 2^(-s))^(1/q)`.

Its polynomial factor is *inside* the `q`th root. Consequently it is bounded
by a universal constant times `2^(-s/(5q))`, and summing costs only one Holder
conjugate. This is the point of the threshold used in the source argument.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal BigOperators

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

attribute [local instance] Classical.propDecidable

noncomputable
section

/-- The source threshold. It balances the `L²` term carrying
`sqrt (nonstandardScaleWeight s)` against the local `L¹` term. -/
def nonstandardScaleThreshold (a p : ℝ) (s : ℕ) : ℝ :=
  a * nonstandardScaleWeight s ^ (-1 / p)

theorem nonstandardScaleThreshold_pos {a p : ℝ} (ha : 0 < a) (s : ℕ) :
    0 < nonstandardScaleThreshold a p s := by
  unfold nonstandardScaleThreshold
  exact mul_pos ha (Real.rpow_pos_of_pos (nonstandardScaleWeight_pos s) _)

theorem sqrt_weight_mul_threshold_rpow
    {a p : ℝ} (ha : 0 < a) (hp : 0 < p) (s : ℕ) :
    Real.sqrt (nonstandardScaleWeight s) *
        nonstandardScaleThreshold a p s ^ (1 - p / 2) =
      a ^ (1 - p / 2) * nonstandardScaleWeight s ^ ((p - 1) / p) := by
  simpa only [nonstandardScaleThreshold] using
    sqrt_mul_threshold_rpow ha (nonstandardScaleWeight_pos s) hp

theorem threshold_rpow_one_sub
    {a p : ℝ} (ha : 0 < a) (hp : 0 < p) (s : ℕ) :
    nonstandardScaleThreshold a p s ^ (1 - p) =
      a ^ (1 - p) * nonstandardScaleWeight s ^ ((p - 1) / p) := by
  simpa only [nonstandardScaleThreshold] using
    positive_threshold_rpow_one_sub ha (nonstandardScaleWeight_pos s) hp

theorem one_div_holderConjugate_eq {p : ℝ} :
    1 / holderConjugate p = (p - 1) / p := by
  rw [holderConjugate]
  exact reciprocal_holder_quotient p

end

end KrauseLaceyBadScale
end QuadraticCarleson

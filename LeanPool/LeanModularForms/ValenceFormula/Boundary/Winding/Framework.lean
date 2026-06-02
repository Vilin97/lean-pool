/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ContourIntegral.CrossingLimit
import LeanPool.LeanModularForms.ContourIntegral.WindingNumber

/-!
# Single-Crossing Winding Number Framework

Unified framework for computing `generalizedWindingNumber' γ a b s` when the
curve `γ` crosses the point `s` at exactly one parameter value `t₀ ∈ (a, b)`.

## Overview

The three edge/arc winding proofs (RightEdge, LeftEdge, UnitArc) share a
common 5-step structure:

1. Identify the unique crossing parameter `t₀`
2. Define a cutoff function `δ(ε)` that maps the norm threshold `ε` to a
   parameter-space interval radius around `t₀`
3. Prove far/near bounds: curve is ε-far from `s` outside `[t₀-δ, t₀+δ]`,
   and ε-close inside
4. Prove the FTC telescope: the far-segment integrals sum to some `E(ε)`
5. Prove `E(ε) → L` as `ε → 0⁺`, giving `gWN = L / (2πi)`

This file provides:
- `SingleCrossingData`: a structure bundling all geometric ingredients
- `gWN_of_singleCrossing`: the master theorem that assembles these
  ingredients into a `generalizedWindingNumber'` computation
- `gWN_eq_neg_half_of_singleCrossing`: specialized version for `gWN = -1/2`

## Design

The key abstraction is that `pv_tendsto_of_crossing_limit` already handles
steps 3-5 at the level of the PV integral. This framework adds the final
conversion from PV Tendsto to `generalizedWindingNumber'`, handling the
`deriv (fun t => γ t - s) = deriv γ` rewrite that every caller must perform.

The `SingleCrossingData` structure bundles the 8 obligations of
`pv_tendsto_of_crossing_limit` together with a target limit value,
making it easy to instantiate for each geometric case.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

/-- Data for a single-crossing winding number computation.

Bundles all the geometric ingredients needed by `pv_tendsto_of_crossing_limit`:
- A curve `γ : ℝ → ℂ` on `[a, b]` with a unique crossing at `t₀`
- A cutoff function `δ : ℝ → ℝ` mapping norm thresholds to parameter radii
- A threshold below which all bounds hold
- The far/near bounds, FTC telescope, integrability, and limit target -/
structure SingleCrossingData (γ : ℝ → ℂ) (a b : ℝ) (s : ℂ) where
  /-- Target limit value for the PV integral. -/
  L : ℂ
  /-- Unique crossing parameter in `(a, b)`. -/
  t₀ : ℝ
  /-- Proof that `t₀ ∈ (a, b)`. -/
  ht₀ : t₀ ∈ Ioo a b
  /-- Cutoff function: maps norm threshold `ε` to parameter-space radius. -/
  δ : ℝ → ℝ
  /-- Threshold below which all bounds hold. -/
  threshold : ℝ
  /-- Threshold is positive. -/
  hthresh : 0 < threshold
  /-- `δ(ε)` is positive for valid `ε`. -/
  hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ ε
  /-- `δ(ε)` is small enough: stays within `(a, b)` around `t₀`. -/
  hδ_small : ∀ ε, 0 < ε → ε < threshold → δ ε < min (t₀ - a) (b - t₀)
  /-- Far bound: curve is ε-far from `s` outside the δ-neighborhood of `t₀`. -/
  h_far : ∀ ε, 0 < ε → ε < threshold →
    ∀ t ∈ Icc a b, δ ε < |t - t₀| → ε < ‖γ t - s‖
  /-- Near bound: curve is within `ε` of `s` inside the δ-neighborhood. -/
  h_near : ∀ ε, 0 < ε → ε < threshold →
    ∀ t, |t - t₀| ≤ δ ε → ‖γ t - s‖ ≤ ε
  /-- Expression that the far-segment integrals sum to. -/
  E : ℝ → ℂ
  /-- FTC telescope: far-segment integrals equal `E(ε)`. -/
  h_ftc : ∀ ε, 0 < ε → ε < threshold →
    (∫ t in a..(t₀ - δ ε), (γ t - s)⁻¹ * deriv γ t) +
    (∫ t in (t₀ + δ ε)..b, (γ t - s)⁻¹ * deriv γ t) = E ε
  /-- Integrability on the left segment. -/
  hint_left : ∀ ε, 0 < ε → ε < threshold →
    IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t) volume a (t₀ - δ ε)
  /-- Integrability on the right segment. -/
  hint_right : ∀ ε, 0 < ε → ε < threshold →
    IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t) volume (t₀ + δ ε) b
  /-- Limit: `E(ε) → L` as `ε → 0⁺`. -/
  h_limit : Tendsto E (nhdsWithin 0 (Ioi 0)) (nhds L)

namespace SingleCrossingData

/-- The PV integral of `(γ - s)⁻¹ · γ'` tends to `L`. This is the core intermediate
result, obtained directly from `pv_tendsto_of_crossing_limit`. -/
theorem pvTendsto (D : SingleCrossingData γ a b s) :
    Tendsto (fun ε => ∫ t in a..b,
      if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0)
    (nhdsWithin 0 (Ioi 0)) (nhds D.L) :=
  ContourIntegral.pv_tendsto_of_crossing_limit
    D.ht₀ D.hthresh D.hδ_pos D.hδ_small D.h_far D.h_near
    D.h_ftc D.hint_left D.hint_right D.h_limit

end SingleCrossingData

/-- Convert from the natural PV integral form `(γ t - s)⁻¹ * deriv γ t` to the
form `(γ t - s)⁻¹ * deriv (fun t => γ t - s) t` expected by
`generalizedWindingNumber'`. -/
private theorem pv_convert {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} {L : ℂ}
    (h : Tendsto (fun ε => ∫ t in a..b,
      if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0)
      (nhdsWithin 0 (Ioi 0)) (nhds L)) :
    Tendsto (fun ε => ∫ t in a..b,
      if (ε < ‖(γ t - s : ℂ) - 0‖) then (γ t - s)⁻¹ * deriv (fun t => γ t - s) t else 0)
      (nhdsWithin 0 (Ioi 0)) (nhds L) := by
  have hd : ∀ t, deriv (fun t => γ t - s) t = deriv γ t :=
    fun t => deriv_sub_const (f := γ) _
  convert h using 1
  ext ε; congr 1; ext t; simp only [sub_zero, gt_iff_lt, hd]

/-- Master theorem: compute `generalizedWindingNumber'` from single-crossing data.

Given `SingleCrossingData` for curve `γ`, the generalized winding number
at `s` equals `L / (2πi)`.

This handles the conversion from `(γ t - s)⁻¹ * deriv γ t` (used in
the PV integral) to the form `(γ t - s)⁻¹ * deriv (fun t => γ t - s) t`
expected by `generalizedWindingNumber'`. -/
theorem gWN_of_singleCrossing {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ}
    (D : SingleCrossingData γ a b s) :
    generalizedWindingNumber' γ a b s = D.L / (2 * ↑Real.pi * I) :=
  ContourIntegral.gWN_eq_of_pv_tendsto γ a b s D.L (pv_convert D.pvTendsto)

/-- Specialized version: if `L = -(π * I)`, then `gWN = -1/2`.

This is the most common case, used by RightEdge, LeftEdge, and UnitArc. -/
theorem gWN_eq_neg_half_of_singleCrossing {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ}
    (D : SingleCrossingData γ a b s)
    (hL : D.L = -(↑Real.pi * I)) :
    generalizedWindingNumber' γ a b s = -1/2 := by
  apply ContourIntegral.gWN_eq_neg_half_of_pv_tendsto
  exact hL ▸ pv_convert D.pvTendsto

/-- Specialized version: if `L = -(π / 3 * I)`, then `gWN = -1/6`.

Used for elliptic point winding number computations. -/
theorem gWN_eq_neg_sixth_of_singleCrossing {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ}
    (D : SingleCrossingData γ a b s)
    (hL : D.L = -(↑Real.pi / 3 * I)) :
    generalizedWindingNumber' γ a b s = -1/6 := by
  apply ContourIntegral.gWN_eq_neg_sixth_of_pv_tendsto
  exact hL ▸ pv_convert D.pvTendsto

end

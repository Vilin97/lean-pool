/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.Definitions

/-!
# Principal values for the quadratic Hilbert transform

This file establishes basic facts about the symmetric principal-value notion
used in the definition of the quadratic Carleson operator.
-/

open Filter Set
open scoped Topology

namespace QuadraticCarleson

theorem HasQuadraticPrincipalValue.unique
    {modulation : ℝ} {f : ℝ → ℂ} {x : ℝ} {z w : ℂ}
    (hz : HasQuadraticPrincipalValue modulation f x z)
    (hw : HasQuadraticPrincipalValue modulation f x w) : z = w := by
  exact tendsto_nhds_unique hz hw

theorem hasQuadraticPrincipalValue_iff_tendsto
    (modulation : ℝ) (f : ℝ → ℂ) (x : ℝ) (z : ℂ) :
    HasQuadraticPrincipalValue modulation f x z ↔
      Tendsto (fun ε : ℝ => quadraticHilbertTrunc modulation ε f x)
        (nhdsWithin 0 (Ioi 0)) (nhds z) := by
  rfl

end QuadraticCarleson

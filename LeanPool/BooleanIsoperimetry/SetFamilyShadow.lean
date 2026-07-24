/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import LeanPool.BooleanIsoperimetry.Shadow

/-!
# Set-family shadow corollaries

This file exposes thin numeric corollaries of the upstream Kruskal-Katona
upper-shadow theorem in the notation used by the Harper proof.
-/

open scoped BigOperators

open Finset

namespace BooleanIsoperimetry

/- # Set-family shadow corollaries (thin wrapper)

The Kruskal–Katona core (`layer`, `layerInitSeg`, `upperLayerShadow`,
`upperLayerShadow_min`, and the numeric value `upperShadowVal` with its minimum
`upperShadowVal_numeric_min`) has been **relocated upstream** into
`BooleanIsoperimetry.KruskalKatona`, which imports only `Cube` / `Cascade` /
`Macaulay`.  This module now only ties the relocated numeric value
`upperShadowVal` back to the `Shadow.lean` numeric scaffold `upperShadow` (the two
are definitionally equal) so the original public names remain available. -/

/-- The `Shadow.lean` numeric scaffold `upperShadow` and the relocated upstream
`upperShadowVal` are definitionally equal. -/
lemma upperShadow_eq_upperShadowVal (N r t : ℕ) :
    upperShadow N r t = upperShadowVal N r t := rfl

/-- `Shadow.upperShadow` form of the partial-layer identity. -/
theorem upperShadow_eq_card_upperLayerShadow {N r t : ℕ} (hr : 1 ≤ r)
    (ht : t ≤ Nat.choose N r) :
    upperShadow N r t = (upperLayerShadow N r (layerInitSeg N r t)).card := by
  rw [upperShadow_eq_upperShadowVal]
  exact upperShadowVal_eq_card_upperLayerShadow hr ht

/-- `Shadow.upperShadow` form of the Kruskal–Katona numeric minimum. -/
theorem upperShadow_numeric_min {N r t : ℕ} (hr : 1 ≤ r)
    (ht : t ≤ Nat.choose N r) {A : Finset (Cube N)}
    (hA : ∀ x ∈ A, x.card = r) (hcard : A.card = t) :
    upperShadow N r t ≤ (upperLayerShadow N r A).card := by
  rw [upperShadow_eq_upperShadowVal]
  exact upperShadowVal_numeric_min hr ht hA hcard

end BooleanIsoperimetry

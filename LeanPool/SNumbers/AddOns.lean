/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import LeanPool.SNumbers.AddOns.Approximable
import LeanPool.SNumbers.AddOns.Compact

/-!
# Add-ons: compactness measured by s-numbers

Auxiliary Hilbert/Banach-space material around the s-numbers framework,
following Pietsch, *Eigenvalues and s-numbers* (Cambridge, 1987), §2.11.

## Layout

* `AddOns.Approximable` — the class of *approximable* operators (those
  whose approximation numbers `aₙ` tend to zero), its closure properties,
  the implication `IsApproximable ⇒ IsCompactOperator`, and the special case
  `isCompactOperator_of_rank_le` (finite rank ⇒ compact) used by the
  example `SNumbers.Examples.IdentityL1Linfty`.
* `AddOns.Compact` — which s-number sequences detect compactness. On every
  Banach space `S` is compact iff `cₙ(S) → 0`, iff `dₙ(S) → 0`. For the
  approximation numbers this fails (Enflo), but on Hilbert spaces
  *every* s-number sequence works, since all of them agree with `aₙ` there.

The singular value decomposition itself — including the **scalar
factorisation** `SVD.exists_scalar_factorisation` consumed by the
`s`-numbers uniqueness theorem — lives in `BasicResults.SVD`.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/

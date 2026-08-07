/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Forms.Finiteness
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# `genus` (CC1, design §2.1) — root-level, exact challenge signature

Unit: holomorphic-forms (`docs/design/holomorphic-forms.md`). `genus X` is the dimension of the
space of global holomorphic 1-forms `RS.Form1 X`. This is the most load-bearing definition of the
project: it is stated at the **root** namespace with the **exact** signature demanded by
`docs/Jacobian_challenge.lean` (`ConnectedSpace X` is carried only to match that signature — it is
not needed for finiteness, see `Jacobian/Forms/Finiteness.lean`).

Main declarations:
* `genus` — `Module.finrank ℂ (RS.Form1 X)`, honest by the `FiniteDimensional` instance of
  `Jacobian/Forms/Finiteness.lean`.
* `genus_eq_zero_iff_subsingleton` — `genus X = 0 ↔ Subsingleton (RS.Form1 X)`.
-/

open scoped ContDiff Manifold

/-- The genus of a compact Riemann surface: the dimension of the space of global holomorphic
1-forms. -/
noncomputable def genus (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : ℕ :=
  Module.finrank ℂ (RS.Form1 X)

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

omit [ConnectedSpace X] in
/-- The genus vanishes iff there are no nonzero global holomorphic 1-forms. -/
theorem genus_eq_zero_iff_subsingleton : genus X = 0 ↔ Subsingleton (RS.Form1 X) :=
  Module.finrank_zero_iff

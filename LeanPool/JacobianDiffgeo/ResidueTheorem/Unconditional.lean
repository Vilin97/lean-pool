/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.ResidueTheorem.Reduction
import LeanPool.JacobianDiffgeo.CanonicalForms.Existence

/-!
# The unconditional residue theorem (D9 gate now open)

Unit: residue-theorem (`docs/design/residue-theorem.md`). `Reduction.lean`'s
`residue_sum_eq_zero_of_exists_nonconstant`/`MForm.sum_resAt_eq_zero_of_exists_nonconstant`/
`residueTheorem_of_exists_nonconstant` were stated against the hypothesis `hex : ∃ f : ℳ X, ∀ c,
f ≠ algebraMap ℂ (ℳ X) c` — EXACTLY canonical-forms D9's `exists_nonconstant_mero` shape — because
`Jacobian/CanonicalForms/Existence.lean` had not yet landed. It now has (its own gate,
`Jacobian/Finiteness/Chi.lean`, closed), so every conditional export here becomes unconditional
by discharging `hex` with `RS.exists_nonconstant_mero` — each a one-line corollary.

## Exports

* `RS.residue_sum_eq_zero (θ : MForm X) : ∑ᶠ x, θ.resAt x = 0` — **THE residue theorem**,
  unconditional.
* `RS.MForm.sum_resAt_eq_zero (f : ℳ X) (θ : MForm X) : ∑ᶠ x, (f • θ).resAt x = 0` — the
  tail-duality consumption shape (`docs/requests/residue-theorem.md`), unconditional; this is
  the name serre-duality-tails' `pairT_alpha` well-definedness argument should thread instead of
  `MForm.sum_resAt_eq_zero_of_exists_nonconstant` now that no hypothesis needs to be supplied.
* `RS.residueTheorem (θ : MForm X) {S : Finset X} (hS : ...) : ∑ x ∈ S, θ.resAt x = 0` —
  the `Finset`-flexible unconditional corollary.
-/

open scoped ContDiff Manifold

namespace RS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **THE residue theorem, unconditional** (Forster 10.21 / Miranda VI eq. 3.2): on ANY compact
connected Riemann surface, the residues of a meromorphic 1-form sum to zero. Existence of the
nonconstant meromorphic function the trace-route proof needs is no longer a hypothesis — D9
(`exists_nonconstant_mero`) supplies it unconditionally. -/
theorem residue_sum_eq_zero (θ : MForm X) : ∑ᶠ x, θ.resAt x = 0 :=
  residue_sum_eq_zero_of_exists_nonconstant exists_nonconstant_mero θ

/-- The tail-duality consumption shape, unconditional: the residues of `f • θ` sum to zero for
any global meromorphic function `f` and meromorphic 1-form `θ`. -/
theorem MForm.sum_resAt_eq_zero (f : ℳ X) (θ : MForm X) : ∑ᶠ x, (f • θ).resAt x = 0 :=
  MForm.sum_resAt_eq_zero_of_exists_nonconstant exists_nonconstant_mero f θ

/-- `Finset`-flexible unconditional corollary: the residues sum to zero over any finite set
containing the support of `resAt`. -/
theorem residueTheorem (θ : MForm X) {S : Finset X}
    (hS : Function.support (fun x => θ.resAt x) ⊆ (S : Set X)) :
    ∑ x ∈ S, θ.resAt x = 0 :=
  residueTheorem_of_exists_nonconstant exists_nonconstant_mero θ hS

end RS

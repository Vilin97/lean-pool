/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.ResidueTheorem.RationalOnP1
import LeanPool.JacobianDiffgeo.ResidueTheorem.MFormCompat
import LeanPool.JacobianDiffgeo.ResidueTheorem.Calibrated
import LeanPool.JacobianDiffgeo.ResidueTheorem.P1Assembly
import LeanPool.JacobianDiffgeo.ResidueTheorem.Reduction
import LeanPool.JacobianDiffgeo.ResidueTheorem.Unconditional

/-!
# residue-theorem (namespaces `RS`/`RS.P1`) — HEADLINE CLOSED

Unit: residue-theorem (`docs/design/residue-theorem.md`). Blueprint target: `∑_p Res_p(θ) = 0`
for a meromorphic 1-form `θ : MForm X` on a compact connected Riemann surface `X`, any genus.
Built along the §6 trace-to-`ℙ¹` route (PRIMARY per the orchestrator addendum; the PoU/Stokes
Area-Gluing atom of §3–5 was NOT built, as instructed).

## Deliverables (zero sorries)

* **THE residue theorem, UNCONDITIONAL** — `RS.residue_sum_eq_zero (θ : MForm X) :
  ∑ᶠ x, θ.resAt x = 0` (`Unconditional.lean`). Canonical-forms D9's `Existence.lean` has now
  landed (its own gate, `Finiteness/Chi.lean`, closed), so the conditional version this unit
  shipped first —
  ```
  theorem residue_sum_eq_zero_of_exists_nonconstant
      [T2Space X] [CompactSpace X] [ConnectedSpace X]
      (hex : ∃ f : ℳ X, ∀ c : ℂ, f ≠ algebraMap ℂ (ℳ X) c) (θ : MForm X) :
      ∑ᶠ x, θ.resAt x = 0
  ```
  (`Reduction.lean`, `hex` EXACTLY canonical-forms D9's `exists_nonconstant_mero` shape) — is
  discharged by `RS.exists_nonconstant_mero` in one line:
  `residue_sum_eq_zero_of_exists_nonconstant exists_nonconstant_mero θ`.
* **serre-duality-tails' consumption shape, unconditional** — `RS.MForm.sum_resAt_eq_zero
  (f : ℳ X) (θ : MForm X) : ∑ᶠ x, (f • θ).resAt x = 0` (`Unconditional.lean`), the
  well-definedness input of `RS.TailDuality.pairT_alpha`; thread this name now instead of the
  conditional `MForm.sum_resAt_eq_zero_of_exists_nonconstant`. Also the unconditional
  `Finset`-flexible `RS.residueTheorem`.
* **The `ℙ¹` base case** — `RS.P1.sum_resAt_eq_zero (Θ : MForm (OnePoint ℂ)) :
  ∑ᶠ y, Θ.resAt y = 0`, UNCONDITIONAL (`P1Assembly.lean`; `ℙ¹` supplies its own coordinate
  function, no existence hypothesis needed).

## How the two previously-documented gaps were closed

1. **`ℙ¹` assembly (Gap 1)**: the junk-value blocker ("`R_mid` has order `≥ 0` at former poles
   but need not be continuous there") is repaired via mathlib's meromorphic normal form:
   `RS.P1.exists_differentiable_of_ord_nonneg` produces an ENTIRE representative of the
   principal-part remainder agreeing with it at every honest-analyticity point (in particular
   near `∞`, where honesty is forced by the two-chart `compat` identity
   `RS.P1.coeffAt_infty_eq` + meromorphy of the `∞` coefficient). The Liouville-free contour
   fact and the monomial companion-pole computations of `RationalOnP1.lean` then close the
   telescope. No weakened-radius variant was needed.
2. **General-`X` reduction (Gap 2)**: no `MForm.ofPullback` object is needed. The
   `d f`-vs-`resAtX` convention mismatch at poles is exactly the target-chart transition
   `dz = -(w²)⁻¹ dw`, handled by pushing TWO coefficient functions along `F := toP1 φ.holoRepr`
   — `h.holoRepr` over finite values and `Hinf := -(φ.holoRepr)²·h.holoRepr` over `∞` —
   matched to `(h • MForm.d φ).resAt` fibre-point-by-fibre-point
   (`RS.resAtX_toP1_eq_of_ord_nonneg` / `RS.resAtX_toP1_eq_of_ord_neg`), with the two traces
   glued into a single `MFormData (OnePoint ℂ)` by `P1.formOfCoeFn` via
   `trace_const_mul_pullback`. The `hcal` calibration hypothesis of form-trace-tower's
   `resAtP1_trace_eq_sum` is discharged by `RS.exists_fiberStack_translated`
   (`Calibrated.lean`, the existence proofs of `exists_adaptedChartsAt`/`exists_fiberStack`
   re-run with the construction-inherent "target chart is a recentered `chartAt`" conclusion
   exposed). `θ = h • d φ` comes from D8 one-dimensionality, seeded by
   `RS.MForm.d_ne_zero` (the differential of a nonconstant function is nonzero — the
   identity-theorem dichotomy).

## File map

* `RationalOnP1.lean` — the ℙ¹ atoms (previous delivery, unchanged): `formOfCoeFn`,
  the Liouville-free `resAt_neg_sq_inv_mul_comp_inv_eq_zero`, the monomial companion poles.
* `MFormCompat.lean` — `MForm.resAt_eq_zero_of_ord_nonneg`, `MForm.finite_setOf_ord_neg`,
  `MForm.finite_support_resAt` (Compat, upstream candidates for canonical-forms).
* `Calibrated.lean` — calibrated adapted charts / fiber stacks.
* `P1Assembly.lean` — the ℙ¹ base case.
* `Reduction.lean` — the bridges, THE conditional theorem, the conditional tails corollary.
  (`MForm.d_ne_zero` no longer lives here — moved to
  `Jacobian/CanonicalForms/Existence.lean`, imported back from there; see that file's note.)
* `Unconditional.lean` — `RS.residue_sum_eq_zero`/`RS.MForm.sum_resAt_eq_zero`/
  `RS.residueTheorem`, each a one-line corollary discharging `hex` with
  canonical-forms' `RS.exists_nonconstant_mero`.

## Notes for downstream consumers

* **serre-duality-tails** (the only DAG-wired consumer): consume the UNCONDITIONAL
  `RS.MForm.sum_resAt_eq_zero (f) (θ) : ∑ᶠ x, (f • θ).resAt x = 0` (`Unconditional.lean`) —
  no `hex` to thread any more, canonical-forms D9 has landed. Shape confirmed against
  `docs/requests/residue-theorem.md` (the `(f • θ)`-finsum form).
* **canonical-forms**: `MFormCompat.lean`'s three lemmas are upstream candidates (requested
  at design time in `docs/design/residue-theorem.md` §11).
-/

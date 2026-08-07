/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Forms.Basic
import LeanPool.JacobianDiffgeo.Forms.Coeffs
import LeanPool.JacobianDiffgeo.Forms.Analyticity
import LeanPool.JacobianDiffgeo.Forms.OfCoeffs
import LeanPool.JacobianDiffgeo.Forms.MDifferential
import LeanPool.JacobianDiffgeo.Forms.Montel
import LeanPool.JacobianDiffgeo.Forms.Finiteness
import LeanPool.JacobianDiffgeo.Forms.Genus

/-!
# holomorphic-forms (CC1): holomorphic 1-forms and `genus`

API summary (see `docs/design/holomorphic-forms.md`):

* **Definition** (namespace `RS`): `RS.Form1 X` is the bundled `C^ω` sections of the Hom-bundle
  from the tangent bundle to the trivial line bundle; `AddCommGroup`/`Module ℂ` instances are
  found by typeclass inference. Evaluation `η x v : ℂ`; extensionality `RS.Form1.ext'`,
  `RS.Form1.ext_apply`, `RS.Form1.ext_coeffAt`.
* **Chart-coefficient API** (`Coeffs.lean`, the project workhorse): `RS.coeffIn e η : ℂ → ℂ` and
  `RS.coeffAt x η : ℂ` (junk off the chart target); ℂ-linear in `η` (`RS.coeffIn_add`,
  `RS.coeffIn_smul`, `RS.coeffIn_zero`, …, and the `coeffAt` counterparts); transition rule
  `RS.coeffIn_trans` (CC1 orientation: `coeffIn e' η z = deriv (e ∘ e'.symm) z * coeffIn e η (e
  (e'.symm z))` for `e e'` in `maximalAtlas 𝓘(ℂ) ω X` and `z` in the image of the overlap).
* **Analyticity** (`Analyticity.lean`, uses the surfaces-and-charts `ContMDiffAt ↔ AnalyticAt`
  bridge `Jacobian.Surface.Bridges.contMDiffAt_iff_analyticAt_comp_chartAt`):
  `RS.contMDiffAt_section_iff_analyticAt_coeffInFun`, `RS.Form1.analyticAt_coeffAt`,
  `RS.Form1.analyticOnNhd_coeffIn` (any maximal-atlas chart), `RS.Form1.continuousOn_coeffIn`,
  `RS.analyticAt_trans` / `RS.deriv_trans_comp` (transition analyticity and chain rule, reusable).
* **Constructor** (`OfCoeffs.lean`): `RS.Form1CoeffData X ι` packages a covering family of
  `ω`-maximal-atlas charts with analytic, pairwise-compatible coefficient functions;
  `RS.Form1.ofCoeffs` assembles the form, `RS.Form1.coeffIn_ofCoeffs` / `RS.Form1.coeffAt_ofCoeffs`
  recover the given coefficients.
* **Differential** (`MDifferential.lean`): `RS.mdifferential f hf : RS.Form1 X` for `ω`-smooth
  `f : X → ℂ`, with `RS.coeffIn_mdifferential : coeffIn e (mdifferential f hf) = deriv (f ∘ e.symm)`
  on `e.target`; ℂ-linearity in `f`. Also `RS.Form1.smulFun f hf η` (`h • η` for holomorphic `h`)
  with `RS.coeffIn_smulFun`.
* **Planar Montel** (`Montel.lean`, no manifold imports — cheap for `finiteness-and-chi`):
  `RS.montelFamily Ω K C`, `RS.isCompact_closure_montelFamily`, `RS.norm_deriv_le_of_bounded`
  (Cauchy estimate).
* **Finiteness** (`Finiteness.lean`): `RS.GoodCover X` (finite doubly-shrunk chart covers, exist on
  compact T2 `X`: `RS.GoodCover.nonempty`), the coefficient embedding `RS.GoodCover.J` into
  `Π i, C(K i, ℂ)` and its injectivity, the Montel bound and closedness/compactness of its unit
  ball, and `instance : FiniteDimensional ℂ (RS.Form1 X)` for `[T2Space X] [CompactSpace X]`.
* **`genus`** (`Genus.lean`, root level, **exact** `docs/Jacobian_challenge.lean` signature):
  `genus X : ℕ := Module.finrank ℂ (RS.Form1 X)`, honest by the instance above;
  `genus_eq_zero_iff_subsingleton : genus X = 0 ↔ Subsingleton (RS.Form1 X)`.

Downstream units use `coeffIn`/`coeffAt` and the lemmas above — never raw bundle internals
(`Form1` is `abbrev`-only plumbing).
-/

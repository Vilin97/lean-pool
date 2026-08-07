/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.CanonicalForms.MForm
import LeanPool.JacobianDiffgeo.CanonicalForms.OrdRes
import LeanPool.JacobianDiffgeo.CanonicalForms.Quotient
import LeanPool.JacobianDiffgeo.CanonicalForms.Differential
import LeanPool.JacobianDiffgeo.CanonicalForms.OneDimensional
import LeanPool.JacobianDiffgeo.CanonicalForms.LinearSystems
import LeanPool.JacobianDiffgeo.CanonicalForms.Existence

/-!
# canonical-forms: meromorphic 1-forms and the canonical divisor `K` (namespace `RS`)

API summary (see `docs/design/canonical-forms.md`). Builds on `residue-calculus` (BUILT) and
`finiteness-and-chi` (BUILT — its χ-ledger gate closed, see D9 below). **Unit COMPLETE**: all of
D1–D13 are proved in full, zero sorries across all 8 files.

## Architecture (representational revision)

A meromorphic 1-form is a **germ class**: `RS.MForm X` (`Quotient.lean`) is the quotient of raw
`chartAt`-indexed coefficient families (`RS.MFormData X`, `MForm.lean` — the meromorphic analogue
of `Form1`'s `coeffIn` API / dbar's `Form01`, `MeromorphicOn` coefficients, `(1,0)`-transition
rule `deriv τ`, no conjugate) by `RS.MFormData.Eqv`: agreement of the preferred-chart coefficients
on a punctured neighborhood of every chart center. This is the same CC3 quotient pattern as
`ℳ X := MeroGermOn X univ`, and fixes the raw representation's junk-value flaw (meromorphic
coefficients carry junk at poles, so RAW equality is too fine: "`ord = ⊤` everywhere ⇒ `θ = 0`"
is FALSE for raw families but DEFINITIONAL for classes). All reading maps (`ord`, `resAt`,
`laurentCoeffAt`, `divisor`) are germ-at-the-center functionals, so they descend by one-line
congruences; the raw files remain the foundation every proof works through via representatives.

## Exports

* **Data layer** (`MForm.lean`/`OrdRes.lean`, D1–D4/D6 raw): `RS.MFormData X` (structure, `ext`,
  `Zero/Add/Neg/Sub/SMul ℂ/AddCommGroup/Module ℂ`); `RS.MFormCoeffData X ι`/`RS.MFormData.ofCoeffs`
  (covering-chart-family constructor, mirrors `Form1CoeffData`); `RS.MFormData.ord`/`resAt` (read
  via the fixed `chartAt`), chart-invariance `RS.MFormData.ord_eq_of_mem_source`/
  `resAt_eq_of_mem_source`, cross-point reading
  `RS.MFormData.ord_eq_meromorphicOrderAt_of_mem_source`
  (`θ.ord p = meromorphicOrderAt (θ.coeffAt x) (chartAt ℂ x p)` for `p` in the chart source —
  D12's engine); propagation `eventually_ord_eq_top`/`eventually_ord_eq_zero`;
  `RS.MFormData.divisor`/`degree`; `RS.MFormData.ofForm1`/`RS.Form1.toMFormData`;
  `RS.MFormData.smul`/`d`/`dlog` (via the canonical `MeroGermOn.holoRepr`; the `compat`-at-poles
  case split is `RS.deriv_comp_chart_congr`).
* **`RS.MForm X`** (`Quotient.lean`, D1/D2/D4–D6): the quotient type, `MForm.mk`/`exists_rep`/
  `ind`/`sound`/`mk_eq_mk`, `AddCommGroup`/`Module ℂ`; `RS.MForm.ord`/`resAt`/`laurentCoeffAt`
  (lifted, `@[simp]` `ord_mk`/`resAt_mk`/`laurentCoeffAt_mk`, `resAt_eq_laurentCoeffAt`);
  `RS.MForm.divisor`/`degree`/`divisor_apply`/`divisor_zero`; propagation lemmas; **D5**
  `RS.MForm.eq_zero_or_forall_ord_ne_top` (the global zero-dichotomy, clopen + connectedness) with
  `RS.MForm.ord_ne_top`/`eq_zero_iff_forall_ord_eq_top`.
* **Differentials & the `ℳ(X)`-module structure** (`Differential.lean`, D7):
  `RS.MForm.ofForm1`/`RS.Form1.toMForm : Form1 X →ₗ[ℂ] MForm X`/`RS.MForm.ofForm1_injective`;
  the full **`Module (ℳ X) (MForm X)`** instance plus `IsScalarTower ℂ (ℳ X) (MForm X)`/
  `SMulCommClass ℂ (ℳ X) (MForm X)` (via the `holoRepr` germ identities `RS.Mero.holoRepr_add`/
  `mul`/`smul`/`inv`/`zero`/`one`); `RS.MForm.ord_smul_mero` (`(h • Θ).ord x = h.ord x + Θ.ord x`);
  `RS.MForm.d` with `d_add`/`d_const`; `RS.MForm.dlog` with the argument-principle atom
  `RS.MForm.resAt_dlog : (dlog f).resAt x = (f.ord x).untop₀` (junk-robust, no `f ≠ 0`).
* **D8, one-dimensionality** (`OneDimensional.lean`): `RS.MForm.exists_unique_smul_of_ne_zero`
  (`θ₀ ≠ 0 → ∀ θ, ∃! h : ℳ X, θ = h • θ₀`; existence `RS.MForm.exists_smul_eq` by chart-local
  ratios + `MeroGermOn.exists_glue`, uniqueness `RS.MForm.smul_left_injective` via
  `RS.MForm.smul_eq_zero_iff`). Needs `[T1Space X] [ConnectedSpace X]`.
* **D10, the canonical divisor** (`OneDimensional.lean`): `RS.canonicalDivisorOf θ₀ := θ₀.divisor`
  (an `abbrev`), `RS.MForm.divisor_smul_mero`, and `RS.canonicalDivisorOf_linearEquiv` (any two
  canonical divisors differ by a principal divisor). D10 lives here, not in the gated
  `Existence.lean` (see below) — it has no finiteness dependence.
* **D11** (`LinearSystems.lean`): `RS.MForm.OmegaSpace D : Submodule ℂ (MForm X)` (order-wise,
  instance-free)/`RS.MForm.mem_omegaSpace_iff`/`RS.MForm.i D` (index of speciality);
  `RS.MForm.smul_mem_omegaSpace_iff` (the pointwise dictionary);
  `RS.ΩIsoLinSys (h₀ : θ₀ ≠ 0) (D) : MForm.OmegaSpace D ≃ₗ[ℂ] LinSys (D + canonicalDivisorOf θ₀)`
  and `RS.i_eq_l_add_canonicalDivisorOf` (`[T1] [T2] [CompactSpace] [ConnectedSpace]`).
* **D12** (`LinearSystems.lean`): `RS.form1ToOmega`/`RS.form1ToOmega_surjective`/
  `RS.holomorphicMFormsEquiv : Form1 X ≃ₗ[ℂ] MForm.OmegaSpace (0 : Divisor X)` (NO topological
  instances needed — the surjectivity repair works pointwise through `holoRepr`), and
  `RS.genus_eq_finrank_omegaSpace_zero` (`[T2] [CompactSpace] [ConnectedSpace]`).
* **D13** (`LinearSystems.lean`): `RS.MLFormData`/`.Realizes` (on classes, via
  `MForm.laurentCoeffAt`)/`.totalRes`/`.Realizes.resAt_eq`.
* **D9** (`Existence.lean`, the unit's raison d'être, gate now closed since
  `Jacobian/Finiteness/Chi.lean` landed): `RS.exists_nonconstant_mero [T2Space X] [CompactSpace X]
  [ConnectedSpace X] : ∃ f : ℳ X, ∀ c : ℂ, f ≠ algebraMap ℂ (ℳ X) c` (Forster 16.11 pattern: a
  divisor `single P n` of large enough degree forces `l(D) ≥ 2 > 1 = l(0)` via
  `finiteness-and-chi`'s `chi_zero_add_degree_le_l`, so `L(0) = span{1}` is a PROPER subspace of
  `L(D)`) and `RS.exists_ne_zero_mform [T2Space X] [CompactSpace X] [ConnectedSpace X] :
  ∃ θ : MForm X, θ ≠ 0` (`:= ⟨MForm.d f, MForm.d_ne_zero hf⟩`); `RS.exists_canonicalDivisor` (a
  canonical divisor concretely exists, feeding D10's `canonicalDivisorOf`). Also
  `Function.locallyFinsuppWithin.degree_single (P) (n) : (single P n : Divisor X).degree = n` —
  closes the §1.6 `Divisor.single` gap honestly: mathlib's own `single` already lands in
  `locallyFinsuppWithin univ Y`, definitionally `RS.Divisor X`, so no separate constructor was
  ever needed, only this degree fact (generalizing `Finiteness.degree_single`'s fixed `n = 1`).
  `RS.MForm.d_ne_zero` also lives here (moved from `residue-theorem/Reduction.lean`, which had
  proved it purely with canonical-forms/meromorphic-and-divisors machinery as an internal step —
  since residue-theorem is DOWNSTREAM of canonical-forms, importing it back would cycle; this is
  the clean home, and `residue-theorem` now imports it from here).
-/

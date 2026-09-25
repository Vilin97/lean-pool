/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornSigmaPowerClearedInequalitySupplier
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalizedCor732SigmaSupplier

/-!
# Wedhorn 8.34(ii) — σ-factored supplier from localized Cor 7.32 (T076)

T073 (`WedhornSigmaPowerClearedInequalitySupplier`) accepts a
σ-factored supplier as input and produces T072's named residual
`SigmaProductClearedInequalitySupplier`. The σ-factored supplier
shape is:

```
∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
  v.vle f s → v.vle 1 t' → ¬ v.vle t' 0 →
  ∃ (σ : Aˣ) (N : ℕ),
    v.vle (t' * D_s ^ N * (σ : A)) (D_s ^ (N + 1) * (σ : A)) ∧
    ¬ v.vle D_s 0
```

This file lands the supplier-side route: a named Prop predicate
`SigmaFactoredSupplier` for the supplier shape, packaging theorems
exposing how T065's localized Cor 7.32 σ-supplier feeds the σ choice,
and an alternative reduction from the direct upper-bound supplier
via the trivial witness `σ := 1`, `N := 0`.

## What this file provides

* `SigmaFactoredSupplier` — named Prop predicate matching T073's
  σ-factored supplier shape exactly. Reusable mathlib-style.

* `sigma_factored_supplier_via_uniform_sigma` — supplier-level
  packaging: from a **uniform σ : Aˣ** (chosen once across all
  per-`(v, t')`) plus a per-`(v, t')` σ-factored inequality
  hypothesis at this fixed σ, produce
  `SigmaFactoredSupplier D_T s D_s f`. Trivial existential
  unpacking; useful when the σ-construction supplies a single global
  σ (e.g., T065's localized Cor 7.32 σ_loc).

* `sigma_factored_supplier_via_direct_upper_bound_supplier` —
  alternative route: from a per-`(v, t')` direct upper-bound supplier
  `v.vle t' D_s ∧ ¬ v.vle D_s 0` (the original Wedhorn 8.34(ii) per-
  piece content, equivalent to T067's pointwise clearing), produce
  `SigmaFactoredSupplier` with witness `σ := 1`, `N := 0`. Useful
  when the σ-construction is already simplified to direct form.

* `sigma_factored_supplier_via_localized_cor732` — **ticket-named
  main theorem**: instantiated at `A := Localization.Away s`, the
  σ-factored supplier holds with σ supplied by T065's localized
  Cor 7.32 supplier, given the named per-`(v, t')` σ-factored
  inequality hypothesis. This is the strongest theorem T076 can
  prove without committing to a specific σ-construction algebraic
  identity beyond what is captured by the named hypothesis.

* `SigmaProductClearedInequalitySupplier_via_sigma_factored_supplier_named`
  — end-to-end bridge composing T076's `SigmaFactoredSupplier`
  named predicate with T073's
  `SigmaProductClearedInequalitySupplier_via_sigma_factored_supplier`
  to produce T072's residual directly.

## The named source-restricted residual

T076 reduces the σ-factored supplier route to **one named source-
restricted hypothesis**: the per-`(v, t')` σ-factored inequality at
a uniform σ. Concretely, parameterised by σ : Aˣ:

```
∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
  v.vle f s → v.vle 1 t' → ¬ v.vle t' 0 →
  ∃ N : ℕ,
    v.vle (t' * D_s^N * (σ : A)) (D_s^(N+1) * (σ : A)) ∧ ¬ v.vle D_s 0
```

This is per-`(v, t')` source-restricted (no universal-over-`D_T`
lower bound), the exponent `N` is per-`(v, t')` chosen, and the
σ is supplied uniformly (by an external σ-construction lane such as
T065's localized Cor 7.32 supplier).

The genuine Wedhorn 8.34(ii) σ-construction algebraic content
(deriving the σ-factored inequality from σ-strict-domination + the
σ-construction's denominator-clearing identity at each Laurent
piece) lives in this named residual. T076 does not commit to a
specific algebraic identity at this layer.

## What T076 does NOT do

* Does **NOT** introduce or use the rejected universal-over-`D_T`
  lower bound or the global universal-over-Spa multi-element bound
  (per T035's counter-example).

* Does **NOT** add any final `ValuationSpectrum.tateAcyclicity`
  hypothesis. T076 is a σ-construction-side supplier wrapper.

* Does **NOT** depend on T001 / Lane-B / Cor 8.32 / Jacobson /
  faithful-flatness / Zavyalov / bivariate-overlap / σ-power-decay /
  M-power-decay content.

## Notes

* No root import; leaf-level file.
* Imports T073 (`WedhornSigmaPowerClearedInequalitySupplier`) for
  the σ-factored supplier consumer and T065
  (`WedhornLocalizedCor732SigmaSupplier`) for the localized Cor 7.32
  σ-supplier.
* No edits to T031–T075 accepted leaves, root imports, or final
  theorem signatures. Disjoint from Tertiary's direct-route file
  and Primary's T075 file.
* All declarations are fully proven, depend only on the standard
  Lean kernel postulates, and avoid native compilation and unchecked
  tactics.
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

omit [IsTopologicalRing A] in
/-- **σ-factored supplier shape** (T076 named Prop predicate).

Prop predicate matching T073's σ-factored supplier shape exactly:
the per-`(v, t')` source-restricted Wedhorn 8.34(ii) σ-construction
algebraic content. At every `v ∈ Spa A A⁺` in the Laurent piece for
some `t' ∈ D_T`, supply σ : Aˣ, N : ℕ, the σ-factored inequality,
and the non-vanishing of `D_s`.

The σ is per-`(v, t')` (allowed to vary), and the exponent `N` is
also per-`(v, t')`. Per-`(v, t')` source-restricted: only `t'` and
`D_s` appear in the cleared inequality, no other `t_i ∈ D_T`. -/
def SigmaFactoredSupplier
    (D_T : Finset A) (s D_s f : A) : Prop :=
  ∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
    v.vle f s →
    v.vle (1 : A) t' →
    ¬ v.vle t' 0 →
    ∃ (σ : Aˣ) (N : ℕ),
      v.vle (t' * D_s ^ N * (σ : A)) (D_s ^ (N + 1) * (σ : A)) ∧
      ¬ v.vle D_s 0

omit [IsTopologicalRing A] in
/-- **σ-factored supplier from a uniform σ + per-`(v, t')` factored
inequality** (T076 packaging theorem).

From a uniform σ : Aˣ chosen once across all per-`(v, t')` (e.g.,
T065's localized Cor 7.32 σ_loc) plus a per-`(v, t')` σ-factored
inequality hypothesis at this fixed σ, produce
`SigmaFactoredSupplier D_T s D_s f`.

Trivial existential unpacking — the per-`(v, t')` σ-factored
inequality hypothesis is the genuine Wedhorn 8.34(ii) σ-construction
algebraic content; this theorem just packages it. -/
theorem sigma_factored_supplier_via_uniform_sigma
    (D_T : Finset A) (s D_s f : A) (σ : Aˣ)
    (h_factored_inequality :
      ∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
        v.vle f s →
        v.vle (1 : A) t' →
        ¬ v.vle t' 0 →
        ∃ N : ℕ,
          v.vle (t' * D_s ^ N * (σ : A))
            (D_s ^ (N + 1) * (σ : A)) ∧
          ¬ v.vle D_s 0) :
    SigmaFactoredSupplier D_T s D_s f := by
  intro t' ht' v hv_spa hv_f hv_one_t hv_t_ne
  obtain ⟨N, hN⟩ := h_factored_inequality t' ht' v hv_spa hv_f hv_one_t hv_t_ne
  exact ⟨σ, N, hN⟩

omit [IsTopologicalRing A] in
/-- **σ-factored supplier from direct upper-bound supplier**
(T076 alternative `σ = 1`, `N = 0` route).

From a per-`(v, t')` direct upper-bound supplier (the original
Wedhorn 8.34(ii) per-piece content, equivalent to T067's pointwise
clearing modulo explicit `D_s` non-vanishing), produce
`SigmaFactoredSupplier` with the trivial witness `σ := 1`, `N := 0`.

**Proof**: at `σ = 1`, the σ-factored inequality `v.vle (t' * D_s^N
* 1) (D_s^(N+1) * 1)` reduces to `v.vle (t' * D_s^N) (D_s^(N+1))`;
at `N = 0`, this further reduces to `v.vle t' D_s` (via `pow_zero`,
`mul_one`, `pow_one`), which is the direct upper bound hypothesis.

Useful when the σ-construction is already simplified to direct form
(e.g., when T065's σ_loc has been cancelled out at the supplier level
upstream). -/
theorem sigma_factored_supplier_via_direct_upper_bound_supplier
    (D_T : Finset A) (s D_s f : A)
    (h_direct_supplier :
      ∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
        v.vle f s →
        v.vle (1 : A) t' →
        ¬ v.vle t' 0 →
        v.vle t' D_s ∧ ¬ v.vle D_s 0) :
    SigmaFactoredSupplier D_T s D_s f := by
  intro t' ht' v hv_spa hv_f hv_one_t hv_t_ne
  obtain ⟨h_clear, h_D_s_ne⟩ :=
    h_direct_supplier t' ht' v hv_spa hv_f hv_one_t hv_t_ne
  refine ⟨1, 0, ?_, h_D_s_ne⟩
  simpa only [pow_zero, mul_one, zero_add, pow_one, Units.val_one] using h_clear

omit [IsTopologicalRing A] in
/-- **`SigmaProductClearedInequalitySupplier` via the named σ-factored
supplier predicate** (T076 end-to-end bridge to T072's residual).

Direct composition of T076's `SigmaFactoredSupplier` with T073's
`SigmaProductClearedInequalitySupplier_via_sigma_factored_supplier`:
from the named σ-factored supplier predicate, produce T072's named
residual `SigmaProductClearedInequalitySupplier`. -/
theorem SigmaProductClearedInequalitySupplier_via_sigma_factored_supplier_named
    (D_T : Finset A) (s D_s f : A)
    (h_supplier : SigmaFactoredSupplier D_T s D_s f) :
    SigmaProductClearedInequalitySupplier D_T s D_s f :=
  SigmaProductClearedInequalitySupplier_via_sigma_factored_supplier
    D_T s D_s f h_supplier

omit [PlusSubring A] in
/-- **`σ_loc` is a localized Cor 7.32 σ-output for `(P, T, s, T_D, s_D)`**
(T076 named predicate restricting σ to T065-style outputs).

Captures the σ-rescaled Laurent cover property of σ_loc on the
localized adic spectrum: at every `w ∈ Spa(Localization.Away s, …)`,
some test element `τ ∈ localizedTestFamily s T_D s_D` rescaled by
`σ_loc⁻¹` lies in the canonical Laurent piece `R({1}) (σ_loc⁻¹ * τ)`
containing `w`.

This is **exactly the cover-property output** of T065's
`localizedCor732_sigma_supplier_for_actual_C1` at the named σ_loc,
extracted as a Prop predicate. Quantifying over σ_loc satisfying this
predicate restricts to T065-style outputs (rather than all units of
the localization). -/
def IsLocalizedCor732SigmaLocOutput
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    ∃ t ∈ (localizedTestFamily s T_D s_D).image
      (fun τ => ((σ_loc⁻¹ : (Localization.Away s)ˣ) :
        Localization.Away s) * τ),
      w ∈ rationalOpen
        ({(1 : Localization.Away s)} :
          Finset (Localization.Away s)) t

omit [PlusSubring A] in
/-- **σ-factored supplier from localized Cor 7.32 σ + factored
inequality at the T065-produced σ_loc** (T076 ticket-named main
theorem, revised).

End-to-end packaging on the localization side: T065's localized
Cor 7.32 supplier produces some `σ_loc` together with the σ-rescaled
Laurent cover property
`IsLocalizedCor732SigmaLocOutput P T s hopen T_D s_D σ_loc`. T076's
revised theorem takes the residual as a **function depending on the
specific `σ_loc` together with its T065 cover-property witness** —
not as a universal-over-all-units claim. The residual quantifier
ranges only over σ_loc that are valid T065 outputs.

**Inputs**:

* Standard localized Cor 7.32 hypotheses (`P, T, s, hopen, π_loc,
  hI_loc, hπ_loc_tn, hπ_loc_unit, hArch_loc, T_D, s_D, hT_loc`).

* `D_T_loc, T_base_loc, s_base_loc, D_s_loc, f_loc` — the
  localization-side rationalOpen data.

* `_h_factored_inequality_at_T065_sigma_loc` — **the named source-
  restricted residual**: a function `(σ_loc, h_cover) ↦ factored
  inequality at σ_loc`, where `h_cover` witnesses
  `IsLocalizedCor732SigmaLocOutput … σ_loc`. The residual is supplied
  only for σ_loc that satisfy the T065 cover-property; it is **not**
  a universal-over-all-units claim. The residual depends explicitly
  on the same σ_loc that T065 will produce.

**Output**: ∃ σ_loc : (Localization.Away s)ˣ,
`SigmaFactoredSupplier D_T_loc s_base_loc D_s_loc f_loc` — i.e., the
σ-factored supplier holds with σ supplied by T065.

**Composition in the proof body**: extract `(σ_loc, h_cover_t)` from
T065's `localizedCor732_sigma_supplier_for_actual_C1`, apply the
residual function at this specific `(σ_loc, h_cover_t)` to get the
factored inequality at this σ_loc, then package via
`sigma_factored_supplier_via_uniform_sigma`. The residual function
is consumed at exactly one input — the T065-produced `(σ_loc,
h_cover_t)` pair.

**Why this revised shape**: the previous revision quantified over all
units of the localization, which is too strong for the Wedhorn
8.34(ii) interface — only the σ_loc supplied by T065 matters. The
revised shape ties the residual to the T065-produced σ_loc through
the explicit `IsLocalizedCor732SigmaLocOutput` precondition. -/
theorem sigma_factored_supplier_via_localized_cor732
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ (π_loc : (locPairOfDefinition P T s hopen).A₀)
      (_hI_loc : (locPairOfDefinition P T s hopen).I = Ideal.span {π_loc})
      (_hπ_loc_tn : IsTopologicallyNilpotent
        ((locPairOfDefinition P T s hopen).A₀.subtype π_loc))
      (_hπ_loc_unit : IsUnit
        ((locPairOfDefinition P T s hopen).A₀.subtype π_loc))
      (_hArch_loc : ∀ w : Spv (Localization.Away s),
        letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero (Localization.Away s)))
      (T_D : Finset A) (s_D : A)
      (_hT_loc : ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D, ¬ w.vle τ 0)
      (D_T_loc : Finset (Localization.Away s))
      (s_base_loc D_s_loc f_loc : Localization.Away s)
      (_h_factored_inequality_at_T065_sigma_loc :
        ∀ (σ_loc : (Localization.Away s)ˣ),
          IsLocalizedCor732SigmaLocOutput P T s hopen T_D s_D σ_loc →
          ∀ t' ∈ D_T_loc,
            ∀ v ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
              v.vle f_loc s_base_loc →
              v.vle (1 : Localization.Away s) t' →
              ¬ v.vle t' 0 →
              ∃ N : ℕ,
                v.vle (t' * D_s_loc ^ N * (σ_loc : Localization.Away s))
                  (D_s_loc ^ (N + 1) *
                    (σ_loc : Localization.Away s)) ∧
                ¬ v.vle D_s_loc 0),
    ∃ _ : (Localization.Away s)ˣ,
      SigmaFactoredSupplier D_T_loc s_base_loc D_s_loc f_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_D s_D hT_loc
    D_T_loc s_base_loc D_s_loc f_loc h_factored_inequality_at_T065_sigma_loc
  -- Extract (σ_loc, h_cover_t) from T065. h_cover_t witnesses the
  -- IsLocalizedCor732SigmaLocOutput predicate at this specific σ_loc.
  obtain ⟨σ_loc, h_cover_t⟩ :=
    localizedCor732_sigma_supplier_for_actual_C1 P T s hopen
      π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_D s_D hT_loc
  refine ⟨σ_loc, ?_⟩
  -- Apply the residual function at the T065-produced (σ_loc, h_cover_t)
  -- pair. The residual is consumed at exactly one input — the
  -- T065-produced σ_loc with its cover-property witness.
  exact sigma_factored_supplier_via_uniform_sigma D_T_loc s_base_loc D_s_loc
    f_loc σ_loc
    (h_factored_inequality_at_T065_sigma_loc σ_loc h_cover_t)

end ValuationSpectrum

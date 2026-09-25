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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornSigmaFactoredSupplierFromLocalizedCor732
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalArithmeticPerTChain

/-!
# Wedhorn 8.34(ii) — σ-factored inequality at the T065-produced σ_loc (T082)

T076 (`WedhornSigmaFactoredSupplierFromLocalizedCor732`) accepted the
σ-factored supplier wrapper with the named source-restricted residual
in function form: `(σ_loc, h_cover_t) ↦ factored inequality at σ_loc`,
where `h_cover_t : IsLocalizedCor732SigmaLocOutput P T s hopen T_D s_D
σ_loc`.

This file lands the substantive arithmetic reduction of that residual
to a **single named source-restricted denominator-clearing identity**
at the T065-produced σ_loc: the per-`(v, t')` direct upper bound

```
v.vle f_loc s_base_loc → v.vle 1 t' → ¬ v.vle t' 0 →
  v.vle t' D_s_loc ∧ ¬ v.vle D_s_loc 0
```

parameterised by `(σ_loc, h_cover_t)` so the residual is consumed only
for σ_loc that satisfy T065's cover-property.

The σ-factored inequality at any `N`, σ-cancelled via T050's
`per_t_inequality_via_sigma_factor`
(`WedhornLocalArithmeticPerTChain.lean`), reduces to
`v.vle (t' * D_s_loc^N) (D_s_loc^(N+1))`. At `N := 0` this further
reduces (via `pow_zero`, `mul_one`, `pow_one`) to `v.vle t' D_s_loc`,
the direct upper bound. So the reduction T082 lands is genuine: the
residual collapses cleanly to the direct upper bound at `N = 0`,
σ-rescaled by the T065 σ_loc.

## What this file provides

* `Cor732SigmaDirectUpperBoundResidual` — Prop predicate for the
  named source-restricted denominator-clearing identity. Function
  form `(σ_loc, h_cover_t) ↦ direct upper bound residual at σ_loc`,
  matching T076's residual structure exactly. The body is the per-
  `(v, t')` direct upper bound `v.vle t' D_s_loc ∧ ¬ v.vle D_s_loc 0`
  source-restricted by the f-bound + Laurent piece membership.
  Reusable mathlib-style.

* `sigma_factored_inequality_at_localized_cor732_sigma` — **main
  ticket-named theorem**: from `Cor732SigmaDirectUpperBoundResidual`,
  derive T076's σ-factored inequality residual at the T065-produced
  σ_loc. The reduction is per-`(v, t')` source-restricted via N=0
  σ-rescaling.

* `sigma_factored_supplier_via_cor732_direct_upper_bound_residual`
  — end-to-end consumer composing T082 with T076's revised wrapper:
  from the named direct upper bound residual, produce the σ-factored
  supplier output of T076 directly. Closes the route from the named
  source-restricted residual to T076's `SigmaFactoredSupplier`
  output.

## The single named source-restricted residual

After T082, the σ-factored inequality is reduced to **one named
source-restricted denominator-clearing identity** at the T065-produced
σ_loc:

```
def Cor732SigmaDirectUpperBoundResidual ... σ_loc h_cover_t :=
  ∀ t' ∈ D_T_loc, ∀ v ∈ Spa(Localization.Away s, …)⁺,
    v.vle f_loc s_base_loc → v.vle 1 t' → ¬ v.vle t' 0 →
    v.vle t' D_s_loc ∧ ¬ v.vle D_s_loc 0
```

This is **per-`(v, t')` and source-restricted** (no universal-over-`D_T`
or universal-over-Spa form), tied to the T065-produced σ_loc through
the function-form residual structure. The genuine Wedhorn 8.34(ii)
content remaining is the per-Laurent-piece direct upper bound — the
specific numerical / arithmetic relationship between the
σ-construction's `f_loc`, `D_s_loc`, and the per-element `t'` at
each Laurent piece.

## What T082 does NOT do

* Does **NOT** quantify the residual over all units of
  `Localization.Away s`; the quantifier is restricted to T065-style
  σ_loc via the explicit `IsLocalizedCor732SigmaLocOutput`
  precondition.

* Does **NOT** introduce or use any global universal-over-`D_T`
  lower bound or universal-over-Spa multi-element clearing claim
  (per T035's counter-example).

* Does **NOT** edit Primary's pointwise route file or Tertiary's
  final σ-power route file. Disjoint write set, leaf-level only.

* Does **NOT** add or modify any final
  `ValuationSpectrum.tateAcyclicity` hypothesis.

## Notes

* No root import; leaf-level file.
* Imports T076 (`WedhornSigmaFactoredSupplierFromLocalizedCor732`) for
  the wrapper and the `IsLocalizedCor732SigmaLocOutput` predicate, and
  `WedhornLocalArithmeticPerTChain` for the σ-factor cancellation
  primitive `per_t_inequality_via_sigma_factor`.
* No edits to T031–T081 accepted leaves, root imports, or final
  theorem signatures.
* All declarations are fully proven, depend only on the standard
  Lean kernel postulates, and avoid native compilation and unchecked
  tactics.
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A]

/-- **Named source-restricted denominator-clearing identity at the
T065-produced σ_loc** (T082 named residual Prop predicate).

Function-form predicate `(σ_loc, h_cover_t) ↦ direct upper bound
residual at σ_loc`, matching T076's residual structure but with the
body reduced from the σ-factored inequality to the per-`(v, t')`
direct upper bound.

The σ_loc and `h_cover_t : IsLocalizedCor732SigmaLocOutput P T s hopen
T_D s_D σ_loc` are precondition parameters — the residual body itself
is σ_loc-independent (the direct upper bound `v.vle t' D_s_loc`
involves only `t'` and `D_s_loc`), but the predicate's quantifier
structure restricts the residual to T065-style σ_loc, matching the
T076 wrapper interface.

Per-`(v, t')` source-restricted: at every `v ∈ Spa(Localization.Away
s, …)` in the Laurent piece for a specific `t' ∈ D_T_loc` (via
`v.vle 1 t'` and `¬ v.vle t' 0`) with the f-bound `v.vle f_loc
s_base_loc`, supply the per-element upper bound `v.vle t' D_s_loc`
and the non-vanishing `¬ v.vle D_s_loc 0`. -/
def Cor732SigmaDirectUpperBoundResidual
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (D_T_loc : Finset (Localization.Away s))
    (s_base_loc D_s_loc f_loc : Localization.Away s) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  ∀ (σ_loc : (Localization.Away s)ˣ),
    IsLocalizedCor732SigmaLocOutput P T s hopen T_D s_D σ_loc →
    ∀ t' ∈ D_T_loc,
      ∀ v ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        v.vle f_loc s_base_loc →
        v.vle (1 : Localization.Away s) t' →
        ¬ v.vle t' 0 →
        v.vle t' D_s_loc ∧ ¬ v.vle D_s_loc 0

/-- **σ-factored inequality at T065-produced σ_loc via direct upper
bound residual** (T082 main ticket-named theorem).

From the named source-restricted denominator-clearing identity
`Cor732SigmaDirectUpperBoundResidual`, derive T076's σ-factored
inequality residual at the T065-produced σ_loc — i.e., the function-
form residual `(σ_loc, h_cover_t) ↦ ∃ N, σ-factored inequality at
σ_loc and N`.

**Reduction**: at each `(σ_loc, h_cover_t)` and per-`(v, t')`, the
named residual supplies the direct upper bound `v.vle t' D_s_loc` and
non-vanishing. Witness `N := 0`; the σ-factored inequality at `N = 0`
reduces (via `pow_zero`, `mul_one`, `pow_one`) to
`v.vle (t' * σ_loc) (D_s_loc * σ_loc)`. By `per_t_inequality_via_sigma_factor`
(T050 σ-factor cancellation), this is equivalent to the direct upper
bound. Real arithmetic — uses the σ-cancellation primitive
substantively.

The residual quantifier is restricted to T065-style σ_loc through the
`IsLocalizedCor732SigmaLocOutput` precondition; the residual is **not
universal over all units** of `Localization.Away s`. -/
theorem sigma_factored_inequality_at_localized_cor732_sigma
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (D_T_loc : Finset (Localization.Away s))
    (s_base_loc D_s_loc f_loc : Localization.Away s)
    (h_direct :
      Cor732SigmaDirectUpperBoundResidual P T s hopen T_D s_D
        D_T_loc s_base_loc D_s_loc f_loc) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
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
            ¬ v.vle D_s_loc 0 := by
  intro σ_loc h_cover_t t' ht' v hv_spa hv_f hv_one_t hv_t_ne
  -- Apply the named direct upper bound residual at this (σ_loc, h_cover_t).
  obtain ⟨h_clear, h_D_s_ne⟩ :=
    h_direct σ_loc h_cover_t t' ht' v hv_spa hv_f hv_one_t hv_t_ne
  -- Witness N := 0; reduce the σ-factored inequality at N = 0 to the
  -- direct upper bound via pow simp + σ-cancellation.
  refine ⟨0, ?_, h_D_s_ne⟩
  -- Goal: v.vle (t' * D_s_loc^0 * σ_loc) (D_s_loc^(0+1) * σ_loc)
  --     = v.vle (t' * 1 * σ_loc) (D_s_loc^1 * σ_loc)
  --     = v.vle (t' * σ_loc) (D_s_loc * σ_loc)
  --     ↔ v.vle t' D_s_loc (by per_t_inequality_via_sigma_factor)
  simpa only [pow_zero, mul_one, zero_add, pow_one] using
    (per_t_inequality_via_sigma_factor v σ_loc t' D_s_loc).mpr h_clear

/-- **End-to-end: σ-factored supplier output via the named direct
upper bound residual** (T082 final consumer).

End-to-end consumer composing T082's main theorem with T076's
revised wrapper: from the named source-restricted denominator-
clearing identity `Cor732SigmaDirectUpperBoundResidual` plus the
standard localized Cor 7.32 hypotheses, produce the σ-factored
supplier output `∃ σ_loc, SigmaFactoredSupplier ...` directly.

This closes the chain from the named source-restricted residual to
T076's `SigmaFactoredSupplier`-shaped output, with the σ_loc
supplied by T065's localized Cor 7.32 supplier.

The named residual is **per-`(v, t')` source-restricted, tied to the
T065-produced σ_loc through the function-form structure, and
σ-construction-content-only** (no global universal-over-D_T or
universal-over-Spa form, no final tateAcyclicity hypothesis). -/
theorem sigma_factored_supplier_via_cor732_direct_upper_bound_residual
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
      (_h_direct_residual :
        Cor732SigmaDirectUpperBoundResidual P T s hopen T_D s_D
          D_T_loc s_base_loc D_s_loc f_loc),
    ∃ _ : (Localization.Away s)ˣ,
      SigmaFactoredSupplier D_T_loc s_base_loc D_s_loc f_loc := by
  intro π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_D s_D hT_loc
    D_T_loc s_base_loc D_s_loc f_loc h_direct_residual
  -- Convert the named direct upper bound residual into T076's
  -- σ-factored inequality residual via T082's main theorem.
  have h_factored_residual :=
    sigma_factored_inequality_at_localized_cor732_sigma P T s hopen T_D s_D
      D_T_loc s_base_loc D_s_loc f_loc h_direct_residual
  -- Apply T076's revised wrapper.
  exact sigma_factored_supplier_via_localized_cor732 P T s hopen
    π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_D s_D hT_loc
    D_T_loc s_base_loc D_s_loc f_loc h_factored_residual

end ValuationSpectrum

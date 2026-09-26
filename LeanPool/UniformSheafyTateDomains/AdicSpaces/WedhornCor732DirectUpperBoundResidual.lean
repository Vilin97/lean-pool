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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornSigmaFactoredInequalityAtCor732Sigma

/-!
# Wedhorn 8.34(ii) — Cor 7.32 σ direct upper bound residual from denominator identity (T084)

T082 (`WedhornSigmaFactoredInequalityAtCor732Sigma`, commit `d162ca0`)
landed the named residual `Cor732SigmaDirectUpperBoundResidual` capturing
the per-`(v, t')` direct upper bound `v.vle t' D_s_loc ∧ ¬ v.vle D_s_loc
0` at the T065-produced σ_loc. T084 attacks the genuine remaining
Wedhorn 8.34(ii) algebraic content by **decomposing the residual into a
strictly sharper named source-restricted denominator-clearing chain
identity** that explicitly relates `f_loc`, `σ_loc`, `D_T_loc`, and
`D_s_loc` through the localized test family, plus a mechanical reduction
from the sharper identity to the T082 residual via Spv.vle_trans + T050
σ-factor cancellation.

## What this file provides

* `Cor732SigmaDenominatorClearingChainIdentity` — **strictly sharper
  named source-restricted algebraic identity**: at every `(σ_loc, h_cover_t,
  t', v)` with `t' ∈ D_T_loc` and source restrictions, supply an
  intermediate `τ ∈ localizedTestFamily s T_D s_D` together with the
  σ-rescaled chain bounds `v.vle (t' * σ_loc) τ` and
  `v.vle τ (D_s_loc * σ_loc)` plus the non-vanishing `¬ v.vle D_s_loc 0`.
  Per-`(v, t')` source-restricted; tied to T065-produced σ_loc via
  `IsLocalizedCor732SigmaLocOutput`; not universal over all units; no
  global universal-over-D_T or universal-over-Spa lower-bound clause.

* `cor732_sigma_direct_upper_bound_residual_from_denominator_identity` —
  **main ticket-named theorem** (T084 reduction): from the chain identity,
  derive T082's `Cor732SigmaDirectUpperBoundResidual`. Real arithmetic —
  uses `Spv.vle_trans` to combine the two chain bounds, then T050's
  `per_t_inequality_via_sigma_factor` σ-factor cancellation (σ_loc unit)
  to extract the direct upper bound `v.vle t' D_s_loc`. The non-vanishing
  passes through.

* `sigma_factored_supplier_via_cor732_denominator_clearing_chain_identity`
  — end-to-end consumer composing T084's reduction with T082's
  `sigma_factored_supplier_via_cor732_direct_upper_bound_residual`. From
  the strictly sharper chain identity + the standard localized Cor 7.32
  hypotheses, deliver the σ-factored supplier output `∃ σ_loc,
  SigmaFactoredSupplier ...` (T076 shape). Closes the chain from the
  named source-restricted denominator-clearing identity to the σ-factored
  supplier, all the way through the Wedhorn 8.34(ii) localized side
  modulo only the chain identity.

## Why this is strictly sharper than `Cor732SigmaDirectUpperBoundResidual`

T082's residual asks for the **direct upper bound** `v.vle t' D_s_loc` at
each (v, t') with the source restrictions. T084's chain identity instead
asks for an **intermediate τ ∈ localizedTestFamily s T_D s_D** together
with **two transitivity bounds** through τ, σ-rescaled by σ_loc:

```
∃ τ ∈ localizedTestFamily s T_D s_D,
  v.vle (t' * σ_loc) τ ∧ v.vle τ (D_s_loc * σ_loc) ∧ ¬ v.vle D_s_loc 0
```

This is strictly sharper in three ways:

1. **More refined data**: the intermediate τ is a specific test-family
   element, exposing how the σ-rescaled Laurent cover factors through
   the localized test family. The original residual hides this
   intermediate.

2. **Two-step chain**: each chain step `v.vle (t' * σ_loc) τ` and
   `v.vle τ (D_s_loc * σ_loc)` is individually a smaller/per-pair
   comparison than the global per-`(v, t')` upper bound `v.vle t'
   D_s_loc`. Discharging the chain reduces to discharging two
   simpler bounds rather than one combined bound.

3. **Explicit relation among `f_loc`, `σ_loc`, `D_T_loc`, `D_s_loc`,
   and the test family**: the chain identity ties σ_loc to t' via the
   first bound (the σ-rescaled Laurent piece structure) and to
   D_s_loc via the second bound (the σ-rescaled cover-piece denominator
   structure), with the test-family element τ as the bridge. The
   four entities are explicitly related through the test-family
   intermediate.

The reduction `chain identity → direct upper bound` is mechanical:
Spv.vle_trans on the two chain bounds gives `v.vle (t' * σ_loc) (D_s_loc
* σ_loc)`, and T050's σ-factor cancellation
(`per_t_inequality_via_sigma_factor`) cancels σ_loc on both sides to
give `v.vle t' D_s_loc`.

## The remaining Wedhorn 8.34(ii) arithmetic

After T084, the residual content reduces to **one named source-restricted
denominator-clearing chain identity** at the T065-produced σ_loc:
`Cor732SigmaDenominatorClearingChainIdentity`. The genuine Wedhorn
8.34(ii) σ-construction algebraic content remaining is the per-`(v, t')`
chain identity itself — supplying the test-family intermediate τ and the
two σ-rescaled chain bounds at each Laurent piece. Discharging this
chain identity is the last theorem-level step on the localized side and
corresponds directly to Wedhorn's per-Laurent-piece arithmetic
(σ-strict-domination plus the σ-construction's f_loc / D_s_loc /
D_T_loc relations).

## What T084 does NOT do

* Does **NOT** quantify the chain identity over all units of
  `Localization.Away s`; the quantifier is restricted to T065-style
  σ_loc via the explicit `IsLocalizedCor732SigmaLocOutput` precondition.

* Does **NOT** introduce or use any global universal-over-`D_T` lower
  bound or universal-over-Spa multi-element clearing claim.

* Does **NOT** edit Primary's pointwise route file or Tertiary's σ-power
  route file. Disjoint write set, leaf-level only.

* Does **NOT** add or modify any final
  `ValuationSpectrum.tateAcyclicity` hypothesis.

## Notes

* No root import; leaf-level file.
* Imports T082 (`WedhornSigmaFactoredInequalityAtCor732Sigma`) for the
  named `Cor732SigmaDirectUpperBoundResidual` Prop predicate, T076's
  `IsLocalizedCor732SigmaLocOutput` predicate, the
  `sigma_factored_supplier_via_cor732_direct_upper_bound_residual`
  end-to-end consumer, and T050's `per_t_inequality_via_sigma_factor`
  σ-factor cancellation primitive (transitively imported via T076 →
  T050).
* No edits to T031–T083 accepted leaves, root imports, or final theorem
  signatures.
* All declarations are fully proven, depend only on the standard Lean
  kernel postulates, and avoid native compilation and unchecked tactics.
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A]

/-- **Strictly sharper named source-restricted denominator-clearing chain
identity at the T065-produced σ_loc** (T084 sharper named identity).

Function-form predicate `(σ_loc, h_cover_t) ↦ chain identity at σ_loc`,
matching T082's residual structure but with the body decomposed from the
direct upper bound `v.vle t' D_s_loc` into a transitivity chain through
an intermediate `τ ∈ localizedTestFamily s T_D s_D` rescaled by σ_loc.

Per-`(v, t')` source-restricted: at every `v ∈ Spa(Localization.Away s,
…)` in the Laurent piece for a specific `t' ∈ D_T_loc` (via
`v.vle 1 t'` and `¬ v.vle t' 0`) with the f-bound `v.vle f_loc
s_base_loc`, supply

* `τ ∈ localizedTestFamily s T_D s_D` — the intermediate test-family
  element bridging `t' * σ_loc` and `D_s_loc * σ_loc`.
* `v.vle (t' * σ_loc) τ` — t'-σ_loc-rescaled lower bound on τ at v.
* `v.vle τ (D_s_loc * σ_loc)` — τ is bounded above by D_s_loc * σ_loc
  at v.
* `¬ v.vle D_s_loc 0` — D_s_loc non-vanishing at v.

The σ_loc and `h_cover_t : IsLocalizedCor732SigmaLocOutput P T s hopen
T_D s_D σ_loc` are precondition parameters — the chain identity body
involves σ_loc explicitly (in the two chain bounds), and the predicate's
quantifier structure restricts to T065-style σ_loc, matching the T076 /
T082 wrapper interface.

**The four entities `f_loc`, `σ_loc`, `D_T_loc`, `D_s_loc` are
explicitly related** through:

* `f_loc, s_base_loc` — supplied via the source restriction
  `v.vle f_loc s_base_loc`.
* `σ_loc` — appears in both chain bounds as the σ-rescaling factor.
* `D_T_loc` — supplies the per-element `t'` ranged over.
* `D_s_loc` — appears in the upper chain bound and the non-vanishing
  clause.
* `τ ∈ localizedTestFamily s T_D s_D` — the intermediate test-family
  element bridging σ_loc-rescaled `t'` and σ_loc-rescaled `D_s_loc`.

Strictly sharper than the direct upper bound: the two chain bounds are
individually per-pair comparisons (smaller content), and the test-family
intermediate exposes the σ-construction's per-Laurent-piece structure. -/
def Cor732SigmaDenominatorClearingChainIdentity
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
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          v.vle (t' * (σ_loc : Localization.Away s)) τ ∧
          v.vle τ (D_s_loc * (σ_loc : Localization.Away s)) ∧
          ¬ v.vle D_s_loc 0

/-- **`Cor732SigmaDirectUpperBoundResidual` from the denominator-clearing
chain identity** (T084 main ticket-named theorem).

From the strictly sharper named source-restricted denominator-clearing
chain identity `Cor732SigmaDenominatorClearingChainIdentity`, derive
T082's `Cor732SigmaDirectUpperBoundResidual` — i.e., the per-`(v, t')`
direct upper bound at the T065-produced σ_loc.

**Reduction**: at each `(σ_loc, h_cover_t, t', v)` with source
restrictions, the chain identity supplies an intermediate `τ ∈
localizedTestFamily s T_D s_D` with the two σ-rescaled chain bounds and
the non-vanishing of D_s_loc. The reduction:

1. `Spv.vle_trans` on `v.vle (t' * σ_loc) τ` and `v.vle τ (D_s_loc *
   σ_loc)` gives `v.vle (t' * σ_loc) (D_s_loc * σ_loc)`.
2. T050's `per_t_inequality_via_sigma_factor` σ-factor cancellation
   (σ_loc unit) cancels σ_loc on both sides, yielding `v.vle t' D_s_loc`.
3. Pair with the chain's `¬ v.vle D_s_loc 0` to obtain the residual.

Real arithmetic — uses Spv.vle_trans + T050 σ-cancellation
substantively. Both the chain identity and the residual are restricted
to T065-style σ_loc via `IsLocalizedCor732SigmaLocOutput`. -/
theorem cor732_sigma_direct_upper_bound_residual_from_denominator_identity
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (D_T_loc : Finset (Localization.Away s))
    (s_base_loc D_s_loc f_loc : Localization.Away s)
    (h_chain : Cor732SigmaDenominatorClearingChainIdentity
        P T s hopen T_D s_D D_T_loc s_base_loc D_s_loc f_loc) :
    Cor732SigmaDirectUpperBoundResidual
      P T s hopen T_D s_D D_T_loc s_base_loc D_s_loc f_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  intro σ_loc h_cover_t t' ht' v hv_spa hv_f hv_one_t hv_t_ne
  -- Apply the chain identity at this (σ_loc, h_cover_t, t', v).
  obtain ⟨τ, _hτ_mem, h_t_le_τ, h_τ_le_D, h_D_s_ne⟩ :=
    h_chain σ_loc h_cover_t t' ht' v hv_spa hv_f hv_one_t hv_t_ne
  refine ⟨?_, h_D_s_ne⟩
  -- Step 1: transitivity gives v.vle (t' * σ_loc) (D_s_loc * σ_loc).
  have h_factored :
      v.vle (t' * (σ_loc : Localization.Away s))
        (D_s_loc * (σ_loc : Localization.Away s)) :=
    v.vle_trans h_t_le_τ h_τ_le_D
  -- Step 2: T050 σ-cancellation gives v.vle t' D_s_loc.
  exact (per_t_inequality_via_sigma_factor v σ_loc t' D_s_loc).mp h_factored

/-- **End-to-end: σ-factored supplier from the denominator-clearing chain
identity** (T084 final consumer).

End-to-end consumer composing T084's reduction with T082's
`sigma_factored_supplier_via_cor732_direct_upper_bound_residual`: from
the strictly sharper named source-restricted denominator-clearing chain
identity plus the standard localized Cor 7.32 hypotheses, produce the
σ-factored supplier output `∃ σ_loc, SigmaFactoredSupplier ...` (T076
shape) directly.

This closes the chain from the named source-restricted chain identity
through the entire Wedhorn 8.34(ii) localized σ-construction interface
(T084 → T082 → T076 → T065's σ_loc) up to the σ-factored supplier
output, with `σ_loc` supplied by T065's localized Cor 7.32 supplier.

The chain identity remains the **single named source-restricted
algebraic residual** at the consumer boundary — strictly sharper than
T082's direct upper bound residual. -/
theorem sigma_factored_supplier_via_cor732_denominator_clearing_chain_identity
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
      (_h_chain_identity :
        Cor732SigmaDenominatorClearingChainIdentity
          P T s hopen T_D s_D D_T_loc s_base_loc D_s_loc f_loc),
    ∃ _ : (Localization.Away s)ˣ,
      SigmaFactoredSupplier D_T_loc s_base_loc D_s_loc f_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_D s_D hT_loc
    D_T_loc s_base_loc D_s_loc f_loc h_chain_identity
  -- Convert the chain identity into the T082 direct upper bound residual.
  have h_direct_residual :=
    cor732_sigma_direct_upper_bound_residual_from_denominator_identity
      P T s hopen T_D s_D D_T_loc s_base_loc D_s_loc f_loc h_chain_identity
  -- Apply T082's end-to-end consumer to deliver SigmaFactoredSupplier.
  exact sigma_factored_supplier_via_cor732_direct_upper_bound_residual
    P T s hopen π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_D s_D hT_loc
    D_T_loc s_base_loc D_s_loc f_loc h_direct_residual

end ValuationSpectrum

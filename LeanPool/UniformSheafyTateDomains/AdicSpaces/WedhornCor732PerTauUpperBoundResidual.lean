/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornCor732ChainIdentityFromLocalizedOutput
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornPointwiseClearingFromLocalizedCor732

/-!
# Wedhorn 8.34(ii) — Per-τ upper-bound residual from localized Cor 7.32 arithmetic (T087)

T085 (commit `8fb8984`) lands the chain identity producer
`cor732_sigma_denominator_clearing_chain_identity_from_localized_cor732_output`
together with the named per-`(v, τ)` upper-bound residual
`Cor732SigmaPerTauUpperBoundResidual`. T081 (commit on
`WedhornPointwiseClearingFromLocalizedCor732.lean`) lands the
**per-τ source-restricted pointwise clearing residual**
`LocalizedPerTauPointwiseClearingResidual` concluding
`v.vle (σ_loc⁻¹ * τ) D_s_loc` from the same source restrictions.

T087 closes the gap between these two residuals at the **theorem level**:
from a per-`σ_loc` T081 pointwise clearing residual (parameterised by
`σ_loc` satisfying `IsLocalizedCor732SigmaLocOutput`), produce T085's
`Cor732SigmaPerTauUpperBoundResidual` directly via σ-cancellation +
non-vanishing transport.

## What this file provides

* `cor732_sigma_per_tau_upper_bound_residual_from_localized_cor732_arithmetic`
  — main theorem-level bridge: from a per-`σ_loc` T081 pointwise
  clearing residual (under `IsLocalizedCor732SigmaLocOutput`), derive
  T085's `Cor732SigmaPerTauUpperBoundResidual`. Substantively consumes
  T081's per-τ pointwise clearing at each per-`(σ_loc, τ, v)` instance.

* `sigma_factored_supplier_via_per_tau_pointwise_clearing` — end-to-end
  consumer composing the bridge with T085's
  `sigma_factored_supplier_via_cor732_image_decomposition_and_per_tau_residual`
  to deliver the σ-factored supplier output `∃ σ_loc,
  SigmaFactoredSupplier ...` from the T081 per-τ pointwise clearing
  residual + the σ-image decomposition + standard localized Cor 7.32
  hypotheses.

## Bridge structure

T081's per-τ pointwise clearing residual at the chosen `σ_loc` produces

```
v.vle (σ_loc⁻¹ * τ) D_s_loc
```

under the source restrictions `v.vle f_loc s_base_loc`,
`v.vle 1 (σ_loc⁻¹ * τ)`, `¬ v.vle (σ_loc⁻¹ * τ) 0`. The bridge
delivers T085's residual `v.vle τ (D_s_loc * σ_loc) ∧ ¬ v.vle D_s_loc 0`
as follows:

* **First conjunct** `v.vle τ (D_s_loc * σ_loc)`: by T050's
  `per_t_inequality_via_sigma_factor.mpr` (right-multiply both sides by
  `σ_loc`), the bound transports to
  `v.vle ((σ_loc⁻¹ * τ) * σ_loc) (D_s_loc * σ_loc)`. Rewriting the LHS
  by T085's algebraic primitive `cor732_sigma_image_mul_unit_eq` then
  collapses `(σ_loc⁻¹ * τ) * σ_loc = τ`.

* **Second conjunct** `¬ v.vle D_s_loc 0`: contrapositive transitivity
  via `Spv.vle_trans` — if `v.vle D_s_loc 0`, the T081 conclusion
  `v.vle (σ_loc⁻¹ * τ) D_s_loc` chains to
  `v.vle (σ_loc⁻¹ * τ) 0`, contradicting the source restriction
  `¬ v.vle (σ_loc⁻¹ * τ) 0`.

Both steps are per-`(v, τ)` source-restricted closed-form valuation
arithmetic; no all-units quantifier, no universal-over-D_T or
universal-Spa claims, no global lower bound.

## Notes

* No root import; leaf-level only.
* Imports T085 (`WedhornCor732ChainIdentityFromLocalizedOutput`) for
  the target predicate `Cor732SigmaPerTauUpperBoundResidual`,
  `cor732_sigma_image_mul_unit_eq`, the chain producer
  `cor732_sigma_denominator_clearing_chain_identity_from_localized_cor732_output`,
  and the σ-factored supplier consumer
  `sigma_factored_supplier_via_cor732_image_decomposition_and_per_tau_residual`.
* Imports T081 (`WedhornPointwiseClearingFromLocalizedCor732`) for the
  hypothesis predicate `LocalizedPerTauPointwiseClearingResidual`.
* Both transitively bring in T050's `per_t_inequality_via_sigma_factor`
  and T076's `IsLocalizedCor732SigmaLocOutput`.
* No edits to T031–T086 accepted leaves, root imports, or final
  `tateAcyclicity` theorem signatures.
* No revival of T001 / Jacobson / Zavyalov / Cor 8.32 / faithful-flatness
  / bivariate-overlap / σ-power-decay / M-power-decay content.
* All declarations are fully proven, depend only on the standard Lean
  kernel postulates, and avoid native compilation and unchecked tactics.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

omit [PlusSubring A] in
/-- **Per-τ upper-bound residual from per-τ pointwise clearing residual**
(T087 main theorem-level bridge).

From a per-`σ_loc` T081 pointwise clearing residual (parameterised by
`σ_loc` satisfying `IsLocalizedCor732SigmaLocOutput`), produce T085's
`Cor732SigmaPerTauUpperBoundResidual` at the same `(P, T, s, hopen,
T_D, s_D, s_base_loc, D_s_loc, f_loc)`.

**Proof structure**:

1. Apply T081's per-τ pointwise clearing residual at `(σ_loc, τ, v)`
   to obtain `h_clear : v.vle (σ_loc⁻¹ * τ) D_s_loc` from the source
   restrictions.

2. **First conjunct** `v.vle τ (D_s_loc * σ_loc)`: by T050's
   `per_t_inequality_via_sigma_factor.mpr`, σ-multiply both sides to
   `v.vle ((σ_loc⁻¹ * τ) * σ_loc) (D_s_loc * σ_loc)`. Rewrite the LHS
   via T085's `cor732_sigma_image_mul_unit_eq` to collapse to τ.

3. **Second conjunct** `¬ v.vle D_s_loc 0`: contrapositive transitivity
   via `Spv.vle_trans` applied to `h_clear` and a hypothetical
   `v.vle D_s_loc 0` would yield `v.vle (σ_loc⁻¹ * τ) 0`, contradicting
   the source restriction.

Substantively consumes T081's per-τ pointwise clearing residual at
each per-`(σ_loc, τ, v)` instance — a real σ-cancellation +
non-vanishing transport, not a pass-through. -/
theorem cor732_sigma_per_tau_upper_bound_residual_from_localized_cor732_arithmetic
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (s_base_loc D_s_loc f_loc : Localization.Away s)
    (h_pointwise :
      ∀ (σ_loc : (Localization.Away s)ˣ),
        IsLocalizedCor732SigmaLocOutput P T s hopen T_D s_D σ_loc →
        LocalizedPerTauPointwiseClearingResidual
          P T s hopen T_D s_D σ_loc s_base_loc D_s_loc f_loc) :
    Cor732SigmaPerTauUpperBoundResidual
      P T s hopen T_D s_D s_base_loc D_s_loc f_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  intro σ_loc h_cover_t τ hτ_mem v hv_spa hv_f hv_one_t hv_t_ne
  -- Step 1: apply T081's per-τ pointwise clearing residual.
  have h_clear :
      v.vle (((σ_loc⁻¹ : (Localization.Away s)ˣ) :
          Localization.Away s) * τ) D_s_loc :=
    h_pointwise σ_loc h_cover_t τ hτ_mem v hv_spa hv_f hv_one_t hv_t_ne
  refine ⟨?_, ?_⟩
  · -- Step 2: σ-cancellation + image identity for the first conjunct.
    have h_factored :
        v.vle ((((σ_loc⁻¹ : (Localization.Away s)ˣ) :
            Localization.Away s) * τ) * (σ_loc : Localization.Away s))
          (D_s_loc * (σ_loc : Localization.Away s)) :=
      (per_t_inequality_via_sigma_factor v σ_loc
        (((σ_loc⁻¹ : (Localization.Away s)ˣ) :
          Localization.Away s) * τ) D_s_loc).mpr h_clear
    rwa [cor732_sigma_image_mul_unit_eq σ_loc τ] at h_factored
  · -- Step 3: non-vanishing via vle_trans contrapositive.
    intro h_D_zero
    exact hv_t_ne (v.vle_trans h_clear h_D_zero)

omit [PlusSubring A] in
/-- **End-to-end: σ-factored supplier from T081 per-τ pointwise clearing**
(T087 final consumer).

Composes the T087 bridge with T085's
`sigma_factored_supplier_via_cor732_image_decomposition_and_per_tau_residual`
to deliver the σ-factored supplier output `∃ σ_loc,
SigmaFactoredSupplier ...` directly from:

* The σ-image decomposition hypothesis on `D_T_loc` (per-`(σ_loc, t')`).
* T081's per-τ source-restricted pointwise clearing residual (per
  `σ_loc` satisfying `IsLocalizedCor732SigmaLocOutput`).
* The standard localized Cor 7.32 hypotheses.

Closes the chain T081 (per-τ pointwise clearing residual) → T087
(per-τ upper-bound residual) → T085 (chain identity) → T084 (direct
upper bound) → T082 → T076 → T065 → σ-factored supplier. Single named
source-restricted residual at the consumer boundary:
`LocalizedPerTauPointwiseClearingResidual` (T081). -/
theorem sigma_factored_supplier_via_per_tau_pointwise_clearing
    [DecidableEq A]
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
      (_h_D_T_loc_image_per_t :
        ∀ (σ_loc : (Localization.Away s)ˣ),
          IsLocalizedCor732SigmaLocOutput P T s hopen T_D s_D σ_loc →
          ∀ t' ∈ D_T_loc,
            ∃ τ ∈ localizedTestFamily s T_D s_D,
              t' = ((σ_loc⁻¹ : (Localization.Away s)ˣ) :
                Localization.Away s) * τ)
      (_h_pointwise :
        ∀ (σ_loc : (Localization.Away s)ˣ),
          IsLocalizedCor732SigmaLocOutput P T s hopen T_D s_D σ_loc →
          LocalizedPerTauPointwiseClearingResidual
            P T s hopen T_D s_D σ_loc s_base_loc D_s_loc f_loc),
    ∃ _ : (Localization.Away s)ˣ,
      SigmaFactoredSupplier D_T_loc s_base_loc D_s_loc f_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_D s_D hT_loc
    D_T_loc s_base_loc D_s_loc f_loc h_D_T_loc_image_per_t h_pointwise
  -- Bridge T081's per-τ pointwise clearing residual to T085's per-τ
  -- upper-bound residual via T087.
  have h_per_tau :
      Cor732SigmaPerTauUpperBoundResidual
        P T s hopen T_D s_D s_base_loc D_s_loc f_loc :=
    cor732_sigma_per_tau_upper_bound_residual_from_localized_cor732_arithmetic
      P T s hopen T_D s_D s_base_loc D_s_loc f_loc h_pointwise
  -- Apply T085's end-to-end consumer with the T087-derived per-τ residual.
  exact sigma_factored_supplier_via_cor732_image_decomposition_and_per_tau_residual
    P T s hopen π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_D s_D hT_loc
    D_T_loc s_base_loc D_s_loc f_loc h_D_T_loc_image_per_t h_per_tau

end ValuationSpectrum

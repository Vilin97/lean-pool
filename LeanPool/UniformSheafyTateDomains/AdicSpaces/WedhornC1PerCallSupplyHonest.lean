/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornStrengthenedC1
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornMPowerStructuralDataHonest

/-!
# Wedhorn 8.34(ii) — Honest top-level C1 supplier interface

Honest counterpart to `Wedhorn834C1SupplierLocalInterface` (commit
upstream): mirrors the predicate-bundling shape but replaces
**component 5** — the old M-power-decay residual carrying the
`T_D` non-vanishing scaffolding — with the honest σ-factored
supplier `WedhornMPowerStructuralDataHonest`.

## Audit-driven motivation

The previous bundled component 5 in `WedhornC1PerCallSupply`
required, at every `(w, τ)`, both:

1. The Wedhorn structural inequality
   `w.vle (algebraMap s) (algebraMap s_D * σ_loc * ∏ erase t')`,
2. `T_D` non-vanishing `∀ t'' ∈ T_D.image algebraMap, ¬ w.vle t'' 0`,
3. `s_D` non-vanishing.

Conjunct (2) was a scaffolding artifact of the multi-element
product cancellation `mul_vle_mul_iff_left` over `∏ erase t'`,
not part of Wedhorn 8.34(ii)'s natural per-`t'` argument
(audit accepted at commit `44c2be3`).

The honest supplier `WedhornMPowerStructuralDataHonest` (commit
`44c2be3`) is the **single-conjunct σ-factored per-`t'` inequality**:

```
∀ t' ∈ T_D.image algebraMap,
  w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)
```

Equivalent under σ-cancellation to `w.vle t' (algebraMap s_D)`. Both
the per-`t'` conclusion and `s_D` non-vanishing for both branches are
auto-derived inside `h_M_power_decay_from_honest_structural_data`. No
`T_D` non-vanishing appears in the public interface.

## What this file provides

* `WedhornC1PerCallSupplyHonest` — honest per-call supply predicate
  (six components, mirror of `WedhornC1PerCallSupply` but with
  component 5 = `WedhornMPowerStructuralDataHonest`).
* `C1SupplierStrong_local_via_honest_residuals` — caller theorem
  composing `rationalOpen_subset_base_via_honest_structural_data` for
  clause 2 of the C1 conclusion. Sorry-free, axiom-clean.

## Notes

* No root import; leaf-level.
* No edits to `Wedhorn834C1SupplierLocalInterface.lean` (the legacy
  `T_D`-non-vanishing-bearing wrapper) or to Tertiary's value-group
  file. The legacy interface remains in place for callers that
  already constructed the old shape; new callers should target the
  honest one.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson /
  T001 / faithful-flatness / Zavyalov / bivariate-overlap content.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Honest per-call Wedhorn 8.34(ii) supply predicate**.

Mirrors `WedhornC1PerCallSupply` (legacy) but replaces component 5
with the honest σ-factored supplier `WedhornMPowerStructuralDataHonest`.
No `T_D` non-vanishing appears: component 5 is the genuine Wedhorn
8.34(ii) per-`t'` content, and `s_D` non-vanishing is auto-derived
downstream. -/
def WedhornC1PerCallSupplyHonest
    [DecidableEq A]
    (P : PairOfDefinition A)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (D : RationalLocData A) (v : Spv A) : Prop :=
  letI : TopologicalSpace (Localization.Away C.base.s) :=
    locTopology P C.base.T C.base.s hopen_base
  letI : PlusSubring (Localization.Away C.base.s) :=
    localizationLocSubringPlusSubring P C.base.T C.base.s
  letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
  ∃ (σ_loc : (Localization.Away C.base.s)ˣ) (f : A),
    -- (1)–(3) Denominator-clearing identity.
    (algebraMap A (Localization.Away C.base.s) f =
      (σ_loc : Localization.Away C.base.s) *
        (∏ τ ∈ D.T.image (algebraMap A (Localization.Away C.base.s)), τ)) ∧
    -- (4) σ-strict-domination on local Spa (Cor 7.32 output;
    -- consumes Tertiary's MulArchimedean transfer R₂ via
    -- `exists_dominating_unit_in_localization_via_global_pi`).
    (∀ w ∈ Spa (Localization.Away C.base.s) (Localization.Away C.base.s)⁺,
        ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
          w.vle (σ_loc : Localization.Away C.base.s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away C.base.s)) ∧
    -- (5) HONEST σ-factored per-`t'` supplier R₁'.
    WedhornMPowerStructuralDataHonest P C.base.T C.base.s hopen_base
      D.T D.s σ_loc ∧
    -- (6a) Clause 1 of C1: v ∈ R(insert f C.base.T, C.base.s).
    v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
    -- (6b) Clause 3 of C1: ¬ v.vle f 0.
    ¬ v.vle f 0

/-- **Honest top-level C1 supplier interface theorem**.

Identical caller signature to `C1SupplierStrong_local_via_named_residuals`
modulo the per-call supply predicate: `WedhornC1PerCallSupplyHonest`
replaces `WedhornC1PerCallSupply`. Internally feeds the honest
σ-factored supplier through
`rationalOpen_subset_base_via_honest_structural_data` for clause 2 of
the C1 conclusion; clauses 1 and 3 read directly from the predicate.

No `T_D` non-vanishing input is required at any point. -/
theorem C1SupplierStrong_local_via_honest_residuals
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (h_per_call_supply :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        WedhornC1PerCallSupplyHonest P C hopen_base D v) :
    C1SupplierStrong_local C := by
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨σ_loc, f, h_alg, h_dom, h_honest, hv_in_plus, hvf_nz⟩ :=
    h_per_call_supply D hD v hv t ht hvt hvD_s
  refine ⟨f, hv_in_plus, ?_, hvf_nz⟩
  exact rationalOpen_subset_base_via_honest_structural_data
    P C.base.T C.base.s hopen_base hA₀_le C.base.T D.T D.s
    (Finset.Subset.refl _) f σ_loc h_alg h_dom h_honest

end ValuationSpectrum

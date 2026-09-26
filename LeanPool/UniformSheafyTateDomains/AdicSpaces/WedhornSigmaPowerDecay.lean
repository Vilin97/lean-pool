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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornFactorExtractionPowerDecay
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Cor732

/-!
# Wedhorn σ-power-decay bridge

Reusable intermediates on the σ-power-decay lane of Wedhorn 8.34(ii).
After sanity-checking the originally-targeted residual statement
against the formalized APIs in `Cor732.lean` (where σ comes from
`exists_dominating_unit` as `s = π^(N+1)`) and `SpaCompact.lean`, the
**originally-targeted shape** `∀ w ∈ Spa A A⁺, w.vle C_base_s
((σ : A) * D_s ^ (N + 1))` is **not directly** Cor 7.32-derivable: the
Cor 7.32 σ-domination is `w(σ) ≤ w(τ_w)` (σ small from above), whereas
the σ-power-decay would require `w(σ) * w(D_s)^(N+1) ≥ w(C_base_s)`
(σ large from below). The actual Wedhorn 8.34(ii) subset-direction
chain uses Cor 7.32-σ-domination at each `w` directly via per-`w`
branch case-split (which `τ_w ∈ T_test` wins), not the σ-power-decay
shape.

Rather than force a false statement, this file lands the
**strongest honest intermediates** on the σ-power-decay lane and
documents the corrected residual.

## What this file provides

* `pointwise_pow_decay_at` — at a single Spa-point `v` with
  `τ : A, ¬ v.vle τ 0`, ∃ N : ℕ with `v.vle (π^N) τ`. Direct wrapper
  for `Cor732.exists_mem_basicOpen_pow_of_tn`. Gives a per-`v`
  topologically-nilpotent power decay.

* `exists_dominating_unit_strict_pair` — repackaging of
  `Cor732.exists_dominating_unit` exposing the strict-domination pair
  `v.vle (σ : A) τ ∧ ¬ v.vle τ (σ : A)` as the per-Spa-point output.
  This is the actual Cor 7.32 supplier shape consumed by the Wedhorn
  8.34(ii) subset-direction chain.

## What this file does NOT provide / corrected residual

The σ-power-decay `∀ w ∈ Spa A A⁺, w.vle C_base_s ((σ : A) * D_s ^
(N + 1))` is **not directly** Cor 7.32-derivable. The next ticket on
this lane should not chase this shape; instead, re-design the
subset-direction transfer to consume Cor 7.32-σ-domination directly
via per-`w` branch case-split. The exact target signature for the
re-designed bridge:

```
theorem subset_inequality_via_cor732_branch_at
    {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A] [IsHuberRing A] [IsTateRing A]
    [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A,
      letI : ValuativeRel A := v.toValuativeRel
      MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (T_D : Finset A) (D_s C_base_s : A) (N : ℕ)
    (hT_test : ∀ v ∈ Spa A A⁺, ∃ t ∈ insert D_s T_D, ¬ v.vle t 0)
    {σ : Aˣ}
    (hσ_dom : ∀ v ∈ Spa A A⁺, ∃ τ ∈ insert D_s T_D,
      v.vle (σ : A) τ ∧ ¬ v.vle τ (σ : A))
    {f : A} (hf : f = (σ : A) * (T_D.prod id) * D_s ^ N)
    {w : Spv A} (hw : w ∈ Spa A A⁺) (hw_f : w.vle f C_base_s) :
    (∀ t' ∈ T_D, w.vle t' D_s) ∧ ¬ w.vle D_s 0
```

This is the same Wedhorn 8.34(ii) target as `vle_of_dominating_unit_multi`
(`WedhornStandardCoverRefinement.lean:301`) but expressed in terms of
the API actually available; its proof requires a per-`w` case
analysis on which `τ ∈ insert D_s T_D` wins σ-domination, plus the
strict-inequality structure to force per-`t'` bounds. This is the
genuinely-new Wedhorn content that does not reduce to Cor 7.32 +
factor extraction alone.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness content.
* Does not edit Tertiary's `WedhornLocalizationLiftContinuity.lean`,
  `WedhornValuationLocalizationLift.lean`, `WedhornC1StrongSupplierCore.lean`,
  Spa/rationalOpen lift wrappers, or any in-flight file.
* Imports `WedhornFactorExtractionPowerDecay` (committed `c5392a5`) and
  `Cor732` (for `exists_mem_basicOpen_pow_of_tn` and
  `exists_dominating_unit`).
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

omit [IsTopologicalRing A] in
/-- **Pointwise topologically-nilpotent power decay**. At a Spa-point
`v` with `τ : A` not vanishing at `v`, every topologically-nilpotent
`π : A` has some power `π^N` whose `v`-valuation is at most `v(τ)`.

Direct wrapper for `Cor732.exists_mem_basicOpen_pow_of_tn`, exposing
the per-`v` decay `v.vle (π^N) τ` as the conclusion. -/
theorem pointwise_pow_decay_at
    {v : Spv A} (hv : v ∈ Spa A A⁺)
    {π : A} (hπ_tn : IsTopologicallyNilpotent π)
    (hArch : letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    {τ : A} (hτ_ne : ¬ v.vle τ 0) :
    ∃ N : ℕ, v.vle (π ^ N) τ :=
  (exists_mem_basicOpen_pow_of_tn hv hπ_tn hArch hτ_ne).imp fun _ h => h.1

omit [IsTopologicalRing A] in
/-- **Cor 7.32 σ-strict-domination supplier**, repackaged for the
Wedhorn 8.34(ii) subset-direction consumer. Direct wrapper for
`Cor732.exists_dominating_unit`. -/
theorem exists_dominating_unit_strict_pair
    [IsLinearTopology A A] [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A,
      letI : ValuativeRel A := v.toValuativeRel
      MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (T : Finset A)
    (hT : ∀ v ∈ Spa A A⁺, ∃ t ∈ T, ¬ v.vle t 0) :
    ∃ σ : Aˣ, ∀ v ∈ Spa A A⁺, ∃ t ∈ T,
      v.vle (σ : A) t ∧ ¬ v.vle t (σ : A) :=
  exists_dominating_unit P hA₀_le π hI hπ_tn hπ_unit hArch T hT

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] in
/-- **Per-`w` Wedhorn 8.34(ii) subset inequality with `C_base_s`
non-vanishing**.

Strict improvement over
`subset_inequality_of_multi_chain_with_decay_at`
(`WedhornFactorExtractionPowerDecay.lean`): replaces the
denominator-non-vanishing hypothesis `¬ w.vle D_s 0` with the more
natural numerator-non-vanishing hypothesis `¬ w.vle C_base_s 0`. The
former is auto-derived from the latter by chaining the σ-power-decay
hypothesis with `D_s ↦ 0` propagation through
`(σ : A) * D_s ^ (N + 1)`.

`C_base_s` non-vanishing is **naturally available** at every `w` in
the cover's plus-piece `R(insert f T_base, C_base_s)`: the rational
open membership condition includes `¬ w.vle C_base_s 0`. By contrast,
`D_s` non-vanishing is the conclusion we are trying to derive at
this `w`; supplying it as a hypothesis is awkward in the natural
Wedhorn 8.34(ii) workflow. This lemma removes that awkwardness.

## Proof strategy

* Auto-derivation of `¬ w.vle D_s 0`: assume `w.vle D_s 0`. Then
  `w.vle ((σ : A) * D_s ^ (N + 1)) 0` (push the zero through
  `(σ : A) * D_s ^ N` left-multiplication and `pow_succ`). Combined
  with the σ-power-decay hypothesis `w.vle C_base_s ((σ : A) * D_s ^ (N + 1))`
  by `vle_trans`: `w.vle C_base_s 0`, contradicting `h_C_base_s_ne`.
* Per-`t'` bound + denominator non-vanishing combined: delegate to
  the existing consumer `subset_inequality_of_multi_chain_with_decay_at`.

## Why this is the right per-`w` branch shape

Per the recorded warning at the head of this file, the σ-power-decay
shape `w.vle C_base_s ((σ : A) * D_s ^ (N + 1))` is **not directly**
Cor 7.32-derivable; the actual Wedhorn 8.34(ii) subset-direction
chain derives this per-`w` via Wedhorn's specific σ-as-π-power
choice plus Spa-quasi-compactness M-choice. This lemma packages the
**consumer** at `w` once that σ-power-decay datum is supplied: the
remaining residual is exactly the per-`w` σ-power-decay
`h_C_decay`, the genuinely-new Wedhorn 8.34(ii) Step 2 content
flagged at `WedhornFactorExtractionPowerDecay.lean:144-171`. -/
theorem subset_inequality_via_sigma_decay_C_base_s_ne_at
    (w : Spv A) {σ : Aˣ} {T_D : Finset A} {D_s C_base_s : A} (N : ℕ)
    {f : A} (hf : f = (σ : A) * (T_D.prod id) * D_s ^ N)
    (hw_f : w.vle f C_base_s)
    (h_C_base_s_ne : ¬ w.vle C_base_s 0)
    (h_T_D_lower : ∀ t'' ∈ T_D, w.vle (1 : A) t'')
    (h_C_decay : w.vle C_base_s ((σ : A) * D_s ^ (N + 1))) :
    (∀ t' ∈ T_D, w.vle t' D_s) ∧ ¬ w.vle D_s 0 := by
  letI : ValuativeRel A := w.toValuativeRel
  have h_D_s_ne : ¬ w.vle D_s 0 := by
    intro h_D_s_zero
    apply h_C_base_s_ne
    have h_step :
        w.vle ((σ : A) * D_s ^ N * D_s) ((σ : A) * D_s ^ N * 0) :=
      ValuativeRel.mul_vle_mul_right h_D_s_zero ((σ : A) * D_s ^ N)
    rw [mul_zero, mul_assoc, ← pow_succ] at h_step
    exact w.vle_trans h_C_decay h_step
  exact subset_inequality_of_multi_chain_with_decay_at w N hf
    h_D_s_ne hw_f h_T_D_lower h_C_decay

end ValuationSpectrum

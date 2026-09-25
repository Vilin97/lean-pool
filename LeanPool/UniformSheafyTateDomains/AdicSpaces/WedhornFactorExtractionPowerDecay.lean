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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornMultiBranchSubsetInequality
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornMultiDominatingUnit

/-!
# Wedhorn factor-extraction discharger

Bridges from the actual Wedhorn 8.34(ii) candidate data
`f := (σ : A) * (T_D.prod id) * D_s ^ N` to the per-`t'` chain
hypothesis consumed by
`WedhornMultiBranchSubsetInequality.subset_inequality_via_per_t_sigma_decay`.

## What this file provides

* `per_t_chain_of_multi_chain_at` — **factor extraction**: from
  `w.vle f C_base_s` for the multi-element candidate
  `f := (σ : A) * (T_D.prod id) * D_s ^ N`, plus the algebraically
  honest hypothesis that each `t'' ∈ T_D` has valuation at least 1 at
  `w` (`∀ t'' ∈ T_D, w.vle 1 t''`), derive the per-`t'` chain
  `∀ t' ∈ T_D, w.vle ((σ : A) * t' * D_s ^ N) C_base_s`.

* `subset_inequality_of_multi_chain_with_decay_at` — **combined
  consumer**: composes `per_t_chain_of_multi_chain_at` with
  `WedhornMultiBranchSubsetInequality.subset_inequality_via_per_t_sigma_decay`
  to produce the full subset-side conclusion
  `(∀ t' ∈ T_D, w.vle t' D_s) ∧ ¬ w.vle D_s 0` from the multi-element
  chain, the lower bound on `T_D`, the σ-power-decay
  `h_C_decay`, and `¬ w.vle D_s 0`.

## Honest hypothesis discussion

The factor-extraction premise `∀ t'' ∈ T_D, w.vle 1 t''` (each
`t''` has `w(t'') ≥ 1`) is the algebraically honest direction:
extracting a single factor `t'` from a product
`σ * (T_D.prod id) * D_s ^ N ≤ C_base_s` to obtain
`σ * t' * D_s ^ N ≤ C_base_s` requires the OTHER factors
`∏ T_D \ {t'}` to have valuation `≥ 1`. The opposite-direction bound
`∀ t'' ∈ T_D, w.vle t'' 1` (`T_D ⊆ A°` at `w`) does NOT suffice for this
extraction.

Whether `∀ t'' ∈ T_D, w.vle 1 t''` is achievable in the actual Wedhorn
8.34(ii) setup depends on the rational-data context: it is a
case-dependent input (typical when each `t' ∈ T_D` is a numerator that
the rational-open `R(T_D, D_s)` situates relative to `D_s`). It is
**not** automatic from `T_D ⊆ A°`. This file consumes it as an explicit
input.

## σ-power-decay residual

The σ-power-decay hypothesis `h_C_decay : w.vle C_base_s ((σ : A) *
D_s ^ (N + 1))` consumed by
`subset_inequality_of_multi_chain_with_decay_at` is the genuinely-new
Wedhorn content (Cor 7.32 + N-choice); this file does **not** derive
it. The exact residual statement is recorded at the bottom of the
file.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness content.
* Does not edit Tertiary's `WedhornLocalizationLiftContinuity.lean`,
  `WedhornValuationLocalizationLift.lean`,
  `WedhornC1StrongSupplierCore.lean`, or any in-flight file.
* Imports `WedhornMultiBranchSubsetInequality` (committed `3bb87eb`)
  and `WedhornMultiDominatingUnit` (for `Spv.vle_prod_of_pointwise`).
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-- **Factor extraction** for the Wedhorn 8.34(ii) multi-element
candidate. From `w.vle f C_base_s` for the candidate
`f := (σ : A) * (T_D.prod id) * D_s ^ N`, plus the lower-bound
hypothesis `∀ t'' ∈ T_D, w.vle 1 t''` (each `t''` has `w(t'') ≥ 1`),
derive the per-`t'` chain
`∀ t' ∈ T_D, w.vle ((σ : A) * t' * D_s ^ N) C_base_s`.

The proof factors `T_D.prod id = t' * (T_D.erase t').prod id` via
`Finset.mul_prod_erase`, lifts the per-`t''` lower bound to a product
lower bound `w.vle 1 ((T_D.erase t').prod id)` via
`Spv.vle_prod_of_pointwise`, and chains via transitivity. -/
theorem per_t_chain_of_multi_chain_at
    (w : Spv A) {σ : Aˣ} {T_D : Finset A} {D_s C_base_s : A} (N : ℕ)
    {f : A} (hf : f = (σ : A) * (T_D.prod id) * D_s ^ N)
    (h_w_f : w.vle f C_base_s)
    (h_T_D_lower_bound : ∀ t'' ∈ T_D, w.vle (1 : A) t'') :
    ∀ t' ∈ T_D, w.vle ((σ : A) * t' * D_s ^ N) C_base_s := by
  classical
  letI : ValuativeRel A := w.toValuativeRel
  intro t' ht'
  -- Product split via `Finset.mul_prod_erase`.
  have h_prod_split : T_D.prod id = t' * (T_D.erase t').prod id :=
    (Finset.mul_prod_erase T_D id ht').symm
  -- Lift per-`t''` lower bound to product lower bound on `T_D.erase t'`.
  have h_per_t : ∀ t'' ∈ T_D.erase t', w.vle ((fun _ : A ↦ (1 : A)) t'') (id t'') :=
    fun t'' ht'' ↦ h_T_D_lower_bound t'' (Finset.mem_of_mem_erase ht'')
  have h_others_lower : w.vle (1 : A) ((T_D.erase t').prod id) := by
    have h_pw := Spv.vle_prod_of_pointwise w (T_D.erase t') h_per_t
    rwa [Finset.prod_const_one] at h_pw
  -- Multiply both sides by `(σ : A) * t' * D_s ^ N` on the LEFT.
  have h_mul : w.vle ((σ : A) * t' * D_s ^ N * 1)
                ((σ : A) * t' * D_s ^ N * (T_D.erase t').prod id) :=
    ValuativeRel.mul_vle_mul_right h_others_lower ((σ : A) * t' * D_s ^ N)
  rw [mul_one] at h_mul
  -- Identify the RHS with `f`.
  have h_eq_f : (σ : A) * t' * D_s ^ N * (T_D.erase t').prod id = f := by
    rw [hf, h_prod_split]; ring
  rw [h_eq_f] at h_mul
  -- Chain through `h_w_f`.
  exact w.vle_trans h_mul h_w_f

/-- **Combined consumer**: composes `per_t_chain_of_multi_chain_at`
with
`WedhornMultiBranchSubsetInequality.subset_inequality_via_per_t_sigma_decay`
to produce the full multi-`t'` subset-side conclusion from the
multi-element candidate data plus the σ-power-decay hypothesis. -/
theorem subset_inequality_of_multi_chain_with_decay_at
    (w : Spv A) {σ : Aˣ} {T_D : Finset A} {D_s C_base_s : A} (N : ℕ)
    {f : A} (hf : f = (σ : A) * (T_D.prod id) * D_s ^ N)
    (h_D_s_ne : ¬ w.vle D_s 0)
    (h_w_f : w.vle f C_base_s)
    (h_T_D_lower_bound : ∀ t'' ∈ T_D, w.vle (1 : A) t'')
    (h_C_decay : w.vle C_base_s ((σ : A) * D_s ^ (N + 1))) :
    (∀ t' ∈ T_D, w.vle t' D_s) ∧ ¬ w.vle D_s 0 :=
  subset_inequality_via_per_t_sigma_decay w N h_D_s_ne
    (per_t_chain_of_multi_chain_at w N hf h_w_f h_T_D_lower_bound)
    h_C_decay

/-! ### Remaining residual: σ-power-decay derivation

The σ-power-decay hypothesis `h_C_decay : w.vle C_base_s ((σ : A) *
D_s ^ (N + 1))` consumed by
`subset_inequality_of_multi_chain_with_decay_at` is established in
Wedhorn 8.34(ii) by the choice of σ from Cor 7.32 plus the choice of
N to clear the denominator. The exact target signature for the
remaining content:

```
theorem sigma_power_decay_of_cor732
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
    (T_test : Finset A)
    (hT_test : ∀ v ∈ Spa A A⁺, ∃ t ∈ T_test, ¬ v.vle t 0)
    (D_s C_base_s : A) (hD_s_in_test : D_s ∈ T_test) :
    ∃ (σ : Aˣ) (N : ℕ),
      (∀ v ∈ Spa A A⁺, ∃ τ ∈ T_test,
        v.vle (σ : A) τ ∧ ¬ v.vle τ (σ : A)) ∧
      (∀ w ∈ Spa A A⁺,
        w.vle C_base_s ((σ : A) * D_s ^ (N + 1)))
```

The first conjunct is `Cor732.exists_dominating_unit` directly. The
second conjunct is the genuinely-new Wedhorn content: the existence of
an exponent `N` (depending on `σ`, `D_s`, `C_base_s`, `T_test`) such
that `C_base_s ≤ σ * D_s ^ (N + 1)` uniformly on `Spa`. This is
achievable via the topological nilpotency of `σ` (which is a Cor 7.32
σ-power, hence topologically nilpotent) plus `Spa`-quasi-compactness,
but is not yet formalized as a named theorem. -/

end ValuationSpectrum

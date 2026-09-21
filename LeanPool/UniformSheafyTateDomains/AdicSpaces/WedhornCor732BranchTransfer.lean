/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornMultiDominatingUnit
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornDominatingBranchInequality
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornSigmaPowerDecay

/-!
# Wedhorn Cor 7.32 branch-compatibility bridge

Honest packaging for the `hT_test_compat` hypothesis consumed by
`WedhornMultiDominatingUnit.rationalOpen_subset_via_strict_sigma_domination`.

## Audit

`WedhornMultiDominatingUnit.lean:148` provides the reducer that takes
σ-strict-domination plus a per-(τ,w) compatibility witness and produces
the rational-open subset inclusion. The `hT_test_compat` is per-(τ, w)
with conclusion `(∀ t' ∈ D.T, w.vle t' D.s) ∧ ¬ w.vle D.s 0`.

Direct algebraic discharge of `hT_test_compat` from σ-strict-domination
alone fails (cf. the audit at `WedhornMultiDominatingUnit.lean:234–304`):
σ-strict-domination by some `τ` at `w` yields per-`τ` information about
`w(σ)/w(τ)` but cannot single-handedly pin down per-`t'` ratios
`w(t')/w(D.s)` for arbitrary `t' ∈ D.T`. The earlier "canonical
T_test choice" docblock confirmed this fails.

## What this file provides

* `hT_test_compat_branch_D_s` — single-branch compatibility for the
  `τ = D.s` case. The non-degeneracy clause `¬ w.vle D.s 0` is
  **discharged automatically** via `not_vle_zero_of_strict_dominator`
  (the strict-domination σ < D.s implies D.s ≠ 0). The per-`t'`
  inequalities are taken as an explicit input (the Wedhorn-content
  residual at this branch).

* `hT_test_compat_of_per_branch_chain` — generic packaging that
  reduces `hT_test_compat` to two per-(τ, w) inputs: the per-`t'`
  chain and the `D.s ≠ 0` discharger. Both are explicit, neither is
  forced; this is honest packaging only.

* `rationalOpen_subset_via_per_branch_chain` — composed consumer that
  feeds `hT_test_compat_of_per_branch_chain` into
  `rationalOpen_subset_via_strict_sigma_domination` to obtain the
  rational-open subset inclusion.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness content.
* Does not edit Tertiary's wrapper/lift files, Primary's files, or
  any in-flight file.
* Uses existing helpers: `not_vle_zero_of_strict_dominator`
  (`WedhornMultiDominatingUnit.lean:189`),
  `rationalOpen_subset_via_strict_sigma_domination`
  (`WedhornMultiDominatingUnit.lean:148`).
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

/-- **Single-branch compatibility for `τ = D.s`**, taking the per-`t'`
chain explicitly.

The non-degeneracy half `¬ w.vle D.s 0` is **discharged automatically**
via `not_vle_zero_of_strict_dominator`: strict σ-domination of `D.s`
(i.e., `¬ w.vle D.s (σ : A)`) implies `¬ w.vle D.s 0`. Only the per-`t'`
inequalities `∀ t' ∈ D.T, w.vle t' D.s` need to be supplied, and those
are the genuine Wedhorn-content residual at this branch. -/
theorem hT_test_compat_branch_D_s
    [DecidableEq A] (C : RationalCoveringData A) (D : RationalLocData A)
    (σ : Aˣ)
    (h_per_t_chain : ∀ w ∈ Spa A A⁺,
      w.vle ((σ : A) * (∏ t ∈ D.T, t)) C.base.s →
      w.vle (σ : A) D.s ∧ ¬ w.vle D.s (σ : A) →
      ∀ t' ∈ D.T, w.vle t' D.s) :
    ∀ τ ∈ ({D.s} : Finset A), ∀ w ∈ Spa A A⁺,
      w.vle ((σ : A) * (∏ t ∈ D.T, t)) C.base.s →
      w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A) →
        (∀ t' ∈ D.T, w.vle t' D.s) ∧ ¬ w.vle D.s 0 := by
  intro τ hτ w hw_spa hw_f hστ
  rw [Finset.mem_singleton] at hτ
  subst hτ
  exact ⟨h_per_t_chain w hw_spa hw_f hστ, not_vle_zero_of_strict_dominator hστ.2⟩

/-- **Generic per-branch chain reducer for `hT_test_compat`**.

Takes per-(τ, w) witnesses for both halves of the conclusion: the per-`t'`
chain `∀ t' ∈ D.T, w.vle t' D.s` and the non-degeneracy `¬ w.vle D.s 0`.
Both are explicit inputs (not derived); this packaging just composes
them into the `hT_test_compat` shape that
`rationalOpen_subset_via_strict_sigma_domination` consumes.

For the τ = D.s branch, `h_per_branch_D_s_ne` is automatically
satisfied via `not_vle_zero_of_strict_dominator`; for τ ∈ D.T branches,
it must be supplied explicitly (the strict σ-domination at τ alone
gives `¬ w.vle τ 0`, NOT `¬ w.vle D.s 0`). -/
theorem hT_test_compat_of_per_branch_chain
    [DecidableEq A] (C : RationalCoveringData A) (D : RationalLocData A)
    (σ : Aˣ) (T_test : Finset A)
    (h_per_branch_t : ∀ τ ∈ T_test, ∀ w ∈ Spa A A⁺,
      w.vle ((σ : A) * (∏ t ∈ D.T, t)) C.base.s →
      w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A) →
      ∀ t' ∈ D.T, w.vle t' D.s)
    (h_per_branch_D_s_ne : ∀ τ ∈ T_test, ∀ w ∈ Spa A A⁺,
      w.vle ((σ : A) * (∏ t ∈ D.T, t)) C.base.s →
      w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A) →
      ¬ w.vle D.s 0) :
    ∀ τ ∈ T_test, ∀ w ∈ Spa A A⁺,
      w.vle ((σ : A) * (∏ t ∈ D.T, t)) C.base.s →
      w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A) →
        (∀ t' ∈ D.T, w.vle t' D.s) ∧ ¬ w.vle D.s 0 := by
  intro τ hτ w hw_spa hw_f hστ
  exact ⟨h_per_branch_t τ hτ w hw_spa hw_f hστ,
    h_per_branch_D_s_ne τ hτ w hw_spa hw_f hστ⟩

/-- **Composed consumer**: rational-open subset inclusion from
σ-strict-domination supplier and the per-branch chain hypotheses.

Composes `hT_test_compat_of_per_branch_chain` with
`rationalOpen_subset_via_strict_sigma_domination` to produce the C1
candidate-side rational-open inclusion. -/
theorem rationalOpen_subset_via_per_branch_chain
    [DecidableEq A] (C : RationalCoveringData A) (D : RationalLocData A)
    (σ : Aˣ) (T_test : Finset A)
    (hσ : ∀ w ∈ Spa A A⁺, ∃ τ ∈ T_test,
      w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A))
    (h_per_branch_t : ∀ τ ∈ T_test, ∀ w ∈ Spa A A⁺,
      w.vle ((σ : A) * (∏ t ∈ D.T, t)) C.base.s →
      w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A) →
      ∀ t' ∈ D.T, w.vle t' D.s)
    (h_per_branch_D_s_ne : ∀ τ ∈ T_test, ∀ w ∈ Spa A A⁺,
      w.vle ((σ : A) * (∏ t ∈ D.T, t)) C.base.s →
      w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A) →
      ¬ w.vle D.s 0) :
    rationalOpen (insert ((σ : A) * (∏ t ∈ D.T, t)) C.base.T) C.base.s ⊆
      rationalOpen D.T D.s :=
  rationalOpen_subset_via_strict_sigma_domination C D σ T_test hσ
    (hT_test_compat_of_per_branch_chain C D σ T_test h_per_branch_t
      h_per_branch_D_s_ne)

/-! ### Remaining residual (one Lean statement)

The genuine Wedhorn content not landed by this file is the per-branch
**per-`t'` chain discharger** for arbitrary `D.T`:

```
theorem h_per_branch_t_chain_of_cor732
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] [DecidableEq A]
    (C : RationalCoveringData A) (D : RationalLocData A) (σ : Aˣ) (τ : A)
    {w : Spv A} (hw_spa : w ∈ Spa A A⁺)
    (hw_f : w.vle ((σ : A) * (∏ t ∈ D.T, t)) C.base.s)
    (hστ : w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A))
    -- additional Wedhorn-specific data linking τ to (D.T, D.s, C.base.s):
    (hτ_link : sorry) :
    ∀ t' ∈ D.T, w.vle t' D.s
```

The `hτ_link` premise is the missing structural data — at the τ = D.s
branch, it would relate `w(C.base.s)` to `w(D.s)^|D.T|` to extract per-`t'`
inequalities from the multi-element f-membership; at τ ∈ T_D branches,
it would relate `w(τ)` to `w(D.s)` similarly.

The `WedhornMultiDominatingUnit.lean:234–304` audit suggests that no
single algebraic `hτ_link` discharges this uniformly; the genuine
Wedhorn 8.34(ii) approach is **pre-localisation at `C.base.s`** (Route
B), reducing to a Spa-of-A_loc problem. The next ticket on this lane
is the formalization of the localisation-transfer step. -/

end ValuationSpectrum

/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornFullLaurentVKBranchDecomposition

/-!
# Wedhorn 8.34(ii) α_T_D branch per-`t'` σ-factored chain (T033)

α_T_D branch counterpart to T030's `alpha_s_D_per_t_factored_chain_via_lower_branch`.
Where the α_s_D branch consumes the V_∅ lower-half rational-open
membership (`w ∈ rationalOpen (T_D.image) σ_loc`), the α_T_D branch
consumes the V_K-nonempty σ-strict-domination witness `(t_0, ...)` from
T031's `laurent_VK_branch_decomposition_at` plus an **intermediate
τ-comparison** that bounds each `t'` by some `τ ∈ Localization.Away s`
which is itself bounded by `algebraMap s_D`.

## α_T_D arithmetic at `w`

In the α_T_D branch, σ_loc is σ-strictly dominated by some
`t_0 ∈ T_D.image (algebraMap)`; the V_K-nonempty witness
`w.vle σ_loc t_0 ∧ ¬ w.vle t_0 σ_loc` is supplied by T031. The
**natural Wedhorn-content additional input** for this branch is an
intermediate `τ : Localization.Away s` with:

* `w.vle τ (algebraMap s_D)` — `τ` is bounded above by
  `algebraMap s_D` at `w`;
* `∀ t' ∈ T_D.image (algebraMap), w.vle t' τ` — each `t'` is bounded
  above by `τ` at `w`.

Transitivity then gives `∀ t' ∈ T_D.image, w.vle t' (algebraMap s_D)`,
and σ-cancellation via `vle_iff_mul_unit_right` lifts to the per-`t'`
σ-factored chain `w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)`.

The natural choice of `τ` in the α_T_D branch is the V_K-nonempty
strict-dom witness `t_0` itself — but this requires the additional
piece `w.vle t_0 (algebraMap s_D)`, which is **NOT** automatic from
the V_K decomposition alone (since `t_0 ∈ T_D.image` is NOT a priori
bounded by `algebraMap s_D`). This file isolates the algebraic step
so the missing comparison is explicit and reusable.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson /
  T001 / faithful-flatness / Zavyalov / bivariate-overlap content.
* No σ-power-decay revival.
* Imports only T031's committed `WedhornFullLaurentVKBranchDecomposition`,
  which transitively brings in T030/T029/T028/T027 + the rational-open
  API + σ-cancellation primitives.
* Does NOT edit T027/T028/T029/T030/T031/T032 accepted files.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-- **σ-cancellation lift from per-`t'` upper bound by `algebraMap s_D`**
(α_T_D branch primitive A).

The simplest substantive step in the α_T_D branch arithmetic: from a
per-`t'` upper bound `∀ t' ∈ T_D.image (algebraMap), w.vle t'
(algebraMap s_D)`, produce the per-`t'` σ-factored chain
`w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)`.

Pure σ-cancellation via `vle_iff_mul_unit_right`. Identical algebraic
mechanism to T029's α_s_D σ-cancellation step — the only difference
is the `τ`-supply structure (α_s_D supplies the per-`t'` upper bound
via V_∅ + Laurent piece at `algebraMap s_D`; α_T_D requires an
explicit intermediate or a different source). -/
theorem alpha_T_D_per_t_factored_chain_from_per_t_bound
    {s : A} (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (w : Spv (Localization.Away s))
    (h_per_t :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle t' (algebraMap A (Localization.Away s) s_D)) :
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle (t' * (σ_loc : Localization.Away s))
        ((algebraMap A (Localization.Away s) s_D) *
          (σ_loc : Localization.Away s)) := by
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro t' ht'
  exact (vle_iff_mul_unit_right w σ_loc t'
    (algebraMap A (Localization.Away s) s_D)).mpr (h_per_t t' ht')

/-- **α_T_D per-`t'` upper bound via intermediate τ-comparison**
(α_T_D branch primitive B).

From two pieces of α_T_D-branch comparison data at `w`:

* `h_τ_le_s_D` — `τ` is bounded above by `algebraMap s_D`;
* `h_t_le_τ` — every `t' ∈ T_D.image (algebraMap)` is bounded above
  by `τ`,

derive the per-`t'` upper bound `∀ t' ∈ T_D.image, w.vle t'
(algebraMap s_D)` via `vle_trans`. The intermediate `τ` is most
naturally chosen as the V_K-nonempty σ-strict-dom witness `t_0` from
T031, although the lemma is independent of how `τ` is supplied. -/
theorem alpha_T_D_per_t_bound_via_intermediate
    {s : A} (T_D : Finset A) (s_D : A)
    (w : Spv (Localization.Away s))
    (τ : Localization.Away s)
    (h_τ_le_s_D : w.vle τ (algebraMap A (Localization.Away s) s_D))
    (h_t_le_τ :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle t' τ) :
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle t' (algebraMap A (Localization.Away s) s_D) := by
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro t' ht'
  exact w.vle_trans (h_t_le_τ t' ht') h_τ_le_s_D

/-- **α_T_D per-`t'` σ-factored chain via intermediate τ-comparison
(T033 main composed deliverable)**.

Composes `alpha_T_D_per_t_bound_via_intermediate` with
`alpha_T_D_per_t_factored_chain_from_per_t_bound`: from the
intermediate τ-comparisons (`τ ≤ algebraMap s_D` and `∀ t' ∈ T_D.image,
t' ≤ τ`), derive the per-`t'` σ-factored chain
`w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)`.

The natural choice for `τ` is the **V_K-nonempty σ-strict-dom witness
`t_0`** from T031's `laurent_VK_branch_decomposition_at` (i.e., the
α_T_D branch case): if `w` is in V_K-nonempty, T031 supplies
`t_0 ∈ T_D.image (algebraMap)` with `w.vle σ_loc t_0` and
`¬ w.vle t_0 σ_loc`. Choosing `τ := t_0`:

* `h_τ_le_s_D := w.vle t_0 (algebraMap s_D)` is the **explicit minimal
  missing comparison** in the α_T_D branch (NOT automatic from V_K
  decomposition alone — `t_0 ∈ T_D.image` is not a priori bounded by
  `algebraMap s_D`);

* `h_t_le_τ := ∀ t' ∈ T_D.image, w.vle t' t_0` is the **explicit
  maximum-element-in-T_D.image hypothesis** (also NOT automatic from
  V_K decomposition — the strict-dom witness `t_0` need not be the
  maximum element).

Both hypotheses are natural in the α_T_D branch consumer interface
and appear as explicit residuals for the T021 / T028 chain. -/
theorem alpha_T_D_per_t_factored_chain_via_intermediate
    {s : A} (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (w : Spv (Localization.Away s))
    (τ : Localization.Away s)
    (h_τ_le_s_D : w.vle τ (algebraMap A (Localization.Away s) s_D))
    (h_t_le_τ :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle t' τ) :
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle (t' * (σ_loc : Localization.Away s))
        ((algebraMap A (Localization.Away s) s_D) *
          (σ_loc : Localization.Away s)) := by
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  exact alpha_T_D_per_t_factored_chain_from_per_t_bound T_D s_D σ_loc w
    (alpha_T_D_per_t_bound_via_intermediate T_D s_D w τ h_τ_le_s_D
      h_t_le_τ)

end ValuationSpectrum

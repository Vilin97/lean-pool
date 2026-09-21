/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornFullLaurentLowerBranchBound

/-!
# Wedhorn 8.34(ii) full Laurent V_K branch decomposition (T031)

Per-`w` decomposition theorem for the full σ_loc-rescaled Laurent
refinement at `T_D.image (algebraMap A (Localization.Away s))`. At any
`w : Spv (Localization.Away s)`, exactly one of the following holds:

1. **V_∅ branch (lower-half on every t')**: every
   `t' ∈ T_D.image (algebraMap)` satisfies `w.vle t' σ_loc` — i.e.,
   `w` lies in the V_∅ piece of the full σ_loc-rescaled Laurent cover.
   This is exactly the input consumed by T030's
   `alpha_s_D_per_t_factored_chain_via_lower_branch`, driving the
   α_s_D branch of T021's honest structural supplier.

2. **V_K-nonempty branch (some t_0 σ-strictly dominates)**: there
   exists `t_0 ∈ T_D.image (algebraMap)` with σ-strict-domination
   `w.vle σ_loc t_0 ∧ ¬ w.vle t_0 σ_loc`. This is the α_T_D-branch
   data of T021's honest structural supplier (σ-strict-dom by
   `τ := t_0 ∈ T_D.image (algebraMap)`).

The disjunction is exhaustive at every `w` by classical case-split on
`∀ t' ∈ T_D.image, w.vle t' σ_loc`, with `vle_total` recovering the
σ-strict-dom direction in the negative case.

## How this feeds the localized Wedhorn 8.34(ii) chain

Combined with T027's per-`w` Laurent-piece membership (which gives a
`τ ∈ localizedTestFamily s T_D s_D` such that `w` is in the Laurent
piece for τ), the V_K decomposition partitions Spa into branches:

* **V_∅ (lower) + Laurent piece at α_s_D (τ = algebraMap s_D)**:
  T030's `alpha_s_D_per_t_factored_chain_via_lower_branch` directly
  produces the per-`t'` σ-factored chain.

* **V_K-nonempty (upper at some t_0) + any Laurent piece**: σ-strict-
  domination by `t_0 ∈ T_D.image (algebraMap)` is exactly the
  α_T_D-branch data; the per-`t'` σ-factored chain on this branch is
  the natural Wedhorn 8.34(ii) α_T_D arithmetic (next ticket).

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson /
  T001 / faithful-flatness / Zavyalov / bivariate-overlap content.
* No σ-power-decay revival.
* Imports only T030's committed `WedhornFullLaurentLowerBranchBound`,
  which transitively brings in T029's α_s_D consumer, T027's localized
  Laurent-piece membership supplier, and the σ-cancellation /
  rational-open API.
* Does NOT edit T027/T028/T029/T030 accepted files.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] in
/-- **Full Laurent V_K branch decomposition at `w`** (T031 main
theorem).

At any `w : Spv (Localization.Away s)`, the σ_loc-rescaled full
Laurent refinement at `T_D.image (algebraMap A (Localization.Away s))`
gives an exhaustive **two-branch** disjunction:

1. **V_∅ branch**: `∀ t' ∈ T_D.image (algebraMap), w.vle t' σ_loc`,
   i.e., every `t'` lies in σ_loc's "≤ 1" half-space at `w`.

2. **V_K-nonempty branch**: `∃ t_0 ∈ T_D.image (algebraMap), w.vle σ_loc
   t_0 ∧ ¬ w.vle t_0 σ_loc`, i.e., some `t_0` σ-strictly dominates
   σ_loc.

Proof: classical case-split on the V_∅ statement. In the negative
case, push the negation to extract a `t_0` with `¬ w.vle t_0 σ_loc`,
then `vle_total` (which is the totality of `≤ᵥ`) gives `w.vle σ_loc
t_0` to complete the σ-strict-dom witness.

This is a **finite-set independent** decomposition: the proof is pure
classical logic + `vle_total`, so the conclusion holds for any
`w : Spv (Localization.Away s)`, finite `T_D : Finset A`, and unit
`σ_loc : (Localization.Away s)ˣ`. -/
theorem laurent_VK_branch_decomposition_at
    {s : A} (T_D : Finset A) (σ_loc : (Localization.Away s)ˣ)
    (w : Spv (Localization.Away s)) :
    (letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle t' (σ_loc : Localization.Away s)) ∨
    (letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∃ t_0 ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle (σ_loc : Localization.Away s) t_0 ∧
          ¬ w.vle t_0 (σ_loc : Localization.Away s)) := by
  classical
  letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
  by_cases h : ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle t' (σ_loc : Localization.Away s)
  · left; exact h
  · right
    push Not at h
    obtain ⟨t_0, ht_0_mem, h_not_le⟩ := h
    refine ⟨t_0, ht_0_mem, ?_, h_not_le⟩
    rcases w.vle_total (σ_loc : Localization.Away s) t_0 with h_le | h_le
    · exact h_le
    · exact absurd h_le h_not_le

omit [PlusSubring A] in
/-- **Per-`w` α_s_D σ-factored chain or α_T_D σ-strict-dom witness**
(combined T031/T030 disjunction).

Combines the V_K branch decomposition (T031) with T030's
`alpha_s_D_per_t_factored_chain_via_lower_branch` to give a
per-`w` outcome:

* If `w` is in V_∅ at `T_D.image`, return the **per-`t'` σ-factored
  chain** `w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)` directly via
  T030 (using the supplied α_s_D-branch Laurent-piece membership).

* Otherwise, return the **σ-strict-dom witness** at some
  `t_0 ∈ T_D.image (algebraMap)`: `w.vle σ_loc t_0 ∧
  ¬ w.vle t_0 σ_loc`. This is the α_T_D-branch data for T021.

The α_s_D-branch Laurent-piece membership is supplied as a
hypothesis (T027's localized supplier output at α_s_D specialisation,
unwrapped for the fixed `w`); the V_K decomposition is internally
discharged by `laurent_VK_branch_decomposition_at`. -/
theorem alpha_s_D_per_t_chain_or_alpha_T_D_strict_dom_at
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (w : Spv (Localization.Away s))
    (h_laurent_α_s_D :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      w ∈ rationalOpen
        ({(1 : Localization.Away s)} : Finset (Localization.Away s))
        (((σ_loc⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) *
          algebraMap A (Localization.Away s) s_D)) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle (t' * (σ_loc : Localization.Away s))
          ((algebraMap A (Localization.Away s) s_D) *
            (σ_loc : Localization.Away s))) ∨
    (∃ t_0 ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle (σ_loc : Localization.Away s) t_0 ∧
          ¬ w.vle t_0 (σ_loc : Localization.Away s)) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  rcases laurent_VK_branch_decomposition_at T_D σ_loc w with h_V_empty | h_V_nonempty
  · -- V_∅ branch: package as α_s_D σ-factored chain via T030.
    left
    have hw_spa : w ∈ Spa (Localization.Away s) (Localization.Away s)⁺ :=
      h_laurent_α_s_D.1
    have hσ_loc_ne : ¬ w.vle (σ_loc : Localization.Away s) 0 :=
      not_vle_zero_of_isUnit σ_loc.isUnit w
    have h_lower_branch :
        w ∈ rationalOpen
          (T_D.image (algebraMap A (Localization.Away s)))
          (σ_loc : Localization.Away s) :=
      ⟨hw_spa, h_V_empty, hσ_loc_ne⟩
    exact alpha_s_D_per_t_factored_chain_via_lower_branch
      P T s hopen T_D s_D σ_loc w h_laurent_α_s_D h_lower_branch
  · -- V_K-nonempty branch: directly return the σ-strict-dom witness.
    right
    exact h_V_nonempty

end ValuationSpectrum

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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornCor732BranchTransfer
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalizedCor732Bridge
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalizationContinuity
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornPrelocalizationTransfer

/-!
# Wedhorn rational-open localization transfer (locSubring form)

Spa/rational-open dictionary for the localization map
`A → Localization.Away s` with the **`locSubring P T s`** plus-subring
form, completing the Route B pre-localisation transfer
infrastructure for Wedhorn 8.34(ii).

## Existing infrastructure (reused)

* `comap_mem_rationalOpen_iff` (`WedhornPrelocalizationTransfer.lean:115`)
  — generic comap pullback for any continuous ring hom with plus-subring
  containment.
* `rationalOpen_transfer_via_localization`
  (`WedhornLocalizationTransferConsumer.lean:86`) — the analogous
  transfer for the `localizationAwayPlusSubring` (image) plus-subring
  form.
* `valuationLocalizationLift_of_spa_rationalOpen_locSubring`
  (`WedhornLocalizedCor732Bridge.lean:127`) — base→local lift landing
  in `Spa(_, locSubring)`.
* `localizationLocSubringPlusSubring`
  (`WedhornLocalizedCor732Bridge.lean:100`) — `PlusSubring` instance
  with `toSubring := locSubring P T s`.
* `rationalOpen_subset_via_per_branch_chain`
  (`WedhornCor732BranchTransfer.lean`) — base-side branch-chain
  consumer.

## What this file provides

* `localizationLocSubring_aplus_le_comap` — plus-subring containment for
  the `locSubring` form: `A⁺ ⊆ algebraMap⁻¹(locSubring P T s)`,
  given `A⁺ ⊆ A₀`. Direct from `algebraMap_mem_locSubring`.
* `rationalOpen_transfer_via_localization_locSubring` — comap-pullback
  iff for the `locSubring` form. Analog of
  `rationalOpen_transfer_via_localization` with `locSubring`-flavored
  Spa.
* `rationalOpen_subset_via_localization_locSubring` — the **full
  transfer**: a local rational-open inclusion on `Spa(Localization.Away
  s, locSubring P T s)` pulls back via lift+comap to the corresponding
  base rational-open inclusion on `Spa(A, A⁺)`.

## Honest scope discussion

The full Wedhorn 8.34(ii) Route B per-`t'` discharge requires
formulating the per-branch chain hypothesis IN THE LOCALIZED context
(on `Spa(A_loc, locSubring P T s)`) and pulling back via this transfer.
The theorems here provide the dictionary; the residual is the local
per-branch chain itself, which is the genuinely-new Wedhorn content
(σ-construction inside `Spa A_loc`).

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness content.
* Does NOT edit Tertiary's uncommitted `WedhornLocalizedCor732Application.lean`,
  Spa/rationalOpen lift wrapper files, T001/T013/T016/T004 files, or
  any other in-flight file.
* Uses existing helpers and committed transfers; adds only new
  theorems for the `locSubring` plus-subring form.
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

omit [IsTopologicalRing A] in
/-- **Plus-subring containment for the `locSubring` form**.

Under the canonical hypothesis `A⁺ ⊆ A₀` (Wedhorn `CompatiblePlusSubring`
direction), the plus-subring `locSubring P T s` on the localization
contains the image of `A⁺` under `algebraMap`. This is the `hAB`
argument required by `comap_mem_rationalOpen_iff`. Direct from
`algebraMap_mem_locSubring`. -/
theorem localizationLocSubring_aplus_le_comap
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀) :
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    (A⁺ : Subring A) ≤
      (PlusSubring.toSubring (A := Localization.Away s)).comap
        (algebraMap A (Localization.Away s)) :=
  fun _ hf => algebraMap_mem_locSubring P T s (hAplus_le_A₀ hf)

/-- **Rational-open transfer via localization (locSubring form)**.

For a Spa-point `w` on the localization w.r.t. the `locSubring P T s`
plus-subring, rational-open membership of `comap (algebraMap A _) w`
in any `R(T', s')` on `Spa(A, A⁺)` transfers to a pointwise condition
on `w` via `algebraMap`. Composes
`locTopology_algebraMap_continuous`,
`localizationLocSubring_aplus_le_comap`, and
`comap_mem_rationalOpen_iff`. -/
theorem rationalOpen_transfer_via_localization_locSubring
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (T' : Finset A) (s' : A) {w : Spv (Localization.Away s)}
    (hw : w ∈ @Spa (Localization.Away s) _ (locTopology P T s hopen)
      (locSubring P T s)) :
    comap (algebraMap A (Localization.Away s)) w ∈ rationalOpen T' s' ↔
      (∀ t ∈ T', w.vle (algebraMap A (Localization.Away s) t)
        (algebraMap A (Localization.Away s) s')) ∧
      ¬ w.vle (algebraMap A (Localization.Away s) s') 0 := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  exact comap_mem_rationalOpen_iff
    (locTopology_algebraMap_continuous P T s hopen)
    (localizationLocSubring_aplus_le_comap P T s hAplus_le_A₀) T' s' hw

/-- **Full rational-open subset transfer via localization (locSubring
form)**: a local rational-open inclusion on `Spa(Localization.Away s,
locSubring P T s)` pulls back to the corresponding base rational-open
inclusion on `Spa(A, A⁺)`.

Given:
* `T ⊆ T1` (so the source rationalOpen `R(T1, s)` lifts to local Spa
  via `valuationLocalizationLift_of_spa_rationalOpen_locSubring`).
* A local set-inclusion hypothesis: every Spa-point `w` on the
  localization satisfying the local-`(T1, s)` rationalOpen conditions
  also satisfies the local-`(T2, s2)` conditions.

Conclude: the base rationalOpen inclusion `R(T1, s) ⊆ R(T2, s2)` on
`Spa(A, A⁺)`. -/
theorem rationalOpen_subset_via_localization_locSubring
    [DecidableEq A]
    (P : PairOfDefinition A) (T T1 T2 : Finset A) (s s2 : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (hA₀_le : P.A₀ ≤ A⁺)
    (h_T_le_T1 : T ⊆ T1)
    (h_local :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      ∀ w : Spv (Localization.Away s),
        w ∈ @Spa (Localization.Away s) _ (locTopology P T s hopen)
          (locSubring P T s) →
        (∀ t ∈ T1, w.vle (algebraMap A (Localization.Away s) t)
          (algebraMap A (Localization.Away s) s)) →
        ¬ w.vle (algebraMap A (Localization.Away s) s) 0 →
        (∀ t ∈ T2, w.vle (algebraMap A (Localization.Away s) t)
          (algebraMap A (Localization.Away s) s2)) ∧
        ¬ w.vle (algebraMap A (Localization.Away s) s2) 0) :
    rationalOpen T1 s ⊆ rationalOpen T2 s2 := by
  intro v hv
  obtain ⟨hv_spa, hv_T1, hv_s_ne⟩ := hv
  -- Pre-condition for lift: v ∈ rationalOpen T s (via T ⊆ T1).
  have hv_T_s : v ∈ rationalOpen T s :=
    ⟨hv_spa, fun t ht => hv_T1 t (h_T_le_T1 ht), hv_s_ne⟩
  -- Lift to local Spa.
  obtain ⟨w, hw_spa, hcomap⟩ :=
    valuationLocalizationLift_of_spa_rationalOpen_locSubring
      P T s hopen hA₀_le hv_T_s
  -- Translate base-side rationalOpen membership of `v` to local side via comap.
  have hw_T1 : ∀ t ∈ T1, w.vle (algebraMap A (Localization.Away s) t)
      (algebraMap A (Localization.Away s) s) := by
    intro t ht
    rw [← comap_vle]
    exact hcomap ▸ hv_T1 t ht
  have hw_s_ne : ¬ w.vle (algebraMap A (Localization.Away s) s) 0 := by
    intro hw_s
    apply hv_s_ne
    rw [← hcomap, comap_vle, map_zero]
    exact hw_s
  -- Apply local inclusion.
  obtain ⟨hw_T2, hw_s2_ne⟩ := h_local w hw_spa hw_T1 hw_s_ne
  -- Translate back to base side.
  refine ⟨hv_spa, fun t ht => ?_, ?_⟩
  · rw [← hcomap, comap_vle]
    exact hw_T2 t ht
  · intro hv_s2
    apply hw_s2_ne
    have : (comap (algebraMap A (Localization.Away s)) w).vle s2 0 := hcomap ▸ hv_s2
    rwa [comap_vle, map_zero] at this

end ValuationSpectrum

/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalizedCor732SigmaSupplier
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornActualC1PerCallClosure
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornPerPieceSubsetProductClearing

/-!
# Wedhorn 8.34(ii) — Per-piece subset adapter from T056 to T064 / T065 (T069)

T056 (`WedhornPerPieceLaurentC1Supplier`) provides
`per_piece_singleton_subset_via_laurent_membership`: for each `τ`,
a τ-indexed per-piece subset
`R(insert f T_base, s) ∩ R({1}, σ⁻¹ * τ) ⊆ R({σ⁻¹ * τ}, D_s)`
under a per-`w`-on-`V_τ` product upper bound hypothesis.

T067 (`WedhornPerPieceSubsetProductClearing`) provides
`per_piece_subset_supplier_via_pointwise_clearing`: a uniform-over-`D_T`
t-indexed per-piece subset
`∀ t' ∈ D_T, R(insert f T_base, s) ∩ R({1}, t') ⊆ R({t'}, D_s)`
under a per-`v` pointwise clearing hypothesis.

T064 / T065 consume the **t-indexed** per-piece subset shape:

* T064 (`C1SupplierStrong_local_via_t_indexed_direct`) takes
  `∀ t' ∈ D.T, R(insert f C.base.T, C.base.s) ∩ R({1}, t') ⊆
  R({t'}, D.s)` per call.
* T065 (`rationalOpen_global_subset_via_localizedCor732_sigma_supplier`)
  takes `∀ σ_loc, ∀ t ∈ (localizedTestFamily s T_D s_D).image
  (σ_loc⁻¹ * ·), R(insert f T_base, s_base) ∩ R({1}, t) ⊆ R({t}, D_s)`
  on the localized side.

This file lands the **interface adapters** packaging T056-style and
T067-style outputs in the exact shape consumed by T064 / T065. The
deliverables are:

* `per_piece_subset_adapter_from_T056_to_T065` — main ticket-named
  adapter: takes a τ-indexed per-piece subset family
  (T056-`per_piece_singleton_subset_via_laurent_membership` shape) and
  re-indexes to the t-indexed `T_test.image (σ⁻¹ * ·)` form consumed
  by T065.

* `per_piece_subset_adapter_from_T056_at_localized` — localized-side
  σ_loc-uniform variant for direct plug-in to
  `rationalOpen_global_subset_via_localizedCor732_sigma_supplier`.

* `per_piece_subset_adapter_from_pointwise_clearing` — packaging of
  T067's `per_piece_subset_supplier_via_pointwise_clearing` in the
  exact T064 input shape.

* `per_piece_subset_adapter_from_pointwise_clearing_localized` —
  σ_loc-uniform localized variant for T065 direct plug-in.

* `C1SupplierStrong_local_via_pointwise_clearing` — end-to-end
  consumer composing T067's pointwise clearing with T064's t-indexed
  closure: takes per-call pointwise clearing inputs and produces
  `C1SupplierStrong_local C` directly.

## Why an adapter rather than substantive new content

T067 and T064 are already in the t-indexed shape T065 needs; T056 is
τ-indexed but the τ → t re-indexing is a one-step substitution
(`Finset.mem_image_of_mem` + `subst`). The adapter exposes these
clean compositions as named theorems so downstream callers can plug
T056-style or T067-style data into T064 / T065 without rebuilding
the τ → t conversion at each call site.

## Notes

* No root import; leaf-level file.
* Imports T065 (`WedhornLocalizedCor732SigmaSupplier`),
  T064 (`WedhornActualC1PerCallClosure`), and T067
  (`WedhornPerPieceSubsetProductClearing`).
* No edits to T031–T067 accepted leaves, root imports, or final
  theorem signatures.
* Disjoint write set from all accepted files.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32 / Jacobson, faithful-flatness, Zavyalov, global universal
  Spa bound, or bivariate-overlap content.
* All declarations are fully proven, depend only on the standard
  Lean kernel postulates, and avoid native compilation and unchecked
  tactics.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

omit [IsTopologicalRing A] in
/-- **τ → t re-indexing of a T056-style per-piece subset family**
(T069 main adapter — ticket-named theorem).

Bridges T056's τ-indexed per-piece subset output (where each `τ ∈
T_test` carries the σ-rescaled subset
`R(insert f T_base, s) ∩ R({1}, σ⁻¹ * τ) ⊆ R({σ⁻¹ * τ}, D_s)`) to the
**t-indexed** form `∀ t ∈ T_test.image (σ⁻¹ * ·), per-piece subset
at t` consumed by T064 / T065.

The conversion is a direct `Finset.mem_image_of_mem` re-indexing —
no arithmetic content, just the natural σ-rescaling cancellation
exposed at the index level.

**Use site**: callers holding a τ-indexed per-piece subset family
from T056 (e.g., from
`per_piece_singleton_subset_via_laurent_membership` instantiated at
each `τ ∈ T_test` with the per-`w`-on-`V_τ` product upper bound
discharged) plug into T065's
`rationalOpen_global_subset_via_localizedCor732_sigma_supplier`
through this adapter. -/
theorem per_piece_subset_adapter_from_T056_to_T065
    [DecidableEq A]
    {σ : Aˣ} (T_test : Finset A) (T_base : Finset A) (s D_s f : A)
    (h_per_τ :
      ∀ τ ∈ T_test,
        rationalOpen (insert f T_base) s ∩
            rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) ⊆
          rationalOpen ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D_s) :
    ∀ t ∈ T_test.image (fun τ => ((σ⁻¹ : Aˣ) : A) * τ),
      rationalOpen (insert f T_base) s ∩
          rationalOpen ({(1 : A)} : Finset A) t ⊆
        rationalOpen ({t} : Finset A) D_s := by
  intro t ht
  obtain ⟨τ, hτ_mem, rfl⟩ := Finset.mem_image.mp ht
  exact h_per_τ τ hτ_mem

omit [PlusSubring A] in
/-- **σ_loc-uniform localized adapter from T056-style per-piece subsets**
(T069 localized variant).

`σ_loc`-uniform localized version of
`per_piece_subset_adapter_from_T056_to_T065`, matching the per-piece
subset hypothesis shape consumed by T065's
`rationalOpen_global_subset_via_localizedCor732_sigma_supplier`
exactly. The user supplies a τ-indexed per-piece subset family
parameterised by `σ_loc`, and the adapter re-indexes each per-piece
subset to the t-indexed `(localizedTestFamily s T_D s_D).image
(σ_loc⁻¹ * ·)` shape T065 expects.

Designed for direct plug-in to T065 — the conclusion shape is
exactly T065's `_h_per_piece_subset_at_supplied_sigma` hypothesis. -/
theorem per_piece_subset_adapter_from_T056_at_localized
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ (T_D : Finset A) (s_D : A)
      (T_base_loc : Finset (Localization.Away s))
      (s_base_loc D_s f_loc : Localization.Away s)
      (_h_per_τ_at_supplied_sigma :
        ∀ (σ_loc : (Localization.Away s)ˣ),
          ∀ τ ∈ localizedTestFamily s T_D s_D,
            rationalOpen (insert f_loc T_base_loc) s_base_loc ∩
                rationalOpen
                  ({(1 : Localization.Away s)} :
                    Finset (Localization.Away s))
                  (((σ_loc⁻¹ : (Localization.Away s)ˣ) :
                    Localization.Away s) * τ) ⊆
              rationalOpen
                ({((σ_loc⁻¹ : (Localization.Away s)ˣ) :
                  Localization.Away s) * τ} :
                  Finset (Localization.Away s)) D_s),
      ∀ (σ_loc : (Localization.Away s)ˣ),
        ∀ t ∈ (localizedTestFamily s T_D s_D).image
            (fun τ => ((σ_loc⁻¹ : (Localization.Away s)ˣ) :
              Localization.Away s) * τ),
          rationalOpen (insert f_loc T_base_loc) s_base_loc ∩
              rationalOpen
                ({(1 : Localization.Away s)} :
                  Finset (Localization.Away s)) t ⊆
            rationalOpen
              ({t} : Finset (Localization.Away s)) D_s := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro T_D s_D T_base_loc s_base_loc D_s f_loc h_per_τ_at_supplied_sigma σ_loc
  exact per_piece_subset_adapter_from_T056_to_T065
    (localizedTestFamily s T_D s_D) T_base_loc s_base_loc D_s f_loc
    (h_per_τ_at_supplied_sigma σ_loc)

omit [IsTopologicalRing A] in
/-- **T067 pointwise-clearing adapter to T064 t-indexed shape**
(T069 packaging).

Direct repackaging of T067's
`per_piece_subset_supplier_via_pointwise_clearing` exposing the exact
T064 per-piece subset input shape `∀ t' ∈ D_T, R(insert f T_base, s)
∩ R({1}, t') ⊆ R({t'}, D_s)`.

Identity wrapper — T067 already produces this shape — but providing it
under T069's documentation umbrella makes the T064 plug-in route
explicit. -/
theorem per_piece_subset_adapter_from_pointwise_clearing
    [DecidableEq A]
    (T_base D_T : Finset A) (s D_s f : A)
    (h_clearing :
      ∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
        v.vle f s →
        v.vle (1 : A) t' →
        ¬ v.vle t' 0 →
        v.vle t' D_s) :
    ∀ t' ∈ D_T,
      rationalOpen (insert f T_base) s ∩
          rationalOpen ({(1 : A)} : Finset A) t' ⊆
        rationalOpen ({t'} : Finset A) D_s :=
  per_piece_subset_supplier_via_pointwise_clearing T_base D_T s D_s f
    h_clearing

omit [PlusSubring A] in
/-- **σ_loc-uniform localized adapter from pointwise clearing**
(T069 localized variant for T065 direct plug-in).

`σ_loc`-uniform localized version of the T067 pointwise-clearing →
T064 packaging adapter, matching T065's per-piece subset hypothesis
shape directly. The user supplies a `σ_loc`-uniform pointwise
clearing on the localized side; the adapter packages it as the
t-indexed per-piece subset family ranging over
`(localizedTestFamily s T_D s_D).image (σ_loc⁻¹ * ·)`. -/
theorem per_piece_subset_adapter_from_pointwise_clearing_localized
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ (T_D : Finset A) (s_D : A)
      (T_base_loc : Finset (Localization.Away s))
      (s_base_loc D_s f_loc : Localization.Away s)
      (_h_clearing_at_supplied_sigma :
        ∀ (σ_loc : (Localization.Away s)ˣ),
          ∀ t ∈ (localizedTestFamily s T_D s_D).image
              (fun τ => ((σ_loc⁻¹ : (Localization.Away s)ˣ) :
                Localization.Away s) * τ),
            ∀ v ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
              v.vle f_loc s_base_loc →
              v.vle (1 : Localization.Away s) t →
              ¬ v.vle t 0 →
              v.vle t D_s),
      ∀ (σ_loc : (Localization.Away s)ˣ),
        ∀ t ∈ (localizedTestFamily s T_D s_D).image
            (fun τ => ((σ_loc⁻¹ : (Localization.Away s)ˣ) :
              Localization.Away s) * τ),
          rationalOpen (insert f_loc T_base_loc) s_base_loc ∩
              rationalOpen
                ({(1 : Localization.Away s)} :
                  Finset (Localization.Away s)) t ⊆
            rationalOpen
              ({t} : Finset (Localization.Away s)) D_s := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro T_D s_D T_base_loc s_base_loc D_s f_loc h_clearing_at_supplied_sigma σ_loc
  exact per_piece_subset_adapter_from_pointwise_clearing
    T_base_loc
    ((localizedTestFamily s T_D s_D).image
      (fun τ => ((σ_loc⁻¹ : (Localization.Away s)ˣ) :
        Localization.Away s) * τ))
    s_base_loc D_s f_loc (h_clearing_at_supplied_sigma σ_loc)

/-- **End-to-end: per-call pointwise clearing ⊢ `C1SupplierStrong_local C`**
(T069 final consumer).

End-to-end consumer composing T067's per-piece subset supplier with
T064's `C1SupplierStrong_local_via_t_indexed_direct`: from per-call
σ-free t-indexed inputs (per-call σ_choice / `f` / `v`-membership /
`f`-non-degeneracy / Laurent cover) **plus a per-`v` pointwise
clearing hypothesis** at each `t' ∈ D.T`, derive
`C1SupplierStrong_local C`.

The pointwise clearing hypothesis is the **single named arithmetic
residual** identified by T067 — the genuine Wedhorn 8.34(ii)
σ-product-clearing content. All non-arithmetic content is
discharged by this composition.

**Significance**: closes the Wedhorn 8.34(ii) C1 supplier route
entirely modulo the per-`v` pointwise clearing residual. With T067's
arithmetic discharge of the pointwise clearing, the chain becomes
unconditional. -/
theorem C1SupplierStrong_local_via_pointwise_clearing
    [DecidableEq A]
    (C : RationalCoveringData A)
    (h_per_call :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
      ∃ (_ : Aˣ) (f : A),
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
        ¬ v.vle f 0 ∧
        (∀ t' ∈ D.T, ∀ w ∈ Spa A A⁺,
          w.vle f C.base.s →
          w.vle (1 : A) t' →
          ¬ w.vle t' 0 →
          w.vle t' D.s) ∧
        (∀ w ∈ rationalOpen (insert f C.base.T) C.base.s,
          ∃ t' ∈ D.T,
            w ∈ rationalOpen ({(1 : A)} : Finset A) t')) :
    C1SupplierStrong_local C := by
  refine C1SupplierStrong_local_via_t_indexed_direct C ?_
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨σ_choice, f, hv_in_plus, hvf_nz, h_clearing, h_cover_t⟩ :=
    h_per_call D hD v hv t ht hvt hvD_s
  exact ⟨σ_choice, f, hv_in_plus, hvf_nz,
    per_piece_subset_adapter_from_pointwise_clearing
      C.base.T D.T C.base.s D.s f h_clearing, h_cover_t⟩

end ValuationSpectrum

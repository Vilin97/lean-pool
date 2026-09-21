/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornMPowerStructuralDataHonestFromLaurentPiece
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornMaxElementSDComparison

/-!
# Wedhorn 8.34(ii) cover-piece rational-bound interface for T021 (T036)

T036 bridges T035's rational-subset-condition-based α_T_D consumer
(`alpha_T_D_per_t_factored_chain_via_rational_open`, commit `8ffad58`)
together with T030's α_s_D consumer
(`alpha_s_D_per_t_factored_chain_via_lower_branch`, commit `89ac44c`)
into T028's per-Laurent-piece consumer interface
(`PerLaurentPieceFactoredChain`, commit `6c0678c`) and T021's
top-level honest structural supplier
(`WedhornMPowerStructuralDataHonest`).

The bridge is **option (1)/(2) hybrid** per the T036 ticket
preferences: a reusable theorem-level interface that produces
`PerLaurentPieceFactoredChain` from two **explicit per-`w` supplier
hypotheses** corresponding to the two T021 branches:

* **α_s_D supplier** (`h_lower`): `∀ w ∈ Spa(Loc s, ⁺), ∀ t' ∈
  T_D.image (algMap), w.vle t' (σ_loc : Loc s)` — every test-family
  element is in σ_loc's "≤ 1" half-space at every `w` (the V_∅ piece
  of the σ_loc-rescaled Laurent refinement at `T_D.image`).
* **α_T_D supplier** (`h_rational_subset`): `∀ w ∈ Spa(Loc s, ⁺),
  ∀ t ∈ T_D.image (algMap), w.vle t (algebraMap A (Loc s) s_D)` — the
  rational-subset condition `R(T_D.image (algMap), algMap s_D)` at
  every `w`.

The interface is composed with T028's
`WedhornMPowerStructuralDataHonest_via_localized_cor732_laurent_consumer`
to produce `WedhornMPowerStructuralDataHonest` from the standard
Cor 7.32 σ-strict-dom output plus the two cover-piece rational-bound
suppliers.

## Mathematical-orientation note

The two supplier hypotheses are stated **universally over
`Spa(Loc s, ⁺)`**, matching T028's `PerLaurentPieceFactoredChain`
universal quantifier. As documented in T035 (`WedhornMaxElementSDComparison`,
commit `8ffad58`), the rational-subset supplier is **not universally
true** on `Spa(Loc s, ⁺)` — see the concrete counter-example at
`A = ℚ_p, T_D = {1}, s_D = p` where `v.vle 1 p` fails at the standard
p-adic valuation.

The natural setting where both suppliers hold is **`w` in the cover
plus-piece** `R(insert f T_base, C_base_s)`, NOT all of
`Spa(Loc s, ⁺)`. T028's `PerLaurentPieceFactoredChain` (and hence
`WedhornMPowerStructuralDataHonest`) currently quantifies over all of
Spa, which is the **structural mismatch** identified by T034/T035.

This T036 interface preserves T028's signature and exposes the two
suppliers as **explicit hypotheses**: callers must supply them
universally, or restrict their downstream usage to settings where
both suppliers actually hold (e.g., explicit cover-piece membership).

## Definition-level next-step (out of T036's leaf scope)

A natural project-level cleanup is to **tighten T028/T021's universal
`∀ w ∈ Spa(Loc s, ⁺)` quantifier to range over the cover plus-piece**
`R(insert f T_base, C_base_s)`. Inside the cover plus-piece, both
suppliers (`h_lower` via Laurent-cover refinement at `T_D.image`,
`h_rational_subset` via the cover refinement target itself) are
naturally available. The tightened `WedhornMPowerStructuralDataHonest`
matches Wedhorn 8.34(ii)'s actual statement on PDF page 84 / Lemma
8.33's cover-level acyclicity. The exact downstream theorem that
becomes mechanical: `rationalOpen_subset_base_via_local_Cor732_chain`
(at `WedhornLocalCor732ToFactoredChain`) once T028's
`PerLaurentPieceFactoredChain` is restricted to cover plus-piece.

## What this file provides — theorems

* `PerLaurentPieceFactoredChain_via_cover_piece_data` — the bridge:
  produces `PerLaurentPieceFactoredChain` from the two universal
  per-`w` supplier hypotheses via case-split on `τ ∈
  localizedTestFamily` (`mem_localizedTestFamily_iff`).
* `WedhornMPowerStructuralDataHonest_via_cover_piece_data` — top-level
  composed wrapper. Takes Cor 7.32 σ-strict-dom + the two suppliers
  and produces `WedhornMPowerStructuralDataHonest` directly.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson /
  T001 / faithful-flatness / Zavyalov / bivariate-overlap content.
* No σ-power-decay revival.
* Imports only T028's `WedhornMPowerStructuralDataHonestFromLaurentPiece`
  and T035's `WedhornMaxElementSDComparison`. Both share T027 as a
  common ancestor.
* Does NOT edit T027/T028/T031/T032/T033/T034/T035 accepted files.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

omit [PlusSubring A] in
/-- **Bridge: `PerLaurentPieceFactoredChain` from cover-piece data**
(T036 main deliverable).

Produces T028's `PerLaurentPieceFactoredChain` residual from two
explicit universal-over-Spa supplier hypotheses corresponding to the
α_s_D and α_T_D branches:

* `h_lower` — α_s_D supplier (V_∅ at `T_D.image (algMap)` with
  denominator σ_loc): every element of `T_D.image (algMap)` is in
  σ_loc's "≤ 1" half-space at every `w`.
* `h_rational_subset` — α_T_D supplier (rational-subset condition
  `R(T_D.image (algMap), algMap s_D)`): every element of
  `T_D.image (algMap)` is bounded above by `algMap s_D` at every `w`.

The proof case-splits on `τ ∈ localizedTestFamily s T_D s_D` via
`mem_localizedTestFamily_iff`:

* α_s_D case (τ = `algMap s_D`): the consumer's Laurent-piece
  membership IS the α_s_D-branch input; combined with the lower-branch
  membership (built from `h_lower w hw_spa` + σ_loc unit
  non-vanishing), invoke T030's
  `alpha_s_D_per_t_factored_chain_via_lower_branch`.
* α_T_D case (τ ∈ `T_D.image (algMap)`): use the τ membership as the
  T_D.image nonemptiness witness; supply the rational-subset condition
  via `h_rational_subset w hw_spa`; invoke T035's
  `alpha_T_D_per_t_factored_chain_via_rational_open`.

The f-membership hypothesis of `PerLaurentPieceFactoredChain` is
**unused** in either branch's arithmetic at this leaf level — it is
threaded through but the per-`t'` σ-factored chain in both branches
follows from the supplier hypotheses + Laurent-piece data + finite
σ-cancellation arithmetic alone.

## Why both suppliers are required universally over Spa

T028's `PerLaurentPieceFactoredChain` quantifies over all `w ∈
Spa(Loc s, ⁺)`. To produce it via this bridge, the suppliers must hold
at every `w`, not just at `w` in some cover plus-piece. As documented
in the file's section docstring, this is the **structural mismatch**:
`h_rational_subset` is mathematically false uniformly on Spa, but it
is required to discharge T028's universal quantifier without a
definition-level signature change. -/
theorem PerLaurentPieceFactoredChain_via_cover_piece_data
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_lower :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle t' (σ_loc : Localization.Away s))
    (h_rational_subset :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∀ t ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle t (algebraMap A (Localization.Away s) s_D)) :
    PerLaurentPieceFactoredChain P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro τ hτ w hw_spa h_laurent_piece _h_f_membership t' ht'
  rw [mem_localizedTestFamily_iff] at hτ
  rcases hτ with rfl | hτ_in_T_D
  · -- α_s_D case: τ = algebraMap s_D. Use T030.
    have hw_lower :
        w ∈ rationalOpen
          (T_D.image (algebraMap A (Localization.Away s)))
          (σ_loc : Localization.Away s) :=
      ⟨hw_spa, h_lower w hw_spa,
        not_vle_zero_of_isUnit σ_loc.isUnit w⟩
    exact alpha_s_D_per_t_factored_chain_via_lower_branch
      P T s hopen T_D s_D σ_loc w h_laurent_piece hw_lower t' ht'
  · -- α_T_D case: τ ∈ T_D.image (algMap). Use T035.
    have hT_D_image_ne :
        (T_D.image (algebraMap A (Localization.Away s))).Nonempty :=
      ⟨τ, hτ_in_T_D⟩
    exact alpha_T_D_per_t_factored_chain_via_rational_open T_D s_D
      σ_loc w hT_D_image_ne (h_rational_subset w hw_spa) t' ht'

omit [PlusSubring A] in
/-- **Top-level: `WedhornMPowerStructuralDataHonest` from cover-piece
data** (T036 composed deliverable).

Composes the bridge `PerLaurentPieceFactoredChain_via_cover_piece_data`
with T028's
`WedhornMPowerStructuralDataHonest_via_localized_cor732_laurent_consumer`
to produce `WedhornMPowerStructuralDataHonest` from three natural
inputs:

* `hσ_loc_dom` — Cor 7.32 σ-strict-domination over
  `localizedTestFamily s T_D s_D` (the natural localized Cor 7.32
  output via `exists_dominating_unit_in_localization`).
* `h_lower` — α_s_D supplier (V_∅ at `T_D.image (algMap)` w.r.t.
  σ_loc).
* `h_rational_subset` — α_T_D supplier (rational-subset condition
  `R(T_D.image (algMap), algMap s_D)`).

This is the **strongest theorem-level T021 honest-structural-supplier
producer** achievable from existing API: the two cover-piece
rational-bound hypotheses (`h_lower` and `h_rational_subset`) are
exposed as the **single explicit downstream supplier obligation** for
Wedhorn 8.34(ii) Step 2. The remaining T021 work is producing these
two suppliers at every `w` in the relevant cover plus-piece — natural
in Wedhorn's actual proof on PDF page 84 / Lemma 8.33's cover-level
acyclicity, but currently outside `WedhornMPowerStructuralDataHonest`'s
universal-over-Spa signature. -/
theorem WedhornMPowerStructuralDataHonest_via_cover_piece_data
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (hσ_loc_dom :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s))
    (h_lower :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle t' (σ_loc : Localization.Away s))
    (h_rational_subset :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∀ t ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle t (algebraMap A (Localization.Away s) s_D)) :
    WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc :=
  WedhornMPowerStructuralDataHonest_via_localized_cor732_laurent_consumer
    P T s hopen T_D s_D σ_loc hσ_loc_dom
    (PerLaurentPieceFactoredChain_via_cover_piece_data
      P T s hopen T_D s_D σ_loc h_lower h_rational_subset)

end ValuationSpectrum

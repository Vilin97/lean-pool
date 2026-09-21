/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornC1CoverPieceStructuralAssembly

/-!
# Wedhorn 8.34(ii) — Per-w cover-piece C1 supplier interface (T039)

C1-level wrapper consuming the **explicit per-`w` cover-piece upper-
bound supplier** instead of the bundled
`WedhornCoverPieceStructuralData` Prop. Lifts T037's
`WedhornCoverPieceStructuralData_via_per_w_supplier` to the C1
per-call layer, so callers supply the genuine per-`w`-with-f-membership
per-`t'` upper bound directly and the wrapper threads it into T038's
top-level C1 theorem.

## Why this layering

T038's
`C1SupplierStrong_local_via_cover_piece_structural_data_residuals`
(commit `3789ead`) consumes T037's `WedhornCoverPieceStructuralData`
as component 5 of the per-call supply. T037's
`WedhornCoverPieceStructuralData_via_per_w_supplier` reduces that
Prop to a **per-`w`** supplier with f-membership and σ-strict-
domination as in-scope premises. This file performs the lift to the
C1 per-call layer: the new per-call predicate exposes the per-`w`
supplier explicitly, and the bridge / top-level theorem compose
T037's per-w bridge with T038's C1 wrapper.

## What this file provides

* `WedhornC1PerCallSupplyPerWCoverPiece` — per-call supply predicate
  mirroring T038's `WedhornC1PerCallSupplyCoverPiece` but replacing
  component 5 with the explicit per-`w` upper-bound supplier:
  `∀ w ∈ Spa(Loc C.base.s, ⁺), w.vle (σ_loc * ∏ D.T.image) (algebraMap C.base.s)
    → ∀ τ ∈ localizedTestFamily, w.vle σ_loc τ ∧ ¬ w.vle τ σ_loc
    → ∀ t ∈ D.T.image (algebraMap), w.vle t (algebraMap D.s)`.

* `WedhornC1PerCallSupplyCoverPiece_of_per_w_supplier` — bridge from
  the per-`w` supply to T038's
  `WedhornC1PerCallSupplyCoverPiece`. Uses T037's
  `WedhornCoverPieceStructuralData_via_per_w_supplier` to discharge
  component 5.

* `C1SupplierStrong_local_via_per_w_cover_piece_supplier` — top-level
  C1 theorem composing the bridge with T038's
  `C1SupplierStrong_local_via_cover_piece_structural_data_residuals`.

## Notes

* No root import; leaf-level.
* Imports only `WedhornC1CoverPieceStructuralAssembly` (T038, commit
  `3789ead`), which transitively brings in T037's
  `WedhornCoverPieceStructuralData` and bridge.
* No edits to T027–T038 accepted files, root imports, or final
  theorem signatures.
* No revival of global universal-over-Spa rational-bound claims,
  σ-power-decay, M-power-decay, T001/Lane-B, Cor 8.32/Jacobson,
  faithful-flatness, Zavyalov, or bivariate-overlap content.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Per-`w` cover-piece per-call C1 supply predicate**.

Mirrors T038's `WedhornC1PerCallSupplyCoverPiece` (commit `3789ead`)
but replaces component 5 with the explicit per-`w` upper-bound
supplier: at every `w ∈ Spa(Localization.Away C.base.s, ⁺)`
satisfying f-membership AND σ-strict-domination by some
`τ ∈ localizedTestFamily`, every `t ∈ D.T.image (algebraMap)` is
bounded above by `algebraMap D.s` at `w`. -/
def WedhornC1PerCallSupplyPerWCoverPiece
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
    -- (4) σ-strict-domination on local Spa (Cor 7.32 output).
    (∀ w ∈ Spa (Localization.Away C.base.s) (Localization.Away C.base.s)⁺,
        ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
          w.vle (σ_loc : Localization.Away C.base.s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away C.base.s)) ∧
    -- (5) PER-W explicit upper-bound supplier (the genuine residual).
    (∀ w ∈ Spa (Localization.Away C.base.s) (Localization.Away C.base.s)⁺,
        w.vle ((σ_loc : Localization.Away C.base.s) *
            (∏ t ∈ D.T.image (algebraMap A (Localization.Away C.base.s)), t))
          (algebraMap A (Localization.Away C.base.s) C.base.s) →
        ∀ τ ∈ localizedTestFamily C.base.s D.T D.s,
          w.vle (σ_loc : Localization.Away C.base.s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away C.base.s) →
          ∀ t ∈ D.T.image (algebraMap A (Localization.Away C.base.s)),
            w.vle t (algebraMap A (Localization.Away C.base.s) D.s)) ∧
    -- (6a) Clause 1 of C1: v ∈ R(insert f C.base.T, C.base.s).
    v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
    -- (6b) Clause 3 of C1: ¬ v.vle f 0.
    ¬ v.vle f 0

/-- **Bridge: per-`w` cover-piece supply → T038 cover-piece supply**.

From `WedhornC1PerCallSupplyPerWCoverPiece` produce
`WedhornC1PerCallSupplyCoverPiece` (T038, commit `3789ead`) by
discharging component 5 (the bundled `WedhornCoverPieceStructuralData`
Prop) via T037's
`WedhornCoverPieceStructuralData_via_per_w_supplier`. The other six
components are unchanged. -/
theorem WedhornC1PerCallSupplyCoverPiece_of_per_w_supplier
    [DecidableEq A]
    (P : PairOfDefinition A)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (D : RationalLocData A) (v : Spv A)
    (h_per_w : WedhornC1PerCallSupplyPerWCoverPiece P C hopen_base D v) :
    WedhornC1PerCallSupplyCoverPiece P C hopen_base D v := by
  letI : TopologicalSpace (Localization.Away C.base.s) :=
    locTopology P C.base.T C.base.s hopen_base
  letI : PlusSubring (Localization.Away C.base.s) :=
    localizationLocSubringPlusSubring P C.base.T C.base.s
  letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
  obtain ⟨σ_loc, f, h_alg, h_dom, h_per_t_le_s_D, hv_in_plus, hvf_nz⟩ := h_per_w
  refine ⟨σ_loc, f, h_alg, h_dom, ?_, hv_in_plus, hvf_nz⟩
  exact WedhornCoverPieceStructuralData_via_per_w_supplier
    P C.base.T C.base.s hopen_base D.T D.s σ_loc h_per_t_le_s_D

/-- **Top-level C1 supplier theorem via per-`w` cover-piece supplier**.

Identical caller signature to T038's
`C1SupplierStrong_local_via_cover_piece_structural_data_residuals`,
modulo the per-call supply predicate:
`WedhornC1PerCallSupplyPerWCoverPiece` replaces
`WedhornC1PerCallSupplyCoverPiece`. Internally lifts each per-call
supply via `WedhornC1PerCallSupplyCoverPiece_of_per_w_supplier`, then
applies T038. -/
theorem C1SupplierStrong_local_via_per_w_cover_piece_supplier
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (h_per_call_supply :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        WedhornC1PerCallSupplyPerWCoverPiece P C hopen_base D v) :
    C1SupplierStrong_local C :=
  C1SupplierStrong_local_via_cover_piece_structural_data_residuals
    P hA₀_le C hopen_base
    (fun D hD v hv t ht hvt hvD_s ↦
      WedhornC1PerCallSupplyCoverPiece_of_per_w_supplier P C hopen_base D v
        (h_per_call_supply D hD v hv t ht hvt hvD_s))

end ValuationSpectrum

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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornStrengthenedC1
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornCoverPieceStructuralData

/-!
# Wedhorn 8.34(ii) — Cover-piece source-restricted C1 supplier interface (T038)

C1-level wrapper consuming T037's source-restricted structural data
(`WedhornCoverPieceStructuralData`, commit `4cff9cb`) instead of the
old global `WedhornMPowerStructuralDataHonest` or T036's universal-
over-Spa suppliers. Mirrors the predicate/wrapper shape of T020's
`WedhornC1PerCallSupplyHonest` / `C1SupplierStrong_local_via_honest_residuals`,
swapping component 5 to the source-restricted Prop and using T037's
`rationalOpen_subset_base_via_cover_piece_structural_data` for clause
2 of the C1 conclusion.

## Why source-restricted at the C1 layer

T035's counter-example (`A = ℚ_p, T_D = {1}, s_D = p`) showed that
universal-over-Spa per-`t'` upper bounds against `algebraMap s_D` are
mathematically false. T037 fixed this by carrying the f-membership
and σ-strict-domination premises **inside** the structural-data
quantifier, so the per-`t'` conclusion is required only at `w` in the
cover plus-piece (where both premises hold). Lifting this honest
shape to the C1 per-call layer drops T036's parked universal premises
in favour of T037's per-`w` source-restricted form.

## What this file provides

* `WedhornC1PerCallSupplyCoverPiece` — per-call supply predicate
  mirroring `WedhornC1PerCallSupplyHonest` (commit `635a2c5`) but
  replacing component 5 with `WedhornCoverPieceStructuralData`.
  Components: σ_loc, f, the denominator-cleared identity, σ-strict-
  domination, T037's source-restricted structural data, source-side
  rational-open membership of `v` and non-degeneracy of `f` at `v`.

* `C1SupplierStrong_local_via_cover_piece_structural_data_residuals`
  — top-level C1 supplier theorem composing the per-call supply with
  `rationalOpen_subset_base_via_cover_piece_structural_data` (T037)
  for clause 2; clauses 1 and 3 come from the predicate.

## Notes

* No root import; leaf-level.
* Imports only `WedhornStrengthenedC1` (for `C1SupplierStrong_local`)
  and `WedhornCoverPieceStructuralData` (T037).
* No edits to T027–T037 accepted files, root imports, or final
  theorem signatures.
* No revival of σ-power-decay, M-power-decay, T036's universal-over-
  Spa rational-bound claims, T001/Lane-B, Cor 8.32/Jacobson, faithful-
  flatness, Zavyalov, or bivariate-overlap content.
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Cover-piece source-restricted per-call C1 supply predicate**.

Mirrors `WedhornC1PerCallSupplyHonest` (commit `635a2c5`) with
component 5 replaced by T037's `WedhornCoverPieceStructuralData`
(source-restricted per-(τ, w) Prop with f-membership and σ-strict-
domination as in-scope premises). The other six components are
unchanged: σ_loc + f + denominator-cleared identity + σ-strict-
domination on the localized Spa + source-side rational-open
membership of `v` + non-vanishing of `f` at `v`. -/
def WedhornC1PerCallSupplyCoverPiece
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
    -- (5) T037 SOURCE-RESTRICTED structural data.
    WedhornCoverPieceStructuralData P C.base.T C.base.s hopen_base
      D.T D.s σ_loc ∧
    -- (6a) Clause 1 of C1: v ∈ R(insert f C.base.T, C.base.s).
    v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
    -- (6b) Clause 3 of C1: ¬ v.vle f 0.
    ¬ v.vle f 0

/-- **Top-level C1 supplier theorem via T037 source-restricted
structural data**.

Identical caller signature to
`C1SupplierStrong_local_via_honest_residuals` (commit `635a2c5`),
modulo the per-call supply predicate: `WedhornC1PerCallSupplyCoverPiece`
replaces `WedhornC1PerCallSupplyHonest`. Internally feeds the
source-restricted Prop through
`rationalOpen_subset_base_via_cover_piece_structural_data` (T037,
commit `4cff9cb`) for clause 2 of the C1 conclusion; clauses 1 and 3
read directly from the predicate. -/
theorem C1SupplierStrong_local_via_cover_piece_structural_data_residuals
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (h_per_call_supply :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        WedhornC1PerCallSupplyCoverPiece P C hopen_base D v) :
    C1SupplierStrong_local C := by
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨σ_loc, f, h_alg, h_dom, h_struct, hv_in_plus, hvf_nz⟩ :=
    h_per_call_supply D hD v hv t ht hvt hvD_s
  refine ⟨f, hv_in_plus, ?_, hvf_nz⟩
  exact rationalOpen_subset_base_via_cover_piece_structural_data
    P C.base.T C.base.s hopen_base hA₀_le C.base.T D.T D.s
    (Finset.Subset.refl _) f σ_loc h_alg h_dom h_struct

end ValuationSpectrum

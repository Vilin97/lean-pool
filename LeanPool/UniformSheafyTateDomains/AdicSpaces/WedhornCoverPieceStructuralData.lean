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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornCoverPieceRationalBoundInterface

/-!
# Wedhorn 8.34(ii) cover-piece source-restricted structural data (T037)

T037 lands the **source-restricted** Wedhorn 8.34(ii) structural-data
API: a Prop matching the local-chain compatibility shape consumed by
`rationalOpen_subset_base_via_local_Cor732_chain`, with the f-membership
premise `w.vle (σ_loc * ∏ T_D.image) (algebraMap s)` and the
σ-strict-domination premise both in scope **before** the per-`t'`
conclusions are required. This tightens T036's universal-over-Spa
suppliers (commit `4ec9dba`, mathematically too strong on Spa per
T035's counter-example) to **per-`w` suppliers conditioned on f-
membership** — the natural "cover plus-piece" shape.

## Source-restricted Prop shape

The Prop `WedhornCoverPieceStructuralData` exactly matches the
`_h_T_test_compat_loc` parameter of
`rationalOpen_subset_base_via_local_Cor732_chain` (in
`WedhornLocalPerBranchChain.lean`) with `T_test_loc` specialised to
`localizedTestFamily s T_D s_D`. It quantifies per-(τ, w) over
`(localizedTestFamily, Spa(Loc s, ⁺))` with f-membership and
σ-strict-domination as **per-`w` premises**, so the conclusion is
required only at `w` in the cover plus-piece (where f-membership at
`w` holds against `algebraMap s`).

## Why this fixes T036's mismatch

T036's suppliers (`h_lower`, `h_rational_subset`) were universal over
all of `Spa(Loc s, ⁺)`, mathematically false in general (per T035's
counter-example at `A = ℚ_p, T_D = {1}, s_D = p`). The suppliers
become true at `w` where f-membership AND σ-strict-domination by
some `τ ∈ localizedTestFamily` hold — i.e., at `w` in the source
cover plus-piece. T037's source-restricted Prop carries those two
premises explicitly, lifting T036's bridge to a per-`w` form that is
actually achievable.

## Caller-friendly direct subset theorem

The companion theorem
`rationalOpen_subset_base_via_cover_piece_structural_data` composes
the source-restricted Prop with `rationalOpen_subset_base_via_local_Cor732_chain`,
producing the base rational-open inclusion
`rationalOpen (insert f T_base) s ⊆ rationalOpen T_D s_D` from:

* Standard Cor 7.32 setup data.
* `h_alg` — the canonical denominator-cleared algebraic identity
  `algebraMap f = σ_loc * ∏ T_D.image (algebraMap)`.
* Cor 7.32 σ-strict-domination over `localizedTestFamily s T_D s_D`.
* The source-restricted structural-data Prop.

This is the **source-restricted analogue** of
`rationalOpen_subset_base_via_M_power_decay` (in
`WedhornLocalCor732ToFactoredChain.lean`), with the M-power-decay
residual replaced by the cleaner per-`t'` upper bound + s_D
non-vanishing shape.

## What this file provides

* `WedhornCoverPieceStructuralData` — the source-restricted Prop,
  matching `_h_T_test_compat_loc`'s shape with `T_test_loc =
  localizedTestFamily s T_D s_D`.
* `WedhornCoverPieceStructuralData_via_per_w_supplier` — bridge from
  per-`w`-with-f-membership suppliers (α_s_D `h_lower_at_w` and α_T_D
  `h_rational_subset_at_w`) to the source-restricted Prop. Mirrors
  T036's bridge but with per-`w` f-membership-conditional suppliers.
* `rationalOpen_subset_base_via_cover_piece_structural_data` —
  caller-friendly direct subset theorem composing the
  source-restricted Prop with
  `rationalOpen_subset_base_via_local_Cor732_chain`.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson /
  T001 / faithful-flatness / Zavyalov / bivariate-overlap content.
* No σ-power-decay revival.
* Imports T036's `WedhornCoverPieceRationalBoundInterface` (commit
  `4ec9dba`), which transitively brings in T028's per-piece consumer,
  T035's α_T_D rational-open wrapper, T030's α_s_D lower-branch
  consumer, and the local-chain APIs via T027.
* Does NOT edit T027/T028/T031/T032/T033/T034/T035/T036 accepted
  files.
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

/-- **Source-restricted Wedhorn structural data Prop**.

Per-(τ, w) statement with τ ∈ `localizedTestFamily s T_D s_D` and
`w ∈ Spa(Loc s, ⁺)`. Carries the f-membership premise
`w.vle (σ_loc * ∏ T_D.image) (algebraMap s)` and the σ-strict-domination
premise `w.vle σ_loc τ ∧ ¬ w.vle τ σ_loc` **before** asking for the
per-`t'` conclusion.

Conclusion at every (τ, w) under both premises:

* `∀ t' ∈ T_D.image (algebraMap), w.vle t' (algebraMap s_D)` — the
  per-`t'` upper bound by `algebraMap s_D`;
* `¬ w.vle (algebraMap s_D) 0` — `algebraMap s_D` non-vanishing at `w`.

Matches the `_h_T_test_compat_loc` parameter of
`rationalOpen_subset_base_via_local_Cor732_chain` with `T_test_loc =
localizedTestFamily s T_D s_D`. -/
def WedhornCoverPieceStructuralData
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ τ ∈ localizedTestFamily s T_D s_D,
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s) →
      w.vle (σ_loc : Localization.Away s) τ ∧
        ¬ w.vle τ (σ_loc : Localization.Away s) →
        (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
            w.vle t' (algebraMap A (Localization.Away s) s_D)) ∧
          ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0

omit [PlusSubring A] in
/-- **Bridge: source-restricted structural data from per-`w`
f-membership-conditional suppliers** (T037 main bridge).

Constructs `WedhornCoverPieceStructuralData` from two per-`w` suppliers
that are conditioned on the f-membership premise (and may also use the
σ-strict-domination premise):

* `h_per_t_le_s_D_at_w` — per-`w` rational-subset-condition supplier:
  at every `w ∈ Spa(Loc s, ⁺)` satisfying f-membership AND with
  σ-strict-domination by some τ ∈ `localizedTestFamily s T_D s_D`,
  every `t ∈ T_D.image (algebraMap)` is bounded above by
  `algebraMap s_D` at `w`.

The proof case-splits on `τ ∈ localizedTestFamily` via
`mem_localizedTestFamily_iff`:

* α_s_D case (τ = `algebraMap s_D`): `¬ algebraMap s_D 0` is
  auto-derived via `not_vle_zero_of_strict_dominator` from the
  σ-strict-dom-by-`algebraMap s_D` premise.
* α_T_D case (τ ∈ `T_D.image`): `¬ algebraMap s_D 0` is auto-derived
  from the per-`t` bound (applied at the σ-strict-dom witness τ
  itself, which is non-vanishing by `not_vle_zero_of_strict_dominator`)
  via transitivity.

In both branches the per-`t'` upper bound is supplied directly by
`h_per_t_le_s_D_at_w`. -/
theorem WedhornCoverPieceStructuralData_via_per_w_supplier
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_per_t_le_s_D_at_w :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        ∀ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s) →
          ∀ t ∈ T_D.image (algebraMap A (Localization.Away s)),
            w.vle t (algebraMap A (Localization.Away s) s_D)) :
    WedhornCoverPieceStructuralData P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro τ hτ w hw_spa hw_f hστ
  have h_per_t :
      ∀ t ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle t (algebraMap A (Localization.Away s) s_D) :=
    h_per_t_le_s_D_at_w w hw_spa hw_f τ hτ hστ
  refine ⟨h_per_t, ?_⟩
  rw [mem_localizedTestFamily_iff] at hτ
  rcases hτ with rfl | hτ_in_T_D
  · -- α_s_D case: τ = algebraMap s_D. Direct from σ-strict-dom.
    exact not_vle_zero_of_strict_dominator hστ.2
  · -- α_T_D case: τ ∈ T_D.image. Use per-t bound at t = τ + non-vanishing of τ.
    intro h_s_D_zero
    apply not_vle_zero_of_strict_dominator hστ.2
    exact w.vle_trans (h_per_t τ hτ_in_T_D) h_s_D_zero

/-- **Caller-friendly direct subset theorem via source-restricted
structural data** (T037 composed deliverable).

Composes `WedhornCoverPieceStructuralData` directly with
`rationalOpen_subset_base_via_local_Cor732_chain` (in
`WedhornLocalPerBranchChain.lean`), specialising the latter's
`T_test_loc` to `localizedTestFamily s T_D s_D`. Produces the base
rational-open inclusion `rationalOpen (insert f T_base) s ⊆
rationalOpen T_D s_D` from:

* Standard Tate / Cor 7.32 setup data (`P`, `T`, `s`, `hopen`,
  `hA₀_le`, `T_base`, `T_D`, `s_D`, `h_T_le_T_base`).
* `f`, `σ_loc`, `h_alg` — the candidate `f` plus the canonical
  denominator-cleared algebraic identity
  `algebraMap f = σ_loc * ∏ T_D.image (algebraMap)`.
* `hσ_loc_dom` — Cor 7.32 σ-strict-domination over
  `localizedTestFamily s T_D s_D` (the natural localized Cor 7.32
  output).
* `h_struct` — the source-restricted structural data Prop.

This is the **source-restricted analogue** of
`rationalOpen_subset_base_via_M_power_decay`, with the M-power-decay
residual cleanly factored as the per-`t'` upper bound + s_D
non-vanishing under f-membership. -/
theorem rationalOpen_subset_base_via_cover_piece_structural_data
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (hA₀_le : P.A₀ ≤ A⁺)
    (T_base T_D : Finset A) (s_D : A)
    (h_T_le_T_base : T ⊆ T_base)
    (f : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_alg :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      algebraMap A (Localization.Away s) f =
        (σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
    (hσ_loc_dom :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s))
    (h_struct :
      WedhornCoverPieceStructuralData P T s hopen T_D s_D σ_loc) :
    rationalOpen (insert f T_base) s ⊆ rationalOpen T_D s_D :=
  rationalOpen_subset_base_via_local_Cor732_chain P T s hopen hA₀_le
    T_base T_D s_D h_T_le_T_base f σ_loc h_alg
    (localizedTestFamily s T_D s_D) hσ_loc_dom h_struct

end ValuationSpectrum

/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornPerWCoverPieceUpperBound

/-!
# Wedhorn 8.34(ii) — Discharge of `WedhornCoverPieceLocRationalBound`
via σ-strict-domination and the V_K-nonempty residual (T041)

T040 (commit `d2aa5d9`) introduced `WedhornCoverPieceLocRationalBound`,
the source-restricted localized rational-bound predicate underlying the
T039 / T038 cover-piece C1 supplier interface. This file lands the
**honest discharge structure** for that predicate by:

1. Discharging the V_∅ branch of T031's full-Laurent V_K decomposition
   directly from σ-strict-domination + transitivity.
2. Stating the **V_K-nonempty rational-bound residual** as a fresh
   source-restricted predicate
   `WedhornCoverPieceVKNonemptyRationalBound`, conditioned on the
   V_K-nonempty witness (existence of `t_K ∈ T_D.image (algebraMap)` with
   `w.vle σ_loc t_K ∧ ¬ w.vle t_K σ_loc`) — i.e., applicable only on
   the genuinely difficult branch.
3. Bridging the V_K-nonempty residual together with the standard
   universal-over-Spa σ-strict-domination output of Cor 7.32 to
   `WedhornCoverPieceLocRationalBound`, internally case-splitting on
   T031's `laurent_VK_branch_decomposition_at`.

## Why this factoring

In the **V_∅ branch** at `w` (every `t ∈ T_D.image (algebraMap)` lies
in `σ_loc`'s "≤ 1" half-space), σ-strict-domination forces the
test-family witness τ to be `algebraMap s_D`: σ-strict-dom by some
`τ ∈ T_D.image` is incompatible with V_∅ at τ (which gives
`w.vle τ σ_loc`). So the conclusion follows by simple transitivity
`w.vle t σ_loc ≤ algebraMap s_D` using the V_∅ premise and
σ-strict-dom by `algebraMap s_D`. The V_∅ branch is mechanically
discharged here.

In the **V_K-nonempty branch** at `w`, neither σ-strict-dom nor f-
membership pins the per-`t` bound at `algebraMap s_D` (this is exactly
the structural mismatch documented in T034's docstring and T035's
counter-example). The V_K-nonempty residual is the genuine remaining
mathematical content; it captures Wedhorn 7.45's deduction in the
α_T_D-style branch, restricted to the cover plus-piece.

Factoring T040's predicate into "V_∅ + V_K-nonempty residual" gives
the cleanest statement of the remaining content:
* **Provable now**: V_∅-branch + σ-strict-dom + transitivity.
* **Genuine residual**: V_K-nonempty branch with f-membership + V_K
  witness ⇒ per-`t` upper bound at `algebraMap s_D`.

## What this file provides

* `WedhornCoverPieceVKNonemptyRationalBound` — the V_K-nonempty residual
  predicate. Source-restricted by f-membership AND V_K-nonempty
  witness. The genuine remaining mathematical content for Wedhorn
  8.34(ii) Step 2 at the C1 layer.

* `WedhornCoverPieceLocRationalBound_via_VK_residual` — the main
  bridge: from σ-strict-domination universal over `Spa(Loc s, ⁺)`
  (the standard Cor 7.32 / `exists_dominating_unit_in_localization`
  output) and the V_K-nonempty residual, derive
  `WedhornCoverPieceLocRationalBound`. V_∅ branch dispatched by
  σ-strict-dom + transitivity.

* `WedhornC1PerCallSupplyPerWCoverPiece_via_VK_residual` — per-call
  composition producing T039's `WedhornC1PerCallSupplyPerWCoverPiece`
  from σ_loc, f, h_alg, h_dom (which doubles as σ-strict-dom),
  `h_VK_residual`, hv_in_plus, hvf_nz. The σ-strict-dom hypothesis
  serves both as component 4 of T039's predicate and as the V_∅
  branch discharge witness internally.

* `C1SupplierStrong_local_via_VK_residual` — top-level C1 caller
  producing `C1SupplierStrong_local C` from per-call delivery of the
  components above. Composes with T040's
  `C1SupplierStrong_local_via_loc_rational_bound`.

## Notes

* No root import; leaf-level.
* Imports only `WedhornPerWCoverPieceUpperBound` (T040, commit
  `d2aa5d9`), which transitively brings in T031's
  `laurent_VK_branch_decomposition_at`,
  `mem_localizedTestFamily_iff`, and the per-`w` cover-piece supplier
  interface.
* No edits to T027–T040 accepted files, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* The V_K-nonempty residual is the **single explicit remaining
  mathematical residual** at this layer; the V_∅ branch is fully
  discharged here.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **V_K-nonempty rational-bound residual predicate** (T041 source-
restricted residual).

At every `w ∈ Spa(Localization.Away s, ⁺)` satisfying:

* the f-membership premise `w.vle (σ_loc * ∏ T_D.image (algebraMap))
  (algebraMap s)`, AND
* the V_K-nonempty witness `∃ t_K ∈ T_D.image (algebraMap),
  w.vle σ_loc t_K ∧ ¬ w.vle t_K σ_loc`,

every element of `T_D.image (algebraMap)` is bounded above by
`algebraMap s_D` at `w`.

This is the **V_K-nonempty branch** of T040's
`WedhornCoverPieceLocRationalBound` — the genuine remaining
mathematical content for Wedhorn 8.34(ii) Step 2 at the C1 layer. The
V_∅ branch is dispatched directly from σ-strict-domination +
transitivity in the bridge theorem below, leaving this residual as
the only non-mechanical piece. -/
def WedhornCoverPieceVKNonemptyRationalBound
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
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    w.vle ((σ_loc : Localization.Away s) *
        (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
      (algebraMap A (Localization.Away s) s) →
    (∃ t_K ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle (σ_loc : Localization.Away s) t_K ∧
        ¬ w.vle t_K (σ_loc : Localization.Away s)) →
    ∀ t ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle t (algebraMap A (Localization.Away s) s_D)

omit [PlusSubring A] in
/-- **Bridge: T040's `WedhornCoverPieceLocRationalBound` from
σ-strict-domination + V_K-nonempty residual** (T041 main bridge).

From two honest source-restricted hypotheses:

* `h_strict_dom` — universal-over-Spa σ-strict-domination on
  `Spa(Localization.Away s, ⁺)` over the canonical test family
  `localizedTestFamily s T_D s_D`. This is the standard output of
  Cor 7.32 / `exists_dominating_unit_in_localization`.

* `h_VK_residual` — the V_K-nonempty rational-bound residual
  (`WedhornCoverPieceVKNonemptyRationalBound`).

derive `WedhornCoverPieceLocRationalBound P T s hopen T_D s_D σ_loc`.

**Proof**: case-split on T031's `laurent_VK_branch_decomposition_at`
at `w`:
* **V_∅ branch** (`∀ t' ∈ T_D.image (algebraMap), w.vle t' σ_loc`):
  Use σ-strict-dom + `mem_localizedTestFamily_iff` to extract τ.
  - α_s_D case (τ = `algebraMap s_D`): `w.vle σ_loc (algebraMap s_D)`
    by σ-strict-dom; transitivity with V_∅ gives the per-`t` bound.
  - α_T_D case (τ ∈ `T_D.image (algebraMap)`): contradiction —
    σ-strict-dom gives `¬ w.vle τ σ_loc`, V_∅ gives `w.vle τ σ_loc`.
* **V_K-nonempty branch**: discharge via `h_VK_residual`. -/
theorem WedhornCoverPieceLocRationalBound_via_VK_residual
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_strict_dom :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s))
    (h_VK_residual :
      WedhornCoverPieceVKNonemptyRationalBound P T s hopen T_D s_D σ_loc) :
    WedhornCoverPieceLocRationalBound P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_f t ht
  rcases laurent_VK_branch_decomposition_at T_D σ_loc w with
    h_V_empty | h_V_nonempty
  · -- V_∅ branch: use σ-strict-dom; the only consistent τ is algebraMap s_D.
    obtain ⟨τ, hτ, hστ⟩ := h_strict_dom w hw_spa
    rw [mem_localizedTestFamily_iff] at hτ
    rcases hτ with rfl | hτ_in_T_D
    · -- α_s_D case: σ < algebraMap s_D; transitivity with V_∅.
      exact w.vle_trans (h_V_empty t ht) hστ.1
    · -- α_T_D case: V_∅ at τ gives w.vle τ σ_loc, contradicting σ-strict-dom.
      exact absurd (h_V_empty τ hτ_in_T_D) hστ.2
  · -- V_K-nonempty branch: discharge via h_VK_residual.
    exact h_VK_residual w hw_spa hw_f h_V_nonempty t ht

/-- **Per-call assembly: `WedhornC1PerCallSupplyPerWCoverPiece` via
σ-strict-domination + V_K-nonempty residual** (T041 composed
deliverable).

Produces T039's per-call supply predicate from the seven natural
components, with the V_K-nonempty residual `h_VK_residual` taking the
place of T040's `h_loc_bound`. The σ-strict-domination hypothesis
`h_dom` (component 4 of T039's predicate) doubles as the universal
σ-strict-dom witness for the V_∅ branch dispatch in T041's main bridge,
so no extra hypothesis is required at this layer.

The V_K-nonempty residual is the **single explicit mathematical
residual**; the other six components are routine Cor 7.32 /
denominator-clearing / base-side data. -/
theorem WedhornC1PerCallSupplyPerWCoverPiece_via_VK_residual
    [DecidableEq A]
    (P : PairOfDefinition A) (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (D : RationalLocData A) (v : Spv A) :
    letI : TopologicalSpace (Localization.Away C.base.s) :=
      locTopology P C.base.T C.base.s hopen_base
    letI : PlusSubring (Localization.Away C.base.s) :=
      localizationLocSubringPlusSubring P C.base.T C.base.s
    letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
    ∀ (σ_loc : (Localization.Away C.base.s)ˣ) (f : A)
      (_h_alg : algebraMap A (Localization.Away C.base.s) f =
        (σ_loc : Localization.Away C.base.s) *
          (∏ τ ∈ D.T.image (algebraMap A (Localization.Away C.base.s)), τ))
      (_h_dom : ∀ w ∈ Spa (Localization.Away C.base.s)
            (Localization.Away C.base.s)⁺,
        ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
          w.vle (σ_loc : Localization.Away C.base.s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away C.base.s))
      (_h_VK_residual :
        WedhornCoverPieceVKNonemptyRationalBound P C.base.T C.base.s
          hopen_base D.T D.s σ_loc)
      (_hv_in_plus : v ∈ rationalOpen (insert f C.base.T) C.base.s)
      (_hvf_nz : ¬ v.vle f 0),
      WedhornC1PerCallSupplyPerWCoverPiece P C hopen_base D v := by
  letI : TopologicalSpace (Localization.Away C.base.s) :=
    locTopology P C.base.T C.base.s hopen_base
  letI : PlusSubring (Localization.Away C.base.s) :=
    localizationLocSubringPlusSubring P C.base.T C.base.s
  letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
  intro σ_loc f h_alg h_dom h_VK_residual hv_in_plus hvf_nz
  exact WedhornC1PerCallSupplyPerWCoverPiece_of_loc_rational_bound
    P C hopen_base D v σ_loc f h_alg h_dom
    (WedhornCoverPieceLocRationalBound_via_VK_residual P C.base.T
      C.base.s hopen_base D.T D.s σ_loc h_dom h_VK_residual)
    hv_in_plus hvf_nz

/-- **Top-level: `C1SupplierStrong_local C` via σ-strict-domination +
V_K-nonempty residual** (T041 final deliverable).

Identical caller signature to T040's
`C1SupplierStrong_local_via_loc_rational_bound`, modulo the per-call
supply: each per-call delivery provides the V_K-nonempty residual
`WedhornCoverPieceVKNonemptyRationalBound` in place of T040's
full-strength `WedhornCoverPieceLocRationalBound`. The V_∅ branch is
discharged automatically inside the bridge using the supplied σ-strict-
domination hypothesis (component 4 of T039's predicate, doubly used
here as universal V_∅ witness).

Composes
`WedhornC1PerCallSupplyPerWCoverPiece_via_VK_residual` with T040's
`C1SupplierStrong_local_via_loc_rational_bound`-style flow through
T039's `C1SupplierStrong_local_via_per_w_cover_piece_supplier`. The
V_K-nonempty residual is the **single explicit remaining mathematical
residual** for Wedhorn 8.34(ii) Step 2 at the C1 layer; honest
discharge corresponds to Wedhorn 7.45's α_T_D-style cover-refinement
deduction restricted to the V_K-nonempty cover plus-piece. -/
theorem C1SupplierStrong_local_via_VK_residual
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (h_per_call_components :
      letI : TopologicalSpace (Localization.Away C.base.s) :=
        locTopology P C.base.T C.base.s hopen_base
      letI : PlusSubring (Localization.Away C.base.s) :=
        localizationLocSubringPlusSubring P C.base.T C.base.s
      letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
      ∃ (σ_loc : (Localization.Away C.base.s)ˣ) (f : A),
        algebraMap A (Localization.Away C.base.s) f =
          (σ_loc : Localization.Away C.base.s) *
            (∏ τ ∈ D.T.image (algebraMap A (Localization.Away C.base.s)), τ) ∧
        (∀ w ∈ Spa (Localization.Away C.base.s)
            (Localization.Away C.base.s)⁺,
          ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
            w.vle (σ_loc : Localization.Away C.base.s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away C.base.s)) ∧
        WedhornCoverPieceVKNonemptyRationalBound P C.base.T C.base.s
          hopen_base D.T D.s σ_loc ∧
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
        ¬ v.vle f 0) :
    C1SupplierStrong_local C := by
  letI : TopologicalSpace (Localization.Away C.base.s) :=
    locTopology P C.base.T C.base.s hopen_base
  letI : PlusSubring (Localization.Away C.base.s) :=
    localizationLocSubringPlusSubring P C.base.T C.base.s
  letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
  refine C1SupplierStrong_local_via_loc_rational_bound P hA₀_le C
    hopen_base ?_
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨σ_loc, f, h_alg, h_dom, h_VK_residual, hv_in_plus, hvf_nz⟩ :=
    h_per_call_components D hD v hv t ht hvt hvD_s
  exact ⟨σ_loc, f, h_alg, h_dom,
    WedhornCoverPieceLocRationalBound_via_VK_residual P C.base.T
      C.base.s hopen_base D.T D.s σ_loc h_dom h_VK_residual,
    hv_in_plus, hvf_nz⟩

end ValuationSpectrum

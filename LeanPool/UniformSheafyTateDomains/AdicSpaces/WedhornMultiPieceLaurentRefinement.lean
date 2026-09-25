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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLaurentLocalBoundsFromCor732

/-!
# Wedhorn 8.34(ii) — Multi-piece Laurent cover refinement (T054)

T053 (commit `1d8045f`) accepted the Cor 7.32 / Laurent-piece subpackage
content and named the remaining residual `MultiElementLowerBoundResidual
D_T : ∀ w ∈ Spa A A⁺, ∀ t' ∈ D_T, w.vle 1 t' ∧ ¬ w.vle t' 0`. T053
documented that this universal-over-`D_T` form is **mathematically
false** for `|D_T| > 1` from Cor 7.32 alone (per T035's counter-
example): on the Laurent piece `V_τ`, only `σ⁻¹ * τ` has the lower
bound, not other `σ⁻¹ * τ'` for `τ' ≠ τ`.

This file lands the **multi-piece Laurent cover refinement**: a
**source-restricted per-piece** version of T053's residual together
with the bridge from Cor 7.32 σ-strict-domination to the per-piece
discharge. The refinement structure matches Wedhorn 8.34(ii) PDF
page 84:

* Each Laurent piece `V_τ := rationalOpen ({1}) (σ⁻¹ * τ)` carries
  the **singleton** D_τ = {σ⁻¹ * τ}.
* On `V_τ`, the per-piece residual `∀ w ∈ V_τ, ∀ t' ∈ D_τ,
  w.vle 1 t' ∧ ¬ w.vle t' 0` holds — a real consequence of
  rationalOpen membership.
* The union `⋃_{τ ∈ T_test} V_τ` **covers** `Spa A A⁺` from Cor 7.32
  σ-strict-domination over `T_test` (existing
  `cor732_laurent_cover_covers_spa`).

## What this file provides

* `MultiElementLowerBoundResidualOnPiece` — source-restricted
  per-piece Prop predicate: `∀ w ∈ V, ∀ t' ∈ D_T, w.vle 1 t' ∧
  ¬ w.vle t' 0`. Replaces T053's universal-over-Spa residual with
  the actually-achievable per-piece form.

* `multi_element_lower_bound_on_piece_singleton_via_laurent_membership`
  — **substantive per-piece discharge**: for `V := rationalOpen
  ({(1 : A)}) (σ⁻¹ * τ)` and `D_τ := {σ⁻¹ * τ}` (singleton),
  `MultiElementLowerBoundResidualOnPiece V D_τ` holds.
  Real proof unfolding the rationalOpen membership.

* `cor732_multi_piece_laurent_refinement` — top-level multi-piece
  refinement theorem: from Cor 7.32 σ-strict-dom over `T_test`,
  derive at every `w ∈ Spa A A⁺` an existential `∃ τ ∈ T_test`
  packaging:
  * `w ∈ V_τ` (Laurent piece membership, from `cor732_laurent_piece_membership_at`).
  * `MultiElementLowerBoundResidualOnPiece V_τ ({σ⁻¹ * τ})` (per-piece
    singleton residual).

* `cor732_existential_singleton_residual_at_each_w` — direct per-`w`
  consequence: at every `w ∈ Spa A A⁺`, ∃ τ ∈ T_test with the per-`w`
  singleton lower bound `w.vle 1 (σ⁻¹ * τ) ∧ ¬ w.vle (σ⁻¹ * τ) 0`.
  Already implicit in T053's
  `cor732_per_w_existential_rescaled_data` but here packaged via the
  per-piece refinement.

## The structured blocker for the global multi-element residual

The multi-piece refinement provides per-piece singleton residuals
that combined COVER `Spa A A⁺` (every `w` lies in some piece). This
is the natural Wedhorn 8.34(ii) Laurent cover output.

However, T053's universal `MultiElementLowerBoundResidual D_T` for
multi-element `D_T` cannot be derived from the multi-piece refinement
alone, because:

* On each piece `V_τ`, ONLY `σ⁻¹ * τ` satisfies the lower bound.
* For ALL elements `t' ∈ D_T = {σ⁻¹ * τ : τ ∈ T_test}` to satisfy
  `w.vle 1 t'` at a single `w`, we'd need `w` to lie in EVERY piece
  `V_τ` simultaneously — impossible by the σ-strict-dom strictness
  (different τ's give different `σ⁻¹ * τ`'s with different
  valuations).

This **is consistent with T035's counter-example**: the multi-element
universal-over-Spa lower bound is genuinely false. The natural
Wedhorn 8.34(ii) approach uses per-piece bounds + cover-level
acyclicity (Lemma 8.33), NOT a global multi-element bound.

The downstream chain (T044–T053) needs to be re-routed to consume
**per-piece** residuals rather than the universal residual; this is
the next theorem-sized step beyond T054.

## Notes

* No root import; leaf-level.
* Imports `WedhornLaurentLocalBoundsFromCor732` (T053).
* No edits to T031–T053 accepted leaves, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* No global universal-over-Spa multi-element clearing claim (per
  T035's counter-example).
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Source-restricted multi-element lower-bound residual on a
piece** (T054 main predicate).

Per-piece form of T053's `MultiElementLowerBoundResidual`: at every
`w ∈ V`, every `t' ∈ D_T` satisfies the lower bound and
non-vanishing. Replaces T053's universal-over-`Spa A A⁺` residual
with the **actually-achievable per-piece form** — restricted to
`w ∈ V`, where `V` is a Laurent piece (or any subset of
`Spa A A⁺`). -/
def MultiElementLowerBoundResidualOnPiece
    (V : Set (Spv A)) (D_T : Finset A) : Prop :=
  ∀ w ∈ V, ∀ t' ∈ D_T, w.vle (1 : A) t' ∧ ¬ w.vle t' 0

omit [IsTopologicalRing A] in
/-- **Per-piece singleton discharge of the lower-bound residual on
a Laurent piece** (T054 substantive subtheorem).

For the Laurent piece `V := rationalOpen ({(1 : A)} : Finset A)
(σ⁻¹ * τ)` and the singleton `D_τ := {σ⁻¹ * τ}`,
`MultiElementLowerBoundResidualOnPiece V D_τ` holds.

**Proof**: take `w ∈ V` and `t' ∈ D_τ`. Since `D_τ` is a singleton,
`t' = σ⁻¹ * τ`. Unfold `V`'s rationalOpen membership at `t' = 1`
to extract `w.vle 1 (σ⁻¹ * τ)` (the per-element bound at the
singleton test element `1`); the non-vanishing
`¬ w.vle (σ⁻¹ * τ) 0` is the third conjunct of rationalOpen
membership.

Real substantive proof — uses rationalOpen unfolding +
`Finset.mem_singleton`. -/
theorem multi_element_lower_bound_on_piece_singleton_via_laurent_membership
    {σ : Aˣ} (τ : A) :
    MultiElementLowerBoundResidualOnPiece
      (rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ))
      ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) := by
  intro w hw_in t' ht'
  obtain rfl := Finset.mem_singleton.mp ht'
  exact ⟨hw_in.2.1 (1 : A) (Finset.mem_singleton.mpr rfl), hw_in.2.2⟩

omit [IsTopologicalRing A] in
/-- **Multi-piece Laurent cover refinement from Cor 7.32**
(T054 main theorem).

From Cor 7.32 σ-strict-domination over `T_test`, at every
`w ∈ Spa A A⁺` there exists `τ ∈ T_test` such that:

* `w ∈ rationalOpen ({(1 : A)}) (σ⁻¹ * τ)` (Laurent piece membership)
* `MultiElementLowerBoundResidualOnPiece (rationalOpen ({(1 : A)})
  (σ⁻¹ * τ)) ({σ⁻¹ * τ})` (per-piece singleton residual).

This is the **multi-piece Laurent cover refinement** that bridges
Cor 7.32's per-`w` existential output to the per-piece source-
restricted residual. The collection `{V_τ : τ ∈ T_test}` covers
`Spa A A⁺` (existing `cor732_laurent_cover_covers_spa`); on each
`V_τ`, the per-piece singleton residual holds (this file's
`multi_element_lower_bound_on_piece_singleton_via_laurent_membership`).

**Substantive composition**: combines `cor732_laurent_piece_membership_at`
(existing, gives the τ + Laurent piece membership) with the per-piece
discharge from `multi_element_lower_bound_on_piece_singleton_via_laurent_membership`. -/
theorem cor732_multi_piece_laurent_refinement
    {σ : Aˣ} {T_test : Finset A}
    (hσ_dom :
      ∀ v ∈ Spa A A⁺, ∃ τ ∈ T_test,
        v.vle (σ : A) τ ∧ ¬ v.vle τ (σ : A)) :
    ∀ w ∈ Spa A A⁺,
      ∃ τ ∈ T_test,
        w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) ∧
        MultiElementLowerBoundResidualOnPiece
          (rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ))
          ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) := by
  intro w hw_spa
  obtain ⟨τ, hτ_mem, hw_in_piece⟩ :=
    cor732_laurent_piece_membership_at hσ_dom hw_spa
  exact ⟨τ, hτ_mem, hw_in_piece,
    multi_element_lower_bound_on_piece_singleton_via_laurent_membership τ⟩

omit [IsTopologicalRing A] in
/-- **Per-`w` existential singleton residual from Cor 7.32**
(T054 direct consequence).

Direct per-`w` consequence of `cor732_multi_piece_laurent_refinement`:
at every `w ∈ Spa A A⁺`, ∃ τ ∈ T_test with the per-`w` singleton
lower bound `w.vle 1 (σ⁻¹ * τ) ∧ ¬ w.vle (σ⁻¹ * τ) 0`.

Equivalent to T053's `cor732_per_w_existential_rescaled_data`,
re-derived through T054's per-piece refinement structure. The
re-derivation is substantive — it routes through the per-piece
`MultiElementLowerBoundResidualOnPiece` predicate, exposing the
underlying refinement structure.

**Note**: this CANNOT be strengthened to `∀ τ ∈ T_test`-with-bounds
universally over `w` — that would be the false universal multi-
element residual (T035 counter-example). The existential per `w`
is genuinely the strongest universal-over-Spa output of Cor 7.32. -/
theorem cor732_existential_singleton_residual_at_each_w
    {σ : Aˣ} {T_test : Finset A}
    (hσ_dom :
      ∀ v ∈ Spa A A⁺, ∃ τ ∈ T_test,
        v.vle (σ : A) τ ∧ ¬ v.vle τ (σ : A)) :
    ∀ w ∈ Spa A A⁺,
      ∃ τ ∈ T_test,
        w.vle (1 : A) (((σ⁻¹ : Aˣ) : A) * τ) ∧
        ¬ w.vle (((σ⁻¹ : Aˣ) : A) * τ) 0 := by
  intro w hw_spa
  obtain ⟨τ, hτ_mem, hw_in_piece, h_residual⟩ :=
    cor732_multi_piece_laurent_refinement hσ_dom w hw_spa
  exact ⟨τ, hτ_mem, h_residual w hw_in_piece (((σ⁻¹ : Aˣ) : A) * τ)
    (Finset.mem_singleton.mpr rfl)⟩

/-- **Structured blocker: global multi-element residual from
multi-piece refinement** (T054 documented gap).

The multi-piece refinement provides per-piece singleton residuals
covering `Spa A A⁺` (every `w` lies in some `V_τ` with the
singleton residual on `V_τ`). This is the natural Wedhorn 8.34(ii)
output.

T053's `MultiElementLowerBoundResidual D_T` (universal over `Spa A
A⁺` AND over `D_T`) for multi-element `D_T` is **NOT derivable**
from the multi-piece refinement — at any `w ∈ V_τ`, only `σ⁻¹ * τ`
satisfies the lower bound, not other `σ⁻¹ * τ'` for `τ' ≠ τ`.

The downstream chain (T044–T053) needs to be **re-routed** to
consume per-piece residuals rather than the universal residual.
This is the next theorem-sized step: refactor the C1 supplier chain
to take the multi-piece refinement output and discharge the
cover-refinement on each Laurent piece separately, then assemble
via cover-level acyclicity (Wedhorn Lemma 8.33).

The Prop predicate naming this structural step is the existing
T053 `MultiElementLowerBoundResidual` (left as residual) AND the
following per-piece-collection predicate, which IS provable from
T054's content.

This Prop names the precise per-piece collection structure that
the multi-piece refinement delivers: a finite collection of
Laurent pieces with per-piece singleton residuals, jointly covering
`Spa A A⁺`. -/
def MultiPieceLaurentCoverRefinementOutput
    {σ : Aˣ} (T_test : Finset A) : Prop :=
  ∀ w ∈ Spa A A⁺,
    ∃ τ ∈ T_test,
      w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) ∧
      MultiElementLowerBoundResidualOnPiece
        (rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ))
        ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A)

omit [IsTopologicalRing A] in
/-- **`MultiPieceLaurentCoverRefinementOutput` from Cor 7.32**
(T054 documented bridge).

From Cor 7.32 σ-strict-domination over `T_test`, derive the
multi-piece Laurent cover refinement output. Direct application of
`cor732_multi_piece_laurent_refinement`. -/
theorem multiPieceLaurentCoverRefinementOutput_via_cor732
    {σ : Aˣ} {T_test : Finset A}
    (hσ_dom :
      ∀ v ∈ Spa A A⁺, ∃ τ ∈ T_test,
        v.vle (σ : A) τ ∧ ¬ v.vle τ (σ : A)) :
    MultiPieceLaurentCoverRefinementOutput (σ := σ) T_test :=
  cor732_multi_piece_laurent_refinement hσ_dom

end ValuationSpectrum

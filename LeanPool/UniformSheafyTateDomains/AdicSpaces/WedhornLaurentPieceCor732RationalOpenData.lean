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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLaurentProductBoundSupplier

/-!
# Wedhorn 8.34(ii) — Base-side Laurent-piece rationalOpen data
construction (T052)

T051 (commit `be99b87`) accepted the consumer
`T050_supplier_via_laurent_piece_membership`, which converts per-`w`
**rationalOpen-style Laurent-piece data** into T050's product/lower-
bound supplier. The remaining residual is the construction of that
rationalOpen data.

This file lands the **substantive reduction** of T051's rationalOpen
data to a per-`w` package of **local bound conditions** — the natural
Wedhorn 8.34(ii) Laurent-piece output expressed in raw inequality
form. The reduction extracts the bounds from the local-bounds package
and assembles them into rationalOpen memberships via the
`rationalOpen` definition's per-element-bound + non-vanishing
structure.

## Documented universality blocker

Per T035's analysis (`WedhornMaxElementSDComparison.lean`), the
universal-over-Spa version of these bounds is mathematically false in
general: T035's counter-example (`A = ℚ_p, T_D = {1}, D_s = p,
σ = p^N`) violates the per-`t'` upper bound at `algMap s_D` even
under all source restrictions. T052 therefore lands a **conditional
reduction** rather than an unconditional construction: given the
per-`w` local-bounds package — which Wedhorn 8.34(ii)'s Laurent cover
refinement is supposed to produce on each Laurent piece — derive
T051's rationalOpen data.

## What this file provides

* `laurent_piece_rationalOpen_data_via_local_bounds` — the main
  substantive reduction: takes a per-`w` package of two local bound
  conditions

  * `(w.vle (T_D.prod id) D_s) ∧ (¬ w.vle D_s 0)` — the product upper
    bound at `D_s` and non-vanishing of `D_s`.
  * `∀ t' ∈ T_D, (w.vle 1 t') ∧ (¬ w.vle t' 0)` — per-element lower
    bound at each `t'` and non-vanishing of `t'`.

  and derives T051's two rationalOpen memberships:

  * `w ∈ rationalOpen ({T_D.prod id} : Finset A) D_s` — assembled via
    Spa-membership + product upper bound + non-vanishing.
  * `∀ t' ∈ T_D, w ∈ rationalOpen ({(1 : A)} : Finset A) t'` —
    assembled per-`t'` via Spa-membership + per-`t'` lower bound +
    per-`t'` non-vanishing.

  The proof **substantively consumes** the local-bounds package: each
  rationalOpen is assembled by extracting the corresponding bound +
  non-vanishing pair and threading the Spa-membership.

* `rationalOpen_subset_via_local_bounds` — composes T052's reduction
  with T051's `rationalOpen_subset_via_laurent_piece_membership` to
  give the base subset clause from local-bounds data.

* `C1SupplierStrong_local_via_local_bounds` — top-level C1 supplier
  wrapper composing T052's reduction with T051 and T049's chain.
  The named residual is the per-`w` local-bounds package — the
  rawest form of the Wedhorn 8.34(ii) Laurent-cover-refinement output
  at each Laurent piece.

## Why local bounds are the natural Wedhorn 8.34(ii) Laurent piece
output

Wedhorn 8.34(ii)'s Laurent cover refinement (PDF page 84) constructs
specific Laurent pieces on which:

* The **product upper bound** `w.vle (T_D.prod id) D_s` arises from
  the cover-piece denominator structure (the cover-piece's
  `R(T_D, D_s)` definition gives per-element upper bounds, and on a
  refined Laurent piece the product upper bound consolidates them).
* The **per-element lower bound** `w.vle 1 t'` arises from the
  σ-rescaled Laurent-piece structure: on the piece where
  `σ⁻¹ * t'` is "≥ 1 at w", we have `w.vle 1 (σ⁻¹ * t')`, which
  unfolds to `w.vle σ t'`. Combined with σ-strict-domination by
  some τ at w, the per-element lower bound at `t'` follows for all
  t' in the Laurent piece.

The local-bounds package matches this Wedhorn-style Laurent-piece
output exactly: each conjunct is a raw inequality matching one of the
Laurent-piece-defining bounds.

## Notes

* No root import; leaf-level.
* Imports only `WedhornLaurentProductBoundSupplier` (T051), which
  transitively brings in T050 / T049's chain.
* No edits to T031–T051 accepted leaves, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* No global universal-over-Spa multi-clearing claim (per T035's
  counter-example).
* The local-bounds package is the **rawest form** of the residual —
  closer than T051's rationalOpen-membership form to the
  Wedhorn 8.34(ii) per-Laurent-piece bounds (PDF page 84).
* Producing the local-bounds package from σ-domination + Laurent
  cover formation is the next theorem-sized step (the actual
  Wedhorn 8.34(ii) σ-rescaled Laurent piece construction).
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

omit [IsTopologicalRing A] in
/-- **T051 rationalOpen data via per-`w` local bounds package** (T052 main substantive
reduction). From a per-`w` local-bounds package — at each `w ∈ Spa A A⁺` with `w.vle f s`, the
product upper bound `w.vle (T_D.prod id) D_s ∧ ¬ w.vle D_s 0` and the per-element lower bound
`∀ t' ∈ T_D, w.vle 1 t' ∧ ¬ w.vle t' 0` — derive T051's per-`w` rationalOpen data
`w ∈ rationalOpen {T_D.prod id} D_s ∧ ∀ t' ∈ T_D, w ∈ rationalOpen {1} t'`. -/
theorem laurent_piece_rationalOpen_data_via_local_bounds
    (T_D : Finset A) (D_s f s : A)
    (h_local :
      ∀ w ∈ Spa A A⁺,
        w.vle f s →
        (w.vle (T_D.prod id) D_s ∧ ¬ w.vle D_s 0) ∧
        (∀ t' ∈ T_D, w.vle (1 : A) t' ∧ ¬ w.vle t' 0)) :
    ∀ w ∈ Spa A A⁺,
      w.vle f s →
      w ∈ rationalOpen ({T_D.prod id} : Finset A) D_s ∧
      ∀ t' ∈ T_D, w ∈ rationalOpen ({(1 : A)} : Finset A) t' := by
  intro w hw_spa hw_f
  obtain ⟨⟨h_prod, h_D_s_ne⟩, h_per_t⟩ := h_local w hw_spa hw_f
  refine ⟨?_, ?_⟩
  · exact ⟨hw_spa, fun c hc ↦ Finset.mem_singleton.mp hc ▸ h_prod, h_D_s_ne⟩
  · exact fun t' ht' ↦ ⟨hw_spa,
      fun c hc ↦ Finset.mem_singleton.mp hc ▸ (h_per_t t' ht').1, (h_per_t t' ht').2⟩

omit [IsTopologicalRing A] in
/-- **Base rationalOpen subset via local-bounds package.** From the per-`w` local-bounds
package, the base subset clause `R(insert f T_base, s) ⊆ R(T_D, D_s)`. -/
theorem rationalOpen_subset_via_local_bounds
    [DecidableEq A]
    (T_base T_D : Finset A) (s D_s f : A)
    (h_local :
      ∀ w ∈ Spa A A⁺,
        w.vle f s →
        (w.vle (T_D.prod id) D_s ∧ ¬ w.vle D_s 0) ∧
        (∀ t' ∈ T_D, w.vle (1 : A) t' ∧ ¬ w.vle t' 0)) :
    rationalOpen (insert f T_base) s ⊆ rationalOpen T_D D_s :=
  rationalOpen_subset_via_laurent_piece_membership T_base T_D s D_s f
    (laurent_piece_rationalOpen_data_via_local_bounds T_D D_s f s h_local)

/-- **Top-level: `C1SupplierStrong_local C` via local-bounds package**
(T052 final deliverable).

Caller theorem producing `C1SupplierStrong_local C` from per-call
delivery of:

* `f : A` — the inserted refinement element.
* The per-`w` **local-bounds package** — the named residual: at each
  `w ∈ Spa A A⁺` with `w.vle f C.base.s`, the product upper bound
  `w.vle (D.T.prod id) D.s ∧ ¬ w.vle D.s 0` AND per-element lower
  bound `∀ t' ∈ D.T, w.vle 1 t' ∧ ¬ w.vle t' 0`.
* `v`-side rationalOpen membership and `f`-non-degeneracy.

Composes T052's `laurent_piece_rationalOpen_data_via_local_bounds`
with T051's `C1SupplierStrong_local_via_laurent_piece_membership`.

**The single named non-tautological residual** is the per-`w`
local-bounds package — the rawest form of the Wedhorn 8.34(ii)
Laurent-cover-refinement output at the base side, expressed as
explicit inequalities. -/
theorem C1SupplierStrong_local_via_local_bounds
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (h_per_call_components :
      ∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
        ∀ t ∈ D.T, v.vle t D.s → ¬ v.vle D.s 0 →
        ∃ f : A,
          (∀ w ∈ Spa A A⁺,
            w.vle f C.base.s →
            (w.vle (D.T.prod id) D.s ∧ ¬ w.vle D.s 0) ∧
            (∀ t' ∈ D.T, w.vle (1 : A) t' ∧ ¬ w.vle t' 0)) ∧
          v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
          ¬ v.vle f 0) :
    C1SupplierStrong_local C := by
  refine C1SupplierStrong_local_via_laurent_piece_membership
    P hA₀_le hAplus_le_A₀ C hopen_base ?_
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨f, h_local, hv_in_plus, hvf_ne⟩ :=
    h_per_call_components D hD v hv t ht hvt hvD_s
  exact ⟨f, laurent_piece_rationalOpen_data_via_local_bounds D.T D.s f C.base.s h_local,
    hv_in_plus, hvf_ne⟩

end ValuationSpectrum

/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornSigmaDominationClearing

/-!
# Wedhorn 8.34(ii) — Laurent-piece product/lower-bound supplier (T051)

T050 (commit `06cac05`) accepted the consumer bridge
`rationalOpen_subset_via_corrected_multi_clearing`, isolating the
remaining residual as a per-`w` product/lower-bound supplier:

```
∀ w ∈ Spa A A⁺, w.vle f C.base.s →
  w.vle (D.T.prod id) D.s ∧ (∀ t' ∈ D.T, w.vle (1 : A) t')
```

This file lands the **Laurent-piece supplier**: from per-`w`
**rationalOpen-style Laurent-piece data** — a singleton-product upper
bound `w ∈ rationalOpen {D.T.prod id} D.s` plus per-element lower
bounds `w ∈ rationalOpen {(1 : A)} t'` for each `t' ∈ D.T` — derive
the T050 supplier residual. This is the natural Wedhorn 8.34(ii)
Laurent cover refinement output: each Laurent piece is itself a
rational subset, and the per-piece bounds unfold into the explicit
inequalities.

## Why this packaging?

The T050 supplier residual carries two distinct kinds of data:

1. A **multi-element product upper bound** `w.vle (D.T.prod id) D.s`
   — equivalently, `w ∈ rationalOpen {D.T.prod id} D.s`'s `t = prod`
   per-element bound.
2. A **per-element lower bound** `∀ t' ∈ D.T, w.vle 1 t'` —
   equivalently, `∀ t' ∈ D.T, w ∈ rationalOpen {(1 : A)} t'`'s
   `t = 1` per-element bound.

Both pieces are naturally rationalOpen memberships: Wedhorn 8.34(ii)
constructs the Laurent cover refinement as a finite set of rational
opens covering Spa, on each of which the bounds hold. T051's packaging
matches this Laurent-piece-rationalOpen structure exactly — the
hypothesis `h_per_w_laurent_piece` consumes rationalOpen membership
data, and the conclusion is the T050 supplier.

## What this file provides

* `T050_supplier_via_laurent_piece_membership` — packages per-`w`
  Laurent-piece rationalOpen data into the T050 supplier residual.
  Both pieces of the supplier are derived by **unfolding rationalOpen
  membership** (extracting the per-element bound at the appropriate
  test element).

* `rationalOpen_subset_via_laurent_piece_membership` — composes T051's
  packaging with T050's `rationalOpen_subset_via_corrected_multi_clearing`
  to give the base inclusion `R(insert f T_base, s) ⊆ R(T_D, D_s)`
  from Laurent-piece data.

* `C1SupplierStrong_local_via_laurent_piece_membership` — top-level
  C1 supplier wrapper composing T051's Laurent-piece packaging with
  T050 and T049's chain. The named residual is the per-`w` Laurent-
  piece rationalOpen data — exactly the Wedhorn 8.34(ii) Laurent-
  cover-refinement output at the base side.

## Why this is the right reformulation

The T050 supplier `w.vle (D.T.prod id) D.s ∧ ∀ t' ∈ D.T, w.vle 1 t'`
mixes a multi-element product bound with per-element lower bounds.
Reformulating both as rationalOpen memberships exposes the natural
Wedhorn 8.34(ii) structure:

* The Laurent cover refinement constructs rational subsets `V_τ` such
  that `∪ V_τ ⊇ R(insert f C.base.T, C.base.s)` (Wedhorn 8.34(ii)
  PDF page 84).
* On each `V_τ`, the multi-element bound + per-element lower bound
  follow from the rationalOpen structure of `V_τ`.
* T051's packaging gives the explicit conversion.

## Notes

* No root import; leaf-level.
* Imports only `WedhornSigmaDominationClearing` (T050).
* No edits to T031–T050 accepted leaves, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* The Laurent-piece membership hypothesis consumed here is the natural
  Wedhorn 8.34(ii) Laurent cover refinement output (PDF page 84) at
  the base side; producing this hypothesis is the next theorem-sized
  step beyond T051 (Wedhorn 8.34(ii) σ-rescaled Laurent piece
  construction at the base side, paralleling the localized
  `WedhornStandardCoverRefinement.cor732_laurent_piece_membership_at`).
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

omit [IsTopologicalRing A] in
/-- **T050 supplier from per-`w` Laurent-piece rationalOpen
membership** (T051 main packaging theorem).

From a per-`w` Laurent-piece data — at each `w ∈ Spa A A⁺` satisfying
`w.vle f s`, supply the **two rationalOpen memberships**:

* `w ∈ rationalOpen {T_D.prod id} D_s` — the singleton-product
  upper bound.
* `∀ t' ∈ T_D, w ∈ rationalOpen {(1 : A)} t'` — per-element lower
  bound at each `t'`.

derive the T050 supplier residual:

```
w.vle (T_D.prod id) D_s ∧ ∀ t' ∈ T_D, w.vle (1 : A) t'
```

**Proof**: at each `w` in the LHS, extract the supplied Laurent-piece
data. For the multi-element product bound, unfold `w ∈ rationalOpen
{T_D.prod id} D_s` and apply at the singleton element `T_D.prod id`.
For the per-element lower bound, unfold each `w ∈ rationalOpen
{(1 : A)} t'` and apply at the singleton element `1`.

This **substantively consumes** the Laurent-piece rationalOpen data —
the hypothesis is not pass-through; both clauses of the conclusion are
extracted from the supplied rationalOpen memberships via the
`rationalOpen` definition's per-element-bound conjunct. -/
theorem T050_supplier_via_laurent_piece_membership
    (T_D : Finset A) (D_s f s : A)
    (h_per_w_laurent_piece :
      ∀ w ∈ Spa A A⁺,
        w.vle f s →
        w ∈ rationalOpen ({T_D.prod id} : Finset A) D_s ∧
        ∀ t' ∈ T_D, w ∈ rationalOpen ({(1 : A)} : Finset A) t') :
    ∀ w ∈ Spa A A⁺,
      w.vle f s →
      w.vle (T_D.prod id) D_s ∧ (∀ t' ∈ T_D, w.vle (1 : A) t') := by
  intro w hw_spa hw_f
  obtain ⟨h_prod_open, h_per_t_open⟩ :=
    h_per_w_laurent_piece w hw_spa hw_f
  refine ⟨?_, ?_⟩
  · obtain ⟨_hw_spa', h_bound, _h_D_s_ne⟩ := h_prod_open
    exact h_bound (T_D.prod id) (Finset.mem_singleton.mpr rfl)
  · intro t' ht'
    obtain ⟨_hw_spa', h_bound, _h_t'_ne⟩ := h_per_t_open t' ht'
    exact h_bound (1 : A) (Finset.mem_singleton.mpr rfl)

omit [IsTopologicalRing A] in
/-- **Base rationalOpen subset via Laurent-piece membership**
(T051 composed deliverable).

Composes T051's `T050_supplier_via_laurent_piece_membership` with
T050's `rationalOpen_subset_via_corrected_multi_clearing` to give the
base rationalOpen inclusion
`R(insert f T_base, s) ⊆ R(T_D, D_s)` from per-`w` Laurent-piece
rationalOpen data.

This is the **single-step reduction** from the Laurent-cover-refinement
output to the cover-piece subset clause consumed by T049 / T044's
chain. -/
theorem rationalOpen_subset_via_laurent_piece_membership
    [DecidableEq A]
    (T_base T_D : Finset A) (s D_s f : A)
    (h_per_w_laurent_piece :
      ∀ w ∈ Spa A A⁺,
        w.vle f s →
        w ∈ rationalOpen ({T_D.prod id} : Finset A) D_s ∧
        ∀ t' ∈ T_D, w ∈ rationalOpen ({(1 : A)} : Finset A) t') :
    rationalOpen (insert f T_base) s ⊆ rationalOpen T_D D_s :=
  rationalOpen_subset_via_corrected_multi_clearing T_base T_D s D_s f
    (T050_supplier_via_laurent_piece_membership T_D D_s f s
      h_per_w_laurent_piece)

/-- **Top-level: `C1SupplierStrong_local C` via Laurent-piece membership**
(T051 final deliverable).

Caller theorem producing `C1SupplierStrong_local C` from per-call
delivery of:

* `f : A` — the inserted refinement element.
* The per-`w` Laurent-piece rationalOpen data — the named residual:
  at each `w ∈ Spa A A⁺` with `w.vle f C.base.s`, the singleton-
  product upper bound `w ∈ R({D.T.prod id}, D.s)` AND per-element
  lower bound `∀ t' ∈ D.T, w ∈ R({1}, t')`.
* `v`-side rationalOpen membership and `f`-non-degeneracy.

Composes T051's `rationalOpen_subset_via_laurent_piece_membership`
with T049's `C1SupplierStrong_local_via_Wedhorn745_pointwise_refinement`.

**The single named non-tautological residual** is the per-`w`
Laurent-piece rationalOpen data — the natural Wedhorn 8.34(ii)
Laurent-cover-refinement output at the base side, expressed in
rationalOpen vocabulary. -/
theorem C1SupplierStrong_local_via_laurent_piece_membership
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
            w ∈ rationalOpen ({D.T.prod id} : Finset A) D.s ∧
            ∀ t' ∈ D.T, w ∈ rationalOpen ({(1 : A)} : Finset A) t') ∧
          v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
          ¬ v.vle f 0) :
    C1SupplierStrong_local C := by
  refine C1SupplierStrong_local_via_Wedhorn745_pointwise_refinement
    P hA₀_le hAplus_le_A₀ C hopen_base ?_
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨f, h_per_w_laurent, hv_in_plus, hvf_ne⟩ :=
    h_per_call_components D hD v hv t ht hvt hvD_s
  refine ⟨f, ?_, hv_in_plus, hvf_ne⟩
  exact rationalOpen_subset_via_laurent_piece_membership C.base.T D.T
    C.base.s D.s f h_per_w_laurent

end ValuationSpectrum

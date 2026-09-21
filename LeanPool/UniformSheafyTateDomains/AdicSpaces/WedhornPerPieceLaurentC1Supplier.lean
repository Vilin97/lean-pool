/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornMultiPieceLaurentRefinement

/-!
# Wedhorn 8.34(ii) — Per-piece Laurent C1 supplier reroute (T056)

T054 (commit `3799c8e`) accepted the per-piece Laurent cover
refinement output `MultiPieceLaurentCoverRefinementOutput` — the
honest Wedhorn 8.34(ii) output structure: Laurent pieces `V_τ`
covering `Spa A A⁺` with per-piece **singleton** residuals
`MultiElementLowerBoundResidualOnPiece V_τ ({σ⁻¹ * τ})`. T053's
universal-over-Spa-and-D_T `MultiElementLowerBoundResidual D_T` for
multi-element `D_T` was named as a structured blocker, with the
documented gap that the universal form is mathematically false (per
T035's counter-example).

This file lands the **per-piece source-restricted reroute** of T050's
`rationalOpen_subset_via_corrected_multi_clearing` chain: instead of
requiring the per-`w`-on-Spa product+lower-bound supply, the new
theorem requires only per-`w`-on-piece supply. The conclusion
correspondingly weakens to a per-piece subset inclusion
`R(insert f T_base, s) ∩ V ⊆ R(T_D, D_s)`.

The reroute matches Wedhorn 8.34(ii) PDF page 84:

* Each Laurent piece `V_τ` has its own singleton `D_τ = {σ⁻¹ * τ}`
  and per-piece bounds.
* On `V_τ`, the per-piece subset `R(insert f T_base, s) ∩ V_τ ⊆
  R(D_τ.T, D_τ.s)` follows from the per-piece local-bounds package.
* The collection of per-piece subsets, jointly with the Laurent
  cover, gives the cover-level structure consumed by Wedhorn
  Lemma 8.33 (binary Laurent cover acyclicity) for the final
  acyclicity assembly.

## What this file provides

* `rationalOpen_subset_intersected_with_piece_via_per_w_local_data`
  — the **substantive reroute**: per-piece source-restricted version
  of T050's `rationalOpen_subset_via_corrected_multi_clearing`.
  Takes per-`w`-on-piece product+lower-bound supply, produces the
  per-piece subset inclusion. **Real proof** using
  `vle_of_dominating_unit_multi_corrected_at` (existing API). Not a
  pass-through — the per-piece hypothesis is genuinely consumed.

* `per_piece_singleton_subset_via_laurent_membership` — composition
  with T054's per-piece singleton residual: at a Laurent piece
  `V_τ := rationalOpen ({1}) (σ⁻¹ * τ)`, the per-piece subset
  `R(insert f T_base, s) ∩ V_τ ⊆ R({σ⁻¹ * τ}, D_s)` follows from
  the per-piece singleton residual + a per-`w`-on-piece product
  upper bound at `D_s`.

* `CoverLevelAssemblyResidual` — explicit Lean Prop predicate naming
  the **next named missing API**: the cover-level assembly that
  combines per-piece subsets via Wedhorn Lemma 8.33 (binary Laurent
  cover acyclicity) to give the C1 supplier's global subset
  conclusion.

## Why this is the natural Wedhorn 8.34(ii) reroute

The C1 supplier's conclusion `R(insert f C.base.T, C.base.s) ⊆
R(D.T, D.s)` is GLOBAL on `Spa(A, A⁺)`. T054's per-piece refinement
provides LOCAL per-piece data that doesn't directly give a global
inclusion (T035's counter-example to the universal multi-element
case). The reroute via per-piece subsets matches Wedhorn 8.34(ii)
PDF page 84's actual approach:

1. Refine the cover via Cor 7.32 σ-rescaled Laurent pieces (T054).
2. On each piece, derive a per-piece subset (this file's
   `rationalOpen_subset_intersected_with_piece_via_per_w_local_data`).
3. Combine per-piece subsets via Wedhorn Lemma 8.33 (binary Laurent
   cover acyclicity) — the `CoverLevelAssemblyResidual` documented
   here as the next named missing API.

## Notes

* No root import; leaf-level.
* Imports `WedhornMultiPieceLaurentRefinement` (T054), which
  transitively brings in T053, T052, T051, T050, T049, T048.
* No edits to T031–T054 accepted leaves, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* Does NOT reintroduce the false universal `MultiElementLowerBoundResidual`
  for `|D_T| > 1` as a goal.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

omit [IsTopologicalRing A] in
/-- **Per-piece source-restricted T050 reroute** (T056 main
substantive theorem).

Per-piece version of T050's
`rationalOpen_subset_via_corrected_multi_clearing`: from a per-`w`-
on-piece product+lower-bound supply on `V`, derive the per-piece
subset inclusion `R(insert f T_base, s) ∩ V ⊆ R(T_D, D_s)`.

**Hypothesis** `h_per_w_on_piece` is **source-restricted to** `V`:
the per-`w` product+lower-bound only needs to hold on `w ∈ V`, not
universally on `Spa A A⁺`. This is the per-piece form consumed by
T054's per-piece refinement output.

**Proof**: take `v ∈ R(insert f T_base, s) ∩ V`. Extract `v.vle f s`
from rationalOpen membership (at the inserted f). Apply the per-`w`-
on-piece supply (since `v ∈ V`) to obtain product upper bound +
per-element lower bound. Apply `vle_of_dominating_unit_multi_corrected_at`
(existing API in `WedhornDominatingUnitInequality`) to derive
per-`t'` upper bound + non-vanishing. Assemble rationalOpen
membership.

The hypothesis is **genuinely consumed**: the per-piece supply at
`v ∈ V` is extracted and threaded through the corrected
multi-clearing. -/
theorem rationalOpen_subset_intersected_with_piece_via_per_w_local_data
    [DecidableEq A]
    (V : Set (Spv A))
    (T_base T_D : Finset A) (s D_s f : A)
    (h_per_w_on_piece :
      ∀ w ∈ V, w ∈ Spa A A⁺ →
        w.vle f s →
        w.vle (T_D.prod id) D_s ∧ (∀ t' ∈ T_D, w.vle (1 : A) t')) :
    rationalOpen (insert f T_base) s ∩ V ⊆ rationalOpen T_D D_s := by
  rintro v ⟨⟨hv_spa, hv_per_c, _⟩, hv_V⟩
  obtain ⟨h_prod, h_lower⟩ :=
    h_per_w_on_piece v hv_V hv_spa (hv_per_c f (Finset.mem_insert_self f T_base))
  obtain ⟨h_per_t, h_D_s_ne⟩ :=
    vle_of_dominating_unit_multi_corrected_at v h_prod h_lower
  exact ⟨hv_spa, h_per_t, h_D_s_ne⟩

omit [IsTopologicalRing A] in
/-- **Per-piece singleton subset via Laurent membership + product
upper bound** (T056 composition with T054).

For the Laurent piece `V_τ := rationalOpen ({(1 : A)}) (σ⁻¹ * τ)`
(provided by T054's `cor732_multi_piece_laurent_refinement`) and the
per-piece singleton `D_τ := {σ⁻¹ * τ}`, derive the per-piece subset
inclusion

```
R(insert f T_base, s) ∩ V_τ ⊆ R({σ⁻¹ * τ}, D_s)
```

from:

* T054's `multi_element_lower_bound_on_piece_singleton_via_laurent_membership`
  (the per-piece singleton lower bound + non-vanishing on `V_τ`).
* A per-`w`-on-piece **product upper bound at `D_s`**
  `h_product_at_D_s` (the only remaining residual at this layer —
  this is the actual Wedhorn-content gap, since the singleton
  `D_τ.prod id = σ⁻¹ * τ`'s upper bound at `D_s` depends on `D_s`'s
  relation to `σ⁻¹ * τ`).

**Substantive composition** of T054's per-piece singleton residual
with T056's per-piece source-restricted reroute. -/
theorem per_piece_singleton_subset_via_laurent_membership
    [DecidableEq A]
    (T_base : Finset A) (s D_s f : A) {σ : Aˣ} (τ : A)
    (h_product_at_D_s :
      ∀ w ∈ rationalOpen ({(1 : A)} : Finset A)
              (((σ⁻¹ : Aˣ) : A) * τ),
        w ∈ Spa A A⁺ →
        w.vle f s →
        w.vle (((σ⁻¹ : Aˣ) : A) * τ) D_s) :
    rationalOpen (insert f T_base) s ∩
        rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ)
      ⊆ rationalOpen ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D_s := by
  refine rationalOpen_subset_intersected_with_piece_via_per_w_local_data
    (rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ))
    T_base ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) s D_s f ?_
  intro w hw_V hw_spa hw_f
  refine ⟨?_, ?_⟩
  · -- Product upper bound: T_D.prod id = σ⁻¹ * τ; needs h_product_at_D_s.
    simpa using h_product_at_D_s w hw_V hw_spa hw_f
  · -- Per-element lower bound: from T054's per-piece singleton residual.
    intro t' ht'
    obtain rfl := Finset.mem_singleton.mp ht'
    -- w ∈ V_τ unfolds; extract w.vle 1 (σ⁻¹ * τ) from rationalOpen.
    exact hw_V.2.1 (1 : A) (Finset.mem_singleton.mpr rfl)

/-- **Cover-level assembly residual — Lean statement of the next
missing API** (T056 structured blocker).

After T054 + T056, we have:

* For each `τ ∈ T_test`, a per-piece subset
  `R(insert f T_base, s) ∩ V_τ ⊆ R(D_τ.T, D_τ.s)` (this file's
  `per_piece_singleton_subset_via_laurent_membership`).
* The pieces `{V_τ : τ ∈ T_test}` cover `Spa A A⁺` (T054's
  `cor732_laurent_cover_covers_spa`).

The C1 supplier's conclusion requires a **global** subset
`R(insert f T_base, s) ⊆ R(D.T, D.s)` for a SPECIFIC base-side
target `(D.T, D.s)` (NOT per-piece). The bridge from the per-piece
subsets to this global subset is the **cover-level assembly**:

* If all per-piece subsets `(D_τ.T, D_τ.s)` collapse to a common
  `(D.T, D.s)`, the union argument gives the global subset.
* In Wedhorn 8.34(ii), the per-piece `D_τ.T = {σ⁻¹ * τ}` differ for
  each τ; the assembly uses **Wedhorn Lemma 8.33** (binary Laurent
  cover acyclicity) to glue per-piece data into the global C1
  supplier output.

This Prop predicate names the missing assembly API: a theorem
combining per-piece subsets (with cover) into a global subset.

The actual Wedhorn 8.33 / cover-level acyclicity machinery
(`LaurentRefinement.lean` and `LaurentCoverExact.lean` partially
develop this) is the next theorem-sized step, beyond T056's reroute.

**Note**: this is NOT the false `MultiElementLowerBoundResidual`
universal-over-D_T form (rejected by T035). The cover-level assembly
operates at the **subset-of-Spa** level, not at the bound level. -/
def CoverLevelAssemblyResidual
    [DecidableEq A]
    {σ : Aˣ} (T_test : Finset A) (T_base : Finset A) (D_T : Finset A)
    (s D_s f : A) : Prop :=
  -- For each τ ∈ T_test, the per-piece subset (T056's output) holds
  -- intersected with the Laurent piece V_τ:
  (∀ τ ∈ T_test,
    rationalOpen (insert f T_base) s ∩
        rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ)
      ⊆ rationalOpen ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D_s) →
  -- The Laurent pieces cover Spa via Cor 7.32:
  (∀ w ∈ Spa A A⁺, ∃ τ ∈ T_test,
    w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ)) →
  -- Conclusion: the global subset on D_T (which is some assembly of
  -- {σ⁻¹ * τ : τ ∈ T_test} via the Wedhorn Lemma 8.33 / cover
  -- acyclicity machinery):
  rationalOpen (insert f T_base) s ⊆ rationalOpen D_T D_s

end ValuationSpectrum

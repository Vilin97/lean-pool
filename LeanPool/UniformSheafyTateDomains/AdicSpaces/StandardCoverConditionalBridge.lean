/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.StandardCover

/-!
# Standard-cover conditional bridge: C1 supplier → candidate-family wrappers

This file lands sorry-free conditional wrappers that bridge from
**Tertiary's `exists_single_f_refinement_at_t_via_dominating_unit`-shaped
supplier** (target signature documented at
`WedhornStandardCoverRefinement.lean:91`, currently unimplemented) to the
existing candidate-family scaffolding in `StandardCover.lean`.

Once Tertiary's lemma lands in `WedhornStandardCoverRefinement.lean`, the
abstract supplier hypothesis below is dischargeable in one step, and the
chain composes cleanly into the user-target shape consumed by
`hZavyalov_per_E_from_candidate_family_construction`
(`StandardCover.lean`).

## What this file provides

* `exists_single_f_refining_point_in_D_via_C1Supplier` — bridges the
  abstract single-`t` supplier into the **pointwise C1** form
  `exists_single_f_refining_point_in_D` (target sig at
  `StandardCover.lean:365–372`). Takes a hypothesis `D.s ∈ D.T` (the
  Wedhorn 7.30(3) normalization, satisfied by any rational-localization
  datum after `rationalOpen_insert_s` rewriting). Sorry-free; one-line
  application of the supplier with `t := D.s`.

* `C1Supplier_local` — a `Prop`-valued predicate packaging Tertiary's
  helper signature so callers can pass it abstractly through downstream
  bridges. Local to this file and to be removed once Tertiary's lemma
  lands.

## Wedhorn ingredients used

* Tertiary's target supplier shape (`WedhornStandardCoverRefinement.lean:91`).
* `RationalSubsets.rationalOpen_insert_s` (Wedhorn 7.30(3)) — used by
  the docstring discussion of normalization, not invoked directly.
* `Spv.vle_total` for the trivial `v.vle D.s D.s` step.

## What this file does NOT provide

* The non-standard ratio proof itself — that is Tertiary's scope at
  `WedhornStandardCoverRefinement.lean`. The hypothesis `h_C1` here is
  the abstract supplier; we do not duplicate the construction.
* The compactness-based finite-subcover extraction step
  (`exists_single_f_refining_point_in_D` → `exists_zavyalov_candidate_family`).
  That is the next layer up and requires
  `SpaCompact.isCompact_preimage_rationalOpen_of_tate_pseudouniformizer`
  threading; it stays as a separate task.

No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
content. No root import; this file imports only `StandardCover` and is
not currently imported by `Adic spaces.lean`. -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Local C1 supplier predicate** (conditional bridge boundary).

Packages Tertiary's `exists_single_f_refinement_at_t_via_dominating_unit`
target signature (`WedhornStandardCoverRefinement.lean:91`) as a `Prop`
so downstream bridges can take it abstractly. Once Tertiary's lemma
lands, callers discharge `C1Supplier_local C` by direct application
(possibly threading the `(P, hA₀_le, π, hI, hπ_tn, hπ_unit, hArch)`
hypothesis bundle their helper requires).

This predicate is **local** to the conditional-bridge layer and will be
removed once the unconditional `exists_single_f_refining_point_in_D`
(itself derivable from Tertiary's helper + `D.s ∈ D.T`-normalization)
is landed in `StandardCover.lean`. -/
def C1Supplier_local [DecidableEq A] (C : RationalCoveringData A) : Prop :=
  ∀ (D : RationalLocData A) (_hD : D ∈ C.covers)
    (v : Spv A) (_hv : v ∈ rationalOpen D.T D.s)
    (t : A) (_ht : t ∈ D.T)
    (_hvt : v.vle t D.s) (_hvD_s : ¬ v.vle D.s 0),
    ∃ f : A,
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s

/-- **Bridge: abstract C1 supplier → pointwise C1 refinement**.

Given Tertiary's abstract single-`t` supplier `h_C1` and a `D ∈ C.covers`
satisfying the Wedhorn 7.30(3)-normalization `D.s ∈ D.T` (which any
rational-localization datum can be normalized to via
`rationalOpen_insert_s`), produce the pointwise C1 form

```
∃ f : A,
  v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
  rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s
```

required by `exists_single_f_refining_point_in_D` (target signature at
`StandardCover.lean:365–372`).

**Bridge proof.** Take `t := D.s ∈ D.T`. The inequality `v.vle D.s D.s`
is immediate from `Spv.vle_total`; `¬ v.vle D.s 0` is the third
component of `v ∈ rationalOpen D.T D.s`. Apply `h_C1`.

**Normalization burden.** The `D.s ∈ D.T` hypothesis is satisfied by the
`insert D.s D.T`-normalization of any `RationalLocData`; the rational
open is unchanged by Wedhorn 7.30(3). Concretely: a caller with
`D : RationalLocData` not satisfying `D.s ∈ D.T` should pre-process by
replacing `D.T` with `insert D.s D.T` (and noting
`rationalOpen (insert D.s D.T) D.s = rationalOpen D.T D.s`). The
modified datum lies in the same rational open. Threading this through
`hD : D ∈ C.covers` requires either a covering-level normalization
(replacing `C.covers` by its insert-normalized image) or this bridge
accepting the membership witness for the original (non-normalized) `D`
together with the `D.s ∈ D.T` hypothesis on the rewritten datum; the
latter form is what `h_C1` consumes downstream. -/
theorem exists_single_f_refining_point_in_D_via_C1Supplier
    [DecidableEq A] (C : RationalCoveringData A)
    (h_C1 : C1Supplier_local C)
    (D : RationalLocData A) (hD : D ∈ C.covers)
    (hD_s_mem : D.s ∈ D.T)
    (v : Spv A) (hv : v ∈ rationalOpen D.T D.s) :
    ∃ f : A,
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s :=
  h_C1 D hD v hv D.s hD_s_mem (v.vle_refl D.s) hv.2.2

/-- **Bridge: per-D pointwise C1 → per-D-and-`v` candidate-element
selector**.

Given the pointwise C1 result for every `D ∈ C.covers` and every
`v ∈ rationalOpen D.T D.s`, this packaging exposes a function-style
selector

```
∀ (D : RationalLocData A), D ∈ C.covers →
  ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
    {f : A // v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
              rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s}
```

This is the input shape consumed by the (still-to-be-written)
finite-subcover extraction step that produces
`mk_S_D : RationalLocData A → Finset A`.

**Note on existence-style outputs.** The output uses the `Subtype` form
to keep the selector total over all valid `(D, hD, v, hv)`; downstream
finite-subcover code can reconstruct the existential via
`Subtype.property`. -/
noncomputable def c1_pointwise_selector
    [DecidableEq A] (C : RationalCoveringData A)
    (h_C1_pointwise :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
        ∃ f : A,
          v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
          rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s)
    (D : RationalLocData A) (hD : D ∈ C.covers)
    (v : Spv A) (hv : v ∈ rationalOpen D.T D.s) :
    {f : A //
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s} :=
  Classical.indefiniteDescription _ (h_C1_pointwise D hD v hv)

/-- **Composed bridge: C1 supplier → per-D-and-`v` selector**.

Combines `exists_single_f_refining_point_in_D_via_C1Supplier` with
`c1_pointwise_selector`: callers pass the abstract supplier `h_C1` and a
covering-level normalization `h_normalized : ∀ D ∈ C.covers, D.s ∈ D.T`,
and obtain the function-style selector ready for the finite-subcover
extraction. -/
noncomputable def c1_selector_via_C1Supplier
    [DecidableEq A] (C : RationalCoveringData A)
    (h_C1 : C1Supplier_local C)
    (h_normalized : ∀ D ∈ C.covers, D.s ∈ D.T)
    (D : RationalLocData A) (hD : D ∈ C.covers)
    (v : Spv A) (hv : v ∈ rationalOpen D.T D.s) :
    {f : A //
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s} :=
  c1_pointwise_selector C
    (fun D' hD' v' hv' =>
      exists_single_f_refining_point_in_D_via_C1Supplier C h_C1 D' hD'
        (h_normalized D' hD') v' hv')
    D hD v hv

end ValuationSpectrum

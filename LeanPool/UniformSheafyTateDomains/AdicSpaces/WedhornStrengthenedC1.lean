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
# Wedhorn Strengthened C1: third-clause `¬ v.vle f 0` audit + small bridge

The Wedhorn 8.34(ii) C1 supplier
(`exists_single_f_refinement_at_t_via_dominating_unit`, target signature
documented at `WedhornStandardCoverRefinement.lean:91`) currently exposes
two output clauses:

```
∃ f : A,
  v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
  rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s
```

`WedhornStage2SpanExtractor.span_top_via_strengthened_cover_and_outside_rescue`
(commit `63c8ecd`) needs an additional **third clause** `¬ v.vle f 0`
to bridge the per-D cover into the no-common-zero / span-top conclusion.

This file lands the smallest local audit deliverable: a `C1SupplierStrong`
predicate with the strengthened third clause and the trivial pointwise
bridge analogous to
`StandardCoverConditionalBridge.exists_single_f_refining_point_in_D_via_C1Supplier`
(commit `240b682`).

## What this file provides

* `C1SupplierStrong_local` — strengthened C1 supplier predicate
  (Tertiary's target signature plus `¬ v.vle f 0`).
* `exists_single_f_refining_point_in_D_via_C1SupplierStrong` — bridge
  from `C1SupplierStrong_local` + `D.s ∈ D.T` normalization to the
  pointwise strengthened C1 form. Sorry-free, axiom-clean.

## Audit conclusion (residual obligations)

Strengthening at three layers:

1. **Tertiary's helper signature** at `WedhornStandardCoverRefinement.lean:91`
   would need the third clause appended. The actual ratio construction
   `f := σ * t * D.s ^ (N - 1)` (per the proof sketch in Tertiary's
   docblock) DOES satisfy `v(f) ≠ 0` when `t = D.s` (the normalized
   choice): `v(f) = v(σ) · v(D.s)^N`, with `σ` a unit (so `v(σ) ≠ 0`)
   and `v(D.s) ≠ 0` from the input rational-open membership. So the
   strengthening is mathematically free — it is a signature-level
   change. **BLOCKED**: this file cannot edit Tertiary's file.

2. **Secondary's compactness extraction**
   (`mk_S_D_of_C1_and_compactness` in `WedhornCompactExtraction.lean`)
   would need to propagate the third clause through the
   finite-subcover step. The natural refinement: replace the open
   cover `V w := Subtype.val ⁻¹' rationalOpen (insert (g w) C.base.T) C.base.s`
   with `V' w := V w ∩ Subtype.val ⁻¹' rationalOpen ∅ (g w)` (the
   `rationalOpen ∅ a = {v ∈ Spa : ¬ v.vle a 0}` form, open by
   `rationalOpen_isOpen`). The `V' w`-cover still covers `K` (each
   witness point satisfies all three clauses), and the finite-subcover
   output now carries `¬ v.vle f 0` for arbitrary `v` in the chosen
   plus-piece. **BLOCKED**: this file cannot edit Secondary's file.

3. **Workaround at this leaf-file level**: re-implementing the
   compactness extraction in a separate leaf file (with the refined
   `V'` cover above) avoids editing Secondary's file. This is a
   straightforward port of Secondary's proof and is the natural next
   ticket; **NOT included here** to keep this audit deliverable small.

The current file lands only piece (1)'s **abstract Prop predicate** plus
the pointwise bridge — exactly the shape `WedhornStage2SpanExtractor`
will consume once the strengthened compactness extraction is in scope.

## Notes

* No root import: leaf-level, not in `Adic spaces.lean`.
* No edits to `StandardCover.lean`, `StandardCoverConditionalBridge.lean`,
  `WedhornCompactExtraction.lean` (Secondary), or
  `WedhornStandardCoverRefinement.lean` (Tertiary).
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson /
  T001 / faithful-flatness content.
* Imports only `StandardCover`. -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Strengthened local C1 supplier predicate**.

Augments `StandardCoverConditionalBridge.C1Supplier_local`
(`StandardCoverConditionalBridge.lean`, commit `240b682`) with the
**third clause** `¬ v.vle f 0` — i.e., the supplied `f` additionally
satisfies `v(f) ≠ 0` at the test point `v`.

Mathematically: under Tertiary's actual ratio construction
`f := σ · t · D.s ^ (N - 1)` (with `σ` a Cor 7.32 unit and `t = D.s`
the normalized choice), `v(f) = v(σ) · v(D.s) ^ N`, with both factors
non-zero on `rationalOpen D.T D.s`. So this strengthening is a
signature-level update, not a new mathematical content step. -/
def C1SupplierStrong_local [DecidableEq A] (C : RationalCoveringData A) : Prop :=
  ∀ (D : RationalLocData A) (_hD : D ∈ C.covers)
    (v : Spv A) (_hv : v ∈ rationalOpen D.T D.s)
    (t : A) (_ht : t ∈ D.T)
    (_hvt : v.vle t D.s) (_hvD_s : ¬ v.vle D.s 0),
    ∃ f : A,
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s ∧
      ¬ v.vle f 0

/-- **Bridge: strengthened C1 supplier → strengthened pointwise C1
refinement**.

Given a strengthened supplier `h_C1_strong` and the normalization
`D.s ∈ D.T`, instantiate the supplier with `t := D.s` to obtain the
strengthened pointwise C1 form

```
∃ f : A,
  v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
  rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s ∧
  ¬ v.vle f 0
```

This is the strengthened analogue of
`StandardCoverConditionalBridge.exists_single_f_refining_point_in_D_via_C1Supplier`.

The third clause `¬ v.vle f 0` is what
`WedhornStage2SpanExtractor.span_top_via_strengthened_cover_and_outside_rescue`
(commit `63c8ecd`) consumes via its `h_cover_D_nonzero` hypothesis. -/
theorem exists_single_f_refining_point_in_D_via_C1SupplierStrong
    [DecidableEq A] (C : RationalCoveringData A)
    (h_C1_strong : C1SupplierStrong_local C)
    (D : RationalLocData A) (hD : D ∈ C.covers)
    (hD_s_mem : D.s ∈ D.T)
    (v : Spv A) (hv : v ∈ rationalOpen D.T D.s) :
    ∃ f : A,
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s ∧
      ¬ v.vle f 0 :=
  h_C1_strong D hD v hv D.s hD_s_mem (v.vle_total D.s D.s |>.elim id id) hv.2.2

end ValuationSpectrum

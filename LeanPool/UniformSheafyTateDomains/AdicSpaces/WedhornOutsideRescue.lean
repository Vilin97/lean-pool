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
# Wedhorn Outside-Base Rescue: audit + minimal bridge

`WedhornStage2SpanExtractor.span_top_via_strengthened_cover_and_outside_rescue`
(commit `63c8ecd`) consumes a hypothesis

```
h_outside_rescue : ∀ v ∈ Spa A A⁺,
  v ∉ rationalOpen C.base.T C.base.s →
    ∃ f ∈ C.covers.biUnion mk_S_D, ¬ v.vle f 0
```

handling Spa-points outside `rationalOpen C.base.T C.base.s` that the
C1/compactness chain cannot reach (because `RationalCoveringData.hcover`
only covers the base). This file audits the derivability of
`h_outside_rescue` from existing data and lands the smallest bridge.

## Audit conclusion

`h_outside_rescue` is **not** derivable from the `RationalCoveringData` data
alone (`base`, `covers`, `hsubset`, `hcover`). The `hcover` field gives
information only for `v ∈ rationalOpen C.base.T C.base.s`; it says
nothing about `Spa A A⁺ \ rationalOpen C.base.T C.base.s`. The
`mk_S_D` family produced by the C1/compactness chain inherits this
limitation: each `mk_S_D D` is a per-piece selector inside the base,
not an external rescue family.

The cleanest sufficient external hypothesis is

```
h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺
```

which makes the outside set empty and the rescue clause vacuously true.
This is the **standard Wedhorn cover-of-Spa setup** (Wedhorn Remark 8.3
realised at `Presheaf.rationalOpen_singleton_one`,
`rationalOpen ({1} : Finset A) (1 : A) = Spa A A⁺`); a `RationalCoveringData`
constructed with `base.T := {1}` and `base.s := 1` satisfies it
unconditionally.

## Why current data is insufficient

`v ∉ rationalOpen C.base.T C.base.s` means `v ∈ Spa A A⁺` and at least
one of:

* `∃ t ∈ C.base.T, ¬ v.vle t C.base.s` — some test fails;
* `v.vle C.base.s 0` — denominator is zero.

In both cases, no element of `mk_S_D D` for `D ∈ C.covers` is
constrained to be non-zero on `v`: the C1 condition
`rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s`
controls behaviour only inside the base. A direct algebraic argument
that some `f ∈ biUnion mk_S_D` has `¬ v.vle f 0` would require either
(a) augmenting the union family with `C.base.s` and `C.base.T`, then
combining with `spanTop_iff_noCommonZero_spa` (Prop 7.14) on the
augmented family, or (b) the `base = Spa` simplification below.

## What this file provides

* `outside_rescue_of_base_eq_Spa` — under
  `rationalOpen C.base.T C.base.s = Spa A A⁺`, the outside-rescue
  hypothesis (parameterised over `mk_S_D` as in
  `WedhornFinalAssemblyBridge`) holds vacuously.

* `outside_rescue_pointwise_of_base_eq_Spa` — the pointwise version
  consumed directly by
  `span_top_via_strengthened_cover_and_outside_rescue`.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness content.
* Does not edit `WedhornStage2SpanExtractor`,
  `WedhornFinalAssemblyBridge`, `WedhornNormalizedC1Assembly`,
  `WedhornC1Assembly`, `WedhornCompactExtraction`,
  `WedhornCoverNormalization`, `StandardCover`, Primary's strengthened
  assembly files, Tertiary's prelocalization-plus work, or root imports.
* Imports only `StandardCover` (for `Spa`, `rationalOpen`,
  `RationalCoveringData`).
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A] [DecidableEq A]

/-- **Pointwise outside-rescue under `base = Spa`** — direct consumer of
`WedhornStage2SpanExtractor.span_top_via_strengthened_cover_and_outside_rescue`.

Under `h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺`,
the premise `v ∉ rationalOpen C.base.T C.base.s` (with `v ∈ Spa A A⁺`)
is contradictory, so the conclusion is vacuously true. -/
theorem outside_rescue_pointwise_of_base_eq_Spa
    (C : RationalCoveringData A)
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    (mk_S_D : RationalLocData A → Finset A) :
    ∀ v ∈ Spa A A⁺,
      v ∉ rationalOpen C.base.T C.base.s →
        ∃ f ∈ C.covers.biUnion mk_S_D, ¬ v.vle f 0 := by
  intro v hv_spa hv_outside
  exact absurd (h_base_eq_Spa ▸ hv_spa) hv_outside

/-- **Outside-rescue under `base = Spa`, parameterised over `mk_S_D` and
`h_in_D`** — the consumer shape used by
`WedhornFinalAssemblyBridge.hZavyalov_per_E_via_normalized_C1_supplier_explicit_stage2`.

Under `h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺`,
the outside set is empty and the rescue clause holds vacuously, for any
`mk_S_D` and any `h_in_D` containment data. -/
theorem outside_rescue_of_base_eq_Spa
    (C : RationalCoveringData A)
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺) :
    ∀ mk_S_D : RationalLocData A → Finset A,
      (∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
        rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s) →
      ∀ v ∈ Spa A A⁺,
        v ∉ rationalOpen C.base.T C.base.s →
          ∃ f ∈ C.covers.biUnion mk_S_D, ¬ v.vle f 0 :=
  fun mk_S_D _ => outside_rescue_pointwise_of_base_eq_Spa C h_base_eq_Spa mk_S_D

end ValuationSpectrum

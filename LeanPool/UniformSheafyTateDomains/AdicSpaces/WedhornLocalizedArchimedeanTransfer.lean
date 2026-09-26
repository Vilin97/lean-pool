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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalizedCor732Consumer

/-!
# MulArchimedean transfer through `comap` for the localized Cor 7.32

The genuine remaining external hypothesis identified in
`WedhornLocalizedCor732Consumer.lean` (commit `a973ca2`):
**`hArch_loc`** for every `w : Spv (Localization.Away s)`, given the
global `hArch` for `Spv A`.

## Mathematical content

For `w : Spv B` with `B = Localization.Away s`, the canonical valuation
ν_B determines a value group `ValueGroupWithZero B` (under
`w.toValuativeRel`). The `comap (algebraMap A B) w : Spv A` has its own
value group `ValueGroupWithZero A`.

For `B = Localization.Away s` (a localization at a single element),
every `b ∈ B` has the form `a / s^k` for `a ∈ A` and `k : ℕ`. Hence
`ν_B(b) = ν_A(a) · ν_A(s)^(-k)` (provided `ν_A(s) ≠ 0`, which we have
when `w` corresponds to a Spa-point of `B` whose comap satisfies
`¬ comap_v.vle s 0`).

Consequently `ν_B`'s value group is generated multiplicatively by
classes of `A`-elements (and the inverse of the class of `s`), which
equals (or is isomorphic to) `ν_A`'s value group as multiplicatively-
ordered groups. MulArchimedean transfers through this isomorphism.

## What this file provides

`hArch_loc_via_value_group_iso` — the **scaffold theorem** that takes
a per-`w` value-group iso as an explicit hypothesis and produces the
target `hArch_loc`. The proof: apply the iso's order-preserving
structure to transfer MulArchimedean from `ValueGroupWithZero A` (under
`comap w`'s ValuativeRel, by global `hArch`) to
`ValueGroupWithZero B` (under `w`'s ValuativeRel).

The value-group iso itself is the **single named residual** —
documented as the precise missing Mathlib-level API at the file's end.

## Notes

* No root import; leaf-level file.
* No edits to committed bridge files or Secondary's branch-link file.
* No `IsLinearTopology` route, no span-basis route.
* No Lane B / Cor 8.32 / Jacobson / T001 / faithful-flatness /
  final-acyclicity content. -/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **Scaffold MulArchimedean transfer for the localized Cor 7.32**.

Takes a per-`w` value-group iso between
`ValueGroupWithZero (Localization.Away s)` (under `w.toValuativeRel`)
and `ValueGroupWithZero A` (under `(comap (algebraMap A _) w).toValuativeRel`),
and produces the target `hArch_loc` from the global `hArch`.

**The value-group iso is the documented residual** (see file's docblock
end). With it in hand, the proof composes:
1. Apply `hArch` to `comap (algebraMap A _) w` to get `MulArchimedean
   (ValueGroupWithZero A)`.
2. Transfer via the iso (`MulArchimedean` is preserved by
   `MulEquiv ∘ OrderIso` — i.e., `OrderMulIso`).

The `letI`/`Nonempty` packaging avoids carrying the iso explicitly when
it isn't needed by the conclusion. -/
theorem hArch_loc_via_value_group_iso
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (hArch : ∀ v : Spv A,
      letI : ValuativeRel A := v.toValuativeRel
      MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (h_transfer : ∀ w : Spv (Localization.Away s),
      letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
      letI : ValuativeRel A := (comap (algebraMap A (Localization.Away s)) w).toValuativeRel
      MulArchimedean (ValuativeRel.ValueGroupWithZero A) →
        MulArchimedean (ValuativeRel.ValueGroupWithZero (Localization.Away s))) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    ∀ w : Spv (Localization.Away s),
      letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
      MulArchimedean (ValuativeRel.ValueGroupWithZero (Localization.Away s)) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  intro w
  exact h_transfer w (hArch (comap (algebraMap A (Localization.Away s)) w))

/-! ## Single residual: the value-group transfer

The genuine remaining piece — the per-`w` MulArchimedean-transfer
along `comap (algebraMap A (Localization.Away s))`. The full Lean
signature:

```lean
theorem mulArchimedean_localization_comap_transfer
    {A : Type*} [CommRing A] (s : A)
    (w : Spv (Localization.Away s))
    (hws : ¬ w.vle (algebraMap A _ s) 0) :  -- s non-degenerate at w
    letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
    letI : ValuativeRel A :=
      (comap (algebraMap A (Localization.Away s)) w).toValuativeRel
    MulArchimedean (ValuativeRel.ValueGroupWithZero A) →
      MulArchimedean (ValuativeRel.ValueGroupWithZero (Localization.Away s))
```

**Mathematical justification**: The value group of `w` on
`Localization.Away s` is generated multiplicatively by `w(b)` for
`b ∈ B`. Every `b = a / s^k`, so `w(b) = w(algebraMap a) · w(algebraMap s)^(-k) =
v(a) · v(s)^(-k)` where `v := comap (algebraMap A _) w`. Since `v(s) ≠ 0`
(by `hws`), `v(s)⁻¹` exists in `v`'s value group (it's a
`ValueGroupWithZero` which IS a group on its non-zero elements). So
`w`'s value group `=` `v`'s value group as ordered multiplicative
groups. MulArchimedean transfers through equality / iso of ordered
groups.

**The residual splits into two precise sub-residuals**:

1. **A `ValueGroupWithZero` iso lemma** for `comap`: given
   `φ : A →+* B` and `w : ValuativeRel B`, when do
   `ValueGroupWithZero A` (under `comap φ w`) and `ValueGroupWithZero B`
   (under `w`) agree (as ordered groups)? For `B = Localization.Away s`
   and `φ = algebraMap`, the iso is the localization-extension
   isomorphism. This iso likely exists in Mathlib's `IsLocalization`
   API as a result on `Valuation.extendToLocalization` — needs
   excavation.

2. **MulArchimedean transfer along the iso**: standard fact that
   MulArchimedean is preserved by ordered group isomorphisms. Likely
   already in Mathlib as `MulArchimedean.of_orderIso` or similar; if
   not, a small wrapper around the existing `MulArchimedean` API.

Without `mulArchimedean_localization_comap_transfer`, the wrapper
`hArch_loc_via_value_group_iso` is the strongest theorem-level
reduction available in this file. The next concrete sub-target is
the value-group iso lemma. -/

omit [TopologicalSpace A] [IsTopologicalRing A] in
/-- **Reduction via `MulArchimedean.comap`**: given a strictly monotonic
monoid homomorphism `f : ValueGroupWithZero (Localization.Away s) →*
ValueGroupWithZero A` (under the appropriate ValuativeRels), the
MulArchimedean transfer follows from `MulArchimedean.comap` (Mathlib's
`Algebra.Order.Archimedean.Basic`).

This packages the residual `mulArchimedean_localization_comap_transfer`
into a clean monoid-hom-based form. The genuine missing piece becomes
**just the construction of `f` and its strict monotonicity**, which
splits into:

* `f := the natural projection ValueGroupWithZero(B) → ValueGroupWithZero(A)`
  arising from the comap structure (b = a/s^k in B has class
  v(a)/v(s)^k in A's value group).
* `StrictMono f`: order-preservation under the comap-induced map.

Both pieces follow from the Mathlib `IsLocalization` × `extendToLocalization`
infrastructure once the right name is excavated. The proof is then
one line: `MulArchimedean.comap f hf hArch_A`. -/
theorem mulArchimedean_localization_comap_via_strictMono_hom
    (s : A) (w : Spv (Localization.Away s))
    (hArch_A :
      letI : ValuativeRel A :=
        (comap (algebraMap A (Localization.Away s)) w).toValuativeRel
      MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (f :
      letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
      letI : ValuativeRel A :=
        (comap (algebraMap A (Localization.Away s)) w).toValuativeRel
      ValuativeRel.ValueGroupWithZero (Localization.Away s) →*
        ValuativeRel.ValueGroupWithZero A)
    (hf :
      letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
      letI : ValuativeRel A :=
        (comap (algebraMap A (Localization.Away s)) w).toValuativeRel
      StrictMono f) :
    letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
    MulArchimedean
      (ValuativeRel.ValueGroupWithZero (Localization.Away s)) := by
  letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
  letI : ValuativeRel A :=
    (comap (algebraMap A (Localization.Away s)) w).toValuativeRel
  haveI : MulArchimedean (ValuativeRel.ValueGroupWithZero A) := hArch_A
  exact MulArchimedean.comap f hf

end ValuationSpectrum

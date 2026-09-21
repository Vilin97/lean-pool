/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.SphereTopHomologyReduction
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Reduced-to-unreduced bridge for sphere top homology

This file builds the **genuine** reduced-to-unreduced comparison for integral
singular homology and uses it to reduce the positive-dimensional sphere top-homology family to the corresponding *reduced* statement.

## Reduced homology, honestly

Pinned Mathlib (`v4.28.0`, commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`) has
**no** reduced-homology API, no suspension, no Mayer–Vietoris and no excision (see
than assume a reduced theory, we *define* reduced integral singular homology in the
standard way, as the kernel of the augmentation to a point:

```text
H̃ₙ(X; ℤ) := ker ( Hₙ(X; ℤ) --Hₙ(X → pt)--> Hₙ(pt; ℤ) ).
```

This is a legitimate definition of reduced homology (the kernel of the map induced
by the unique map to a one-point space), and it requires

## The bridge (proved)

For `n ≥ 1` the point has vanishing homology `Hₙ(pt; ℤ) = 0` (the one-point space
is totally disconnected, via Mathlib's
`isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`). Hence the
augmentation `Hₙ(X) → Hₙ(pt)` is the zero map and its kernel is all of `Hₙ(X)`:

```text
n ≥ 1 ⇒ H̃ₙ(X; ℤ) ≅ Hₙ(X; ℤ). (`reducedToUnreducedIso`)
```

This is the exact reduced/unreduced comparison theorem requested by the project,
proved as an actual Lean isomorphism, not assumed.

## Consequence for the sphere top-homology family

Transporting along the bridge turns a *reduced* sphere top-homology computation
into the ordinary one consumed by the degree API:

```text
(∀ n ≥ 1, H̃ₙ(Sⁿ; ℤ) ≅ ℤ) ⇒ ∀ n ≥ 1, Hₙ(Sⁿ; ℤ) ≅ ℤ.
```

i.e. `sphereTopHomologyIsoPos_of_reducedSphereHomology`, and as a
`SphereOrientationPos` via `sphereOrientationPos_of_reducedSphereHomology`.

## Honest blocker recorded

In the *positive degree* regime reduced and unreduced homology **coincide** (this
file proves exactly that), so the bridge alone supplies no new computation: the
hypothesis `H̃ₙ(Sⁿ) ≅ ℤ` for `n ≥ 1` is, via the bridge, equivalent to the goal
`Hₙ(Sⁿ) ≅ ℤ`. The genuine content needed to *discharge* that reduced hypothesis is
the **reduced suspension isomorphism** `H̃ₖ(Sⁿ) ≅ H̃ₖ₋₁(Sⁿ⁻¹)` (with base
`H̃₀(S⁰) ≅ ℤ`), which rests on Mayer–Vietoris / excision and is absent from pinned
Mathlib. Consequently `SphereSuspensionTower.step` is **not** fillable from this
choice`, `Quot.sound`).
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace SphereOddDegree

/-! ## The one-point space and the augmentation map -/

/-- The unique continuous map from a space `X` to the one-point space `PUnit`.
It induces the augmentation on homology. -/
def toPUnit (X : TopCat.{0}) : X ⟶ TopCat.of (PUnit : Type) :=
  TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩

/-- **Reduced integral singular homology** of a space `X`, defined as the kernel of
the augmentation `Hₙ(X; ℤ) → Hₙ(pt; ℤ)` induced by the unique map `X → pt`. -/
def reducedSingularHomologyℤ (n : ℕ) (X : TopCat.{0}) : ModuleCat.{0} ℤ :=
  kernel ((singularHomologyℤ n).map (toPUnit X))

/-! ## Vanishing of point homology in positive degree -/

/-- `Hₙ(pt; ℤ) = 0` for `n ≥ 1`: the one-point space is totally disconnected, so
its higher singular homology vanishes. -/
theorem isZero_singularHomologyℤ_punit_of_pos (n : ℕ) (hn : 1 ≤ n) :
    IsZero ((singularHomologyℤ n).obj (TopCat.of (PUnit : Type))) :=
  isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{0} ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of (PUnit : Type)) (by omega)

/-! ## The reduced-to-unreduced bridge -/

/-- **Bridge, general form.** Whenever the point's `n`-th homology vanishes, reduced
and unreduced `n`-th homology of `X` agree. The augmentation `Hₙ(X) → Hₙ(pt)` is
then the zero map, whose kernel is all of `Hₙ(X)`. -/
def reducedToUnreducedIsoOfIsZero (n : ℕ) (X : TopCat.{0})
    (hpt : IsZero ((singularHomologyℤ n).obj (TopCat.of (PUnit : Type)))) :
    reducedSingularHomologyℤ n X ≅ (singularHomologyℤ n).obj X :=
  kernelIsoOfEq (hpt.eq_of_tgt _ 0) ≪≫ kernelZeroIsoSource

/-- **Reduced-to-unreduced bridge.** For `n ≥ 1`, reduced and unreduced integral
singular homology agree: `H̃ₙ(X; ℤ) ≅ Hₙ(X; ℤ)`. -/
def reducedToUnreducedIso (n : ℕ) (hn : 1 ≤ n) (X : TopCat.{0}) :
    reducedSingularHomologyℤ n X ≅ (singularHomologyℤ n).obj X :=
  reducedToUnreducedIsoOfIsZero n X (isZero_singularHomologyℤ_punit_of_pos n hn)

/-! ## Consequence for the sphere top-homology family -/

/-- Transport a reduced sphere top-homology identification `H̃ₙ(Sⁿ; ℤ) ≅ ℤ`
(`n ≥ 1`) across the bridge to the ordinary identification `Hₙ(Sⁿ; ℤ) ≅ ℤ`
required by the degree API. -/
def sphereTopHomologyIso_of_reduced {n : ℕ} (hn : 1 ≤ n)
    (e : reducedSingularHomologyℤ n (TopCat.sphere.{0} n) ≅ ModuleCat.of ℤ ℤ) :
    SphereTopHomologyIso n :=
  (reducedToUnreducedIso n hn (TopCat.sphere.{0} n)).symm ≪≫ e

/-- **Reduced ⇒ ordinary, for the whole positive family.** A reduced sphere
top-homology computation in every dimension `n ≥ 1` yields the ordinary
top-homology identification `Hₙ(Sⁿ; ℤ) ≅ ℤ` in every dimension `n ≥ 1`. -/
def sphereTopHomologyIsoPos_of_reducedSphereHomology
    (red : ∀ n : ℕ, 1 ≤ n →
      (reducedSingularHomologyℤ n (TopCat.sphere.{0} n) ≅ ModuleCat.of ℤ ℤ)) :
    ∀ n : ℕ, 1 ≤ n → SphereTopHomologyIso n :=
  fun n hn => sphereTopHomologyIso_of_reduced hn (red n hn)

/-- A reduced sphere top-homology computation yields a genuine (non-vacuous)
positive sphere orientation, hence the unconditional positive-degree theory. -/
def sphereOrientationPos_of_reducedSphereHomology
    (red : ∀ n : ℕ, 1 ≤ n →
      (reducedSingularHomologyℤ n (TopCat.sphere.{0} n) ≅ ModuleCat.of ℤ ℤ)) :
    SphereOrientationPos :=
  ⟨sphereTopHomologyIsoPos_of_reducedSphereHomology red⟩

end SphereOddDegree

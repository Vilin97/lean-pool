/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RouteBVectorFiberElimination

/-!
# Route B: the actual selected local vector block

This file records the collar-specific fact required by the vector-fiber repair
of Steps 4 and 5.  At one local vertex, the `p` coordinate sites determine `p`
distinct scalar-orbit parameters.  Moreover, frozen status depends only on the
geometric vertex, not on the coordinate.

The proof uses the `vertex_orbit_injective` field of
`RelativeAffineCellSystem`; it does not assume freeness of the quotient action
without justification.
-/

@[expose] public section

namespace NRR

open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace ExplicitAffineRelativeCollar
namespace RouteB

open Parameters
open RelativeGenericity

variable {p N₀ N₁ M L : Nat}
variable (hp : Nat.Prime p)
variable (C : RelativeAffineCellSystem hp N₀ N₁ M L)

/-- The local scalar-orbit parameter map is injective in both the vertex and
coordinate indices. -/
theorem localParameter_injective
    (q : C.Cell) :
    Function.Injective (fun z : Fin (p + 1) × Fin p =>
      localParameter hp C q z.1 z.2) := by
  intro a b hab
  have horbit :
      MulAction.orbitRel (PrimeSymmetry p)
        (ScalarSite hp C)
        (sampleVertex hp C (q, a.1), a.2)
        (sampleVertex hp C (q, b.1), b.2) :=
    Quotient.exact hab
  rw [MulAction.orbitRel_apply] at horbit
  obtain ⟨g, hg⟩ := horbit
  have hx : g • sampleVertex hp C (q, b.1) =
      sampleVertex hp C (q, a.1) := by
    simpa using congrArg Prod.fst hg
  have hj : g • b.2 = a.2 := by
    simpa using congrArg Prod.snd hg
  have hpoint : g • C.vertex q b.1 = C.vertex q a.1 := by
    have hglobal := congrArg (globalPoint hp C) hx
    simpa [globalPoint_smul, globalPoint_sampleVertex,
      RelativeAffineCellSystem.slotPoint] using hglobal
  obtain ⟨hg1, hij⟩ := C.vertex_orbit_injective q g b.1 a.1 hpoint
  apply Prod.ext
  · exact hij.symm
  · have hcoord : b.2 = a.2 := by simpa [hg1] using hj
    exact hcoord.symm

/-- Frozen status of a local scalar parameter is independent of its coordinate
index. -/
theorem isFrozenParameter_localParameter_iff
    (q : C.Cell) (i : Fin (p + 1)) (j : Fin p) :
    IsFrozenParameter hp C (localParameter hp C q i j) ↔
      IsHorizontalPoint (C.vertex q i) := by
  change IsFrozenVertex hp C (sampleVertex hp C (q, i)) ↔ _
  simp [IsFrozenVertex, RelativeAffineCellSystem.slotPoint]

/-- If one coordinate at a local vertex is movable, then every coordinate at
that vertex is movable. -/
theorem localParameter_movable_of_one_coordinate
    (q : C.Cell) (i : Fin (p + 1)) (j₀ j : Fin p)
    (h : ¬ IsFrozenParameter hp C (localParameter hp C q i j₀)) :
    ¬ IsFrozenParameter hp C (localParameter hp C q i j) := by
  intro hj
  apply h
  rw [isFrozenParameter_localParameter_iff hp C q i j₀]
  exact (isFrozenParameter_localParameter_iff hp C q i j).1 hj

namespace MixedFaceCase

/-- The complete movable `p`-coordinate block belonging to the retained local
vertex selected by a mixed-face case. -/
noncomputable def vectorParameter
    (κ : MixedFaceCase hp C) (j : Fin p) : MovableParameter hp C :=
  ⟨localParameter hp C κ.cell κ.retained j,
    localParameter_movable_of_one_coordinate hp C κ.cell κ.retained
      κ.coordinate j κ.movable⟩

/-- The selected vector block consists of pairwise distinct movable orbit
parameters. -/
theorem vectorParameter_injective
    (κ : MixedFaceCase hp C) :
    Function.Injective (κ.vectorParameter hp C) := by
  intro j k hjk
  have hfull :
      localParameter hp C κ.cell κ.retained j =
        localParameter hp C κ.cell κ.retained k :=
    congrArg Subtype.val hjk
  have hpair := localParameter_injective hp C κ.cell
    (a₁ := (κ.retained, j)) (a₂ := (κ.retained, k)) hfull
  exact congrArg Prod.snd hpair

/-- The scalar parameter used in Step 4 is one coordinate of the full selected
vector block. -/
@[simp] theorem vectorParameter_coordinate
    (κ : MixedFaceCase hp C) :
    κ.vectorParameter hp C κ.coordinate = κ.selectedParameter hp C := by
  apply Subtype.ext
  rfl

end MixedFaceCase

end RouteB
end ExplicitAffineRelativeCollar
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR

/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EndpointStackLastVertexCore
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ExplicitAffineRelativeCollar
/-!
# Global descent interface for the endpoint-stack last-vertex assignment

The local last-vertex map from `EndpointStackLastVertexCore` assigns a coarse endpoint value to
each local vertex occurrence of one one-step subdivision cylinder.  To obtain a genuine collar
assignment these local values must agree on every pair of symmetry-decorated occurrences which
represent the same geometric cylinder point.

This file packages that exact compatibility condition, proves that it is sufficient to descend the
local values to the global vertex quotient and then to the diagonal scalar-parameter quotient, and
recovers the local cell values and cellwise origin avoidance.  No compatibility assumption is
hidden: the required compatibility theorem is `OneStepLastVertexCompatible`.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace EndpointStackGlobalDescent

noncomputable section

open RefinedAffineMap
open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open ExplicitAffineRelativeCollar.Polynomials
open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap


variable {p : Nat}

/-- The one-step endpoint cylinder used throughout this module. -/
noncomputable abbrev Cells (hp : Nat.Prime p) (N : Nat) :=
  RelativeSubdivisionOneStepCells.cellSystem hp N

/-- Coarse endpoint realization vertex selected at one local one-step-cylinder occurrence. -/
noncomputable def selectedPoint
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (s : (Cells hp A.level).VertexSlot) : Realization p :=
  RefinedAffineMap.vertex hp A.level s.1.1
    (EndpointStackLastVertexCore.endpointIndex hp s.1.2 s.2)

/-- Selected endpoint point on a symmetry-decorated occurrence. -/
noncomputable def decoratedSelectedPoint
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (s : CoverVertexSlot hp (Cells hp A.level)) : Realization p :=
  s.1 • selectedPoint hp A s.2

/-- Coarse endpoint value selected at one local one-step-cylinder vertex occurrence. -/
noncomputable def selectedVector
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (s : (Cells hp A.level).VertexSlot) : Fin p → Real :=
  A.map (RefinedAffineMap.vertex hp A.level s.1.1
    (EndpointStackLastVertexCore.endpointIndex hp s.1.2 s.2))

/-- Value on a symmetry-decorated local occurrence. -/
noncomputable def decoratedSelectedVector
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (s : CoverVertexSlot hp (Cells hp A.level)) : Fin p → Real :=
  s.1 • selectedVector hp A s.2

/-- Pure geometric compatibility statement for the endpoint-stack last-vertex retraction.
Two decorated occurrences of one global cylinder vertex must select the same decorated endpoint
realization vertex. -/
def OneStepLastVertexPointCompatible
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F) : Prop :=
  ∀ a b : CoverVertexSlot hp (Cells hp A.level),
    coverPoint hp (Cells hp A.level) a = coverPoint hp (Cells hp A.level) b →
      decoratedSelectedPoint hp A a = decoratedSelectedPoint hp A b

/-- Decorated selected vectors are samples of the global approximation map at decorated selected
points. -/
theorem decoratedSelectedVector_eq_map
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (s : CoverVertexSlot hp (Cells hp A.level)) :
    decoratedSelectedVector hp A s = A.map (decoratedSelectedPoint hp A s) := by
  symm
  exact A.equivariant s.1 (selectedPoint hp A s.2)

/-- Exact global overlap condition required for the local last-vertex values to descend.

This is the simplicial-carrier compatibility theorem in value form.  It says that two decorated local
occurrences representing the same geometric cylinder point select the same equivariant endpoint
value. -/
def OneStepLastVertexCompatible
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F) : Prop :=
  ∀ a b : CoverVertexSlot hp (Cells hp A.level),
    coverPoint hp (Cells hp A.level) a = coverPoint hp (Cells hp A.level) b →
      decoratedSelectedVector hp A a = decoratedSelectedVector hp A b

/-- The geometric point-compatibility theorem implies the value-compatibility theorem. -/
theorem oneStepLastVertexCompatible_of_pointCompatible
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (hpoint : OneStepLastVertexPointCompatible hp A) :
    OneStepLastVertexCompatible hp A := by
  intro a b hab
  rw [decoratedSelectedVector_eq_map, decoratedSelectedVector_eq_map]
  exact congrArg A.map (hpoint a b hab)

/-- Under the exact overlap theorem, the selected vectors descend to global collar vertices. -/
noncomputable def globalSelectedVector
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (hcompat : OneStepLastVertexCompatible hp A) :
    GlobalVertex hp (Cells hp A.level) → Fin p → Real :=
  Quotient.lift (decoratedSelectedVector hp A) (by
    intro a b hab
    exact hcompat a b hab)

@[simp] theorem globalSelectedVector_mk
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (hcompat : OneStepLastVertexCompatible hp A)
    (s : CoverVertexSlot hp (Cells hp A.level)) :
    globalSelectedVector hp A hcompat (Quotient.mk _ s) =
      decoratedSelectedVector hp A s := rfl

/-- The descended global vector assignment is prime-equivariant. -/
theorem globalSelectedVector_smul
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (hcompat : OneStepLastVertexCompatible hp A)
    (g : PrimeSymmetry hp)
    (x : GlobalVertex hp (Cells hp A.level)) :
    globalSelectedVector hp A hcompat (g • x) =
      g • globalSelectedVector hp A hcompat x := by
  refine Quotient.inductionOn x ?_
  intro s
  rfl

/-- Scalar site value obtained from the descended global vector assignment. -/
noncomputable def selectedSiteValue
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (hcompat : OneStepLastVertexCompatible hp A)
    (s : ScalarSite hp (Cells hp A.level)) : Real :=
  globalSelectedVector hp A hcompat s.1 s.2

/-- The selected scalar site value is constant on diagonal prime orbits. -/
theorem selectedSiteValue_eq_of_orbitRel
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (hcompat : OneStepLastVertexCompatible hp A)
    {a b : ScalarSite hp (Cells hp A.level)}
    (hab : MulAction.orbitRel (PrimeSymmetry hp)
      (ScalarSite hp (Cells hp A.level)) a b) :
    selectedSiteValue hp A hcompat a = selectedSiteValue hp A hcompat b := by
  rw [MulAction.orbitRel_apply] at hab
  rcases hab with ⟨g, rfl⟩
  have h := congrFun (globalSelectedVector_smul hp A hcompat g b.1) (g • b.2)
  simpa [selectedSiteValue, PrimeSymmetry.smul_coordinate_apply,
    PrimeSymmetry.smul_label] using h

/-- Genuine compatible equivariant assignment obtained from the local last-vertex values. -/
noncomputable def assignment
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (hcompat : OneStepLastVertexCompatible hp A) :
    Assignment hp (Cells hp A.level) :=
  fun q => Quotient.liftOn q (selectedSiteValue hp A hcompat) (by
    intro a b hab
    exact selectedSiteValue_eq_of_orbitRel hp A hcompat hab)

/-- The descended assignment reconstructs the intended selected value at every local slot. -/
theorem vectorValue_assignment_sample
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (hcompat : OneStepLastVertexCompatible hp A)
    (s : (Cells hp A.level).VertexSlot) :
    vectorValue hp (Cells hp A.level) (assignment hp A hcompat)
      (sampleVertex hp (Cells hp A.level) s) = selectedVector hp A s := by
  rfl

/-- Local vertex map of the descended assignment is exactly the simplex-local last-vertex map. -/
theorem localVertexMap_assignment_value
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (hcompat : OneStepLastVertexCompatible hp A)
    (q : (Cells hp A.level).Cell)
    (i : Fin (p + 1)) :
    (Polynomials.localVertexMap hp (Cells hp A.level) (assignment hp A hcompat) q).value i =
      A.map (RefinedAffineMap.vertex hp A.level q.1
        (EndpointStackLastVertexCore.endpointIndex hp q.2 i)) := by
  exact vectorValue_assignment_sample hp A hcompat (q, i)

/-- Every one-step endpoint-stack cell of the globally descended assignment avoids the origin. -/
theorem assignment_avoidsOrigin
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (hcompat : OneStepLastVertexCompatible hp A)
    (q : (Cells hp A.level).Cell) :
    AffinePositiveRayBoundary.VertexMap.AvoidsOrigin
      (Polynomials.localVertexMap hp (Cells hp A.level) (assignment hp A hcompat) q) := by
  intro w
  change
    (fun c => ∑ i : Fin (p + 1), w i *
      (Polynomials.localVertexMap hp (Cells hp A.level)
        (assignment hp A hcompat) q).value i c) ≠ 0
  have h := EndpointStackLastVertexCore.affine_selectedEndpointValue_ne_zero hp A q.1 q.2
    (StandardSimplex.toDelta w)
  intro hz
  apply h
  calc
    (fun c => ∑ i : Fin (p + 1), (StandardSimplex.toDelta w) i *
        A.map (vertex hp A.level q.1
          (EndpointStackLastVertexCore.endpointIndex hp q.2 i)) c) =
        (fun c => ∑ i : Fin (p + 1), w i *
          A.map (vertex hp A.level q.1
            (EndpointStackLastVertexCore.endpointIndex hp q.2 i)) c) := by
      funext c
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
    _ = 0 := hz

end

end EndpointStackGlobalDescent
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR

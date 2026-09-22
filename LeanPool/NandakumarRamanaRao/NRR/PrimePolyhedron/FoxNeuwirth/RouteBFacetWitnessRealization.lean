/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RouteBSmallGenericPerturbation
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RouteBSelectedVectorBlock

/-!
# Realizing local facet witnesses with frozen boundary parameters

A local target may prescribe arbitrary vectors at movable vertices, but must agree with the base
assignment at frozen vertices.  Injectivity of the local scalar-parameter map then lets us realize
that target by one global movable-parameter assignment.  This is the algebraic adapter used by the
concrete endpoint-stack facet witnesses.
-/

namespace NRR
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace ExplicitAffineRelativeCollar
namespace RouteB

open Parameters
open Polynomials
open RelativeGenericity
open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap

variable {p N₀ N₁ M L : Nat}
variable (hp : Nat.Prime p)
variable (C : RelativeAffineCellSystem hp N₀ N₁ M L)

/-- A local target respects the relative boundary when it agrees with the base assignment at every
frozen local scalar site. -/
def LocalTargetRespectsFrozen
    (base : Assignment hp C) (q : C.Cell)
    (target : Fin (p + 1) → Fin p → Real) : Prop :=
  ∀ (i : Fin (p + 1)) (j : Fin p),
    IsFrozenParameter hp C (localParameter hp C q i j) →
      target i j = base (localParameter hp C q i j)

/-- Movable assignment realizing one prescribed local target.  Outside the selected local cell it
retains the base movable value. -/
noncomputable def localTargetMove
    (base : Assignment hp C) (q : C.Cell)
    (target : Fin (p + 1) → Fin p → Real) :
    MovableParameter hp C → Real :=
  fun s =>
    if h : ∃ z : Fin (p + 1) × Fin p,
        localParameter hp C q z.1 z.2 = s.1 then
      target (Classical.choose h).1 (Classical.choose h).2
    else
      base s.1

/-- At every movable local scalar site, `localTargetMove` returns the prescribed coordinate. -/
theorem localTargetMove_localParameter
    (base : Assignment hp C) (q : C.Cell)
    (target : Fin (p + 1) → Fin p → Real)
    (i : Fin (p + 1)) (j : Fin p)
    (hmovable : ¬ IsFrozenParameter hp C (localParameter hp C q i j)) :
    localTargetMove hp C base q target
        ⟨localParameter hp C q i j, hmovable⟩ = target i j := by
  classical
  let h : ∃ z : Fin (p + 1) × Fin p,
      localParameter hp C q z.1 z.2 =
        (⟨localParameter hp C q i j, hmovable⟩ : MovableParameter hp C).1 :=
    ⟨(i, j), rfl⟩
  rw [localTargetMove, dite_eq_left h]
  have hchosen : Classical.choose h = (i, j) := by
    apply RouteB.localParameter_injective hp C q
    exact Classical.choose_spec h
  simp [hchosen]

/-- Reconstructing the full assignment from `localTargetMove` realizes the target at every local
vertex, provided the target respects frozen sites. -/
theorem localVertexMap_replaceMovable_localTargetMove
    (base : Assignment hp C) (q : C.Cell)
    (target : Fin (p + 1) → Fin p → Real)
    (hfrozen : LocalTargetRespectsFrozen hp C base q target) :
    localVertexMap hp C
        (replaceMovable hp C base (localTargetMove hp C base q target)) q =
      ⟨target⟩ := by
  rw [VertexMap.mk.injEq]
  funext i j
  rw [localVertexMap_value_apply_eq_assignment_localParameter]
  by_cases h : IsFrozenParameter hp C (localParameter hp C q i j)
  · simpa [replaceMovable, h] using (hfrozen i j h).symm
  · simp [replaceMovable, h,
      localTargetMove_localParameter hp C base q target i j h]

/-- A boundary-respecting local target with nonzero selected facet determinant gives the pointwise
witness consumed by `AllFacetRegularityWitnesses`. -/
theorem exists_facetRegularityWitness_of_localTarget
    (base : Assignment hp C) (q : C.Cell) (k : Fin (p + 1))
    (target : Fin (p + 1) → Fin p → Real)
    (hfrozen : LocalTargetRespectsFrozen hp C base q target)
    (hdet : facetDeterminant hp (⟨target⟩ : VertexMap p) k ≠ 0) :
    ∃ x : MovableParameter hp C → Real,
      facetDeterminant hp
        (localVertexMap hp C (replaceMovable hp C base x) q) k ≠ 0 := by
  refine ⟨localTargetMove hp C base q target, ?_⟩
  rw [localVertexMap_replaceMovable_localTargetMove hp C base q target hfrozen]
  exact hdet

end RouteB
end ExplicitAffineRelativeCollar
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR

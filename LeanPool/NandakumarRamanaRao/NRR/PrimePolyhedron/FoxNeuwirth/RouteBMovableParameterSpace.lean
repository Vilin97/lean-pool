/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ExplicitAffineRelativeCollarGenericity
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Route B, Step 2: the movable parameter space

This file packages the already existing boundary-relative scalar parameters as a
finite-dimensional product of real lines.  It also records the elementary
coordinate-replacement and reconstruction lemmas needed by the incidence
argument.
-/

@[expose] public section

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace ExplicitAffineRelativeCollar
namespace RouteB

open Parameters
open RelativeGenericity
open EquivariantPrismGenericPerturbation

variable {p N₀ N₁ M L : Nat}
variable (hp : Nat.Prime p)
variable (C : RelativeAffineCellSystem hp N₀ N₁ M L)

/-- The finite-dimensional real parameter space of all movable scalar orbits. -/
abbrev MovableParameterSpace := MovableParameter hp C → Real

/-- Movable coordinates extracted from a full assignment. -/
noncomputable def baseMovableParameters
    (base : Assignment hp C) : MovableParameterSpace hp C :=
  movableRestriction hp C base

/-- Reconstruct the full equivariant assignment while retaining every frozen
horizontal coordinate literally. -/
noncomputable def assignmentOfMovableParameters
    (base : Assignment hp C) (x : MovableParameterSpace hp C) : Assignment hp C :=
  replaceMovable hp C base x

@[simp] theorem assignmentOfMovableParameters_frozen
    (base : Assignment hp C) (x : MovableParameterSpace hp C)
    {q : Parameter hp C} (hq : IsFrozenParameter hp C q) :
    assignmentOfMovableParameters hp C base x q = base q :=
  replaceMovable_eq_base hp C base x hq

@[simp] theorem assignmentOfMovableParameters_movable
    (base : Assignment hp C) (x : MovableParameterSpace hp C)
    (q : MovableParameter hp C) :
    assignmentOfMovableParameters hp C base x q.1 = x q :=
  replaceMovable_eq_move hp C base x q

@[simp] theorem assignmentOf_baseMovableParameters
    (base : Assignment hp C) :
    assignmentOfMovableParameters hp C base (baseMovableParameters hp C base) = base :=
  replaceMovable_movableRestriction hp C base

/-- Replace one movable scalar orbit and leave every other movable orbit fixed. -/
noncomputable def replaceCoordinate
    (x : MovableParameterSpace hp C) (q : MovableParameter hp C) (r : Real) :
    MovableParameterSpace hp C :=
  Function.update x q r

@[simp] theorem replaceCoordinate_same
    (x : MovableParameterSpace hp C) (q : MovableParameter hp C) (r : Real) :
    replaceCoordinate hp C x q r q = r := by
  simp [replaceCoordinate]

@[simp] theorem replaceCoordinate_other
    (x : MovableParameterSpace hp C) {q q' : MovableParameter hp C}
    (h : q' ≠ q) (r : Real) :
    replaceCoordinate hp C x q r q' = x q' := by
  simp [replaceCoordinate, h]

/-- Replacing one movable coordinate has no effect on frozen endpoint data. -/
theorem assignment_replaceCoordinate_frozen
    (base : Assignment hp C) (x : MovableParameterSpace hp C)
    (q : MovableParameter hp C) (r : Real)
    {s : Parameter hp C} (hs : IsFrozenParameter hp C s) :
    assignmentOfMovableParameters hp C base (replaceCoordinate hp C x q r) s = base s :=
  assignmentOfMovableParameters_frozen hp C base _ hs

/-- Every reconstructed full assignment remains prime-equivariant. -/
theorem vectorValue_assignmentOfMovableParameters_smul
    (base : Assignment hp C) (x : MovableParameterSpace hp C)
    (g : PrimeSymmetry p) (v : GlobalVertex hp C) :
    vectorValue hp C (assignmentOfMovableParameters hp C base x) (g • v) =
      g • vectorValue hp C (assignmentOfMovableParameters hp C base x) v :=
  vectorValue_smul hp C (assignmentOfMovableParameters hp C base x) g v

/-- Coordinatewise closeness in the movable product. -/
def MovableClose
    (x y : MovableParameterSpace hp C) (ε : Real) : Prop :=
  ∀ q, |x q - y q| < ε

/-- Coordinatewise movable closeness lifts to coordinatewise closeness of the
reconstructed full assignments. -/
theorem assignmentOfMovableParameters_close
    (base : Assignment hp C) (x y : MovableParameterSpace hp C)
    {ε : Real} (hε : 0 < ε) (hxy : MovableClose hp C x y ε) :
    AssignmentClose
      (assignmentOfMovableParameters hp C base x)
      (assignmentOfMovableParameters hp C base y) ε := by
  exact replaceMovable_assignmentClose hp C base x y hε hxy

/-- Evaluation at one movable coordinate is continuous in the product topology. -/
theorem continuous_apply_movableParameter
    (q : MovableParameter hp C) :
    Continuous (fun x : MovableParameterSpace hp C => x q) :=
  continuous_apply q

end RouteB
end ExplicitAffineRelativeCollar
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR

/-! ## Continuity of reconstructed scalar coordinates -/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace ExplicitAffineRelativeCollar
namespace RouteB

open Parameters

variable {p N₀ N₁ M L : Nat}
variable (hp : Nat.Prime p)
variable (C : RelativeAffineCellSystem hp N₀ N₁ M L)

/-- Every scalar coordinate of the reconstructed full assignment depends
continuously on the movable product parameter. -/
theorem continuous_assignmentOfMovableParameters_apply
    (base : Assignment hp C) (q : Parameter hp C) :
    Continuous (fun x : MovableParameterSpace hp C =>
      assignmentOfMovableParameters hp C base x q) := by
  by_cases hq : IsFrozenParameter hp C q
  · simpa [assignmentOfMovableParameters, replaceMovable, hq] using
      (continuous_const : Continuous
        (fun _ : MovableParameterSpace hp C => base q))
  · simpa [assignmentOfMovableParameters, replaceMovable, hq] using
      (continuous_apply (⟨q, hq⟩ : MovableParameter hp C))

end RouteB
end ExplicitAffineRelativeCollar
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR

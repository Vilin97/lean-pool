/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ExplicitAffineRelativeCollarAssignmentCompose
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ExplicitAffineRelativeCollarReverse
/-!
# Reversal of assignments on relative affine collars

Reflection changes only the time coordinate of a collar vertex.  Therefore an assignment on the
original collar can be transported to the reversed collar by using the same decorated local
occurrence.  Injectivity of interval reflection proves that the transported cover value descends
to reversed global vertices.  Local vertex maps are unchanged, so origin avoidance is preserved
literally.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace ExplicitAffineRelativeCollarAssignmentReverse

open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open ExplicitAffineRelativeCollar.Polynomials
open ExplicitAffineRelativeCollarReverse
open ExplicitAffineRelativeCollarAssignmentCompose
open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap

variable {p N₀ N₁ M L : Nat}
variable {hp : Nat.Prime p}

/-- A reversed local occurrence, viewed as the corresponding original occurrence. -/
def originalCoverVertex
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (s : CoverVertexSlot hp (reverseCells C)) : CoverVertexSlot hp C :=
  s

/-- Reversed cover points are reflections of the original cover points. -/
@[simp] theorem coverPoint_reverse
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (s : CoverVertexSlot hp (reverseCells C)) :
    coverPoint hp (reverseCells C) s =
      reflectPoint (coverPoint hp C (originalCoverVertex C s)) := by
  rfl

/-- The original global vertex represented by a reversed local occurrence. -/
noncomputable def originalGlobalVertex
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (s : CoverVertexSlot hp (reverseCells C)) : GlobalVertex hp C :=
  Quotient.mk _ (originalCoverVertex C s)

/-- Piecewise value used for descent to reversed global vertices. -/
noncomputable def reverseCoverVector
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (a : Assignment hp C)
    (s : CoverVertexSlot hp (reverseCells C)) : Fin p → Real :=
  vectorValue hp C a (originalGlobalVertex C s)

/-- Equality of reflected geometric vertices implies equality of their original quotient
vertices. -/
theorem reverseCoverVector_eq_of_coverPoint_eq
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (a : Assignment hp C)
    {s t : CoverVertexSlot hp (reverseCells C)}
    (hst : coverPoint hp (reverseCells C) s = coverPoint hp (reverseCells C) t) :
    reverseCoverVector C a s = reverseCoverVector C a t := by
  apply congrArg (vectorValue hp C a)
  apply Quotient.sound
  apply reflectPoint_injective
  simpa [coverPoint_reverse] using hst

/-- Descended vector assignment on the reversed collar. -/
noncomputable def reverseGlobalVector
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (a : Assignment hp C) :
    GlobalVertex hp (reverseCells C) → Fin p → Real :=
  Quotient.lift (reverseCoverVector C a) (by
    intro s t hst
    exact reverseCoverVector_eq_of_coverPoint_eq C a hst)

@[simp] theorem reverseGlobalVector_mk
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (a : Assignment hp C)
    (s : CoverVertexSlot hp (reverseCells C)) :
    reverseGlobalVector C a (Quotient.mk _ s) =
      vectorValue hp C a (Quotient.mk _ (originalCoverVertex C s)) := by
  rfl

/-- Reversal preserves prime equivariance. -/
theorem reverseGlobalVector_smul
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (a : Assignment hp C)
    (g : PrimeSymmetry hp)
    (x : GlobalVertex hp (reverseCells C)) :
    reverseGlobalVector C a (g • x) = g • reverseGlobalVector C a x := by
  refine Quotient.inductionOn x ?_
  rintro ⟨h, ⟨q, i⟩⟩
  change vectorValue hp C a (Quotient.mk _ (g * h, (q, i))) =
    g • vectorValue hp C a (Quotient.mk _ (h, (q, i)))
  have hact :
      g • (Quotient.mk _ (h, (q, i)) : GlobalVertex hp C) =
        Quotient.mk _ (g * h, (q, i)) := by
    change Quotient.map (actCoverVertex hp C g) _ (Quotient.mk _ (h, (q, i))) = _
    rfl
  rw [← hact]
  exact vectorValue_smul hp C a g (Quotient.mk _ (h, (q, i)))

/-- Assignment transported to the reversed cell system. -/
noncomputable def reverseAssignment
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (a : Assignment hp C) : Assignment hp (reverseCells C) :=
  assignmentOfEquivariantVector (reverseCells C) (reverseGlobalVector C a)
    (reverseGlobalVector_smul C a)

/-- Reversal does not change any local target vertex value. -/
theorem localVertexMap_reverseAssignment
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (a : Assignment hp C) (q : C.Cell) :
    localVertexMap hp (reverseCells C) (reverseAssignment C a) q =
      localVertexMap hp C a q := rfl

/-- Cellwise origin avoidance is preserved under reversal. -/
theorem reverseAssignment_avoidsOrigin
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (a : Assignment hp C)
    (ha : ∀ q : C.Cell, AvoidsOrigin (localVertexMap hp C a q)) :
    ∀ q : (reverseCells C).Cell,
      AvoidsOrigin
        (localVertexMap hp (reverseCells C) (reverseAssignment C a) q) := by
  intro q
  simpa [localVertexMap_reverseAssignment] using ha q

end ExplicitAffineRelativeCollarAssignmentReverse
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR

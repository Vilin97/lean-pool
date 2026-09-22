/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RouteBAffineFibers
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RouteBFiniteAvoidance

/-!
# Route B, Step 5: bad-set nullity certificates and finite avoidance

Step 4 proves that, after fixing a barycentric witness `w` and all movable
coordinates except one selected scalar orbit, the corresponding scalar fiber is
null whenever one total orbit coefficient is nonzero.

There is an important logical distinction between that statement and nullity of
`mixedFaceBadSet`: the latter existentially quantifies over an uncountable
simplex of witnesses.  Projection of a null subset of a product need not be
null.  Consequently no theorem in this file silently promotes the Step 4
fixed-witness result to full bad-set nullity.

Instead this file does two things:

* packages the exact full-set nullity certificate needed by the perturbation
  selection argument;
* proves that a finite family of certified mixed-face bad sets can be avoided
  in every positive-volume parameter ball.

Full bad-set nullity requires an elimination theorem
showing that each full `mixedFaceBadSet` is null.  It must use the complete
system of deviation equations (or an equivalent nonzero elimination
polynomial), rather than only one fixed-witness scalar equation.
-/

namespace NRR

open FoxNeuwirthOrderComplex
open MeasureTheory

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace ExplicitAffineRelativeCollar
namespace RouteB

open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap
open Parameters
open Polynomials
open RelativeGenericity

variable {p N₀ N₁ M L : Nat}
variable (hp : Nat.Prime p)
variable (C : RelativeAffineCellSystem hp N₀ N₁ M L)

/-- A checked nullity certificate for one complete mixed-face bad set.

This deliberately concerns `mixedFaceBadSet` itself, after existential
quantification over all barycentric witnesses.  A collection of merely
fixed-witness fiber statements is not sufficient to construct this value. -/
structure MixedFaceBadSetNullCertificate
    (base : Assignment hp C) (κ : MixedFaceCase hp C) : Prop where
  volume_eq_zero :
    MeasureTheory.volume (mixedFaceBadSet hp C base κ) = 0

/-- The family of all mixed-face cases is finite. -/
noncomputable def allMixedFaceCases : Finset (MixedFaceCase hp C) :=
  Finset.univ

@[simp] theorem mem_allMixedFaceCases (κ : MixedFaceCase hp C) :
    κ ∈ allMixedFaceCases hp C := by
  simp [allMixedFaceCases]

/-- Full-set nullity certificates imply simultaneous avoidance in any
positive-volume parameter ball. -/
theorem exists_mem_ball_avoiding_all_mixedFaceBadSets
    (base : Assignment hp C)
    (center : MovableParameterSpace hp C)
    (radius : Real)
    (hball : MeasureTheory.volume (Metric.ball center radius) ≠ 0)
    (hnull : ∀ κ : MixedFaceCase hp C,
      MixedFaceBadSetNullCertificate hp C base κ) :
    ∃ x ∈ Metric.ball center radius,
      ∀ κ : MixedFaceCase hp C, x ∉ mixedFaceBadSet hp C base κ := by
  obtain ⟨x, hxball, hxavoid⟩ :=
    RouteBFiniteAvoidance.exists_mem_ball_avoiding_finset_of_null
      MeasureTheory.volume
      (fun κ : MixedFaceCase hp C => mixedFaceBadSet hp C base κ)
      (allMixedFaceCases hp C) center radius hball
      (fun κ _ => (hnull κ).volume_eq_zero)
  refine ⟨x, hxball, ?_⟩
  intro κ
  exact hxavoid κ (mem_allMixedFaceCases hp C κ)

/-- Avoiding every case excludes every mixed positive-ray incidence that has a
positive movable witness. -/
theorem no_incidence_with_movableWitness_of_avoids_all_badSets
    (base : Assignment hp C) (x : MovableParameterSpace hp C)
    (havoid : ∀ κ : MixedFaceCase hp C,
      x ∉ mixedFaceBadSet hp C base κ) :
    ¬ ∃ (q : C.Cell) (w : StandardSimplex p)
        (i j : Fin (p + 1)),
        i ≠ j ∧ w i = 0 ∧ w j = 0 ∧
        (∀ r : Fin (p - 1),
          deviation hp
            (affineValue
              (localVertexMap hp C
                (assignmentOfMovableParameters hp C base x) q) w) r = 0) ∧
        0 < mean p
          (affineValue
            (localVertexMap hp C
              (assignmentOfMovableParameters hp C base x) q) w) ∧
        HasPositiveMovableWitness hp C q w i j := by
  intro h
  have hcase : ∃ κ : MixedFaceCase hp C,
      x ∈ mixedFaceBadSet hp C base κ :=
    (exists_badCase_iff_incidence_with_movableWitness hp C base x).2 h
  rcases hcase with ⟨κ, hκ⟩
  exact havoid κ hκ

/-- Step 4 supplies a null scalar fiber for every fixed witness carrying a
nonzero selected-orbit coefficient.  This theorem records the valid local
input, without making the invalid projection inference. -/
theorem fixedWitness_scalarFiber_null
    (base : Assignment hp C) (x : MovableParameterSpace hp C)
    (κ : MixedFaceCase hp C) (w : StandardSimplex p)
    (r : Fin (p - 1))
    (hr : deviationOrbitCoefficient hp C κ w r ≠ 0) :
    MeasureTheory.volume (mixedFaceScalarFiber hp C base x κ w) = 0 :=
  volume_mixedFaceScalarFiber_eq_zero hp C base x κ w r hr

/-- The elimination property for a mixed-face case.

A proof of this proposition must control the existential barycentric witness.
It can be obtained, for example, by deriving a nonzero polynomial obstruction
in the remaining movable parameters whose zero set contains the complete bad
set. -/
def HasNullElimination
    (base : Assignment hp C) (κ : MixedFaceCase hp C) : Prop :=
  MeasureTheory.volume (mixedFaceBadSet hp C base κ) = 0

/-- The elimination property is exactly the certificate consumed by the finite
avoidance theorem. -/
theorem certificate_of_hasNullElimination
    (base : Assignment hp C) (κ : MixedFaceCase hp C)
    (h : HasNullElimination hp C base κ) :
    MixedFaceBadSetNullCertificate hp C base κ :=
  ⟨h⟩

end RouteB
end ExplicitAffineRelativeCollar
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR

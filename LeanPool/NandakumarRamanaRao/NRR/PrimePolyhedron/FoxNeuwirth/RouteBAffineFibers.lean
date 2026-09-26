/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RouteBMixedFaceIncidence
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
/-!
# Route B, Step 4: one-coordinate affine fibers

A movable parameter is an orbit of scalar sites, so changing one parameter can
alter several local coordinates simultaneously.  The coefficient below is the
total barycentric coefficient of that orbit in one deviation equation.  This is
the correct replacement for the invalid argument that used only the weight of
one retained vertex.

For fixed barycentric data and all other movable parameters, every deviation is
an affine function of the distinguished scalar parameter.  If one total orbit
coefficient is nonzero, the bad fiber is contained in a singleton and therefore
has Lebesgue measure zero.
-/

@[expose] public section

namespace NRR

open FoxNeuwirthOrderComplex
open scoped BigOperators

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

/-- The movable parameter selected by a mixed-face case. -/
noncomputable def MixedFaceCase.selectedParameter
    (κ : MixedFaceCase hp C) : MovableParameter hp C :=
  ⟨localParameter hp C κ.cell κ.retained κ.coordinate, κ.movable⟩

/-- Indicator that a local scalar site belongs to the selected movable orbit. -/
noncomputable def selectedOrbitIndicator
    (κ : MixedFaceCase hp C) (i : Fin (p + 1)) (j : Fin p) : Real :=
  if localParameter hp C κ.cell i j = κ.selectedParameter hp C then 1 else 0

/-- Total coefficient of the selected scalar orbit in one deviation equation.
It includes every local occurrence of the same quotient parameter. -/
noncomputable def deviationOrbitCoefficient
    (κ : MixedFaceCase hp C) (w : StandardSimplex p)
    (r : Fin (p - 1)) : Real :=
  ∑ i : Fin (p + 1), w i *
    (selectedOrbitIndicator hp C κ i
        (ReferenceAffineOrbitCount.coordinateLabel hp r) -
      selectedOrbitIndicator hp C κ i
        (ReferenceAffineOrbitCount.lastLabel hp))

/-- The deviation intercept obtained by setting the distinguished parameter to
zero while retaining every other movable parameter. -/
noncomputable def deviationFiberIntercept
    (base : Assignment hp C) (x : MovableParameterSpace hp C)
    (κ : MixedFaceCase hp C) (w : StandardSimplex p)
    (r : Fin (p - 1)) : Real :=
  deviation hp
    (affineValue
      (localVertexMap hp C
        (assignmentOfMovableParameters hp C base
          (replaceCoordinate hp C x (κ.selectedParameter hp C) 0)) κ.cell) w) r

/-- Fixed-barycentric bad fiber in the distinguished scalar coordinate. -/
def mixedFaceScalarFiber
    (base : Assignment hp C) (x : MovableParameterSpace hp C)
    (κ : MixedFaceCase hp C) (w : StandardSimplex p) : Set Real :=
  {t | (∀ r : Fin (p - 1),
      deviation hp
        (affineValue
          (localVertexMap hp C
            (assignmentOfMovableParameters hp C base
              (replaceCoordinate hp C x (κ.selectedParameter hp C) t)) κ.cell) w) r = 0) ∧
    0 < mean p
      (affineValue
        (localVertexMap hp C
          (assignmentOfMovableParameters hp C base
            (replaceCoordinate hp C x (κ.selectedParameter hp C) t)) κ.cell) w)}

/-- Replacing the selected coordinate evaluates a local scalar site by `t`
exactly when that site belongs to the selected orbit. -/
theorem assignment_replace_selected_apply
    (base : Assignment hp C) (x : MovableParameterSpace hp C)
    (κ : MixedFaceCase hp C) (t : Real)
    (i : Fin (p + 1)) (j : Fin p) :
    assignmentOfMovableParameters hp C base
        (replaceCoordinate hp C x (κ.selectedParameter hp C) t)
        (localParameter hp C κ.cell i j) =
      if localParameter hp C κ.cell i j = κ.selectedParameter hp C then t
      else assignmentOfMovableParameters hp C base
        (replaceCoordinate hp C x (κ.selectedParameter hp C) 0)
        (localParameter hp C κ.cell i j) := by
  by_cases hq : IsFrozenParameter hp C (localParameter hp C κ.cell i j)
  · have hne : localParameter hp C κ.cell i j ≠ κ.selectedParameter hp C := by
      intro h
      exact (MixedFaceCase.selectedParameter hp C κ).property (h ▸ hq)
    simp [assignmentOfMovableParameters,  replaceMovable,
      hq, hne]
  · let q : MovableParameter hp C :=
      ⟨localParameter hp C κ.cell i j, hq⟩
    by_cases h : q = κ.selectedParameter hp C
    · have heq : (⟨localParameter hp C κ.cell i j, hq⟩ : MovableParameter hp C) =
          κ.selectedParameter hp C := h
      have hval : localParameter hp C κ.cell i j = κ.selectedParameter hp C :=
        congrArg Subtype.val heq
      have hmov : ¬ IsFrozenParameter hp C (κ.selectedParameter hp C).1 :=
        (κ.selectedParameter hp C).2
      simp [assignmentOfMovableParameters, replaceMovable, hval, hmov]
    · have hval : localParameter hp C κ.cell i j ≠ κ.selectedParameter hp C := by
        intro heq
        apply h
        exact Subtype.ext heq
      have hsub : (⟨localParameter hp C κ.cell i j, hq⟩ : MovableParameter hp C) ≠
          κ.selectedParameter hp C := h
      simp [assignmentOfMovableParameters, replaceMovable, hq, hval,
        replaceCoordinate, Function.update_of_ne hsub]

/-- Every deviation is affine in the selected scalar orbit, with the total
orbit coefficient defined above. -/
theorem deviation_replace_selected
    (base : Assignment hp C) (x : MovableParameterSpace hp C)
    (κ : MixedFaceCase hp C) (w : StandardSimplex p)
    (r : Fin (p - 1)) (t : Real) :
    deviation hp
        (affineValue
          (localVertexMap hp C
            (assignmentOfMovableParameters hp C base
              (replaceCoordinate hp C x (κ.selectedParameter hp C) t)) κ.cell) w) r =
      deviationFiberIntercept hp C base x κ w r +
        t * deviationOrbitCoefficient hp C κ w r := by
  have hsite : ∀ (i : Fin (p + 1)) (j : Fin p),
      assignmentOfMovableParameters hp C base
          (replaceCoordinate hp C x (MixedFaceCase.selectedParameter hp C κ) t)
          (localParameter hp C κ.cell i j) =
        assignmentOfMovableParameters hp C base
          (replaceCoordinate hp C x (MixedFaceCase.selectedParameter hp C κ) 0)
          (localParameter hp C κ.cell i j) +
        t * selectedOrbitIndicator hp C κ i j := by
    intro i j
    rw [assignment_replace_selected_apply hp C base x κ t]
    by_cases h : localParameter hp C κ.cell i j =
        MixedFaceCase.selectedParameter hp C κ
    · simp [selectedOrbitIndicator, h]
    · simp [selectedOrbitIndicator, h]
  simp only [deviationFiberIntercept, deviation, affineValue,
    localVertexMap_value_apply_eq_assignment_localParameter]
  simp_rw [hsite]
  simp only [deviationOrbitCoefficient, mul_add]
  repeat' rw [Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hcomm (j : Fin p) :
      (∑ i : Fin (p + 1), w i * (t * selectedOrbitIndicator hp C κ i j)) =
        ∑ i : Fin (p + 1), t * (w i * selectedOrbitIndicator hp C κ i j) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hcomm (ReferenceAffineOrbitCount.coordinateLabel hp r),
    hcomm (ReferenceAffineOrbitCount.lastLabel hp)]
  abel

/-- A nonzero deviation coefficient forces every bad scalar to equal one
explicit value. -/
theorem mixedFaceScalarFiber_subset_singleton
    (base : Assignment hp C) (x : MovableParameterSpace hp C)
    (κ : MixedFaceCase hp C) (w : StandardSimplex p)
    (r : Fin (p - 1))
    (hr : deviationOrbitCoefficient hp C κ w r ≠ 0) :
    mixedFaceScalarFiber hp C base x κ w ⊆
      {-deviationFiberIntercept hp C base x κ w r /
        deviationOrbitCoefficient hp C κ w r} := by
  intro t ht
  rcases ht with ⟨hdev, hmean⟩
  have hzero := hdev r
  rw [deviation_replace_selected hp C base x κ w r t] at hzero
  have htval :
      t = -deviationFiberIntercept hp C base x κ w r /
        deviationOrbitCoefficient hp C κ w r := by
    apply (eq_div_iff hr).2
    linarith
  simpa [Set.mem_singleton_iff] using htval

/-- Under one nonzero total orbit coefficient, the fixed-barycentric bad fiber
has one-dimensional Lebesgue measure zero. -/
theorem volume_mixedFaceScalarFiber_eq_zero
    (base : Assignment hp C) (x : MovableParameterSpace hp C)
    (κ : MixedFaceCase hp C) (w : StandardSimplex p)
    (r : Fin (p - 1))
    (hr : deviationOrbitCoefficient hp C κ w r ≠ 0) :
    MeasureTheory.volume (mixedFaceScalarFiber hp C base x κ w) = 0 := by
  apply MeasureTheory.measure_mono_null
    (mixedFaceScalarFiber_subset_singleton hp C base x κ w r hr)
  simp

end RouteB
end ExplicitAffineRelativeCollar
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR

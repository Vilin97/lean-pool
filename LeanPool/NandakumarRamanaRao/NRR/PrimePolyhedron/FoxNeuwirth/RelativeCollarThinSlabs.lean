/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeCollarMiddlePrismEndpoints
/-!
# Thin-time stacks of unrefined Fox--Neuwirth staircase prisms

The fully barycentrically refined middle prism changes the horizontal spatial triangulation from
level `N` to level `N + L`.  For a boundary-relative comparison this is undesirable: the supplied
stable endpoint approximation must remain fixed on its exact level.

This module refines only the interval direction.  A thin stack with `m > 0` consists of `m` copies
of the unrefined (`L = 0`) staircase prism.  Copy `r : Fin m` is embedded in the time slab
`[r/m, (r+1)/m]`.  Spatial coordinates and all prime-orbit data are unchanged.

The construction below supplies the genuine affine-cell system.  The subsequent boundary module
collects quotient-facet incidences: side facets cancel inside each slab, adjacent horizontal facets
cancel between consecutive slabs, and only the first lower and final upper boundary remain.
-/

namespace NRR

open scoped BigOperators
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace RelativeCollarThinSlabs

open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open EquivariantPrismVertexParameters
open ExplicitAffineRelativeCollar
open RelativeCollarMiddlePrism

variable {p : Nat}

/-- Affine rescaling of the unit interval onto slab `r` of a positive `m`-slab partition. -/
noncomputable def slabTime
    (m : Nat) (hm : 0 < m) (r : Fin m) (t : Set.Icc (0 : Real) 1) :
    Set.Icc (0 : Real) 1 := by
  let y : Real := ((r.1 : Real) + t.1) / (m : Real)
  refine ⟨y, ?_, ?_⟩
  · dsimp [y]
    have hmR : (0 : Real) < (m : Real) := by exact_mod_cast hm
    apply div_nonneg (add_nonneg (by positivity) t.2.1) (le_of_lt hmR)
  · dsimp [y]
    have hmR : (0 : Real) < (m : Real) := by exact_mod_cast hm
    have hr : (r.1 : Real) + 1 ≤ (m : Real) := by
      exact_mod_cast (Nat.succ_le_iff.mpr r.2)
    have ht := t.2.2
    apply (div_le_one hmR).2
    linarith

@[simp] theorem slabTime_val
    (m : Nat) (hm : 0 < m) (r : Fin m) (t : Set.Icc (0 : Real) 1) :
    (slabTime m hm r t).1 = ((r.1 : Real) + t.1) / (m : Real) :=
  rfl

/-- Embed one cylinder point into a specified thin time slab. -/
noncomputable def slabPoint
    (m : Nat) (hm : 0 < m) (r : Fin m) (z : CylinderPoint p) : CylinderPoint p where
  spatial := z.spatial
  time := slabTime m hm r z.time

@[simp] theorem slabPoint_spatial
    (m : Nat) (hm : 0 < m) (r : Fin m) (z : CylinderPoint p) :
    (slabPoint m hm r z).spatial = z.spatial :=
  rfl

@[simp] theorem slabPoint_time
    (m : Nat) (hm : 0 < m) (r : Fin m) (z : CylinderPoint p) :
    (slabPoint m hm r z).time.1 = ((r.1 : Real) + z.time.1) / (m : Real) :=
  rfl

/-- Time rescaling commutes with prime symmetry. -/
@[simp] theorem slabPoint_smul
    (hp : Nat.Prime p) (m : Nat) (hm : 0 < m) (r : Fin m)
    (g : PrimeSymmetry hp) (z : CylinderPoint p) :
    slabPoint m hm r (g • z) = g • slabPoint m hm r z :=
  rfl

/-- Rescaling into one fixed positive slab is injective. -/
theorem slabPoint_injective
    (m : Nat) (hm : 0 < m) (r : Fin m) :
    Function.Injective (slabPoint (p := p) m hm r) := by
  intro x y hxy
  cases x with
  | mk xs xt =>
      cases y with
      | mk ys yt =>
          simp only [slabPoint] at hxy
          have hspatial : xs = ys := congrArg CylinderPoint.spatial hxy
          have htimeVal : xt.1 = yt.1 := by
            have h := congrArg (fun z : CylinderPoint p => z.time.1) hxy
            simp only [slabPoint_time] at h
            have hmR : (0 : Real) < (m : Real) := by exact_mod_cast hm
            have hm0 : (m : Real) ≠ 0 := ne_of_gt hmR
            change ((r.1 : Real) + xt.1) / (m : Real) =
              ((r.1 : Real) + yt.1) / (m : Real) at h
            have hadd := (div_left_inj' hm0).mp h
            linarith
          have htime : xt = yt := Subtype.ext htimeVal
          subst hspatial
          subst htime
          rfl

/-- One top-cell representative in a thin stack. -/
abbrev Cell (hp : Nat.Prime p) (N m : Nat) :=
  Fin m × (RelativeCollarMiddlePrism.cellSystem hp N 0).Cell

noncomputable instance cellFintype (hp : Nat.Prime p) (N m : Nat) :
    Fintype (Cell hp N m) := inferInstance

noncomputable instance cellDecidableEq (hp : Nat.Prime p) (N m : Nat) :
    DecidableEq (Cell hp N m) := inferInstance

/-- A canonical cell witnessing nonemptiness of a positive thin stack. -/
noncomputable def defaultCell
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m) : Cell hp N m :=
  (⟨0, hm⟩, RelativeCollarMiddlePrism.defaultPrismCell hp N 0)

/-- Geometric vertex of a thin-stack cell. -/
noncomputable def vertex
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (q : Cell hp N m) (i : Fin (p + 1)) : CylinderPoint p :=
  slabPoint m hm q.1
    ((RelativeCollarMiddlePrism.cellSystem hp N 0).vertex q.2 i)

/-- Affine chart of a thin-stack cell. -/
noncomputable def chart
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (q : Cell hp N m) (w : Delta p) : CylinderPoint p :=
  slabPoint m hm q.1
    ((RelativeCollarMiddlePrism.cellSystem hp N 0).chart q.2 w)

@[simp] theorem chart_vertex
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (q : Cell hp N m) (i : Fin (p + 1)) :
    chart hp N m hm q (stdSimplex.vertex (S := Real) i) =
      vertex hp N m hm q i := by
  simp [chart, vertex,
    (RelativeCollarMiddlePrism.cellSystem hp N 0).chart_vertex]

/-- The thin stack is a genuine affine cell system with unchanged spatial endpoint level `N`. -/
noncomputable def cellSystem
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m) :
    RelativeAffineCellSystem hp N N N m where
  lower_le_common := le_rfl
  upper_le_common := le_rfl
  Cell := Cell hp N m
  cell_nonempty := ⟨defaultCell hp N m hm⟩
  instCellFintype := inferInstance
  instCellDecidableEq := inferInstance
  coefficient := fun q =>
    (RelativeCollarMiddlePrism.cellSystem hp N 0).coefficient q.2
  vertex := vertex hp N m hm
  chart := chart hp N m hm
  chart_vertex := chart_vertex hp N m hm
  chart_spatial_affine := by
    intro q w c
    simpa [chart, vertex] using
      (RelativeCollarMiddlePrism.cellSystem hp N 0).chart_spatial_affine q.2 w c
  chart_time_affine := by
    intro q w
    have hbase :=
      (RelativeCollarMiddlePrism.cellSystem hp N 0).chart_time_affine q.2 w
    simp only [chart, vertex, slabPoint_time]
    rw [hbase]
    have hsum : (∑ i : Fin (p + 1), w i) = (1 : Real) :=
      stdSimplex.sum_eq_one w
    have hmR : (0 : Real) < (m : Real) := by exact_mod_cast hm
    have hm0 : (m : Real) ≠ 0 := ne_of_gt hmR
    rw [div_eq_iff hm0]
    rw [Finset.sum_mul]
    calc
      _ = (∑ i : Fin (p + 1), w i) * (q.1.1 : Real) +
          ∑ i : Fin (p + 1), w i *
            ((RelativeCollarMiddlePrism.cellSystem hp N 0).vertex q.2 i).time.1 := by
        rw [hsum]
        ring
      _ = ∑ i : Fin (p + 1),
          (w i * (q.1.1 : Real) + w i *
            ((RelativeCollarMiddlePrism.cellSystem hp N 0).vertex q.2 i).time.1) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        field_simp [hm0]
  chart_injective := by
    intro q x y hxy
    apply (RelativeCollarMiddlePrism.cellSystem hp N 0).chart_injective q.2
    apply slabPoint_injective m hm q.1
    exact hxy
  vertex_injective := by
    intro q i j hij
    apply (RelativeCollarMiddlePrism.cellSystem hp N 0).vertex_injective q.2
    apply slabPoint_injective m hm q.1
    exact hij
  vertex_orbit_injective := by
    intro q g i j hij
    have hrescaled :
        slabPoint m hm q.1
            (g • (RelativeCollarMiddlePrism.cellSystem hp N 0).vertex q.2 i) =
          slabPoint m hm q.1
            ((RelativeCollarMiddlePrism.cellSystem hp N 0).vertex q.2 j) := by
      simpa [vertex] using hij
    have hbase := slabPoint_injective m hm q.1 hrescaled
    exact (RelativeCollarMiddlePrism.cellSystem hp N 0).vertex_orbit_injective
      q.2 g i j hbase

end RelativeCollarThinSlabs
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR

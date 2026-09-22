/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricSubdivisionHomotopyOperator
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricSubdivisionDiameter
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.AffineSubdivisionDeterminant
/-!
# Recursive one-step subdivision cylinders

This module gives the explicit finite cell and vertex formulas for the relative triangulation of
`Delta d x I` whose lower boundary is the coarse simplex and whose upper boundary is its first
barycentric subdivision.

The construction is recursive. Triangulate the boundary of the prism by one coarse lower simplex,
all barycentric top simplices, and recursively triangulated side cylinders. Every boundary simplex
is then coned to the central point `(barycenter, 1 / 2)`.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace RelativeSubdivisionCylinderCombinatorics

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision

/-- Top cells of the recursive cone triangulation of `Delta d x I`. -/
def Cell : Nat → Type
  | 0 => Unit ⊕ Equiv.Perm (Fin 1)
  | d + 1 =>
      Unit ⊕ (Equiv.Perm (Fin (d + 2)) ⊕ (Fin (d + 2) × Cell d))

noncomputable instance cellDecidableEq (d : Nat) : DecidableEq (Cell d) :=
  Classical.decEq _

noncomputable instance cellFintype : (d : Nat) → Fintype (Cell d)
  | 0 => by
      change Fintype (Unit ⊕ Equiv.Perm (Fin 1))
      infer_instance
  | d + 1 => by
      letI : Fintype (Cell d) := cellFintype d
      change Fintype (Unit ⊕ (Equiv.Perm (Fin (d + 2)) ⊕ (Fin (d + 2) × Cell d)))
      infer_instance

/-- The cell coned from the coarse lower simplex. -/
def lowerCell : (d : Nat) → Cell d
  | 0 => Sum.inl ()
  | _ + 1 => Sum.inl ()

/-- The cell coned from one top barycentric simplex. -/
def upperCell : (d : Nat) → Equiv.Perm (Fin (d + 1)) → Cell d
  | 0, pi => Sum.inr pi
  | _ + 1, pi => Sum.inr (Sum.inl pi)

/-- A cell coned from a recursively triangulated side face. -/
def sideCell (d : Nat) (k : Fin (d + 2)) (q : Cell d) : Cell (d + 1) :=
  Sum.inr (Sum.inr (k, q))

/-- The central cone point. -/
noncomputable def apex (d : Nat) : Delta d × Set.Icc (0 : Real) 1 :=
  (deltaBarycenter d, ⟨(1 : Real) / 2, by constructor <;> norm_num⟩)

/-- Coarse lower-boundary vertex. -/
noncomputable def lowerBoundaryVertex
    (d : Nat) (i : Fin (d + 1)) : Delta d × Set.Icc (0 : Real) 1 :=
  (stdSimplex.vertex (S := Real) i, ⟨0, by norm_num⟩)

/-- Barycentric upper-boundary vertex. -/
noncomputable def upperBoundaryVertex
    (d : Nat) (pi : Equiv.Perm (Fin (d + 1))) (i : Fin (d + 1)) :
    Delta d × Set.Icc (0 : Real) 1 :=
  (prefixBarycenter d pi i, ⟨1, by norm_num⟩)

/-- Embed a point of a lower-dimensional cylinder into the side opposite `k`. -/
noncomputable def sidePoint
    (d : Nat) (k : Fin (d + 2))
    (z : Delta d × Set.Icc (0 : Real) 1) :
    Delta (d + 1) × Set.Icc (0 : Real) 1 :=
  (stdSimplex.map (S := Real) k.succAbove z.1, z.2)

@[simp] theorem sidePoint_spatial_succAbove
    (d : Nat) (k : Fin (d + 2))
    (z : Delta d × Set.Icc (0 : Real) 1) (i : Fin (d + 1)) :
    (sidePoint d k z).1 (k.succAbove i) = z.1 i := by
  unfold sidePoint
  change (stdSimplex.map (S := Real) k.succAbove z.1 : Fin (d + 2) → Real) (k.succAbove i) = z.1 i
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  have h_filter : (Finset.univ.filter (fun j => k.succAbove j = k.succAbove i)) = {i} := by
    ext j
    simp [Fin.succAbove_right_injective.eq_iff]
  rw [h_filter, Finset.sum_singleton]

@[simp] theorem sidePoint_spatial_deleted
    (d : Nat) (k : Fin (d + 2))
    (z : Delta d × Set.Icc (0 : Real) 1) :
    (sidePoint d k z).1 k = 0 := by
  change (stdSimplex.map (S := Real) k.succAbove z.1 : Fin (d + 2) → Real) k = 0
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro i hi
  exact (Fin.succAbove_ne k i (Finset.mem_filter.mp hi).2).elim

/-- Ordered vertices of a recursive cylinder cell. -/
noncomputable def vertex :
    (d : Nat) → Cell d → Fin (d + 2) → Delta d × Set.Icc (0 : Real) 1
  | 0, q, i =>
      Fin.cases (apex 0)
        (fun j =>
          match q with
          | Sum.inl _ => lowerBoundaryVertex 0 j
          | Sum.inr pi => upperBoundaryVertex 0 pi j)
        i
  | d + 1, q, i =>
      Fin.cases (apex (d + 1))
        (fun j =>
          match q with
          | Sum.inl _ => lowerBoundaryVertex (d + 1) j
          | Sum.inr (Sum.inl pi) => upperBoundaryVertex (d + 1) pi j
          | Sum.inr (Sum.inr (k, r)) => sidePoint d k (vertex d r j))
        i

@[simp] theorem vertex_zero (d : Nat) (q : Cell d) :
    vertex d q 0 = apex d := by
  cases d <;> rfl

@[simp] theorem vertex_succ_lower
    (d : Nat) (j : Fin (d + 1)) :
    vertex d (lowerCell d) j.succ = lowerBoundaryVertex d j := by
  cases d <;> rfl

@[simp] theorem vertex_succ_upper
    (d : Nat) (pi : Equiv.Perm (Fin (d + 1))) (j : Fin (d + 1)) :
    vertex d (upperCell d pi) j.succ = upperBoundaryVertex d pi j := by
  cases d <;> rfl

@[simp] theorem vertex_succ_side
    (d : Nat) (k : Fin (d + 2)) (q : Cell d) (j : Fin (d + 2)) :
    vertex (d + 1) (sideCell d k q) j.succ = sidePoint d k (vertex d q j) :=
  rfl

/-- Spatial barycentric interpolation of a recursive cylinder cell. -/
noncomputable def spatialPoint
    (d : Nat) (q : Cell d) (w : Delta (d + 1)) : Delta d :=
  ⟨fun c => ∑ i : Fin (d + 2), w i * (vertex d q i).1 c, by
    constructor
    · intro c
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (stdSimplex.zero_le w i) (stdSimplex.zero_le (vertex d q i).1 c)
    · rw [Finset.sum_comm]
      calc
        ∑ i : Fin (d + 2), ∑ c : Fin (d + 1),
            w i * (vertex d q i).1 c =
            ∑ i : Fin (d + 2), w i *
              (∑ c : Fin (d + 1), (vertex d q i).1 c) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.mul_sum]
        _ = ∑ i : Fin (d + 2), w i := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [stdSimplex.sum_eq_one, mul_one]
        _ = 1 := stdSimplex.sum_eq_one w⟩

/-- Time barycentric interpolation of a recursive cylinder cell. -/
noncomputable def timePoint
    (d : Nat) (q : Cell d) (w : Delta (d + 1)) : Set.Icc (0 : Real) 1 :=
  ⟨∑ i : Fin (d + 2), w i * (vertex d q i).2.1, by
    constructor
    · exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (stdSimplex.zero_le w i) (vertex d q i).2.2.1
    · calc
        ∑ i : Fin (d + 2), w i * (vertex d q i).2.1
            ≤ ∑ i : Fin (d + 2), w i * 1 := by
              apply Finset.sum_le_sum
              intro i hi
              exact mul_le_mul_of_nonneg_left (vertex d q i).2.2.2
                (stdSimplex.zero_le w i)
        _ = 1 := by simp [stdSimplex.sum_eq_one w]⟩

/-- Affine chart of one recursive one-step cylinder cell. -/
noncomputable def chart
    (d : Nat) (q : Cell d) (w : Delta (d + 1)) :
    Delta d × Set.Icc (0 : Real) 1 :=
  (spatialPoint d q w, timePoint d q w)

@[simp] theorem chart_vertex
    (d : Nat) (q : Cell d) (i : Fin (d + 2)) :
    chart d q (stdSimplex.vertex (S := Real) i) = vertex d q i := by
  unfold chart;
  unfold spatialPoint timePoint;
  simp +decide [ Pi.single_apply ];
  rfl

/-- Every spatial coordinate is the barycentric interpolation of declared vertices. -/
theorem chart_spatial_affine
    (d : Nat) (q : Cell d) (w : Delta (d + 1)) (c : Fin (d + 1)) :
    (chart d q w).1 c =
      ∑ i : Fin (d + 2), w i * (vertex d q i).1 c := rfl

/-- The time coordinate is the barycentric interpolation of declared vertex times. -/
theorem chart_time_affine
    (d : Nat) (q : Cell d) (w : Delta (d + 1)) :
    (chart d q w).2.1 =
      ∑ i : Fin (d + 2), w i * (vertex d q i).2.1 := rfl

@[simp] theorem timePoint_lower
    (d : Nat) (w : Delta (d + 1)) :
    (timePoint d (lowerCell d) w).1 = w 0 / 2 := by
  change (∑ i : Fin (d + 2), w i * (vertex d (lowerCell d) i).2.1) = w 0 / 2
  rw [Fin.sum_univ_succ]
  simp [vertex_zero, vertex_succ_lower, apex, lowerBoundaryVertex]
  ring

@[simp] theorem timePoint_upper
    (d : Nat) (pi : Equiv.Perm (Fin (d + 1))) (w : Delta (d + 1)) :
    (timePoint d (upperCell d pi) w).1 = 1 - w 0 / 2 := by
  change (∑ i : Fin (d + 2), w i * (vertex d (upperCell d pi) i).2.1) =
    1 - w 0 / 2
  rw [Fin.sum_univ_succ]
  simp [vertex_zero, vertex_succ_upper, apex, upperBoundaryVertex]
  have hsum := stdSimplex.sum_eq_one w
  rw [Fin.sum_univ_succ] at hsum
  linarith

@[simp] theorem timePoint_side
    (d : Nat) (k : Fin (d + 2)) (q : Cell d) (w : Delta (d + 2)) :
    (timePoint (d + 1) (sideCell d k q) w).1 =
      w 0 / 2 + ∑ i : Fin (d + 2), w i.succ * (vertex d q i).2.1 := by
  change (∑ i : Fin (d + 3), w i *
      (vertex (d + 1) (sideCell d k q) i).2.1) = _
  rw [Fin.sum_univ_succ]
  simp [vertex_zero, vertex_succ_side, apex, sidePoint]
  ring

@[simp] theorem spatialPoint_lower_coord
    (d : Nat) (w : Delta (d + 1)) (c : Fin (d + 1)) :
    spatialPoint d (lowerCell d) w c =
      w 0 * deltaBarycenter d c + w c.succ := by
  change (∑ i : Fin (d + 2), w i * (vertex d (lowerCell d) i).1 c) = _
  rw [Fin.sum_univ_succ]
  simp [vertex_zero, vertex_succ_lower, apex, lowerBoundaryVertex,
    stdSimplex.vertex, Pi.single_apply]

@[simp] theorem spatialPoint_upper_coord
    (d : Nat) (pi : Equiv.Perm (Fin (d + 1)))
    (w : Delta (d + 1)) (c : Fin (d + 1)) :
    spatialPoint d (upperCell d pi) w c =
      w 0 * deltaBarycenter d c +
        ∑ i : Fin (d + 1), w i.succ * prefixBarycenter d pi i c := by
  change (∑ i : Fin (d + 2), w i * (vertex d (upperCell d pi) i).1 c) = _
  rw [Fin.sum_univ_succ]
  simp [vertex_zero, vertex_succ_upper, apex, upperBoundaryVertex]

@[simp] theorem spatialPoint_side_missing_coord
    (d : Nat) (k : Fin (d + 2)) (q : Cell d)
    (w : Delta (d + 2)) :
    spatialPoint (d + 1) (sideCell d k q) w k =
      w 0 * deltaBarycenter (d + 1) k := by
  change (∑ i : Fin (d + 3), w i * (vertex (d + 1) (sideCell d k q) i).1 k) = _
  rw [Fin.sum_univ_succ]
  simp [vertex_zero, vertex_succ_side, apex, sidePoint_spatial_deleted]

/-- The lower cone simplex is nondegenerate. -/
theorem chart_lower_injective (d : Nat) :
    Function.Injective (chart d (lowerCell d)) := by
  intro x y hxy
  have ht := congrArg (fun z : Delta d × Set.Icc (0 : Real) 1 => z.2.1) hxy
  have h0 : x 0 = y 0 := by
    simp only [chart, timePoint_lower] at ht
    linarith
  apply Subtype.ext
  funext i
  refine Fin.cases h0 (fun c => ?_) i
  have hc := congrArg (fun z : Delta d × Set.Icc (0 : Real) 1 => z.1 c) hxy
  simp only [chart, spatialPoint_lower_coord] at hc
  rw [h0] at hc
  exact add_left_cancel hc

/-
Every upper cone simplex is nondegenerate.
-/
theorem chart_upper_injective
    (d : Nat) (pi : Equiv.Perm (Fin (d + 1))) :
    Function.Injective (chart d (upperCell d pi)) := by
  intro x y hxy
  have ht := congrArg (fun z : Delta d × Set.Icc (0 : Real) 1 => z.2.1) hxy
  have h0 : x 0 = y 0 := by
    simp only [chart, timePoint_upper] at ht
    linarith
  apply Subtype.ext
  have h_tail : (AffineSubdivisionDeterminant.stepVertexMatrix d pi).mulVec (x ∘ Fin.succ) =
                (AffineSubdivisionDeterminant.stepVertexMatrix d pi).mulVec (y ∘ Fin.succ) := by
    ext c
    have hc := congrArg (fun z : Delta d × Set.Icc (0 : Real) 1 => z.1 c) hxy
    dsimp [chart] at hc
    rw [spatialPoint_upper_coord, spatialPoint_upper_coord] at hc
    rw [h0] at hc
    have h_sub := add_left_cancel hc
    dsimp [AffineSubdivisionDeterminant.stepVertexMatrix, Matrix.mulVec, dotProduct]
    change ∑ i, prefixBarycenter d pi i c * x i.succ = ∑ i, prefixBarycenter d pi i c * y i.succ
    simp_rw [mul_comm (prefixBarycenter _ _ _ _)]
    exact h_sub
  have h_tail_eq : x ∘ Fin.succ = y ∘ Fin.succ := by
    have hdet := AffineSubdivisionDeterminant.det_stepVertexMatrix_ne_zero d pi
    have h_inv : Invertible (AffineSubdivisionDeterminant.stepVertexMatrix d pi) :=
      Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hdet)
    exact Matrix.mulVec_injective_of_invertible (AffineSubdivisionDeterminant.stepVertexMatrix d pi) h_tail
  exact funext fun i => Fin.cases h0 (fun i => congr_fun h_tail_eq i) i

/-- Pairwise distinct vertices follow from injectivity of the affine chart. -/
theorem vertex_injective_of_chart_injective
    (d : Nat) (q : Cell d) (hchart : Function.Injective (chart d q)) :
    Function.Injective (vertex d q) := by
  intro i j hij
  have hstd :
      (stdSimplex.vertex (S := Real) i : Delta (d + 1)) =
        stdSimplex.vertex (S := Real) j := by
    apply hchart
    simpa using hij
  by_contra hne
  have hi := congrArg (fun w : Delta (d + 1) => w i) hstd
  simpa [stdSimplex.vertex, hne] using hi

/-- A facet is entirely at time zero exactly for the coarse lower base facet. -/
theorem lowerFacet_classification
    (d : Nat) (q : Cell d) (j : Fin (d + 2))
    (h : ∀ i : Fin (d + 1), (vertex d q (j.succAbove i)).2.1 = 0) :
    q = lowerCell d ∧ j = 0 := by
  have hj : j = 0 := by
    by_contra hjne
    have hjpos : (0 : Fin (d + 2)) < j := Fin.pos_of_ne_zero hjne
    have hlt : (0 : Fin (d + 1)).castSucc < j := by simpa using hjpos
    have hs : j.succAbove (0 : Fin (d + 1)) = 0 := by
      simpa using Fin.succAbove_of_castSucc_lt j (0 : Fin (d + 1)) hlt
    have ha := h 0
    rw [hs, vertex_zero] at ha
    norm_num [apex] at ha
  subst j
  constructor
  · cases d with
    | zero =>
        rcases q with q | pi
        · rfl
        · exfalso
          have hu := h 0
          change (upperBoundaryVertex 0 pi 0).2.1 = 0 at hu
          norm_num [upperBoundaryVertex] at hu
    | succ d =>
        rcases q with q | q
        · rfl
        · rcases q with pi | side
          · exfalso
            have hu := h 0
            change (upperBoundaryVertex (d + 1) pi 0).2.1 = 0 at hu
            norm_num [upperBoundaryVertex] at hu
          · rcases side with ⟨k, r⟩
            exfalso
            have hs := h 0
            change (sidePoint d k (vertex d r 0)).2.1 = 0 at hs
            simp [sidePoint, vertex_zero, apex] at hs
  · rfl

/-- A facet is entirely at time one exactly for an upper barycentric base facet. -/
theorem upperFacet_classification
    (d : Nat) (q : Cell d) (j : Fin (d + 2))
    (h : ∀ i : Fin (d + 1), (vertex d q (j.succAbove i)).2.1 = 1) :
    j = 0 ∧ ∃ pi : Equiv.Perm (Fin (d + 1)), q = upperCell d pi := by
  have hj : j = 0 := by
    by_contra hjne
    have hjpos : (0 : Fin (d + 2)) < j := Fin.pos_of_ne_zero hjne
    have hlt : (0 : Fin (d + 1)).castSucc < j := by simpa using hjpos
    have hs : j.succAbove (0 : Fin (d + 1)) = 0 := by
      simpa using Fin.succAbove_of_castSucc_lt j (0 : Fin (d + 1)) hlt
    have ha := h 0
    rw [hs, vertex_zero] at ha
    norm_num [apex] at ha
  subst j
  refine ⟨rfl, ?_⟩
  cases d with
  | zero =>
      rcases q with q | pi
      · exfalso
        have hl := h 0
        change (lowerBoundaryVertex 0 0).2.1 = 1 at hl
        norm_num [lowerBoundaryVertex] at hl
      · exact ⟨pi, rfl⟩
  | succ d =>
      rcases q with q | q
      · exfalso
        have hl := h 0
        change (lowerBoundaryVertex (d + 1) 0).2.1 = 1 at hl
        norm_num [lowerBoundaryVertex] at hl
      · rcases q with pi | side
        · exact ⟨pi, rfl⟩
        · rcases side with ⟨k, r⟩
          exfalso
          have hs := h 0
          change (sidePoint d k (vertex d r 0)).2.1 = 1 at hs
          simp [sidePoint, vertex_zero, apex] at hs

/-- The coordinates after the leading cone coordinate sum to `1 - w 0`. -/
theorem sum_succ_eq_one_sub
    (n : Nat) (w : Delta (n + 1)) :
    (∑ i : Fin (n + 1), w i.succ) = 1 - w 0 := by
  have hsum := stdSimplex.sum_eq_one w
  rw [Fin.sum_univ_succ] at hsum
  linarith

/-- At the cone apex all tail coordinates vanish. -/
theorem succ_eq_zero_of_zero_eq_one
    (n : Nat) (w : Delta (n + 1)) (h0 : w 0 = 1)
    (i : Fin (n + 1)) :
    w i.succ = 0 := by
  have htail : (∑ j : Fin (n + 1), w j.succ) = 0 := by
    rw [sum_succ_eq_one_sub n w, h0]
    ring
  have hle : w i.succ ≤ ∑ j : Fin (n + 1), w j.succ :=
    Finset.single_le_sum
      (fun j _ => stdSimplex.zero_le w j.succ) (Finset.mem_univ i)
  rw [htail] at hle
  exact le_antisymm hle (stdSimplex.zero_le w i.succ)

/-- Normalize the tail barycentric coordinates away from the cone apex. -/
noncomputable def coneTail
    {n : Nat} (w : Delta (n + 1)) : Delta n :=
  if h : w 0 = 1 then deltaBarycenter n else
    ⟨fun i => w i.succ / (1 - w 0), by
      constructor
      · intro i
        exact div_nonneg (stdSimplex.zero_le w i.succ)
          (sub_nonneg.mpr (stdSimplex.le_one w 0))
      · calc
          ∑ i : Fin (n + 1), w i.succ / (1 - w 0) =
              (∑ i : Fin (n + 1), w i.succ) / (1 - w 0) := by
                rw [Finset.sum_div]
          _ = (1 - w 0) / (1 - w 0) := by
                rw [sum_succ_eq_one_sub n w]
          _ = 1 := div_self (sub_ne_zero.mpr (Ne.symm h))⟩

@[simp] theorem coneTail_apply
    {n : Nat} (w : Delta (n + 1)) (hw : w 0 ≠ 1) (i : Fin (n + 1)) :
    coneTail w i = w i.succ / (1 - w 0) := by
  unfold coneTail; aesop;



@[simp] theorem sidePoint_time
    (d : Nat) (k : Fin (d + 2))
    (z : Delta d × Set.Icc (0 : Real) 1) :
    (sidePoint d k z).2 = z.2 := rfl

/-
Away from the apex, a side spatial chart is the affine cone on its base chart.
-/
theorem spatialPoint_side_succAbove_decompose
    (d : Nat) (k : Fin (d + 2)) (q : Cell d)
    (w : Delta (d + 2)) (hw : w 0 ≠ 1) (c : Fin (d + 1)) :
    spatialPoint (d + 1) (sideCell d k q) w (k.succAbove c) =
      w 0 * deltaBarycenter (d + 1) (k.succAbove c) +
        (1 - w 0) * spatialPoint d q (coneTail w) c := by
  change (∑ j : Fin (d + 3), w j * (vertex (d + 1) (sideCell d k q) j).1 (k.succAbove c)) = _
  rw [Fin.sum_univ_succ]
  simp only [vertex_zero, vertex_succ_side, apex, sidePoint_spatial_succAbove]
  congr 1
  change (∑ j : Fin (d + 2), w j.succ * (vertex d q j).1 c) = (1 - w 0) * ∑ i : Fin (d + 2), (coneTail w) i * (vertex d q i).1 c
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h_cone : (coneTail w) i = w i.succ / (1 - w 0) := coneTail_apply w hw i
  rw [h_cone, div_mul_eq_mul_div, mul_div_cancel₀ _ (sub_ne_zero.mpr (Ne.symm hw))]

/-
Away from the apex, a side time chart is the affine cone on its base chart.
-/
theorem timePoint_side_decompose
    (d : Nat) (k : Fin (d + 2)) (q : Cell d)
    (w : Delta (d + 2)) (hw : w 0 ≠ 1) :
    (timePoint (d + 1) (sideCell d k q) w).1 =
      w 0 / 2 + (1 - w 0) * (timePoint d q (coneTail w)).1 := by
  rw [ timePoint_side, timePoint ];
  simp +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_left_comm,  hw, coneTail_apply, div_eq_inv_mul ];
  grind

/-
A recursive side cone is nondegenerate whenever its base chart is.
-/
theorem chart_side_injective
    (d : Nat) (k : Fin (d + 2)) (q : Cell d)
    (hq : Function.Injective (chart d q)) :
    Function.Injective (chart (d + 1) (sideCell d k q)) := by
  intro x y hxy
  have h0 : x 0 = y 0 := by
    have hc := congrArg (fun z : Delta (d + 1) × Set.Icc (0 : Real) 1 => z.1 k) hxy
    dsimp [chart] at hc
    rw [spatialPoint_side_missing_coord, spatialPoint_side_missing_coord] at hc
    dsimp [deltaBarycenter, stdSimplex.barycenter] at hc
    have h_pos : (Fintype.card (Fin (d + 2)) : Real)⁻¹ ≠ 0 := ne_of_gt (inv_pos.mpr (by positivity))
    exact mul_right_cancel₀ h_pos hc
  by_cases hx : x 0 = 1
  · have hy : y 0 = 1 := by rw [← h0, hx]
    apply Subtype.ext
    ext i
    refine Fin.cases h0 (fun j => ?_) i
    have hx_zero := succ_eq_zero_of_zero_eq_one (d + 1) x hx j
    have hy_zero := succ_eq_zero_of_zero_eq_one (d + 1) y hy j
    change x j.succ = y j.succ
    rw [hx_zero, hy_zero]
  · have hy : y 0 ≠ 1 := by rw [← h0]; exact hx
    have h_tail : chart d q (coneTail x) = chart d q (coneTail y) := by
      apply Prod.ext
      · ext c
        have hc := congrArg (fun z : Delta (d + 1) × Set.Icc (0 : Real) 1 => z.1 (k.succAbove c)) hxy
        dsimp [chart] at hc
        rw [spatialPoint_side_succAbove_decompose _ _ _ _ hx,
            spatialPoint_side_succAbove_decompose _ _ _ _ hy] at hc
        rw [h0] at hc
        have h_sub := add_left_cancel hc
        have h1 : 1 - y 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
        exact mul_left_cancel₀ h1 h_sub
      · apply Subtype.ext
        have ht := congrArg (fun z : Delta (d + 1) × Set.Icc (0 : Real) 1 => z.2.1) hxy
        dsimp [chart] at ht
        rw [timePoint_side_decompose _ _ _ _ hx,
            timePoint_side_decompose _ _ _ _ hy] at ht
        rw [h0] at ht
        have h_sub := add_left_cancel ht
        have h1 : 1 - y 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
        exact mul_left_cancel₀ h1 h_sub
    have h_eq := hq h_tail
    have h_tail_val := congr_arg Subtype.val h_eq
    have h_tail_fun := congr_fun h_tail_val
    apply Subtype.ext
    ext i
    refine Fin.cases h0 (fun j => ?_) i
    have hj := h_tail_fun j
    have hx_c : (coneTail x) j = x j.succ / (1 - x 0) := coneTail_apply x hx j
    have hy_c : (coneTail y) j = y j.succ / (1 - y 0) := coneTail_apply y hy j
    change (coneTail x) j = (coneTail y) j at hj
    rw [hx_c, hy_c] at hj
    rw [h0] at hj
    have hy_sub : 1 - y 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
    exact (div_left_inj' hy_sub).mp hj

/-- Every recursive one-step cylinder chart is injective. -/
theorem chart_injective_all :
    ∀ (d : Nat) (q : Cell d), Function.Injective (chart d q)
  | 0, Sum.inl _ => chart_lower_injective 0
  | 0, Sum.inr pi => chart_upper_injective 0 pi
  | d + 1, Sum.inl _ => chart_lower_injective (d + 1)
  | d + 1, Sum.inr (Sum.inl pi) => chart_upper_injective (d + 1) pi
  | d + 1, Sum.inr (Sum.inr (k, q)) =>
      chart_side_injective d k q (chart_injective_all d q)

/-- Every recursive cylinder cell has pairwise distinct ordered vertices. -/
theorem vertex_injective_all
    (d : Nat) (q : Cell d) :
    Function.Injective (vertex d q) :=
  vertex_injective_of_chart_injective d q (chart_injective_all d q)

namespace Oriented

open SphereOddDegree.AffineBarycentricSubdivision

/-- Integral orientation coefficient of a recursive cylinder top cell. -/
def coefficientInt : (d : Nat) → Cell d → Int
  | 0, Sum.inl _ => -1
  | 0, Sum.inr pi => Equiv.Perm.sign pi
  | _d + 1, Sum.inl _ => -1
  | _d + 1, Sum.inr (Sum.inl pi) => Equiv.Perm.sign pi
  | d + 1, Sum.inr (Sum.inr (k, q)) =>
      -((-1 : Int) ^ k.1) * coefficientInt d q

/-- Orientation coefficient with values in an arbitrary commutative ring. -/
noncomputable def coefficient
    (R : Type) [CommRing R] : (d : Nat) → Cell d → R
  | 0, Sum.inl _ => -1
  | 0, Sum.inr pi => permSignCoeff R pi
  | _d + 1, Sum.inl _ => -1
  | _d + 1, Sum.inr (Sum.inl pi) => permSignCoeff R pi
  | d + 1, Sum.inr (Sum.inr (k, q)) =>
      -((-1 : R) ^ k.1) * coefficient R d q

@[simp] theorem coefficientInt_lower (d : Nat) :
    coefficientInt d (lowerCell d) = -1 := by
  cases d <;> rfl

@[simp] theorem coefficientInt_upper
    (d : Nat) (pi : Equiv.Perm (Fin (d + 1))) :
    coefficientInt d (upperCell d pi) = Equiv.Perm.sign pi := by
  cases d <;> rfl

@[simp] theorem coefficientInt_side
    (d : Nat) (k : Fin (d + 2)) (q : Cell d) :
    coefficientInt (d + 1) (sideCell d k q) =
      -((-1 : Int) ^ k.1) * coefficientInt d q := rfl

@[simp] theorem coefficient_lower
    (R : Type) [CommRing R] (d : Nat) :
    coefficient R d (lowerCell d) = -1 := by
  cases d <;> rfl

@[simp] theorem coefficient_upper
    (R : Type) [CommRing R]
    (d : Nat) (pi : Equiv.Perm (Fin (d + 1))) :
    coefficient R d (upperCell d pi) = permSignCoeff R pi := by
  cases d <;> rfl

@[simp] theorem coefficient_side
    (R : Type) [CommRing R]
    (d : Nat) (k : Fin (d + 2)) (q : Cell d) :
    coefficient R (d + 1) (sideCell d k q) =
      -((-1 : R) ^ k.1) * coefficient R d q := rfl

/-- Ordered vertex signature of the cone-base facet. -/
noncomputable def baseFacetVertex
    (d : Nat) (q : Cell d) (i : Fin (d + 1)) :
    Delta d × Set.Icc (0 : Real) 1 :=
  vertex d q i.succ

@[simp] theorem baseFacetVertex_lower
    (d : Nat) (i : Fin (d + 1)) :
    baseFacetVertex d (lowerCell d) i = lowerBoundaryVertex d i :=
  vertex_succ_lower d i

@[simp] theorem baseFacetVertex_upper
    (d : Nat) (pi : Equiv.Perm (Fin (d + 1))) (i : Fin (d + 1)) :
    baseFacetVertex d (upperCell d pi) i = upperBoundaryVertex d pi i :=
  vertex_succ_upper d pi i

@[simp] theorem baseFacetVertex_side
    (d : Nat) (k : Fin (d + 2)) (q : Cell d) (i : Fin (d + 2)) :
    baseFacetVertex (d + 1) (sideCell d k q) i =
      sidePoint d k (vertex d q i) :=
  vertex_succ_side d k q i

/-- Weighted pairing with the triangulated boundary simplex opposite the cone apex. -/
noncomputable def baseFacetPairing
    (R : Type) [CommRing R]
    (d : Nat)
    (W : (Fin (d + 1) → Delta d × Set.Icc (0 : Real) 1) → R) : R :=
  ∑ q : Cell d, coefficient R d q * W (baseFacetVertex d q)

/-- The lower coarse boundary contribution. -/
noncomputable def lowerPairing
    (R : Type) [CommRing R]
    (d : Nat)
    (W : (Fin (d + 1) → Delta d × Set.Icc (0 : Real) 1) → R) : R :=
  -W (lowerBoundaryVertex d)

/-- The upper barycentric-subdivision boundary contribution. -/
noncomputable def upperPairing
    (R : Type) [CommRing R]
    (d : Nat)
    (W : (Fin (d + 1) → Delta d × Set.Icc (0 : Real) 1) → R) : R :=
  ∑ pi : Equiv.Perm (Fin (d + 1)),
    permSignCoeff R pi * W (upperBoundaryVertex d pi)

/-- Recursive side-boundary contribution in positive dimension. -/
noncomputable def sidePairing
    (R : Type) [CommRing R]
    (d : Nat)
    (W : (Fin (d + 2) → Delta (d + 1) × Set.Icc (0 : Real) 1) → R) : R :=
  ∑ k : Fin (d + 2),
    ∑ q : Cell d,
      (-((-1 : R) ^ k.1) * coefficient R d q) *
        W (fun i => sidePoint d k (vertex d q i))

/-
In dimension zero the cone-base boundary is upper minus lower.
-/
theorem baseFacetPairing_zero
    (R : Type) [CommRing R]
    (W : (Fin 1 → Delta 0 × Set.Icc (0 : Real) 1) → R) :
    baseFacetPairing R 0 W = lowerPairing R 0 W + upperPairing R 0 W := by
  dsimp [baseFacetPairing, lowerPairing, upperPairing, Cell]
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_unique, Fintype.sum_unique]
  dsimp [coefficient, permSignCoeff]
  have h_low : baseFacetVertex 0 (Sum.inl ()) = lowerBoundaryVertex 0 := by
    funext i; fin_cases i; rfl
  have h_upp : baseFacetVertex 0 (Sum.inr 1) = upperBoundaryVertex 0 1 := by
    funext i; fin_cases i; rfl
  rw [h_low, h_upp]
  simp [Equiv.Perm.sign_one]

theorem baseFacetPairing_succ
    (R : Type) [CommRing R]
    (d : Nat)
    (W : (Fin (d + 2) → Delta (d + 1) × Set.Icc (0 : Real) 1) → R) :
    baseFacetPairing R (d + 1) W =
      lowerPairing R (d + 1) W + upperPairing R (d + 1) W +
        sidePairing R d W := by
  dsimp [baseFacetPairing, lowerPairing, upperPairing, sidePairing, Cell]
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_unique]
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_prod_type]
  have h_low : baseFacetVertex (d + 1) (Sum.inl ()) = lowerBoundaryVertex (d + 1) := by
    funext i; rfl
  have h_upp : ∀ pi, baseFacetVertex (d + 1) (Sum.inr (Sum.inl pi)) = upperBoundaryVertex (d + 1) pi := by
    intro pi; funext i; rfl
  have h_side : ∀ k q, baseFacetVertex (d + 1) (Sum.inr (Sum.inr (k, q))) = fun i => sidePoint d k (vertex d q i) := by
    intro k q; funext i; rfl
  simp_rw [h_low, h_upp, h_side]
  dsimp [coefficient]
  simp [add_assoc, mul_assoc]

end Oriented

end RelativeSubdivisionCylinderCombinatorics
end FoxNeuwirthOrderComplex
end NRR

namespace NRR.FoxNeuwirthOrderComplex.RelativeSubdivisionCylinderCombinatorics

/-
Every declared cylinder vertex at time zero is one of the coarse lower-boundary vertices.
-/
theorem vertex_eq_lowerBoundaryVertex_of_time_eq_zero :
    ∀ (d : Nat) (q : Cell d) (i : Fin (d + 2)),
      (vertex d q i).2.1 = 0 →
        ∃ j : Fin (d + 1), vertex d q i = lowerBoundaryVertex d j := by
  intro d;
  induction' d with d ih;
  · rintro ( _ | _ ) ( _ | _ ) <;> simp +decide [ vertex ];
    · unfold apex lowerBoundaryVertex; aesop;
    · exact fun h => absurd h <| ne_of_gt <| Subtype.mk_lt_mk.mpr <| by norm_num;
    · unfold upperBoundaryVertex; aesop;
  · intro q i hi; rcases q with ( _ | _ | q ) <;> rcases i with ( _ | i ) <;> norm_num [ NRR.FoxNeuwirthOrderComplex.RelativeSubdivisionCylinderCombinatorics.vertex ] at hi ⊢;
    · exact absurd hi ( by erw [ Subtype.mk_eq_mk ]; norm_num );
    · exact absurd hi ( by exact ne_of_gt ( by exact Subtype.mk_lt_mk.mpr ( by norm_num ) ) );
    · unfold upperBoundaryVertex at hi; norm_num at hi;
    · exact absurd hi ( by erw [ Subtype.mk_eq_mk ]; norm_num );
    · obtain ⟨ j, hj ⟩ := ih q.2 ⟨ i, by linarith ⟩ ( by simpa using congr_arg Subtype.val hi );
      use q.1.succAbove j; simp +decide [ hj, sidePoint, lowerBoundaryVertex ];

end NRR.FoxNeuwirthOrderComplex.RelativeSubdivisionCylinderCombinatorics

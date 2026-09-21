/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RefinedAffineMap
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.OrderComplexChain
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fin.Tuple.Basic
/-!
# The affine positive-ray boundary identity

This is the local PL intersection theorem required by S6.  An affine map from a `p`-simplex to
`ℝ^p`, transverse on every facet and avoiding the origin, meets the open positive diagonal ray in
an oriented compact interval (or not at all).  Hence the signed positive-ray intersections of its
oriented facets add to zero.

The proof is elementary finite-dimensional linear algebra.  In fixed difference coordinates the
zero set of the deviation map is an affine line.  Cramer's rule identifies the signs of its facet
endpoints with the alternating facet determinants.  The full-origin avoidance hypothesis makes the
coordinate mean have a constant sign along the interval.
-/

namespace NRR

open scoped BigOperators

namespace AffinePositiveRayBoundary

variable {p : Nat}

/-- Vertex values of one affine `p`-simplex in the full coordinate representation. -/
structure VertexMap (p : Nat) where
  /-- The full coordinate vector assigned to each vertex of the affine simplex. -/
  value : Fin (p + 1) → Fin p → Real

namespace VertexMap

/-- Full affine interpolation. -/
noncomputable def affineValue
    (V : VertexMap p) (w : StandardSimplex p) : Fin p → Real :=
  fun r => ∑ i : Fin (p + 1), w i * V.value i r

/-- Fixed difference coordinate. -/
noncomputable def deviation
    (hp : Nat.Prime p) (y : Fin p → Real) (r : Fin (p - 1)) : Real :=
  y (FoxNeuwirthOrderComplex.ReferenceAffineOrbitCount.coordinateLabel hp r) -
    y (FoxNeuwirthOrderComplex.ReferenceAffineOrbitCount.lastLabel hp)

/-- Mean coordinate. -/
noncomputable def mean (hp : Nat.Prime p) (y : Fin p → Real) : Real :=
  coordinateMean hp.pos y

/-- Restriction to the facet omitting vertex `k`. -/
noncomputable def facetValue
    (V : VertexMap p) (k : Fin (p + 1)) (i : Fin p) : Fin p → Real :=
  V.value (k.succAbove i)

/-- Reindex the `p` augmented rows as the `p - 1` deviation rows followed by the
constant row. -/
def augmentedRowEquiv (hp : Nat.Prime p) : Fin p ≃ Fin (p - 1 + 1) :=
  (Fin.castOrderIso (Nat.sub_add_cancel hp.pos).symm).toEquiv

/-- Augmented deviation matrix of an oriented facet. -/
noncomputable def facetMatrix
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1)) :
    Matrix (Fin p) (Fin p) Real :=
  fun r i => Fin.lastCases (1 : Real)
    (fun q => deviation hp (facetValue V k i) q) (augmentedRowEquiv hp r)

/-- Facet determinant. -/
noncomputable def facetDeterminant
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1)) : Real :=
  Matrix.det (facetMatrix hp V k)

/-- Canonical embedding of the `p` facet-vertex indices into the coordinate type of
`StandardSimplex (p - 1)`.  For positive `p` this is an equivalence; the inclusion form keeps
`facetAffineValue` meaningful without adding a positivity hypothesis to its public API. -/
def facetCoordinateIndex (i : Fin p) : Fin ((p - 1) + 1) :=
  Fin.castLE (by omega) i

/-- Full-coordinate affine interpolation on a facet. -/
noncomputable def facetAffineValue
    (V : VertexMap p) (k : Fin (p + 1))
    (w : StandardSimplex (p - 1)) : Fin p → Real :=
  fun r => ∑ i : Fin p, w (facetCoordinateIndex i) * facetValue V k i r

/-- A relative-interior intersection of a facet with the positive diagonal ray. -/
def FacetHasPositiveRayIntersection
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1)) : Prop :=
  ∃ w : StandardSimplex (p - 1),
    StandardSimplex.IsInterior w ∧
      (∀ r : Fin (p - 1), deviation hp (facetAffineValue V k w) r = 0) ∧
      0 < mean hp (facetAffineValue V k w)

noncomputable instance facetHasPositiveRayIntersectionDecidable
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1)) :
    Decidable (FacetHasPositiveRayIntersection hp V k) :=
  Classical.propDecidable _

/-- Signed positive-ray intersection number of one oriented facet. -/
noncomputable def facetIndex
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1)) : ZMod p :=
  if FacetHasPositiveRayIntersection hp V k then
    (-1 : ZMod p) ^ k.1 *
      FoxNeuwirthOrderComplex.AffineVertexMap.determinantIndex
        (facetDeterminant hp V k)
  else 0

/-- The affine simplex avoids the full origin. -/
def AvoidsOrigin (V : VertexMap p) : Prop :=
  ∀ w : StandardSimplex p, affineValue V w ≠ 0

/-- Facet transversality. -/
def FacetRegular (hp : Nat.Prime p) (V : VertexMap p) : Prop :=
  ∀ k : Fin (p + 1), facetDeterminant hp V k ≠ 0

/-- The deviation-zero affine line does not meet a codimension-two face of the simplex.  This is
the general-position condition needed to rule out a ray endpoint at the intersection of
two facets.  Facet regularity alone does not imply this condition. -/
def AvoidsCodimTwoDeviationZero (hp : Nat.Prime p) (V : VertexMap p) : Prop :=
  ∀ (w : StandardSimplex p) (i j : Fin (p + 1)), i ≠ j →
    (∀ r : Fin (p - 1), deviation hp (affineValue V w) r = 0) →
      ¬ (w i = 0 ∧ w j = 0)

/-- Positive-ray-relative codimension-two avoidance.  Degenerate deviation-zero points with
negative mean are irrelevant to the open positive ray and are intentionally permitted. -/
def AvoidsPositiveRayCodimTwo (hp : Nat.Prime p) (V : VertexMap p) : Prop :=
  ∀ (w : StandardSimplex p) (i j : Fin (p + 1)), i ≠ j →
    (∀ r : Fin (p - 1), deviation hp (affineValue V w) r = 0) →
      0 < mean hp (affineValue V w) → ¬ (w i = 0 ∧ w j = 0)

/-- Exact local hypotheses needed by positive-ray Stokes.  This is weaker than `GeneralPosition`:
it excludes codimension-two degeneracy only on the positive part of the deviation-zero line. -/
structure PositiveRayGeneralPosition (hp : Nat.Prime p) (V : VertexMap p) : Prop where
  facetRegular : FacetRegular hp V
  avoidsPositiveRayCodimTwo : AvoidsPositiveRayCodimTwo hp V
  avoidsOrigin : AvoidsOrigin V

/-- Exact local general-position hypotheses for unrestricted deviation-zero intersection theory. -/
structure GeneralPosition (hp : Nat.Prime p) (V : VertexMap p) : Prop where
  facetRegular : FacetRegular hp V
  avoidsCodimTwo : AvoidsCodimTwoDeviationZero hp V
  avoidsOrigin : AvoidsOrigin V

/-- Unrestricted codimension-two avoidance implies the positive-ray-relative condition. -/
theorem GeneralPosition.toPositiveRayGeneralPosition
    {hp : Nat.Prime p} {V : VertexMap p}
    (hgp : GeneralPosition hp V) : PositiveRayGeneralPosition hp V where
  facetRegular := hgp.facetRegular
  avoidsPositiveRayCodimTwo := by
    intro w i j hij hdev hmean
    exact hgp.avoidsCodimTwo w i j hij hdev
  avoidsOrigin := hgp.avoidsOrigin

/-- The rectangular augmented deviation matrix.  Its final row is the barycentric-sum row and
its preceding rows are the fixed deviation coordinates.  Deleting column `k` gives the oriented
facet matrix. -/
noncomputable def augmentedDeviationMatrix
    (hp : Nat.Prime p) (V : VertexMap p) :
    Matrix (Fin p) (Fin (p + 1)) Real :=
  fun r k => Fin.lastCases (1 : Real)
    (fun q => deviation hp (V.value k) q) (augmentedRowEquiv hp r)

/-- The signed maximal minor of a `p × (p+1)` matrix obtained by deleting column `k`. -/
noncomputable def signedMaximalMinor
    (A : Matrix (Fin p) (Fin (p + 1)) Real) (k : Fin (p + 1)) : Real :=
  (-1 : Real) ^ k.1 * Matrix.det (A.submatrix id k.succAbove)

/-- Laplace expansion with a repeated row: every row of a `p × (p+1)` matrix annihilates its
vector of signed maximal minors.  This is the rectangular cofactor-kernel identity used below. -/
theorem row_dot_signedMaximalMinor_eq_zero
    (A : Matrix (Fin p) (Fin (p + 1)) Real) (r : Fin p) :
    ∑ k : Fin (p + 1), A r k * signedMaximalMinor A k = 0 := by
  classical
  let B : Matrix (Fin (p + 1)) (Fin (p + 1)) Real :=
    fun i k => Fin.cases (A r k) (fun s => A s k) i
  have hrows : B 0 = B r.succ := by
    funext k
    simp [B]
  have hne : (0 : Fin (p + 1)) ≠ r.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  have hdet : Matrix.det B = 0 := by
    exact Matrix.det_zero_of_row_eq hne hrows
  rw [Matrix.det_succ_row_zero] at hdet
  have hminor : ∀ k : Fin (p + 1),
      Matrix.det (B.submatrix Fin.succ k.succAbove) =
        Matrix.det (A.submatrix id k.succAbove) := by
    intro k
    apply congrArg Matrix.det
    ext i j
    change A i (k.succAbove j) = A i (k.succAbove j)
    rfl
  simpa [signedMaximalMinor, B, hminor, mul_assoc, mul_left_comm, mul_comm] using hdet

/-- Deleting a column from the augmented deviation matrix gives the corresponding facet matrix. -/
theorem augmentedDeviationMatrix_minor
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1)) :
    (augmentedDeviationMatrix hp V).submatrix id k.succAbove = facetMatrix hp V k := by
  ext r i
  simp [augmentedDeviationMatrix, facetMatrix, facetValue]

/-- Cofactor direction of the affine deviation-zero line. -/
noncomputable def cofactorDirection
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1)) : Real :=
  (-1 : Real) ^ k.1 * facetDeterminant hp V k

/-- The project cofactor direction is exactly the signed-maximal-minor vector of the augmented
deviation matrix. -/
theorem cofactorDirection_eq_signedMaximalMinor
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1)) :
    cofactorDirection hp V k = signedMaximalMinor (augmentedDeviationMatrix hp V) k := by
  rw [cofactorDirection, signedMaximalMinor, facetDeterminant, augmentedDeviationMatrix_minor]

/-- Every row of the augmented deviation matrix annihilates the cofactor direction. -/
theorem augmentedDeviationMatrix_mul_cofactorDirection_eq_zero
    (hp : Nat.Prime p) (V : VertexMap p) (r : Fin p) :
    ∑ k : Fin (p + 1),
      augmentedDeviationMatrix hp V r k * cofactorDirection hp V k = 0 := by
  simpa only [cofactorDirection_eq_signedMaximalMinor] using
    row_dot_signedMaximalMinor_eq_zero (augmentedDeviationMatrix hp V) r

/-- Index of the final (constant) row of the augmented deviation matrix. -/
def constantRow (hp : Nat.Prime p) : Fin p :=
  (augmentedRowEquiv hp).symm (Fin.last (p - 1))

/-- Index of a deviation row in the augmented deviation matrix. -/
def deviationRow (hp : Nat.Prime p) (q : Fin (p - 1)) : Fin p :=
  (augmentedRowEquiv hp).symm q.castSucc

@[simp] theorem augmentedDeviationMatrix_constantRow
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1)) :
    augmentedDeviationMatrix hp V (constantRow hp) k = 1 := by
  simp [augmentedDeviationMatrix, constantRow, Fin.lastCases]

@[simp] theorem augmentedDeviationMatrix_deviationRow
    (hp : Nat.Prime p) (V : VertexMap p)
    (q : Fin (p - 1)) (k : Fin (p + 1)) :
    augmentedDeviationMatrix hp V (deviationRow hp q) k = deviation hp (V.value k) q := by
  simp [augmentedDeviationMatrix, deviationRow, Fin.lastCases]

/-- The cofactor direction preserves the barycentric sum. -/
theorem sum_cofactorDirection_eq_zero
    (hp : Nat.Prime p) (V : VertexMap p) :
    ∑ k : Fin (p + 1), cofactorDirection hp V k = 0 := by
  simpa using augmentedDeviationMatrix_mul_cofactorDirection_eq_zero
    hp V (constantRow hp)

/-- The cofactor direction lies in the kernel of every deviation row. -/
theorem weighted_deviation_sum_cofactorDirection_eq_zero
    (hp : Nat.Prime p) (V : VertexMap p) (q : Fin (p - 1)) :
    ∑ k : Fin (p + 1),
      cofactorDirection hp V k * deviation hp (V.value k) q = 0 := by
  have h := augmentedDeviationMatrix_mul_cofactorDirection_eq_zero
    hp V (deviationRow hp q)
  simpa [mul_comm] using h

/-- Under facet regularity, every coordinate of the cofactor direction is nonzero. -/
theorem cofactorDirection_ne_zero
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (k : Fin (p + 1)) :
    cofactorDirection hp V k ≠ 0 := by
  unfold cofactorDirection
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (hregular k)

/-- The facet matrix omitting vertex `0` is the tail-column block of the augmented matrix. -/
@[simp] theorem facetMatrix_zero_apply
    (hp : Nat.Prime p) (V : VertexMap p) (r : Fin p) (i : Fin p) :
    facetMatrix hp V 0 r i = augmentedDeviationMatrix hp V r i.succ := by
  simp [facetMatrix, augmentedDeviationMatrix, facetValue]

/-- A vector in the augmented-row kernel is zero if its zeroth coordinate is zero.  The remaining
coordinates form a vector annihilated by the facet matrix omitting vertex `0`; facet regularity
makes that square matrix nonsingular. -/
theorem eq_zero_of_zero_at_zero_of_augmented_rows_eq_zero
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (z : Fin (p + 1) → Real)
    (hz0 : z 0 = 0)
    (hzrows : ∀ r : Fin p,
      ∑ k : Fin (p + 1), augmentedDeviationMatrix hp V r k * z k = 0) :
    z = 0 := by
  classical
  let zTail : Fin p → Real := fun i => z i.succ
  have hmul : Matrix.mulVec (facetMatrix hp V 0) zTail = 0 := by
    funext r
    have hr := hzrows r
    rw [Fin.sum_univ_succ] at hr
    simp only [hz0, mul_zero, zero_add] at hr
    change (∑ i : Fin p, augmentedDeviationMatrix hp V r i.succ * z i.succ) = 0
    exact hr
  have hdet : Matrix.det (facetMatrix hp V 0) ≠ 0 := by
    simpa [facetDeterminant] using hregular 0
  have htail : zTail = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  funext k
  refine Fin.cases hz0 (fun i => ?_) k
  have hi := congr_fun htail i
  simpa [zTail] using hi

/-- The augmented-row kernel is the one-dimensional span of the cofactor direction.  The scalar
is fixed by the zeroth coordinate; subtracting that multiple leaves a kernel vector with zeroth
coordinate zero, hence the zero vector by the preceding nonsingularity lemma. -/
theorem eq_smul_cofactorDirection_of_augmented_rows_eq_zero
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (x : Fin (p + 1) → Real)
    (hx : ∀ r : Fin p,
      ∑ k : Fin (p + 1), augmentedDeviationMatrix hp V r k * x k = 0) :
    ∃ t : Real, x = t • cofactorDirection hp V := by
  classical
  let c : Fin (p + 1) → Real := cofactorDirection hp V
  let t : Real := x 0 / c 0
  let z : Fin (p + 1) → Real := x - t • c
  have hc0 : c 0 ≠ 0 := by
    simpa [c] using cofactorDirection_ne_zero hp V hregular 0
  have hz0 : z 0 = 0 := by
    simp [z, t, hc0]
  have hzrows : ∀ r : Fin p,
      ∑ k : Fin (p + 1), augmentedDeviationMatrix hp V r k * z k = 0 := by
    intro r
    calc
      ∑ k : Fin (p + 1), augmentedDeviationMatrix hp V r k * z k =
          ∑ k : Fin (p + 1),
            (augmentedDeviationMatrix hp V r k * x k -
              t * (augmentedDeviationMatrix hp V r k * c k)) := by
                apply Finset.sum_congr rfl
                intro k hk
                simp [z]
                ring
      _ = (∑ k : Fin (p + 1), augmentedDeviationMatrix hp V r k * x k) -
            ∑ k : Fin (p + 1),
              t * (augmentedDeviationMatrix hp V r k * c k) :=
              by rw [Finset.sum_sub_distrib]
      _ = (∑ k : Fin (p + 1), augmentedDeviationMatrix hp V r k * x k) -
            t * (∑ k : Fin (p + 1),
              augmentedDeviationMatrix hp V r k * c k) := by
              rw [Finset.mul_sum]
      _ = 0 := by
        rw [hx r]
        have hc : ∑ k : Fin (p + 1),
            augmentedDeviationMatrix hp V r k * c k = 0 := by
          simpa [c] using
            augmentedDeviationMatrix_mul_cofactorDirection_eq_zero hp V r
        rw [hc]
        ring
  have hz : z = 0 :=
    eq_zero_of_zero_at_zero_of_augmented_rows_eq_zero hp V hregular z hz0 hzrows
  refine ⟨t, ?_⟩
  have hsub : x - t • c = 0 := by
    simpa [z] using hz
  simpa [c] using sub_eq_zero.mp hsub

/-- Every row of the augmented matrix is either the final barycentric-sum row or one of the
preceding deviation rows. -/
theorem eq_constantRow_or_eq_deviationRow
    (hp : Nat.Prime p) (r : Fin p) :
    r = constantRow hp ∨ ∃ q : Fin (p - 1), r = deviationRow hp q := by
  have hp0 : 0 < p := hp.pos
  by_cases hlast : r.1 = p - 1
  · left
    apply Fin.ext
    simp [constantRow, augmentedRowEquiv, hlast]
  · right
    have hrlt : r.1 < p - 1 := by omega
    let q : Fin (p - 1) := ⟨r.1, hrlt⟩
    refine ⟨q, ?_⟩
    apply Fin.ext
    simp [deviationRow, augmentedRowEquiv, q]

/-- Deviation commutes with barycentric affine interpolation. -/
theorem deviation_affineValue_eq_weighted_sum
    (hp : Nat.Prime p) (V : VertexMap p) (w : StandardSimplex p)
    (q : Fin (p - 1)) :
    deviation hp (affineValue V w) q =
      ∑ k : Fin (p + 1), w k * deviation hp (V.value k) q := by
  unfold deviation affineValue
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Vanishing fixed deviations force every full coordinate to equal the distinguished final
coordinate. -/
theorem coordinate_eq_lastLabel_of_deviation_eq_zero
    (hp : Nat.Prime p) (y : Fin p → Real)
    (hdev : ∀ q : Fin (p - 1), deviation hp y q = 0)
    (i : Fin p) :
    y i = y (FoxNeuwirthOrderComplex.ReferenceAffineOrbitCount.lastLabel hp) := by
  by_cases hi : i = FoxNeuwirthOrderComplex.ReferenceAffineOrbitCount.lastLabel hp
  · simpa [hi]
  · obtain ⟨q, hq⟩ : ∃ q : Fin (p - 1),
        FoxNeuwirthOrderComplex.ReferenceAffineOrbitCount.coordinateLabel hp q = i := by
      have hiSet : i ∈ {x : Fin p |
          x ≠ FoxNeuwirthOrderComplex.ReferenceAffineOrbitCount.lastLabel hp} := hi
      rw [← FoxNeuwirthOrderComplex.ReferenceAffineOrbitCount.coordinateLabel_range hp] at hiSet
      exact hiSet
    subst i
    have hqzero := hdev q
    unfold deviation at hqzero
    linarith

/-- On the fixed-deviation-zero locus, the coordinate mean is the common coordinate value. -/
theorem mean_eq_lastLabel_of_deviation_eq_zero
    (hp : Nat.Prime p) (y : Fin p → Real)
    (hdev : ∀ q : Fin (p - 1), deviation hp y q = 0) :
    mean hp y = y (FoxNeuwirthOrderComplex.ReferenceAffineOrbitCount.lastLabel hp) := by
  have hall : ∀ i : Fin p,
      y i = y (FoxNeuwirthOrderComplex.ReferenceAffineOrbitCount.lastLabel hp) :=
    coordinate_eq_lastLabel_of_deviation_eq_zero hp y hdev
  unfold mean coordinateMean
  simp [hall, hp.ne_zero]

/-- The standard full-coordinate deviation vanishes whenever all fixed differences vanish. -/
theorem coordinateDeviation_eq_zero_of_deviation_eq_zero
    (hp : Nat.Prime p) (y : Fin p → Real)
    (hdev : ∀ q : Fin (p - 1), deviation hp y q = 0) :
    coordinateDeviation hp.pos y = 0 := by
  apply ZeroSum.ext
  intro i
  rw [coordinateDeviation_apply]
  change y i - coordinateMean hp.pos y = 0
  rw [show coordinateMean hp.pos y =
      y (FoxNeuwirthOrderComplex.ReferenceAffineOrbitCount.lastLabel hp) from
    mean_eq_lastLabel_of_deviation_eq_zero hp y hdev]
  exact sub_eq_zero.mpr
    (coordinate_eq_lastLabel_of_deviation_eq_zero hp y hdev i)

/-- Fixed deviations together with zero mean determine the zero full-coordinate vector. -/
theorem coordinate_eq_zero_of_deviation_eq_zero_of_mean_eq_zero
    (hp : Nat.Prime p) (y : Fin p → Real)
    (hdev : ∀ q : Fin (p - 1), deviation hp y q = 0)
    (hmean : mean hp y = 0) :
    y = 0 := by
  apply (coordinate_eq_zero_iff hp.pos y).2
  exact ⟨coordinateDeviation_eq_zero_of_deviation_eq_zero hp y hdev,
    by simpa [mean] using hmean⟩

/-- The coordinate mean commutes with barycentric affine interpolation. -/
theorem mean_affineValue_eq_weighted_sum
    (hp : Nat.Prime p) (V : VertexMap p) (w : StandardSimplex p) :
    mean hp (affineValue V w) =
      ∑ k : Fin (p + 1), w k * mean hp (V.value k) := by
  have haffine : affineValue V w =
      ∑ k : Fin (p + 1), w k • V.value k := by
    funext r
    simp [affineValue]
  rw [haffine]
  simp [mean]

/-- Two barycentric points with deviation-zero affine values differ by a scalar multiple of the
cofactor direction.  Their coordinate difference has barycentric sum zero and is annihilated by
every deviation row, so the augmented-kernel uniqueness theorem applies. -/
theorem sub_eq_smul_cofactorDirection_of_deviation_eq_zero
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (w₀ w₁ : StandardSimplex p)
    (hw₀ : ∀ q : Fin (p - 1), deviation hp (affineValue V w₀) q = 0)
    (hw₁ : ∀ q : Fin (p - 1), deviation hp (affineValue V w₁) q = 0) :
    ∃ t : Real,
      (fun k : Fin (p + 1) => w₁ k - w₀ k) =
        t • cofactorDirection hp V := by
  refine eq_smul_cofactorDirection_of_augmented_rows_eq_zero hp V hregular
    (fun k : Fin (p + 1) => w₁ k - w₀ k) ?_
  intro r
  rcases eq_constantRow_or_eq_deviationRow hp r with hr | ⟨q, hr⟩
  · subst r
    calc
      ∑ k : Fin (p + 1),
          augmentedDeviationMatrix hp V (constantRow hp) k * (w₁ k - w₀ k) =
          ∑ k : Fin (p + 1), (w₁ k - w₀ k) := by simp
      _ = (∑ k : Fin (p + 1), w₁ k) - ∑ k : Fin (p + 1), w₀ k :=
        by rw [Finset.sum_sub_distrib]
      _ = 0 := by
        rw [StandardSimplex.sum_eq_one, StandardSimplex.sum_eq_one]
        ring
  · subst r
    calc
      ∑ k : Fin (p + 1),
          augmentedDeviationMatrix hp V (deviationRow hp q) k * (w₁ k - w₀ k) =
          ∑ k : Fin (p + 1),
            (w₁ k * deviation hp (V.value k) q -
              w₀ k * deviation hp (V.value k) q) := by
                apply Finset.sum_congr rfl
                intro k hk
                rw [augmentedDeviationMatrix_deviationRow]
                ring
      _ = (∑ k : Fin (p + 1), w₁ k * deviation hp (V.value k) q) -
            ∑ k : Fin (p + 1), w₀ k * deviation hp (V.value k) q :=
              by rw [Finset.sum_sub_distrib]
      _ = deviation hp (affineValue V w₁) q -
            deviation hp (affineValue V w₀) q := by
              rw [deviation_affineValue_eq_weighted_sum,
                deviation_affineValue_eq_weighted_sum]
      _ = 0 := by rw [hw₁ q, hw₀ q, sub_self]

/-- Barycentric coordinate of the cofactor line through `w` at parameter `t`. -/
noncomputable def lineCoordinate
    (hp : Nat.Prime p) (V : VertexMap p)
    (w : StandardSimplex p) (t : Real) (k : Fin (p + 1)) : Real :=
  w k + t * cofactorDirection hp V k

/-- Parameters for which the cofactor line remains in the standard simplex.  The barycentric sum
is automatic because the cofactor direction has coordinate sum zero, so feasibility consists only
of the coordinatewise nonnegativity inequalities. -/
def LineFeasible
    (hp : Nat.Prime p) (V : VertexMap p)
    (w : StandardSimplex p) (t : Real) : Prop :=
  ∀ k : Fin (p + 1), 0 ≤ lineCoordinate hp V w t k

/-- Indices at which the cofactor direction points into the simplex as the parameter increases. -/
noncomputable def positiveCofactorIndices
    (hp : Nat.Prime p) (V : VertexMap p) : Finset (Fin (p + 1)) :=
  Finset.univ.filter fun k => 0 < cofactorDirection hp V k

/-- Indices at which the cofactor direction points out of the simplex as the parameter increases. -/
noncomputable def negativeCofactorIndices
    (hp : Nat.Prime p) (V : VertexMap p) : Finset (Fin (p + 1)) :=
  Finset.univ.filter fun k => cofactorDirection hp V k < 0

/-- A nonzero vector with zero coordinate sum has a positive coordinate. -/
theorem exists_pos_cofactorDirection
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) :
    ∃ k : Fin (p + 1), 0 < cofactorDirection hp V k := by
  by_contra h
  push Not at h
  have hstrict : cofactorDirection hp V 0 < 0 :=
    lt_of_le_of_ne (h 0) (cofactorDirection_ne_zero hp V hregular 0)
  have hsumneg :
      (∑ k : Fin (p + 1), cofactorDirection hp V k) < 0 :=
    Finset.sum_neg' (fun k _ => h k) ⟨0, by simpa using hstrict⟩
  rw [sum_cofactorDirection_eq_zero] at hsumneg
  exact (lt_irrefl 0) hsumneg

/-- A nonzero vector with zero coordinate sum has a negative coordinate. -/
theorem exists_neg_cofactorDirection
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) :
    ∃ k : Fin (p + 1), cofactorDirection hp V k < 0 := by
  by_contra h
  push Not at h
  have hstrict : 0 < cofactorDirection hp V 0 :=
    lt_of_le_of_ne (h 0) (Ne.symm (cofactorDirection_ne_zero hp V hregular 0))
  have hsumpos :
      0 < ∑ k : Fin (p + 1), cofactorDirection hp V k :=
    Finset.sum_pos' (fun k _ => h k) ⟨0, by simpa using hstrict⟩
  rw [sum_cofactorDirection_eq_zero] at hsumpos
  exact (lt_irrefl 0) hsumpos

/-- The positive cofactor-index finset is nonempty under facet regularity. -/
theorem positiveCofactorIndices_nonempty
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) :
    (positiveCofactorIndices hp V).Nonempty := by
  rcases exists_pos_cofactorDirection hp V hregular with ⟨k, hk⟩
  exact ⟨k, by simp [positiveCofactorIndices, hk]⟩

/-- The negative cofactor-index finset is nonempty under facet regularity. -/
theorem negativeCofactorIndices_nonempty
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) :
    (negativeCofactorIndices hp V).Nonempty := by
  rcases exists_neg_cofactorDirection hp V hregular with ⟨k, hk⟩
  exact ⟨k, by simp [negativeCofactorIndices, hk]⟩

/-- Lower-bound candidates contributed by positive cofactor coordinates. -/
noncomputable def positiveThresholds
    (hp : Nat.Prime p) (V : VertexMap p) (w : StandardSimplex p) : Finset Real :=
  (positiveCofactorIndices hp V).image fun k =>
    -w k / cofactorDirection hp V k

/-- Upper-bound candidates contributed by negative cofactor coordinates. -/
noncomputable def negativeThresholds
    (hp : Nat.Prime p) (V : VertexMap p) (w : StandardSimplex p) : Finset Real :=
  (negativeCofactorIndices hp V).image fun k =>
    -w k / cofactorDirection hp V k

/-- The lower-threshold finset is nonempty. -/
theorem positiveThresholds_nonempty
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    (positiveThresholds hp V w).Nonempty := by
  classical
  rcases positiveCofactorIndices_nonempty hp V hregular with ⟨k, hk⟩
  refine ⟨-w k / cofactorDirection hp V k, ?_⟩
  exact Finset.mem_image.mpr ⟨k, hk, rfl⟩

/-- The upper-threshold finset is nonempty. -/
theorem negativeThresholds_nonempty
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    (negativeThresholds hp V w).Nonempty := by
  classical
  rcases negativeCofactorIndices_nonempty hp V hregular with ⟨k, hk⟩
  refine ⟨-w k / cofactorDirection hp V k, ?_⟩
  exact Finset.mem_image.mpr ⟨k, hk, rfl⟩

/-- Greatest lower bound imposed by the positive cofactor coordinates. -/
noncomputable def lowerParameter
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) : Real :=
  (positiveThresholds hp V w).max'
    (positiveThresholds_nonempty hp V hregular w)

/-- Least upper bound imposed by the negative cofactor coordinates. -/
noncomputable def upperParameter
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) : Real :=
  (negativeThresholds hp V w).min'
    (negativeThresholds_nonempty hp V hregular w)

/-- Every positive-coordinate threshold lies below the chosen lower endpoint. -/
theorem positive_threshold_le_lowerParameter
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p)
    (k : Fin (p + 1)) (hk : 0 < cofactorDirection hp V k) :
    -w k / cofactorDirection hp V k ≤ lowerParameter hp V hregular w := by
  classical
  apply Finset.le_max'
  exact Finset.mem_image.mpr
    ⟨k, by simp [positiveCofactorIndices, hk], rfl⟩

/-- Every negative-coordinate threshold lies above the chosen upper endpoint. -/
theorem upperParameter_le_negative_threshold
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p)
    (k : Fin (p + 1)) (hk : cofactorDirection hp V k < 0) :
    upperParameter hp V hregular w ≤ -w k / cofactorDirection hp V k := by
  classical
  apply Finset.min'_le
  exact Finset.mem_image.mpr
    ⟨k, by simp [negativeCofactorIndices, hk], rfl⟩

/-- The lower endpoint is attained by a positive cofactor coordinate. -/
theorem lowerParameter_spec
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    ∃ k : Fin (p + 1),
      0 < cofactorDirection hp V k ∧
        lowerParameter hp V hregular w = -w k / cofactorDirection hp V k := by
  classical
  have hm : lowerParameter hp V hregular w ∈ positiveThresholds hp V w := by
    exact Finset.max'_mem _ _
  rcases Finset.mem_image.mp hm with ⟨k, hk, hvalue⟩
  refine ⟨k, ?_, hvalue.symm⟩
  simpa [positiveCofactorIndices] using hk

/-- The upper endpoint is attained by a negative cofactor coordinate. -/
theorem upperParameter_spec
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    ∃ k : Fin (p + 1),
      cofactorDirection hp V k < 0 ∧
        upperParameter hp V hregular w = -w k / cofactorDirection hp V k := by
  classical
  have hm : upperParameter hp V hregular w ∈ negativeThresholds hp V w := by
    exact Finset.min'_mem _ _
  rcases Finset.mem_image.mp hm with ⟨k, hk, hvalue⟩
  refine ⟨k, ?_, hvalue.symm⟩
  simpa [negativeCofactorIndices] using hk

/-- For a positive direction coordinate, nonnegativity is the corresponding lower-bound
inequality on the line parameter. -/
theorem lineCoordinate_nonneg_iff_of_pos
    (hp : Nat.Prime p) (V : VertexMap p)
    (w : StandardSimplex p) (t : Real) (k : Fin (p + 1))
    (hk : 0 < cofactorDirection hp V k) :
    0 ≤ lineCoordinate hp V w t k ↔
      -w k / cofactorDirection hp V k ≤ t := by
  unfold lineCoordinate
  constructor
  · intro h
    apply (div_le_iff₀ hk).2
    linarith
  · intro h
    have h' := (div_le_iff₀ hk).1 h
    linarith

/-- For a negative direction coordinate, nonnegativity is the corresponding upper-bound
inequality on the line parameter. -/
theorem lineCoordinate_nonneg_iff_of_neg
    (hp : Nat.Prime p) (V : VertexMap p)
    (w : StandardSimplex p) (t : Real) (k : Fin (p + 1))
    (hk : cofactorDirection hp V k < 0) :
    0 ≤ lineCoordinate hp V w t k ↔
      t ≤ -w k / cofactorDirection hp V k := by
  unfold lineCoordinate
  constructor
  · intro h
    apply (le_div_iff_of_neg hk).2
    linarith
  · intro h
    have h' := (le_div_iff_of_neg hk).1 h
    linarith

/-- The cofactor line meets the simplex exactly on the closed interval between the finite lower and
upper parameters. -/
theorem lineFeasible_iff_mem_Icc
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) (t : Real) :
    LineFeasible hp V w t ↔
      t ∈ Set.Icc (lowerParameter hp V hregular w)
        (upperParameter hp V hregular w) := by
  classical
  constructor
  · intro ht
    constructor
    · refine Finset.max'_le _ _ t ?_
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
      have hkpos : 0 < cofactorDirection hp V k := by
        simpa [positiveCofactorIndices] using hk
      exact (lineCoordinate_nonneg_iff_of_pos hp V w t k hkpos).1 (ht k)
    · refine Finset.le_min' _ _ t ?_
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
      have hkneg : cofactorDirection hp V k < 0 := by
        simpa [negativeCofactorIndices] using hk
      exact (lineCoordinate_nonneg_iff_of_neg hp V w t k hkneg).1 (ht k)
  · rintro ⟨hlower, hupper⟩ k
    rcases lt_trichotomy (cofactorDirection hp V k) 0 with hkneg | hkzero | hkpos
    · apply (lineCoordinate_nonneg_iff_of_neg hp V w t k hkneg).2
      exact hupper.trans
        (upperParameter_le_negative_threshold hp V hregular w k hkneg)
    · exact False.elim
        (cofactorDirection_ne_zero hp V hregular k hkzero)
    · apply (lineCoordinate_nonneg_iff_of_pos hp V w t k hkpos).2
      exact (positive_threshold_le_lowerParameter hp V hregular w k hkpos).trans hlower

/-- Set-level form of the line--simplex interval classification. -/
theorem lineFeasible_set_eq_Icc
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    {t : Real | LineFeasible hp V w t} =
      Set.Icc (lowerParameter hp V hregular w)
        (upperParameter hp V hregular w) := by
  ext t
  exact lineFeasible_iff_mem_Icc hp V hregular w t

/-- Parameter zero is feasible because it is the original simplex point. -/
theorem lineFeasible_zero
    (hp : Nat.Prime p) (V : VertexMap p) (w : StandardSimplex p) :
    LineFeasible hp V w 0 := by
  intro k
  simpa [lineCoordinate] using w.nonneg k

/-- The lower endpoint is at most zero. -/
theorem lowerParameter_le_zero
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    lowerParameter hp V hregular w ≤ 0 := by
  exact ((lineFeasible_iff_mem_Icc hp V hregular w 0).1
    (lineFeasible_zero hp V w)).1

/-- The upper endpoint is at least zero. -/
theorem zero_le_upperParameter
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    0 ≤ upperParameter hp V hregular w := by
  exact ((lineFeasible_iff_mem_Icc hp V hregular w 0).1
    (lineFeasible_zero hp V w)).2

/-- The finite lower endpoint does not exceed the finite upper endpoint. -/
theorem lowerParameter_le_upperParameter
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    lowerParameter hp V hregular w ≤ upperParameter hp V hregular w :=
  (lowerParameter_le_zero hp V hregular w).trans
    (zero_le_upperParameter hp V hregular w)

/-- The lower endpoint is feasible. -/
theorem lowerParameter_feasible
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    LineFeasible hp V w (lowerParameter hp V hregular w) := by
  apply (lineFeasible_iff_mem_Icc hp V hregular w _).2
  exact ⟨le_rfl, lowerParameter_le_upperParameter hp V hregular w⟩

/-- The upper endpoint is feasible. -/
theorem upperParameter_feasible
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    LineFeasible hp V w (upperParameter hp V hregular w) := by
  apply (lineFeasible_iff_mem_Icc hp V hregular w _).2
  exact ⟨lowerParameter_le_upperParameter hp V hregular w, le_rfl⟩

/-- Chosen coordinate attaining the lower endpoint. -/
noncomputable def lowerEndpointIndex
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) : Fin (p + 1) :=
  Classical.choose (lowerParameter_spec hp V hregular w)

/-- Chosen coordinate attaining the upper endpoint. -/
noncomputable def upperEndpointIndex
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) : Fin (p + 1) :=
  Classical.choose (upperParameter_spec hp V hregular w)

/-- The lower endpoint coordinate has positive cofactor direction. -/
theorem lowerEndpointIndex_pos
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    0 < cofactorDirection hp V (lowerEndpointIndex hp V hregular w) :=
  (Classical.choose_spec (lowerParameter_spec hp V hregular w)).1

/-- The upper endpoint coordinate has negative cofactor direction. -/
theorem upperEndpointIndex_neg
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    cofactorDirection hp V (upperEndpointIndex hp V hregular w) < 0 :=
  (Classical.choose_spec (upperParameter_spec hp V hregular w)).1

/-- Formula for the lower endpoint parameter at its chosen coordinate. -/
theorem lowerParameter_eq_threshold
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    lowerParameter hp V hregular w =
      -w (lowerEndpointIndex hp V hregular w) /
        cofactorDirection hp V (lowerEndpointIndex hp V hregular w) :=
  (Classical.choose_spec (lowerParameter_spec hp V hregular w)).2

/-- Formula for the upper endpoint parameter at its chosen coordinate. -/
theorem upperParameter_eq_threshold
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    upperParameter hp V hregular w =
      -w (upperEndpointIndex hp V hregular w) /
        cofactorDirection hp V (upperEndpointIndex hp V hregular w) :=
  (Classical.choose_spec (upperParameter_spec hp V hregular w)).2

/-- The chosen lower-endpoint coordinate vanishes. -/
theorem lowerEndpoint_coordinate_eq_zero
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    lineCoordinate hp V w (lowerParameter hp V hregular w)
      (lowerEndpointIndex hp V hregular w) = 0 := by
  have hc : cofactorDirection hp V (lowerEndpointIndex hp V hregular w) ≠ 0 :=
    cofactorDirection_ne_zero hp V hregular _
  rw [lineCoordinate, lowerParameter_eq_threshold]
  field_simp [hc]; ring

/-- The chosen upper-endpoint coordinate vanishes. -/
theorem upperEndpoint_coordinate_eq_zero
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    lineCoordinate hp V w (upperParameter hp V hregular w)
      (upperEndpointIndex hp V hregular w) = 0 := by
  have hc : cofactorDirection hp V (upperEndpointIndex hp V hregular w) ≠ 0 :=
    cofactorDirection_ne_zero hp V hregular _
  rw [lineCoordinate, upperParameter_eq_threshold]
  field_simp [hc]; ring

/-- A feasible line parameter gives a barycentric point of the standard simplex. -/
noncomputable def lineSimplexPoint
    (hp : Nat.Prime p) (V : VertexMap p) (w : StandardSimplex p)
    (t : Real) (ht : LineFeasible hp V w t) : StandardSimplex p :=
  ⟨fun k => lineCoordinate hp V w t k,
    ⟨ht, by
      calc
        ∑ k : Fin (p + 1), lineCoordinate hp V w t k =
            ∑ k : Fin (p + 1),
              (w k + t * cofactorDirection hp V k) := by rfl
        _ = (∑ k : Fin (p + 1), w k) +
              ∑ k : Fin (p + 1), t * cofactorDirection hp V k :=
            Finset.sum_add_distrib
        _ = (∑ k : Fin (p + 1), w k) +
              t * (∑ k : Fin (p + 1), cofactorDirection hp V k) := by
            rw [Finset.mul_sum]
        _ = 1 := by
          rw [StandardSimplex.sum_eq_one, sum_cofactorDirection_eq_zero]
          ring⟩⟩

@[simp] theorem lineSimplexPoint_apply
    (hp : Nat.Prime p) (V : VertexMap p) (w : StandardSimplex p)
    (t : Real) (ht : LineFeasible hp V w t) (k : Fin (p + 1)) :
    lineSimplexPoint hp V w t ht k = lineCoordinate hp V w t k :=
  rfl

/-- A scalar-multiple description of the barycentric difference identifies the second point with
its coordinatewise position on the cofactor line through the first point. -/
theorem lineCoordinate_eq_of_sub_eq_smul_cofactorDirection
    (hp : Nat.Prime p) (V : VertexMap p)
    (w₀ w₁ : StandardSimplex p) (t : Real)
    (hsub : (fun k : Fin (p + 1) => w₁ k - w₀ k) =
      t • cofactorDirection hp V) (k : Fin (p + 1)) :
    lineCoordinate hp V w₀ t k = w₁ k := by
  have hk := congrFun hsub k
  have hk' : w₁ k - w₀ k = t * cofactorDirection hp V k := by
    simpa using hk
  unfold lineCoordinate
  linarith

/-- Every zero-deviation simplex point lies on the feasible cofactor line through any chosen
zero-deviation base point. -/
theorem exists_lineSimplexPoint_eq_of_deviation_eq_zero
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (w₀ w₁ : StandardSimplex p)
    (hw₀ : ∀ q : Fin (p - 1), deviation hp (affineValue V w₀) q = 0)
    (hw₁ : ∀ q : Fin (p - 1), deviation hp (affineValue V w₁) q = 0) :
    ∃ t : Real, ∃ ht : LineFeasible hp V w₀ t,
      w₁ = lineSimplexPoint hp V w₀ t ht := by
  obtain ⟨t, hsub⟩ :=
    sub_eq_smul_cofactorDirection_of_deviation_eq_zero hp V hregular w₀ w₁ hw₀ hw₁
  have hcoord : ∀ k : Fin (p + 1), lineCoordinate hp V w₀ t k = w₁ k :=
    lineCoordinate_eq_of_sub_eq_smul_cofactorDirection hp V w₀ w₁ t hsub
  have ht : LineFeasible hp V w₀ t := by
    intro k
    rw [hcoord k]
    exact w₁.nonneg k
  refine ⟨t, ht, ?_⟩
  apply Subtype.ext
  funext k
  exact (hcoord k).symm

/-- Closed-interval form of the classification of all zero-deviation simplex points. -/
theorem exists_lineParameter_mem_Icc_of_deviation_eq_zero
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (w₀ w₁ : StandardSimplex p)
    (hw₀ : ∀ q : Fin (p - 1), deviation hp (affineValue V w₀) q = 0)
    (hw₁ : ∀ q : Fin (p - 1), deviation hp (affineValue V w₁) q = 0) :
    ∃ t : Real,
      t ∈ Set.Icc (lowerParameter hp V hregular w₀)
        (upperParameter hp V hregular w₀) ∧
      ∃ ht : LineFeasible hp V w₀ t,
        w₁ = lineSimplexPoint hp V w₀ t ht := by
  obtain ⟨t, ht, hpoint⟩ :=
    exists_lineSimplexPoint_eq_of_deviation_eq_zero hp V hregular w₀ w₁ hw₀ hw₁
  exact ⟨t, (lineFeasible_iff_mem_Icc hp V hregular w₀ t).1 ht, ht, hpoint⟩

/-- The cofactor-line parameter is unique under facet regularity. -/
theorem lineCoordinate_parameter_unique
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p)
    {t₀ t₁ : Real}
    (hline : (fun k : Fin (p + 1) => lineCoordinate hp V w t₀ k) =
      fun k : Fin (p + 1) => lineCoordinate hp V w t₁ k) :
    t₀ = t₁ := by
  have hk := congrFun hline (0 : Fin (p + 1))
  have hc : cofactorDirection hp V (0 : Fin (p + 1)) ≠ 0 :=
    cofactorDirection_ne_zero hp V hregular 0
  have hmul : (t₀ - t₁) * cofactorDirection hp V (0 : Fin (p + 1)) = 0 := by
    unfold lineCoordinate at hk
    linarith
  have hdiff : t₀ - t₁ = 0 := (mul_eq_zero.mp hmul).resolve_right hc
  linarith

/-- The feasible cofactor-line representation of a zero-deviation simplex point is unique. -/
theorem exists_unique_lineParameter_of_deviation_eq_zero
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (w₀ w₁ : StandardSimplex p)
    (hw₀ : ∀ q : Fin (p - 1), deviation hp (affineValue V w₀) q = 0)
    (hw₁ : ∀ q : Fin (p - 1), deviation hp (affineValue V w₁) q = 0) :
    ∃! t : Real, ∃ ht : LineFeasible hp V w₀ t,
      w₁ = lineSimplexPoint hp V w₀ t ht := by
  obtain ⟨t, ht, hpoint⟩ :=
    exists_lineSimplexPoint_eq_of_deviation_eq_zero hp V hregular w₀ w₁ hw₀ hw₁
  refine ⟨t, ⟨ht, hpoint⟩, ?_⟩
  intro s hs
  rcases hs with ⟨hsfeasible, hspoint⟩
  apply lineCoordinate_parameter_unique hp V hregular w₀
  funext k
  have htcoord := congrArg (fun z : StandardSimplex p => z k) hpoint
  have hscoord := congrArg (fun z : StandardSimplex p => z k) hspoint
  simpa using hscoord.symm.trans htcoord

/-- If the base point has zero deviation, every feasible point on the cofactor line also has zero
deviation. -/
theorem lineSimplexPoint_deviation_eq_zero
    (hp : Nat.Prime p) (V : VertexMap p) (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0)
    (t : Real) (ht : LineFeasible hp V w t) (q : Fin (p - 1)) :
    deviation hp (affineValue V (lineSimplexPoint hp V w t ht)) q = 0 := by
  rw [deviation_affineValue_eq_weighted_sum]
  calc
    ∑ k : Fin (p + 1),
        lineSimplexPoint hp V w t ht k * deviation hp (V.value k) q =
        ∑ k : Fin (p + 1),
          (w k * deviation hp (V.value k) q +
            t * (cofactorDirection hp V k * deviation hp (V.value k) q)) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [lineSimplexPoint_apply, lineCoordinate]
              ring
    _ = (∑ k : Fin (p + 1), w k * deviation hp (V.value k) q) +
          ∑ k : Fin (p + 1),
            t * (cofactorDirection hp V k * deviation hp (V.value k) q) :=
          Finset.sum_add_distrib
    _ = deviation hp (affineValue V w) q +
          t * (∑ k : Fin (p + 1),
            cofactorDirection hp V k * deviation hp (V.value k) q) := by
          rw [deviation_affineValue_eq_weighted_sum, Finset.mul_sum]
    _ = 0 := by
      rw [hw q, weighted_deviation_sum_cofactorDirection_eq_zero]
      ring

/-- Exact classification of the deviation-zero simplex locus by feasible cofactor-line points. -/
theorem deviation_eq_zero_iff_exists_lineSimplexPoint_eq
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (w₀ w₁ : StandardSimplex p)
    (hw₀ : ∀ q : Fin (p - 1), deviation hp (affineValue V w₀) q = 0) :
    (∀ q : Fin (p - 1), deviation hp (affineValue V w₁) q = 0) ↔
      ∃ t : Real, ∃ ht : LineFeasible hp V w₀ t,
        w₁ = lineSimplexPoint hp V w₀ t ht := by
  constructor
  · intro hw₁
    exact exists_lineSimplexPoint_eq_of_deviation_eq_zero
      hp V hregular w₀ w₁ hw₀ hw₁
  · rintro ⟨t, ht, rfl⟩ q
    exact lineSimplexPoint_deviation_eq_zero hp V w₀ hw₀ t ht q

/-- Slope of the coordinate mean along the cofactor line. -/
noncomputable def cofactorMeanSlope
    (hp : Nat.Prime p) (V : VertexMap p) : Real :=
  ∑ k : Fin (p + 1), cofactorDirection hp V k * mean hp (V.value k)

/-- The coordinate mean along the feasible cofactor line is affine in the line parameter. -/
theorem lineSimplexPoint_mean_eq
    (hp : Nat.Prime p) (V : VertexMap p) (w : StandardSimplex p)
    (t : Real) (ht : LineFeasible hp V w t) :
    mean hp (affineValue V (lineSimplexPoint hp V w t ht)) =
      mean hp (affineValue V w) + t * cofactorMeanSlope hp V := by
  rw [mean_affineValue_eq_weighted_sum]
  calc
    ∑ k : Fin (p + 1),
        lineSimplexPoint hp V w t ht k * mean hp (V.value k) =
        ∑ k : Fin (p + 1),
          (w k * mean hp (V.value k) +
            t * (cofactorDirection hp V k * mean hp (V.value k))) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [lineSimplexPoint_apply, lineCoordinate]
              ring
    _ = (∑ k : Fin (p + 1), w k * mean hp (V.value k)) +
          ∑ k : Fin (p + 1),
            t * (cofactorDirection hp V k * mean hp (V.value k)) :=
          Finset.sum_add_distrib
    _ = mean hp (affineValue V w) + t * cofactorMeanSlope hp V := by
          rw [← mean_affineValue_eq_weighted_sum, ← Finset.mul_sum]
          rfl

/-- Origin avoidance makes the mean nonzero at every deviation-zero simplex point. -/
theorem mean_ne_zero_of_deviation_eq_zero_of_avoidsOrigin
    (hp : Nat.Prime p) (V : VertexMap p)
    (havoid : AvoidsOrigin V) (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0) :
    mean hp (affineValue V w) ≠ 0 := by
  intro hmean
  apply havoid w
  exact coordinate_eq_zero_of_deviation_eq_zero_of_mean_eq_zero
    hp (affineValue V w) hw hmean

/-- Origin avoidance makes the mean nonzero everywhere on a feasible deviation-zero cofactor line. -/
theorem lineSimplexPoint_mean_ne_zero
    (hp : Nat.Prime p) (V : VertexMap p)
    (havoid : AvoidsOrigin V) (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0)
    (t : Real) (ht : LineFeasible hp V w t) :
    mean hp (affineValue V (lineSimplexPoint hp V w t ht)) ≠ 0 := by
  apply mean_ne_zero_of_deviation_eq_zero_of_avoidsOrigin hp V havoid
  intro q
  exact lineSimplexPoint_deviation_eq_zero hp V w hw t ht q

/-- An affine real function with opposite endpoint signs has a zero between the endpoints. -/
theorem exists_affine_zero_between_of_opposite_signs
    (a b t₀ t₁ : Real) (ht : t₀ ≤ t₁)
    (hopposite :
      (a + t₀ * b < 0 ∧ 0 < a + t₁ * b) ∨
        (0 < a + t₀ * b ∧ a + t₁ * b < 0)) :
    ∃ t : Real, t ∈ Set.Icc t₀ t₁ ∧ a + t * b = 0 := by
  rcases hopposite with hnegpos | hposneg
  · have hb : 0 < b := by
      by_contra h
      have hbnonpos : b ≤ 0 := le_of_not_gt h
      have hmul : (t₁ - t₀) * b ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht) hbnonpos
      nlinarith
    refine ⟨-a / b, ⟨?_, ?_⟩, ?_⟩
    · apply le_of_lt
      apply (lt_div_iff₀ hb).2
      linarith
    · apply le_of_lt
      apply (div_lt_iff₀ hb).2
      linarith
    · field_simp [ne_of_gt hb]; ring
  · have hb : b < 0 := by
      by_contra h
      have hbnonneg : 0 ≤ b := le_of_not_gt h
      have hmul : 0 ≤ (t₁ - t₀) * b :=
        mul_nonneg (sub_nonneg.mpr ht) hbnonneg
      nlinarith
    refine ⟨-a / b, ⟨?_, ?_⟩, ?_⟩
    · apply le_of_lt
      apply (lt_div_iff_of_neg hb).2
      linarith
    · apply le_of_lt
      apply (div_lt_iff_of_neg hb).2
      linarith
    · field_simp [ne_of_lt hb]; ring

/-- Along an ordered pair of feasible parameters, origin avoidance forces the mean to have the
same positive/nonpositive classification at both points. -/
theorem lineSimplexPoint_mean_pos_iff_of_le
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (havoid : AvoidsOrigin V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0)
    (t₀ t₁ : Real) (ht₀ : LineFeasible hp V w t₀)
    (ht₁ : LineFeasible hp V w t₁) (ht : t₀ ≤ t₁) :
    0 < mean hp (affineValue V (lineSimplexPoint hp V w t₀ ht₀)) ↔
      0 < mean hp (affineValue V (lineSimplexPoint hp V w t₁ ht₁)) := by
  let a : Real := mean hp (affineValue V w)
  let b : Real := cofactorMeanSlope hp V
  let m₀ : Real := mean hp (affineValue V (lineSimplexPoint hp V w t₀ ht₀))
  let m₁ : Real := mean hp (affineValue V (lineSimplexPoint hp V w t₁ ht₁))
  have hm₀ : m₀ = a + t₀ * b := by
    simpa [a, b, m₀] using lineSimplexPoint_mean_eq hp V w t₀ ht₀
  have hm₁ : m₁ = a + t₁ * b := by
    simpa [a, b, m₁] using lineSimplexPoint_mean_eq hp V w t₁ ht₁
  have hm₀ne : m₀ ≠ 0 := by
    simpa [m₀] using lineSimplexPoint_mean_ne_zero hp V havoid w hw t₀ ht₀
  have hm₁ne : m₁ ≠ 0 := by
    simpa [m₁] using lineSimplexPoint_mean_ne_zero hp V havoid w hw t₁ ht₁
  have hzeroImpossible : ¬ ((m₀ < 0 ∧ 0 < m₁) ∨ (0 < m₀ ∧ m₁ < 0)) := by
    intro hopposite
    have hopposite' :
        (a + t₀ * b < 0 ∧ 0 < a + t₁ * b) ∨
          (0 < a + t₀ * b ∧ a + t₁ * b < 0) := by
      rw [hm₀, hm₁] at hopposite
      exact hopposite
    rcases exists_affine_zero_between_of_opposite_signs a b t₀ t₁ ht hopposite' with
      ⟨t, htbetween, hmeanZero⟩
    have ht₀Icc := (lineFeasible_iff_mem_Icc hp V hregular w t₀).1 ht₀
    have ht₁Icc := (lineFeasible_iff_mem_Icc hp V hregular w t₁).1 ht₁
    have htfeasible : LineFeasible hp V w t := by
      apply (lineFeasible_iff_mem_Icc hp V hregular w t).2
      exact ⟨ht₀Icc.1.trans htbetween.1, htbetween.2.trans ht₁Icc.2⟩
    have hlineMeanZero :
        mean hp (affineValue V (lineSimplexPoint hp V w t htfeasible)) = 0 := by
      rw [lineSimplexPoint_mean_eq]
      simpa [a, b] using hmeanZero
    exact (lineSimplexPoint_mean_ne_zero hp V havoid w hw t htfeasible) hlineMeanZero
  constructor
  · intro hm₀pos
    have hm₁nonneg : 0 ≤ m₁ := by
      by_contra hm₁neg
      exact hzeroImpossible (Or.inr ⟨hm₀pos, lt_of_not_ge hm₁neg⟩)
    exact lt_of_le_of_ne hm₁nonneg (Ne.symm hm₁ne)
  · intro hm₁pos
    have hm₀nonneg : 0 ≤ m₀ := by
      by_contra hm₀neg
      exact hzeroImpossible (Or.inl ⟨lt_of_not_ge hm₀neg, hm₁pos⟩)
    exact lt_of_le_of_ne hm₀nonneg (Ne.symm hm₀ne)

/-- The mean has one constant sign on the entire feasible deviation-zero interval. -/
theorem lineSimplexPoint_mean_pos_iff
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (havoid : AvoidsOrigin V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0)
    (t₀ t₁ : Real) (ht₀ : LineFeasible hp V w t₀)
    (ht₁ : LineFeasible hp V w t₁) :
    0 < mean hp (affineValue V (lineSimplexPoint hp V w t₀ ht₀)) ↔
      0 < mean hp (affineValue V (lineSimplexPoint hp V w t₁ ht₁)) := by
  by_cases ht : t₀ ≤ t₁
  · exact lineSimplexPoint_mean_pos_iff_of_le hp V hregular havoid w hw
      t₀ t₁ ht₀ ht₁ ht
  · exact (lineSimplexPoint_mean_pos_iff_of_le hp V hregular havoid w hw
      t₁ t₀ ht₁ ht₀ (le_of_not_ge ht)).symm

/-- Under codimension-two avoidance, the chosen lower endpoint is the unique vanishing coordinate. -/
theorem lowerEndpoint_unique_zero
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsCodimTwoDeviationZero hp V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0)
    (j : Fin (p + 1))
    (hj : lineCoordinate hp V w (lowerParameter hp V hregular w) j = 0) :
    j = lowerEndpointIndex hp V hregular w := by
  by_contra hne
  let ht := lowerParameter_feasible hp V hregular w
  let wLower := lineSimplexPoint hp V w (lowerParameter hp V hregular w) ht
  have hdev : ∀ q : Fin (p - 1),
      deviation hp (affineValue V wLower) q = 0 := by
    intro q
    exact lineSimplexPoint_deviation_eq_zero hp V w hw _ ht q
  exact hcodim wLower j (lowerEndpointIndex hp V hregular w) hne hdev
    ⟨by simpa [wLower] using hj,
      by simpa [wLower] using lowerEndpoint_coordinate_eq_zero hp V hregular w⟩

/-- Under codimension-two avoidance, the chosen upper endpoint is the unique vanishing coordinate. -/
theorem upperEndpoint_unique_zero
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsCodimTwoDeviationZero hp V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0)
    (j : Fin (p + 1))
    (hj : lineCoordinate hp V w (upperParameter hp V hregular w) j = 0) :
    j = upperEndpointIndex hp V hregular w := by
  by_contra hne
  let ht := upperParameter_feasible hp V hregular w
  let wUpper := lineSimplexPoint hp V w (upperParameter hp V hregular w) ht
  have hdev : ∀ q : Fin (p - 1),
      deviation hp (affineValue V wUpper) q = 0 := by
    intro q
    exact lineSimplexPoint_deviation_eq_zero hp V w hw _ ht q
  exact hcodim wUpper j (upperEndpointIndex hp V hregular w) hne hdev
    ⟨by simpa [wUpper] using hj,
      by simpa [wUpper] using upperEndpoint_coordinate_eq_zero hp V hregular w⟩

/-- On the positive part of the deviation-zero line, the chosen lower endpoint is the unique
vanishing coordinate under positive-ray-relative codimension-two avoidance. -/
theorem lowerEndpoint_unique_zero_of_positiveMean
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsPositiveRayCodimTwo hp V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0)
    (hmean : 0 < mean hp
      (affineValue V (lineSimplexPoint hp V w
        (lowerParameter hp V hregular w)
        (lowerParameter_feasible hp V hregular w))))
    (j : Fin (p + 1))
    (hj : lineCoordinate hp V w (lowerParameter hp V hregular w) j = 0) :
    j = lowerEndpointIndex hp V hregular w := by
  by_contra hne
  let ht := lowerParameter_feasible hp V hregular w
  let wLower := lineSimplexPoint hp V w (lowerParameter hp V hregular w) ht
  have hdev : ∀ q : Fin (p - 1),
      deviation hp (affineValue V wLower) q = 0 := by
    intro q
    exact lineSimplexPoint_deviation_eq_zero hp V w hw _ ht q
  exact hcodim wLower j (lowerEndpointIndex hp V hregular w) hne hdev
    (by simpa [wLower] using hmean)
    ⟨by simpa [wLower] using hj,
      by simpa [wLower] using lowerEndpoint_coordinate_eq_zero hp V hregular w⟩

/-- On the positive part of the deviation-zero line, the chosen upper endpoint is the unique
vanishing coordinate under positive-ray-relative codimension-two avoidance. -/
theorem upperEndpoint_unique_zero_of_positiveMean
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsPositiveRayCodimTwo hp V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0)
    (hmean : 0 < mean hp
      (affineValue V (lineSimplexPoint hp V w
        (upperParameter hp V hregular w)
        (upperParameter_feasible hp V hregular w))))
    (j : Fin (p + 1))
    (hj : lineCoordinate hp V w (upperParameter hp V hregular w) j = 0) :
    j = upperEndpointIndex hp V hregular w := by
  by_contra hne
  let ht := upperParameter_feasible hp V hregular w
  let wUpper := lineSimplexPoint hp V w (upperParameter hp V hregular w) ht
  have hdev : ∀ q : Fin (p - 1),
      deviation hp (affineValue V wUpper) q = 0 := by
    intro q
    exact lineSimplexPoint_deviation_eq_zero hp V w hw _ ht q
  exact hcodim wUpper j (upperEndpointIndex hp V hregular w) hne hdev
    (by simpa [wUpper] using hmean)
    ⟨by simpa [wUpper] using hj,
      by simpa [wUpper] using upperEndpoint_coordinate_eq_zero hp V hregular w⟩

/-- Every nonomitted lower-endpoint coordinate is positive when that endpoint lies on the positive
ray. -/
theorem lowerEndpoint_coordinate_pos_of_ne_of_positiveMean
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsPositiveRayCodimTwo hp V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0)
    (hmean : 0 < mean hp
      (affineValue V (lineSimplexPoint hp V w
        (lowerParameter hp V hregular w)
        (lowerParameter_feasible hp V hregular w))))
    (j : Fin (p + 1))
    (hj : j ≠ lowerEndpointIndex hp V hregular w) :
    0 < lineCoordinate hp V w (lowerParameter hp V hregular w) j := by
  have hnonneg := lowerParameter_feasible hp V hregular w j
  have hnezero :
      lineCoordinate hp V w (lowerParameter hp V hregular w) j ≠ 0 := by
    intro hzero
    exact hj (lowerEndpoint_unique_zero_of_positiveMean hp V hregular hcodim
      w hw hmean j hzero)
  exact lt_of_le_of_ne hnonneg (Ne.symm hnezero)

/-- Every nonomitted upper-endpoint coordinate is positive when that endpoint lies on the positive
ray. -/
theorem upperEndpoint_coordinate_pos_of_ne_of_positiveMean
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsPositiveRayCodimTwo hp V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0)
    (hmean : 0 < mean hp
      (affineValue V (lineSimplexPoint hp V w
        (upperParameter hp V hregular w)
        (upperParameter_feasible hp V hregular w))))
    (j : Fin (p + 1))
    (hj : j ≠ upperEndpointIndex hp V hregular w) :
    0 < lineCoordinate hp V w (upperParameter hp V hregular w) j := by
  have hnonneg := upperParameter_feasible hp V hregular w j
  have hnezero :
      lineCoordinate hp V w (upperParameter hp V hregular w) j ≠ 0 := by
    intro hzero
    exact hj (upperEndpoint_unique_zero_of_positiveMean hp V hregular hcodim
      w hw hmean j hzero)
  exact lt_of_le_of_ne hnonneg (Ne.symm hnezero)

/-- Every nonvanishing coordinate at the lower endpoint is strictly positive. -/
theorem lowerEndpoint_coordinate_pos_of_ne
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsCodimTwoDeviationZero hp V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0)
    (j : Fin (p + 1))
    (hj : j ≠ lowerEndpointIndex hp V hregular w) :
    0 < lineCoordinate hp V w (lowerParameter hp V hregular w) j := by
  have hnonneg := lowerParameter_feasible hp V hregular w j
  have hnezero :
      lineCoordinate hp V w (lowerParameter hp V hregular w) j ≠ 0 := by
    intro hzero
    exact hj (lowerEndpoint_unique_zero hp V hregular hcodim w hw j hzero)
  exact lt_of_le_of_ne hnonneg (Ne.symm hnezero)

/-- Every nonvanishing coordinate at the upper endpoint is strictly positive. -/
theorem upperEndpoint_coordinate_pos_of_ne
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsCodimTwoDeviationZero hp V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0)
    (j : Fin (p + 1))
    (hj : j ≠ upperEndpointIndex hp V hregular w) :
    0 < lineCoordinate hp V w (upperParameter hp V hregular w) j := by
  have hnonneg := upperParameter_feasible hp V hregular w j
  have hnezero :
      lineCoordinate hp V w (upperParameter hp V hregular w) j ≠ 0 := by
    intro hzero
    exact hj (upperEndpoint_unique_zero hp V hregular hcodim w hw j hzero)
  exact lt_of_le_of_ne hnonneg (Ne.symm hnezero)

/-- The two endpoint coordinates are distinct because their cofactor signs are opposite. -/
theorem lowerEndpointIndex_ne_upperEndpointIndex
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    lowerEndpointIndex hp V hregular w ≠ upperEndpointIndex hp V hregular w := by
  intro heq
  have hpos := lowerEndpointIndex_pos hp V hregular w
  have hneg := upperEndpointIndex_neg hp V hregular w
  rw [← heq] at hneg
  linarith

/-- Under codimension-two avoidance, the feasible parameter interval is nondegenerate. -/
theorem lowerParameter_lt_upperParameter
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsCodimTwoDeviationZero hp V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0) :
    lowerParameter hp V hregular w < upperParameter hp V hregular w := by
  apply lt_of_le_of_ne (lowerParameter_le_upperParameter hp V hregular w)
  intro heq
  have hz : lineCoordinate hp V w (lowerParameter hp V hregular w)
      (upperEndpointIndex hp V hregular w) = 0 := by
    rw [heq]
    exact upperEndpoint_coordinate_eq_zero hp V hregular w
  have hindices : upperEndpointIndex hp V hregular w =
      lowerEndpointIndex hp V hregular w :=
    lowerEndpoint_unique_zero hp V hregular hcodim w hw _ hz
  have hpos := lowerEndpointIndex_pos hp V hregular w
  have hneg := upperEndpointIndex_neg hp V hregular w
  rw [hindices] at hneg
  linarith

/-- Complete endpoint classification: the lower endpoint has one vanishing coordinate with positive
cofactor direction, and no other coordinate vanishes. -/
theorem lowerEndpoint_classification
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsCodimTwoDeviationZero hp V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0) :
    0 < cofactorDirection hp V (lowerEndpointIndex hp V hregular w) ∧
      lineCoordinate hp V w (lowerParameter hp V hregular w)
          (lowerEndpointIndex hp V hregular w) = 0 ∧
      ∀ j : Fin (p + 1),
        lineCoordinate hp V w (lowerParameter hp V hregular w) j = 0 →
          j = lowerEndpointIndex hp V hregular w :=
  ⟨lowerEndpointIndex_pos hp V hregular w,
    lowerEndpoint_coordinate_eq_zero hp V hregular w,
    lowerEndpoint_unique_zero hp V hregular hcodim w hw⟩

/-- Complete endpoint classification: the upper endpoint has one vanishing coordinate with negative
cofactor direction, and no other coordinate vanishes. -/
theorem upperEndpoint_classification
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsCodimTwoDeviationZero hp V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0) :
    cofactorDirection hp V (upperEndpointIndex hp V hregular w) < 0 ∧
      lineCoordinate hp V w (upperParameter hp V hregular w)
          (upperEndpointIndex hp V hregular w) = 0 ∧
      ∀ j : Fin (p + 1),
        lineCoordinate hp V w (upperParameter hp V hregular w) j = 0 →
          j = upperEndpointIndex hp V hregular w :=
  ⟨upperEndpointIndex_neg hp V hregular w,
    upperEndpoint_coordinate_eq_zero hp V hregular w,
    upperEndpoint_unique_zero hp V hregular hcodim w hw⟩

/-- For prime `p`, the coordinate type of `StandardSimplex (p - 1)` is canonically
identified with the `p` vertices of a facet. -/
def facetIndexEquiv (hp : Nat.Prime p) : Fin ((p - 1) + 1) ≃ Fin p :=
  (augmentedRowEquiv hp).symm

/-- The generic facet-coordinate inclusion is inverse to `facetIndexEquiv` for prime `p`. -/
@[simp] theorem facetIndexEquiv_facetCoordinateIndex
    (hp : Nat.Prime p) (i : Fin p) :
    facetIndexEquiv hp (facetCoordinateIndex i) = i := by
  apply Fin.ext
  simp [facetIndexEquiv, facetCoordinateIndex, augmentedRowEquiv]

/-- The reverse composite is also the identity. -/
@[simp] theorem facetCoordinateIndex_facetIndexEquiv
    (hp : Nat.Prime p) (i : Fin ((p - 1) + 1)) :
    facetCoordinateIndex (facetIndexEquiv hp i) = i := by
  apply Fin.ext
  simp [facetIndexEquiv, facetCoordinateIndex, augmentedRowEquiv]

/-- Restrict a simplex point whose `k`-th coordinate vanishes to barycentric coordinates on the
facet omitting vertex `k`. -/
noncomputable def facetCoordinates
    (hp : Nat.Prime p) (w : StandardSimplex p)
    (k : Fin (p + 1)) (hk : w k = 0) : StandardSimplex (p - 1) :=
  ⟨fun i => w (k.succAbove (facetIndexEquiv hp i)),
    ⟨fun i => w.nonneg _, by
      have hrest : (∑ i : Fin p, w (k.succAbove i)) = 1 := by
        have hsum := w.sum_eq_one
        rw [Fin.sum_univ_succAbove (fun j : Fin (p + 1) => w j) k] at hsum
        simpa [hk] using hsum
      calc
        ∑ i : Fin ((p - 1) + 1), w (k.succAbove (facetIndexEquiv hp i)) =
            ∑ i : Fin p, w (k.succAbove i) := by
              exact Fintype.sum_equiv (facetIndexEquiv hp) _ _ (fun _ => rfl)
        _ = 1 := hrest⟩⟩

@[simp] theorem facetCoordinates_apply
    (hp : Nat.Prime p) (w : StandardSimplex p)
    (k : Fin (p + 1)) (hk : w k = 0) (i : Fin ((p - 1) + 1)) :
    facetCoordinates hp w k hk i = w (k.succAbove (facetIndexEquiv hp i)) :=
  rfl

/-- Reading the restricted point at the coordinate corresponding to facet vertex `i` recovers the
original simplex coordinate at `k.succAbove i`. -/
theorem facetCoordinates_facetCoordinateIndex
    (hp : Nat.Prime p) (w : StandardSimplex p)
    (k : Fin (p + 1)) (hk : w k = 0) (i : Fin p) :
    facetCoordinates hp w k hk (facetCoordinateIndex i) = w (k.succAbove i) := by
  simp [facetCoordinates]

/-- The restricted facet point is the unique facet-coordinate vector recovering all non-`k`
coordinates of the original simplex point. -/
theorem facetCoordinates_unique
    (hp : Nat.Prime p) (w : StandardSimplex p)
    (k : Fin (p + 1)) (hk : w k = 0)
    (u : StandardSimplex (p - 1))
    (hu : ∀ i : Fin p, u (facetCoordinateIndex i) = w (k.succAbove i)) :
    u = facetCoordinates hp w k hk := by
  apply Subtype.ext
  funext i
  have hi := hu (facetIndexEquiv hp i)
  simpa using hi

/-- If `k` is the unique zero coordinate of `w`, the restricted facet coordinates are in the
relative interior of the facet simplex. -/
theorem facetCoordinates_isInterior
    (hp : Nat.Prime p) (w : StandardSimplex p)
    (k : Fin (p + 1)) (hk : w k = 0)
    (hpos : ∀ j : Fin (p + 1), j ≠ k → 0 < w j) :
    StandardSimplex.IsInterior (facetCoordinates hp w k hk) := by
  intro i
  rw [facetCoordinates_apply]
  exact hpos _ (Fin.succAbove_ne k _)

/-- Affine interpolation of the restricted facet coordinates agrees with full-simplex affine
interpolation at the original point. -/
theorem facetAffineValue_facetCoordinates
    (hp : Nat.Prime p) (V : VertexMap p) (w : StandardSimplex p)
    (k : Fin (p + 1)) (hk : w k = 0) :
    facetAffineValue V k (facetCoordinates hp w k hk) = affineValue V w := by
  funext r
  unfold facetAffineValue affineValue
  calc
    ∑ i : Fin p,
        facetCoordinates hp w k hk (facetCoordinateIndex i) * facetValue V k i r =
        ∑ i : Fin p, w (k.succAbove i) * V.value (k.succAbove i) r := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [facetValue]
    _ = ∑ j : Fin (p + 1), w j * V.value j r := by
      rw [Fin.sum_univ_succAbove (fun j : Fin (p + 1) => w j * V.value j r) k]
      simp [hk]

/-- Deviation values are likewise unchanged by facet-coordinate conversion. -/
theorem deviation_facetAffineValue_facetCoordinates
    (hp : Nat.Prime p) (V : VertexMap p) (w : StandardSimplex p)
    (k : Fin (p + 1)) (hk : w k = 0) (q : Fin (p - 1)) :
    deviation hp (facetAffineValue V k (facetCoordinates hp w k hk)) q =
      deviation hp (affineValue V w) q := by
  rw [facetAffineValue_facetCoordinates]


/-- Embed barycentric coordinates on the facet omitting `k` into the full simplex by inserting a
zero at coordinate `k`.  The prime hypothesis identifies the `p` facet vertices with the
coordinate type of `StandardSimplex (p - 1)`. -/
noncomputable def fullSimplexOfFacet
    (hp : Nat.Prime p) (k : Fin (p + 1))
    (u : StandardSimplex (p - 1)) : StandardSimplex p :=
  ⟨k.insertNth (0 : Real) (fun i : Fin p => u (facetCoordinateIndex i)),
    ⟨by
      intro j
      rcases Fin.eq_self_or_eq_succAbove k j with rfl | ⟨i, rfl⟩
      · simp
      · simpa using u.nonneg (facetCoordinateIndex i),
     by
      rw [Fin.sum_univ_succAbove
        (fun j : Fin (p + 1) =>
          k.insertNth (0 : Real) (fun i : Fin p => u (facetCoordinateIndex i)) j) k]
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, zero_add]
      calc
        ∑ i : Fin p, u (facetCoordinateIndex i) =
            ∑ i : Fin ((p - 1) + 1), u i := by
          symm
          exact Fintype.sum_equiv (facetIndexEquiv hp)
            (fun i : Fin ((p - 1) + 1) => u i)
            (fun i : Fin p => u (facetCoordinateIndex i))
            (fun i => by simp)
        _ = 1 := u.sum_eq_one⟩⟩

/-- The inserted coordinate is zero. -/
@[simp] theorem fullSimplexOfFacet_omitted_eq_zero
    (hp : Nat.Prime p) (k : Fin (p + 1))
    (u : StandardSimplex (p - 1)) :
    fullSimplexOfFacet hp k u k = 0 := by
  simp [fullSimplexOfFacet]

/-- Every non-omitted coordinate recovers the corresponding facet coordinate. -/
@[simp] theorem fullSimplexOfFacet_succAbove
    (hp : Nat.Prime p) (k : Fin (p + 1))
    (u : StandardSimplex (p - 1)) (i : Fin p) :
    fullSimplexOfFacet hp k u (k.succAbove i) = u (facetCoordinateIndex i) := by
  simp [fullSimplexOfFacet]

/-- Recovery stated directly in the native coordinate type of the facet simplex. -/
theorem fullSimplexOfFacet_succAbove_facetIndexEquiv
    (hp : Nat.Prime p) (k : Fin (p + 1))
    (u : StandardSimplex (p - 1)) (i : Fin ((p - 1) + 1)) :
    fullSimplexOfFacet hp k u (k.succAbove (facetIndexEquiv hp i)) = u i := by
  simp [fullSimplexOfFacet]

/-- An interior facet point is strictly positive at every full-simplex coordinate other than the
inserted zero coordinate. -/
theorem fullSimplexOfFacet_pos_of_ne
    (hp : Nat.Prime p) (k : Fin (p + 1))
    (u : StandardSimplex (p - 1))
    (hu : StandardSimplex.IsInterior u)
    (j : Fin (p + 1)) (hj : j ≠ k) :
    0 < fullSimplexOfFacet hp k u j := by
  obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hj
  simpa using hu (facetCoordinateIndex i)

/-- For an interior facet point, the inserted coordinate is the unique zero coordinate of its
full-simplex embedding. -/
theorem fullSimplexOfFacet_eq_zero_iff
    (hp : Nat.Prime p) (k : Fin (p + 1))
    (u : StandardSimplex (p - 1))
    (hu : StandardSimplex.IsInterior u)
    (j : Fin (p + 1)) :
    fullSimplexOfFacet hp k u j = 0 ↔ j = k := by
  constructor
  · intro hjzero
    by_contra hj
    have hjpos := fullSimplexOfFacet_pos_of_ne hp k u hu j hj
    linarith
  · intro hj
    subst j
    exact fullSimplexOfFacet_omitted_eq_zero hp k u

/-- Restricting the full-simplex embedding back to the same facet recovers the original facet
point. -/
theorem facetCoordinates_fullSimplexOfFacet
    (hp : Nat.Prime p) (k : Fin (p + 1))
    (u : StandardSimplex (p - 1)) :
    facetCoordinates hp (fullSimplexOfFacet hp k u) k
        (fullSimplexOfFacet_omitted_eq_zero hp k u) = u := by
  apply Subtype.ext
  funext i
  simp [facetCoordinates, fullSimplexOfFacet]

/-- Conversely, embedding the facet coordinates of a full simplex point with zero `k`-th
coordinate recovers that full simplex point. -/
theorem fullSimplexOfFacet_facetCoordinates
    (hp : Nat.Prime p) (w : StandardSimplex p)
    (k : Fin (p + 1)) (hk : w k = 0) :
    fullSimplexOfFacet hp k (facetCoordinates hp w k hk) = w := by
  apply Subtype.ext
  funext j
  rcases Fin.eq_self_or_eq_succAbove k j with rfl | ⟨i, rfl⟩
  · simp [fullSimplexOfFacet, hk]
  · simp [fullSimplexOfFacet, facetCoordinates]

/-- Affine interpolation of an embedded facet point agrees with affine interpolation on the
facet.  This is the inverse direction of `facetAffineValue_facetCoordinates`. -/
theorem affineValue_fullSimplexOfFacet
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1))
    (u : StandardSimplex (p - 1)) :
    affineValue V (fullSimplexOfFacet hp k u) = facetAffineValue V k u := by
  symm
  simpa only [facetCoordinates_fullSimplexOfFacet] using
    facetAffineValue_facetCoordinates hp V (fullSimplexOfFacet hp k u) k
      (fullSimplexOfFacet_omitted_eq_zero hp k u)

/-- Fixed-deviation coordinates are preserved by embedding a facet point into the full simplex. -/
@[simp] theorem deviation_affineValue_fullSimplexOfFacet
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1))
    (u : StandardSimplex (p - 1)) (q : Fin (p - 1)) :
    deviation hp (affineValue V (fullSimplexOfFacet hp k u)) q =
      deviation hp (facetAffineValue V k u) q := by
  rw [affineValue_fullSimplexOfFacet]

/-- The mean coordinate is preserved by embedding a facet point into the full simplex. -/
@[simp] theorem mean_affineValue_fullSimplexOfFacet
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1))
    (u : StandardSimplex (p - 1)) :
    mean hp (affineValue V (fullSimplexOfFacet hp k u)) =
      mean hp (facetAffineValue V k u) := by
  rw [affineValue_fullSimplexOfFacet]

/-- A facet point with zero fixed deviations gives a full-simplex point with zero fixed deviations. -/
theorem fullSimplexOfFacet_deviation_eq_zero
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1))
    (u : StandardSimplex (p - 1))
    (hu : ∀ q : Fin (p - 1), deviation hp (facetAffineValue V k u) q = 0) :
    ∀ q : Fin (p - 1),
      deviation hp (affineValue V (fullSimplexOfFacet hp k u)) q = 0 := by
  intro q
  simpa using hu q

/-- A positive-mean facet point gives a positive-mean full-simplex point. -/
theorem fullSimplexOfFacet_mean_pos
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1))
    (u : StandardSimplex (p - 1))
    (hu : 0 < mean hp (facetAffineValue V k u)) :
    0 < mean hp (affineValue V (fullSimplexOfFacet hp k u)) := by
  simpa using hu

/-- The deviation-zero and positive-mean data of a positive-ray facet witness transfer together to
its full-simplex embedding. -/
theorem fullSimplexOfFacet_positiveRayData
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1))
    (u : StandardSimplex (p - 1))
    (hdev : ∀ q : Fin (p - 1), deviation hp (facetAffineValue V k u) q = 0)
    (hmean : 0 < mean hp (facetAffineValue V k u)) :
    (∀ q : Fin (p - 1),
      deviation hp (affineValue V (fullSimplexOfFacet hp k u)) q = 0) ∧
      0 < mean hp (affineValue V (fullSimplexOfFacet hp k u)) :=
  ⟨fullSimplexOfFacet_deviation_eq_zero hp V k u hdev,
    fullSimplexOfFacet_mean_pos hp V k u hmean⟩

/-- The simplex point at the lower feasible parameter. -/
noncomputable def lowerEndpointSimplexPoint
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) : StandardSimplex p :=
  lineSimplexPoint hp V w (lowerParameter hp V hregular w)
    (lowerParameter_feasible hp V hregular w)

/-- The simplex point at the upper feasible parameter. -/
noncomputable def upperEndpointSimplexPoint
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) : StandardSimplex p :=
  lineSimplexPoint hp V w (upperParameter hp V hregular w)
    (upperParameter_feasible hp V hregular w)

@[simp] theorem lowerEndpointSimplexPoint_apply
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) (j : Fin (p + 1)) :
    lowerEndpointSimplexPoint hp V hregular w j =
      lineCoordinate hp V w (lowerParameter hp V hregular w) j :=
  rfl

@[simp] theorem upperEndpointSimplexPoint_apply
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) (j : Fin (p + 1)) :
    upperEndpointSimplexPoint hp V hregular w j =
      lineCoordinate hp V w (upperParameter hp V hregular w) j :=
  rfl

/-- The omitted coordinate of the lower endpoint point is zero. -/
theorem lowerEndpointSimplexPoint_omitted_eq_zero
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    lowerEndpointSimplexPoint hp V hregular w
        (lowerEndpointIndex hp V hregular w) = 0 := by
  exact lowerEndpoint_coordinate_eq_zero hp V hregular w

/-- The omitted coordinate of the upper endpoint point is zero. -/
theorem upperEndpointSimplexPoint_omitted_eq_zero
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    upperEndpointSimplexPoint hp V hregular w
        (upperEndpointIndex hp V hregular w) = 0 := by
  exact upperEndpoint_coordinate_eq_zero hp V hregular w

/-- Restriction of the lower endpoint to its unique boundary facet. -/
noncomputable def lowerEndpointFacetPoint
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    StandardSimplex (p - 1) :=
  facetCoordinates hp (lowerEndpointSimplexPoint hp V hregular w)
    (lowerEndpointIndex hp V hregular w)
    (lowerEndpointSimplexPoint_omitted_eq_zero hp V hregular w)

/-- Restriction of the upper endpoint to its unique boundary facet. -/
noncomputable def upperEndpointFacetPoint
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    StandardSimplex (p - 1) :=
  facetCoordinates hp (upperEndpointSimplexPoint hp V hregular w)
    (upperEndpointIndex hp V hregular w)
    (upperEndpointSimplexPoint_omitted_eq_zero hp V hregular w)

/-- The lower endpoint gives a relative-interior point of its boundary facet. -/
theorem lowerEndpointFacetPoint_isInterior
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsCodimTwoDeviationZero hp V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0) :
    StandardSimplex.IsInterior (lowerEndpointFacetPoint hp V hregular w) := by
  refine facetCoordinates_isInterior hp
    (lowerEndpointSimplexPoint hp V hregular w)
    (lowerEndpointIndex hp V hregular w)
    (lowerEndpointSimplexPoint_omitted_eq_zero hp V hregular w) ?_
  intro j hj
  simpa [lowerEndpointSimplexPoint] using
    lowerEndpoint_coordinate_pos_of_ne hp V hregular hcodim w hw j hj

/-- The upper endpoint gives a relative-interior point of its boundary facet. -/
theorem upperEndpointFacetPoint_isInterior
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsCodimTwoDeviationZero hp V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0) :
    StandardSimplex.IsInterior (upperEndpointFacetPoint hp V hregular w) := by
  refine facetCoordinates_isInterior hp
    (upperEndpointSimplexPoint hp V hregular w)
    (upperEndpointIndex hp V hregular w)
    (upperEndpointSimplexPoint_omitted_eq_zero hp V hregular w) ?_
  intro j hj
  simpa [upperEndpointSimplexPoint] using
    upperEndpoint_coordinate_pos_of_ne hp V hregular hcodim w hw j hj

/-- A positive lower endpoint gives a relative-interior point of its boundary facet under
positive-ray-relative codimension-two avoidance. -/
theorem lowerEndpointFacetPoint_isInterior_of_positiveMean
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsPositiveRayCodimTwo hp V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0)
    (hmean : 0 < mean hp (affineValue V
      (lowerEndpointSimplexPoint hp V hregular w))) :
    StandardSimplex.IsInterior (lowerEndpointFacetPoint hp V hregular w) := by
  refine facetCoordinates_isInterior hp
    (lowerEndpointSimplexPoint hp V hregular w)
    (lowerEndpointIndex hp V hregular w)
    (lowerEndpointSimplexPoint_omitted_eq_zero hp V hregular w) ?_
  intro j hj
  simpa [lowerEndpointSimplexPoint] using
    lowerEndpoint_coordinate_pos_of_ne_of_positiveMean hp V hregular hcodim
      w hw (by simpa [lowerEndpointSimplexPoint] using hmean) j hj

/-- A positive upper endpoint gives a relative-interior point of its boundary facet under
positive-ray-relative codimension-two avoidance. -/
theorem upperEndpointFacetPoint_isInterior_of_positiveMean
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsPositiveRayCodimTwo hp V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0)
    (hmean : 0 < mean hp (affineValue V
      (upperEndpointSimplexPoint hp V hregular w))) :
    StandardSimplex.IsInterior (upperEndpointFacetPoint hp V hregular w) := by
  refine facetCoordinates_isInterior hp
    (upperEndpointSimplexPoint hp V hregular w)
    (upperEndpointIndex hp V hregular w)
    (upperEndpointSimplexPoint_omitted_eq_zero hp V hregular w) ?_
  intro j hj
  simpa [upperEndpointSimplexPoint] using
    upperEndpoint_coordinate_pos_of_ne_of_positiveMean hp V hregular hcodim
      w hw (by simpa [upperEndpointSimplexPoint] using hmean) j hj

/-- Facet interpolation at the lower endpoint restriction equals full interpolation at the lower
endpoint simplex point. -/
theorem lowerEndpoint_facetAffineValue_eq
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    facetAffineValue V (lowerEndpointIndex hp V hregular w)
        (lowerEndpointFacetPoint hp V hregular w) =
      affineValue V (lowerEndpointSimplexPoint hp V hregular w) := by
  simpa [lowerEndpointFacetPoint] using
    facetAffineValue_facetCoordinates hp V
      (lowerEndpointSimplexPoint hp V hregular w)
      (lowerEndpointIndex hp V hregular w)
      (lowerEndpointSimplexPoint_omitted_eq_zero hp V hregular w)

/-- Facet interpolation at the upper endpoint restriction equals full interpolation at the upper
endpoint simplex point. -/
theorem upperEndpoint_facetAffineValue_eq
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p) :
    facetAffineValue V (upperEndpointIndex hp V hregular w)
        (upperEndpointFacetPoint hp V hregular w) =
      affineValue V (upperEndpointSimplexPoint hp V hregular w) := by
  simpa [upperEndpointFacetPoint] using
    facetAffineValue_facetCoordinates hp V
      (upperEndpointSimplexPoint hp V hregular w)
      (upperEndpointIndex hp V hregular w)
      (upperEndpointSimplexPoint_omitted_eq_zero hp V hregular w)

/-- The lower endpoint facet point has zero deviation whenever the base line point does. -/
theorem lowerEndpointFacetPoint_deviation_eq_zero
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0)
    (q : Fin (p - 1)) :
    deviation hp
        (facetAffineValue V (lowerEndpointIndex hp V hregular w)
          (lowerEndpointFacetPoint hp V hregular w)) q = 0 := by
  rw [lowerEndpoint_facetAffineValue_eq]
  simpa [lowerEndpointSimplexPoint] using
    lineSimplexPoint_deviation_eq_zero hp V w hw
      (lowerParameter hp V hregular w)
      (lowerParameter_feasible hp V hregular w) q

/-- The upper endpoint facet point has zero deviation whenever the base line point does. -/
theorem upperEndpointFacetPoint_deviation_eq_zero
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0)
    (q : Fin (p - 1)) :
    deviation hp
        (facetAffineValue V (upperEndpointIndex hp V hregular w)
          (upperEndpointFacetPoint hp V hregular w)) q = 0 := by
  rw [upperEndpoint_facetAffineValue_eq]
  simpa [upperEndpointSimplexPoint] using
    lineSimplexPoint_deviation_eq_zero hp V w hw
      (upperParameter hp V hregular w)
      (upperParameter_feasible hp V hregular w) q

/-- The lower and upper endpoint means have the same sign. -/
theorem lowerEndpoint_mean_pos_iff_upperEndpoint_mean_pos
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (havoid : AvoidsOrigin V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0) :
    0 < mean hp (affineValue V (lowerEndpointSimplexPoint hp V hregular w)) ↔
      0 < mean hp (affineValue V (upperEndpointSimplexPoint hp V hregular w)) := by
  simpa [lowerEndpointSimplexPoint, upperEndpointSimplexPoint] using
    lineSimplexPoint_mean_pos_iff hp V hregular havoid w hw
      (lowerParameter hp V hregular w) (upperParameter hp V hregular w)
      (lowerParameter_feasible hp V hregular w)
      (upperParameter_feasible hp V hregular w)

/-- Mean-sign constancy transferred to the two relative-interior facet representatives. -/
theorem lowerEndpointFacet_mean_pos_iff_upperEndpointFacet_mean_pos
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (havoid : AvoidsOrigin V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0) :
    0 < mean hp
        (facetAffineValue V (lowerEndpointIndex hp V hregular w)
          (lowerEndpointFacetPoint hp V hregular w)) ↔
      0 < mean hp
        (facetAffineValue V (upperEndpointIndex hp V hregular w)
          (upperEndpointFacetPoint hp V hregular w)) := by
  rw [lowerEndpoint_facetAffineValue_eq, upperEndpoint_facetAffineValue_eq]
  exact lowerEndpoint_mean_pos_iff_upperEndpoint_mean_pos hp V hregular havoid w hw

/-- A positive mean at the lower endpoint supplies the required positive-ray facet witness. -/
theorem lowerEndpoint_facetHasPositiveRayIntersection
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsCodimTwoDeviationZero hp V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0)
    (hmean : 0 < mean hp
      (affineValue V (lineSimplexPoint hp V w
        (lowerParameter hp V hregular w)
        (lowerParameter_feasible hp V hregular w)))) :
    FacetHasPositiveRayIntersection hp V (lowerEndpointIndex hp V hregular w) := by
  refine ⟨lowerEndpointFacetPoint hp V hregular w,
    lowerEndpointFacetPoint_isInterior hp V hregular hcodim w hw, ?_, ?_⟩
  · intro q
    exact lowerEndpointFacetPoint_deviation_eq_zero hp V hregular w hw q
  · rw [lowerEndpoint_facetAffineValue_eq]
    exact hmean

/-- A positive mean at the upper endpoint supplies the required positive-ray facet witness. -/
theorem upperEndpoint_facetHasPositiveRayIntersection
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsCodimTwoDeviationZero hp V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0)
    (hmean : 0 < mean hp
      (affineValue V (lineSimplexPoint hp V w
        (upperParameter hp V hregular w)
        (upperParameter_feasible hp V hregular w)))) :
    FacetHasPositiveRayIntersection hp V (upperEndpointIndex hp V hregular w) := by
  refine ⟨upperEndpointFacetPoint hp V hregular w,
    upperEndpointFacetPoint_isInterior hp V hregular hcodim w hw, ?_, ?_⟩
  · intro q
    exact upperEndpointFacetPoint_deviation_eq_zero hp V hregular w hw q
  · rw [upperEndpoint_facetAffineValue_eq]
    exact hmean

/-- A positive lower endpoint supplies the positive-ray facet witness under the weaker
positive-ray-relative codimension-two condition. -/
theorem lowerEndpoint_facetHasPositiveRayIntersection_of_positiveCodimTwo
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsPositiveRayCodimTwo hp V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0)
    (hmean : 0 < mean hp
      (affineValue V (lowerEndpointSimplexPoint hp V hregular w))) :
    FacetHasPositiveRayIntersection hp V (lowerEndpointIndex hp V hregular w) := by
  refine ⟨lowerEndpointFacetPoint hp V hregular w,
    lowerEndpointFacetPoint_isInterior_of_positiveMean hp V hregular hcodim
      w hw hmean, ?_, ?_⟩
  · intro q
    exact lowerEndpointFacetPoint_deviation_eq_zero hp V hregular w hw q
  · rw [lowerEndpoint_facetAffineValue_eq]
    exact hmean

/-- A positive upper endpoint supplies the positive-ray facet witness under the weaker
positive-ray-relative codimension-two condition. -/
theorem upperEndpoint_facetHasPositiveRayIntersection_of_positiveCodimTwo
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsPositiveRayCodimTwo hp V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0)
    (hmean : 0 < mean hp
      (affineValue V (upperEndpointSimplexPoint hp V hregular w))) :
    FacetHasPositiveRayIntersection hp V (upperEndpointIndex hp V hregular w) := by
  refine ⟨upperEndpointFacetPoint hp V hregular w,
    upperEndpointFacetPoint_isInterior_of_positiveMean hp V hregular hcodim
      w hw hmean, ?_, ?_⟩
  · intro q
    exact upperEndpointFacetPoint_deviation_eq_zero hp V hregular w hw q
  · rw [upperEndpoint_facetAffineValue_eq]
    exact hmean

/-- A feasible cofactor-line point with a vanishing coordinate occurs at one of the two
finite interval endpoints.  The sign of that coordinate's cofactor direction determines which
endpoint is attained. -/
theorem lineParameter_eq_lower_or_upper_of_coordinate_eq_zero
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V) (w : StandardSimplex p)
    (t : Real) (ht : LineFeasible hp V w t) (k : Fin (p + 1))
    (hk : lineCoordinate hp V w t k = 0) :
    t = lowerParameter hp V hregular w ∨
      t = upperParameter hp V hregular w := by
  have htIcc := (lineFeasible_iff_mem_Icc hp V hregular w t).1 ht
  rcases lt_trichotomy (cofactorDirection hp V k) 0 with hcneg | hczero | hcpos
  · have hcne : cofactorDirection hp V k ≠ 0 := ne_of_lt hcneg
    have hmul : t * cofactorDirection hp V k = -w k := by
      unfold lineCoordinate at hk
      linarith
    have hthreshold : t = -w k / cofactorDirection hp V k := by
      exact (eq_div_iff hcne).2 hmul
    right
    apply le_antisymm htIcc.2
    rw [hthreshold]
    exact upperParameter_le_negative_threshold hp V hregular w k hcneg
  · exact False.elim (cofactorDirection_ne_zero hp V hregular k hczero)
  · have hcne : cofactorDirection hp V k ≠ 0 := ne_of_gt hcpos
    have hmul : t * cofactorDirection hp V k = -w k := by
      unfold lineCoordinate at hk
      linarith
    have hthreshold : t = -w k / cofactorDirection hp V k := by
      exact (eq_div_iff hcne).2 hmul
    left
    apply le_antisymm
    · rw [hthreshold]
      exact positive_threshold_le_lowerParameter hp V hregular w k hcpos
    · exact htIcc.1

/-- Strong classification of an arbitrary positive-ray facet witness.  Its full-simplex embedding
is one of the two classified endpoint points, so both the omitted facet index and the positive mean
are identified with the corresponding endpoint data. -/
theorem facetHasPositiveRayIntersection_endpoint_classification
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsCodimTwoDeviationZero hp V)
    (w₀ : StandardSimplex p)
    (hw₀ : ∀ q : Fin (p - 1), deviation hp (affineValue V w₀) q = 0)
    (k : Fin (p + 1))
    (hfacet : FacetHasPositiveRayIntersection hp V k) :
    (k = lowerEndpointIndex hp V hregular w₀ ∧
        0 < mean hp
          (affineValue V (lowerEndpointSimplexPoint hp V hregular w₀))) ∨
      (k = upperEndpointIndex hp V hregular w₀ ∧
        0 < mean hp
          (affineValue V (upperEndpointSimplexPoint hp V hregular w₀))) := by
  rcases hfacet with ⟨u, hu, hdev, hmean⟩
  let w₁ : StandardSimplex p := fullSimplexOfFacet hp k u
  have hw₁ : ∀ q : Fin (p - 1), deviation hp (affineValue V w₁) q = 0 := by
    intro q
    simpa [w₁] using fullSimplexOfFacet_deviation_eq_zero hp V k u hdev q
  have hw₁mean : 0 < mean hp (affineValue V w₁) := by
    simpa [w₁] using fullSimplexOfFacet_mean_pos hp V k u hmean
  obtain ⟨t, ht, hpoint⟩ :=
    exists_lineSimplexPoint_eq_of_deviation_eq_zero
      hp V hregular w₀ w₁ hw₀ hw₁
  have hkzero : lineCoordinate hp V w₀ t k = 0 := by
    have hcoord : w₁ k = lineCoordinate hp V w₀ t k := by
      simpa [lineSimplexPoint_apply] using
        congrArg (fun z : StandardSimplex p => z k) hpoint
    have hw₁zero : w₁ k = 0 := by
      simpa [w₁] using fullSimplexOfFacet_omitted_eq_zero hp k u
    linarith
  rcases lineParameter_eq_lower_or_upper_of_coordinate_eq_zero
      hp V hregular w₀ t ht k hkzero with htLower | htUpper
  · subst t
    have hkLower : k = lowerEndpointIndex hp V hregular w₀ :=
      lowerEndpoint_unique_zero hp V hregular hcodim w₀ hw₀ k hkzero
    left
    refine ⟨hkLower, ?_⟩
    rw [hpoint] at hw₁mean
    simpa [lowerEndpointSimplexPoint] using hw₁mean
  · subst t
    have hkUpper : k = upperEndpointIndex hp V hregular w₀ :=
      upperEndpoint_unique_zero hp V hregular hcodim w₀ hw₀ k hkzero
    right
    refine ⟨hkUpper, ?_⟩
    rw [hpoint] at hw₁mean
    simpa [upperEndpointSimplexPoint] using hw₁mean

/-- Strong classification of a positive-ray facet under positive-ray-relative
codimension-two avoidance. -/
theorem facetHasPositiveRayIntersection_endpoint_classification_of_positiveCodimTwo
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsPositiveRayCodimTwo hp V)
    (w₀ : StandardSimplex p)
    (hw₀ : ∀ q : Fin (p - 1), deviation hp (affineValue V w₀) q = 0)
    (k : Fin (p + 1))
    (hfacet : FacetHasPositiveRayIntersection hp V k) :
    (k = lowerEndpointIndex hp V hregular w₀ ∧
        0 < mean hp
          (affineValue V (lowerEndpointSimplexPoint hp V hregular w₀))) ∨
      (k = upperEndpointIndex hp V hregular w₀ ∧
        0 < mean hp
          (affineValue V (upperEndpointSimplexPoint hp V hregular w₀))) := by
  rcases hfacet with ⟨u, hu, hdev, hmean⟩
  let w₁ : StandardSimplex p := fullSimplexOfFacet hp k u
  have hw₁ : ∀ q : Fin (p - 1), deviation hp (affineValue V w₁) q = 0 := by
    intro q
    simpa [w₁] using fullSimplexOfFacet_deviation_eq_zero hp V k u hdev q
  have hw₁mean : 0 < mean hp (affineValue V w₁) := by
    simpa [w₁] using fullSimplexOfFacet_mean_pos hp V k u hmean
  obtain ⟨t, ht, hpoint⟩ :=
    exists_lineSimplexPoint_eq_of_deviation_eq_zero
      hp V hregular w₀ w₁ hw₀ hw₁
  have hkzero : lineCoordinate hp V w₀ t k = 0 := by
    have hcoord : w₁ k = lineCoordinate hp V w₀ t k := by
      simpa [lineSimplexPoint_apply] using
        congrArg (fun z : StandardSimplex p => z k) hpoint
    have hw₁zero : w₁ k = 0 := by
      simpa [w₁] using fullSimplexOfFacet_omitted_eq_zero hp k u
    linarith
  rcases lineParameter_eq_lower_or_upper_of_coordinate_eq_zero
      hp V hregular w₀ t ht k hkzero with htLower | htUpper
  · subst t
    have hmeanLower : 0 < mean hp
        (affineValue V (lowerEndpointSimplexPoint hp V hregular w₀)) := by
      rw [hpoint] at hw₁mean
      simpa [lowerEndpointSimplexPoint] using hw₁mean
    have hkLower : k = lowerEndpointIndex hp V hregular w₀ :=
      lowerEndpoint_unique_zero_of_positiveMean hp V hregular hcodim w₀ hw₀
        (by simpa [lowerEndpointSimplexPoint] using hmeanLower) k hkzero
    exact Or.inl ⟨hkLower, hmeanLower⟩
  · subst t
    have hmeanUpper : 0 < mean hp
        (affineValue V (upperEndpointSimplexPoint hp V hregular w₀)) := by
      rw [hpoint] at hw₁mean
      simpa [upperEndpointSimplexPoint] using hw₁mean
    have hkUpper : k = upperEndpointIndex hp V hregular w₀ :=
      upperEndpoint_unique_zero_of_positiveMean hp V hregular hcodim w₀ hw₀
        (by simpa [upperEndpointSimplexPoint] using hmeanUpper) k hkzero
    exact Or.inr ⟨hkUpper, hmeanUpper⟩

/-- Every positive-ray facet is one of the two interval endpoint facets under positive-ray-relative
codimension-two avoidance. -/
theorem facetHasPositiveRayIntersection_imp_eq_lower_or_upper_of_positiveCodimTwo
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsPositiveRayCodimTwo hp V)
    (w₀ : StandardSimplex p)
    (hw₀ : ∀ q : Fin (p - 1), deviation hp (affineValue V w₀) q = 0)
    (k : Fin (p + 1)) :
    FacetHasPositiveRayIntersection hp V k →
      k = lowerEndpointIndex hp V hregular w₀ ∨
        k = upperEndpointIndex hp V hregular w₀ := by
  intro hfacet
  rcases facetHasPositiveRayIntersection_endpoint_classification_of_positiveCodimTwo
      hp V hregular hcodim w₀ hw₀ k hfacet with hLower | hUpper
  · exact Or.inl hLower.1
  · exact Or.inr hUpper.1

/-- If the lower endpoint has positive mean, the positive-ray facets are exactly the lower and
upper endpoints under positive-ray-relative codimension-two avoidance. -/
theorem facetHasPositiveRayIntersection_iff_eq_lower_or_upper_of_positiveCodimTwo
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsPositiveRayCodimTwo hp V)
    (havoid : AvoidsOrigin V)
    (w₀ : StandardSimplex p)
    (hw₀ : ∀ q : Fin (p - 1), deviation hp (affineValue V w₀) q = 0)
    (hlowerMean : 0 < mean hp
      (affineValue V (lowerEndpointSimplexPoint hp V hregular w₀)))
    (k : Fin (p + 1)) :
    FacetHasPositiveRayIntersection hp V k ↔
      k = lowerEndpointIndex hp V hregular w₀ ∨
        k = upperEndpointIndex hp V hregular w₀ := by
  constructor
  · exact facetHasPositiveRayIntersection_imp_eq_lower_or_upper_of_positiveCodimTwo
      hp V hregular hcodim w₀ hw₀ k
  · rintro (rfl | rfl)
    · exact lowerEndpoint_facetHasPositiveRayIntersection_of_positiveCodimTwo
        hp V hregular hcodim w₀ hw₀ hlowerMean
    · have hupperMean : 0 < mean hp
          (affineValue V (upperEndpointSimplexPoint hp V hregular w₀)) :=
        (lowerEndpoint_mean_pos_iff_upperEndpoint_mean_pos
          hp V hregular havoid w₀ hw₀).1 hlowerMean
      exact upperEndpoint_facetHasPositiveRayIntersection_of_positiveCodimTwo
        hp V hregular hcodim w₀ hw₀ hupperMean

/-- Every positive-ray facet is one of the two interval endpoint facets. -/
theorem facetHasPositiveRayIntersection_imp_eq_lower_or_upper
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsCodimTwoDeviationZero hp V)
    (w₀ : StandardSimplex p)
    (hw₀ : ∀ q : Fin (p - 1), deviation hp (affineValue V w₀) q = 0)
    (k : Fin (p + 1)) :
    FacetHasPositiveRayIntersection hp V k →
      k = lowerEndpointIndex hp V hregular w₀ ∨
        k = upperEndpointIndex hp V hregular w₀ := by
  intro hfacet
  rcases facetHasPositiveRayIntersection_endpoint_classification
      hp V hregular hcodim w₀ hw₀ k hfacet with hLower | hUpper
  · exact Or.inl hLower.1
  · exact Or.inr hUpper.1

/-- If the lower endpoint has positive mean, the positive-ray facets are exactly the lower and upper
endpoint facets. -/
theorem facetHasPositiveRayIntersection_iff_eq_lower_or_upper
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsCodimTwoDeviationZero hp V)
    (havoid : AvoidsOrigin V)
    (w₀ : StandardSimplex p)
    (hw₀ : ∀ q : Fin (p - 1), deviation hp (affineValue V w₀) q = 0)
    (hlowerMean : 0 < mean hp
      (affineValue V (lowerEndpointSimplexPoint hp V hregular w₀)))
    (k : Fin (p + 1)) :
    FacetHasPositiveRayIntersection hp V k ↔
      k = lowerEndpointIndex hp V hregular w₀ ∨
        k = upperEndpointIndex hp V hregular w₀ := by
  constructor
  · exact facetHasPositiveRayIntersection_imp_eq_lower_or_upper
      hp V hregular hcodim w₀ hw₀ k
  · rintro (rfl | rfl)
    · exact lowerEndpoint_facetHasPositiveRayIntersection
        hp V hregular hcodim w₀ hw₀ hlowerMean
    · have hupperMean : 0 < mean hp
          (affineValue V (upperEndpointSimplexPoint hp V hregular w₀)) :=
        (lowerEndpoint_mean_pos_iff_upperEndpoint_mean_pos
          hp V hregular havoid w₀ hw₀).1 hlowerMean
      exact upperEndpoint_facetHasPositiveRayIntersection
        hp V hregular hcodim w₀ hw₀ hupperMean

/-- Finite description of the positive-ray boundary of one generic affine prism simplex.
Either the positive ray misses every facet, or it meets exactly two facets with opposite cofactor
orientations. -/
inductive RayBoundaryCertificate
    (hp : Nat.Prime p) (V : VertexMap p) : Type
  | empty
      (no_positive_facet : ∀ k, ¬ FacetHasPositiveRayIntersection hp V k)
  | pair
      (lower upper : Fin (p + 1))
      (lower_ne_upper : lower ≠ upper)
      (lower_positive : 0 < cofactorDirection hp V lower)
      (upper_negative : cofactorDirection hp V upper < 0)
      (positive_facets : ∀ k,
        FacetHasPositiveRayIntersection hp V k ↔ k = lower ∨ k = upper)

/-- The alternating determinant sign is the sign of the cofactor direction. -/
theorem faceSign_mul_determinantIndex_eq_directionIndex
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1)) :
    (-1 : ZMod p) ^ k.1 *
        FoxNeuwirthOrderComplex.AffineVertexMap.determinantIndex
          (facetDeterminant hp V k) =
      FoxNeuwirthOrderComplex.AffineVertexMap.determinantIndex
        (cofactorDirection hp V k) := by
  classical
  rcases Nat.even_or_odd k.1 with heven | hodd
  · have hpowR : ((-1 : Real) ^ k.1) = 1 := Even.neg_one_pow heven
    have hpowZ : ((-1 : ZMod p) ^ k.1) = 1 := Even.neg_one_pow heven
    rcases lt_trichotomy (facetDeterminant hp V k) 0 with hneg | hzero | hpos
    · simp [FoxNeuwirthOrderComplex.SimplicialChain.faceSign, cofactorDirection,
        FoxNeuwirthOrderComplex.AffineVertexMap.determinantIndex,
        hpowR, hpowZ, hneg]
    · simp [FoxNeuwirthOrderComplex.SimplicialChain.faceSign, cofactorDirection,
        FoxNeuwirthOrderComplex.AffineVertexMap.determinantIndex,
        hpowR, hpowZ, hzero]
    · simp [FoxNeuwirthOrderComplex.SimplicialChain.faceSign, cofactorDirection,
        FoxNeuwirthOrderComplex.AffineVertexMap.determinantIndex,
        hpowR, hpowZ, hpos]
  · have hpowR : ((-1 : Real) ^ k.1) = -1 := Odd.neg_one_pow hodd
    have hpowZ : ((-1 : ZMod p) ^ k.1) = -1 := Odd.neg_one_pow hodd
    rcases lt_trichotomy (facetDeterminant hp V k) 0 with hneg | hzero | hpos
    · have hprod : 0 < (-1 : Real) * facetDeterminant hp V k := by linarith
      have hnpos : ¬ 0 < facetDeterminant hp V k := by linarith
      simp [cofactorDirection,
        FoxNeuwirthOrderComplex.AffineVertexMap.determinantIndex,
        hpowR, hpowZ, hneg, hprod, hnpos]
    · simp [FoxNeuwirthOrderComplex.SimplicialChain.faceSign, cofactorDirection,
        FoxNeuwirthOrderComplex.AffineVertexMap.determinantIndex,
        hpowR, hpowZ, hzero]
    · have hprod : (-1 : Real) * facetDeterminant hp V k < 0 := by linarith
      have hnneg : ¬ facetDeterminant hp V k < 0 := by linarith
      simp [cofactorDirection,
        FoxNeuwirthOrderComplex.AffineVertexMap.determinantIndex,
        hpowR, hpowZ, hpos, hprod, hnneg]

/-- The exact local line-geometry statement needed for the prism argument.  It says that facet
regularity and origin avoidance produce the two signed boundary points of the positive-ray
preimage.  The construction is finite-dimensional: write the deviation-zero affine line using
signed maximal minors, intersect it with the barycentric simplex, and use origin avoidance to keep
the mean sign constant. -/
def RayBoundaryTheorem : Prop :=
  ∀ {p : Nat} (hp : Nat.Prime p) (V : VertexMap p),
    GeneralPosition hp V → Nonempty (RayBoundaryCertificate hp V)

/-- Construct the finite positive-ray boundary certificate from the local general-position
hypotheses.  If the deviation-zero line misses the simplex, or if its constant nonzero mean is
negative, no facet meets the open positive ray.  Otherwise the lower and upper feasible endpoints
are exactly the two positive-ray facets and have opposite cofactor signs. -/
noncomputable def rayBoundaryCertificate
    (hp : Nat.Prime p) (V : VertexMap p)
    (hgp : GeneralPosition hp V) : RayBoundaryCertificate hp V := by
  classical
  by_cases hzero : ∃ w : StandardSimplex p,
      ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0
  · let w₀ : StandardSimplex p := Classical.choose hzero
    have hw₀ : ∀ q : Fin (p - 1),
        deviation hp (affineValue V w₀) q = 0 := Classical.choose_spec hzero
    by_cases hlowerMean : 0 < mean hp
        (affineValue V (lowerEndpointSimplexPoint hp V hgp.facetRegular w₀))
    · exact RayBoundaryCertificate.pair
        (lowerEndpointIndex hp V hgp.facetRegular w₀)
        (upperEndpointIndex hp V hgp.facetRegular w₀)
        (lowerEndpointIndex_ne_upperEndpointIndex hp V hgp.facetRegular w₀)
        (lowerEndpointIndex_pos hp V hgp.facetRegular w₀)
        (upperEndpointIndex_neg hp V hgp.facetRegular w₀)
        (facetHasPositiveRayIntersection_iff_eq_lower_or_upper
          hp V hgp.facetRegular hgp.avoidsCodimTwo hgp.avoidsOrigin
          w₀ hw₀ hlowerMean)
    · exact RayBoundaryCertificate.empty (fun k hfacet => by
        rcases facetHasPositiveRayIntersection_endpoint_classification
            hp V hgp.facetRegular hgp.avoidsCodimTwo w₀ hw₀ k hfacet with
          hLower | hUpper
        · exact hlowerMean hLower.2
        · have hlowerMean' : 0 < mean hp
              (affineValue V
                (lowerEndpointSimplexPoint hp V hgp.facetRegular w₀)) :=
            (lowerEndpoint_mean_pos_iff_upperEndpoint_mean_pos
              hp V hgp.facetRegular hgp.avoidsOrigin w₀ hw₀).2 hUpper.2
          exact hlowerMean hlowerMean')
  · exact RayBoundaryCertificate.empty (fun k hfacet => by
      rcases hfacet with ⟨u, huInterior, huDeviation, huMean⟩
      apply hzero
      exact ⟨fullSimplexOfFacet hp k u,
        fullSimplexOfFacet_deviation_eq_zero hp V k u huDeviation⟩)

/-- Construct the finite positive-ray boundary certificate from the weaker
positive-ray-relative general-position hypotheses. -/
noncomputable def rayBoundaryCertificateOfPositiveRayGeneralPosition
    (hp : Nat.Prime p) (V : VertexMap p)
    (hgp : PositiveRayGeneralPosition hp V) : RayBoundaryCertificate hp V := by
  classical
  by_cases hzero : ∃ w : StandardSimplex p,
      ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0
  · let w₀ : StandardSimplex p := Classical.choose hzero
    have hw₀ : ∀ q : Fin (p - 1),
        deviation hp (affineValue V w₀) q = 0 := Classical.choose_spec hzero
    by_cases hlowerMean : 0 < mean hp
        (affineValue V (lowerEndpointSimplexPoint hp V hgp.facetRegular w₀))
    · exact RayBoundaryCertificate.pair
        (lowerEndpointIndex hp V hgp.facetRegular w₀)
        (upperEndpointIndex hp V hgp.facetRegular w₀)
        (lowerEndpointIndex_ne_upperEndpointIndex hp V hgp.facetRegular w₀)
        (lowerEndpointIndex_pos hp V hgp.facetRegular w₀)
        (upperEndpointIndex_neg hp V hgp.facetRegular w₀)
        (facetHasPositiveRayIntersection_iff_eq_lower_or_upper_of_positiveCodimTwo
          hp V hgp.facetRegular hgp.avoidsPositiveRayCodimTwo hgp.avoidsOrigin
          w₀ hw₀ hlowerMean)
    · exact RayBoundaryCertificate.empty (fun k hfacet => by
        rcases
            facetHasPositiveRayIntersection_endpoint_classification_of_positiveCodimTwo
              hp V hgp.facetRegular hgp.avoidsPositiveRayCodimTwo
              w₀ hw₀ k hfacet with
          hLower | hUpper
        · exact hlowerMean hLower.2
        · have hlowerMean' : 0 < mean hp
              (affineValue V
                (lowerEndpointSimplexPoint hp V hgp.facetRegular w₀)) :=
            (lowerEndpoint_mean_pos_iff_upperEndpoint_mean_pos
              hp V hgp.facetRegular hgp.avoidsOrigin w₀ hw₀).2 hUpper.2
          exact hlowerMean hlowerMean')
  · exact RayBoundaryCertificate.empty (fun k hfacet => by
      rcases hfacet with ⟨u, huInterior, huDeviation, huMean⟩
      apply hzero
      exact ⟨fullSimplexOfFacet hp k u,
        fullSimplexOfFacet_deviation_eq_zero hp V k u huDeviation⟩)

/-- The local affine positive-ray boundary theorem. -/
theorem rayBoundaryTheorem : RayBoundaryTheorem := by
  intro p hp V hgp
  exact ⟨rayBoundaryCertificate hp V hgp⟩

/-- Local affine Stokes theorem from the explicit boundary certificate. -/
theorem alternating_facetIndex_sum_eq_zero_of_certificate
    (hp : Nat.Prime p) (V : VertexMap p)
    (C : RayBoundaryCertificate hp V) :
    ∑ k : Fin (p + 1), facetIndex hp V k = 0 := by
  classical
  cases C with
  | empty hnone =>
      apply Finset.sum_eq_zero
      intro k hk
      rw [facetIndex, if_neg (hnone k)]
  | pair lower upper hne hlower hupper hfacets =>
      have hlow : facetIndex hp V lower = 1 := by
        rw [facetIndex, if_pos ((hfacets lower).2 (Or.inl rfl))]
        rw [faceSign_mul_determinantIndex_eq_directionIndex]
        simp [FoxNeuwirthOrderComplex.AffineVertexMap.determinantIndex, hlower]
      have hupp : facetIndex hp V upper = -1 := by
        rw [facetIndex, if_pos ((hfacets upper).2 (Or.inr rfl))]
        rw [faceSign_mul_determinantIndex_eq_directionIndex]
        have hnpos : ¬ 0 < cofactorDirection hp V upper := by linarith
        simp [FoxNeuwirthOrderComplex.AffineVertexMap.determinantIndex, hupper, hnpos]
      have hother : ∀ k, k ≠ lower → k ≠ upper → facetIndex hp V k = 0 := by
        intro k hkl hku
        rw [facetIndex, if_neg]
        intro hk
        rcases (hfacets k).1 hk with hk | hk
        · exact hkl hk
        · exact hku hk
      calc
        ∑ k : Fin (p + 1), facetIndex hp V k =
            (∑ k ∈ (Finset.univ.erase lower), facetIndex hp V k) +
              facetIndex hp V lower := by
                exact (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ lower)).symm
        _ = facetIndex hp V lower +
              ∑ k ∈ (Finset.univ.erase lower), facetIndex hp V k := by ac_rfl
        _ = facetIndex hp V lower +
              ((∑ k ∈ ((Finset.univ.erase lower).erase upper), facetIndex hp V k) +
                facetIndex hp V upper) := by
                rw [Finset.sum_erase_add]
                simpa [hne.symm]
        _ = facetIndex hp V lower + facetIndex hp V upper +
              ∑ k ∈ ((Finset.univ.erase lower).erase upper), facetIndex hp V k := by ac_rfl
        _ = 1 + (-1) + 0 := by
              rw [hlow, hupp]
              congr 1
              apply Finset.sum_eq_zero
              intro k hk
              have hk' : k ≠ upper ∧ k ≠ lower := by simpa using hk
              exact hother k hk'.2 hk'.1
        _ = 0 := by ring

/-- Unconditional local affine Stokes under positive-ray-relative general position. -/
theorem alternating_facetIndex_sum_eq_zero_of_positiveRayGeneralPosition
    (hp : Nat.Prime p) (V : VertexMap p)
    (hgp : PositiveRayGeneralPosition hp V) :
    ∑ k : Fin (p + 1), facetIndex hp V k = 0 :=
  alternating_facetIndex_sum_eq_zero_of_certificate hp V
    (rayBoundaryCertificateOfPositiveRayGeneralPosition hp V hgp)

/-- Local affine Stokes, reduced to the finite line-geometry theorem. -/
theorem alternating_facetIndex_sum_eq_zero
    (Hline : RayBoundaryTheorem)
    (hp : Nat.Prime p) (V : VertexMap p)
    (hgp : GeneralPosition hp V) :
    ∑ k : Fin (p + 1), facetIndex hp V k = 0 :=
  alternating_facetIndex_sum_eq_zero_of_certificate hp V
    (Classical.choice (Hline hp V hgp))

/-- Unconditional local affine Stokes theorem under the general-position hypotheses. -/
theorem alternating_facetIndex_sum_eq_zero_of_generalPosition
    (hp : Nat.Prime p) (V : VertexMap p)
    (hgp : GeneralPosition hp V) :
    ∑ k : Fin (p + 1), facetIndex hp V k = 0 :=
  alternating_facetIndex_sum_eq_zero rayBoundaryTheorem hp V hgp

end VertexMap
end AffinePositiveRayBoundary
end NRR

/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.AffineNormalization
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Localized transition maps for the weighted trace-cover charts

The four standard charts of the biprojective trace cover have two affine coordinate rings,
corresponding to the weight orders `(alpha, beta)` and `(beta, alpha)`.  This file localizes each
ring away from the coordinate axes and constructs the actual algebra isomorphisms induced by
`x ↦ x⁻¹` and `y ↦ y⁻¹`.

These are coordinate-ring isomorphisms, not merely equivalences of torus-valued points.  The next
geometric wall is to identify these localizations with overlap opens in the affine normalizations
and use the maps in a scheme-gluing datum.
-/

@[expose] public section

namespace BGS.Markoff

noncomputable section

variable {K : Type*} [Field K]

def weightedSplitTraceAffineX (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceAffineCoordinateRing alpha beta d e :=
  Ideal.Quotient.mk _ (MvPolynomial.X 0)

def weightedSplitTraceAffineY (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceAffineCoordinateRing alpha beta d e :=
  Ideal.Quotient.mk _ (MvPolynomial.X 1)

def weightedSplitTraceAffineCoordinateProduct (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceAffineCoordinateRing alpha beta d e :=
  weightedSplitTraceAffineX alpha beta d e * weightedSplitTraceAffineY alpha beta d e

abbrev WeightedSplitTraceLaurentCoordinateRing (alpha beta : K) (d e : ℕ) :=
  Localization.Away (weightedSplitTraceAffineCoordinateProduct alpha beta d e)

def weightedSplitTraceLaurentX (alpha beta : K) (d e : ℕ) : WeightedSplitTraceLaurentCoordinateRing alpha beta d e :=
  algebraMap _ _ (weightedSplitTraceAffineX alpha beta d e)

def weightedSplitTraceLaurentY (alpha beta : K) (d e : ℕ) : WeightedSplitTraceLaurentCoordinateRing alpha beta d e :=
  algebraMap _ _ (weightedSplitTraceAffineY alpha beta d e)

theorem weightedSplitTraceLaurentCoordinateProduct_isUnit (alpha beta : K) (d e : ℕ) :
    IsUnit (weightedSplitTraceLaurentX alpha beta d e * weightedSplitTraceLaurentY alpha beta d e) := by
  simpa only [weightedSplitTraceLaurentX, weightedSplitTraceLaurentY, weightedSplitTraceAffineCoordinateProduct, map_mul] using
    (IsLocalization.Away.algebraMap_isUnit
      (S := WeightedSplitTraceLaurentCoordinateRing alpha beta d e) (weightedSplitTraceAffineCoordinateProduct alpha beta d e))

theorem weightedSplitTraceLaurentX_isUnit (alpha beta : K) (d e : ℕ) :
    IsUnit (weightedSplitTraceLaurentX alpha beta d e) :=
  ((Commute.all _ _).isUnit_mul_iff.mp
    (weightedSplitTraceLaurentCoordinateProduct_isUnit alpha beta d e)).1

theorem weightedSplitTraceLaurentY_isUnit (alpha beta : K) (d e : ℕ) :
    IsUnit (weightedSplitTraceLaurentY alpha beta d e) :=
  ((Commute.all _ _).isUnit_mul_iff.mp
    (weightedSplitTraceLaurentCoordinateProduct_isUnit alpha beta d e)).2

def weightedSplitTraceLaurentXUnit (alpha beta : K) (d e : ℕ) :
    (WeightedSplitTraceLaurentCoordinateRing alpha beta d e)ˣ :=
  (weightedSplitTraceLaurentX_isUnit alpha beta d e).unit

def weightedSplitTraceLaurentYUnit (alpha beta : K) (d e : ℕ) :
    (WeightedSplitTraceLaurentCoordinateRing alpha beta d e)ˣ :=
  (weightedSplitTraceLaurentY_isUnit alpha beta d e).unit

@[simp]
theorem weightedSplitTraceLaurentXUnit_val (alpha beta : K) (d e : ℕ) :
    (weightedSplitTraceLaurentXUnit alpha beta d e : WeightedSplitTraceLaurentCoordinateRing alpha beta d e) =
      weightedSplitTraceLaurentX alpha beta d e :=
  (weightedSplitTraceLaurentX_isUnit alpha beta d e).unit_spec

@[simp]
theorem weightedSplitTraceLaurentYUnit_val (alpha beta : K) (d e : ℕ) :
    (weightedSplitTraceLaurentYUnit alpha beta d e : WeightedSplitTraceLaurentCoordinateRing alpha beta d e) =
      weightedSplitTraceLaurentY alpha beta d e :=
  (weightedSplitTraceLaurentY_isUnit alpha beta d e).unit_spec

def weightedSplitTraceLaurentXInverse (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceLaurentCoordinateRing alpha beta d e :=
  ↑(weightedSplitTraceLaurentXUnit alpha beta d e)⁻¹

def weightedSplitTraceLaurentYInverse (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceLaurentCoordinateRing alpha beta d e :=
  ↑(weightedSplitTraceLaurentYUnit alpha beta d e)⁻¹

theorem weightedSplitTraceAffineDefiningRelation (alpha beta : K) (d e : ℕ) :
    Ideal.Quotient.mk (Ideal.span {splitTraceCoverPolynomial alpha beta d e})
        (splitTraceCoverPolynomial alpha beta d e) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

theorem weightedSplitTraceLaurentDefiningRelation (alpha beta : K) (d e : ℕ) :
    algebraMap K (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) alpha *
          weightedSplitTraceLaurentX alpha beta d e ^ d * weightedSplitTraceLaurentY alpha beta d e ^ (2 * e) +
        algebraMap K (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) beta *
          weightedSplitTraceLaurentX alpha beta d e ^ d -
        weightedSplitTraceLaurentX alpha beta d e ^ (2 * d) * weightedSplitTraceLaurentY alpha beta d e ^ e -
        weightedSplitTraceLaurentY alpha beta d e ^ e = 0 := by
  let ev : MvPolynomial (Fin 2) K →+* WeightedSplitTraceLaurentCoordinateRing alpha beta d e :=
    MvPolynomial.eval₂Hom (algebraMap K (WeightedSplitTraceLaurentCoordinateRing alpha beta d e))
      ![weightedSplitTraceLaurentX alpha beta d e, weightedSplitTraceLaurentY alpha beta d e]
  have hev : ev =
      (algebraMap (WeightedSplitTraceAffineCoordinateRing alpha beta d e)
        (WeightedSplitTraceLaurentCoordinateRing alpha beta d e)).comp
        (Ideal.Quotient.mk (Ideal.span {splitTraceCoverPolynomial alpha beta d e})) := by
    ext a
    · simp only [RingHom.comp_apply, ev, MvPolynomial.eval₂Hom_C]
      exact IsScalarTower.algebraMap_apply K
        (WeightedSplitTraceAffineCoordinateRing alpha beta d e)
        (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) a
    · fin_cases a <;>
        simp [RingHom.comp_apply, ev, weightedSplitTraceLaurentX, weightedSplitTraceLaurentY, weightedSplitTraceAffineX, weightedSplitTraceAffineY]
  have hp : ev (splitTraceCoverPolynomial alpha beta d e) = 0 := by
    rw [hev]
    simpa only [RingHom.comp_apply, map_zero] using congrArg
      (algebraMap (WeightedSplitTraceAffineCoordinateRing alpha beta d e)
        (WeightedSplitTraceLaurentCoordinateRing alpha beta d e))
      (weightedSplitTraceAffineDefiningRelation alpha beta d e)
  simpa [ev, splitTraceCoverPolynomial] using hp

theorem weightedSplitTraceLeftInverseDefiningRelation (alpha beta : K) (d e : ℕ) :
    algebraMap K (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) alpha *
          weightedSplitTraceLaurentXInverse alpha beta d e ^ d *
          weightedSplitTraceLaurentY alpha beta d e ^ (2 * e) +
        algebraMap K (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) beta *
          weightedSplitTraceLaurentXInverse alpha beta d e ^ d -
        weightedSplitTraceLaurentXInverse alpha beta d e ^ (2 * d) *
          weightedSplitTraceLaurentY alpha beta d e ^ e -
        weightedSplitTraceLaurentY alpha beta d e ^ e = 0 := by
  let u := weightedSplitTraceLaurentXUnit alpha beta d e
  have hcancel :
      ((↑(u⁻¹) : WeightedSplitTraceLaurentCoordinateRing alpha beta d e) ^ (2 * d)) *
          ((↑u : WeightedSplitTraceLaurentCoordinateRing alpha beta d e) ^ d) =
        (↑(u⁻¹) : WeightedSplitTraceLaurentCoordinateRing alpha beta d e) ^ d := by
    norm_cast
    simp [two_mul, pow_add]
  have hcancelTwo :
      ((↑(u⁻¹) : WeightedSplitTraceLaurentCoordinateRing alpha beta d e) ^ (2 * d)) *
          ((↑u : WeightedSplitTraceLaurentCoordinateRing alpha beta d e) ^ (2 * d)) = 1 := by
    norm_cast
    simp
  dsimp [u] at hcancel hcancelTwo
  calc
    algebraMap K (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) alpha *
            weightedSplitTraceLaurentXInverse alpha beta d e ^ d *
            weightedSplitTraceLaurentY alpha beta d e ^ (2 * e) +
          algebraMap K (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) beta *
            weightedSplitTraceLaurentXInverse alpha beta d e ^ d -
          weightedSplitTraceLaurentXInverse alpha beta d e ^ (2 * d) *
            weightedSplitTraceLaurentY alpha beta d e ^ e -
          weightedSplitTraceLaurentY alpha beta d e ^ e =
        weightedSplitTraceLaurentXInverse alpha beta d e ^ (2 * d) *
          (algebraMap K (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) alpha *
              weightedSplitTraceLaurentX alpha beta d e ^ d *
                weightedSplitTraceLaurentY alpha beta d e ^ (2 * e) +
            algebraMap K (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) beta *
              weightedSplitTraceLaurentX alpha beta d e ^ d -
            weightedSplitTraceLaurentX alpha beta d e ^ (2 * d) *
              weightedSplitTraceLaurentY alpha beta d e ^ e -
            weightedSplitTraceLaurentY alpha beta d e ^ e) := by
          dsimp [weightedSplitTraceLaurentXInverse]
          rw [← weightedSplitTraceLaurentXUnit_val]
          linear_combination
            -(algebraMap K (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) alpha *
                weightedSplitTraceLaurentY alpha beta d e ^ (2 * e)) * hcancel -
              algebraMap K (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) beta * hcancel +
              weightedSplitTraceLaurentY alpha beta d e ^ e * hcancelTwo
    _ = 0 := by rw [weightedSplitTraceLaurentDefiningRelation, mul_zero]

def weightedSplitTraceLeftInversionPolynomialMap (alpha beta : K) (d e : ℕ) :
    MvPolynomial (Fin 2) K →ₐ[K] WeightedSplitTraceLaurentCoordinateRing alpha beta d e :=
  MvPolynomial.aeval
    ![weightedSplitTraceLaurentXInverse alpha beta d e, weightedSplitTraceLaurentY alpha beta d e]

theorem weightedSplitTraceLeftInversionPolynomialMap_relation (alpha beta : K) (d e : ℕ) :
    weightedSplitTraceLeftInversionPolynomialMap alpha beta d e
      (splitTraceCoverPolynomial alpha beta d e) = 0 := by
  simpa [weightedSplitTraceLeftInversionPolynomialMap, MvPolynomial.aeval_def, splitTraceCoverPolynomial] using
    weightedSplitTraceLeftInverseDefiningRelation alpha beta d e

def weightedSplitTraceLeftInversionAffineMap (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceAffineCoordinateRing alpha beta d e →ₐ[K]
      WeightedSplitTraceLaurentCoordinateRing alpha beta d e := by
  refine Ideal.Quotient.liftₐ
    (Ideal.span {splitTraceCoverPolynomial alpha beta d e})
    (weightedSplitTraceLeftInversionPolynomialMap alpha beta d e) ?_
  intro p hp
  have hle : Ideal.span {splitTraceCoverPolynomial alpha beta d e} ≤
      RingHom.ker (weightedSplitTraceLeftInversionPolynomialMap alpha beta d e).toRingHom := by
    rw [Ideal.span_le]
    intro q hq
    simp only [Set.mem_singleton_iff] at hq
    subst q
    exact weightedSplitTraceLeftInversionPolynomialMap_relation alpha beta d e
  exact hle hp

@[simp]
theorem weightedSplitTraceLeftInversionAffineMap_x (alpha beta : K) (d e : ℕ) :
    weightedSplitTraceLeftInversionAffineMap alpha beta d e (weightedSplitTraceAffineX alpha beta d e) =
      weightedSplitTraceLaurentXInverse alpha beta d e := by
  change MvPolynomial.aeval
    ![weightedSplitTraceLaurentXInverse alpha beta d e,
      weightedSplitTraceLaurentY alpha beta d e] (MvPolynomial.X 0) = _
  simp

@[simp]
theorem weightedSplitTraceLeftInversionAffineMap_y (alpha beta : K) (d e : ℕ) :
    weightedSplitTraceLeftInversionAffineMap alpha beta d e (weightedSplitTraceAffineY alpha beta d e) =
      weightedSplitTraceLaurentY alpha beta d e := by
  change MvPolynomial.aeval
    ![weightedSplitTraceLaurentXInverse alpha beta d e,
      weightedSplitTraceLaurentY alpha beta d e] (MvPolynomial.X 1) = _
  simp

theorem weightedSplitTraceLeftInversionAffineMap_coordinateProduct_isUnit (alpha beta : K) (d e : ℕ) :
    IsUnit (weightedSplitTraceLeftInversionAffineMap alpha beta d e (weightedSplitTraceAffineCoordinateProduct alpha beta d e)) := by
  simpa [weightedSplitTraceAffineCoordinateProduct, weightedSplitTraceLaurentXInverse] using
    (Units.isUnit (weightedSplitTraceLaurentXUnit alpha beta d e)⁻¹).mul
      (weightedSplitTraceLaurentY_isUnit alpha beta d e)

def weightedSplitTraceLeftInversionLaurentMap (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceLaurentCoordinateRing alpha beta d e →ₐ[K] WeightedSplitTraceLaurentCoordinateRing alpha beta d e :=
  IsLocalization.Away.liftAlgHom (weightedSplitTraceAffineCoordinateProduct alpha beta d e)
    (weightedSplitTraceLeftInversionAffineMap_coordinateProduct_isUnit alpha beta d e)

@[simp]
theorem weightedSplitTraceLeftInversionLaurentMap_x (alpha beta : K) (d e : ℕ) :
    weightedSplitTraceLeftInversionLaurentMap alpha beta d e (weightedSplitTraceLaurentX alpha beta d e) =
      weightedSplitTraceLaurentXInverse alpha beta d e := by
  simp only [weightedSplitTraceLeftInversionLaurentMap, weightedSplitTraceLaurentX, IsLocalization.Away.liftAlgHom_apply]
  rw [IsLocalization.Away.lift_eq]
  exact weightedSplitTraceLeftInversionAffineMap_x alpha beta d e

@[simp]
theorem weightedSplitTraceLeftInversionLaurentMap_y (alpha beta : K) (d e : ℕ) :
    weightedSplitTraceLeftInversionLaurentMap alpha beta d e (weightedSplitTraceLaurentY alpha beta d e) =
      weightedSplitTraceLaurentY alpha beta d e := by
  simp only [weightedSplitTraceLeftInversionLaurentMap, weightedSplitTraceLaurentY, IsLocalization.Away.liftAlgHom_apply]
  rw [IsLocalization.Away.lift_eq]
  exact weightedSplitTraceLeftInversionAffineMap_y alpha beta d e

@[simp]
theorem weightedSplitTraceLeftInversionLaurentMap_xInverse (alpha beta : K) (d e : ℕ) :
    weightedSplitTraceLeftInversionLaurentMap alpha beta d e (weightedSplitTraceLaurentXInverse alpha beta d e) =
      weightedSplitTraceLaurentX alpha beta d e := by
  let u := weightedSplitTraceLaurentXUnit alpha beta d e
  let f := weightedSplitTraceLeftInversionLaurentMap alpha beta d e
  have hu : Units.map f.toMonoidHom u = u⁻¹ := by
    ext
    simp [f, u, weightedSplitTraceLaurentXInverse]
  change f (↑(u⁻¹) : WeightedSplitTraceLaurentCoordinateRing alpha beta d e) =
    (↑u : WeightedSplitTraceLaurentCoordinateRing alpha beta d e)
  calc
    f (↑(u⁻¹) : WeightedSplitTraceLaurentCoordinateRing alpha beta d e) =
        ↑(Units.map f.toMonoidHom (u⁻¹)) :=
          (Units.coe_map f.toMonoidHom (u⁻¹)).symm
    _ = ↑((Units.map f.toMonoidHom u)⁻¹) := by rw [map_inv]
    _ = ↑((u⁻¹)⁻¹) := by rw [hu]
    _ = (↑u : WeightedSplitTraceLaurentCoordinateRing alpha beta d e) := by simp

@[simp]
theorem weightedSplitTraceLeftInversionLaurentMap_yInverse
    (alpha beta : K) (d e : ℕ) :
    weightedSplitTraceLeftInversionLaurentMap alpha beta d e
        (weightedSplitTraceLaurentYInverse alpha beta d e) =
      weightedSplitTraceLaurentYInverse alpha beta d e := by
  let u := weightedSplitTraceLaurentYUnit alpha beta d e
  let f := weightedSplitTraceLeftInversionLaurentMap alpha beta d e
  have hu : Units.map f.toMonoidHom u = u := by
    ext
    simp [f, u]
  change f (↑(u⁻¹) : WeightedSplitTraceLaurentCoordinateRing alpha beta d e) =
    (↑(u⁻¹) : WeightedSplitTraceLaurentCoordinateRing alpha beta d e)
  calc
    f (↑(u⁻¹) : WeightedSplitTraceLaurentCoordinateRing alpha beta d e) =
        ↑(Units.map f.toMonoidHom (u⁻¹)) :=
          (Units.coe_map f.toMonoidHom (u⁻¹)).symm
    _ = ↑((Units.map f.toMonoidHom u)⁻¹) := by rw [map_inv]
    _ = (↑(u⁻¹) : WeightedSplitTraceLaurentCoordinateRing alpha beta d e) := by rw [hu]

theorem weightedSplitTraceLeftInversionLaurentMap_involutive (alpha beta : K) (d e : ℕ) :
    (weightedSplitTraceLeftInversionLaurentMap alpha beta d e).comp
        (weightedSplitTraceLeftInversionLaurentMap alpha beta d e) =
      AlgHom.id K (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (weightedSplitTraceAffineCoordinateProduct alpha beta d e))
  apply Ideal.Quotient.algHom_ext K
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change weightedSplitTraceLeftInversionLaurentMap alpha beta d e
        (weightedSplitTraceLeftInversionLaurentMap alpha beta d e (weightedSplitTraceLaurentX alpha beta d e)) =
      weightedSplitTraceLaurentX alpha beta d e
    rw [weightedSplitTraceLeftInversionLaurentMap_x, weightedSplitTraceLeftInversionLaurentMap_xInverse]
  · change weightedSplitTraceLeftInversionLaurentMap alpha beta d e
        (weightedSplitTraceLeftInversionLaurentMap alpha beta d e (weightedSplitTraceLaurentY alpha beta d e)) =
      weightedSplitTraceLaurentY alpha beta d e
    rw [weightedSplitTraceLeftInversionLaurentMap_y, weightedSplitTraceLeftInversionLaurentMap_y]

def weightedSplitTraceLeftInversionLaurentEquiv (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceLaurentCoordinateRing alpha beta d e ≃ₐ[K] WeightedSplitTraceLaurentCoordinateRing alpha beta d e :=
  AlgEquiv.ofAlgHom (weightedSplitTraceLeftInversionLaurentMap alpha beta d e)
    (weightedSplitTraceLeftInversionLaurentMap alpha beta d e)
    (weightedSplitTraceLeftInversionLaurentMap_involutive alpha beta d e)
    (weightedSplitTraceLeftInversionLaurentMap_involutive alpha beta d e)

/-! ### The weight-swapping second-coordinate transition -/

/-- Substituting `y⁻¹` changes the defining equation with weights `(alpha, beta)` into the
defining equation with weights `(beta, alpha)`. -/
theorem weightedSplitTraceRightInverseDefiningRelation
    (alpha beta : K) (d e : ℕ) :
    algebraMap K (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) beta *
          weightedSplitTraceLaurentX alpha beta d e ^ d *
          weightedSplitTraceLaurentYInverse alpha beta d e ^ (2 * e) +
        algebraMap K (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) alpha *
          weightedSplitTraceLaurentX alpha beta d e ^ d -
        weightedSplitTraceLaurentX alpha beta d e ^ (2 * d) *
          weightedSplitTraceLaurentYInverse alpha beta d e ^ e -
        weightedSplitTraceLaurentYInverse alpha beta d e ^ e = 0 := by
  let u := weightedSplitTraceLaurentYUnit alpha beta d e
  have hcancel :
      ((↑(u⁻¹) : WeightedSplitTraceLaurentCoordinateRing alpha beta d e) ^ (2 * e)) *
          ((↑u : WeightedSplitTraceLaurentCoordinateRing alpha beta d e) ^ e) =
        (↑(u⁻¹) : WeightedSplitTraceLaurentCoordinateRing alpha beta d e) ^ e := by
    norm_cast
    simp [two_mul, pow_add]
  have hcancelTwo :
      ((↑(u⁻¹) : WeightedSplitTraceLaurentCoordinateRing alpha beta d e) ^ (2 * e)) *
          ((↑u : WeightedSplitTraceLaurentCoordinateRing alpha beta d e) ^ (2 * e)) = 1 := by
    norm_cast
    simp
  dsimp [u] at hcancel hcancelTwo
  calc
    algebraMap K (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) beta *
            weightedSplitTraceLaurentX alpha beta d e ^ d *
            weightedSplitTraceLaurentYInverse alpha beta d e ^ (2 * e) +
          algebraMap K (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) alpha *
            weightedSplitTraceLaurentX alpha beta d e ^ d -
          weightedSplitTraceLaurentX alpha beta d e ^ (2 * d) *
            weightedSplitTraceLaurentYInverse alpha beta d e ^ e -
          weightedSplitTraceLaurentYInverse alpha beta d e ^ e =
        weightedSplitTraceLaurentYInverse alpha beta d e ^ (2 * e) *
          (algebraMap K (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) alpha *
              weightedSplitTraceLaurentX alpha beta d e ^ d *
                weightedSplitTraceLaurentY alpha beta d e ^ (2 * e) +
            algebraMap K (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) beta *
              weightedSplitTraceLaurentX alpha beta d e ^ d -
            weightedSplitTraceLaurentX alpha beta d e ^ (2 * d) *
              weightedSplitTraceLaurentY alpha beta d e ^ e -
            weightedSplitTraceLaurentY alpha beta d e ^ e) := by
          dsimp [weightedSplitTraceLaurentYInverse]
          rw [← weightedSplitTraceLaurentYUnit_val]
          linear_combination
            (weightedSplitTraceLaurentX alpha beta d e ^ (2 * d) + 1) * hcancel -
              (algebraMap K (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) alpha *
                weightedSplitTraceLaurentX alpha beta d e ^ d) * hcancelTwo
    _ = 0 := by rw [weightedSplitTraceLaurentDefiningRelation, mul_zero]

/-- Polynomial substitution defining the second-coordinate transition from the swapped chart. -/
def weightedSplitTraceRightInversionPolynomialMap (alpha beta : K) (d e : ℕ) :
    MvPolynomial (Fin 2) K →ₐ[K]
      WeightedSplitTraceLaurentCoordinateRing alpha beta d e :=
  MvPolynomial.aeval
    ![weightedSplitTraceLaurentX alpha beta d e,
      weightedSplitTraceLaurentYInverse alpha beta d e]

theorem weightedSplitTraceRightInversionPolynomialMap_relation
    (alpha beta : K) (d e : ℕ) :
    weightedSplitTraceRightInversionPolynomialMap alpha beta d e
      (splitTraceCoverPolynomial beta alpha d e) = 0 := by
  simpa [weightedSplitTraceRightInversionPolynomialMap, MvPolynomial.aeval_def,
    splitTraceCoverPolynomial] using
    weightedSplitTraceRightInverseDefiningRelation alpha beta d e

/-- The swapped affine chart maps to the original Laurent chart by `x ↦ x`, `y ↦ y⁻¹`. -/
def weightedSplitTraceRightInversionAffineMap (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceAffineCoordinateRing beta alpha d e →ₐ[K]
      WeightedSplitTraceLaurentCoordinateRing alpha beta d e := by
  refine Ideal.Quotient.liftₐ
    (Ideal.span {splitTraceCoverPolynomial beta alpha d e})
    (weightedSplitTraceRightInversionPolynomialMap alpha beta d e) ?_
  intro p hp
  have hle : Ideal.span {splitTraceCoverPolynomial beta alpha d e} ≤
      RingHom.ker
        (weightedSplitTraceRightInversionPolynomialMap alpha beta d e).toRingHom := by
    rw [Ideal.span_le]
    intro q hq
    simp only [Set.mem_singleton_iff] at hq
    subst q
    exact weightedSplitTraceRightInversionPolynomialMap_relation alpha beta d e
  exact hle hp

@[simp]
theorem weightedSplitTraceRightInversionAffineMap_x
    (alpha beta : K) (d e : ℕ) :
    weightedSplitTraceRightInversionAffineMap alpha beta d e
        (weightedSplitTraceAffineX beta alpha d e) =
      weightedSplitTraceLaurentX alpha beta d e := by
  change MvPolynomial.aeval
    ![weightedSplitTraceLaurentX alpha beta d e,
      weightedSplitTraceLaurentYInverse alpha beta d e] (MvPolynomial.X 0) = _
  simp

@[simp]
theorem weightedSplitTraceRightInversionAffineMap_y
    (alpha beta : K) (d e : ℕ) :
    weightedSplitTraceRightInversionAffineMap alpha beta d e
        (weightedSplitTraceAffineY beta alpha d e) =
      weightedSplitTraceLaurentYInverse alpha beta d e := by
  change MvPolynomial.aeval
    ![weightedSplitTraceLaurentX alpha beta d e,
      weightedSplitTraceLaurentYInverse alpha beta d e] (MvPolynomial.X 1) = _
  simp

theorem weightedSplitTraceRightInversionAffineMap_coordinateProduct_isUnit
    (alpha beta : K) (d e : ℕ) :
    IsUnit (weightedSplitTraceRightInversionAffineMap alpha beta d e
      (weightedSplitTraceAffineCoordinateProduct beta alpha d e)) := by
  simpa [weightedSplitTraceAffineCoordinateProduct,
    weightedSplitTraceLaurentYInverse] using
    (weightedSplitTraceLaurentX_isUnit alpha beta d e).mul
      (Units.isUnit (weightedSplitTraceLaurentYUnit alpha beta d e)⁻¹)

/-- The localized coordinate-ring map for second-coordinate inversion. -/
def weightedSplitTraceRightInversionLaurentMap (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceLaurentCoordinateRing beta alpha d e →ₐ[K]
      WeightedSplitTraceLaurentCoordinateRing alpha beta d e :=
  IsLocalization.Away.liftAlgHom
    (weightedSplitTraceAffineCoordinateProduct beta alpha d e)
    (weightedSplitTraceRightInversionAffineMap_coordinateProduct_isUnit alpha beta d e)

@[simp]
theorem weightedSplitTraceRightInversionLaurentMap_x
    (alpha beta : K) (d e : ℕ) :
    weightedSplitTraceRightInversionLaurentMap alpha beta d e
        (weightedSplitTraceLaurentX beta alpha d e) =
      weightedSplitTraceLaurentX alpha beta d e := by
  simp only [weightedSplitTraceRightInversionLaurentMap, weightedSplitTraceLaurentX,
    IsLocalization.Away.liftAlgHom_apply]
  rw [IsLocalization.Away.lift_eq]
  exact weightedSplitTraceRightInversionAffineMap_x alpha beta d e

@[simp]
theorem weightedSplitTraceRightInversionLaurentMap_y
    (alpha beta : K) (d e : ℕ) :
    weightedSplitTraceRightInversionLaurentMap alpha beta d e
        (weightedSplitTraceLaurentY beta alpha d e) =
      weightedSplitTraceLaurentYInverse alpha beta d e := by
  simp only [weightedSplitTraceRightInversionLaurentMap, weightedSplitTraceLaurentY,
    IsLocalization.Away.liftAlgHom_apply]
  rw [IsLocalization.Away.lift_eq]
  exact weightedSplitTraceRightInversionAffineMap_y alpha beta d e

@[simp]
theorem weightedSplitTraceRightInversionLaurentMap_yInverse
    (alpha beta : K) (d e : ℕ) :
    weightedSplitTraceRightInversionLaurentMap alpha beta d e
        (weightedSplitTraceLaurentYInverse beta alpha d e) =
      weightedSplitTraceLaurentY alpha beta d e := by
  let sourceUnit := weightedSplitTraceLaurentYUnit beta alpha d e
  let targetUnit := weightedSplitTraceLaurentYUnit alpha beta d e
  let f := weightedSplitTraceRightInversionLaurentMap alpha beta d e
  have hu : Units.map f.toMonoidHom sourceUnit = targetUnit⁻¹ := by
    ext
    simp [f, sourceUnit, targetUnit, weightedSplitTraceLaurentYInverse]
  change f (↑(sourceUnit⁻¹) : WeightedSplitTraceLaurentCoordinateRing beta alpha d e) =
    (↑targetUnit : WeightedSplitTraceLaurentCoordinateRing alpha beta d e)
  calc
    f (↑(sourceUnit⁻¹) : WeightedSplitTraceLaurentCoordinateRing beta alpha d e) =
        ↑(Units.map f.toMonoidHom (sourceUnit⁻¹)) :=
          (Units.coe_map f.toMonoidHom (sourceUnit⁻¹)).symm
    _ = ↑((Units.map f.toMonoidHom sourceUnit)⁻¹) := by rw [map_inv]
    _ = ↑((targetUnit⁻¹)⁻¹) := by rw [hu]
    _ = (↑targetUnit : WeightedSplitTraceLaurentCoordinateRing alpha beta d e) := by simp

@[simp]
theorem weightedSplitTraceRightInversionLaurentMap_xInverse
    (alpha beta : K) (d e : ℕ) :
    weightedSplitTraceRightInversionLaurentMap alpha beta d e
        (weightedSplitTraceLaurentXInverse beta alpha d e) =
      weightedSplitTraceLaurentXInverse alpha beta d e := by
  let sourceUnit := weightedSplitTraceLaurentXUnit beta alpha d e
  let targetUnit := weightedSplitTraceLaurentXUnit alpha beta d e
  let f := weightedSplitTraceRightInversionLaurentMap alpha beta d e
  have hu : Units.map f.toMonoidHom sourceUnit = targetUnit := by
    ext
    simp [f, sourceUnit, targetUnit]
  change f (↑(sourceUnit⁻¹) : WeightedSplitTraceLaurentCoordinateRing beta alpha d e) =
    (↑(targetUnit⁻¹) : WeightedSplitTraceLaurentCoordinateRing alpha beta d e)
  calc
    f (↑(sourceUnit⁻¹) : WeightedSplitTraceLaurentCoordinateRing beta alpha d e) =
        ↑(Units.map f.toMonoidHom (sourceUnit⁻¹)) :=
          (Units.coe_map f.toMonoidHom (sourceUnit⁻¹)).symm
    _ = ↑((Units.map f.toMonoidHom sourceUnit)⁻¹) := by rw [map_inv]
    _ = (↑(targetUnit⁻¹) : WeightedSplitTraceLaurentCoordinateRing alpha beta d e) := by rw [hu]

theorem weightedSplitTraceRightInversionLaurentMap_inverseComposition
    (alpha beta : K) (d e : ℕ) :
    (weightedSplitTraceRightInversionLaurentMap alpha beta d e).comp
        (weightedSplitTraceRightInversionLaurentMap beta alpha d e) =
      AlgHom.id K (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (weightedSplitTraceAffineCoordinateProduct alpha beta d e))
  apply Ideal.Quotient.algHom_ext K
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change weightedSplitTraceRightInversionLaurentMap alpha beta d e
        (weightedSplitTraceRightInversionLaurentMap beta alpha d e
          (weightedSplitTraceLaurentX alpha beta d e)) =
      weightedSplitTraceLaurentX alpha beta d e
    rw [weightedSplitTraceRightInversionLaurentMap_x,
      weightedSplitTraceRightInversionLaurentMap_x]
  · change weightedSplitTraceRightInversionLaurentMap alpha beta d e
        (weightedSplitTraceRightInversionLaurentMap beta alpha d e
          (weightedSplitTraceLaurentY alpha beta d e)) =
      weightedSplitTraceLaurentY alpha beta d e
    rw [weightedSplitTraceRightInversionLaurentMap_y,
      weightedSplitTraceRightInversionLaurentMap_yInverse]

/-- The two coordinate inversions commute on the Laurent overlap.  This is the algebraic cocycle
square needed by the four-chart gluing datum. -/
theorem weightedSplitTraceLaurentInversions_commute
    (alpha beta : K) (d e : ℕ) :
    (weightedSplitTraceLeftInversionLaurentMap alpha beta d e).comp
        (weightedSplitTraceRightInversionLaurentMap alpha beta d e) =
      (weightedSplitTraceRightInversionLaurentMap alpha beta d e).comp
        (weightedSplitTraceLeftInversionLaurentMap beta alpha d e) := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (weightedSplitTraceAffineCoordinateProduct beta alpha d e))
  apply Ideal.Quotient.algHom_ext K
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change weightedSplitTraceLeftInversionLaurentMap alpha beta d e
        (weightedSplitTraceRightInversionLaurentMap alpha beta d e
          (weightedSplitTraceLaurentX beta alpha d e)) =
      weightedSplitTraceRightInversionLaurentMap alpha beta d e
        (weightedSplitTraceLeftInversionLaurentMap beta alpha d e
          (weightedSplitTraceLaurentX beta alpha d e))
    rw [weightedSplitTraceRightInversionLaurentMap_x,
      weightedSplitTraceLeftInversionLaurentMap_x,
      weightedSplitTraceLeftInversionLaurentMap_x,
      weightedSplitTraceRightInversionLaurentMap_xInverse]
  · change weightedSplitTraceLeftInversionLaurentMap alpha beta d e
        (weightedSplitTraceRightInversionLaurentMap alpha beta d e
          (weightedSplitTraceLaurentY beta alpha d e)) =
      weightedSplitTraceRightInversionLaurentMap alpha beta d e
        (weightedSplitTraceLeftInversionLaurentMap beta alpha d e
          (weightedSplitTraceLaurentY beta alpha d e))
    rw [weightedSplitTraceRightInversionLaurentMap_y,
      weightedSplitTraceLeftInversionLaurentMap_yInverse,
      weightedSplitTraceLeftInversionLaurentMap_y,
      weightedSplitTraceRightInversionLaurentMap_y]

/-- The Laurent coordinate rings of the two weight orderings are isomorphic by `y ↦ y⁻¹`. -/
def weightedSplitTraceRightInversionLaurentEquiv (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceLaurentCoordinateRing beta alpha d e ≃ₐ[K]
      WeightedSplitTraceLaurentCoordinateRing alpha beta d e :=
  AlgEquiv.ofAlgHom (weightedSplitTraceRightInversionLaurentMap alpha beta d e)
    (weightedSplitTraceRightInversionLaurentMap beta alpha d e)
    (weightedSplitTraceRightInversionLaurentMap_inverseComposition alpha beta d e)
    (weightedSplitTraceRightInversionLaurentMap_inverseComposition beta alpha d e)

end

end BGS.Markoff

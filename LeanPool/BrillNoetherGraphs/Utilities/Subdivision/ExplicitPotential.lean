/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.AffineCover
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionArithmetic

/-!
# Explicit-potential local subdivision certificates

This module defines a local arithmetic checker for rank-one subdivision
certificates.  It deliberately avoids shortest-path and negative-cycle
reasoning.  A certificate supplies, for every rank-one anchor, one integral
linear potential on the expanded core.  The displayed cone contains the
endpoint inequalities for those potentials literally.

The Boolean checker verifies only exact integer data:

* expanded edges are loopless;
* the proposed divisor has the advertised degree;
* endpoint slope bounds are compatible and make every core residual
  nonnegative; and
* every positivity/bound form needed by the semantics is either the zero form
  or occurs in the displayed cone.

The theorems below turn an accepted record and a point in its cone into the
positive segment lengths, endpoint slope inequalities, nonnegative core
balances, and nonnegative interior second differences needed to assemble an
actual firing script on a subdivision graph.  The graph-construction layer is
kept separate so that this file remains a small arithmetic trust boundary.
-/

-- The `Certificate` structure deliberately lives inside a namespace that already
-- ends in `Certificate`; renaming either would ripple through every consumer.
-- Lean v4.33 added `linter.dupNamespace`, which flags exactly this shape.
namespace Utilities.Certificate

open Finset

namespace ExplicitPotential

/-- Local shorthand for the affine-cover arithmetic type. -/
abbrev AffineForm (m : ℕ) := AffineCover.AffineForm m

/-- Local shorthand for conjunctions of affine-cover rows. -/
abbrev FormsHold {m : ℕ} := AffineCover.FormsHold (m := m)

/-- Executable universal quantification over a finite index type. -/
def allFin {k : ℕ} (test : Fin k → Bool) : Bool :=
  AffineCover.allFin test

@[simp] theorem allFin_eq_true_iff {k : ℕ} (test : Fin k → Bool) :
    allFin test = true ↔ ∀ index : Fin k, test index = true := by
  exact AffineCover.allFin_eq_true_iff test

/-- A finite loopless expanded core, with `p` ordered edge copies. -/
structure Core (n p : ℕ) where
  tail : Fin p → Fin n
  head : Fin p → Fin n

/-- Endpoint slopes and a core potential for one removed-chip test. -/
structure AnchorWitness (m n p : ℕ) where
  alpha : Fin p → ℤ
  beta : Fin p → ℤ
  potential : Fin n → AffineForm m

/-- Passive local data for a rank-one divisor over one length cone. -/
structure Certificate (m n p : ℕ) where
  core : Core n p
  segment : Fin p → AffineForm m
  divisor : Fin n → ℤ
  witness : Fin n → AnchorWitness m n p
  cone : List (AffineForm m)

variable {m n p : ℕ}

namespace AffineForm

/-- Integral scalar multiplication, kept explicit to make the generated data
grammar independent of typeclass inference. -/
def scale (scalar : ℤ) (form : AffineForm m) : AffineForm m where
  fixedValue := scalar * form.constant
  coefficient := fun coordinate => scalar * form.coefficient coordinate

/-- Difference of two integral affine forms. -/
def sub (left right : AffineForm m) : AffineForm m where
  fixedValue := left.constant - right.constant
  coefficient := fun coordinate =>
    left.coefficient coordinate - right.coefficient coordinate

/-- The strict-integral positivity row `form(point) - 1 >= 0`. -/
def positive (form : AffineForm m) : AffineForm m where
  fixedValue := form.constant - 1
  coefficient := form.coefficient

@[simp] theorem eval_scale (scalar : ℤ) (form : AffineForm m)
    (point : Fin m → ℤ) :
    (scale scalar form).eval point = scalar * form.eval point := by
  simp only [scale, AffineCover.AffineForm.eval]
  calc
    scalar * form.constant +
        ∑ x, scalar * form.coefficient x * point x =
      scalar * form.constant +
        ∑ x, scalar * (form.coefficient x * point x) := by
          congr 1
          apply Finset.sum_congr rfl
          intro x _hx
          ring
    _ = scalar * (form.constant +
        ∑ x, form.coefficient x * point x) := by
          rw [mul_add]
          congr 1
          exact (Finset.mul_sum Finset.univ
            (fun x : Fin m => form.coefficient x * point x) scalar).symm

@[simp] theorem eval_sub (left right : AffineForm m)
    (point : Fin m → ℤ) :
    (sub left right).eval point = left.eval point - right.eval point := by
  simp only [sub, AffineCover.AffineForm.eval, sub_mul]
  rw [Finset.sum_sub_distrib]
  ring

@[simp] theorem eval_positive (form : AffineForm m)
    (point : Fin m → ℤ) :
    (positive form).eval point = form.eval point - 1 := by
  simp only [positive, AffineCover.AffineForm.eval]
  ring

end AffineForm

namespace Certificate

/-- The potential rise from the tail to the head of one expanded edge. -/
def rise (certificate : Certificate m n p) (anchor : Fin n)
    (edge : Fin p) : AffineForm m :=
  AffineForm.sub
    ((certificate.witness anchor).potential (certificate.core.head edge))
    ((certificate.witness anchor).potential (certificate.core.tail edge))

/-- The displayed lower endpoint inequality `rise - alpha * length >= 0`. -/
def lowerForm (certificate : Certificate m n p) (anchor : Fin n)
    (edge : Fin p) : AffineForm m :=
  AffineForm.sub (certificate.rise anchor edge)
    (AffineForm.scale ((certificate.witness anchor).alpha edge)
      (certificate.segment edge))

/-- The displayed upper endpoint inequality
`-beta * length - rise >= 0`. -/
def upperForm (certificate : Certificate m n p) (anchor : Fin n)
    (edge : Fin p) : AffineForm m :=
  AffineForm.sub
    (AffineForm.scale (-((certificate.witness anchor).beta edge))
      (certificate.segment edge))
    (certificate.rise anchor edge)

/-- The target coefficient at a core vertex after removing the anchor chip. -/
def targetCoefficient (certificate : Certificate m n p)
    (anchor vertex : Fin n) : ℤ :=
  certificate.divisor vertex - if vertex = anchor then 1 else 0

/-- The conservative endpoint contribution checked before seeing any lengths. -/
def lowerEndpointContribution (certificate : Certificate m n p)
    (anchor vertex : Fin n) : ℤ :=
  ∑ edge : Fin p,
    ((if certificate.core.tail edge = vertex then
        (certificate.witness anchor).alpha edge else 0) +
      (if certificate.core.head edge = vertex then
        (certificate.witness anchor).beta edge else 0))

/-- Point-independent exact validity of a passive local record. -/
def Valid (certificate : Certificate m n p) (degree : ℤ) : Prop :=
  (∀ edge : Fin p, certificate.core.tail edge ≠ certificate.core.head edge) ∧
  (∑ vertex : Fin n, certificate.divisor vertex) = degree ∧
  (∀ anchor : Fin n, ∀ edge : Fin p,
    (certificate.witness anchor).alpha edge +
      (certificate.witness anchor).beta edge ≤ 0) ∧
  (∀ anchor vertex : Fin n,
    0 ≤ certificate.targetCoefficient anchor vertex +
      certificate.lowerEndpointContribution anchor vertex) ∧
  (∀ edge : Fin p,
    AffineForm.positive (certificate.segment edge) = 0 ∨
      AffineForm.positive (certificate.segment edge) ∈ certificate.cone) ∧
  (∀ anchor : Fin n, ∀ edge : Fin p,
    (certificate.lowerForm anchor edge = 0 ∨
      certificate.lowerForm anchor edge ∈ certificate.cone) ∧
    (certificate.upperForm anchor edge = 0 ∨
      certificate.upperForm anchor edge ∈ certificate.cone))

/-- Executable exact validity checker. -/
def check (certificate : Certificate m n p) (degree : ℤ) : Bool :=
  (allFin fun edge : Fin p =>
    decide (certificate.core.tail edge ≠ certificate.core.head edge)) &&
  decide ((∑ vertex : Fin n, certificate.divisor vertex) = degree) &&
  (allFin fun anchor : Fin n =>
    allFin fun edge : Fin p =>
      decide ((certificate.witness anchor).alpha edge +
        (certificate.witness anchor).beta edge ≤ 0)) &&
  (allFin fun anchor : Fin n =>
    allFin fun vertex : Fin n =>
      decide (0 ≤ certificate.targetCoefficient anchor vertex +
        certificate.lowerEndpointContribution anchor vertex)) &&
  (allFin fun edge : Fin p =>
    AffineCover.AffineForm.equal
        (AffineForm.positive (certificate.segment edge)) 0 ||
      AffineCover.AffineForm.mem
        (AffineForm.positive (certificate.segment edge)) certificate.cone) &&
  (allFin fun anchor : Fin n =>
    allFin fun edge : Fin p =>
      (AffineCover.AffineForm.equal (certificate.lowerForm anchor edge) 0 ||
        AffineCover.AffineForm.mem (certificate.lowerForm anchor edge)
          certificate.cone) &&
      (AffineCover.AffineForm.equal (certificate.upperForm anchor edge) 0 ||
        AffineCover.AffineForm.mem (certificate.upperForm anchor edge)
          certificate.cone))

@[simp] theorem check_eq_true_iff
    (certificate : Certificate m n p) (degree : ℤ) :
    certificate.check degree = true ↔ certificate.Valid degree := by
  simp [check, Valid, and_assoc]

/-- A cone holds any required form which is either literally zero or a member
of that cone. -/
private theorem form_holds_of_zero_or_mem
    (certificate : Certificate m n p) (point : Fin m → ℤ)
    (form : AffineForm m)
    (hForm : form = 0 ∨ form ∈ certificate.cone)
    (hCone : FormsHold certificate.cone point) :
    form.Holds point := by
  rcases hForm with rfl | hMember
  · simp [AffineCover.AffineForm.Holds]
  · exact hCone form hMember

/-- Every expanded segment has positive integral length at a point in an
accepted local cone. -/
theorem segment_positive_of_valid
    (certificate : Certificate m n p) {degree : ℤ}
    (hValid : certificate.Valid degree) (point : Fin m → ℤ)
    (hCone : FormsHold certificate.cone point) (edge : Fin p) :
    0 < (certificate.segment edge).eval point := by
  have hHolds := certificate.form_holds_of_zero_or_mem point
    (AffineForm.positive (certificate.segment edge)) (hValid.2.2.2.2.1 edge)
    hCone
  simp only [AffineCover.AffineForm.Holds, AffineForm.eval_positive] at hHolds
  omega

/-- The natural-number segment length decoded from an integral point. -/
def segmentNat (certificate : Certificate m n p)
    (point : Fin m → ℤ) (edge : Fin p) : ℕ :=
  ((certificate.segment edge).eval point).toNat

theorem segmentNat_cast_eq
    (certificate : Certificate m n p) {degree : ℤ}
    (hValid : certificate.Valid degree) (point : Fin m → ℤ)
    (hCone : FormsHold certificate.cone point) (edge : Fin p) :
    (certificate.segmentNat point edge : ℤ) =
      (certificate.segment edge).eval point := by
  exact Int.toNat_of_nonneg
    (le_of_lt (certificate.segment_positive_of_valid hValid point hCone edge))

theorem segmentNat_positive
    (certificate : Certificate m n p) {degree : ℤ}
    (hValid : certificate.Valid degree) (point : Fin m → ℤ)
    (hCone : FormsHold certificate.cone point) (edge : Fin p) :
    0 < certificate.segmentNat point edge := by
  have hPositive := certificate.segment_positive_of_valid hValid point hCone edge
  rw [← certificate.segmentNat_cast_eq hValid point hCone edge] at hPositive
  exact_mod_cast hPositive

/-- Numerical core-potential rise at one integral length point. -/
def riseValue (certificate : Certificate m n p) (anchor : Fin n)
    (point : Fin m → ℤ) (edge : Fin p) : ℤ :=
  (certificate.rise anchor edge).eval point

/-- Membership of the explicit lower/upper forms yields their endpoint rise
bounds with no shortest-path theorem. -/
theorem rise_bounds_of_valid
    (certificate : Certificate m n p) {degree : ℤ}
    (hValid : certificate.Valid degree) (point : Fin m → ℤ)
    (hCone : FormsHold certificate.cone point)
    (anchor : Fin n) (edge : Fin p) :
    (certificate.witness anchor).alpha edge *
        (certificate.segment edge).eval point ≤
      certificate.riseValue anchor point edge ∧
    certificate.riseValue anchor point edge ≤
      -((certificate.witness anchor).beta edge) *
        (certificate.segment edge).eval point := by
  have hRequired := hValid.2.2.2.2.2 anchor edge
  have hLower := certificate.form_holds_of_zero_or_mem point
    (certificate.lowerForm anchor edge) hRequired.1 hCone
  have hUpper := certificate.form_holds_of_zero_or_mem point
    (certificate.upperForm anchor edge) hRequired.2 hCone
  simp only [AffineCover.AffineForm.Holds, lowerForm, upperForm,
    AffineForm.eval_sub, AffineForm.eval_scale] at hLower hUpper
  unfold riseValue
  constructor <;> omega

/-- The two endpoint slopes supplied by integer interpolation dominate the
advertised `alpha`/`beta` bounds. -/
theorem interpolated_endpoint_bounds
    (certificate : Certificate m n p) {degree : ℤ}
    (hValid : certificate.Valid degree) (point : Fin m → ℤ)
    (hCone : FormsHold certificate.cone point)
    (anchor : Fin n) (edge : Fin p) :
    (certificate.witness anchor).alpha edge ≤
      SubdivisionArithmetic.step
        (certificate.segmentNat point edge)
        (certificate.riseValue anchor point edge) 0 ∧
    (certificate.witness anchor).beta edge ≤
      -SubdivisionArithmetic.step
        (certificate.segmentNat point edge)
        (certificate.riseValue anchor point edge)
        (certificate.segmentNat point edge - 1) := by
  have hBounds := certificate.rise_bounds_of_valid hValid point hCone anchor edge
  have hCast := certificate.segmentNat_cast_eq hValid point hCone edge
  apply SubdivisionArithmetic.endpointSlopeBounds
    (hL := certificate.segmentNat_positive hValid point hCone edge)
  · simpa only [hCast] using hBounds.1
  · simpa only [hCast] using hBounds.2

/-- Actual interpolated endpoint contribution at a core vertex. -/
def endpointContribution (certificate : Certificate m n p)
    (anchor : Fin n) (point : Fin m → ℤ) (vertex : Fin n) : ℤ :=
  ∑ edge : Fin p,
    ((if certificate.core.tail edge = vertex then
      SubdivisionArithmetic.step
        (certificate.segmentNat point edge)
        (certificate.riseValue anchor point edge) 0 else 0) +
    (if certificate.core.head edge = vertex then
      -SubdivisionArithmetic.step
        (certificate.segmentNat point edge)
        (certificate.riseValue anchor point edge)
        (certificate.segmentNat point edge - 1) else 0))

theorem lowerEndpointContribution_le_endpointContribution
    (certificate : Certificate m n p) {degree : ℤ}
    (hValid : certificate.Valid degree) (point : Fin m → ℤ)
    (hCone : FormsHold certificate.cone point)
    (anchor vertex : Fin n) :
    certificate.lowerEndpointContribution anchor vertex ≤
      certificate.endpointContribution anchor point vertex := by
  unfold lowerEndpointContribution endpointContribution
  apply Finset.sum_le_sum
  intro edge _hEdge
  have hBounds :=
    certificate.interpolated_endpoint_bounds hValid point hCone anchor edge
  by_cases hTail : certificate.core.tail edge = vertex <;>
    by_cases hHead : certificate.core.head edge = vertex <;>
      simp only [hTail, ↓reduceIte, hHead, le_add_neg_iff_add_le, ge_iff_le, add_zero, zero_add,
        Std.le_refl]<;> omega

/-- At every expanded core vertex, the target plus actual interpolated edge
contributions is nonnegative. -/
theorem core_balance_nonnegative
    (certificate : Certificate m n p) {degree : ℤ}
    (hValid : certificate.Valid degree) (point : Fin m → ℤ)
    (hCone : FormsHold certificate.cone point)
    (anchor vertex : Fin n) :
    0 ≤ certificate.targetCoefficient anchor vertex +
      certificate.endpointContribution anchor point vertex := by
  have hConstant := hValid.2.2.2.1 anchor vertex
  have hComparison := certificate.lowerEndpointContribution_le_endpointContribution
    hValid point hCone anchor vertex
  omega

/-- Interpolation is convex at every positive interior offset, hence its
second difference (the path-interior principal-divisor coefficient) is
nonnegative. -/
theorem interior_balance_nonnegative
    (certificate : Certificate m n p) (anchor : Fin n)
    (point : Fin m → ℤ) (edge : Fin p) (offset : ℕ)
    (hOffset : 0 < offset) :
    0 ≤ SubdivisionArithmetic.potential
          (certificate.segmentNat point edge)
          (certificate.riseValue anchor point edge) (offset - 1) -
        2 * SubdivisionArithmetic.potential
          (certificate.segmentNat point edge)
          (certificate.riseValue anchor point edge) offset +
        SubdivisionArithmetic.potential
          (certificate.segmentNat point edge)
          (certificate.riseValue anchor point edge) (offset + 1) :=
  SubdivisionArithmetic.interiorSecondDifference_nonneg _ hOffset

end Certificate

end ExplicitPotential

end Utilities.Certificate

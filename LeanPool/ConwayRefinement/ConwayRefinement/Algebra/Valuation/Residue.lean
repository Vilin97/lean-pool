/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.RV
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Maps

import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The residue map

For a max-additive degree, the elements of nonpositive degree form a subring. Those of strictly
negative degree form an ideal in that subring, and projection to the grade-zero component is a
surjective ring homomorphism with this ideal as its kernel. Consequently, the grade-zero component
is canonically isomorphic to the quotient by the strictly negative ideal. Submultiplicativity
suffices for all of this; multiplicativity enters only in the comparison with the RV class.

This is the quotient presentation in LM24, Proposition 4.2.10. It also realizes the ring in
Corollary 4.2.8 as `MaxAddDegree.ResidueRing`. The module structure of Corollary 4.2.9 is the
grade-zero action `Module ν.ResidueRing (ν.Component m)` supplied by Mathlib's graded direct sums.
The quotient construction remains additive when two degree-zero representatives cancel to strictly
lower degree; `ConwayRefinement.Algebra.Valuation.Tests.Residue` includes a certificate for that
case.
-/

universe u v

public noncomputable section

open scoped DirectSum

namespace MaxAddDegree

variable {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M]
  [LinearOrder M] [IsOrderedCancelAddMonoid M]

/-- The subring of elements whose degree is at most zero. -/
def nonpositiveSubring (ν : MaxAddDegree R M) : Subring R where
  carrier := {x | ν x ≤ 0}
  zero_mem' := by simp
  one_mem' := ν.map_one_le_zero
  add_mem' {x y} hx hy := (ν.map_add_le_max x y).trans (max_le hx hy)
  mul_mem' {x y} hx hy := by
    change ν (x * y) ≤ 0
    change ν x ≤ 0 at hx
    change ν y ≤ 0 at hy
    simpa using degree_mul_le_add hx hy
  neg_mem' {x} hx := by simpa using hx

@[simp]
theorem mem_nonpositiveSubring_iff (ν : MaxAddDegree R M) (x : R) :
    x ∈ ν.nonpositiveSubring ↔ ν x ≤ 0 :=
  Iff.rfl

/-- The additive identification of the nonpositive subring with the weak filtration at zero. -/
def nonpositiveEquivFiltrationLEZero (ν : MaxAddDegree R M) :
    ν.nonpositiveSubring ≃+ ν.filtrationLE 0 where
  toFun x := ⟨x, (ν.mem_filtrationLE_iff 0 x).mpr
    ((ν.mem_nonpositiveSubring_iff x).mp x.2)⟩
  invFun x := ⟨x, (ν.mem_nonpositiveSubring_iff x).mpr
    ((ν.mem_filtrationLE_iff 0 x).mp x.2)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl

@[simp]
theorem coe_nonpositiveEquivFiltrationLEZero (ν : MaxAddDegree R M)
    (x : ν.nonpositiveSubring) :
    (ν.nonpositiveEquivFiltrationLEZero x : R) = x :=
  by simp [nonpositiveEquivFiltrationLEZero]

/-- The projection from the nonpositive subring to the grade-zero homogeneous quotient. -/
def residueMap (ν : MaxAddDegree R M) :
    ν.nonpositiveSubring →+* ν.ResidueRing where
  toFun x := ν.componentMk 0 (ν.nonpositiveEquivFiltrationLEZero x)
  map_zero' := by simp
  map_add' x y := by
    change ν.componentMk 0
      (ν.nonpositiveEquivFiltrationLEZero (x + y)) = _
    rw [map_add, map_add]
  map_one' := by
    change ν.componentMk 0
      (ν.nonpositiveEquivFiltrationLEZero 1) = ν.componentOne
    rw [ν.componentOne_eq_componentMk]
    congr
  map_mul' x y := by
    apply ν.residueRingHom_injective
    simp only [ν.residueRingHom_apply]
    rw [DirectSum.of_zero_mul]
    simp only [← ν.homogeneousMk_apply]
    rw [ν.homogeneousMk_mul]
    simp only [ν.homogeneousMk_apply]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    apply Sigma.ext (zero_add 0).symm
    apply ν.componentMk_heq_of_grade_eq_of_coe_eq (zero_add 0).symm
    simp only [ν.coe_nonpositiveEquivFiltrationLEZero, ν.coe_mulFiltrationLE]
    exact _root_.map_mul ν.nonpositiveSubring.subtype x y

@[simp]
theorem residueMap_apply (ν : MaxAddDegree R M) (x : ν.nonpositiveSubring) :
    ν.residueMap x =
      ν.componentMk 0 (ν.nonpositiveEquivFiltrationLEZero x) :=
  by simp [residueMap]

/-- Every grade-zero class has a representative of nonpositive degree. -/
theorem residueMap_surjective (ν : MaxAddDegree R M) :
    Function.Surjective ν.residueMap := by
  intro c
  induction c using QuotientAddGroup.induction_on with
  | H x => exact ⟨ν.nonpositiveEquivFiltrationLEZero.symm x, by simp⟩

theorem residueMap_eq_zero_iff (ν : MaxAddDegree R M)
    (x : ν.nonpositiveSubring) :
    ν.residueMap x = 0 ↔ ν (x : R) < 0 := by
  rw [ν.residueMap_apply, ν.componentMk_eq_zero_iff]
  rfl

/-- At degree zero or bottom, the RV class and residue class have the same homogeneous image. -/
theorem coe_rvEquivHomogeneous_rv_eq_residueRingHom_residueMap
    (ν : MaxAddDegree R M) [ν.IsMultiplicative] (x : ν.nonpositiveSubring)
    (hx : ν (x : R) = 0 ∨ ν (x : R) = ⊥) :
    (ν.rvEquivHomogeneous (ν.rv (x : R)) : ν.AssociatedGraded) =
      ν.residueRingHom (ν.residueMap x) := by
  rw [ν.rvEquivHomogeneous_apply, ν.coe_rvHomogeneous,
    ν.rvInitialFormHom_rv]
  rcases hx with hx | hx
  · have hxnonbot : ν (x : R) ≠ ⊥ := by simp [hx]
    rw [ν.initialForm_eq_homogeneousMk_of_ne_bot hxnonbot]
    rw [ν.residueRingHom_apply, ν.residueMap_apply, ν.homogeneousMk_apply]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    have hgrade : (ν (x : R)).unbot hxnonbot = 0 :=
      (WithBot.unbot_eq_iff hxnonbot).mpr hx
    apply Sigma.ext hgrade
    apply ν.componentMk_heq_of_grade_eq_of_coe_eq hgrade
    rw [ν.coe_initialRepresentative, ν.coe_nonpositiveEquivFiltrationLEZero]
  · rw [ν.initialForm_eq_zero_of_eq_bot hx]
    have hresidue : ν.residueMap x = 0 := by
      rw [ν.residueMap_eq_zero_iff, hx]
      simp
    rw [hresidue, ν.residueRingHom.map_zero]

/-- The ideal of strictly negative elements in the nonpositive subring. -/
def negativeIdeal (ν : MaxAddDegree R M) : Ideal ν.nonpositiveSubring where
  carrier := {x | ν (x : R) < 0}
  zero_mem' := by simp
  add_mem' {x y} hx hy := (ν.map_add_le_max x y).trans_lt (max_lt hx hy)
  smul_mem' x y hy := by
    change ν ((x : R) * (y : R)) < 0
    simpa using degree_mul_lt_add_of_le_of_lt x.2 hy

@[simp]
theorem mem_negativeIdeal_iff (ν : MaxAddDegree R M)
    (x : ν.nonpositiveSubring) :
    x ∈ ν.negativeIdeal ↔ ν (x : R) < 0 :=
  Iff.rfl

/-- The kernel statement in LM24, Proposition 4.2.10. -/
theorem residueMap_ker (ν : MaxAddDegree R M) :
    RingHom.ker ν.residueMap = ν.negativeIdeal := by
  ext x
  rw [RingHom.mem_ker, ν.residueMap_eq_zero_iff, ν.mem_negativeIdeal_iff]

/-- The first-isomorphism presentation of the residue ring. -/
def residueQuotientEquiv (ν : MaxAddDegree R M) :
    ν.nonpositiveSubring ⧸ ν.negativeIdeal ≃+* ν.ResidueRing :=
  (Ideal.quotEquivOfEq ν.residueMap_ker.symm).trans
    (RingHom.quotientKerEquivOfSurjective ν.residueMap_surjective)

@[simp]
theorem residueQuotientEquiv_mk (ν : MaxAddDegree R M)
    (x : ν.nonpositiveSubring) :
    ν.residueQuotientEquiv (Ideal.Quotient.mk ν.negativeIdeal x) = ν.residueMap x := by
  simp [residueQuotientEquiv]

end MaxAddDegree

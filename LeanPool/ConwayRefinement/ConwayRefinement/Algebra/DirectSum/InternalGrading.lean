/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The internal grading of an external graded algebra

An external graded algebra `⨁ i, A i` is internally graded by the ranges of the canonical
inclusions `lof i : A i → ⨁ i, A i`. This file records the submodules `rangeLof R A i` and the
resulting `GradedAlgebra` instance, so that results stated for internally graded algebras apply
to direct sums.
-/

universe u v w

open scoped DirectSum

public noncomputable section

namespace DirectSum

variable (R : Type u) {ι : Type v} (A : ι → Type w)
variable [CommSemiring R] [DecidableEq ι] [AddMonoid ι]
variable [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)] [GSemiring A] [GAlgebra R A]

/-- The grade-`i` part of an external direct sum: the range of the inclusion of `A i`. -/
def rangeLof (i : ι) : Submodule R (⨁ i, A i) :=
  LinearMap.range (lof R ι A i)

omit [AddMonoid ι] [GSemiring A] [GAlgebra R A] in
theorem rangeLof_eq_range (i : ι) : rangeLof R A i = LinearMap.range (lof R ι A i) := (rfl)

omit [AddMonoid ι] [GSemiring A] [GAlgebra R A] in
theorem lof_mem_rangeLof (i : ι) (a : A i) : lof R ι A i a ∈ rangeLof R A i :=
  ⟨a, rfl⟩

omit [AddMonoid ι] [GSemiring A] [GAlgebra R A] in
theorem of_mem_rangeLof (i : ι) (a : A i) : of A i a ∈ rangeLof R A i :=
  ⟨a, rfl⟩

omit [AddMonoid ι] [GSemiring A] [GAlgebra R A] in
theorem mem_rangeLof_iff (i : ι) (x : ⨁ i, A i) :
    x ∈ rangeLof R A i ↔ ∃ a : A i, lof R ι A i a = x :=
  Iff.rfl

instance instRangeLofGradedMonoid : SetLike.GradedMonoid (rangeLof R A) where
  one_mem := ⟨GradedMonoid.GOne.one, (one_def A).symm⟩
  mul_mem i j x y hx hy := by
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨GradedMonoid.GMul.mul a b, by
      rw [lof_eq_of, lof_eq_of, lof_eq_of, of_mul_of]⟩

/-- The componentwise equivalence `A i ≃ rangeLof R A i`. -/
def rangeLofEquiv (i : ι) : A i ≃ₗ[R] rangeLof R A i :=
  LinearEquiv.ofInjective (lof R ι A i) (of_injective i)

/-- The decomposition of an external direct sum along its internal grading. -/
def rangeLofDecompose : (⨁ i, A i) →ₗ[R] ⨁ i, rangeLof R A i :=
  toModule R ι _ fun i ↦ (lof R ι (fun i ↦ rangeLof R A i) i).comp (rangeLofEquiv R A i).toLinearMap

omit [AddMonoid ι] [GSemiring A] [GAlgebra R A] in
theorem rangeLofDecompose_lof (i : ι) (a : A i) :
    rangeLofDecompose R A (lof R ι A i a) =
      lof R ι (fun i ↦ rangeLof R A i) i (rangeLofEquiv R A i a) := by
  rw [rangeLofDecompose, toModule_lof, LinearMap.comp_apply, LinearEquiv.coe_coe]

omit [GAlgebra R A] in
theorem coeLinearMap_rangeLofDecompose (x : ⨁ i, A i) :
    coeLinearMap (rangeLof R A) (rangeLofDecompose R A x) = x := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of i a =>
    rw [← lof_eq_of R, rangeLofDecompose_lof, coeLinearMap_lof]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [GAlgebra R A] in
theorem rangeLofDecompose_coeLinearMap (x : ⨁ i, rangeLof R A i) :
    rangeLofDecompose R A (coeLinearMap (rangeLof R A) x) = x := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of i a =>
    obtain ⟨b, rfl⟩ := (rangeLofEquiv R A i).surjective a
    rw [← lof_eq_of R, coeLinearMap_lof]
    change rangeLofDecompose R A (lof R ι A i b) = _
    rw [rangeLofDecompose_lof]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [GAlgebra R A] in
theorem rangeLof_isInternal : IsInternal (rangeLof R A) :=
  Function.bijective_iff_has_inverse.mpr ⟨rangeLofDecompose R A,
    rangeLofDecompose_coeLinearMap R A, coeLinearMap_rangeLofDecompose R A⟩

/-- The internal graded-algebra structure on an external direct sum. -/
instance instRangeLofGradedAlgebra : GradedAlgebra (rangeLof R A) :=
  (rangeLof_isInternal R A).gradedAlgebra

/-- The decomposition of the internal grading recovers the components. -/
theorem coe_decompose_rangeLof (x : ⨁ i, A i) (i : ι) :
    ((DirectSum.decompose (rangeLof R A) x i : rangeLof R A i) : ⨁ i, A i) =
      lof R ι A i (x i) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_of x]
  rw [DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum, Finset.sum_eq_single i]
  · rw [DirectSum.decompose_of_mem_same _ (of_mem_rangeLof R A i (x i)), lof_eq_of]
  · intro j _ hji
    rw [DirectSum.decompose_of_mem_ne _ (of_mem_rangeLof R A j (x j)) hji]
  · intro hi
    rw [DFinsupp.notMem_support_iff.mp hi, map_zero, DirectSum.decompose_zero]
    rfl

end DirectSum

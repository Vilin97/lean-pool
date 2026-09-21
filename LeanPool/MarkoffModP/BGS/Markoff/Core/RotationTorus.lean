/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Assembly.ElementaryCounts
import LeanPool.MarkoffModP.BGS.Markoff.Core.Rotation
import Mathlib.FieldTheory.Finite.Trace

/-!
# Split-torus traces and normalized Markoff rotations

This module makes explicit the elementary diagonalization used when a normalized rotation has
split characteristic polynomial.  The two parabolic parameters are excluded by the mathematical
hypothesis `w ^ 2 ≠ 1`; at those parameters the matrix need not have the same order as `w`.
-/

namespace BGS.Markoff

open scoped Matrix

section SplitTorus

variable {F : Type*} [Field F]

/-- The trace of the determinant-one diagonal matrix with eigenvalues `w` and `w⁻¹`. -/
def splitTorusTrace (w : Fˣ) : F :=
  (w : F) + (w⁻¹ : Fˣ)

/-- The determinant-one diagonal matrix with eigenvalues `w` and `w⁻¹`. -/
noncomputable def splitDiagonalSL (w : Fˣ) : Matrix.SpecialLinearGroup (Fin 2) F :=
  Matrix.SpecialLinearGroup.diag2 (w : F) w.ne_zero

@[simp]
theorem splitDiagonalSL_coe (w : Fˣ) :
    (splitDiagonalSL w : Matrix (Fin 2) (Fin 2) F) =
      !![(w : F), 0; 0, (w⁻¹ : Fˣ)] := by
  simpa [splitDiagonalSL] using Matrix.SpecialLinearGroup.diag2_coe' w.ne_zero

/-- An eigenbasis for a non-parabolic split trace. -/
def splitEigenbasis (w : Fˣ) : Matrix (Fin 2) (Fin 2) F :=
  !![1, 1; (w : F), (w⁻¹ : Fˣ)]

theorem splitEigenbasis_det (w : Fˣ) :
    (splitEigenbasis w).det = (w⁻¹ : Fˣ) - (w : F) := by
  simp [splitEigenbasis, Matrix.det_fin_two_of]

theorem splitEigenbasis_det_ne_zero (w : Fˣ) (hw : (w : F) ^ 2 ≠ 1) :
    (splitEigenbasis w).det ≠ 0 := by
  rw [splitEigenbasis_det]
  intro hdet
  have hinv : ((w⁻¹ : Fˣ) : F) = (w : F) := sub_eq_zero.mp hdet
  apply hw
  rw [pow_two]
  calc
    (w : F) * (w : F) = ((w⁻¹ : Fˣ) : F) * (w : F) := by rw [hinv]
    _ = 1 := by simp

/-- The eigenbasis, regarded as an invertible matrix. -/
noncomputable def splitEigenbasisGL (w : Fˣ) (hw : (w : F) ^ 2 ≠ 1) :
    Matrix.GeneralLinearGroup (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (splitEigenbasis w)
    (splitEigenbasis_det_ne_zero w hw)

@[simp]
theorem splitEigenbasisGL_coe (w : Fˣ) (hw : (w : F) ^ 2 ≠ 1) :
    (splitEigenbasisGL w hw : Matrix (Fin 2) (Fin 2) F) = splitEigenbasis w :=
  rfl

/-- In the split eigenbasis, `rho (w + w⁻¹)` is diagonal. -/
theorem splitEigenbasis_semiconj (w : Fˣ) (hw : (w : F) ^ 2 ≠ 1) :
    SemiconjBy (splitEigenbasisGL w hw)
      (Matrix.SpecialLinearGroup.toGL (splitDiagonalSL w))
      (Matrix.SpecialLinearGroup.toGL (rhoSL (splitTorusTrace w))) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [splitEigenbasisGL, splitEigenbasis, splitDiagonalSL_coe,
      splitTorusTrace, rho, Matrix.mul_apply] <;>
    field_simp <;> ring

/-- Diagonal determinant-one matrices multiply by multiplying their first eigenvalues. -/
@[simp]
theorem splitDiagonalSL_mul (w z : Fˣ) :
    splitDiagonalSL (w * z) = splitDiagonalSL w * splitDiagonalSL z := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitDiagonalSL_coe, Matrix.mul_apply]
  all_goals ring

/-- Diagonal determinant-one matrices form the split-torus homomorphism into `SL₂`. -/
noncomputable def splitDiagonalSLHom : Fˣ →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun := splitDiagonalSL
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [splitDiagonalSL_coe]
  map_mul' := splitDiagonalSL_mul

theorem splitDiagonalSLHom_injective :
    Function.Injective (splitDiagonalSLHom : Fˣ → Matrix.SpecialLinearGroup (Fin 2) F) := by
  intro w z h
  apply Units.ext
  have hentry := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
    (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  exact hentry

/-- The diagonal `SL₂` element has exactly the multiplicative order of its first eigenvalue. -/
theorem splitDiagonalSL_orderOf (w : Fˣ) :
    orderOf (splitDiagonalSL w) = orderOf w := by
  exact orderOf_injective splitDiagonalSLHom splitDiagonalSLHom_injective w

/-- A non-parabolic split trace has rotation order equal to the order of either eigenvalue. -/
theorem rotationOrder_splitTorusTrace (w : Fˣ) (hw : (w : F) ^ 2 ≠ 1) :
    rotationOrder (splitTorusTrace w) = orderOf w := by
  calc
    rotationOrder (splitTorusTrace w) =
        orderOf (Matrix.SpecialLinearGroup.toGL (rhoSL (splitTorusTrace w))) := by
      rw [rotationOrder]
      symm
      exact orderOf_injective Matrix.SpecialLinearGroup.toGL
        Matrix.SpecialLinearGroup.toGL_injective _
    _ = orderOf (Matrix.SpecialLinearGroup.toGL (splitDiagonalSL w)) :=
      (splitEigenbasis_semiconj w hw).orderOf_eq.symm
    _ = orderOf (splitDiagonalSL w) :=
      orderOf_injective Matrix.SpecialLinearGroup.toGL
        Matrix.SpecialLinearGroup.toGL_injective _
    _ = orderOf w := splitDiagonalSL_orderOf w

/-- A small non-parabolic split rotation parameter belongs to the canonical bounded-order
split-trace set used by the giant-orbit count. -/
theorem splitTorusTrace_mem_boundedOrderTraceSet_of_rotationOrder_lt
    [Fintype Fˣ] [DecidableEq F] (w : Fˣ) (hw : (w : F) ^ 2 ≠ 1) (bound : ℕ)
    (hsmall : rotationOrder (splitTorusTrace w) < bound) :
    splitTorusTrace w ∈ boundedOrderTraceSet splitTorusTrace bound := by
  rw [boundedOrderTraceSet, Finset.mem_image]
  refine ⟨w, ?_, rfl⟩
  rw [elementsOfOrderLessThan, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, (rotationOrder_splitTorusTrace w hw) ▸ hsmall⟩

end SplitTorus

section ExtensionEigenvalues

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- Diagonalization after extending scalars.  This is the common kernel for both split
eigenvalues and eigenvalues in a quadratic nonsplit torus. -/
theorem extensionEigenbasis_semiconj (t : F) (w : Eˣ)
    (hw : (w : E) ^ 2 ≠ 1) (htrace : algebraMap F E t = splitTorusTrace w) :
    SemiconjBy (splitEigenbasisGL w hw)
      (Matrix.SpecialLinearGroup.toGL (splitDiagonalSL w))
      (Matrix.SpecialLinearGroup.mapGL E (rhoSL t)) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [splitEigenbasisGL, splitEigenbasis, splitDiagonalSL_coe,
      splitTorusTrace, rho, Matrix.mul_apply, htrace] <;>
    field_simp <;> ring

/-- If the eigenvalues of a non-parabolic normalized rotation lie in an injective scalar
extension, its rotation order is exactly the multiplicative order of either eigenvalue. -/
theorem rotationOrder_eq_orderOf_extensionEigenvalue [FaithfulSMul F E]
    (t : F) (w : Eˣ) (hw : (w : E) ^ 2 ≠ 1)
    (htrace : algebraMap F E t = splitTorusTrace w) :
    rotationOrder t = orderOf w := by
  calc
    rotationOrder t = orderOf (Matrix.SpecialLinearGroup.mapGL E (rhoSL t)) := by
      rw [rotationOrder]
      symm
      exact orderOf_injective (Matrix.SpecialLinearGroup.mapGL E)
        Matrix.SpecialLinearGroup.mapGL_injective _
    _ = orderOf (Matrix.SpecialLinearGroup.toGL (splitDiagonalSL w)) :=
      (extensionEigenbasis_semiconj t w hw htrace).orderOf_eq.symm
    _ = orderOf (splitDiagonalSL w) :=
      orderOf_injective Matrix.SpecialLinearGroup.toGL
        Matrix.SpecialLinearGroup.toGL_injective _
    _ = orderOf w := splitDiagonalSL_orderOf w

/-- The scalar-extension order calculation feeds directly into the canonical bounded-order trace
set for any honestly embedded torus.  In the nonsplit application, `H` is the norm-one subgroup
of a quadratic extension and `includeEigenvalue` is its subtype map. -/
theorem extensionTrace_mem_boundedOrderTraceSet_of_rotationOrder_lt
    [FaithfulSMul F E] {H : Type*} [Group H] [Fintype H] [DecidableEq F]
    (includeEigenvalue : H →* Eˣ) (hinclude : Function.Injective includeEigenvalue)
    (trace : H → F) (g : H) (hw : ((includeEigenvalue g : Eˣ) : E) ^ 2 ≠ 1)
    (htrace : algebraMap F E (trace g) = splitTorusTrace (includeEigenvalue g))
    (bound : ℕ) (hsmall : rotationOrder (trace g) < bound) :
    trace g ∈ boundedOrderTraceSet trace bound := by
  rw [boundedOrderTraceSet, Finset.mem_image]
  refine ⟨g, ?_, rfl⟩
  rw [elementsOfOrderLessThan, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [rotationOrder_eq_orderOf_extensionEigenvalue (trace g) (includeEigenvalue g) hw htrace,
    orderOf_injective includeEigenvalue hinclude] at hsmall
  exact hsmall

end ExtensionEigenvalues

section QuadraticFiniteField

variable (p : ℕ) [Fact p.Prime]

/-- The canonical quadratic extension of `ZMod p` supplied by Mathlib. -/
abbrev quadraticFiniteField := GaloisField p 2

/-- The norm-one subgroup of the multiplicative group of the quadratic finite field. -/
noncomputable def quadraticNormOneTorus : Subgroup (quadraticFiniteField p)ˣ :=
  MonoidHom.ker (Units.map (Algebra.norm (ZMod p) (S := quadraticFiniteField p)))

noncomputable instance quadraticNormOneTorusFintype : Fintype (quadraticNormOneTorus p) :=
  Fintype.ofFinite (quadraticNormOneTorus p)

/-- The base-field trace on the quadratic norm-one torus. -/
noncomputable def quadraticNormOneTrace (w : quadraticNormOneTorus p) : ZMod p :=
  Algebra.trace (ZMod p) (quadraticFiniteField p)
    ((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p)

/-- For a norm-one element in the quadratic extension, its field trace is the eigenvalue trace
`w + w⁻¹`. -/
theorem algebraMap_quadraticNormOneTrace (w : quadraticNormOneTorus p) :
    algebraMap (ZMod p) (quadraticFiniteField p) (quadraticNormOneTrace p w) =
      splitTorusTrace (w : (quadraticFiniteField p)ˣ) := by
  have hfinrank : Module.finrank (ZMod p) (quadraticFiniteField p) = 2 :=
    GaloisField.finrank p (by norm_num)
  have htrace := FiniteField.algebraMap_trace_eq_sum_pow
    (ZMod p) (quadraticFiniteField p)
      ((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p)
  have hnorm := FiniteField.algebraMap_norm_eq_prod_pow
    (ZMod p) (quadraticFiniteField p)
      ((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p)
  rw [hfinrank, Nat.card_zmod] at htrace hnorm
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.prod_range_succ,
    Finset.prod_range_zero, pow_zero, pow_one, zero_add, one_mul] at htrace hnorm
  have hwNorm : Algebra.norm (ZMod p)
      ((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) = 1 := by
    have hwMem := w.property
    exact congrArg Units.val hwMem
  rw [hwNorm, map_one] at hnorm
  have hFrob : ((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ p =
      (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p)⁻¹) := by
    apply (mul_eq_one_iff_eq_inv₀
      (show ((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ≠ 0 by
        exact Units.ne_zero _)).mp
    rw [mul_comm]
    exact hnorm.symm
  rw [quadraticNormOneTrace, htrace, hFrob]
  simp [splitTorusTrace]

/-- Away from the two parabolic eigenvalues, the normalized rotation order equals the order of
the corresponding norm-one element in the quadratic extension. -/
theorem rotationOrder_quadraticNormOneTrace (w : quadraticNormOneTorus p)
    (hw : (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ 2) ≠ 1) :
    rotationOrder (quadraticNormOneTrace p w) = orderOf w := by
  calc
    rotationOrder (quadraticNormOneTrace p w) =
        orderOf (w : (quadraticFiniteField p)ˣ) :=
      rotationOrder_eq_orderOf_extensionEigenvalue
        (quadraticNormOneTrace p w) (w : (quadraticFiniteField p)ˣ) hw
        (algebraMap_quadraticNormOneTrace p w)
    _ = orderOf w :=
      orderOf_injective (quadraticNormOneTorus p).subtype Subtype.coe_injective w

/-- A small non-parabolic nonsplit rotation trace belongs to the canonical bounded-order trace
set of the quadratic norm-one torus. -/
theorem quadraticNormOneTrace_mem_boundedOrderTraceSet_of_rotationOrder_lt
    (w : quadraticNormOneTorus p)
    (hw : (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ 2) ≠ 1)
    (bound : ℕ) (hsmall : rotationOrder (quadraticNormOneTrace p w) < bound) :
    quadraticNormOneTrace p w ∈ boundedOrderTraceSet (quadraticNormOneTrace p) bound := by
  exact extensionTrace_mem_boundedOrderTraceSet_of_rotationOrder_lt
    (quadraticNormOneTorus p).subtype Subtype.coe_injective (quadraticNormOneTrace p) w hw
    (algebraMap_quadraticNormOneTrace p w) bound hsmall

/-- The nonsplit bounded-order trace set has the same crude quadratic bound used by the final
giant-orbit count. -/
theorem quadraticNormOneTraceSet_card_le_bound_sq (bound : ℕ) :
    (boundedOrderTraceSet (quadraticNormOneTrace p) bound).card ≤ bound ^ 2 :=
  boundedOrderTraceSet_card_le_bound_sq (quadraticNormOneTrace p) bound

end QuadraticFiniteField

end BGS.Markoff

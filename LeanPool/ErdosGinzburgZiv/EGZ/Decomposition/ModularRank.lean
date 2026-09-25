/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.ScalarExtension
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Injectivity over the reals from injectivity modulo a prime

For a square integer matrix, injectivity modulo a prime implies that the
integer determinant is nonzero. Its real scalar extension is therefore
injective. This applies to integral affine maps between equal-rank fibres.
-/

@[expose] public section

namespace EGZ.IntegralAffineMap

variable {p m n : ℕ} [Fact p.Prime]

/-- The integer coefficient matrix in standard coordinate bases. -/
def coefficientMatrix (A : IntCoord m →ₗ[ℤ] IntCoord n) : Matrix (Fin n) (Fin m) ℤ :=
  fun i j ↦ A (Pi.single j 1) i

omit [Fact p.Prime] in
theorem linearScalarExtension_eq_mulVec (R : Type*) [CommRing R]
    (A : IntCoord m →ₗ[ℤ] IntCoord n) :
    ⇑(linearScalarExtension R A) =
      ((coefficientMatrix A).map (Int.castRingHom R)).mulVec := by
  funext x i
  simp only [linearScalarExtension, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec,
    dotProduct, Matrix.map_apply, Int.coe_castRingHom, coefficientMatrix, mul_comm]

/-- A square integer linear map injective modulo `p` stays injective
after extending scalars to the real numbers. -/
theorem linearScalarExtension_real_injective_of_modp
    (A : IntCoord n →ₗ[ℤ] IntCoord n)
    (hA : Function.Injective (linearScalarExtension (ZMod p) A)) :
    Function.Injective (linearScalarExtension ℝ A) := by
  classical
  let M := coefficientMatrix A
  have hmod : Function.Injective ((M.map (Int.castRingHom (ZMod p))).mulVec) := by
    simpa only [linearScalarExtension_eq_mulVec] using hA
  have hdetmod : (M.map (Int.castRingHom (ZMod p))).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hmod)).ne_zero
  have hdet : M.det ≠ 0 := by
    intro heq
    apply hdetmod
    have hcast : (M.map (Int.castRingHom (ZMod p))).det = (M.det : ZMod p) :=
      ((Int.castRingHom (ZMod p)).map_det M).symm
    rw [hcast, heq, Int.cast_zero]
  have hdetreal : (M.map (Int.castRingHom ℝ)).det ≠ 0 := by
    have hcast : (M.map (Int.castRingHom ℝ)).det = (M.det : ℝ) :=
      ((Int.castRingHom ℝ).map_det M).symm
    rw [hcast]
    exact_mod_cast hdet
  rw [linearScalarExtension_eq_mulVec]
  exact Matrix.mulVec_injective_of_det_ne_zero hdetreal

theorem ofIntAffineMap_real_injective_of_modp
    (A : IntCoord n →ᵃ[ℤ] IntCoord n)
    (hA : Function.Injective ((ofIntAffineMap A).modp p)) :
    Function.Injective (ofIntAffineMap A).real := by
  apply ((ofIntAffineMap A).real.linear_injective_iff).mp
  have hlin : Function.Injective (linearScalarExtension (ZMod p) A.linear) := by
    simpa [ofIntAffineMap, scalarExtension] using
      (((ofIntAffineMap A).modp p).linear_injective_iff.mpr hA)
  simpa [ofIntAffineMap, scalarExtension] using
    linearScalarExtension_real_injective_of_modp A.linear hlin

/-- An equal-rank integral affine map which is injective modulo a prime
is injective on its real coordinate spaces. -/
theorem real_injective_of_modp_of_rank_eq (A : IntegralAffineMap m n) (hrank : m = n)
    (hA : Function.Injective (A.modp p)) : Function.Injective A.real := by
  subst n
  have h := ofIntAffineMap_real_injective_of_modp A.toIntAffineMap (by simpa using hA)
  simpa using h

/-- The same map is injective on its integer lattices. -/
theorem integer_injective_of_modp_of_rank_eq (A : IntegralAffineMap m n) (hrank : m = n)
    (hA : Function.Injective (A.modp p)) : Function.Injective A.integer := by
  have hr := A.real_injective_of_modp_of_rank_eq hrank hA
  intro x y hxy
  apply IntCoord.real_injective
  apply hr
  rw [A.real_integer, A.real_integer, hxy]

end EGZ.IntegralAffineMap

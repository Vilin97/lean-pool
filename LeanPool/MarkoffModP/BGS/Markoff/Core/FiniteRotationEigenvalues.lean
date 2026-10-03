/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Core.ParabolicFibers
public import LeanPool.MarkoffModP.BGS.Markoff.Core.RotationTorus

/-!
# Finite-order Markoff rotations have torsion eigenvalues

This file isolates the algebraic kernel used in the opening argument of
Bourgain--Gamburd--Sarnak.  Over an algebraically closed field, a finite-order
normalized rotation has an eigenvalue of finite multiplicative order, and its
trace is the sum of that eigenvalue and its inverse.

The passage from a finite orbit of a *point* to finite order of the rotation
matrix is deliberately not assumed here.  It is a separate geometric step,
and is delicate at the parabolic traces `2` and `-2`.
-/

@[expose] public section

namespace BGS.Markoff

open scoped Matrix
open Polynomial

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- A finite-order normalized rotation has a torsion eigenvalue whose
eigenvalue trace is the rotation parameter.

This includes the parabolic eigenvalues.  In that case the eigenvalue squares
to one, so it is visibly torsion; away from that case the existing
diagonalization theorem transfers finite order from the rotation to the
eigenvalue. -/
theorem finiteOrderRotation_has_torsion_eigenvalue (t : K)
    (hfinite : IsOfFinOrder (rhoSL t)) :
    ∃ w : Kˣ, IsOfFinOrder w ∧ t = splitTorusTrace w := by
  let f : K[X] := X ^ 2 - C t * X + 1
  have hfdegree : f.degree ≠ 0 := by
    have hfshape : IsMonicOfDegree f 2 := by
      simpa [f] using isMonicOfDegree_sub_add_two t (1 : K)
    rw [degree_eq_natDegree hfshape.monic.ne_zero, hfshape.natDegree_eq]
    norm_num
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root f hfdegree
  have hreigen : r ^ 2 - t * r + 1 = 0 := by
    simpa [f] using hr
  have hrne : r ≠ 0 := by
    intro hrzero
    simp [hrzero] at hreigen
  let w : Kˣ := Units.mk0 r hrne
  have htrace : t = splitTorusTrace w := by
    have hmul : t * r = r ^ 2 + 1 := by
      linear_combination -hreigen
    change t = r + r⁻¹
    apply (mul_right_cancel₀ hrne)
    rw [hmul]
    field_simp
  refine ⟨w, ?_, htrace⟩
  by_cases hparabolic : (w : K) ^ 2 = 1
  · rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨2, by omega, ?_⟩
    apply Units.ext
    exact hparabolic
  · rw [← orderOf_pos_iff]
    have hrotation : 0 < rotationOrder t := by
      simpa [rotationOrder] using hfinite.orderOf_pos
    rw [htrace, rotationOrder_splitTorusTrace w hparabolic] at hrotation
    exact hrotation

section ParabolicObstruction

variable {R : Type*} [CommRing R] [CharZero R]

/-- The trace-`2` unipotent rotation has infinite order in characteristic
zero. -/
theorem rhoSL_two_not_finiteOrder : ¬ IsOfFinOrder (rhoSL (2 : R)) := by
  intro hfinite
  obtain ⟨n, hnpos, hpower⟩ := hfinite.exists_pow_eq_one
  have hmatrix := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 2) R ↦
      (g : Matrix (Fin 2) (Fin 2) R)) hpower
  change rho (2 : R) ^ n = 1 at hmatrix
  have hoffDiagonal := congrArg
    (fun m : Matrix (Fin 2) (Fin 2) R ↦ m 0 1) hmatrix
  have hnzero : (n : R) = 0 := by
    simpa [rho_two_pow] using hoffDiagonal
  have : n = 0 := by exact_mod_cast hnzero
  exact hnpos.ne' this

/-- Periodicity of one vector under a coordinate rotation does not by itself
imply finite order of the rotation matrix.  The nonzero vector `(1,1)` is
fixed by the trace-`2` rotation, while that matrix has infinite order in
characteristic zero.

This is the parabolic obstruction that must be handled before the paper's
finite-orbit discussion can invoke `finiteOrderRotation_has_torsion_eigenvalue`.
-/
theorem exists_nonzero_fixedVector_with_infiniteOrder_rotation :
    ∃ v : Fin 2 → R,
      v ≠ 0 ∧ rho (2 : R) *ᵥ v = v ∧ ¬ IsOfFinOrder (rhoSL (2 : R)) := by
  refine ⟨![1, 1], ?_, ?_, ?_⟩
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · rw [rho_mulVec]
    ext i
    fin_cases i
    · simp
    · simp
      ring
  · exact rhoSL_two_not_finiteOrder

end ParabolicObstruction

end BGS.Markoff

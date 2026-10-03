/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Foundation

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Determinant bounds for Hessian estimates
-/

@[expose] public noncomputable section

open scoped ContDiff MatrixOrder Topology
open scoped ENNReal

open ContinuousLinearMap

namespace ViscositySolns

variable {n : Nat}

/--
Determinant bound for positive semidefinite matrices bounded above by a
scalar multiple of the identity.

In quantified mathematical form, if `A` is a positive semidefinite real
`n × n` matrix, if `0 ≤ lambda`, and if `A ≤ lambda I` in the Loewner order,
then `det A ≤ lambda^n`.
-/
theorem Matrix.PosSemidef.det_le_pow_of_le_smul_one
    {lambda : Real} (hlambda : 0 <= lambda) {A : Hessian n}
    (hA : A.PosSemidef) (hAle : A <= lambda • (1 : Hessian n)) :
    A.det <= lambda ^ n := by
  classical
  have _hlambda_nonneg : 0 <= lambda := hlambda
  let hHerm : A.IsHermitian := hA.isHermitian
  have heigen_upper :
      ∀ i : Fin n, hHerm.eigenvalues i <= lambda := by
    intro i
    let v : Point n := ⇑(hHerm.eigenvectorBasis i)
    have hpsd : (lambda • (1 : Hessian n) - A).PosSemidef :=
      Matrix.le_iff.mp hAle
    have hquad_nonneg :
        0 <= dotProduct v (Matrix.mulVec (lambda • (1 : Hessian n) - A) v) :=
      hpsd.dotProduct_mulVec_nonneg v
    have hv_norm : dotProduct v v = 1 := by
      have hnorm : ‖hHerm.eigenvectorBasis i‖ = (1 : Real) :=
        hHerm.eigenvectorBasis.norm_eq_one i
      have hnorm_sq : ‖hHerm.eigenvectorBasis i‖ ^ 2 = (1 : Real) := by
        rw [hnorm]
        norm_num
      rw [EuclideanSpace.real_norm_sq_eq] at hnorm_sq
      simpa [v, dotProduct, pow_two] using hnorm_sq
    have hdotA : dotProduct v (Matrix.mulVec A v) = hHerm.eigenvalues i := by
      have heig := hHerm.eigenvalues_eq i
      simpa [v] using heig.symm
    have hsmul_one :
        dotProduct v (Matrix.mulVec (lambda • (1 : Hessian n)) v) = lambda := by
      calc
        dotProduct v (Matrix.mulVec (lambda • (1 : Hessian n)) v)
            = lambda * dotProduct v v := by
              simp [Matrix.smul_mulVec, Matrix.one_mulVec]
        _ = lambda := by
          rw [hv_norm]
          ring
    have hquad :
        dotProduct v (Matrix.mulVec (lambda • (1 : Hessian n) - A) v) =
          lambda - hHerm.eigenvalues i := by
      calc
        dotProduct v (Matrix.mulVec (lambda • (1 : Hessian n) - A) v)
            = dotProduct v (Matrix.mulVec (lambda • (1 : Hessian n)) v) -
                dotProduct v (Matrix.mulVec A v) := by
              simp [Matrix.sub_mulVec, dotProduct_sub]
        _ = lambda - hHerm.eigenvalues i := by
          rw [hsmul_one, hdotA]
    linarith
  calc
    A.det = ∏ i : Fin n, hHerm.eigenvalues i := by
      simpa [hHerm] using hHerm.det_eq_prod_eigenvalues
    _ <= ∏ _i : Fin n, lambda := by
      exact Finset.prod_le_prod₀
        (fun i _hi => hA.eigenvalues_nonneg i)
        (fun i _hi => heigen_upper i)
    _ = lambda ^ n := by
      simp

/--
Determinant bound for Hermitian matrices whose eigenvalues lie between
`-lambda` and `0`.

In quantified mathematical form, if `A` is Hermitian, `0 ≤ lambda`,
`-lambda I ≤ A`, and `A ≤ 0`, then `|det A| ≤ lambda^n`.
-/
theorem hessian_abs_det_le_pow_of_neg_smul_one_le_of_le_zero
    {lambda : Real} (hlambda : 0 <= lambda) {A : Hessian n}
    (hA : A.IsHermitian)
    (hlower : -(lambda • (1 : Hessian n)) <= A)
    (hupper : A <= 0) :
    |A.det| <= lambda ^ n := by
  classical
  have _hA_hermitian : A.IsHermitian := hA
  have hnegA_psd : (-A).PosSemidef := by
    simpa [Matrix.le_iff] using hupper
  have hnegA_le : (-A) <= lambda • (1 : Hessian n) := by
    simpa using (neg_le_neg hlower)
  have hdet_neg_le :
      (-A).det <= lambda ^ n :=
    Matrix.PosSemidef.det_le_pow_of_le_smul_one
      (n := n) hlambda hnegA_psd hnegA_le
  have hdet_abs_eq : |A.det| = (-A).det := by
    have hdet_neg_nonneg : 0 <= (-A).det :=
      Matrix.PosSemidef.det_nonneg hnegA_psd
    have habs_neg : |(-A).det| = (-A).det := abs_of_nonneg hdet_neg_nonneg
    have hsame_abs : |(-A).det| = |A.det| := by
      rw [Matrix.det_neg]
      simp [abs_mul]
    linarith
  simpa [hdet_abs_eq] using hdet_neg_le

/--
The determinant bound in the `ℝ≥0∞` form used by the Jacobian estimate.

In quantified mathematical form, if `A` is Hermitian, `0 ≤ lambda`,
`-lambda I ≤ A`, and `A ≤ 0`, then
`ofReal |det A| ≤ ofReal (max (lambda^n) 1)`.

The maximum with `1` gives a positive finite constant for the later division
step, while still dominating the determinant bound supplied by the preceding
theorem.
-/
theorem hessian_ofReal_abs_det_le_of_neg_smul_one_le_of_le_zero
    {lambda : Real} (hlambda : 0 <= lambda) {A : Hessian n}
    (hA : A.IsHermitian)
    (hlower : -(lambda • (1 : Hessian n)) <= A)
    (hupper : A <= 0) :
    ENNReal.ofReal |A.det| <= ENNReal.ofReal (max (lambda ^ n) 1) := by
  exact ENNReal.ofReal_le_ofReal
    ((hessian_abs_det_le_pow_of_neg_smul_one_le_of_le_zero
      (n := n) hlambda hA hlower hupper).trans (le_max_left _ _))

/--
Pointwise determinant bound from Loewner-order Hessian bounds.

In quantified mathematical form, let `S ⊆ R^n` and let `H x` be a real
symmetric matrix for every `x ∈ S`. If `0 ≤ lambda` and, for every `x ∈ S`,
`-lambda I ≤ H x ≤ 0`, then for every `x ∈ S`,
`ofReal |det (H x)| ≤ ofReal (max (lambda^n) 1)`.
-/
theorem ofReal_abs_det_le_of_forall_hessian_bounds
    {S : Set (Point n)} {H : Point n -> Hessian n} {lambda : Real}
    (hlambda : 0 <= lambda)
    (hHerm : ∀ x : Point n, x ∈ S -> (H x).IsHermitian)
    (hlower :
      ∀ x : Point n, x ∈ S -> -(lambda • (1 : Hessian n)) <= H x)
    (hupper : ∀ x : Point n, x ∈ S -> H x <= 0) :
    ∀ x : Point n, x ∈ S ->
      ENNReal.ofReal |(H x).det| <= ENNReal.ofReal (max (lambda ^ n) 1) := by
  intro x hx
  exact hessian_ofReal_abs_det_le_of_neg_smul_one_le_of_le_zero
    (n := n) hlambda (hHerm x hx) (hlower x hx) (hupper x hx)

end ViscositySolns

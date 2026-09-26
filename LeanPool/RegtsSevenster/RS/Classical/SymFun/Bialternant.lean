/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SymFun.EHDischarge

/-!
# The bialternant Jacobi–Trudi identity

The matrix of variable powers `x_j^{v i + (k−1−i)}` factors as the
column-reversed Jacobi–Trudi matrix of complete homogeneous
polynomials times the signed elementary matrix in the
complementary variables — entrywise this is the resolvent.  Taking
determinants and anchoring at `v = 0` gives the bialternant form:

    `det (powMat v) = det (jtMat v) * det (powMat 0)`,

the polynomial Jacobi–Trudi identity `a_{v+δ} = s_v · a_δ`.
-/

@[expose] public section

namespace RS

open Finset MvPolynomial Equiv

variable {k : ℕ}

/-- The alternant matrix of variable powers. -/
noncomputable def powMat (v : Fin k → ℕ) :
    Matrix (Fin k) (Fin k) (MvPolynomial (Fin k) ℂ) :=
  Matrix.of fun i j => X j ^ (v i + ((k - 1) - (i : ℕ)))

/-- The column-reversed complete homogeneous matrix. -/
noncomputable def hMat (v : Fin k → ℕ) :
    Matrix (Fin k) (Fin k) (MvPolynomial (Fin k) ℂ) :=
  Matrix.of fun i r => hSubZ Finset.univ
    ((v i : ℤ) + ((k : ℤ) - 1 - (r : ℕ)) - (i : ℕ))

/-- The Jacobi–Trudi matrix of complete homogeneous
polynomials. -/
noncomputable def jtMat (v : Fin k → ℕ) :
    Matrix (Fin k) (Fin k) (MvPolynomial (Fin k) ℂ) :=
  Matrix.of fun i j => hSubZ Finset.univ
    ((v i : ℤ) + (j : ℕ) - (i : ℕ))

/-- The signed elementary matrix in complementary variables. -/
noncomputable def eMat (k : ℕ) :
    Matrix (Fin k) (Fin k) (MvPolynomial (Fin k) ℂ) :=
  Matrix.of fun r j =>
    (-1) ^ (r : ℕ) * eSub (Finset.univ.erase j) r

/-- **The entrywise factorization** via the resolvent. -/
theorem powMat_eq_mul (v : Fin k → ℕ) :
    powMat v = hMat v * eMat k := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply]
  have hj : j ∉ Finset.univ.erase j := Finset.notMem_erase j _
  have hcard : (Finset.univ.erase j).card + 1 = k := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ, Fintype.card_fin]
    have hk := j.pos
    omega
  have hres := sum_fin_resolvent' hj hcard (v i + ((k - 1) - (i : ℕ)))
  rw [Finset.insert_erase (Finset.mem_univ j)] at hres
  rw [show powMat v i j = X j ^ (v i + ((k - 1) - (i : ℕ)))
    from rfl]
  rw [← hres]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [show hMat v i r = hSubZ Finset.univ
      ((v i : ℤ) + ((k : ℤ) - 1 - (r : ℕ)) - (i : ℕ)) from rfl]
  rw [show eMat k r j =
      (-1) ^ (r : ℕ) * eSub (Finset.univ.erase j) r from rfl]
  rw [show ((v i + ((k - 1) - (i : ℕ)) : ℕ) : ℤ) - (r : ℕ) =
      (v i : ℤ) + ((k : ℤ) - 1 - (r : ℕ)) - (i : ℕ) from by
    have hi := i.isLt
    omega]
  ring

/-- The reversed columns of `hMat` give the Jacobi–Trudi
matrix. -/
theorem hMat_eq_submatrix (v : Fin k → ℕ) :
    hMat v = (jtMat v).submatrix id Fin.revPerm := by
  refine Matrix.ext fun i r => ?_
  change hSubZ Finset.univ
      ((v i : ℤ) + ((k : ℤ) - 1 - (r : ℕ)) - (i : ℕ)) =
    hSubZ Finset.univ
      ((v i : ℤ) + ((Fin.revPerm r : Fin k) : ℕ) - (i : ℕ))
  congr 1
  have hr := r.isLt
  have hrev : ((Fin.revPerm r : Fin k) : ℕ) = k - ((r : ℕ) + 1) :=
    Fin.val_rev r
  rw [hrev]
  omega

/-- The power matrix's determinant is the Jacobi–Trudi matrix's, up
to the column-reversal sign. -/
theorem det_hMat (v : Fin k → ℕ) :
    (hMat v).det =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin k)) : ℤ) :
        MvPolynomial (Fin k) ℂ) * (jtMat v).det := by
  rw [hMat_eq_submatrix, Matrix.det_permute']

/-- The zero-shape Jacobi–Trudi matrix is upper triangular with
unit diagonal. -/
theorem det_jtMat_zero :
    (jtMat (fun _ : Fin k => 0)).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    change hSubZ Finset.univ
      (((0 : ℕ) : ℤ) + (i : ℕ) - (i : ℕ)) = 1
    rw [show (((0 : ℕ) : ℤ) + (i : ℕ) - (i : ℕ)) =
      ((0 : ℕ) : ℤ) from by omega]
    rw [hSubZ_natCast, hSub_zero]
  · intro i j hij
    change hSubZ Finset.univ
      (((0 : ℕ) : ℤ) + (j : ℕ) - (i : ℕ)) = 0
    have hlt : (j : ℕ) < (i : ℕ) := hij
    exact hSubZ_neg _ _ (by omega)

/-- **The bialternant Jacobi–Trudi identity**:
`a_{v+δ} = s_v · a_δ` over the polynomial ring. -/
theorem bialternant (v : Fin k → ℕ) :
    (powMat v).det =
      (jtMat v).det * (powMat (fun _ : Fin k => 0)).det := by
  have h1 : (powMat v).det = (hMat v).det * (eMat k).det := by
    rw [powMat_eq_mul, Matrix.det_mul]
  have h0 : (powMat (fun _ : Fin k => 0)).det =
      (hMat (fun _ : Fin k => 0)).det * (eMat k).det := by
    rw [powMat_eq_mul, Matrix.det_mul]
  rw [h1, det_hMat, h0, det_hMat, det_jtMat_zero]
  ring

end RS

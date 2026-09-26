/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Power sums and the determinant Schur specialization

Given a sequence `t : ℕ → ℂ` of prospective power sums, this module
defines the complete homogeneous sequence `newtonH t` by the Newton
recursion `(n+1) · h (n+1) = ∑_{i ≤ n} t (i+1) · h (n−i)`, its
integer-indexed extension `newtonHZ` (zero in negative degrees), and
the Schur specialization

    `schurDet t rows = det (newtonHZ t (rows i + j − i))`,

the Jacobi–Trudi determinant read as a *definition*.  All Schur
values in this development are these determinants; the link to the
symmetric-group characters is the `frobenius` field of
`SchurPackage` in `Interfaces/SchurPackage.lean`.
-/

@[expose] public section

namespace RS

/-- The complete homogeneous sequence attached to a sequence of
power sums, via the Newton recursion
`(n+1) · h (n+1) = ∑_{i ≤ n} t (i+1) · h (n−i)`; `h 0 = 1`. -/
noncomputable def newtonH (t : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 =>
      ((n : ℂ) + 1)⁻¹ *
        ∑ i ∈ Finset.range (n + 1), t (i + 1) * newtonH t (n - i)
  decreasing_by exact Nat.lt_succ_of_le (Nat.sub_le n i)

/-- Integer-indexed extension of `newtonH`, vanishing in negative
degrees — the form entering the Jacobi–Trudi determinant. -/
noncomputable def newtonHZ (t : ℕ → ℂ) (n : ℤ) : ℂ :=
  if 0 ≤ n then newtonH t n.toNat else 0

/-- The Schur specialization of a row-length list `rows`, defined as
the Jacobi–Trudi determinant `det (h_{rows i − i + j})_{i,j}`. -/
noncomputable def schurDet (t : ℕ → ℂ) (rows : List ℕ) : ℂ :=
  Matrix.det <| Matrix.of fun i j : Fin rows.length =>
    newtonHZ t ((rows.get i : ℤ) + (j : ℤ) - (i : ℤ))

/-- The Schur specialization of a Young diagram: `schurDet` on its
row-length list. -/
noncomputable def diagramSchur (μ : YoungDiagram) (t : ℕ → ℂ) : ℂ :=
  schurDet t μ.rowLens

/-- The complete homogeneous sequence starts at `1`. -/
@[simp]
theorem newtonH_zero (t : ℕ → ℂ) : newtonH t 0 = 1 := by
  simp [newtonH]

/-- Its integer extension agrees in non-negative degrees. -/
@[simp]
theorem newtonHZ_natCast (t : ℕ → ℂ) (n : ℕ) :
    newtonHZ t (n : ℤ) = newtonH t n := by
  simp [newtonHZ]

/-- And vanishes in negative ones. -/
@[simp]
theorem newtonHZ_neg (t : ℕ → ℂ) (n : ℤ) (hn : n < 0) :
    newtonHZ t n = 0 := by
  simp [newtonHZ, not_le.mpr hn]

end RS

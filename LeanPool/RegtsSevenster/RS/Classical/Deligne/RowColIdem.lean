/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.AltPow
import LeanPool.RegtsSevenster.RS.Classical.Deligne.PieriPos

/-!
# The one-row and one-column idempotents

The central idempotent of the single-row shape of size `n` is the
symmetriser of `ℂ[S_n]`, and that of the single-column shape is the
antisymmetriser: `Shape.e P (rowShape n) = symmetriser n` and
`Shape.e P (colShape n) = antisymmetriser n`.

The route runs through the Frobenius field of the package.  The
Schur specialisation of the single-row shape is the complete
homogeneous value `newtonH t n` (a one-by-one Jacobi–Trudi
determinant), and that of the single-column shape is the elementary
value `(-1)^n · newtonH (-t) n` (an `n × n` determinant, evaluated
by clearing with the unitriangular matrix of `newtonHZ (-t)` through
the convolution identity of `NewtonConv.lean`).  The cycle-sum
identity of `SchurTheory/CycleSum.lean` expresses the same two
specialisations as the Frobenius pairings of the constant and the
sign character, so the determination theorem of `RegularSum.lean`
pins the package's characters on these shapes; idempotency then
forces dimension one, and the idempotents coincide with the
symmetriser and antisymmetriser on the nose.
-/

namespace RS

open Finset Equiv

universe u

/-! ### Complete homogeneous values: the zero and alternating
sequences -/

/-- The complete homogeneous values of the zero sequence vanish in
positive degree. -/
theorem newtonH_zero_fun (m : ℕ) :
    newtonH (fun _ => (0 : ℂ)) (m + 1) = 0 := by
  rw [newtonH]
  rw [Finset.sum_congr rfl fun i _ => by
    change (fun _ => (0 : ℂ)) (i + 1) * _ = (0 : ℂ)
    exact zero_mul _]
  rw [Finset.sum_const_zero, mul_zero]

/-- The complete homogeneous values of the alternating twist of a
sequence are, up to sign, those of its negation. -/
theorem newtonH_alt (t : ℕ → ℂ) :
    ∀ m, newtonH (fun c => (-1) ^ (c + 1) * t c) m =
      (-1) ^ m * newtonH (fun c => -t c) m
  | 0 => by rw [newtonH, newtonH]; norm_num
  | m + 1 => by
    rw [newtonH, newtonH]
    have hterm : ∀ i ∈ Finset.range (m + 1),
        (fun c => (-1 : ℂ) ^ (c + 1) * t c) (i + 1) *
            newtonH (fun c => (-1 : ℂ) ^ (c + 1) * t c) (m - i) =
          (-1) ^ (m + 1) *
            ((fun c => -t c) (i + 1) *
              newtonH (fun c => -t c) (m - i)) := by
      intro i hi
      have him : i ≤ m := by
        have := Finset.mem_range.mp hi
        omega
      rw [newtonH_alt t (m - i)]
      have hpow : (-1 : ℂ) ^ (i + 1 + 1) * (-1) ^ (m - i) =
          (-1) ^ (m + 1) * (-1) := by
        rw [← pow_add, ← pow_succ]
        congr 1
        omega
      change (-1 : ℂ) ^ (i + 1 + 1) * t (i + 1) *
          ((-1) ^ (m - i) * newtonH (fun c => -t c) (m - i)) =
        (-1) ^ (m + 1) *
          (-t (i + 1) * newtonH (fun c => -t c) (m - i))
      linear_combination
        (t (i + 1) * newtonH (fun c => -t c) (m - i)) * hpow
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    ring
  decreasing_by exact Nat.lt_succ_of_le (Nat.sub_le m i)

/-! ### The row lengths of the one-row and one-column shapes -/

/-- The single-row shape of size zero has no rows. -/
theorem rowShape_rowLens_zero : (rowShape 0).val.rowLens = [] := by
  have hcol : (rowShape 0).val.colLen 0 = 0 := by
    by_contra h
    have hmem : ((0, 0) : ℕ × ℕ) ∈ (rowShape 0).val :=
      YoungDiagram.mem_iff_lt_colLen.mpr (Nat.pos_of_ne_zero h)
    rw [YoungDiagram.mem_iff_lt_rowLen, rowShape_rowLen_zero] at hmem
    omega
  rw [show (rowShape 0).val.rowLens =
    (List.range ((rowShape 0).val.colLen 0)).map
      (rowShape 0).val.rowLen from rfl, hcol]
  rfl

/-- The single-row shape of positive size has row-length list
`[n]`. -/
theorem rowShape_rowLens_pos {n : ℕ} (hn : 0 < n) :
    (rowShape n).val.rowLens = [n] := by
  have hcol : (rowShape n).val.colLen 0 = 1 := by
    have hle := rowShape_colLen n
    have hmem : ((0, 0) : ℕ × ℕ) ∈ (rowShape n).val := by
      rw [YoungDiagram.mem_iff_lt_rowLen, rowShape_rowLen_zero]
      exact hn
    have := YoungDiagram.mem_iff_lt_colLen.mp hmem
    omega
  rw [show (rowShape n).val.rowLens =
    (List.range ((rowShape n).val.colLen 0)).map
      (rowShape n).val.rowLen from rfl, hcol]
  rw [List.range_one, List.map_singleton, rowShape_rowLen_zero]

/-- The Schur specialisation of the single-row shape is the
complete homogeneous value. -/
theorem diagramSchur_rowShape (n : ℕ) (t : ℕ → ℂ) :
    diagramSchur (rowShape n).val t = newtonH t n := by
  cases n with
  | zero =>
    rw [diagramSchur, rowShape_rowLens_zero]
    rw [show schurDet t [] = Matrix.det (Matrix.of fun i j : Fin 0 =>
      newtonHZ t ((([] : List ℕ).get i : ℤ) + (j : ℤ) - (i : ℤ)))
      from rfl]
    rw [Matrix.det_fin_zero, newtonH_zero]
  | succ m =>
    rw [diagramSchur, rowShape_rowLens_pos (Nat.succ_pos m)]
    rw [show schurDet t [m + 1] =
      Matrix.det (Matrix.of fun i j : Fin 1 =>
        newtonHZ t ((([m + 1] : List ℕ).get i : ℤ) +
          (j : ℤ) - (i : ℤ))) from rfl]
    rw [Matrix.det_fin_one, Matrix.of_apply]
    norm_num
    rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring,
      newtonHZ_natCast]

/-- The first column of the single-column shape has length `n`. -/
theorem colShape_colLen_zero (n : ℕ) :
    (colShape n).val.colLen 0 = n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · by_contra h
    have hmem : ((0, 0) : ℕ × ℕ) ∈ (colShape 0).val :=
      YoungDiagram.mem_iff_lt_colLen.mpr (Nat.pos_of_ne_zero h)
    rw [YoungDiagram.mem_iff_lt_rowLen,
      colShape_rowLen_le 0 (Nat.zero_le _)] at hmem
    omega
  · have h1 : n - 1 < (colShape n).val.colLen 0 := by
      have hmem : ((n - 1, 0) : ℕ × ℕ) ∈ (colShape n).val := by
        rw [YoungDiagram.mem_iff_lt_rowLen,
          colShape_rowLen_lt n (by omega)]
        omega
      exact YoungDiagram.mem_iff_lt_colLen.mp hmem
    have h2 : ¬ n < (colShape n).val.colLen 0 := by
      intro h
      have hmem := YoungDiagram.mem_iff_lt_colLen.mpr h
      rw [YoungDiagram.mem_iff_lt_rowLen,
        colShape_rowLen_le n le_rfl] at hmem
      omega
    omega

/-- The single-column shape has row-length list `[1, …, 1]`. -/
theorem colShape_rowLens (n : ℕ) :
    (colShape n).val.rowLens = List.replicate n 1 := by
  rw [show (colShape n).val.rowLens =
    (List.range ((colShape n).val.colLen 0)).map
      (colShape n).val.rowLen from rfl, colShape_colLen_zero]
  refine List.ext_getElem (by simp) ?_
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range,
    List.getElem_replicate]
  exact colShape_rowLen_lt n (by simpa using h1)

/-! ### The single-column Jacobi–Trudi determinant -/

/-- The Jacobi–Trudi matrix of the single-column shape of size
`n`. -/
noncomputable def colJTMat (t : ℕ → ℂ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => newtonHZ t (1 + (j : ℤ) - (i : ℤ))

/-- The Schur specialisation of the single-column shape is the
determinant of `colJTMat`. -/
theorem schurDet_replicate_one (t : ℕ → ℂ) (n : ℕ) :
    schurDet t (List.replicate n 1) = (colJTMat t n).det := by
  have hlen : (List.replicate n (1 : ℕ)).length = n :=
    List.length_replicate ..
  calc schurDet t (List.replicate n 1)
      = ((colJTMat t n).submatrix
          (finCongr hlen) (finCongr hlen)).det := by
        rw [schurDet]
        congr 1
        ext i j
        rw [Matrix.of_apply, Matrix.submatrix_apply]
        rw [show (colJTMat t n) (finCongr hlen i) (finCongr hlen j) =
          newtonHZ t (1 + ((finCongr hlen j : ℕ) : ℤ) -
            ((finCongr hlen i : ℕ) : ℤ)) from rfl]
        have hget : (List.replicate n (1 : ℕ)).get i = 1 := by
          simp [List.get_eq_getElem]
        rw [hget]
        norm_num
    _ = (colJTMat t n).det := Matrix.det_submatrix_equiv_self _ _

/-- The unitriangular convolution matrix of the negated
sequence. -/
noncomputable def negHMat (t : ℕ → ℂ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => newtonHZ (fun c => -t c) ((j : ℤ) - (i : ℤ))

/-- The convolution matrix is unitriangular: determinant one. -/
theorem negHMat_det (t : ℕ → ℂ) (n : ℕ) : (negHMat t n).det = 1 := by
  have htri : (negHMat t n).BlockTriangular id := by
    intro i j hij
    change newtonHZ (fun c => -t c) ((j : ℤ) - (i : ℤ)) = 0
    refine newtonHZ_neg _ _ ?_
    have : (j : ℕ) < (i : ℕ) := hij
    omega
  rw [Matrix.det_of_isUpperTriangular htri]
  refine Finset.prod_eq_one fun i _ => ?_
  change newtonHZ (fun c => -t c) ((i : ℤ) - (i : ℤ)) = 1
  rw [sub_self, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl,
    newtonHZ_natCast, newtonH_zero]

/-- The alternating `h`-convolution vanishes: the guarded
convolution sum of `newtonHZ t` against `newtonHZ (-t)` along a row
of positive index reduces to a Kronecker delta. -/
private theorem conv_sum_pos (t : ℕ → ℂ) {n ik kk : ℕ}
    (hik : 0 < ik) (hkn : kk < n) :
    ∑ j ∈ Finset.range n,
      newtonHZ t (1 + (j : ℤ) - (ik : ℤ)) *
        newtonHZ (fun c => -t c) ((kk : ℤ) - (j : ℤ)) =
      if kk + 1 = ik then 1 else 0 := by
  rcases Nat.lt_or_ge (kk + 1) ik with hB | hA
  · -- below the surviving band every term vanishes
    rw [ite_eq_right (by omega)]
    refine Finset.sum_eq_zero fun j hj => ?_
    rcases Nat.lt_or_ge (j + 1) ik with hj' | hj'
    · rw [newtonHZ_neg t (1 + (j : ℤ) - (ik : ℤ)) (by omega),
        zero_mul]
    · rw [newtonHZ_neg (fun c => -t c) ((kk : ℤ) - (j : ℤ))
        (by omega), mul_zero]
  · -- the full antidiagonal convolution
    have h3 : ∀ d ∈ Finset.range (n - (ik - 1)),
        newtonHZ t (1 + ((ik - 1 + d : ℕ) : ℤ) - (ik : ℤ)) *
          newtonHZ (fun c => -t c)
            ((kk : ℤ) - ((ik - 1 + d : ℕ) : ℤ)) =
        newtonHZ t (d : ℤ) *
          newtonHZ (fun c => -t c)
            (((kk + 1 - ik : ℕ) : ℤ) - (d : ℤ)) := by
      intro d _
      have e1 : 1 + ((ik - 1 + d : ℕ) : ℤ) - (ik : ℤ) = (d : ℤ) := by
        omega
      have e2 : (kk : ℤ) - ((ik - 1 + d : ℕ) : ℤ) =
          ((kk + 1 - ik : ℕ) : ℤ) - (d : ℤ) := by
        omega
      rw [e1, e2]
    have h5 : ∀ d ∈ Finset.range (kk + 1 - ik + 1),
        newtonHZ t (d : ℤ) * newtonHZ (fun c => -t c)
          (((kk + 1 - ik : ℕ) : ℤ) - (d : ℤ)) =
        newtonH t d * newtonH (fun c => -t c) (kk + 1 - ik - d) := by
      intro d hd
      rw [Finset.mem_range] at hd
      rw [newtonHZ_natCast, show ((kk + 1 - ik : ℕ) : ℤ) - (d : ℤ) =
        ((kk + 1 - ik - d : ℕ) : ℤ) by omega, newtonHZ_natCast]
    calc ∑ j ∈ Finset.range n,
          newtonHZ t (1 + (j : ℤ) - (ik : ℤ)) *
            newtonHZ (fun c => -t c) ((kk : ℤ) - (j : ℤ))
        = ∑ j ∈ Finset.Ico (ik - 1) n,
            newtonHZ t (1 + (j : ℤ) - (ik : ℤ)) *
              newtonHZ (fun c => -t c) ((kk : ℤ) - (j : ℤ)) := by
          refine (Finset.sum_subset ?_ ?_).symm
          · intro x hx
            rw [Finset.mem_Ico] at hx
            exact Finset.mem_range.mpr hx.2
          · intro x hx hnot
            rw [Finset.mem_range] at hx
            have hxlt : x < ik - 1 := by
              rw [Finset.mem_Ico] at hnot
              omega
            rw [newtonHZ_neg t (1 + (x : ℤ) - (ik : ℤ)) (by omega),
              zero_mul]
      _ = ∑ d ∈ Finset.range (n - (ik - 1)),
            newtonHZ t (1 + ((ik - 1 + d : ℕ) : ℤ) - (ik : ℤ)) *
              newtonHZ (fun c => -t c)
                ((kk : ℤ) - ((ik - 1 + d : ℕ) : ℤ)) :=
          Finset.sum_Ico_eq_sum_range _ _ _
      _ = ∑ d ∈ Finset.range (n - (ik - 1)),
            newtonHZ t (d : ℤ) *
              newtonHZ (fun c => -t c)
                (((kk + 1 - ik : ℕ) : ℤ) - (d : ℤ)) :=
          Finset.sum_congr rfl h3
      _ = ∑ d ∈ Finset.range (kk + 1 - ik + 1),
            newtonHZ t (d : ℤ) *
              newtonHZ (fun c => -t c)
                (((kk + 1 - ik : ℕ) : ℤ) - (d : ℤ)) := by
          have hsub : Finset.range (kk + 1 - ik + 1) ⊆
              Finset.range (n - (ik - 1)) :=
            Finset.range_subset_range.mpr (by omega)
          refine (Finset.sum_subset hsub ?_).symm
          intro x _ hnot
          rw [Finset.mem_range] at hnot
          rw [newtonHZ_neg (fun c => -t c)
            (((kk + 1 - ik : ℕ) : ℤ) - (x : ℤ)) (by omega),
            mul_zero]
      _ = ∑ d ∈ Finset.range (kk + 1 - ik + 1),
            newtonH t d *
              newtonH (fun c => -t c) (kk + 1 - ik - d) :=
          Finset.sum_congr rfl h5
      _ = newtonH (fun c => t c + -t c) (kk + 1 - ik) := by
          have h6 := newtonH_add t (fun c => -t c) (kk + 1 - ik)
          rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h6
          exact h6.symm
      _ = if kk + 1 = ik then 1 else 0 := by
          rw [show (fun c => t c + -t c) = (fun _ => (0 : ℂ)) from
            funext fun c => by ring]
          rcases Nat.eq_zero_or_pos (kk + 1 - ik) with hz | hp
          · rw [hz, newtonH_zero, ite_eq_left (by omega)]
          · obtain ⟨l, hl⟩ : ∃ l, kk + 1 - ik = l + 1 :=
              ⟨kk - ik, by omega⟩
            rw [hl, newtonH_zero_fun, ite_eq_right (by omega)]

/-- The top-row convolution sum: the missing degree-zero term
leaves the negated elementary value. -/
private theorem conv_sum_zero (t : ℕ → ℂ) {n kk : ℕ}
    (hkn : kk < n) :
    ∑ j ∈ Finset.range n,
      newtonHZ t (1 + (j : ℤ)) *
        newtonHZ (fun c => -t c) ((kk : ℤ) - (j : ℤ)) =
      -newtonH (fun c => -t c) (kk + 1) := by
  have hstep : ∀ j ∈ Finset.range (kk + 1),
      newtonH t (j + 1) * newtonH (fun c => -t c) (kk - j) =
      (fun d => newtonH t d *
        newtonH (fun c => -t c) (kk + 1 - d)) (j + 1) := by
    intro j _
    change _ = newtonH t (j + 1) *
      newtonH (fun c => -t c) (kk + 1 - (j + 1))
    rw [Nat.succ_sub_succ]
  have hconv : ∑ d ∈ Finset.range (kk + 1 + 1),
      newtonH t d * newtonH (fun c => -t c) (kk + 1 - d) =
      newtonH (fun c => t c + -t c) (kk + 1) := by
    have h6 := newtonH_add t (fun c => -t c) (kk + 1)
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h6
    exact h6.symm
  have hzero : newtonH (fun c => t c + -t c) (kk + 1) = 0 := by
    rw [show (fun c => t c + -t c) = (fun _ => (0 : ℂ)) from
      funext fun c => by ring]
    exact newtonH_zero_fun kk
  have hsucc := Finset.sum_range_succ'
    (fun d => newtonH t d * newtonH (fun c => -t c) (kk + 1 - d))
    (kk + 1)
  have h0 : (fun d => newtonH t d *
      newtonH (fun c => -t c) (kk + 1 - d)) 0 =
      newtonH (fun c => -t c) (kk + 1) := by
    change newtonH t 0 * newtonH (fun c => -t c) (kk + 1 - 0) = _
    rw [newtonH_zero, one_mul, Nat.sub_zero]
  calc ∑ j ∈ Finset.range n,
        newtonHZ t (1 + (j : ℤ)) *
          newtonHZ (fun c => -t c) ((kk : ℤ) - (j : ℤ))
      = ∑ j ∈ Finset.range (kk + 1),
          newtonHZ t (1 + (j : ℤ)) *
            newtonHZ (fun c => -t c) ((kk : ℤ) - (j : ℤ)) := by
        have hsub : Finset.range (kk + 1) ⊆ Finset.range n :=
          Finset.range_subset_range.mpr (by omega)
        refine (Finset.sum_subset hsub ?_).symm
        intro x _ hnot
        rw [Finset.mem_range] at hnot
        rw [newtonHZ_neg (fun c => -t c)
          ((kk : ℤ) - (x : ℤ)) (by omega), mul_zero]
    _ = ∑ j ∈ Finset.range (kk + 1),
          newtonH t (j + 1) *
            newtonH (fun c => -t c) (kk - j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        rw [show 1 + (j : ℤ) = ((j + 1 : ℕ) : ℤ) by omega,
          newtonHZ_natCast,
          show (kk : ℤ) - (j : ℤ) = ((kk - j : ℕ) : ℤ) by omega,
          newtonHZ_natCast]
    _ = ∑ j ∈ Finset.range (kk + 1),
          (fun d => newtonH t d *
            newtonH (fun c => -t c) (kk + 1 - d)) (j + 1) :=
        Finset.sum_congr rfl hstep
    _ = -newtonH (fun c => -t c) (kk + 1) := by
        have hs : (0 : ℂ) = ∑ j ∈ Finset.range (kk + 1),
            (fun d => newtonH t d *
              newtonH (fun c => -t c) (kk + 1 - d)) (j + 1) +
            newtonH (fun c => -t c) (kk + 1) := by
          rw [← h0, ← hsucc, hconv, hzero]
        linear_combination -hs

/-- The positive-index rows of the cleared Jacobi–Trudi matrix form
a shifted identity. -/
theorem colJT_mul_negH_pos (t : ℕ → ℂ) {n : ℕ} (i k : Fin n)
    (hi : 0 < (i : ℕ)) :
    (colJTMat t n * negHMat t n) i k =
      if (k : ℕ) + 1 = (i : ℕ) then 1 else 0 := by
  rw [Matrix.mul_apply]
  calc ∑ j, colJTMat t n i j * negHMat t n j k
      = ∑ j ∈ Finset.range n,
          newtonHZ t (1 + (j : ℤ) - ((i : ℕ) : ℤ)) *
            newtonHZ (fun c => -t c) (((k : ℕ) : ℤ) - (j : ℤ)) :=
        Fin.sum_univ_eq_sum_range
          (fun j => newtonHZ t (1 + (j : ℤ) - ((i : ℕ) : ℤ)) *
            newtonHZ (fun c => -t c) (((k : ℕ) : ℤ) - (j : ℤ))) n
    _ = _ := conv_sum_pos t hi k.isLt

/-- The top row of the cleared Jacobi–Trudi matrix carries the
negated elementary values. -/
theorem colJT_mul_negH_zero (t : ℕ → ℂ) {n : ℕ} (i k : Fin n)
    (hi : (i : ℕ) = 0) :
    (colJTMat t n * negHMat t n) i k =
      -newtonH (fun c => -t c) ((k : ℕ) + 1) := by
  rw [Matrix.mul_apply]
  calc ∑ j, colJTMat t n i j * negHMat t n j k
      = ∑ j ∈ Finset.range n,
          newtonHZ t (1 + (j : ℤ) - ((i : ℕ) : ℤ)) *
            newtonHZ (fun c => -t c) (((k : ℕ) : ℤ) - (j : ℤ)) :=
        Fin.sum_univ_eq_sum_range
          (fun j => newtonHZ t (1 + (j : ℤ) - ((i : ℕ) : ℤ)) *
            newtonHZ (fun c => -t c) (((k : ℕ) : ℤ) - (j : ℤ))) n
    _ = ∑ j ∈ Finset.range n,
          newtonHZ t (1 + (j : ℤ)) *
            newtonHZ (fun c => -t c) (((k : ℕ) : ℤ) - (j : ℤ)) := by
        simp only [hi, Nat.cast_zero, sub_zero]
    _ = _ := conv_sum_zero t k.isLt

/-- **The single-column determinant**: the Jacobi–Trudi determinant
of the one-column shape is the elementary value
`(-1)^n · newtonH (-t) n`. -/
theorem colJTMat_det (t : ℕ → ℂ) (n : ℕ) :
    (colJTMat t n).det = (-1) ^ n * newtonH (fun c => -t c) n := by
  cases n with
  | zero =>
    rw [Matrix.det_fin_zero, newtonH_zero]
    norm_num
  | succ m =>
    have hdetP : (colJTMat t (m + 1) * negHMat t (m + 1)).det =
        (colJTMat t (m + 1)).det := by
      rw [Matrix.det_mul, negHMat_det, mul_one]
    have htri : ((colJTMat t (m + 1) * negHMat t (m + 1)).submatrix
        (finRotate (m + 1)) id).BlockTriangular
          OrderDual.toDual := by
      intro a b hab
      have hab' : a < b := OrderDual.toDual_lt_toDual.mp hab
      have hne : a ≠ Fin.last m := by
        intro h
        rw [h] at hab'
        exact absurd hab' (not_lt.mpr (Fin.le_last b))
      rw [Matrix.submatrix_apply, id_eq]
      rw [colJT_mul_negH_pos t _ _ (by
        rw [coe_finRotate_of_ne_last hne]
        omega)]
      rw [ite_eq_right (by
        rw [coe_finRotate_of_ne_last hne]
        have : (a : ℕ) < (b : ℕ) := hab'
        omega)]
    have hdiag : ((colJTMat t (m + 1) * negHMat t (m + 1)).submatrix
        (finRotate (m + 1)) id).det =
        -newtonH (fun c => -t c) (m + 1) := by
      rw [Matrix.det_of_isLowerTriangular _ htri]
      rw [Fin.prod_univ_castSucc]
      have hone : ∀ i : Fin m,
          ((colJTMat t (m + 1) * negHMat t (m + 1)).submatrix
            (finRotate (m + 1)) id) i.castSucc i.castSucc = 1 := by
        intro i
        have hne : i.castSucc ≠ Fin.last m :=
          (Fin.castSucc_lt_last i).ne
        rw [Matrix.submatrix_apply, id_eq]
        rw [colJT_mul_negH_pos t _ _ (by
          rw [coe_finRotate_of_ne_last hne]
          omega)]
        rw [ite_eq_left (by rw [coe_finRotate_of_ne_last hne])]
      rw [Finset.prod_congr rfl fun i _ => hone i,
        Finset.prod_const_one, one_mul]
      rw [Matrix.submatrix_apply, id_eq, finRotate_last]
      rw [colJT_mul_negH_zero t _ _ (by simp), Fin.val_last]
    have hperm := Matrix.det_permute (finRotate (m + 1))
      (colJTMat t (m + 1) * negHMat t (m + 1))
    rw [hdiag, hdetP, sign_finRotate] at hperm
    have hfin : (-1 : ℂ) ^ m * (colJTMat t (m + 1)).det =
        -newtonH (fun c => -t c) (m + 1) := by
      rw [hperm, Nat.add_sub_cancel]
      push_cast
      ring
    have hsq : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨m, rfl⟩
    calc (colJTMat t (m + 1)).det
        = ((-1 : ℂ) ^ m * (-1 : ℂ) ^ m) *
            (colJTMat t (m + 1)).det := by
          rw [hsq, one_mul]
      _ = (-1 : ℂ) ^ m *
            ((-1 : ℂ) ^ m * (colJTMat t (m + 1)).det) := by
          ring
      _ = (-1 : ℂ) ^ m * (-newtonH (fun c => -t c) (m + 1)) := by
          rw [hfin]
      _ = (-1 : ℂ) ^ (m + 1) * newtonH (fun c => -t c) (m + 1) := by
          ring

/-- The Schur specialisation of the single-column shape is the
elementary value. -/
theorem diagramSchur_colShape (n : ℕ) (t : ℕ → ℂ) :
    diagramSchur (colShape n).val t =
      (-1) ^ n * newtonH (fun c => -t c) n := by
  rw [diagramSchur, colShape_rowLens, schurDet_replicate_one,
    colJTMat_det]

/-! ### The signed cycle sum -/

/-- The product of alternating signs over a multiset. -/
private theorem prod_map_neg_one_pow (m : Multiset ℕ) :
    (m.map fun c => (-1 : ℂ) ^ (c + 1)).prod =
      (-1) ^ (m.sum + Multiset.card m) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih,
      Multiset.sum_cons, Multiset.card_cons, ← pow_add]
    congr 1
    omega

/-- The sign of a permutation times its completed cycle product is
the completed cycle product of the alternating twist. -/
theorem sign_mul_cycleProd (t : ℕ → ℂ) {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign π : ℤ) : ℂ) * cycleProd t π =
      cycleProd (fun c => (-1) ^ (c + 1) * t c) π := by
  change ((Equiv.Perm.sign π : ℤ) : ℂ) *
      ((π.cycleType.map t).prod * t 1 ^ (n - π.cycleType.sum)) =
    (π.cycleType.map fun c => (-1 : ℂ) ^ (c + 1) * t c).prod *
      ((-1 : ℂ) ^ (1 + 1) * t 1) ^ (n - π.cycleType.sum)
  rw [Multiset.prod_map_mul, prod_map_neg_one_pow,
    Equiv.Perm.sign_of_cycleType]
  push_cast
  ring

/-- **The signed cycle sum**: the sign-weighted completed cycle
products of all permutations sum to `n!` times the elementary
value. -/
theorem signed_cycleSum (t : ℕ → ℂ) (n : ℕ) :
    ∑ π : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign π : ℤ) : ℂ) * cycleProd t π =
      (n.factorial : ℂ) *
        ((-1) ^ n * newtonH (fun c => -t c) n) := by
  rw [Finset.sum_congr rfl fun π _ => sign_mul_cycleProd t π]
  rw [cycleSum_eq, newtonH_alt]

/-! ### Pinning the characters of the one-row and one-column
shapes -/

/-- A package character agreeing with a class function in all
Frobenius pairings is that class function. -/
theorem SchurPackage.char_eq_of_frobenius
    (P : SchurPackage.{u}) (μ : YoungDiagram)
    (χ : Equiv.Perm (Fin μ.card) → ℂ)
    (hconj : ∀ g c : Equiv.Perm (Fin μ.card), χ (c * g * c⁻¹) = χ g)
    (hsum : ∀ t : ℕ → ℂ,
      ∑ π : Equiv.Perm (Fin μ.card), χ π * cycleProd t π =
        (μ.card.factorial : ℂ) * diagramSchur μ t)
    (π : Equiv.Perm (Fin μ.card)) :
    P.char μ π = χ π := by
  have hconj' : ∀ g c : Equiv.Perm (Fin μ.card),
      P.char μ (c * g * c⁻¹) - χ (c * g * c⁻¹) =
        P.char μ g - χ g := by
    intro g c
    rw [P.char_conj μ g c, hconj g c]
  have hvan : ∀ t : ℕ → ℂ,
      ∑ π' : Equiv.Perm (Fin μ.card),
        (P.char μ π' - χ π') * cycleProd t π' = 0 := by
    intro t
    have hne : ((μ.card.factorial : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h1 : ∑ π' : Equiv.Perm (Fin μ.card),
        P.char μ π' * cycleProd t π' =
        (μ.card.factorial : ℂ) * diagramSchur μ t := by
      calc ∑ π' : Equiv.Perm (Fin μ.card),
            P.char μ π' * cycleProd t π'
          = (μ.card.factorial : ℂ) *
              (((μ.card.factorial : ℂ))⁻¹ *
                ∑ π' : Equiv.Perm (Fin μ.card),
                  P.char μ π' * cycleProd t π') := by
            rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
        _ = (μ.card.factorial : ℂ) * diagramSchur μ t := by
            rw [show ((μ.card.factorial : ℂ))⁻¹ *
                ∑ π' : Equiv.Perm (Fin μ.card),
                  P.char μ π' * cycleProd t π' =
                diagramSchur μ t from P.frobenius μ t]
    rw [Finset.sum_congr rfl fun π' _ =>
      sub_mul (P.char μ π') (χ π') (cycleProd t π')]
    rw [Finset.sum_sub_distrib, h1, hsum t, sub_self]
  exact sub_eq_zero.mp (classFun_eq_zero_of_cycleProd
    (fun π' => P.char μ π' - χ π') hconj' hvan π)

/-- The character of the single-row shape is constant one. -/
theorem SchurPackage.char_rowShape (P : SchurPackage.{u}) (n : ℕ)
    (π : Equiv.Perm (Fin (rowShape n).val.card)) :
    P.char (rowShape n).val π = 1 := by
  refine P.char_eq_of_frobenius (rowShape n).val (fun _ => 1)
    (fun _ _ => rfl) ?_ π
  intro t
  show ∑ π' : Equiv.Perm (Fin (rowShape n).val.card),
      (1 : ℂ) * cycleProd t π' = _
  simp only [one_mul]
  rw [cycleSum_eq, diagramSchur_rowShape, (rowShape n).prop]

/-- The character of the single-column shape is the sign. -/
theorem SchurPackage.char_colShape (P : SchurPackage.{u}) (n : ℕ)
    (π : Equiv.Perm (Fin (colShape n).val.card)) :
    P.char (colShape n).val π =
      ((Equiv.Perm.sign π : ℤ) : ℂ) := by
  refine P.char_eq_of_frobenius (colShape n).val
    (fun σ => ((Equiv.Perm.sign σ : ℤ) : ℂ)) ?_ ?_ π
  · intro g c
    have hs : Equiv.Perm.sign (c * g * c⁻¹) = Equiv.Perm.sign g := by
      rw [map_mul, map_mul, map_inv,
        mul_comm (Equiv.Perm.sign c) (Equiv.Perm.sign g),
        mul_assoc, mul_inv_cancel, mul_one]
    rw [hs]
  · intro t
    show ∑ π' : Equiv.Perm (Fin (colShape n).val.card),
        ((Equiv.Perm.sign π' : ℤ) : ℂ) * cycleProd t π' = _
    rw [signed_cycleSum, diagramSchur_colShape, (colShape n).prop]

/-! ### The idempotents -/

/-- The single-row dimension is one. -/
theorem SchurPackage.dim_rowShape (P : SchurPackage.{u}) (n : ℕ) :
    P.dim (rowShape n).val = 1 := by
  have h := P.char_one (rowShape n).val
  rw [P.char_rowShape n 1] at h
  exact_mod_cast h.symm

/-- The single-column dimension is one. -/
theorem SchurPackage.dim_colShape (P : SchurPackage.{u}) (n : ℕ) :
    P.dim (colShape n).val = 1 := by
  have h := P.char_one (colShape n).val
  rw [P.char_colShape n 1, map_one] at h
  have h1 : ((P.dim (colShape n).val : ℕ) : ℂ) =
      ((1 : ℕ) : ℂ) := by
    rw [← h]
    norm_num
  exact Nat.cast_injective h1

/-- `charIdempotent` at dimension one and the constant character:
the symmetriser. -/
theorem charIdempotent_const_one (n : ℕ) :
    charIdempotent (n := n) 1 (fun _ => (1 : ℂ)) =
      symmetriser n := by
  rw [charIdempotent, symmetriser]
  congr 1
  · rw [Nat.cast_one, one_div]
  · refine Finset.sum_congr rfl fun π _ => ?_
    show (1 : ℂ) • MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) π =
      MonoidAlgebra.single π (1 : ℂ)
    rw [one_smul, MonoidAlgebra.of_apply]

/-- `charIdempotent` at dimension one and the sign character: the
antisymmetriser. -/
theorem charIdempotent_sign (n : ℕ) :
    charIdempotent (n := n) 1
      (fun π => ((Equiv.Perm.sign π : ℤ) : ℂ)) =
      antisymmetriser n := by
  rw [charIdempotent, antisymmetriser]
  congr 1
  · rw [Nat.cast_one, one_div]
  · refine Finset.sum_congr rfl fun π _ => ?_
    show ((Equiv.Perm.sign π : ℤ) : ℂ) •
        MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) π =
      MonoidAlgebra.single π ((Equiv.Perm.sign π : ℤ) : ℂ)
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]

/-- The package idempotent of the single-row shape is the
symmetriser, at the native size. -/
theorem SchurPackage.e_rowShape (P : SchurPackage.{u}) (n : ℕ) :
    P.e (rowShape n).val = symmetriser (rowShape n).val.card := by
  rw [SchurPackage.e_def, P.dim_rowShape n,
    show P.char (rowShape n).val = (fun _ => (1 : ℂ)) from
      funext (P.char_rowShape n),
    charIdempotent_const_one]

/-- The package idempotent of the single-column shape is the
antisymmetriser, at the native size. -/
theorem SchurPackage.e_colShape (P : SchurPackage.{u}) (n : ℕ) :
    P.e (colShape n).val =
      antisymmetriser (colShape n).val.card := by
  rw [SchurPackage.e_def, P.dim_colShape n,
    show P.char (colShape n).val =
        (fun π => ((Equiv.Perm.sign π : ℤ) : ℂ)) from
      funext (P.char_colShape n),
    charIdempotent_sign]

/-- Recasting the symmetriser along an equality of sizes. -/
theorem symCast_symmetriser {m n : ℕ} (h : m = n) :
    symCast (le_of_eq h) (symmetriser m) = symmetriser n := by
  subst h
  exact symCast_le_refl _ _

/-- Recasting the antisymmetriser along an equality of sizes. -/
theorem symCast_antisymmetriser {m n : ℕ} (h : m = n) :
    symCast (le_of_eq h) (antisymmetriser m) = antisymmetriser n := by
  subst h
  exact symCast_le_refl _ _

end RS

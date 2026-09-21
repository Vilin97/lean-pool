/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.BinomialH
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.SquareStair

/-!
# Nonvanishing of square-diagram Schur values at constant sequences

The Jacobi–Trudi determinant for the square diagram at constant
power-sum sequences `m` (resp. `−m`) is nonzero.  The positive case
is proved here by a row-normalized product identity; the negated
case is stated as `SquareBinomialDetPos` and proved by the
Lindström–Gessel–Viennot argument of `LGVStrict.lean`.
-/

namespace RS

open Finset Matrix

/-! ## The hard core -/

/-- The negated case: the Jacobi–Trudi determinant for
`squareDiagram s` evaluated at the constant negative sequence `−m`
is nonzero whenever `s ≤ m`.

Equivalently (by sign extraction), the binomial Toeplitz determinant
`det [C(m, s+j−i)]_{0 ≤ i,j < s}` is nonzero for `m ≥ s`.

Proved as `squareBinomialDetPos` in `LGVStrict.lean`, by a
Lindström–Gessel–Viennot lattice-path count whose
non-intersecting-path formula is manifestly positive. -/
abbrev SquareBinomialDetPos : Prop :=
  ∀ (s m : ℕ), 1 ≤ s → s ≤ m →
    diagramSchur (squareDiagram s) (fun _ => -(m : ℂ)) ≠ 0

/-! ## Combinatorial tools -/

private theorem vandermonde_conv (a b n : ℕ) :
    Nat.choose (a + b) n =
    ∑ k ∈ Finset.range (n + 1),
      Nat.choose a (n - k) * Nat.choose b k := by
  calc Nat.choose (a + b) n
      = Nat.choose (b + a) n := by rw [show a + b = b + a from by omega]
    _ = ∑ ij ∈ Finset.antidiagonal n,
          Nat.choose b ij.1 * Nat.choose a ij.2 :=
        Nat.add_choose_eq b a n
    _ = ∑ k ∈ Finset.range (n + 1),
          Nat.choose b k * Nat.choose a (n - k) :=
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun p q => Nat.choose b p * Nat.choose a q) n
    _ = _ := Finset.sum_congr rfl (fun k _ => Nat.mul_comm _ _)

private theorem vandermonde_conv_trunc (s m : ℕ) (hm : s ≤ m)
    (a j : ℕ) (hj : j < s) :
    Nat.choose (a + j) (m - 1) =
    ∑ t ∈ Finset.range s,
      Nat.choose a (m - 1 - t) * Nat.choose j t := by
  rw [vandermonde_conv a j (m - 1), show m - 1 + 1 = m from by omega]
  symm; apply Finset.sum_subset (Finset.range_mono hm)
  intro t ht hts
  have : s ≤ t := by rw [Finset.mem_range] at hts; omega
  rw [Nat.choose_eq_zero_of_lt (show j < t by omega), Nat.mul_zero]

private theorem det_choose_upper (s : ℕ) :
    (Matrix.of fun t j : Fin s =>
      (Nat.choose (j : ℕ) (t : ℕ) : ℂ)).det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun t j (htj : id j < id t) => by
    rw [Matrix.of_apply]
    exact_mod_cast Nat.choose_eq_zero_of_lt htj)]
  simp [Matrix.of_apply, Nat.choose_self]

private theorem diagramSchur_empty (t : ℕ → ℂ) :
    diagramSchur (squareDiagram 0) t = 1 := by
  rw [diagramSchur, schurDet]
  have : (squareDiagram 0).rowLens = [] :=
    List.eq_nil_of_length_eq_zero (by rw [squareDiagram_rowLens,
      List.length_replicate])
  rw [this]; simp

private theorem descFactorial_add (n k l : ℕ) :
    n.descFactorial (k + l) =
    n.descFactorial k * (n - k).descFactorial l := by
  rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range,
    Nat.descFactorial_eq_prod_range, Finset.prod_range_add]
  congr 1; apply Finset.prod_congr rfl; intro i _; omega

/-! ## Positive case: the row-normalized product identity -/

/-- The core determinantal identity for `diagramSchur (squareDiagram s)`
at the constant sequence `m`.  Mirrors `diagramSchur_delta_mul`. -/
private theorem diagramSchur_square_const_mul (s m : ℕ) (hm : s ≤ m)
    (hs : 1 ≤ s) :
    diagramSchur (squareDiagram s) (fun _ => (m : ℂ)) *
      ∏ j : Fin s, (((m - 1 - (j : ℕ)).factorial : ℕ) : ℂ) =
    (∏ i : Fin s,
      (((m + s - 1 - (i : ℕ)).descFactorial (m - s) : ℕ) : ℂ)) *
    ∏ i : Fin s, ∏ j ∈ Finset.Ioi i,
      (((s + (j : ℕ) : ℕ) : ℂ) - ((s + (i : ℕ) : ℕ) : ℂ)) := by
  classical
  have hm1 : 1 ≤ m := by omega
  have hL : (squareDiagram s).rowLens.length = s :=
    square_rowLens_length s
  rw [diagramSchur, schurDet]
  set L := (squareDiagram s).rowLens.length with hLdef
  -- ═══════ SETUP: TRANSPORT THE PRODUCTS TO THE MATRIX INDEX ═══════
  -- Transport Fin s products to Fin L (matching matrix dimension)
  rw [show (∏ j : Fin s, (((m - 1 - (j : ℕ)).factorial : ℕ) : ℂ)) =
    (∏ j : Fin L, (((m - 1 - (j : ℕ)).factorial : ℕ) : ℂ)) from hL ▸ rfl,
    show (∏ i : Fin s,
      (((m + s - 1 - (i : ℕ)).descFactorial (m - s) : ℕ) : ℂ)) =
    (∏ i : Fin L,
      (((m + s - 1 - (i : ℕ)).descFactorial (m - s) : ℕ) : ℂ)) from hL ▸ rfl,
    show (∏ i : Fin s, ∏ j ∈ Finset.Ioi i,
      (((s + (j : ℕ) : ℕ) : ℂ) - ((s + (i : ℕ) : ℕ) : ℂ))) =
    (∏ i : Fin L, ∏ j ∈ Finset.Ioi i,
      (((s + (j : ℕ) : ℕ) : ℂ) - ((s + (i : ℕ) : ℕ) : ℂ))) from hL ▸ rfl]
  -- Now all products and the matrix are over Fin L
  set L_mat := Matrix.of fun (i t : Fin L) =>
    (Nat.choose (m + s - 1 - (i : ℕ)) (m - 1 - (t : ℕ)) : ℂ)
    with hLmat
  set U_mat := Matrix.of fun (t j : Fin L) =>
    (Nat.choose (j : ℕ) (t : ℕ) : ℂ) with hUmat
  -- ═══════ STAGE 1: THE PASCAL FACTORIZATION `A = L · U` ═══════
  have hAeq : (Matrix.of fun i j : Fin L =>
      newtonHZ (fun _ => (m : ℂ))
        (((squareDiagram s).rowLens.get i : ℤ) +
          (j : ℕ) - (i : ℕ))) = L_mat * U_mat := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.of_apply, hLmat, hUmat, Matrix.mul_apply]
    simp only [Matrix.of_apply]
    have hi : (i : ℕ) < s := by rw [← hL]; exact i.isLt
    have hj : (j : ℕ) < s := by rw [← hL]; exact j.isLt
    rw [List.get_eq_getElem, YoungDiagram.get_rowLens,
      rowLen_squareDiagram hi]
    have hpos : 0 ≤ (s : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) := by
      omega
    rw [newtonHZ, if_pos hpos]
    have harg : ((s : ℤ) + ↑↑j - ↑↑i).toNat =
        s + (j : ℕ) - (i : ℕ) := by omega
    rw [harg, newtonH_const]
    have hcompl :
        Nat.choose (m + (s + (j : ℕ) - (i : ℕ)) - 1)
          (s + (j : ℕ) - (i : ℕ)) =
        Nat.choose (m + s - 1 - (i : ℕ) + (j : ℕ)) (m - 1) := by
      rw [show m + (s + (j : ℕ) - (i : ℕ)) - 1 =
          m + s - 1 - (i : ℕ) + (j : ℕ) from by omega,
        show s + (j : ℕ) - (i : ℕ) =
          (m + s - 1 - (i : ℕ) + (j : ℕ)) - (m - 1) from by omega]
      exact Nat.choose_symm (by omega)
    -- Prove the full ℕ identity, then cast
    have hnat : Nat.choose (m + (s + (j : ℕ) - (i : ℕ)) - 1)
          (s + (j : ℕ) - (i : ℕ)) =
        ∑ t : Fin L, Nat.choose (m + s - 1 - (i : ℕ)) (m - 1 - (t : ℕ)) *
          Nat.choose ((j : ℕ)) (t : ℕ) := by
      rw [hcompl, vandermonde_conv_trunc s m hm
        (m + s - 1 - (i : ℕ)) ((j : ℕ)) hj,
        ← Fin.sum_univ_eq_sum_range]
      exact hL ▸ rfl
    exact_mod_cast hnat
  rw [hAeq, Matrix.det_mul]
  have hUdet : U_mat.det = 1 := by
    rw [hUmat, show L = s from hL]; exact det_choose_upper s
  rw [hUdet, mul_one]
  -- ═══════ STAGE 2: ROW-NORMALIZE AND SPLIT THE ENTRIES ═══════
  rw [mul_comm, ← Matrix.det_mul_row
    (fun j : Fin L => (((m - 1 - (j : ℕ)).factorial : ℕ) : ℂ))]
  have hEntryDF : ∀ (i j : Fin L),
      (((m - 1 - (j : ℕ)).factorial : ℕ) : ℂ) *
        (Nat.choose (m + s - 1 - (i : ℕ)) (m - 1 - (j : ℕ)) : ℂ) =
      ((m + s - 1 - (i : ℕ)).descFactorial (m - 1 - (j : ℕ)) : ℂ) := by
    intro i j
    have hnat : (m - 1 - (j : ℕ)).factorial *
        Nat.choose (m + s - 1 - (i : ℕ)) (m - 1 - (j : ℕ)) =
        (m + s - 1 - (i : ℕ)).descFactorial (m - 1 - (j : ℕ)) := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      exact Nat.mul_div_cancel' (Nat.factorial_dvd_descFactorial _ _)
    exact_mod_cast hnat
  have hDFsplit : ∀ (i j : Fin L),
      (m + s - 1 - (i : ℕ)).descFactorial (m - 1 - (j : ℕ)) =
      (m + s - 1 - (i : ℕ)).descFactorial (m - s) *
        (2 * s - 1 - (i : ℕ)).descFactorial (s - 1 - (j : ℕ)) := by
    intro i j
    have hi : (i : ℕ) < s := by rw [← hL]; exact i.isLt
    have hj : (j : ℕ) < s := by rw [← hL]; exact j.isLt
    rw [show m - 1 - (j : ℕ) = (m - s) + (s - 1 - (j : ℕ))
      from by omega, descFactorial_add]
    congr 1; congr 1; omega
  have h1 :
      (Matrix.of fun i j : Fin L =>
        (((m - 1 - (j : ℕ)).factorial : ℕ) : ℂ) *
        (Nat.choose (m + s - 1 - (i : ℕ)) (m - 1 - (j : ℕ)) : ℂ)).det =
      (∏ i : Fin L,
        (((m + s - 1 - (i : ℕ)).descFactorial (m - s) : ℕ) : ℂ)) *
      (Matrix.of fun i j : Fin L =>
        (descPochhammer ℂ (s - 1 - (j : ℕ))).eval
          ((2 * s - 1 - (i : ℕ) : ℕ) : ℂ)).det := by
    rw [← Matrix.det_mul_column
      (fun i : Fin L =>
        (((m + s - 1 - (i : ℕ)).descFactorial (m - s) : ℕ) : ℂ))]
    congr 1
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply]
    rw [hEntryDF i j, descPochhammer_eval_eq_descFactorial]
    push_cast [hDFsplit i j]; ring
  have h2 :
      (Matrix.of fun i j : Fin L =>
        (descPochhammer ℂ (s - 1 - (j : ℕ))).eval
          ((2 * s - 1 - (i : ℕ) : ℕ) : ℂ)).det =
      ∏ i : Fin L, ∏ j ∈ Finset.Ioi i,
        (((s + (j : ℕ) : ℕ) : ℂ) -
          ((s + (i : ℕ) : ℕ) : ℂ)) := by
    rw [← Matrix.det_submatrix_equiv_self
      (Fin.revPerm : Equiv.Perm (Fin L))]
    have hsub :
        (Matrix.of fun i j : Fin L =>
          (descPochhammer ℂ (s - 1 - (j : ℕ))).eval
            ((2 * s - 1 - (i : ℕ) : ℕ) : ℂ)).submatrix
          (⇑Fin.revPerm) (⇑Fin.revPerm) =
        Matrix.of fun i j : Fin L =>
          (descPochhammer ℂ (j : ℕ)).eval
            ((s + (i : ℕ) : ℕ) : ℂ) := by
      refine Matrix.ext fun i j => ?_
      rw [Matrix.submatrix_apply, Matrix.of_apply, Matrix.of_apply]
      have hri : ((Fin.revPerm i : Fin L) : ℕ) =
          L - ((i : ℕ) + 1) := Fin.val_rev i
      have hrj : ((Fin.revPerm j : Fin L) : ℕ) =
          L - ((j : ℕ) + 1) := Fin.val_rev j
      have hi := i.isLt
      have hj := j.isLt
      have hLs : L = s := hL
      rw [hrj, hri]
      have hd : s - 1 - (L - ((j : ℕ) + 1)) = (j : ℕ) := by omega
      have he : 2 * s - 1 - (L - ((i : ℕ) + 1)) = s + (i : ℕ) := by omega
      rw [hd, he]
    rw [hsub, det_descPochhammer_eval]
  -- ═══════ ASSEMBLY ═══════
  -- Unfold L_mat so the goal matches h1
  simp only [hLmat, Matrix.of_apply]
  rw [h1, h2]

/-! ## Positive case: nonvanishing -/

/-- The square-diagram Schur value at the constant sequence `m` is
a positive rational. -/
theorem diagramSchur_square_const_pos (s m : ℕ) (hm : s ≤ m) :
    ∃ N D : ℕ, 0 < N ∧ 0 < D ∧
      (D : ℂ) * diagramSchur (squareDiagram s) (fun _ => (m : ℂ)) =
        (N : ℂ) := by
  classical
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · exact ⟨1, 1, Nat.one_pos, Nat.one_pos, by
      rw [diagramSchur_empty]; push_cast; ring⟩
  have hid := diagramSchur_square_const_mul s m hm hs
  -- Rewrite the ℂ-differences as ℕ casts
  have hdiff : ∀ (i : Fin s) (j : Fin s), j ∈ Finset.Ioi i →
      (((s + (j : ℕ) : ℕ) : ℂ) - ((s + (i : ℕ) : ℕ) : ℂ)) =
      (((j : ℕ) - (i : ℕ) : ℕ) : ℂ) := by
    intro i j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hij' : (i : ℕ) < (j : ℕ) := hij
    push_cast [Nat.cast_sub (Nat.le_of_lt hij')]
    ring
  rw [Finset.prod_congr rfl (fun i _ =>
    Finset.prod_congr rfl (hdiff i))] at hid
  set D := ∏ j : Fin s, (m - 1 - (j : ℕ)).factorial with hD_def
  set R := ∏ i : Fin s,
    (m + s - 1 - (i : ℕ)).descFactorial (m - s) with hR_def
  set V := ∏ i : Fin s, ∏ j ∈ Finset.Ioi i,
    ((j : ℕ) - (i : ℕ)) with hV_def
  have hD_pos : 0 < D :=
    Finset.prod_pos fun j _ => Nat.factorial_pos _
  have hR_pos : 0 < R := by
    apply Finset.prod_pos; intro i _
    rw [Nat.descFactorial_eq_prod_range]
    apply Finset.prod_pos; intro t ht
    rw [Finset.mem_range] at ht; have := i.isLt; omega
  have hV_pos : 0 < V := by
    apply Finset.prod_pos; intro i _
    apply Finset.prod_pos; intro j hj
    have : i < j := Finset.mem_Ioi.mp hj
    have hij : (i : ℕ) < (j : ℕ) := this
    omega
  refine ⟨R * V, D, Nat.mul_pos hR_pos hV_pos, hD_pos, ?_⟩
  show (D : ℂ) * diagramSchur (squareDiagram s)
      (fun _ => (m : ℂ)) = ((R * V : ℕ) : ℂ)
  rw [hD_def, hR_def, hV_def]
  push_cast
  linear_combination hid

/-- The square-diagram Schur value at the constant sequence `m`
does not vanish. -/
theorem diagramSchur_square_const_ne_zero (s m : ℕ) (hm : s ≤ m) :
    diagramSchur (squareDiagram s) (fun _ => (m : ℂ)) ≠ 0 := by
  obtain ⟨N, D, hN, hD, hDet⟩ := diagramSchur_square_const_pos s m hm
  intro h; rw [h, mul_zero] at hDet
  exact absurd (show (N : ℕ) = 0 from by exact_mod_cast hDet.symm) (by omega)

/-! ## Negative case -/

/-- The square-diagram Schur value at the negated constant
sequence `−m` does not vanish. -/
theorem diagramSchur_square_neg_const_ne_zero
    (H : SquareBinomialDetPos) (s m : ℕ) (hm : s ≤ m) :
    diagramSchur (squareDiagram s) (fun _ => -(m : ℂ)) ≠ 0 := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · rw [diagramSchur_empty]; exact one_ne_zero
  · exact H s m hs hm

end RS

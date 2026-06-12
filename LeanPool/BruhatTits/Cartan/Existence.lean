/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import LeanPool.BruhatTits.Utils.RingHom
import LeanPool.BruhatTits.Utils.Matrix
import LeanPool.BruhatTits.Utils.Misc
import LeanPool.BruhatTits.Utils.ValuationRings
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Transvection

/-!

# The Cartan Decomposition of GL(n,K) for K a discretely valued field

We establish the Cartan decomposition of `GL(n,K)` for `K` a discretely valued field.

Given `K` as the fraction field of a DVR `R` with uniformizer `ϖ`, the Cartan decomposition
says that any matrix `g ∈ GL(n,K)` can be written as a product `k_1 * diag * k_2`, where
`k_i ∈ GL(n,R)` and `diag` is a diagonal matrix with entries increasing powers of the
uniformizer.

There is an analogue where one uses decreasing powers instead, both versions are used in
mathematics. We only show the "increasing" version.

Most of the linear algebra preparations below are for arbitrary valuation rings.
Only from line 628 onwards we specialize to DVRs.

## Implementation details

This is inspired by the file https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Transvection.html.

-/

open Module


-- Let R be a valuation ring and K its field of fractions
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]

local notation "v" => ValuationRing.valuation R K

attribute [-simp] Subring.coe_subtype

/-- We can normalize any `g : Matrix (Fin k) (Fin k) K` such that the coefficient on the bottom
right has maximal valuation. -/
lemma exists_normalization0 {k : ℕ+} (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K) :
    ∃ (k₁ k₂ : GL (Fin k ⊕ Unit) R),
    v ((k₁.val * g * k₂.val) (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v := by
  -- the maximal element is in row `p.1` and column `p.2`
  let p := g.coeffsSupAt v
  -- swap `i`-th row with last row and `j`-th col with last col
  refine ⟨.swap R (Sum.inr ()) p.1, .swap R (Sum.inr ()) p.2, ?_⟩
  simp only [Matrix.GeneralLinearGroup.val_swap, Matrix.map_swap, Matrix.mul_swap_apply_left,
    Matrix.swap_mul_apply_left]
  rw [← Matrix.coeffs_sup_at_sup]

/-- We can normalize any `g : Matrix (Fin k) (Fin k) K` such that the coefficient on the bottom
right has maximal valuation and the maximal valuation is unchanged. -/
lemma exists_normalization0' {k : ℕ+} (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K) :
    ∃ (k₁ k₂ : GL (Fin k ⊕ Unit) R),
    v ((k₁.val * g * k₂.val) (Sum.inr ()) (Sum.inr ())) = (k₁.val * g * k₂.val).coeffsSup v
    ∧ (k₁.val * g * k₂.val).coeffsSup v = g.coeffsSup v := by
  -- the maximal element is in row `p.1` and column `p.2`
  let p := g.coeffsSupAt v
  -- swap `i`-th row with last row and `j`-th col with last col
  let k₁ := Matrix.GeneralLinearGroup.swap R (Sum.inr ()) p.1
  let k₂ := Matrix.GeneralLinearGroup.swap R (Sum.inr ()) p.2
  have hv : v ((k₁.val * g * k₂.val) (Sum.inr ()) (Sum.inr ())) =
      (k₁.val * g * k₂.val).coeffsSup v := by
    simp only [Matrix.GeneralLinearGroup.val_swap, Matrix.map_swap, Matrix.mul_swap_apply_left,
      Matrix.swap_mul_apply_left, Matrix.coeffs_sup_mul_swap, Matrix.coeffs_sup_swap_mul, k₁, p, k₂]
    rw [← Matrix.coeffs_sup_at_sup]
  refine ⟨.swap R (Sum.inr ()) p.1, .swap R (Sum.inr ()) p.2, hv, ?_⟩
  · rw [← hv]
    simp only [Matrix.GeneralLinearGroup.val_swap, Matrix.map_swap, Matrix.mul_swap_apply_left,
      Matrix.swap_mul_apply_left, k₁, p, k₂]
    rw [← Matrix.coeffs_sup_at_sup]

/-- The maximal valuation of the coefficients of any element of `GL (Fin k) K` is non-zero. -/
lemma sup_val_non_zero {k : ℕ+} (g : GL (Fin k) K) : g.val.coeffsSup v ≠ 0 := by
  intro h
  have hzero (i j : Fin k) : g i j = 0 := by
    have h2 : v (g i j) ≤ g.val.coeffsSup v := Matrix.coeff_le_coeffs_sup v g.val i j
    simpa [h] using h2
  apply Units.ne_zero g
  ext i j
  simp only [hzero, Matrix.zero_apply]

open Matrix

variable {k l : ℕ+}

noncomputable section

/-- The element of `R` used to eliminate the last row and column of `g` if
the coefficient in the bottom-right has maximal valuation. -/
def multFactor (g : Matrix (Fin k ⊕ Unit) (Fin l ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) (j : Fin l) : R :=
  letI := Classical.typeDecidableEq K
  let x : K := g (Sum.inr ()) (Sum.inl j)
  have hvxvg : v x ≤ v (g (Sum.inr ()) (Sum.inr ())) := by
    rw [h]
    apply Matrix.coeff_le_coeffs_sup
  have hmem (hn : g (Sum.inr ()) (Sum.inr ()) ≠ 0) :
      -x * (g (Sum.inr ()) (Sum.inr ()))⁻¹ ∈ R := by
    simp only [mem_subring_iff_integer, neg_mul, Valuation.map_neg, _root_.map_mul, map_inv₀]
    have hnz : v (g (Sum.inr ()) (Sum.inr ())) ≠ 0 := (Valuation.ne_zero_iff v).mpr hn
    rw [← div_eq_mul_inv]
    exact div_le_one_of_le₀ hvxvg zero_le
  if hn : g (Sum.inr ()) (Sum.inr ()) = 0 then 0
  else ⟨- x * (g (Sum.inr ()) (Sum.inr ()))⁻¹, hmem hn⟩

lemma multFactor_mul (g : Matrix (Fin k ⊕ Unit) (Fin l ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) (j : Fin l) :
    g (Sum.inr ()) (Sum.inl j) + multFactor g h j * g (Sum.inr ()) (Sum.inr ()) = 0 := by
  simp only [multFactor, neg_mul]
  split
  · next h1 =>
      simpa [← h, h1] using Matrix.coeff_le_coeffs_sup v g (Sum.inr ()) (Sum.inl j)
  · next h1 =>
      rw [neg_mul, mul_assoc]
      simp [inv_mul_cancel₀ h1]

/-- The transvection struct in `R` for the transvection eliminating the `j`-th entry in the last
row of `g`, where the bottom-right element of `g` has maximal valuation. -/
def rowEliminationTransvection (g : Matrix (Fin k ⊕ Unit) (Fin l ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) (j : Fin l) :
    TransvectionStruct (Fin l ⊕ Unit) R :=
  ⟨Sum.inr (), Sum.inl j, Sum.inr_ne_inl, multFactor g h j⟩

lemma rowEliminationTransvection_mul_same (g : Matrix (Fin l ⊕ Unit) (Fin l ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) (j : Fin l) (a : Fin l ⊕ Unit) :
    (g * (rowEliminationTransvection g h j).toMatrix.map R.subtype) a (Sum.inl j)
      = g a (Sum.inl j) + multFactor g h j * g a (Sum.inr ()) := by
  simp only [rowEliminationTransvection, TransvectionStruct.toMatrix_mk,
    map_transvection, mul_transvection_apply_same, add_right_inj]
  rfl

lemma rowEliminationTransvection_mul_neq {g : Matrix (Fin l ⊕ Unit) (Fin l ⊕ Unit) K}
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) (j : Fin l) (a b : Fin l ⊕ Unit)
    (hb : b ≠ Sum.inl j) :
    (g * (rowEliminationTransvection g h j).toMatrix) a b = g a b := by
  simp only [rowEliminationTransvection, TransvectionStruct.toMatrix_mk, map_transvection]
  rw [Matrix.mul_transvection_apply_of_ne]
  simpa using hb

/-- Multiplying on the right with `rowEliminationTransvection` kills all elements in the first row
but the first. -/
lemma rowEliminationTransvection_mul (g : Matrix (Fin l ⊕ Unit) (Fin l ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) (j : Fin l) :
    (g * (rowEliminationTransvection g h j).toMatrix) (Sum.inr ()) (Sum.inl j) = 0 := by
  simp only [rowEliminationTransvection, TransvectionStruct.toMatrix_mk, map_transvection,
    mul_transvection_apply_same]
  exact multFactor_mul g h j

lemma rowEliminationTransvection_mul_coeffs_sup' (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) (j : Fin k) (c : R) :
    v ((g * transvection (Sum.inr ()) (Sum.inl j) (c : K)) (Sum.inr ()) (Sum.inr ())) =
      (g * transvection (Sum.inr ()) (Sum.inl j) (c : K)).coeffsSup v := by
  apply le_antisymm
  · apply Matrix.coeff_le_coeffs_sup
  · apply Matrix.coeffs_sup_le
    intro a b
    by_cases he : b = Sum.inl j
    · subst he
      simp only [mul_transvection_apply_same, ne_eq, reduceCtorEq, not_false_eq_true,
        mul_transvection_apply_of_ne]
      trans
      · apply Valuation.map_add
      · simp only [_root_.map_mul, max_le_iff]
        constructor
        · rw [h]
          apply Matrix.coeff_le_coeffs_sup
        · have : (ValuationRing.valuation R K) c ≤ 1 := by
            rw [← mem_subring_iff_integer]
            simp only [SetLike.coe_mem]
          trans
          · apply mul_le_mul' this (by rfl)
          · rw [one_mul, h]
            apply Matrix.coeff_le_coeffs_sup
    · simp only [ne_eq, reduceCtorEq, not_false_eq_true, mul_transvection_apply_of_ne]
      rw [mul_transvection_apply_of_ne _ _ _ _ he, h]
      apply Matrix.coeff_le_coeffs_sup

/-- After multiplying on the right with `rowEliminationTransvection`, the maximal valuation
of the coefficients does not change. -/
lemma rowEliminationTransvection_mul_coeffs_sup (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) (j : Fin k) :
    g.coeffsSup v =
      (g * (rowEliminationTransvection g h j).toMatrix).coeffsSup v := by
  apply le_antisymm
  · rw [← h, ← rowEliminationTransvection_mul_neq h j _ _ Sum.inr_ne_inl]
    apply Matrix.coeff_le_coeffs_sup
  · apply Matrix.coeffs_sup_le
    intro a b
    by_cases he : b = Sum.inl j
    · subst he
      rw [rowEliminationTransvection_mul_same]
      trans
      · apply Valuation.map_add
      · rw [_root_.map_mul, max_le_iff]
        constructor
        · apply Matrix.coeff_le_coeffs_sup
        · have : (ValuationRing.valuation R K) (multFactor g h j) ≤ 1 := by
            simp [← mem_subring_iff_integer, SetLike.coe_mem]
          trans
          · apply mul_le_mul' this (by rfl)
          · rw [one_mul]
            apply Matrix.coeff_le_coeffs_sup
    · rw [rowEliminationTransvection_mul_neq h j _ _ he]
      apply Matrix.coeff_le_coeffs_sup

/-- The row transvections used to eliminate the last row away from the diagonal. -/
def rowEliminationList (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) :
    List (Matrix.TransvectionStruct (Fin k ⊕ Unit) R) :=
  List.ofFn (fun j : Fin k ↦ rowEliminationTransvection g h j)

/-- The matrix form of `rowEliminationList`. -/
def rowEliminationListMatrix (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) :
    List (Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K) :=
  List.ofFn (fun j : Fin k ↦ (rowEliminationTransvection g h j).toMatrix)

attribute [-simp] Fin.natCast_eq_last Fin.coe_eq_castSucc

lemma rowEliminationList_get (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) (n : Fin k) :
    (rowEliminationListMatrix g h)[n]? =
      (some <| transvection (Sum.inr ()) (Sum.inl n) (multFactor g h n)) := by
  simp [rowEliminationListMatrix, rowEliminationTransvection]

lemma mul_rowEliminationListMatrix_prod_apply_lastCol_aux
    (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) (j : Fin k ⊕ Unit)
    {r : ℕ} (hr : r ≤ k) :
    (g * ((rowEliminationListMatrix g h).take r).prod) j (Sum.inr ()) = g j (Sum.inr ()) := by
  induction r with
  | zero =>
    simp
  | succ n ih =>
    let n' : Fin k := ⟨n, hr⟩
    erw [List.take_add_one, List.prod_append, rowEliminationList_get g h n']
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      map_transvection, Option.toList_some, List.prod_cons, List.prod_nil, mul_one]
    rw [← mul_assoc, mul_transvection_apply_of_ne, ih (by omega)]
    exact Sum.inr_ne_inl

lemma mul_rowEliminationListMatrix_prod_apply_lastCol (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) (j : Fin k ⊕ Unit) :
    (g * (rowEliminationListMatrix g h).prod) j (Sum.inr ()) = g j (Sum.inr ()) := by
  have hl : (rowEliminationListMatrix g h).length = k := by simp [rowEliminationListMatrix]
  rw [← List.take_length (l := rowEliminationListMatrix g h), hl]
  rw [mul_rowEliminationListMatrix_prod_apply_lastCol_aux g h j le_rfl]

lemma mul_rowEliminationListMatrix_prod_apply_aux
    (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) (j : Fin k) (r : ℕ)
    (hrk : r ≤ k) :
    (g * ((rowEliminationListMatrix g h).take r).prod) (Sum.inr ()) (Sum.inl j) =
      if r ≤ j then g (Sum.inr ()) (Sum.inl j) else 0 := by
  induction r with
  | zero =>
    simp
  | succ n ih =>
    let n' : Fin k := ⟨n, hrk⟩
    erw [List.take_add_one, List.prod_append, rowEliminationList_get g h n']
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, map_transvection,
      Option.toList_some, List.prod_cons, List.prod_nil, mul_one]
    have hnk : n ≤ k := by omega
    rw [← Matrix.mul_assoc]
    by_cases he : n' = j
    · subst he
      rw [mul_transvection_apply_same, ih hnk]
      simp only [le_refl, ↓reduceIte, Subring.subtype_apply, add_le_iff_nonpos_right,
        nonpos_iff_eq_zero, one_ne_zero, n']
      rw [mul_rowEliminationListMatrix_prod_apply_lastCol_aux _ _ _ hnk]
      apply multFactor_mul g h n'
    · have hni : n ≠ j := by
        intro hc
        apply he
        ext
        exact hc
      rw [mul_transvection_apply_of_ne, ih hnk]
      · by_cases hi : n + 1 ≤ (j : ℕ)
        · simp only [n.le_succ.trans hi, ↓reduceIte, hi]
        · rw [if_neg, if_neg]
          · simpa using hi
          · intro hnj
            apply hni
            omega
      · simpa using (Ne.symm he)

lemma mul_rowEliminationListMatrix_prod_apply (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) (j : Fin k) :
    (g * ((rowEliminationListMatrix g h).prod)) (Sum.inr ()) (Sum.inl j) = 0 := by
  have hl : (rowEliminationListMatrix g h).length = k := by simp [rowEliminationListMatrix]
  rw [← List.take_length (l := rowEliminationListMatrix g h), hl]
  rw [mul_rowEliminationListMatrix_prod_apply_aux g h j k le_rfl]
  simp

/-- The product of row transvections eliminating the last row away from the diagonal. -/
def rowEliminator (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) : GL (Fin k ⊕ Unit) R :=
  (List.map (fun t ↦ TransvectionStruct.toGL t) (rowEliminationList g h)).prod

lemma mul_rowEliminator_lastRow (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) (j : Fin k) :
    (g * (rowEliminator g h).val) (Sum.inr ()) (Sum.inl j) = 0 := by
  dsimp only [rowEliminator]
  rw [← map_listProd_toGL]
  simp only [rowEliminationList, List.map_ofFn]
  apply mul_rowEliminationListMatrix_prod_apply g h j

lemma mul_rowEliminator_lastCol (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) (j : Fin k ⊕ Unit) :
    (g * (rowEliminator g h).val) j (Sum.inr ()) = g j (Sum.inr ()) := by
  dsimp only [rowEliminator]
  rw [← map_listProd_toGL]
  simp only [rowEliminationList, List.map_ofFn]
  apply mul_rowEliminationListMatrix_prod_apply_lastCol g h j

/-- The column eliminator, defined by transposing and applying the row eliminator. -/
def colEliminator (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) :
    GL (Fin k ⊕ Unit) R :=
  have : v (g.transpose (Sum.inr ()) (Sum.inr ())) = g.transpose.coeffsSup v := by
    simpa [coeffs_sup_transpose]
  GL.transpose <| rowEliminator g.transpose this

lemma colEliminator_mul_lastCol (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr k) (Sum.inr k)) = g.coeffsSup v) (j : Fin k) :
    ((colEliminator g h).val * g) (Sum.inl j) (Sum.inr ()) = 0 := by
  rw [← transpose_apply (((colEliminator g h).val.map R.subtype) * g) (Sum.inr ()) (Sum.inl j),
    Matrix.transpose_mul]
  apply mul_rowEliminator_lastRow

lemma colEliminator_mul_lastRow (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) (j : Fin k ⊕ Unit) :
    ((colEliminator g h).val * g) (Sum.inr ()) j = g (Sum.inr ()) j := by
  rw [← transpose_apply (((colEliminator g h).val.map R.subtype) * g) j (Sum.inr ()),
    Matrix.transpose_mul]
  apply mul_rowEliminator_lastCol

lemma mul_rowEliminationListMatrix_coeffs_sup_aux (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) (r : ℕ) (hrk : r ≤ k) :
    v ((g * ((rowEliminationListMatrix g h).take r).prod) (Sum.inr ()) (Sum.inr ()))
      = (g * ((rowEliminationListMatrix g h).take r).prod).coeffsSup v := by
  induction r with
  | zero =>
    simpa
  | succ n ih =>
    let n' : Fin k := ⟨n, hrk⟩
    erw [List.take_add_one, List.prod_append, rowEliminationList_get g h n']
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, map_transvection,
      Option.toList_some, List.prod_cons, List.prod_nil, mul_one]
    rw [← mul_assoc]
    apply rowEliminationTransvection_mul_coeffs_sup'
    apply ih
    omega

lemma mul_rowEliminationListMatrix_coeffs_sup (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) :
    v ((g * (rowEliminationListMatrix g h).prod) (Sum.inr ()) (Sum.inr ()))
      = (g * (rowEliminationListMatrix g h).prod).coeffsSup v := by
  have hl : (rowEliminationListMatrix g h).length = k := by simp [rowEliminationListMatrix]
  rw [← List.take_length (l := rowEliminationListMatrix g h), hl]
  rw [mul_rowEliminationListMatrix_coeffs_sup_aux g h k le_rfl]

lemma mul_rowEliminator_coeffs_sup (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) :
    v ((g * (rowEliminator g h).val) (Sum.inr ()) (Sum.inr ()))
      = (g * (rowEliminator g h).val).coeffsSup v := by
  dsimp only [rowEliminator]
  rw [← map_listProd_toGL]
  simp only [rowEliminationList, List.map_ofFn]
  apply mul_rowEliminationListMatrix_coeffs_sup

lemma colEliminator_mul_coeffs_sup (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) :
    v (((colEliminator g h).val * g) (Sum.inr ()) (Sum.inr ()))
      = ((colEliminator g h).val * g).coeffsSup v := by
  simp only [colEliminator, GL.val_transpose]
  rw [← transpose_apply
    (((rowEliminator g.transpose _).val).transpose.map ⇑R.subtype * g) (Sum.inr ()) (Sum.inr ())]
  rw [transpose_mul]
  rw [← coeffs_sup_transpose]
  rw [transpose_mul]
  rw [transpose_map, transpose_transpose]
  apply mul_rowEliminator_coeffs_sup

lemma rowEliminator_colEliminator (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) :
    rowEliminator (((colEliminator g h).val : Matrix _ _ K) * g)
      (colEliminator_mul_coeffs_sup g h) =
      rowEliminator g h := by
  classical
  simp [rowEliminator, rowEliminationList, rowEliminationTransvection, multFactor,
    colEliminator_mul_lastRow]

lemma colEliminator_rowEliminator (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) :
    colEliminator (g * (↑(rowEliminator g h).val : Matrix _ _ K))
      (mul_rowEliminator_coeffs_sup g h) =
      colEliminator g h := by
  simp only [colEliminator, transpose_mul]
  apply congrArg
  apply rowEliminator_colEliminator

lemma colEliminator_mul_rowEliminator_lastRow (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) (j : Fin k) :
    ((colEliminator g h).val * g * (rowEliminator g h).val) (Sum.inr ()) (Sum.inl j) = 0 := by
  rw [← rowEliminator_colEliminator]
  apply mul_rowEliminator_lastRow

lemma colEliminator_mul_rowEliminator_lastCol (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) (j : Fin k) :
    ((colEliminator g h).val * g * (rowEliminator g h).val) (Sum.inl j) (Sum.inr ()) = 0 := by
  rw [← colEliminator_rowEliminator, mul_assoc]
  apply colEliminator_mul_lastCol

lemma colEliminator_mul_rowEliminator_last_last (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) :
    ((colEliminator g h).val * g * (rowEliminator g h).val) (Sum.inr ()) (Sum.inr ()) =
      g (Sum.inr ()) (Sum.inr ()) := by
  rw [← colEliminator_rowEliminator, mul_assoc, colEliminator_mul_lastRow,
    mul_rowEliminator_lastCol]

lemma colEliminator_mul_rowEliminator_coeffs_sup (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) :
    ((colEliminator g h).val * g * (rowEliminator g h).val).coeffsSup v = g.coeffsSup v := by
  rwa [← rowEliminator_colEliminator, ← mul_rowEliminator_coeffs_sup, mul_rowEliminator_lastCol,
    colEliminator_mul_lastRow]

/-- A `(k + 1) × (k + 1)` matrix is of normal block form, if it is block diagonal and
the bottom-right coefficient has maximal valuation. -/
structure IsNormalBlock (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K) : Prop where
  isTwoBlockDiagonal : IsTwoBlockDiagonal g
  monotone : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v


lemma exists_trafo_isNormalBlock (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K) :
    ∃ (k₁ k₂ : GL (Fin k ⊕ Unit) R),
    IsNormalBlock (R := R) ((k₁.val : Matrix _ _ K) * g * (k₂.val : Matrix _ _ K)) ∧
      ((k₁.val : Matrix _ _ K) * g * (k₂.val : Matrix _ _ K)).coeffsSup v = g.coeffsSup v := by
  obtain ⟨a, b, hagb, hagbv⟩ := exists_normalization0' (R := R) g
  let g' : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K := a.val * g * b.val
  have hg' : v (g' (Sum.inr ()) (Sum.inr ())) = g'.coeffsSup v := hagb
  let k₁ := colEliminator g' hg' * a
  let k₂ := b * rowEliminator g' hg'
  use k₁
  use k₂
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · ext j _
    simp only [Units.val_mul, Matrix.map_mul, zero_apply, k₁, k₂]
    convert_to
      ((colEliminator g' hg').val * g' * (rowEliminator g' hg').val) (Sum.inl j)
        (Sum.inr ()) = 0
    · simp only [toBlocks₁₂, of_apply, g']
      group
    · apply colEliminator_mul_rowEliminator_lastCol
  · ext _ j
    simp only [Units.val_mul, Matrix.map_mul, zero_apply, k₁, k₂]
    convert_to
      ((colEliminator g' hg').val * g' * (rowEliminator g' hg').val) (Sum.inr ())
        (Sum.inl j) = 0
    · simp only [toBlocks₂₁, of_apply, g']
      group
    · apply colEliminator_mul_rowEliminator_lastRow
  · simp only [Units.val_mul, Matrix.map_mul, k₁, k₂]
    convert_to
      v (((colEliminator g' hg').val * g' * (rowEliminator g' hg').val) (Sum.inr ())
        (Sum.inr ())) =
        ((colEliminator g' hg').val * g' * (rowEliminator g' hg').val).coeffsSup v
    · simp only [g']
      group
    · simp only [g']
      group
    · rw [colEliminator_mul_rowEliminator_coeffs_sup]
      rwa [colEliminator_mul_rowEliminator_last_last]
  · simp only [Units.val_mul, Matrix.map_mul, k₁, k₂]
    convert_to ((colEliminator g' hg').val * g' * (rowEliminator g' hg').val).coeffsSup v =
        g.coeffsSup v
    · simp only [g']
      group
    · rw [colEliminator_mul_rowEliminator_coeffs_sup]
      exact hagbv

/-- A matrix is monotone diagonal if it is diagonal and the coefficients on the diagonal
have monotonically increasing valuations. -/
structure IsMonotoneDiag {n : Type*} [Fintype n] [Preorder n] (g : Matrix n n K) : Prop where
  isDiag : IsDiag g
  monotone : Monotone (fun j ↦ v (g j j))

/-- An equivalent spelling of `IsMonotoneDiag` for `(k + 1) × (k + 1)`-matrices. -/
structure IsBlockMonotoneDiag (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K) : Prop where
  isDiag : IsDiag g
  monotone : Monotone (fun (j : Fin k) ↦ v (g (Sum.inl j) (Sum.inl j)))
  max_bot_right : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v

lemma monotone_of_isBlockMonotoneDiag (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (hb : IsBlockMonotoneDiag (R := R) g) :
    Monotone fun j ↦ v (g (Fin.succEquivUnit k j) (Fin.succEquivUnit k j)) := by
  intro i j hij
  simp only [Fin.succEquivUnit_apply]
  split_ifs
  · apply hb.monotone
    simpa
  · rw [hb.max_bot_right]
    apply coeff_le_coeffs_sup
  · omega
  · rfl

lemma exists_trafo_isDiag_induction_step (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (ih : ∀ (h : Matrix (Fin k) (Fin k) K), ∃ (k₁ k₂ : GL (Fin k) R),
      IsMonotoneDiag (R := R) ((k₁.val : Matrix _ _ K) * h * (k₂.val : Matrix _ _ K)) ∧
      ((k₁.val : Matrix _ _ K) * h * (k₂.val : Matrix _ _ K)).coeffsSup v = h.coeffsSup v) :
    ∃ (k₁ k₂ : GL (Fin k ⊕ Unit) R),
    IsBlockMonotoneDiag (R := R) ((k₁.val : Matrix _ _ K) * g * (k₂.val : Matrix _ _ K)) ∧
      ((k₁.val : Matrix _ _ K) * g * (k₂.val : Matrix _ _ K)).coeffsSup v = g.coeffsSup v := by
  obtain ⟨h₁, h₂, hh, hvc⟩ := exists_trafo_isNormalBlock (R := R) g
  let g' : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K :=
    (h₁.val : Matrix _ _ K) * g * (h₂.val : Matrix _ _ K)
  let h : Matrix (Fin k) (Fin k) K := toBlocks₁₁ g'
  obtain ⟨l₁, l₂, hl, hv⟩ := ih h
  let l₁' : GL (Fin k ⊕ Unit) R := GL.diagonalBlocks l₁ 1
  let l₂' : GL (Fin k ⊕ Unit) R := GL.diagonalBlocks l₂ 1
  use l₁' * h₁
  use h₂ * l₂'
  simp only [Units.val_mul, Matrix.map_mul]
  have he : g' = Matrix.fromBlocks h 0 0 (fun _ _ ↦ (g' (Sum.inr ()) (Sum.inr ()))) := by
    rw [Matrix.ext_iff_blocks]
    simp only [toBlocks_fromBlocks₁₁, hh.isTwoBlockDiagonal.left, toBlocks_fromBlocks₁₂,
      hh.isTwoBlockDiagonal.right, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, true_and, g', h]
    rfl
  convert_to IsBlockMonotoneDiag (R := R) ((l₁'.val : Matrix _ _ K) * g' * (l₂'.val : Matrix _ _ K))
    ∧ ((l₁'.val : Matrix _ _ K) * g' * (l₂'.val : Matrix _ _ K)).coeffsSup v = g.coeffsSup v
  · simp only [g']
    group
  · simp only [g']
    group
  · rw [he]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simp only [GL.val_diagonalBlocks, Units.val_one, l₁', l₂']
      rw [Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
        Matrix.fromBlocks_multiply]
      simp only [map_zero, Matrix.map_zero, Matrix.mul_zero, add_zero, Matrix.zero_mul,
        _root_.map_one, Matrix.map_one, Matrix.mul_one, one_mul, zero_add, mul_one]
      apply Matrix.IsDiag.fromBlocks hl.isDiag
      · apply isDiag_of_subsingleton
    · intro i j hij
      simp only [GL.val_diagonalBlocks, Units.val_one, l₁', l₂']
      rw [Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
        Matrix.fromBlocks_multiply]
      simp only [map_zero, Matrix.map_zero, Matrix.mul_zero, add_zero, Matrix.zero_mul,
        _root_.map_one, Matrix.map_one, Matrix.mul_one, one_mul, zero_add, mul_one,
        fromBlocks_apply₁₁]
      apply hl.monotone hij
    · simp only [GL.val_diagonalBlocks, Units.val_one, l₁', l₂']
      rw [Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
        Matrix.fromBlocks_multiply]
      simp only [map_zero, Matrix.map_zero, Matrix.mul_zero, add_zero, Matrix.zero_mul,
        _root_.map_one, Matrix.map_one, Matrix.mul_one, one_mul, zero_add, mul_one,
        fromBlocks_apply₂₂]
      simp only [g', hh.monotone, coeffs_sup_fromBlocks, coeffs_sup_zero]
      simp only [zero_le, sup_of_le_left]
      rw [hv, coeffs_sup_unique (n := Unit)]
      simp only [hh.monotone, coeffs_sup_toBlock₁₁_le_coeffs_sup, sup_of_le_right, h, g']
    · simp only [GL.val_diagonalBlocks, Units.val_one, l₁', l₂']
      rw [Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
        Matrix.fromBlocks_multiply]
      simpa [coeffs_sup_fromBlocks, coeffs_sup_zero, hv, coeffs_sup_unique (n := Unit), g',
        hh.monotone, coeffs_sup_toBlock₁₁_le_coeffs_sup, h]

lemma exists_trafo_isDiag (g : Matrix (Fin k) (Fin k) K) :
    ∃ (k₁ k₂ : GL (Fin k) R),
    IsMonotoneDiag (n := Fin k) (R := R) (k₁.val * g * k₂.val) ∧
    (k₁.val * g * k₂.val).coeffsSup v = g.coeffsSup v := by
  induction k using PNat.recOn with
  | one =>
      refine ⟨1, 1, ?_⟩
      haveI : Unique (Fin (1 : ℕ+)) := inferInstanceAs <| Unique (Fin 1)
      refine ⟨⟨isDiag_of_subsingleton _, Subsingleton.monotone _⟩, ?_⟩
      rw [Matrix.coeffs_sup_unique v, Matrix.coeffs_sup_unique v]
      congr 1
      simp only [Units.val_one]
      rw [Matrix.map_one, one_mul, mul_one] <;> rfl
  | succ n ih =>
      let e : Fin (n + 1) ≃ Fin n ⊕ Unit := Fin.succEquivUnit n
      let g' : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) K :=
        Matrix.reindex e e g
      obtain ⟨k₁', k₂', hk, hc⟩ := exists_trafo_isDiag_induction_step g' ih
      use GL.reindex e.symm k₁'
      use GL.reindex e.symm k₂'
      convert_to IsMonotoneDiag (n := Fin (n + 1)) (R := R)
          (Matrix.reindex e.symm e.symm (k₁'.val * g' * k₂'.val)) ∧
          (Matrix.reindex e.symm e.symm
            ((k₁'.val : Matrix _ _ K) * g' * (k₂'.val : Matrix _ _ K))).coeffsSup v
            = g.coeffsSup v
      · simp only [PNat.add_coe, PNat.val_ofNat, GL.val_reindex, reindex_apply, Equiv.symm_symm, g']
        rw [Matrix.submatrix_mul _ _ e e e e.bijective]
        rw [Matrix.submatrix_mul _ _ e e e e.bijective]
        rw [Matrix.submatrix_map, Matrix.submatrix_map, Matrix.submatrix_submatrix]
        apply iff_of_eq
        congr
        ext i j
        simp [Function.comp_def]
      · simp only [PNat.add_coe, PNat.val_ofNat, GL.val_reindex, reindex_apply, Equiv.symm_symm, g']
        rw [Matrix.submatrix_mul _ _ e e e e.bijective]
        rw [Matrix.submatrix_mul _ _ e e e e.bijective]
        rw [Matrix.submatrix_map, Matrix.submatrix_map, Matrix.submatrix_submatrix]
        apply iff_of_eq
        congr
        ext i j
        simp [Function.comp_def]
      · refine ⟨⟨?_, ?_⟩, ?_⟩
        · simp only [reindex_apply, Equiv.symm_symm]
          apply IsDiag.submatrix hk.isDiag (Equiv.injective e)
        · simp only [reindex_apply, Equiv.symm_symm, submatrix_apply]
          apply monotone_of_isBlockMonotoneDiag _ hk
        · simp only [g', coeffs_sup_reindex, hc]
          rfl

-- From here onwards we work with a DVR

variable (ϖ : R) (hϖ : Irreducible ϖ)

/-- A matrix is normal diagonal if it is diagonal, the first entries on the
diagonal are given by powers of the uniformiser `ϖ` and the last entries by `0`. -/
def IsNormalDiag (g : Matrix (Fin k) (Fin k) K) : Prop :=
  ∃ (r : ℕ) (hr : r ≤ k) (f : Fin r → ℤ),
    Monotone f ∧ (∀ (j : Fin r), g (j.castLE hr) (j.castLE hr) = ϖ ^ f j) ∧
      ∀ (j : Fin k) (_ : r ≤ j), g j j = 0

include hϖ in
lemma exists_normalization_of_isMonotoneDiag [IsDiscreteValuationRing R] (g : GL (Fin k) K)
    (h : IsMonotoneDiag (R := R) g.val) :
    ∃ (d : Fin k → Rˣ) (f : Fin k → ℤ) ,
    Antitone f ∧ ∀ (j : Fin k), (GL.diagonal d * g).val j j = ϖ ^ f j := by
  have (j : Fin k) : ∃ (n : ℤ) (u : Rˣ), g j j = u * ϖ ^ n := by
    apply eq_unit_mul_pow_irreducible ϖ hϖ
    apply g.apply_ne_zero_of_isDiag
    exact h.isDiag
  choose f d hd using this
  use (fun j ↦ (d j)⁻¹)
  use f
  refine ⟨?_, ?_⟩
  · intro i j hij
    have hle : v (g i i) ≤ v (g j j) := h.monotone hij
    rw [hd i, hd j] at hle
    simp only [map_mul, valuation_unit_eq_one, one_mul, map_zpow₀] at hle
    apply exp_le_exp_of_pow_le_pow (v ϖ) _ _ hle
    · apply valuation_lt_one_of_irreducible ϖ hϖ
    · rw [Valuation.ne_zero_iff]
      intro hzero
      rw [Subring.coe_eq_zero_iff] at hzero
      apply Irreducible.ne_zero hϖ hzero
  · intro j
    simp only [GL.map, GL.val_diagonal, RingHom.mapMatrix_apply, map_zero, diagonal_map,
      map_units_inv, Units.inv_eq_val_inv, coe_units_inv, Units.val_mul, diagonal_mul]
    rw [hd j]
    simp [Subring.subtype_apply]

/-- The cartan diagonal for a tuple of integers `f` is the diagonal matrix
where the diagonal entries are given by `ϖ ^ f i`. -/
@[simps! -isSimp]
def cartanDiag {k : ℕ} (f : Fin k → ℤ) : GL (Fin k) K :=
  let d (j : Fin k) : Kˣ := {
    val := ϖ ^ f j
    inv := ϖ ^ (-f j)
    val_inv := by
      have hzero : (↑ϖ : K) ≠ 0 := by
        intro hzero
        rw [Subring.coe_eq_zero_iff] at hzero
        exact Irreducible.ne_zero hϖ hzero
      rw [← zpow_add₀ hzero, add_neg_cancel, zpow_zero]
    inv_val := by
      have hzero : (↑ϖ : K) ≠ 0 := by
        intro hzero
        rw [Subring.coe_eq_zero_iff] at hzero
        exact Irreducible.ne_zero hϖ hzero
      rw [← zpow_add₀ hzero, neg_add_cancel, zpow_zero]
  }
  GL.diagonal d

omit [ValuationRing ↥R] [IsFractionRing R K] in
lemma cartanDiag_inv {k : ℕ} (f : Fin k → ℤ) :
    (cartanDiag ϖ hϖ f)⁻¹ = cartanDiag ϖ hϖ (fun i ↦ - f i) := by
  simp [cartanDiag]
  congr

omit [ValuationRing ↥R] [IsFractionRing (↥R) K] in
@[simp]
lemma cartanDiag_zero {k : ℕ} {ϖ : R} (hϖ : Irreducible ϖ) :
    cartanDiag (k := k) ϖ hϖ 0 = 1 := by
  ext
  simp [cartanDiag]

omit [ValuationRing ↥R] [IsFractionRing (↥R) K] in
lemma conj_cartanDiag_zero_zero {ϖ : R} (hϖ : Irreducible ϖ) (g : GL (Fin 2) K) (f : Fin 2 → ℤ) :
    MulAut.conj (cartanDiag ϖ hϖ f) g 0 0 = g 0 0 := by
  rw [cartanDiag, Matrix.GL.conj_diagonal_apply]
  simp only [Fin.isValue, zpow_neg, Units.inv_mk]
  rw [mul_inv_cancel₀]
  · simp
  · apply zpow_ne_zero
    intro hzero
    rw [Subring.coe_eq_zero_iff] at hzero
    exact hϖ.ne_zero hzero

omit [ValuationRing ↥R] [IsFractionRing (↥R) K] in
lemma conj_cartanDiag_one_one {ϖ : R} (hϖ : Irreducible ϖ) (g : GL (Fin 2) K) (f : Fin 2 → ℤ) :
    MulAut.conj (cartanDiag ϖ hϖ f) g 1 1 = g 1 1 := by
  rw [cartanDiag, Matrix.GL.conj_diagonal_apply]
  simp only [Fin.isValue, zpow_neg, Units.inv_mk]
  rw [mul_inv_cancel₀]
  · simp
  · apply zpow_ne_zero
    intro hzero
    rw [Subring.coe_eq_zero_iff] at hzero
    exact hϖ.ne_zero hzero

omit [ValuationRing ↥R] [IsFractionRing (↥R) K] in
lemma conj_cartanDiag_one_zero {ϖ : R} (hϖ : Irreducible ϖ) (g : GL (Fin 2) K) (f : Fin 2 → ℤ) :
    MulAut.conj (cartanDiag ϖ hϖ f) g 1 0 = ϖ.val ^ (f 1 - f 0) * g 1 0 := by
  rw [cartanDiag, Matrix.GL.conj_diagonal_apply]
  simp only [Fin.isValue, zpow_neg, Units.inv_mk, mul_eq_mul_right_iff]
  have hzero : (↑ϖ : K) ≠ 0 := by
    intro hzero
    rw [Subring.coe_eq_zero_iff] at hzero
    exact hϖ.ne_zero hzero
  rw [zpow_sub₀ hzero]
  ring_nf
  left
  trivial

omit [ValuationRing ↥R] [IsFractionRing (↥R) K] in
lemma conj_cartanDiag_zero_one {ϖ : R} (hϖ : Irreducible ϖ) (g : GL (Fin 2) K) (f : Fin 2 → ℤ) :
    MulAut.conj (cartanDiag ϖ hϖ f) g 0 1 = ϖ.val ^ (f 0 - f 1) * g 0 1 := by
  rw [cartanDiag, Matrix.GL.conj_diagonal_apply]
  simp only [Fin.isValue, zpow_neg, Units.inv_mk, mul_eq_mul_right_iff]
  have hzero : (↑ϖ : K) ≠ 0 := by
    intro hzero
    rw [Subring.coe_eq_zero_iff] at hzero
    exact hϖ.ne_zero hzero
  rw [zpow_sub₀ hzero]
  ring_nf
  left
  trivial

/--
Existence part of cartan decomposition: If `R` is a discrete valuation ring with
uniformizer `ϖ` and `g` an invertible matrix over `K`, then there exist invertible matrices `k₁` and
`k₂` over `R` such that `k₁ * g * k₂` is a diagonal matrix with decreasing powers of `ϖ` on the
diagonal.
See `cartan_decomposition'` for a version where instead `g` is written as a product.
-/
theorem cartan_decomposition [IsDiscreteValuationRing R] (g : GL (Fin k) K) :
    ∃ (k₁ k₂ : GL (Fin k) R) (f : Fin k → ℤ),
      Antitone f ∧ k₁ * g * k₂ = cartanDiag ϖ hϖ f := by
  obtain ⟨k₁', k₂, hk, _⟩ := exists_trafo_isDiag (R := R) g.val
  obtain ⟨d, f, hf, hd⟩ :=
    exists_normalization_of_isMonotoneDiag (R := R) ϖ hϖ
      ((k₁' : GL _ K) * g * (k₂ : GL _ K)) (by simpa using hk)
  refine ⟨(GL.diagonal d) * k₁', k₂, f, hf, ?_⟩
  apply Units.ext
  simp only [GL.map, Units.val_mul, GL.val_diagonal, _root_.map_mul, RingHom.mapMatrix_apply,
    map_zero, diagonal_map, Units.inv_eq_val_inv, _root_.mul_inv_rev, coe_units_inv, val_cartanDiag]
  ext i j
  simp only [mul_assoc, mul_assoc, diagonal_mul]
  rw [← mul_assoc]
  by_cases hij : i = j
  · subst hij
    simp only [GL.map, GL.val_diagonal, RingHom.mapMatrix_apply, map_zero, diagonal_map,
      Units.inv_eq_val_inv, coe_units_inv, Units.val_mul, diagonal_mul] at hd
    rw [diagonal_apply_eq]
    exact hd i
  · simp [diagonal_apply_ne _ hij, hk.isDiag hij]

/-- Variant of `cartan_decomposition` where `g` is written as a product. -/
theorem cartan_decomposition' [IsDiscreteValuationRing R] (g : GL (Fin k) K) :
    ∃ (k₁ k₂ : GL (Fin k) R) (f : Fin k → ℤ),
      Antitone f ∧ k₁ * cartanDiag ϖ hϖ f * k₂ = g := by
  obtain ⟨k₁, k₂, f, hf, hfeq⟩ := cartan_decomposition ϖ hϖ g
  refine ⟨k₁⁻¹, k₂⁻¹, f, hf, ?_⟩
  rw [← hfeq, mul_assoc, mul_assoc, GL.map_mul_map_inv, mul_one, ← mul_assoc, GL.map_inv_mul_map,
    one_mul]

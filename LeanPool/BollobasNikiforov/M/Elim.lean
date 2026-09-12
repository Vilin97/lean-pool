/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import LeanPool.BollobasNikiforov.CP.Basic
public import LeanPool.BollobasNikiforov.M.Config
public import LeanPool.BollobasNikiforov.TN.Truncated
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef

/-!
# Ordered elimination residuals

The residual of symmetric Gaussian elimination of a principal index list is a
ratio of minors (EL01). Eliminating `idxZ0` leaves the `z`-block and its
`y`-coupling unchanged (EL02). That `z`-block is a Gram matrix plus a
positive diagonal, hence PD, so later pivots stay positive (EL03). The
numerator minor expands in the `I`-diagonal as a sum of complementary Gram
minors (EL04); those principal cofactors have sign `+1` (EL05). Factoring
`s i > 0` and `ρ > 0` leaves the unscaled kernel `(1 + t_a t_b)²` or a last
row `(t_b - x)₊²` (EL06). An algebraic identity rewrites `(1 + s t)²` as a
truncated square (EL07). Row arguments `-1/t_a` are increasing and lie
below any `x ≥ 0` (EL08–EL09). Those leftover minors are nonnegative by
TN13 (EL10), so residual columns stay nonnegative (EL11). Scaled outer
products of those columns yield a completely positive `C₀` (EL12). The
remainder is the `T`-Schur complement of `E` and is PSD (EL13–EL14).
-/

@[expose] public section

open Matrix Function

namespace BollobasNikiforov

variable {ι : Type*} {r : ℕ}


noncomputable section

/-- The residual entry after eliminating the principal block indexed by `e`. -/
def schurComplementEntry (A : Matrix ι ι ℝ) (e : Fin r → ι) (α j : ι) : ℝ :=
  A α j - (fun i ↦ A α (e i)) ⬝ᵥ ((A.submatrix e e)⁻¹ *ᵥ fun i ↦ A (e i) j)

lemma submatrix_elim_eq_fromBlocks (A : Matrix ι ι ℝ) (e : Fin r → ι) (α j : ι) :
    A.submatrix (Sum.elim e fun _ : Fin 1 ↦ α) (Sum.elim e fun _ : Fin 1 ↦ j) =
      fromBlocks (A.submatrix e e) (A.submatrix e fun _ : Fin 1 ↦ j)
        (A.submatrix (fun _ : Fin 1 ↦ α) e)
        (A.submatrix (fun _ : Fin 1 ↦ α) fun _ : Fin 1 ↦ j) := by
  ext i k
  cases i <;> cases k <;> rfl

lemma snoc_eq_elim_comp_finSumFinEquiv_symm (e : Fin r → ι) (x : ι) :
    Fin.snoc e x =
      Sum.elim e (fun _ : Fin 1 ↦ x) ∘ (finSumFinEquiv (m := r) (n := 1)).symm := by
  ext i
  induction i using Fin.lastCases with
  | last =>
    have hlast : (finSumFinEquiv (m := r) (n := 1)).symm (Fin.last r) = Sum.inr 0 := by
      refine (finSumFinEquiv (m := r) (n := 1)).symm_apply_eq.2 ?_
      apply Fin.ext
      simp [finSumFinEquiv_apply_right]
    simp [Fin.snoc_last, hlast]
  | cast k =>
    simp [Fin.snoc_castSucc, finSumFinEquiv_symm_apply_castSucc]

lemma det_submatrix_snoc_eq_det_elim (A : Matrix ι ι ℝ) (e : Fin r → ι) (α j : ι) :
    (A.submatrix (Fin.snoc e α) (Fin.snoc e j)).det =
      (A.submatrix (Sum.elim e fun _ : Fin 1 ↦ α)
        (Sum.elim e fun _ : Fin 1 ↦ j)).det := by
  have hα := snoc_eq_elim_comp_finSumFinEquiv_symm e α
  have hj := snoc_eq_elim_comp_finSumFinEquiv_symm e j
  rw [hα, hj, ← submatrix_submatrix, det_submatrix_equiv_self]

lemma mul_fin_one_apply (C : Matrix (Fin 1) (Fin r) ℝ) (M : Matrix (Fin r) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin 1) ℝ) :
    (C * M * B) 0 0 = (fun i ↦ C 0 i) ⬝ᵥ (M *ᵥ fun i ↦ B i 0) := by
  calc
    (C * M * B) 0 0 = ∑ i, (∑ k, C 0 k * M k i) * B i 0 := by
      simp [Matrix.mul_apply]
    _ = ∑ i, ∑ k, C 0 k * M k i * B i 0 := by
      simp [Finset.sum_mul]
    _ = ∑ k, ∑ i, C 0 k * (M k i * B i 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
      ring
    _ = (fun k ↦ C 0 k) ⬝ᵥ (M *ᵥ fun i ↦ B i 0) := by
      simp [dotProduct, mulVec, Finset.mul_sum]

/-- EL01: the residual after eliminating the principal block `A[I]` is a ratio of
minors. Injectivity of `e` and `α, j ∉ range e` record the elimination setup. -/
lemma schurComplementEntry_eq_minor_div_det (A : Matrix ι ι ℝ) (e : Fin r → ι)
    (_he : e.Injective) {α j : ι} (_hα : α ∉ Set.range e) (_hj : j ∉ Set.range e)
    (hdet : (A.submatrix e e).det ≠ 0) :
    schurComplementEntry A e α j =
      (A.submatrix (Fin.snoc e α) (Fin.snoc e j)).det / (A.submatrix e e).det := by
  let AII := A.submatrix e e
  let B : Matrix (Fin r) (Fin 1) ℝ := A.submatrix e fun _ ↦ j
  let C : Matrix (Fin 1) (Fin r) ℝ := A.submatrix (fun _ ↦ α) e
  let D : Matrix (Fin 1) (Fin 1) ℝ := A.submatrix (fun _ ↦ α) fun _ ↦ j
  have hunit : IsUnit AII := (Matrix.isUnit_iff_isUnit_det AII).2 (Ne.isUnit hdet)
  let : Invertible AII := hunit.invertible
  have hblocks : A.submatrix (Sum.elim e fun _ : Fin 1 ↦ α) (Sum.elim e fun _ : Fin 1 ↦ j) =
      fromBlocks AII B C D := submatrix_elim_eq_fromBlocks A e α j
  have hdetb : (fromBlocks AII B C D).det = AII.det * (D - C * ⅟AII * B).det :=
    det_fromBlocks₁₁ AII B C D
  have hsnoc : (A.submatrix (Fin.snoc e α) (Fin.snoc e j)).det = (fromBlocks AII B C D).det := by
    rw [det_submatrix_snoc_eq_det_elim, hblocks]
  have hentry : (D - C * ⅟AII * B).det = schurComplementEntry A e α j := by
    rw [det_fin_one, Matrix.sub_apply, invOf_eq_nonsing_inv, mul_fin_one_apply]
    simp [schurComplementEntry, AII, B, C, D, submatrix_apply]
  rw [eq_div_iff hdet, hsnoc, hdetb, hentry, mul_comm]

/-- Empty elimination: the residual is the original entry and the denominator is `1`. -/
lemma schurComplementEntry_elim0 (A : Matrix ι ι ℝ) (e : Fin 0 → ι) (α j : ι) :
    schurComplementEntry A e α j = A α j ∧ (A.submatrix e e).det = 1 := by
  refine ⟨?_, det_fin_zero⟩
  · simp [schurComplementEntry]

/-- A vanishing eliminated row leaves the residual equal to the original entry. -/
lemma schurComplementEntry_eq_of_row (A : Matrix ι ι ℝ) (e : Fin r → ι) {α j : ι}
    (h : ∀ i, A α (e i) = 0) :
    schurComplementEntry A e α j = A α j := by
  simp [schurComplementEntry, h]

/-- A vanishing eliminated column leaves the residual equal to the original entry. -/
lemma schurComplementEntry_eq_of_col (A : Matrix ι ι ℝ) (e : Fin r → ι) {α j : ι}
    (h : ∀ i, A (e i) j = 0) :
    schurComplementEntry A e α j = A α j := by
  have hz : (fun i ↦ A (e i) j) = 0 := funext h
  unfold schurComplementEntry
  rw [hz]
  simp [mulVec, dotProduct]

/-- Singleton Schur residual, before simplifying the `1 × 1` inverse. -/
lemma schurComplementEntry_one (A : Matrix ι ι ℝ) (q α j : ι) :
    schurComplementEntry A (fun _ : Fin 1 ↦ q) α j =
      A α j -
        A α q * ((A.submatrix (fun _ : Fin 1 ↦ q) (fun _ : Fin 1 ↦ q))⁻¹ 0 0) *
          A q j := by
  simp only [schurComplementEntry, dotProduct, mulVec, Fin.sum_univ_one]
  ring

/-- The inverse entry of a nonzero `1 × 1` matrix is the reciprocal. -/
lemma inv_fin_one_apply (A : Matrix (Fin 1) (Fin 1) ℝ) (hA : A 0 0 ≠ 0) :
    A⁻¹ 0 0 = (A 0 0)⁻¹ := by
  have hdet : A.det ≠ 0 := by
    rwa [det_fin_one]
  have hmul := mul_nonsing_inv A (Ne.isUnit hdet)
  have hentry : (A * A⁻¹) 0 0 = 1 := by
    rw [hmul]
    rfl
  rw [Matrix.mul_apply, Fin.sum_univ_one] at hentry
  exact eq_inv_of_mul_eq_one_right hentry

/-- Singleton Schur residual as the rank-one update `A α j - A α q * A q j / A q q`. -/
lemma schurComplementEntry_one_div (A : Matrix ι ι ℝ) (q α j : ι) (hq : A q q ≠ 0) :
    schurComplementEntry A (fun _ : Fin 1 ↦ q) α j =
      A α j - A α q * A q j / A q q := by
  have hinv :
      (A.submatrix (fun _ : Fin 1 ↦ q) (fun _ : Fin 1 ↦ q))⁻¹ 0 0 = (A q q)⁻¹ := by
    have h0 : (A.submatrix (fun _ : Fin 1 ↦ q) (fun _ : Fin 1 ↦ q)) 0 0 ≠ 0 := by
      simpa [submatrix_apply] using hq
    rw [inv_fin_one_apply _ h0, submatrix_apply]
  rw [schurComplementEntry_one, hinv, div_eq_mul_inv]
  ring

variable {k p : ℕ}

/-- The opposite `z`-`z₀` block entry vanishes by symmetry of `Xconfig`. -/
lemma MX_z_z0 (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (i : Fin k) :
    M (Xconfig s t ρ x) (idxZ i) idxZ0 = 0 := by
  rw [M_apply_of_ne _ (Xconfig_isSymm s t ρ x) (idxZ0_ne_idxZ (p := p) i).symm]
  rw [posPart_apply, (Xconfig_isSymm s t ρ x).apply, Xconfig_z0_z,
    max_eq_right (neg_nonpos.mpr (Real.sqrt_nonneg _)), zero_pow (by decide)]

/-- EL02: eliminating `idxZ0` does not change a `z`-`z` entry. The eliminated
column on `{idxZ i}` is zero (`MX_z0_z`). -/
lemma schurComplementEntry_elimZ0_z_z (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (i h : Fin k) :
    schurComplementEntry (M (Xconfig s t ρ x)) (fun _ : Fin 1 ↦ idxZ0)
      (idxZ i) (idxZ h) =
      M (Xconfig s t ρ x) (idxZ i) (idxZ h) :=
  schurComplementEntry_eq_of_col _ _ fun _ ↦ MX_z0_z s t ρ x h

/-- EL02: eliminating `idxZ0` does not change a `z`-`y` coupling. The
eliminated row on `{idxZ i}` is zero (`MX_z_z0`), even if `M idxZ0 (idxY j)`
is nonzero. -/
lemma schurComplementEntry_elimZ0_z_y (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (i : Fin k) (j : Fin p) :
    schurComplementEntry (M (Xconfig s t ρ x)) (fun _ : Fin 1 ↦ idxZ0)
      (idxZ i) (idxY j) =
      M (Xconfig s t ρ x) (idxZ i) (idxY j) :=
  schurComplementEntry_eq_of_row _ _ fun _ ↦ MX_z_z0 s t ρ x i

/-- EL02: the opposite `y`-`z` coupling is likewise unchanged (`MX_z0_z`). -/
lemma schurComplementEntry_elimZ0_y_z (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (j : Fin p) (i : Fin k) :
    schurComplementEntry (M (Xconfig s t ρ x)) (fun _ : Fin 1 ↦ idxZ0)
      (idxY j) (idxZ i) =
      M (Xconfig s t ρ x) (idxY j) (idxZ i) :=
  schurComplementEntry_eq_of_col _ _ fun _ ↦ MX_z0_z s t ρ x i

/-- Squared inner products of configuration `z`-vectors. -/
lemma zVec_dot_sq (s t : Fin k → ℝ) (hs : ∀ i, 0 < s i) (i h : Fin k) :
    (zVec s t i ⬝ᵥ zVec s t h) ^ 2 = s i * s h * (1 + t i * t h) ^ 2 := by
  rw [zVec_dot_zVec, mul_pow, mul_pow, Real.sq_sqrt (hs i).le, Real.sq_sqrt (hs h).le]

/-- Feature map `i ↦ zᵢ ⊗ zᵢ` on `Fin 2 × Fin 2`. -/
def zKron (s t : Fin k → ℝ) : Matrix (Fin k) (Fin 2 × Fin 2) ℝ :=
  fun i p ↦ zVec s t i p.1 * zVec s t i p.2

/-- The squared-Gram matrix of the `z`-vectors is `zKron * zKronᵀ`. -/
lemma zKron_mul_transpose (s t : Fin k → ℝ) :
    (of fun i h : Fin k ↦ (zVec s t i ⬝ᵥ zVec s t h) ^ 2) =
      zKron s t * (zKron s t)ᵀ := by
  ext i h
  calc
    (of fun i h ↦ (zVec s t i ⬝ᵥ zVec s t h) ^ 2) i h =
        (zVec s t i ⬝ᵥ zVec s t h) ^ 2 :=
      rfl
    _ = (∑ a, zVec s t i a * zVec s t h a) *
          (∑ b, zVec s t i b * zVec s t h b) := by
      simp [dotProduct, pow_two]
    _ = ∑ a, ∑ b,
          (zVec s t i a * zVec s t h a) * (zVec s t i b * zVec s t h b) := by
      rw [Finset.sum_mul_sum]
    _ = ∑ a, ∑ b,
          zVec s t i a * zVec s t i b * zVec s t h a * zVec s t h b := by
      refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
      ring
    _ = ∑ p : Fin 2 × Fin 2, zKron s t i p * zKron s t h p := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
      simp [zKron]
      ring
    _ = (zKron s t * (zKron s t)ᵀ) i h := by
      simp [mul_apply, transpose_apply]

/-- The squared-Gram `z`-block is positive semidefinite. -/
lemma zGram_posSemidef (s t : Fin k → ℝ) :
    (of fun i h : Fin k ↦ (zVec s t i ⬝ᵥ zVec s t h) ^ 2).PosSemidef := by
  rw [zKron_mul_transpose]
  simpa [conjTranspose_eq_transpose_of_trivial] using
    posSemidef_self_mul_conjTranspose (zKron s t)

/-- EL03: the principal `z`-block is a Gram matrix plus `diagonal (s i * d i)`. -/
lemma MX_zBlock_eq (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j) :
    (M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p)) =
      (of fun i h ↦ (zVec s t i ⬝ᵥ zVec s t h) ^ 2) +
        diagonal fun i ↦ s i * configD t ρ x i := by
  ext i h
  rw [submatrix_apply, Matrix.add_apply, of_apply, diagonal_apply,
    MX_z_z s t ρ x hs ht hρ, zVec_dot_sq s t hs]

/-- EL03: the principal `z`-block is positive definite. -/
lemma MX_zBlock_posDef (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j) :
    ((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p))).PosDef := by
  rw [MX_zBlock_eq s t ρ x hs ht hρ]
  refine PosDef.posSemidef_add (zGram_posSemidef s t) ?_
  exact PosDef.diagonal fun i ↦ mul_pos (hs i) (configD_pos t hρ x i)

/-- A diagonal Schur residual of a PD matrix is a ratio of positive principal
minors, hence positive. -/
lemma schurComplementEntry_diag_pos_of_posDef {n : Type*}
    {A : Matrix n n ℝ} (hA : A.PosDef) {m : ℕ} (e : Fin m → n) (he : e.Injective)
    {α : n} (hα : α ∉ Set.range e) :
    0 < schurComplementEntry A e α α := by
  have hI : (A.submatrix e e).PosDef := hA.submatrix he
  have hdetI : (A.submatrix e e).det ≠ 0 := (PosDef.det_pos hI).ne'
  have heα : (Fin.snoc e α).Injective := Fin.snoc_injective_of_injective he hα
  have hIa : (A.submatrix (Fin.snoc e α) (Fin.snoc e α)).PosDef := hA.submatrix heα
  rw [schurComplementEntry_eq_minor_div_det A e he hα hα hdetI]
  exact div_pos (PosDef.det_pos hIa) (PosDef.det_pos hI)

/-- EL03: every Schur pivot inside the `z`-block is positive. -/
lemma MX_zBlock_schur_pivot_pos (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    {m : ℕ} (e : Fin m → Fin k) (he : e.Injective) {i : Fin k}
    (hi : i ∉ Set.range e) :
    0 < schurComplementEntry
      ((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p))) e i i :=
  schurComplementEntry_diag_pos_of_posDef (MX_zBlock_posDef s t ρ x hs ht hρ) e he hi

/-- EL03: leading principal submatrices of the `z`-block are PD. -/
lemma MX_zBlock_leading_posDef (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    {m : ℕ} (hm : m ≤ k) :
    (((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p))).submatrix
      (Fin.castLE hm) (Fin.castLE hm)).PosDef :=
  (MX_zBlock_posDef s t ρ x hs ht hρ).submatrix (Fin.castLE_injective hm)

/-- EL03: leading principal minors of the `z`-block are positive. -/
lemma MX_zBlock_leading_det_pos (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    {m : ℕ} (hm : m ≤ k) :
    0 < (((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p))).submatrix
      (Fin.castLE hm) (Fin.castLE hm)).det :=
  PosDef.det_pos (MX_zBlock_leading_posDef s t ρ x hs ht hρ hm)

/-- EL03: after removing `idxZ0`, each remaining `z`-diagonal pivot is positive. -/
lemma schurComplementEntry_elimZ0_z_diag_pos (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j) (i : Fin k) :
    0 < schurComplementEntry (M (Xconfig s t ρ x)) (fun _ : Fin 1 ↦ idxZ0)
      (idxZ i) (idxZ i) := by
  rw [schurComplementEntry_elimZ0_z_z]
  simpa [submatrix_apply] using
    PosDef.diag_pos (MX_zBlock_posDef s t ρ x hs ht hρ) (i := i)

/-! ### EL04 — diagonal expansion of a numerator minor -/

open Finset

/-- Unscaled `z`-`z` kernel `K_{ab} = (1 + t_a t_b)²`. -/
def elimKernelZZ (t : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun a b ↦ (1 + t a * t b) ^ 2

/-- Unscaled `z`-`y` kernel `K_{a,y} = (t_a - x)₊²`. -/
def elimKernelZY (t : Fin k → ℝ) (x : ℝ) : Fin k → ℝ :=
  fun a ↦ (max (t a - x) 0) ^ 2

/-- Non-dependent concatenation of a `z`-index list with a later index. -/
def elimSnoc {m : ℕ} (e : Fin m → Fin k) (z : Fin k) : Fin m.succ → Fin k :=
  fun a ↦ if h : a = Fin.last m then z else e (a.castPred h)

lemma elimSnoc_last {m : ℕ} (e : Fin m → Fin k) (z : Fin k) :
    elimSnoc e z (Fin.last m) = z := by
  simp [elimSnoc]

lemma elimSnoc_castSucc {m : ℕ} (e : Fin m → Fin k) (z : Fin k) (i : Fin m) :
    elimSnoc e z i.castSucc = e i := by
  simp [elimSnoc, Fin.castSucc_ne_last]

/-- `idxZ` is injective. -/
lemma idxZ_inj {i h : Fin k} : idxZ (p := p) i = idxZ h ↔ i = h := by
  constructor
  · intro hih
    exact Fin.ext (by simpa [idxZ_val] using congrArg Fin.val hih)
  · rintro rfl; rfl

/-- Equal index Finsets give equal principal minors. -/
lemma det_submatrix_finset_eq {n : Type*} [DecidableEq n]
    (A : Matrix n n ℝ) {s t : Finset n} (h : s = t) :
    (A.submatrix (Subtype.val : {x // x ∈ s} → n) Subtype.val).det =
      (A.submatrix (Subtype.val : {x // x ∈ t} → n) Subtype.val).det :=
  h ▸ rfl

/-- EL04: `det(A + diagonal d)` expands over kept index sets `S`.
The product runs over the complementary (deleted) diagonal entries, and the
leftover minor is the principal submatrix of `A` on `S`. -/
lemma det_add_diagonal_eq_sum {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (d : n → ℝ) :
    (A + diagonal d).det =
      ∑ S : Finset n,
        (∏ i ∈ Sᶜ, d i) *
          (A.submatrix (Subtype.val : {x // x ∈ S} → n)
            (Subtype.val : {x // x ∈ S} → n)).det := by
  let D := detRowAlternating (R := ℝ) (n := n)
  have hdet : (A + diagonal d).det = D (fun i ↦ A i + (diagonal d) i) := rfl
  have hadd : (fun i ↦ A i + (diagonal d) i) =
      (fun i ↦ A i) + fun i ↦ (diagonal d) i := rfl
  rw [hdet, hadd, D.map_add_univ]
  refine Fintype.sum_congr _ _ fun S ↦ ?_
  have hscale :
      S.piecewise (A : n → n → ℝ) (diagonal d) =
        fun i ↦ (if i ∈ S then (1 : ℝ) else d i) •
          S.piecewise (A : n → n → ℝ) (1 : Matrix n n ℝ) i := by
    ext i j
    by_cases hi : i ∈ S
    · simp [Finset.piecewise, hi]
    · simp [Finset.piecewise, hi, diagonal, Matrix.one_apply, smul_eq_mul, mul_ite]
  rw [hscale, D.map_smul_univ, smul_eq_mul]
  have hc : (∏ i : n, if i ∈ S then (1 : ℝ) else d i) = ∏ i ∈ Sᶜ, d i := by
    rw [prod_ite, filter_univ_mem]
    have hSc : univ.filter (fun i : n ↦ i ∉ S) = Sᶜ := by
      ext i
      simp
    rw [hSc, prod_const_one, one_mul]
  rw [hc]
  congr 1
  have hpw :
      S.piecewise (A : n → n → ℝ) (1 : Matrix n n ℝ) =
        of (S.piecewise A.row (1 : Matrix n n ℝ).row) := by
    ext i j
    rfl
  rw [hpw]
  exact det_piecewise_one_eq_submatrix_det A S

/-- If `d` is supported on `I`, the expansion runs over deleted sets `S ⊆ I`. -/
lemma det_add_diagonal_eq_sum_subset {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (d : n → ℝ) (I : Finset n)
    (hd : ∀ i, i ∉ I → d i = 0) :
    (A + diagonal d).det =
      ∑ S ∈ I.powerset,
        (∏ i ∈ S, d i) *
          (A.submatrix (Subtype.val : {x // x ∈ Sᶜ} → n)
            (Subtype.val : {x // x ∈ Sᶜ} → n)).det := by
  rw [det_add_diagonal_eq_sum]
  let e : Finset n ≃ Finset n :=
    { toFun := fun S ↦ (Sᶜ : Finset n)
      invFun := fun S ↦ Sᶜ
      left_inv := compl_compl
      right_inv := compl_compl }
  rw [Fintype.sum_equiv e
    (fun S ↦ (∏ i ∈ Sᶜ, d i) *
      (A.submatrix (Subtype.val : {x // x ∈ S} → n) Subtype.val).det)
    (fun S ↦ (∏ i ∈ S, d i) *
      (A.submatrix (Subtype.val : {x // x ∈ Sᶜ} → n) Subtype.val).det)
    (fun S ↦ by
      change (∏ i ∈ Sᶜ, d i) *
          (A.submatrix (Subtype.val : {x // x ∈ S} → n) Subtype.val).det =
        (∏ i ∈ Sᶜ, d i) *
          (A.submatrix (Subtype.val : {x // x ∈ (Sᶜ)ᶜ} → n) Subtype.val).det
      exact congrArg _ (det_submatrix_finset_eq A (compl_compl S).symm))]
  have hpow : I.powerset = univ.filter (fun S : Finset n ↦ S ⊆ I) := by
    ext S
    simp [mem_powerset]
  rw [hpow, sum_filter]
  refine Fintype.sum_congr _ _ fun S ↦ ?_
  by_cases hS : S ⊆ I
  · simp [hS]
  · have hz : ∏ i ∈ S, d i = 0 := by
      obtain ⟨i, hiS, hiI⟩ := not_subset.mp hS
      exact prod_eq_zero hiS (hd i hiI)
    simp [hS, hz]

/-- The leading block `I` inside `Fin (m + 1)`, excluding the last index. -/
def elimI (m : ℕ) : Finset (Fin m.succ) :=
  univ.map Fin.castSuccEmb

lemma mem_elimI_iff {m : ℕ} {a : Fin m.succ} : a ∈ elimI m ↔ a ≠ Fin.last m := by
  constructor
  · intro h
    rcases mem_map.mp h with ⟨i, _, hi⟩
    exact hi ▸ Fin.castSucc_ne_last i
  · intro ha
    refine mem_map.mpr ⟨a.castPred ha, mem_univ _, Fin.castSucc_castPred a ha⟩

lemma not_mem_elimI_last {m : ℕ} : Fin.last m ∉ elimI m := by
  simp [mem_elimI_iff]

/-- Diagonal weights `s i * d i` on `I`, and `0` on the last index. -/
def elimIDiag (s d : Fin k → ℝ) {m : ℕ} (e : Fin m → Fin k) : Fin m.succ → ℝ :=
  fun a ↦ if h : a = Fin.last m then 0 else s (e (a.castPred h)) * d (e (a.castPred h))

lemma elimIDiag_last (s d : Fin k → ℝ) {m : ℕ} (e : Fin m → Fin k) :
    elimIDiag s d e (Fin.last m) = 0 := by
  simp [elimIDiag]

lemma elimIDiag_castSucc (s d : Fin k → ℝ) {m : ℕ} (e : Fin m → Fin k) (i : Fin m) :
    elimIDiag s d e i.castSucc = s (e i) * d (e i) := by
  simp [elimIDiag, Fin.castSucc_ne_last]

lemma elimIDiag_eq_zero_of_not_mem (s d : Fin k → ℝ) {m : ℕ} (e : Fin m → Fin k)
    {a : Fin m.succ} (ha : a ∉ elimI m) : elimIDiag s d e a = 0 := by
  have : a = Fin.last m := by
    simpa [mem_elimI_iff] using ha
  simp [this, elimIDiag_last]

/-- Pure Gram block on `elimSnoc e αidx` vs `elimSnoc e jidx` (no `I`-diagonal extras). -/
def elimGramZZ (s t : Fin k → ℝ) {m : ℕ} (e : Fin m → Fin k) (αidx jidx : Fin k) :
    Matrix (Fin m.succ) (Fin m.succ) ℝ :=
  of fun a b ↦
    s (elimSnoc e αidx a) * s (elimSnoc e jidx b) *
      (1 + t (elimSnoc e αidx a) * t (elimSnoc e jidx b)) ^ 2

/-- Last-entry correction when `α = j` (the pivot diagonal is not expanded). -/
def elimLastDiag (s : Fin k → ℝ) (d : Fin k → ℝ) {m : ℕ} (αidx jidx : Fin k) :
    Fin m.succ → ℝ :=
  fun a ↦ if a = Fin.last m ∧ αidx = jidx then s αidx * d αidx else 0

lemma elimSnoc_eq_iff {m : ℕ} {e : Fin m → Fin k}
    (he : e.Injective) {zα zj : Fin k} (hzα : zα ∉ Set.range e) (hzj : zj ∉ Set.range e)
    {a b : Fin m.succ} :
    elimSnoc e zα a = elimSnoc e zj b ↔ a = b ∧ (a = Fin.last m → zα = zj) := by
  constructor
  · intro h
    by_cases ha : a = Fin.last m
    · by_cases hb : b = Fin.last m
      · subst ha; subst hb
        simp only [elimSnoc_last] at h
        exact ⟨rfl, fun _ ↦ h⟩
      · subst ha
        have hb' : elimSnoc e zj b = e (b.castPred hb) := by simp [elimSnoc, hb]
        rw [elimSnoc_last, hb'] at h
        exact (hzα ⟨b.castPred hb, h.symm⟩).elim
    · by_cases hb : b = Fin.last m
      · subst hb
        have ha' : elimSnoc e zα a = e (a.castPred ha) := by simp [elimSnoc, ha]
        rw [ha', elimSnoc_last] at h
        exact (hzj ⟨a.castPred ha, h⟩).elim
      · have ha' : elimSnoc e zα a = e (a.castPred ha) := by simp [elimSnoc, ha]
        have hb' : elimSnoc e zj b = e (b.castPred hb) := by simp [elimSnoc, hb]
        rw [ha', hb'] at h
        have hab' : a.castPred ha = b.castPred hb := he h
        have hab : a = b := by
          rw [← Fin.castSucc_castPred a ha, ← Fin.castSucc_castPred b hb, hab']
        exact ⟨hab, fun hlast ↦ (ha hlast).elim⟩
  · rintro ⟨hab, hz⟩
    subst hab
    by_cases ha : a = Fin.last m
    · subst ha
      simp [elimSnoc, hz rfl]
    · simp [elimSnoc, ha]

/-- The `z`-`z` numerator minor is the Gram block plus the `I`-diagonal
(and the unexpanded last diagonal if `α = j`). -/
lemma MX_snoc_z_eq_gram_add_diag (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    {m : ℕ} (e : Fin m → Fin k) (he : e.Injective) {αidx jidx : Fin k}
    (hα : αidx ∉ Set.range e) (hj : jidx ∉ Set.range e) :
    (M (Xconfig s t ρ x)).submatrix
        (idxZ (p := p) ∘ elimSnoc e αidx) (idxZ (p := p) ∘ elimSnoc e jidx) =
      elimGramZZ s t e αidx jidx +
        diagonal (elimIDiag s (configD t ρ x) e) +
          diagonal (elimLastDiag s (configD t ρ x) αidx jidx) := by
  ext a b
  simp only [submatrix_apply, Function.comp_apply, Matrix.add_apply, of_apply,
    diagonal_apply, elimGramZZ]
  rw [MX_z_z s t ρ x hs ht hρ]
  rcases eq_or_ne a b with rfl | hab
  · by_cases ha : a = Fin.last m
    · subst ha
      simp [elimSnoc_last, elimIDiag_last, elimLastDiag]
    · simp [elimSnoc, ha, elimIDiag, elimLastDiag]
  · have hne : elimSnoc e αidx a ≠ elimSnoc e jidx b := fun h ↦
      hab ((elimSnoc_eq_iff he hα hj).mp h).1
    simp [hab, hne]

/-- EL04: expand a `z`-`z` numerator in the diagonal summands on `I`. -/
lemma det_MX_snoc_z_eq_sum (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    {m : ℕ} (e : Fin m → Fin k) (he : e.Injective) {αidx jidx : Fin k}
    (hα : αidx ∉ Set.range e) (hj : jidx ∉ Set.range e) :
    ((M (Xconfig s t ρ x)).submatrix
        (idxZ (p := p) ∘ elimSnoc e αidx) (idxZ (p := p) ∘ elimSnoc e jidx)).det =
      ∑ S ∈ (elimI m).powerset,
        (∏ i ∈ S, elimIDiag s (configD t ρ x) e i) *
          ((elimGramZZ s t e αidx jidx +
              diagonal (elimLastDiag s (configD t ρ x) αidx jidx)).submatrix
            (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ)
            (Subtype.val)).det := by
  rw [MX_snoc_z_eq_gram_add_diag s t ρ x hs ht hρ e he hα hj]
  have hrearr :
      elimGramZZ s t e αidx jidx +
          diagonal (elimIDiag s (configD t ρ x) e) +
            diagonal (elimLastDiag s (configD t ρ x) αidx jidx) =
        elimGramZZ s t e αidx jidx +
            diagonal (elimLastDiag s (configD t ρ x) αidx jidx) +
          diagonal (elimIDiag s (configD t ρ x) e) := by
    abel
  rw [hrearr, det_add_diagonal_eq_sum_subset _ _ (elimI m)]
  intro a ha
  exact elimIDiag_eq_zero_of_not_mem s (configD t ρ x) e ha

/-- Gram/coupling block for a last `y`-row against columns `snoc e j`. -/
def elimGramZY (s t : Fin k → ℝ) (ρval xval : ℝ) {m : ℕ} (e : Fin m → Fin k)
    (jidx : Fin k) : Matrix (Fin m.succ) (Fin m.succ) ℝ :=
  of fun a b ↦
    if a = Fin.last m then
      s (elimSnoc e jidx b) * ρval * (max (t (elimSnoc e jidx b) - xval) 0) ^ 2
    else
      s (elimSnoc e jidx a) * s (elimSnoc e jidx b) *
        (1 + t (elimSnoc e jidx a) * t (elimSnoc e jidx b)) ^ 2

/-- The opposite `y`-`z` block equals the `z`-`y` formula. -/
lemma MX_y_z (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j) (i : Fin k) (j : Fin p) :
    M (Xconfig s t ρ x) (idxY j) (idxZ i) =
      s i * ρ j * (max (t i - x j) 0) ^ 2 := by
  have hX := Xconfig_isSymm s t ρ x
  have hne : (idxY j : ConfigIdx k p) ≠ idxZ i := (idxZ_ne_idxY (p := p) i j).symm
  rw [← MX_z_y s t ρ x hs hρ i j]
  rw [M_apply_of_ne _ hX hne, M_apply_of_ne _ hX hne.symm, posPart_apply, posPart_apply, hX.apply]

/-- Row map for a last `y`-index after the `I`-block. -/
def elimRowY {m : ℕ} (e : Fin m → Fin k) (ℓ : Fin p) : Fin m.succ → ConfigIdx k p :=
  fun a ↦ if h : a = Fin.last m then idxY ℓ else idxZ (p := p) (e (a.castPred h))

lemma elimRowY_last {m : ℕ} (e : Fin m → Fin k) (ℓ : Fin p) :
    elimRowY e ℓ (Fin.last m) = idxY ℓ := by
  simp [elimRowY]

lemma elimRowY_castSucc {m : ℕ} (e : Fin m → Fin k) (ℓ : Fin p) (i : Fin m) :
    elimRowY e ℓ i.castSucc = idxZ (p := p) (e i) := by
  simp [elimRowY, Fin.castSucc_ne_last]

/-- The `y`-row numerator minor is the Gram/coupling block plus the `I`-diagonal. -/
lemma MX_snoc_y_eq_gram_add_diag (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    {m : ℕ} (e : Fin m → Fin k) (he : e.Injective) {jidx : Fin k} {ℓ : Fin p}
    (hj : jidx ∉ Set.range e) :
    (M (Xconfig s t ρ x)).submatrix (elimRowY e ℓ) (idxZ (p := p) ∘ elimSnoc e jidx) =
      elimGramZY s t (ρ ℓ) (x ℓ) e jidx +
        diagonal (elimIDiag s (configD t ρ x) e) := by
  ext a b
  simp only [submatrix_apply, Function.comp_apply, Matrix.add_apply, diagonal_apply,
    elimGramZY, of_apply]
  by_cases ha : a = Fin.last m
  · subst ha
    simp only [elimRowY_last, elimIDiag_last]
    rw [MX_y_z s t ρ x hs hρ]
    simp
  · have hae : elimRowY e ℓ a = idxZ (p := p) (e (a.castPred ha)) := by
      simp [elimRowY, ha]
    have hrow : elimSnoc e jidx a = e (a.castPred ha) := by
      simp [elimSnoc, ha]
    rw [hae, MX_z_z s t ρ x hs ht hρ]
    have hab_iff : e (a.castPred ha) = elimSnoc e jidx b ↔ a = b := by
      by_cases hb : b = Fin.last m
      · subst hb
        simp only [elimSnoc_last, Nat.succ_eq_add_one]
        constructor
        · intro h
          exact (hj ⟨a.castPred ha, h⟩).elim
        · intro h
          exact (ha h).elim
      · have hbe : elimSnoc e jidx b = e (b.castPred hb) := by simp [elimSnoc, hb]
        rw [hbe]
        constructor
        · intro h
          have : a.castPred ha = b.castPred hb := he h
          rw [← Fin.castSucc_castPred a ha, ← Fin.castSucc_castPred b hb, this]
        · intro hab
          subst hab
          rfl
    simp [ha, hrow, hab_iff, elimIDiag]

/-- EL04: expand a `y`-row numerator in the diagonal summands on `I`. -/
lemma det_MX_snoc_y_eq_sum (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    {m : ℕ} (e : Fin m → Fin k) (he : e.Injective) {jidx : Fin k} {ℓ : Fin p}
    (hj : jidx ∉ Set.range e) :
    ((M (Xconfig s t ρ x)).submatrix
        (elimRowY e ℓ) (idxZ (p := p) ∘ elimSnoc e jidx)).det =
      ∑ S ∈ (elimI m).powerset,
        (∏ i ∈ S, elimIDiag s (configD t ρ x) e i) *
          ((elimGramZY s t (ρ ℓ) (x ℓ) e jidx).submatrix
            (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ)
            (Subtype.val)).det := by
  rw [MX_snoc_y_eq_gram_add_diag s t ρ x hs ht hρ e he hj,
    det_add_diagonal_eq_sum_subset _ _ (elimI m)]
  intro a ha
  exact elimIDiag_eq_zero_of_not_mem s (configD t ρ x) e ha

/-! ### EL05 — principal cofactor signs are `+1` -/

/-- EL05: a principal cofactor sign is `(-1)^{p+p} = 1`. -/
lemma principal_cofactor_sign (q : ℕ) : (-1 : ℝ) ^ (q + q) = 1 := by
  rw [← two_mul, pow_mul, neg_one_pow_two, one_pow]

/-- EL05: deleting the same row and column subset contributes sign `+1`.
The leftover is the complementary principal minor, with no extra sign. -/
lemma det_piecewise_one_eq_compl_minor {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (S : Finset n) :
    (of (Sᶜ.piecewise A.row (1 : Matrix n n ℝ).row)).det =
      (A.submatrix (Subtype.val : {x // x ∈ Sᶜ} → n) Subtype.val).det :=
  det_piecewise_one_eq_submatrix_det A Sᶜ

/-! ### EL06 — factor positive `s` and `ρ` -/

/-- Homogeneity: row scales `u` and column scales `v` factor out of `det`. -/
lemma det_smul_row_col {n : Type*} [Fintype n] [DecidableEq n]
    (u v : n → ℝ) (A : Matrix n n ℝ) :
    (of fun i j ↦ u i * v j * A i j).det =
      (∏ i, u i) * (∏ j, v j) * A.det := by
  have hfun :
      (of fun i j ↦ u i * v j * A i j) =
        of fun i j ↦ u i * (v j * A i j) := by
    ext i j
    exact mul_assoc _ _ _
  have hcol : (of fun i j ↦ v j * A i j).det = (∏ j, v j) * A.det :=
    det_mul_row v A
  have hrow :
      (of fun i j ↦ u i * (v j * A i j)).det =
        (∏ i, u i) * (of fun i j ↦ v j * A i j).det :=
    det_mul_column u (of fun i j ↦ v j * A i j)
  rw [hfun, hrow, hcol]
  ring

/-- EL06: a `z`-`z` Gram block factors as `s`-row and `s`-column times the
unscaled kernel minor. -/
lemma det_elimGramZZ_factor (s t : Fin k → ℝ) {m : ℕ} (e : Fin m → Fin k)
    (αidx jidx : Fin k) :
    (elimGramZZ s t e αidx jidx).det =
      (∏ a, s (elimSnoc e αidx a)) * (∏ b, s (elimSnoc e jidx b)) *
        ((elimKernelZZ t).submatrix (elimSnoc e αidx) (elimSnoc e jidx)).det := by
  simpa [elimGramZZ, elimKernelZZ, submatrix_apply] using
    det_smul_row_col (s ∘ elimSnoc e αidx) (s ∘ elimSnoc e jidx)
      ((elimKernelZZ t).submatrix (elimSnoc e αidx) (elimSnoc e jidx))

/-- EL06: the same factoring on a complementary leftover of the `z`-`z` Gram. -/
lemma det_elimGramZZ_submatrix_factor (s t : Fin k → ℝ) {m : ℕ}
    (e : Fin m → Fin k) (αidx jidx : Fin k) (S : Finset (Fin m.succ)) :
    ((elimGramZZ s t e αidx jidx).submatrix
        (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ) Subtype.val).det =
      (∏ i : {x // x ∈ Sᶜ}, s (elimSnoc e αidx i.val)) *
        (∏ i : {x // x ∈ Sᶜ}, s (elimSnoc e jidx i.val)) *
          ((elimKernelZZ t).submatrix
            (elimSnoc e αidx ∘ (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ))
            (elimSnoc e jidx ∘ (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ))).det := by
  let u : {x // x ∈ Sᶜ} → ℝ := fun i ↦ s (elimSnoc e αidx i.val)
  let v : {x // x ∈ Sᶜ} → ℝ := fun i ↦ s (elimSnoc e jidx i.val)
  let K : Matrix {x // x ∈ Sᶜ} {x // x ∈ Sᶜ} ℝ :=
    (elimKernelZZ t).submatrix
      (elimSnoc e αidx ∘ (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ))
      (elimSnoc e jidx ∘ (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ))
  have hfun :
      (elimGramZZ s t e αidx jidx).submatrix
          (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ) Subtype.val =
        of fun i j ↦ u i * v j * K i j := by
    ext i j
    simp [elimGramZZ, elimKernelZZ, submatrix_apply, u, v, K]
  rw [hfun]
  exact det_smul_row_col (n := {x // x ∈ Sᶜ}) u v K

/-- Unscaled leftover kernel with a last truncated-square row. -/
def elimKernelMinorZY (t : Fin k → ℝ) (xval : ℝ) {m : ℕ}
    (e : Fin m → Fin k) (jidx : Fin k) : Matrix (Fin m.succ) (Fin m.succ) ℝ :=
  of fun a b ↦
    if a = Fin.last m then
      elimKernelZY t xval (elimSnoc e jidx b)
    else
      elimKernelZZ t (elimSnoc e jidx a) (elimSnoc e jidx b)

/-- EL06: a `y`-row Gram/coupling block factors `ρ` from the last row and
`s` from every `z`-row/column. -/
lemma det_elimGramZY_factor (s t : Fin k → ℝ) (ρval xval : ℝ) {m : ℕ}
    (e : Fin m → Fin k) (jidx : Fin k) :
    (elimGramZY s t ρval xval e jidx).det =
      (∏ a, if a = Fin.last m then ρval else s (elimSnoc e jidx a)) *
        (∏ b, s (elimSnoc e jidx b)) *
          (elimKernelMinorZY t xval e jidx).det := by
  have hfun :
      elimGramZY s t ρval xval e jidx =
        of fun a b ↦
          (if a = Fin.last m then ρval else s (elimSnoc e jidx a)) *
            s (elimSnoc e jidx b) *
              elimKernelMinorZY t xval e jidx a b := by
    ext a b
    simp only [elimGramZY, elimKernelMinorZY, elimKernelZZ, elimKernelZY, of_apply]
    split_ifs <;> ring
  rw [hfun]
  exact det_smul_row_col
    (fun a ↦ if a = Fin.last m then ρval else s (elimSnoc e jidx a))
    (fun b ↦ s (elimSnoc e jidx b))
    (elimKernelMinorZY t xval e jidx)

/-- EL07: `(1 + s t)² = s² (t - (-1/s))₊²` for `s, t > 0`. -/
lemma one_add_mul_sq_eq_sq_mul_max_sub {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (1 + s * t) ^ 2 = s ^ 2 * (max (t - (-1 / s)) 0) ^ 2 := by
  have hpos : 0 < t + s⁻¹ := add_pos ht (inv_pos.mpr hs)
  have hmax : max (t - (-1 / s)) 0 = t + s⁻¹ := by
    have : t - (-1 / s) = t + s⁻¹ := by
      rw [neg_div, sub_neg_eq_add, one_div]
    rw [this, max_eq_left hpos.le]
  rw [hmax]
  have hfac : s * (t + s⁻¹) = 1 + s * t := by
    rw [mul_add, mul_inv_cancel₀ hs.ne', add_comm]
  rw [← hfac, mul_pow]

/-- Reciprocal is antitone on `(0, ∞)`, so `-1/t` is increasing in `t > 0`. -/
lemma neg_one_div_le_neg_one_div {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (h : s ≤ t) :
    -1 / s ≤ -1 / t := by
  rw [neg_div, neg_div, neg_le_neg_iff, one_div, one_div]
  exact (inv_le_inv₀ ht hs).mpr h

lemma neg_one_div_lt_zero {t : ℝ} (ht : 0 < t) : -1 / t < 0 :=
  div_neg_of_neg_of_pos neg_one_lt_zero ht

/-- EL08: if `t` is positive and monotone, then `i ↦ -1 / t i` is monotone and negative. -/
lemma monotone_neg_one_div {k : ℕ} {t : Fin k → ℝ} (ht : ∀ i, 0 < t i) (hmono : Monotone t) :
    Monotone (fun i ↦ -1 / t i) :=
  fun _ _ hij ↦ neg_one_div_le_neg_one_div (ht _) (ht _) (hmono hij)

lemma neg_one_div_apply_lt_zero {k : ℕ} {t : Fin k → ℝ} (ht : ∀ i, 0 < t i) (i : Fin k) :
    -1 / t i < 0 :=
  neg_one_div_lt_zero (ht i)

/-- EL09: a later positive `t α ≥ t j` keeps `-1/t` nondecreasing. -/
lemma neg_one_div_le_neg_one_div_of_ge {tα tj : ℝ} (hα : 0 < tα) (hj : 0 < tj) (h : tj ≤ tα) :
    -1 / tj ≤ -1 / tα :=
  neg_one_div_le_neg_one_div hj hα h

/-- EL09: a last argument `x ≥ 0` follows every `-1 / t a`. -/
lemma neg_one_div_le_of_nonneg {ta x : ℝ} (hta : 0 < ta) (hx : 0 ≤ x) :
    -1 / ta ≤ x :=
  (neg_one_div_lt_zero hta).le.trans hx

/-! ### EL10 — leftover kernel minors are nonnegative -/

lemma elimSnoc_eq_finSnoc {m : ℕ} (e : Fin m → Fin k) (z : Fin k) :
    elimSnoc e z = Fin.snoc e z := by
  ext a
  by_cases ha : a = Fin.last m
  · subst ha
    simp [elimSnoc, Fin.snoc]
  · have hlt : a.val < m :=
      Nat.lt_of_le_of_ne (Nat.le_of_lt_succ a.isLt) fun h ↦ ha (Fin.ext h)
    simp [elimSnoc, Fin.snoc, ha, hlt]

lemma elimKernelZZ_eq_truncated (t : Fin k → ℝ) (ht : ∀ i, 0 < t i)
    (a b : Fin k) :
    elimKernelZZ t a b =
      t a ^ 2 * truncatedSquare (fun i ↦ -1 / t i) t a b := by
  simpa [elimKernelZZ, truncatedSquare] using
    one_add_mul_sq_eq_sq_mul_max_sub (ht a) (ht b)

/-- EL10: a `z`-`z` kernel minor with strictly increasing index maps is
nonnegative. -/
lemma det_elimKernelZZ_submatrix_nonneg (t : Fin k → ℝ)
    (ht : ∀ i, 0 < t i) (hmono : Monotone t)
    {n : ℕ} {I J : Fin n → Fin k} (hI : StrictMono I) (hJ : StrictMono J) :
    0 ≤ ((elimKernelZZ t).submatrix I J).det := by
  have hfun :
      (elimKernelZZ t).submatrix I J =
        of fun i j ↦ (t (I i) ^ 2) * (1 : ℝ) *
          (truncatedSquare (fun a ↦ -1 / t a) t).submatrix I J i j := by
    ext i j
    simp [submatrix_apply, elimKernelZZ_eq_truncated t ht]
  rw [hfun, det_smul_row_col]
  refine mul_nonneg (mul_nonneg (prod_nonneg fun i _ ↦ sq_nonneg _) (by simp))
    ((isTotallyNonneg_truncatedSquare
        (monotone_neg_one_div ht hmono) hmono) n I J hI hJ)

/-- EL10: the same minor stays nonnegative for merely monotone maps. -/
lemma det_elimKernelZZ_submatrix_monotone (t : Fin k → ℝ)
    (ht : ∀ i, 0 < t i) (hmono : Monotone t)
    {n : ℕ} {I J : Fin n → Fin k} (hI : Monotone I) (hJ : Monotone J) :
    0 ≤ ((elimKernelZZ t).submatrix I J).det := by
  have hTN : IsTotallyNonneg (truncatedSquare (fun a ↦ -1 / t a) t) :=
    isTotallyNonneg_truncatedSquare (monotone_neg_one_div ht hmono) hmono
  have hfun :
      (elimKernelZZ t).submatrix I J =
        of fun i j ↦ (t (I i) ^ 2) * (1 : ℝ) *
          (truncatedSquare (fun a ↦ -1 / t a) t).submatrix I J i j := by
    ext i j
    simp [submatrix_apply, elimKernelZZ_eq_truncated t ht]
  rw [hfun, det_smul_row_col]
  refine mul_nonneg (mul_nonneg (prod_nonneg fun i _ ↦ sq_nonneg _) (by simp))
    (hTN.det_submatrix_monotone hI hJ)

lemma elimSnoc_monotone {m : ℕ} {e : Fin m → Fin k} (he : Monotone e)
    {z : Fin k} (hz : ∀ i, e i ≤ z) : Monotone (elimSnoc e z) := by
  intro a b hab
  by_cases hb : b = Fin.last m
  · subst hb
    by_cases ha : a = Fin.last m
    · subst ha
      simp [elimSnoc]
    · simp only [elimSnoc, Nat.succ_eq_add_one, ha, ↓reduceDIte]
      exact hz _
  · have ha : a ≠ Fin.last m := by
      intro ha
      exact hb (le_antisymm (Fin.le_last b) (ha ▸ hab))
    simp only [elimSnoc, Nat.succ_eq_add_one, ha, ↓reduceDIte, hb, ge_iff_le]
    refine he ?_
    rw [← Fin.castSucc_le_castSucc_iff, Fin.castSucc_castPred, Fin.castSucc_castPred]
    exact hab

lemma elimSnoc_strictMono {m : ℕ} {e : Fin m → Fin k} (he : StrictMono e)
    {z : Fin k} (hz : ∀ i, e i < z) : StrictMono (elimSnoc e z) := by
  intro a b hab
  by_cases hb : b = Fin.last m
  · subst hb
    have ha : a ≠ Fin.last m := ne_of_lt hab
    simp only [elimSnoc, Nat.succ_eq_add_one, ha, ↓reduceDIte, gt_iff_lt]
    exact hz _
  · have ha : a ≠ Fin.last m := fun h ↦
      hb (le_antisymm (Fin.le_last b) (h ▸ hab.le))
    simp only [elimSnoc, Nat.succ_eq_add_one, ha, ↓reduceDIte, hb, gt_iff_lt]
    refine he ?_
    rw [← Fin.castSucc_lt_castSucc_iff, Fin.castSucc_castPred, Fin.castSucc_castPred]
    exact hab

lemma castLE_lt {m : ℕ} (hm : m ≤ k) {z : Fin k} (hz : m ≤ z.val) (i : Fin m) :
    Fin.castLE hm i < z := by
  exact Nat.lt_of_lt_of_le i.isLt hz

lemma det_elimKernelZZ_elimSnoc_nonneg (t : Fin k → ℝ)
    (ht : ∀ i, 0 < t i) (hmono : Monotone t)
    {m : ℕ} {e : Fin m → Fin k} (he : StrictMono e)
    {αidx jidx : Fin k} (hα : ∀ i, e i < αidx) (hj : ∀ i, e i < jidx) :
    0 ≤ ((elimKernelZZ t).submatrix (elimSnoc e αidx) (elimSnoc e jidx)).det :=
  det_elimKernelZZ_submatrix_nonneg t ht hmono
    (elimSnoc_strictMono he hα) (elimSnoc_strictMono he hj)

lemma det_submatrix_subtype_eq_orderEmb {n : Type*}
    [LinearOrder n] [DecidableEq n]
    (A : Matrix n n ℝ) (S : Finset n) :
    (A.submatrix (Subtype.val : {x // x ∈ S} → n) Subtype.val).det =
      (A.submatrix (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl)).det := by
  rw [← det_submatrix_equiv_self (S.orderIsoOfFin rfl).toEquiv]
  rfl

/-- EL10: complementary leftover of a `z`-`z` kernel minor is nonnegative. -/
lemma det_elimKernelZZ_compl_nonneg (t : Fin k → ℝ)
    (ht : ∀ i, 0 < t i) (hmono : Monotone t)
    {m : ℕ} {e : Fin m → Fin k} (he : StrictMono e)
    {αidx jidx : Fin k} (hα : ∀ i, e i < αidx) (hj : ∀ i, e i < jidx)
    (S : Finset (Fin m.succ)) :
    0 ≤ ((elimKernelZZ t).submatrix
      (elimSnoc e αidx ∘ (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ))
      (elimSnoc e jidx ∘ (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ))).det := by
  have hre :=
    det_submatrix_subtype_eq_orderEmb
      ((elimKernelZZ t).submatrix (elimSnoc e αidx) (elimSnoc e jidx)) Sᶜ
  have hsm :
      ((elimKernelZZ t).submatrix (elimSnoc e αidx) (elimSnoc e jidx)).submatrix
          (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ) Subtype.val =
        (elimKernelZZ t).submatrix
          (elimSnoc e αidx ∘ (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ))
          (elimSnoc e jidx ∘ (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ)) := by
    ext i j
    rfl
  rw [← hsm, hre]
  refine det_elimKernelZZ_submatrix_nonneg t ht hmono ?_ ?_
  · exact (elimSnoc_strictMono he hα).comp (Sᶜ.orderEmbOfFin rfl).strictMono
  · exact (elimSnoc_strictMono he hj).comp (Sᶜ.orderEmbOfFin rfl).strictMono

/-- Row argument of the elimination step: the vector on `Fin m.succ` whose last entry is `xval` and
whose other entries are `-1 / t` along the indices selected by `elimSnoc e jidx`. -/
def elimRowArg (t : Fin k → ℝ) (xval : ℝ) {m : ℕ}
    (e : Fin m → Fin k) (jidx : Fin k) : Fin m.succ → ℝ :=
  fun a ↦ if a = Fin.last m then xval else -1 / t (elimSnoc e jidx a)

/-- Column argument of the elimination step: `t` evaluated along `elimSnoc e jidx`. -/
def elimColArg (t : Fin k → ℝ) {m : ℕ}
    (e : Fin m → Fin k) (jidx : Fin k) : Fin m.succ → ℝ :=
  fun b ↦ t (elimSnoc e jidx b)

lemma elimRowArg_monotone (t : Fin k → ℝ) (ht : ∀ i, 0 < t i) (hmono : Monotone t)
    (xval : ℝ) (hx : 0 ≤ xval) {m : ℕ} {e : Fin m → Fin k} (he : Monotone e)
    {jidx : Fin k} (hj : ∀ i, e i ≤ jidx) :
    Monotone (elimRowArg t xval e jidx) := by
  intro a b hab
  by_cases hb : b = Fin.last m
  · subst hb
    by_cases ha : a = Fin.last m
    · subst ha
      simp [elimRowArg]
    · simp only [elimRowArg, Nat.succ_eq_add_one, ha, ↓reduceIte]
      exact neg_one_div_le_of_nonneg (ht _) hx
  · have ha : a ≠ Fin.last m := fun h ↦
      hb (le_antisymm (Fin.le_last b) (h ▸ hab))
    simp only [elimRowArg, Nat.succ_eq_add_one, ha, ↓reduceIte, hb, ge_iff_le]
    exact neg_one_div_le_neg_one_div (ht _) (ht _)
      (hmono (elimSnoc_monotone he hj hab))

lemma elimColArg_monotone (t : Fin k → ℝ) (hmono : Monotone t)
    {m : ℕ} {e : Fin m → Fin k} (he : Monotone e)
    {jidx : Fin k} (hj : ∀ i, e i ≤ jidx) :
    Monotone (elimColArg t e jidx) :=
  hmono.comp (elimSnoc_monotone he hj)

lemma elimKernelMinorZY_eq_scaled (t : Fin k → ℝ) (ht : ∀ i, 0 < t i)
    (xval : ℝ) {m : ℕ} (e : Fin m → Fin k) (jidx : Fin k) (a b : Fin m.succ) :
    elimKernelMinorZY t xval e jidx a b =
      (if a = Fin.last m then (1 : ℝ) else t (elimSnoc e jidx a) ^ 2) *
        truncatedSquare (elimRowArg t xval e jidx) (elimColArg t e jidx) a b := by
  by_cases ha : a = Fin.last m
  · subst ha
    simp [elimKernelMinorZY, elimKernelZY, elimRowArg, elimColArg, truncatedSquare]
  · simp only [elimKernelMinorZY, elimKernelZZ, elimRowArg, elimColArg, truncatedSquare,
      ha, ↓reduceIte, of_apply]
    simpa using one_add_mul_sq_eq_sq_mul_max_sub (ht _) (ht _)

/-- EL10: a last truncated-square row still gives a nonnegative minor. -/
lemma det_elimKernelMinorZY_nonneg (t : Fin k → ℝ)
    (ht : ∀ i, 0 < t i) (hmono : Monotone t)
    (xval : ℝ) (hx : 0 ≤ xval) {m : ℕ} {e : Fin m → Fin k}
    (he : Monotone e) {jidx : Fin k} (hj : ∀ i, e i ≤ jidx) :
    0 ≤ (elimKernelMinorZY t xval e jidx).det := by
  have hfun :
      elimKernelMinorZY t xval e jidx =
        of fun a b ↦
          (if a = Fin.last m then (1 : ℝ) else t (elimSnoc e jidx a) ^ 2) * (1 : ℝ) *
            truncatedSquare (elimRowArg t xval e jidx) (elimColArg t e jidx) a b := by
    ext a b
    simp [elimKernelMinorZY_eq_scaled t ht]
  rw [hfun, det_smul_row_col]
  refine mul_nonneg (mul_nonneg (prod_nonneg fun a _ ↦ ?_) (by simp)) ?_
  · split_ifs
    · exact zero_le_one
    · exact sq_nonneg _
  · exact (isTotallyNonneg_truncatedSquare
        (elimRowArg_monotone t ht hmono xval hx he hj)
        (elimColArg_monotone t hmono he hj)).det_submatrix_monotone
      monotone_id monotone_id

lemma det_elimGramZY_submatrix_factor (s t : Fin k → ℝ) (ρval xval : ℝ)
    {m : ℕ} (e : Fin m → Fin k) (jidx : Fin k) (S : Finset (Fin m.succ)) :
    ((elimGramZY s t ρval xval e jidx).submatrix
        (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ) Subtype.val).det =
      (∏ i : {x // x ∈ Sᶜ},
          if i.val = Fin.last m then ρval else s (elimSnoc e jidx i.val)) *
        (∏ i : {x // x ∈ Sᶜ}, s (elimSnoc e jidx i.val)) *
          ((elimKernelMinorZY t xval e jidx).submatrix
            (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ) Subtype.val).det := by
  let u : {x // x ∈ Sᶜ} → ℝ :=
    fun i ↦ if i.val = Fin.last m then ρval else s (elimSnoc e jidx i.val)
  let v : {x // x ∈ Sᶜ} → ℝ := fun i ↦ s (elimSnoc e jidx i.val)
  let K : Matrix {x // x ∈ Sᶜ} {x // x ∈ Sᶜ} ℝ :=
    (elimKernelMinorZY t xval e jidx).submatrix Subtype.val Subtype.val
  have hfun :
      (elimGramZY s t ρval xval e jidx).submatrix
          (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ) Subtype.val =
        of fun i j ↦ u i * v j * K i j := by
    ext i j
    simp only [submatrix_apply, elimGramZY, elimKernelMinorZY, elimKernelZZ, elimKernelZY,
      of_apply, u, v, K]
    split_ifs <;> ring
  rw [hfun]
  exact det_smul_row_col (n := {x // x ∈ Sᶜ}) u v K

/-- EL10: complementary leftover of a `y`-row kernel minor is nonnegative. -/
lemma det_elimKernelMinorZY_compl_nonneg (t : Fin k → ℝ)
    (ht : ∀ i, 0 < t i) (hmono : Monotone t)
    (xval : ℝ) (hx : 0 ≤ xval) {m : ℕ} {e : Fin m → Fin k}
    (he : Monotone e) {jidx : Fin k} (hj : ∀ i, e i ≤ jidx)
    (S : Finset (Fin m.succ)) :
    0 ≤ ((elimKernelMinorZY t xval e jidx).submatrix
      (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ) Subtype.val).det := by
  have hre :=
    det_submatrix_subtype_eq_orderEmb (elimKernelMinorZY t xval e jidx) Sᶜ
  rw [hre]
  have hfun :
      (elimKernelMinorZY t xval e jidx).submatrix
          (Sᶜ.orderEmbOfFin rfl) (Sᶜ.orderEmbOfFin rfl) =
        of fun i j ↦
          (if (Sᶜ.orderEmbOfFin rfl i) = Fin.last m then (1 : ℝ)
            else t (elimSnoc e jidx (Sᶜ.orderEmbOfFin rfl i)) ^ 2) * (1 : ℝ) *
            (truncatedSquare (elimRowArg t xval e jidx)
              (elimColArg t e jidx)).submatrix
              (Sᶜ.orderEmbOfFin rfl) (Sᶜ.orderEmbOfFin rfl) i j := by
    ext i j
    simp [submatrix_apply, elimKernelMinorZY_eq_scaled t ht]
  rw [hfun, det_smul_row_col]
  refine mul_nonneg (mul_nonneg (prod_nonneg fun _ _ ↦ ?_) (by simp)) ?_
  · split_ifs
    · exact zero_le_one
    · exact sq_nonneg _
  · exact (isTotallyNonneg_truncatedSquare
        (elimRowArg_monotone t ht hmono xval hx he hj)
        (elimColArg_monotone t hmono he hj)).det_submatrix_monotone
      (Sᶜ.orderEmbOfFin rfl).strictMono.monotone
      (Sᶜ.orderEmbOfFin rfl).strictMono.monotone

/-! ### EL11 — residual columns are nonnegative -/

lemma elimIDiag_nonneg (s : Fin k → ℝ) (d : Fin k → ℝ)
    (hs : ∀ i, 0 < s i) (hd : ∀ i, 0 ≤ d i) {m : ℕ} (e : Fin m → Fin k)
    (a : Fin m.succ) : 0 ≤ elimIDiag s d e a := by
  by_cases ha : a = Fin.last m
  · subst ha
    simp [elimIDiag]
  · simp only [elimIDiag, Nat.succ_eq_add_one, ha, ↓reduceDIte]
    exact mul_nonneg (hs _).le (hd _)

lemma elimRowY_eq_snoc {m : ℕ} (e : Fin m → Fin k) (ℓ : Fin p) :
    elimRowY e ℓ = Fin.snoc (idxZ (p := p) ∘ e) (idxY ℓ) := by
  ext a
  by_cases ha : a = Fin.last m
  · subst ha
    simp [elimRowY, Fin.snoc]
  · have hlt : a.val < m :=
      Nat.lt_of_le_of_ne (Nat.le_of_lt_succ a.isLt) fun h ↦ ha (Fin.ext h)
    simp [elimRowY, Fin.snoc, ha, hlt]

lemma idxZ_comp_snoc {m : ℕ} (e : Fin m → Fin k) (z : Fin k) :
    idxZ (p := p) ∘ Fin.snoc e z = idxZ (p := p) ∘ elimSnoc e z := by
  simp [elimSnoc_eq_finSnoc]

/-- EL11: a later `z`-`z` numerator minor is nonnegative. -/
lemma det_MX_snoc_z_nonneg (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hmono : Monotone t)
    (hρ : ∀ j, 0 < ρ j)
    {m : ℕ} {e : Fin m → Fin k} (he : StrictMono e) {αidx jidx : Fin k}
    (hα : αidx ∉ Set.range e) (hj : jidx ∉ Set.range e)
    (hαlt : ∀ i, e i < αidx) (hjlt : ∀ i, e i < jidx) (hαj : αidx ≠ jidx) :
    0 ≤ ((M (Xconfig s t ρ x)).submatrix
        (idxZ (p := p) ∘ elimSnoc e αidx) (idxZ (p := p) ∘ elimSnoc e jidx)).det := by
  have hlast :
      elimLastDiag (m := m) s (configD t ρ x) αidx jidx = 0 := by
    funext a
    simp [elimLastDiag, hαj]
  rw [det_MX_snoc_z_eq_sum s t ρ x hs ht hρ e he.injective hα hj]
  refine sum_nonneg fun S _ ↦ mul_nonneg
      (prod_nonneg fun i _ ↦
        elimIDiag_nonneg s (configD t ρ x) hs
          (fun i ↦ (configD_pos t hρ x i).le) e i) ?_
  have hG :
      elimGramZZ s t e αidx jidx +
          diagonal (elimLastDiag (m := m) s (configD t ρ x) αidx jidx) =
        elimGramZZ s t e αidx jidx := by
    ext a b
    simp [hlast, Matrix.add_apply]
  simp_rw [hG]
  have hf := det_elimGramZZ_submatrix_factor s t e αidx jidx S
  rw [hf]
  refine mul_nonneg (mul_nonneg
      (prod_nonneg fun _ _ ↦ (hs _).le)
      (prod_nonneg fun _ _ ↦ (hs _).le))
    (det_elimKernelZZ_compl_nonneg t ht hmono he hαlt hjlt S)

/-- EL11: a `y`-row numerator minor is nonnegative. -/
lemma det_MX_snoc_y_nonneg (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hmono : Monotone t)
    (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j)
    {m : ℕ} {e : Fin m → Fin k} (he : StrictMono e) {jidx : Fin k} {ℓ : Fin p}
    (hj : jidx ∉ Set.range e) (hjlt : ∀ i, e i ≤ jidx) :
    0 ≤ ((M (Xconfig s t ρ x)).submatrix
        (elimRowY e ℓ) (idxZ (p := p) ∘ elimSnoc e jidx)).det := by
  rw [det_MX_snoc_y_eq_sum s t ρ x hs ht hρ e he.injective hj]
  refine sum_nonneg fun S _ ↦ mul_nonneg
      (prod_nonneg fun i _ ↦
        elimIDiag_nonneg s (configD t ρ x) hs
          (fun i ↦ (configD_pos t hρ x i).le) e i) ?_
  have hf := det_elimGramZY_submatrix_factor s t (ρ ℓ) (x ℓ) e jidx S
  rw [hf]
  refine mul_nonneg (mul_nonneg
      (prod_nonneg fun i _ ↦ by
        split_ifs
        · exact (hρ ℓ).le
        · exact (hs _).le)
      (prod_nonneg fun _ _ ↦ (hs _).le))
    (det_elimKernelMinorZY_compl_nonneg t ht hmono (x ℓ) (hx ℓ)
      he.monotone hjlt S)

/-- EL11: residual of a later `z`-index against a leading `z`-pivot is `≥ 0`. -/
lemma schurComplementEntry_z_later_nonneg (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hmono : Monotone t)
    (hρ : ∀ j, 0 < ρ j)
    {m : ℕ} (hm : m ≤ k) {j α : Fin k} (hj : m ≤ j.val) (hα : m ≤ α.val)
    (hαj : α ≠ j) :
    0 ≤ schurComplementEntry
      ((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p)))
      (Fin.castLE hm) α j := by
  have he : StrictMono (Fin.castLE hm) := Fin.strictMono_castLE hm
  have hjn : j ∉ Set.range (Fin.castLE hm) := by
    rintro ⟨i, hi⟩
    have : (i : ℕ) = j.val := by
      simpa [Fin.ext_iff] using hi
    exact (i.isLt.trans_le hj).ne this
  have hαn : α ∉ Set.range (Fin.castLE hm) := by
    rintro ⟨i, hi⟩
    have : (i : ℕ) = α.val := by
      simpa [Fin.ext_iff] using hi
    exact (i.isLt.trans_le hα).ne this
  have hdet := MX_zBlock_leading_det_pos s t ρ x hs ht hρ hm
  have hnum := det_MX_snoc_z_nonneg s t ρ x hs ht hmono hρ he hαn hjn
    (fun i ↦ castLE_lt hm hα i) (fun i ↦ castLE_lt hm hj i) hαj
  rw [schurComplementEntry_eq_minor_div_det
      ((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p)))
      (Fin.castLE hm) he.injective hαn hjn hdet.ne']
  refine div_nonneg ?_ hdet.le
  simpa [submatrix_submatrix, Function.comp_assoc, elimSnoc_eq_finSnoc] using hnum


/-- EL11: residual of a `y`-index against a leading `z`-pivot is `≥ 0`. -/
lemma schurComplementEntry_y_later_nonneg (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hmono : Monotone t)
    (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j)
    {m : ℕ} (hm : m ≤ k) {j : Fin k} (hj : m ≤ j.val) (ℓ : Fin p) :
    0 ≤ schurComplementEntry (M (Xconfig s t ρ x))
      (idxZ (p := p) ∘ Fin.castLE hm) (idxY ℓ) (idxZ j) := by
  have he : StrictMono (Fin.castLE hm) := Fin.strictMono_castLE hm
  have hZinj : (idxZ (p := p) : Fin k → ConfigIdx k p).Injective :=
    fun _ _ h ↦ (idxZ_inj (p := p)).mp h
  have heZ : (idxZ (p := p) ∘ Fin.castLE hm).Injective :=
    hZinj.comp (Fin.castLE_injective hm)
  have hjn : j ∉ Set.range (Fin.castLE hm) := by
    rintro ⟨i, hi⟩
    exact (i.isLt.trans_le hj).ne (by simpa [Fin.ext_iff] using hi)
  have hjnZ : idxZ (p := p) j ∉ Set.range (idxZ (p := p) ∘ Fin.castLE hm) := by
    rintro ⟨i, hi⟩
    exact hjn ⟨i, (idxZ_inj (p := p)).mp hi⟩
  have hYn : idxY (k := k) ℓ ∉ Set.range (idxZ (p := p) ∘ Fin.castLE hm) := by
    rintro ⟨i, hi⟩
    exact (idxZ_ne_idxY (p := p) (Fin.castLE hm i) ℓ) hi
  have hdet := MX_zBlock_leading_det_pos s t ρ x hs ht hρ hm
  have hdet' :
      ((M (Xconfig s t ρ x)).submatrix
          (idxZ (p := p) ∘ Fin.castLE hm) (idxZ (p := p) ∘ Fin.castLE hm)).det ≠ 0 := by
    simpa [submatrix_submatrix] using hdet.ne'
  have hnum := det_MX_snoc_y_nonneg s t ρ x hs ht hmono hρ hx he (ℓ := ℓ) hjn
    (fun i ↦ (castLE_lt hm hj i).le)
  rw [schurComplementEntry_eq_minor_div_det (M (Xconfig s t ρ x))
      (idxZ (p := p) ∘ Fin.castLE hm) heZ hYn hjnZ hdet']
  refine div_nonneg ?_ hdet.le
  simpa [elimRowY_eq_snoc, elimSnoc_eq_finSnoc, Function.comp_assoc,
    submatrix_submatrix, Fin.comp_snoc] using hnum

/-! ### Index sets `E` and `T` for elimination -/

/-- Case split on a configuration index. -/
lemma elim_configIdx_cases {P : ConfigIdx k p → Prop} (α : ConfigIdx k p)
    (h0 : P idxZ0) (hz : ∀ i, P (idxZ i)) (hy : ∀ j, P (idxY j)) : P α := by
  rw [← (configIdxEquiv k p).symm_apply_apply α]
  rcases configIdxEquiv k p α with o | j
  · rcases o with _ | i
    · simpa [idxZ0] using h0
    · simpa [idxZ] using hz i
  · simpa [idxY] using hy j

lemma idxY_inj {j ℓ : Fin p} : idxY (k := k) j = idxY ℓ ↔ j = ℓ := by
  constructor
  · intro h
    exact Fin.ext (by simpa [idxY_val] using congrArg Fin.val h)
  · rintro rfl; rfl

lemma MX_isHermitian (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    (M (Xconfig s t ρ x)).IsHermitian :=
  (M_posSemidef (Xconfig_posSemidef s t ρ x)).isHermitian

lemma MX_isSymm (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    (M (Xconfig s t ρ x)).IsSymm :=
  isHermitian_iff_isSymm.mp (MX_isHermitian s t ρ x)

/-- `E`-embedding: `none` is `z₀`, `some i` is `zᵢ`. -/
def elimEEmbed : Option (Fin k) → ConfigIdx k p
  | none => idxZ0
  | some i => idxZ i

/-- `T`-embedding: the `y`-indices. -/
def elimT : Fin p → ConfigIdx k p := idxY

lemma elimEEmbed_none : elimEEmbed (p := p) (none : Option (Fin k)) = idxZ0 := rfl
lemma elimEEmbed_some (i : Fin k) : elimEEmbed (p := p) (some i) = idxZ i := rfl
lemma elimT_apply (j : Fin p) : elimT (k := k) j = idxY j := rfl

lemma configIdxEquiv_idxZ0 : configIdxEquiv k p (idxZ0 : ConfigIdx k p) = Sum.inl none :=
  Equiv.apply_symm_apply _ _

lemma configIdxEquiv_idxZ (i : Fin k) :
    configIdxEquiv k p (idxZ (p := p) i) = Sum.inl (some i) :=
  Equiv.apply_symm_apply _ _

lemma configIdxEquiv_idxY (j : Fin p) :
    configIdxEquiv k p (idxY (k := k) j) = Sum.inr j :=
  Equiv.apply_symm_apply _ _

lemma elimEEmbed_ne_elimT (a : Option (Fin k)) (j : Fin p) :
    elimEEmbed (p := p) a ≠ elimT (k := k) j := by
  cases a with
  | none => exact idxZ0_ne_idxY j
  | some i => exact idxZ_ne_idxY i j

/-- The `E`-block of `M (Xconfig s t ρ x)`: rows and columns indexed by the axis vector and the left
vectors through `elimEEmbed`. -/
def elimEE (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Matrix (Option (Fin k)) (Option (Fin k)) ℝ :=
  (M (Xconfig s t ρ x)).submatrix elimEEmbed elimEEmbed

/-- The block of `M (Xconfig s t ρ x)` with `E`-rows (via `elimEEmbed`) and right-vector columns
(via `elimT`). -/
def elimET (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Matrix (Option (Fin k)) (Fin p) ℝ :=
  (M (Xconfig s t ρ x)).submatrix elimEEmbed elimT

/-- The block of `M (Xconfig s t ρ x)` with right-vector rows (via `elimT`) and `E`-columns (via
`elimEEmbed`). -/
def elimTE (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Matrix (Fin p) (Option (Fin k)) ℝ :=
  (M (Xconfig s t ρ x)).submatrix elimT elimEEmbed

/-- The right-vector block of `M (Xconfig s t ρ x)`: rows and columns indexed through `elimT`. -/
def elimTT (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  (M (Xconfig s t ρ x)).submatrix elimT elimT

lemma elimEE_none_none (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    elimEE s t ρ x none none = M (Xconfig s t ρ x) idxZ0 idxZ0 := rfl

lemma elimEE_none_some (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (i : Fin k) :
    elimEE s t ρ x none (some i) = 0 :=
  MX_z0_z s t ρ x i

lemma elimEE_some_none (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (i : Fin k) :
    elimEE s t ρ x (some i) none = 0 :=
  MX_z_z0 s t ρ x i

lemma elimEE_some_some (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (i h : Fin k) :
    elimEE s t ρ x (some i) (some h) =
      M (Xconfig s t ρ x) (idxZ i) (idxZ h) := rfl

lemma elimEE_isHermitian (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    (elimEE s t ρ x).IsHermitian :=
  (MX_isHermitian s t ρ x).submatrix elimEEmbed

lemma elimEE_isSymm (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    (elimEE s t ρ x).IsSymm :=
  isHermitian_iff_isSymm.mp (elimEE_isHermitian s t ρ x)

lemma elimEE_mulVec_none (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (v : Option (Fin k) → ℝ) :
    (elimEE s t ρ x *ᵥ v) none =
      M (Xconfig s t ρ x) idxZ0 idxZ0 * v none := by
  simp [mulVec, dotProduct, Fintype.sum_option, elimEE_none_none, elimEE_none_some]

lemma elimEE_mulVec_some (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (v : Option (Fin k) → ℝ) (i : Fin k) :
    (elimEE s t ρ x *ᵥ v) (some i) =
      (((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p))) *ᵥ
        fun h => v (some h)) i := by
  simp [mulVec, dotProduct, Fintype.sum_option, elimEE_some_none, elimEE_some_some,
    submatrix_apply]

lemma elimEE_quad (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (v : Option (Fin k) → ℝ) :
    v ⬝ᵥ (elimEE s t ρ x *ᵥ v) =
      M (Xconfig s t ρ x) idxZ0 idxZ0 * v none * v none +
        (fun i => v (some i)) ⬝ᵥ
          ((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p)) *ᵥ
            fun i => v (some i)) := by
  simp [dotProduct, Fintype.sum_option, elimEE_mulVec_none, elimEE_mulVec_some]
  ring

/-- EL13: the principal `E`-block is positive definite. -/
lemma elimEE_posDef (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) :
    (elimEE s t ρ x).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (elimEE_isHermitian s t ρ x) fun v hv => ?_
  have hstar : star v = v := funext fun _ => star_trivial _
  rw [hstar, elimEE_quad]
  have hZ := MX_zBlock_posDef s t ρ x hs ht hρ
  have h00 := MX_z0_z0_pos s t ρ x hs hx
  have hZnn :=
    (posSemidef_iff_dotProduct_mulVec.mp hZ.posSemidef).2 (fun i => v (some i))
  have hstarZ : star (fun i : Fin k => v (some i)) = fun i => v (some i) :=
    funext fun _ => star_trivial _
  rw [hstarZ] at hZnn
  rcases eq_or_ne (v none) 0 with hv0 | hvn
  · have hsome : (fun i : Fin k => v (some i)) ≠ 0 := by
      intro h
      apply hv
      funext a
      cases a with
      | none => exact hv0
      | some i => exact congrFun h i
    have hpos := hZ.dotProduct_mulVec_pos hsome
    simp [hv0] at hpos ⊢
    simpa [hstarZ] using hpos
  · nlinarith [sq_pos_of_ne_zero hvn, h00, hZnn]

lemma elimTE_eq_conjTranspose (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    elimTE s t ρ x = (elimET s t ρ x)ᴴ := by
  ext i j
  simp only [elimTE, submatrix_apply, elimET, conjTranspose_apply, star_trivial]
  exact (MX_isSymm s t ρ x).apply _ _

lemma M_submatrix_sumElim (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    (M (Xconfig s t ρ x)).submatrix
        (Sum.elim (elimEEmbed (p := p)) (elimT (k := k)))
        (Sum.elim (elimEEmbed (p := p)) (elimT (k := k))) =
      fromBlocks (elimEE s t ρ x) (elimET s t ρ x)
        (elimTE s t ρ x) (elimTT s t ρ x) := by
  ext i j
  cases i <;> cases j <;> rfl

/-- Schur complement of the `E`-block in the `T`-block. -/
def elimSchurR (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  elimTT s t ρ x - elimTE s t ρ x * (elimEE s t ρ x)⁻¹ * elimET s t ρ x

/-- Extension by zero off the `T`-indices. -/
def extendByZeroT (R : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (ConfigIdx k p) (ConfigIdx k p) ℝ :=
  fun α β =>
    match configIdxEquiv k p α, configIdxEquiv k p β with
    | Sum.inr j, Sum.inr ℓ => R j ℓ
    | _, _ => 0

lemma extendByZeroT_y_y (R : Matrix (Fin p) (Fin p) ℝ) (j ℓ : Fin p) :
    extendByZeroT (k := k) R (idxY j) (idxY ℓ) = R j ℓ := by
  simp [extendByZeroT, configIdxEquiv_idxY]

lemma extendByZeroT_z0_left (R : Matrix (Fin p) (Fin p) ℝ) (β : ConfigIdx k p) :
    extendByZeroT (k := k) R idxZ0 β = 0 := by
  simp [extendByZeroT, configIdxEquiv_idxZ0]

lemma extendByZeroT_z_left (R : Matrix (Fin p) (Fin p) ℝ) (i : Fin k)
    (β : ConfigIdx k p) :
    extendByZeroT (k := k) R (idxZ i) β = 0 := by
  simp [extendByZeroT, configIdxEquiv_idxZ]

lemma extendByZeroT_z0_right (R : Matrix (Fin p) (Fin p) ℝ) (α : ConfigIdx k p) :
    extendByZeroT (k := k) R α idxZ0 = 0 := by
  simp [extendByZeroT, configIdxEquiv_idxZ0]

lemma extendByZeroT_z_right (R : Matrix (Fin p) (Fin p) ℝ) (α : ConfigIdx k p)
    (i : Fin k) :
    extendByZeroT (k := k) R α (idxZ i) = 0 := by
  simp [extendByZeroT, configIdxEquiv_idxZ]

/-- EL13: the `T`-Schur complement of `E` is positive semidefinite. -/
lemma elimSchurR_posSemidef (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) :
    (elimSchurR s t ρ x).PosSemidef := by
  have hE := elimEE_posDef s t ρ x hs ht hρ hx
  have hblk := M_submatrix_sumElim s t ρ x
  have hPSD :=
    (M_posSemidef (Xconfig_posSemidef s t ρ x)).submatrix
      (Sum.elim (elimEEmbed (p := p)) (elimT (k := k)))
  rw [hblk, elimTE_eq_conjTranspose] at hPSD
  let := hE.isUnit.invertible
  simpa [elimSchurR, elimTE_eq_conjTranspose] using
    (PosDef.fromBlocks₁₁ (elimET s t ρ x) (elimTT s t ρ x) hE).1 hPSD

/-! ### Residual columns after ordered `z`-elimination -/

lemma isUnit_det_of_isUnit {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (h : IsUnit A) : IsUnit A.det :=
  (isUnit_iff_isUnit_det A).mp h

lemma mul_inv_of_isUnit_real {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (h : IsUnit A) : A * A⁻¹ = 1 :=
  mul_nonsing_inv A (isUnit_det_of_isUnit h)

lemma inv_mul_of_isUnit_real {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (h : IsUnit A) : A⁻¹ * A = 1 :=
  nonsing_inv_mul A (isUnit_det_of_isUnit h)

lemma schurComplementEntry_submatrix {n : Type*}
    (A : Matrix ι ι ℝ) (f : n → ι) (e : Fin r → n) (a b : n) :
    schurComplementEntry (A.submatrix f f) e a b =
      schurComplementEntry A (f ∘ e) (f a) (f b) := by
  have h : (A.submatrix f f).submatrix e e = A.submatrix (f ∘ e) (f ∘ e) := by
    ext i j
    simp
  simp only [schurComplementEntry, submatrix_apply]
  rw [h]
  rfl

lemma schurComplementEntry_eq_zero_of_mem {n : Type*}
    (A : Matrix n n ℝ) (e : Fin r → n) (hU : IsUnit (A.submatrix e e))
    (i : Fin r) (j : n) :
    schurComplementEntry A e (e i) j = 0 := by
  have hmul := mul_inv_of_isUnit_real hU
  unfold schurComplementEntry
  have hdot :
      (fun k => A (e i) (e k)) ⬝ᵥ ((A.submatrix e e)⁻¹ *ᵥ fun k => A (e k) j) =
        ((A.submatrix e e) *ᵥ ((A.submatrix e e)⁻¹ *ᵥ fun k => A (e k) j)) i := by
    simp [mulVec, dotProduct, submatrix_apply]
  rw [hdot, mulVec_mulVec, hmul, one_mulVec]
  simp

lemma castLE_proof_irrel {n : ℕ} (h1 h2 : n ≤ k) :
    Fin.castLE h1 = Fin.castLE h2 :=
  funext fun _ => Fin.ext rfl

/-- Residual of column `idxZ j` after eliminating earlier `z`-indices. -/
def elimRes (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (j : Fin k)
    (α : ConfigIdx k p) : ℝ :=
  schurComplementEntry (M (Xconfig s t ρ x))
    (idxZ (p := p) ∘ Fin.castLE (Nat.le_of_lt j.isLt)) α (idxZ j)

/-- Pivot at `z`-index `j` after eliminating earlier `z`-indices. -/
def elimPivot (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (j : Fin k) : ℝ :=
  schurComplementEntry
    ((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p)))
    (Fin.castLE (Nat.le_of_lt j.isLt)) j j

lemma elimPivot_pos (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j) (j : Fin k) :
    0 < elimPivot s t ρ x j :=
  MX_zBlock_schur_pivot_pos s t ρ x hs ht hρ
    (Fin.castLE (Nat.le_of_lt j.isLt)) (Fin.castLE_injective _)
    (by
      rintro ⟨i, hi⟩
      exact i.isLt.ne (by simpa [Fin.ext_iff] using hi))

lemma elimRes_idxZ (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (j β : Fin k) :
    elimRes s t ρ x j (idxZ β) =
      schurComplementEntry
        ((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p)))
        (Fin.castLE (Nat.le_of_lt j.isLt)) β j :=
  (schurComplementEntry_submatrix (M (Xconfig s t ρ x)) (idxZ (p := p))
    (Fin.castLE (Nat.le_of_lt j.isLt)) β j).symm

lemma elimRes_eq_pivot (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (j : Fin k) :
    elimRes s t ρ x j (idxZ j) = elimPivot s t ρ x j :=
  elimRes_idxZ s t ρ x j j

/-- EL11: every residual column on `ConfigIdx` is nonnegative. -/
lemma elimRes_nonneg (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hmono : Monotone t)
    (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j) (j : Fin k)
    (α : ConfigIdx k p) :
    0 ≤ elimRes s t ρ x j α := by
  refine elim_configIdx_cases (P := fun α => 0 ≤ elimRes s t ρ x j α) α ?_ ?_ ?_
  · simp [elimRes, schurComplementEntry, MX_z0_z]
  · intro β
    have hm : (j : ℕ) ≤ k := Nat.le_of_lt j.isLt
    rcases lt_trichotomy β.val j.val with hlt | heq | hgt
    · have hi : idxZ (p := p) β =
          (idxZ (p := p) ∘ Fin.castLE (Nat.le_of_lt j.isLt)) ⟨β.val, hlt⟩ := by
        simp
      rw [elimRes, hi]
      have hU : IsUnit
          ((M (Xconfig s t ρ x)).submatrix
            (idxZ (p := p) ∘ Fin.castLE (Nat.le_of_lt j.isLt))
            (idxZ (p := p) ∘ Fin.castLE (Nat.le_of_lt j.isLt))) := by
        simpa [submatrix_submatrix] using
          (MX_zBlock_leading_posDef s t ρ x hs ht hρ hm).isUnit
      exact ge_of_eq (schurComplementEntry_eq_zero_of_mem (M (Xconfig s t ρ x))
        (idxZ (p := p) ∘ Fin.castLE (Nat.le_of_lt j.isLt)) hU ⟨β.val, hlt⟩
        (idxZ j))
    · have hβ : β = j := Fin.ext heq
      rw [hβ, elimRes_eq_pivot]
      exact (elimPivot_pos s t ρ x hs ht hρ j).le
    · rw [elimRes_idxZ]
      exact schurComplementEntry_z_later_nonneg s t ρ x hs ht hmono hρ hm
        (j := j) (α := β) le_rfl hgt.le fun h => hgt.ne' (congrArg Fin.val h)
  · intro ℓ
    exact schurComplementEntry_y_later_nonneg s t ρ x hs ht hmono hρ hx
      (Nat.le_of_lt j.isLt) le_rfl ℓ

/-! ### EL12 — `C₀` is completely positive -/

/-- The `idxZ0` column of `M (Xconfig s t ρ x)` divided by the square root of its diagonal entry:
the first factor of `C₀`. -/
def elimVec0 (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) : ConfigIdx k p → ℝ :=
  fun α =>
    M (Xconfig s t ρ x) α idxZ0 /
      Real.sqrt (M (Xconfig s t ρ x) idxZ0 idxZ0)

/-- The `j`-th elimination residual `elimRes` divided by the square root of its pivot `elimPivot`:
the `j.succ`-th factor of `C₀`. -/
def elimVec (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (j : Fin k) :
    ConfigIdx k p → ℝ :=
  fun α => elimRes s t ρ x j α / Real.sqrt (elimPivot s t ρ x j)

/-- The `k + 1` factors of `C₀`: `elimVec0` followed by the vectors `elimVec s t ρ x j`. -/
def elimC0Factor (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Fin (k + 1) → ConfigIdx k p → ℝ :=
  Fin.cons (elimVec0 s t ρ x) (elimVec s t ρ x)

/-- Sum of scaled residual outer products. -/
def elimC0 (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Matrix (ConfigIdx k p) (ConfigIdx k p) ℝ :=
  ∑ a : Fin (k + 1), vecMulVec (elimC0Factor s t ρ x a) (elimC0Factor s t ρ x a)

lemma elimVec0_nonneg (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j)
    (α : ConfigIdx k p) :
    0 ≤ elimVec0 s t ρ x α :=
  div_nonneg
    (by
      rw [(MX_isSymm s t ρ x).apply]
      exact MX_z0_nonneg s t ρ x hs hρ hx α)
    (Real.sqrt_nonneg _)

lemma elimVec_nonneg (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hmono : Monotone t)
    (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j) (j : Fin k)
    (α : ConfigIdx k p) :
    0 ≤ elimVec s t ρ x j α :=
  div_nonneg (elimRes_nonneg s t ρ x hs ht hmono hρ hx j α) (Real.sqrt_nonneg _)

lemma elimC0Factor_nonneg (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hmono : Monotone t)
    (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j) (a : Fin (k + 1))
    (α : ConfigIdx k p) :
    0 ≤ elimC0Factor s t ρ x a α := by
  induction a using Fin.cases with
  | zero =>
    simpa [elimC0Factor] using elimVec0_nonneg s t ρ x hs hρ hx α
  | succ j =>
    simpa [elimC0Factor] using elimVec_nonneg s t ρ x hs ht hmono hρ hx j α

/-- EL12: `C₀` is completely positive. -/
lemma isCompletelyPositive_elimC0 (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hmono : Monotone t)
    (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j) :
    IsCompletelyPositive (elimC0 s t ρ x) :=
  ⟨k + 1, elimC0Factor s t ρ x,
    elimC0Factor_nonneg s t ρ x hs ht hmono hρ hx, rfl⟩

/-! ### Gram of the `E`-columns and the identity `M = C₀ + pad R` -/

/-- Row `α` of `M (Xconfig s t ρ x)` restricted to the `E`-columns. -/
def elimColE (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (α : ConfigIdx k p) :
    Option (Fin k) → ℝ :=
  fun a => M (Xconfig s t ρ x) α (elimEEmbed a)

/-- `P EE⁻¹ Pᵀ` on configuration indices. -/
def elimGramE (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Matrix (ConfigIdx k p) (ConfigIdx k p) ℝ :=
  fun α β =>
    elimColE s t ρ x α ⬝ᵥ (elimEE s t ρ x)⁻¹ *ᵥ elimColE s t ρ x β

/-- The leading `m × m` principal block of `M (Xconfig s t ρ x)` on the left-vector indices `idxZ
(Fin.castLE hm i)`. -/
def elimZLead (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) {m : ℕ} (hm : m ≤ k) :
    Matrix (Fin m) (Fin m) ℝ :=
  ((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p))).submatrix
    (Fin.castLE hm) (Fin.castLE hm)

/-- Row `α` of `M (Xconfig s t ρ x)` restricted to the first `m` left-vector columns. -/
def elimColZLead (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) {m : ℕ} (hm : m ≤ k)
    (α : ConfigIdx k p) : Fin m → ℝ :=
  fun i => M (Xconfig s t ρ x) α (idxZ (Fin.castLE hm i))

/-- The matrix `c_α ⬝ᵥ (elimZLead)⁻¹ *ᵥ c_β` built from the columns `elimColZLead`: the part of `M`
explained by the first `m` left vectors. -/
def elimGramZLead (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) {m : ℕ} (hm : m ≤ k) :
    Matrix (ConfigIdx k p) (ConfigIdx k p) ℝ :=
  fun α β =>
    elimColZLead s t ρ x hm α ⬝ᵥ
      (elimZLead s t ρ x hm)⁻¹ *ᵥ elimColZLead s t ρ x hm β

/-- The block-diagonal matrix on `Option (Fin k)` with `(M idxZ0 idxZ0)⁻¹` in the `none` corner and
the inverse of the left-vector block of `M (Xconfig s t ρ x)` on the `some` indices. -/
def elimEEInv (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Matrix (Option (Fin k)) (Option (Fin k)) ℝ :=
  fun a b =>
    match a, b with
    | none, none => (M (Xconfig s t ρ x) idxZ0 idxZ0)⁻¹
    | none, some _ => 0
    | some _, none => 0
    | some i, some h =>
        ((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p)))⁻¹ i h

lemma elimEE_mul_inv (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) :
    elimEE s t ρ x * elimEEInv s t ρ x = 1 := by
  have h00 := (MX_z0_z0_pos s t ρ x hs hx).ne'
  have hZ := (MX_zBlock_posDef s t ρ x hs ht hρ).isUnit
  have hZmul :=
    mul_inv_of_isUnit_real hZ
  ext a b
  cases a with
  | none =>
    cases b with
    | none =>
      simp only [Matrix.mul_apply, elimEEInv, Fintype.sum_option, elimEE_none_none,
        elimEE_none_some, mul_zero, sum_const_zero, add_zero, one_apply_eq]
      exact mul_inv_cancel₀ h00
    | some h =>
      simp [Matrix.mul_apply, Fintype.sum_option, elimEE_none_none, elimEE_none_some,
        elimEEInv]
  | some i =>
    cases b with
    | none =>
      simp [Matrix.mul_apply, Fintype.sum_option, elimEE_some_none, elimEE_some_some,
        elimEEInv]
    | some h =>
      have h1 :
          ∑ i' : Fin k,
              elimEE s t ρ x (some i) (some i') *
                elimEEInv s t ρ x (some i') (some h) =
            (1 : Matrix (Fin k) (Fin k) ℝ) i h := by
        simpa [elimEE_some_some, elimEEInv, Matrix.mul_apply] using
          congrFun (congrFun hZmul i) h
      simpa [Matrix.mul_apply, Fintype.sum_option, elimEE_some_none, elimEEInv,
        Matrix.one_apply] using h1

lemma elimEE_inv_eq (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) :
    (elimEE s t ρ x)⁻¹ = elimEEInv s t ρ x :=
  inv_eq_right_inv (elimEE_mul_inv s t ρ x hs ht hρ hx)

lemma elimEEInv_mulVec (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (v : Option (Fin k) → ℝ) :
    elimEEInv s t ρ x *ᵥ v =
      fun a =>
        match a with
        | none => (M (Xconfig s t ρ x) idxZ0 idxZ0)⁻¹ * v none
        | some i =>
            (((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p)))⁻¹ *ᵥ
              fun h => v (some h)) i := by
  funext a
  cases a with
  | none =>
    simp [mulVec, dotProduct, Fintype.sum_option, elimEEInv]
  | some i =>
    simp [mulVec, dotProduct, Fintype.sum_option, elimEEInv]

lemma elimGramE_eq_z0_add_Z (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) (α β : ConfigIdx k p) :
    elimGramE s t ρ x α β =
      (M (Xconfig s t ρ x) α idxZ0) *
          ((M (Xconfig s t ρ x) idxZ0 idxZ0)⁻¹ *
            M (Xconfig s t ρ x) β idxZ0) +
        elimGramZLead s t ρ x le_rfl α β := by
  have hinv := elimEE_inv_eq s t ρ x hs ht hρ hx
  simp only [elimGramE, elimGramZLead, elimZLead]
  rw [hinv, elimEEInv_mulVec]
  simp [dotProduct, Fintype.sum_option]
  rfl

lemma IsHermitian.nonsing_inv_real {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (_hU : IsUnit A) :
    A⁻¹.IsHermitian := by
  rw [isHermitian_iff_isSymm] at hA ⊢
  change (A⁻¹)ᵀ = A⁻¹
  rw [transpose_nonsing_inv, hA]

lemma dotProduct_nonsing_inv_comm {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (hU : IsUnit A) (x y : n → ℝ) :
    x ⬝ᵥ (A⁻¹ *ᵥ y) = y ⬝ᵥ (A⁻¹ *ᵥ x) := by
  have hS : (A⁻¹)ᵀ = A⁻¹ :=
    isHermitian_iff_isSymm.mp (IsHermitian.nonsing_inv_real hA hU)
  simpa [hS] using (dotProduct_transpose_mulVec (A := A⁻¹) x y)

lemma mulVec_sum_castSucc {m : ℕ} (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (x : Fin (m + 1) → ℝ) (i : Fin m) :
    (Z *ᵥ x) i.castSucc =
      ((Z.submatrix Fin.castSucc Fin.castSucc) *ᵥ fun j => x j.castSucc) i +
        Z i.castSucc (Fin.last m) * x (Fin.last m) := by
  simp [mulVec, dotProduct, Fin.sum_univ_castSucc, submatrix_apply]

lemma mulVec_sum_last {m : ℕ} (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (x : Fin (m + 1) → ℝ) :
    (Z *ᵥ x) (Fin.last m) =
      (fun i : Fin m => Z (Fin.last m) i.castSucc) ⬝ᵥ (fun j => x j.castSucc) +
        Z (Fin.last m) (Fin.last m) * x (Fin.last m) := by
  simp [mulVec, dotProduct, Fin.sum_univ_castSucc]

lemma dotProduct_sum_castSucc {m : ℕ} (P x : Fin (m + 1) → ℝ) :
    P ⬝ᵥ x =
      (fun i : Fin m => P i.castSucc) ⬝ᵥ (fun j => x j.castSucc) +
        P (Fin.last m) * x (Fin.last m) := by
  simp [dotProduct, Fin.sum_univ_castSucc]

lemma gram_inv_castSucc_step {m : ℕ}
    (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (hZ : Z.PosDef)
    (Pα Pβ : Fin (m + 1) → ℝ) :
    Pα ⬝ᵥ (Z⁻¹ *ᵥ Pβ) =
      (fun i : Fin m => Pα i.castSucc) ⬝ᵥ
          ((Z.submatrix Fin.castSucc Fin.castSucc)⁻¹ *ᵥ
            fun i : Fin m => Pβ i.castSucc) +
        (1 / schurComplementEntry Z Fin.castSucc (Fin.last m) (Fin.last m)) *
          (Pα (Fin.last m) -
            (fun i : Fin m => Pα i.castSucc) ⬝ᵥ
              ((Z.submatrix Fin.castSucc Fin.castSucc)⁻¹ *ᵥ
                fun i : Fin m => Z i.castSucc (Fin.last m))) *
          (Pβ (Fin.last m) -
            (fun i : Fin m => Pβ i.castSucc) ⬝ᵥ
              ((Z.submatrix Fin.castSucc Fin.castSucc)⁻¹ *ᵥ
                fun i : Fin m => Z i.castSucc (Fin.last m))) := by
  set A := Z.submatrix Fin.castSucc Fin.castSucc
  set b : Fin m → ℝ := fun i => Z i.castSucc (Fin.last m)
  set d := schurComplementEntry Z Fin.castSucc (Fin.last m) (Fin.last m)
  set resP := fun P : Fin (m + 1) → ℝ =>
    P (Fin.last m) - (fun i : Fin m => P i.castSucc) ⬝ᵥ (A⁻¹ *ᵥ b)
  have hA : A.PosDef := hZ.submatrix (Fin.castSucc_injective (n := m))
  have hlast : Fin.last m ∉ Set.range Fin.castSucc := by
    rintro ⟨i, hi⟩
    exact (Fin.castSucc_lt_last i).ne hi
  have hdpos :=
    schurComplementEntry_diag_pos_of_posDef hZ Fin.castSucc
      (Fin.castSucc_injective (n := m)) hlast
  have hd0 : d ≠ 0 := hdpos.ne'
  have hZsym : Z.IsSymm := isHermitian_iff_isSymm.mp hZ.1
  have hrow : (fun i : Fin m => Z (Fin.last m) i.castSucc) = b :=
    funext fun i => (hZsym.apply _ _)
  have hdetZ : IsUnit Z.det := isUnit_det_of_isUnit hZ.isUnit
  have hdetA : IsUnit A.det := isUnit_det_of_isUnit hA.isUnit
  have hZx : Z *ᵥ (Z⁻¹ *ᵥ Pβ) = Pβ := by
    rw [mulVec_mulVec, mul_nonsing_inv Z hdetZ, one_mulVec]
  set x := Z⁻¹ *ᵥ Pβ
  have hxcast : A *ᵥ (fun j => x j.castSucc) =
      fun i => Pβ i.castSucc - x (Fin.last m) * b i := by
    ext i
    have := congrArg (fun v => v i.castSucc) hZx
    have hx := mulVec_sum_castSucc Z x i
    simp only [x] at hx this
    linarith
  have hxlead : (fun j => x j.castSucc) =
      A⁻¹ *ᵥ fun i => Pβ i.castSucc - x (Fin.last m) * b i := by
    have := congrArg (fun w => A⁻¹ *ᵥ w) hxcast
    rw [mulVec_mulVec, nonsing_inv_mul A hdetA, one_mulVec] at this
    exact this
  have hxlast_eq :
      b ⬝ᵥ (fun j => x j.castSucc) + Z (Fin.last m) (Fin.last m) * x (Fin.last m) =
        Pβ (Fin.last m) := by
    have := congrArg (fun v => v (Fin.last m)) hZx
    rw [mulVec_sum_last, hrow] at this
    exact this
  have hbAu :
      b ⬝ᵥ (A⁻¹ *ᵥ fun i => Pβ i.castSucc) =
        (fun i : Fin m => Pβ i.castSucc) ⬝ᵥ (A⁻¹ *ᵥ b) :=
    dotProduct_nonsing_inv_comm hA.1 hA.isUnit _ _
  have hxlast : x (Fin.last m) = resP Pβ / d := by
    have hlast' := hxlast_eq
    rw [hxlead] at hlast'
    have hlin :
        b ⬝ᵥ (A⁻¹ *ᵥ fun i => Pβ i.castSucc - x (Fin.last m) * b i) =
          b ⬝ᵥ (A⁻¹ *ᵥ fun i => Pβ i.castSucc) -
            x (Fin.last m) * (b ⬝ᵥ (A⁻¹ *ᵥ b)) := by
      have hfun :
          (fun i => Pβ i.castSucc - x (Fin.last m) * b i) =
            (fun i => Pβ i.castSucc) - x (Fin.last m) • b := by
        funext i
        simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hfun, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rw [hlin, hbAu] at hlast'
    have hddef : d =
        Z (Fin.last m) (Fin.last m) - b ⬝ᵥ (A⁻¹ *ᵥ b) := by
      simp [d, schurComplementEntry, A, b, hrow]
    have hmuld : x (Fin.last m) * d = resP Pβ := by
      simp only [resP]
      linear_combination hlast' + x (Fin.last m) * hddef
    exact (eq_div_iff hd0).2 hmuld
  have hLHS : Pα ⬝ᵥ x =
      (fun i : Fin m => Pα i.castSucc) ⬝ᵥ (fun j => x j.castSucc) +
        Pα (Fin.last m) * x (Fin.last m) :=
    dotProduct_sum_castSucc Pα x
  rw [hLHS, hxlead]
  have hlinα :
      (fun i : Fin m => Pα i.castSucc) ⬝ᵥ
          (A⁻¹ *ᵥ fun i => Pβ i.castSucc - x (Fin.last m) * b i) =
        (fun i : Fin m => Pα i.castSucc) ⬝ᵥ (A⁻¹ *ᵥ fun i => Pβ i.castSucc) -
          x (Fin.last m) *
            ((fun i : Fin m => Pα i.castSucc) ⬝ᵥ (A⁻¹ *ᵥ b)) := by
    have hfun :
        (fun i => Pβ i.castSucc - x (Fin.last m) * b i) =
          (fun i => Pβ i.castSucc) - x (Fin.last m) • b := by
      funext i
      simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hfun, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [hlinα, hxlast]
  unfold resP
  field_simp [hd0]
  ring

lemma elimZLead_posDef (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    {m : ℕ} (hm : m ≤ k) :
    (elimZLead s t ρ x hm).PosDef :=
  MX_zBlock_leading_posDef s t ρ x hs ht hρ hm

lemma elimZLead_castSucc (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    {m : ℕ} (hm : m + 1 ≤ k) :
    (elimZLead s t ρ x hm).submatrix Fin.castSucc Fin.castSucc =
      elimZLead s t ρ x (Nat.le_of_succ_le hm) := by
  ext i j
  simp [elimZLead, submatrix_apply]

lemma elimColZLead_castSucc (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    {m : ℕ} (hm : m + 1 ≤ k) (α : ConfigIdx k p) :
    (fun i : Fin m => elimColZLead s t ρ x hm α i.castSucc) =
      elimColZLead s t ρ x (Nat.le_of_succ_le hm) α := by
  funext i
  simp [elimColZLead]

lemma elimColZLead_last (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    {m : ℕ} (hm : m + 1 ≤ k) (α : ConfigIdx k p) :
    elimColZLead s t ρ x hm α (Fin.last m) =
      M (Xconfig s t ρ x) α (idxZ ⟨m, Nat.lt_of_succ_le hm⟩) := by
  simp only [elimColZLead]
  exact congrArg (fun z : Fin k => M (Xconfig s t ρ x) α (idxZ z))
    (Fin.ext (by simp))

lemma elimZLead_last_col (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    {m : ℕ} (hm : m + 1 ≤ k) (i : Fin m) :
    elimZLead s t ρ x hm i.castSucc (Fin.last m) =
      M (Xconfig s t ρ x)
        (idxZ (Fin.castLE (Nat.le_of_succ_le hm) i))
        (idxZ ⟨m, Nat.lt_of_succ_le hm⟩) := by
  simp only [elimZLead, submatrix_apply, Fin.castLE_castSucc]
  apply congrArg₂ (M (Xconfig s t ρ x))
  · exact congrArg idxZ (Fin.ext (by simp))
  · exact congrArg idxZ (Fin.ext (by simp))

lemma elimRes_succ (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    {m : ℕ} (hm : m + 1 ≤ k) (α : ConfigIdx k p) :
    elimRes s t ρ x ⟨m, Nat.lt_of_succ_le hm⟩ α =
      elimColZLead s t ρ x hm α (Fin.last m) -
        elimColZLead s t ρ x (Nat.le_of_succ_le hm) α ⬝ᵥ
          (elimZLead s t ρ x (Nat.le_of_succ_le hm))⁻¹ *ᵥ
            fun i => elimZLead s t ρ x hm i.castSucc (Fin.last m) := by
  have hcast : Fin.castLE (Nat.le_of_lt (⟨m, Nat.lt_of_succ_le hm⟩ : Fin k).isLt) =
      Fin.castLE (Nat.le_of_succ_le hm) :=
    castLE_proof_irrel _ _
  have hcomp : Fin.castLE (Nat.le_of_succ_le hm) =
      Fin.castLE hm ∘ Fin.castSucc :=
    funext fun _ => Fin.ext rfl
  have he :
      idxZ (p := p) ∘ Fin.castLE (Nat.le_of_lt (⟨m, Nat.lt_of_succ_le hm⟩ : Fin k).isLt) =
        idxZ (p := p) ∘ Fin.castLE hm ∘ Fin.castSucc := by
    rw [hcast, hcomp]
  have hlast : Fin.castLE hm (Fin.last m) = ⟨m, Nat.lt_of_succ_le hm⟩ :=
    Fin.ext (by simp)
  have h1 : M (Xconfig s t ρ x) α (idxZ ⟨m, Nat.lt_of_succ_le hm⟩) =
      elimColZLead s t ρ x hm α (Fin.last m) := by
    simp [elimColZLead, hlast]
  have h2 :
      (fun i => M (Xconfig s t ρ x) α
        ((idxZ (p := p) ∘ Fin.castLE hm ∘ Fin.castSucc) i)) =
        elimColZLead s t ρ x (Nat.le_of_succ_le hm) α := by
    funext i
    simp [elimColZLead]
  have h3 :
      (M (Xconfig s t ρ x)).submatrix
          (idxZ (p := p) ∘ Fin.castLE hm ∘ Fin.castSucc)
          (idxZ (p := p) ∘ Fin.castLE hm ∘ Fin.castSucc) =
        elimZLead s t ρ x (Nat.le_of_succ_le hm) := by
    ext i j
    simp [elimZLead, submatrix_apply]
  have h4 :
      (fun i =>
        M (Xconfig s t ρ x)
          ((idxZ (p := p) ∘ Fin.castLE hm ∘ Fin.castSucc) i)
          (idxZ ⟨m, Nat.lt_of_succ_le hm⟩)) =
        fun i => elimZLead s t ρ x hm i.castSucc (Fin.last m) := by
    funext i
    simp [elimZLead, submatrix_apply, hlast]
  simp only [elimRes, schurComplementEntry]
  rw [he, h1, h2, h3, h4]

lemma elimPivot_succ (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    {m : ℕ} (hm : m + 1 ≤ k) :
    elimPivot s t ρ x ⟨m, Nat.lt_of_succ_le hm⟩ =
      schurComplementEntry (elimZLead s t ρ x hm) Fin.castSucc
        (Fin.last m) (Fin.last m) := by
  have hcast : Fin.castLE (Nat.le_of_lt (⟨m, Nat.lt_of_succ_le hm⟩ : Fin k).isLt) =
      Fin.castLE (Nat.le_of_succ_le hm) :=
    castLE_proof_irrel _ _
  have hcomp : Fin.castLE (Nat.le_of_succ_le hm) =
      Fin.castLE hm ∘ Fin.castSucc :=
    funext fun _ => Fin.ext rfl
  have hlast : Fin.castLE hm (Fin.last m) = ⟨m, Nat.lt_of_succ_le hm⟩ :=
    Fin.ext (by simp)
  have hR :
      schurComplementEntry (elimZLead s t ρ x hm) Fin.castSucc
        (Fin.last m) (Fin.last m) =
        schurComplementEntry
          ((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p)))
          (Fin.castLE hm ∘ Fin.castSucc)
          (Fin.castLE hm (Fin.last m)) (Fin.castLE hm (Fin.last m)) := by
    simpa [elimZLead] using
      schurComplementEntry_submatrix
        ((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p)))
        (Fin.castLE hm) Fin.castSucc (Fin.last m) (Fin.last m)
  rw [elimPivot, hR, hcast, hcomp, hlast]

lemma elimGramZLead_succ (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    {m : ℕ} (hm : m + 1 ≤ k) :
    elimGramZLead s t ρ x hm =
      elimGramZLead s t ρ x (Nat.le_of_succ_le hm) +
        (1 / elimPivot s t ρ x ⟨m, Nat.lt_of_succ_le hm⟩) •
          vecMulVec (elimRes s t ρ x ⟨m, Nat.lt_of_succ_le hm⟩)
            (elimRes s t ρ x ⟨m, Nat.lt_of_succ_le hm⟩) := by
  ext α β
  have hZ := elimZLead_posDef s t ρ x hs ht hρ hm
  have hstep :=
    gram_inv_castSucc_step (elimZLead s t ρ x hm) hZ
      (elimColZLead s t ρ x hm α) (elimColZLead s t ρ x hm β)
  have hA := elimZLead_castSucc s t ρ x hm
  have hPα := elimColZLead_castSucc s t ρ x hm α
  have hPβ := elimColZLead_castSucc s t ρ x hm β
  have hresα := elimRes_succ s t ρ x hm α
  have hresβ := elimRes_succ s t ρ x hm β
  have hpiv := elimPivot_succ s t ρ x hm
  simp only [elimGramZLead, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply]
  rw [hstep, hA, hPα, hPβ, hpiv, hresα, hresβ]
  ring

lemma elimGramZLead_eq_sum (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j) :
    ∀ (m : ℕ) (hm : m ≤ k),
      elimGramZLead s t ρ x hm =
        ∑ j : Fin m,
          (1 / elimPivot s t ρ x (Fin.castLE hm j)) •
            vecMulVec (elimRes s t ρ x (Fin.castLE hm j))
              (elimRes s t ρ x (Fin.castLE hm j)) := by
  intro m
  induction m with
  | zero =>
    intro hm
    ext α β
    simp [elimGramZLead, elimColZLead, dotProduct, mulVec]
  | succ m ih =>
    intro hm
    have hm' : m ≤ k := Nat.le_of_succ_le hm
    have hcastj : ∀ j : Fin m, Fin.castLE hm j.castSucc = Fin.castLE hm' j :=
      fun j => Fin.ext (by simp)
    have hlast : Fin.castLE hm (Fin.last m) = ⟨m, Nat.lt_of_succ_le hm⟩ :=
      Fin.ext (by simp)
    simp [elimGramZLead_succ s t ρ x hs ht hρ hm, ih hm', Fin.sum_univ_castSucc,
      hcastj, hlast]

lemma vecMulVec_div_sqrt {n : Type*} (v : n → ℝ) {d : ℝ} (hd : 0 < d) :
    vecMulVec (fun i => v i / Real.sqrt d) (fun i => v i / Real.sqrt d) =
      d⁻¹ • vecMulVec v v := by
  ext i j
  simp [vecMulVec_apply, Matrix.smul_apply, div_mul_div_comm, Real.mul_self_sqrt hd.le]
  ring

lemma elimC0_eq_sum_scaled (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) :
    elimC0 s t ρ x =
      (M (Xconfig s t ρ x) idxZ0 idxZ0)⁻¹ •
          vecMulVec (fun α => M (Xconfig s t ρ x) α idxZ0)
            (fun α => M (Xconfig s t ρ x) α idxZ0) +
        ∑ j : Fin k,
          (elimPivot s t ρ x j)⁻¹ •
            vecMulVec (elimRes s t ρ x j) (elimRes s t ρ x j) := by
  have h00 := MX_z0_z0_pos s t ρ x hs hx
  unfold elimC0
  rw [Fin.sum_univ_succ]
  simp only [elimC0Factor, Fin.cons_zero, Fin.cons_succ]
  congr 1
  · exact vecMulVec_div_sqrt (fun α => M (Xconfig s t ρ x) α idxZ0) h00
  · refine Fintype.sum_congr _ _ fun j => ?_
    exact vecMulVec_div_sqrt (elimRes s t ρ x j)
      (elimPivot_pos s t ρ x hs ht hρ j)

lemma elimGramZLead_full (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j) :
    elimGramZLead s t ρ x le_rfl =
      ∑ j : Fin k,
        (elimPivot s t ρ x j)⁻¹ •
          vecMulVec (elimRes s t ρ x j) (elimRes s t ρ x j) := by
  simpa [one_div] using elimGramZLead_eq_sum s t ρ x hs ht hρ k le_rfl

lemma elimC0_eq_elimGramE (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) :
    elimC0 s t ρ x = elimGramE s t ρ x := by
  ext α β
  have h00 := (MX_z0_z0_pos s t ρ x hs hx).ne'
  rw [elimC0_eq_sum_scaled s t ρ x hs ht hρ hx,
    elimGramE_eq_z0_add_Z s t ρ x hs ht hρ hx, elimGramZLead_full s t ρ x hs ht hρ]
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply,
    mul_left_comm]

lemma elimColE_embed (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (a : Option (Fin k)) :
    elimColE s t ρ x (elimEEmbed a) = fun b => elimEE s t ρ x a b := by
  funext b
  rfl

lemma elimGramE_embed (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) (a b : Option (Fin k)) :
    elimGramE s t ρ x (elimEEmbed a) (elimEEmbed b) = elimEE s t ρ x a b := by
  have hU : IsUnit (elimEE s t ρ x) := (elimEE_posDef s t ρ x hs ht hρ hx).isUnit
  have hmul := mul_inv_of_isUnit_real hU
  have hsym := elimEE_isSymm s t ρ x
  simp only [elimGramE, elimColE_embed]
  have hcol : (fun i => elimEE s t ρ x b i) = fun i => elimEE s t ρ x i b :=
    funext fun i => hsym.apply i b
  rw [hcol]
  have hdot :
      (fun i => elimEE s t ρ x a i) ⬝ᵥ
          ((elimEE s t ρ x)⁻¹ *ᵥ fun i => elimEE s t ρ x i b) =
        (elimEE s t ρ x *ᵥ
          ((elimEE s t ρ x)⁻¹ *ᵥ fun i => elimEE s t ρ x i b)) a := by
    simp [mulVec, dotProduct]
  rw [hdot, mulVec_mulVec, hmul, one_mulVec]

lemma elimGramE_embed_y (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) (a : Option (Fin k)) (ℓ : Fin p) :
    elimGramE s t ρ x (elimEEmbed a) (idxY ℓ) = elimET s t ρ x a ℓ := by
  have hU : IsUnit (elimEE s t ρ x) := (elimEE_posDef s t ρ x hs ht hρ hx).isUnit
  have hmul := mul_inv_of_isUnit_real hU
  simp only [elimGramE]
  rw [elimColE_embed]
  have hcol : elimColE s t ρ x (idxY ℓ) =
      fun i => M (Xconfig s t ρ x) (idxY ℓ) (elimEEmbed i) := rfl
  rw [hcol]
  have hdot :
      (fun i => elimEE s t ρ x a i) ⬝ᵥ
          Matrix.mulVec (elimEE s t ρ x)⁻¹
            (fun i => M (Xconfig s t ρ x) (idxY ℓ) (elimEEmbed i)) =
        Matrix.mulVec (elimEE s t ρ x)
          (Matrix.mulVec (elimEE s t ρ x)⁻¹
            (fun i => M (Xconfig s t ρ x) (idxY ℓ) (elimEEmbed i))) a := by
    simp [mulVec, dotProduct]
  rw [hdot, mulVec_mulVec, hmul, one_mulVec]
  simp only [elimET, submatrix_apply]
  exact (MX_isSymm s t ρ x).apply _ _

lemma elimGramE_y_embed (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) (j : Fin p) (b : Option (Fin k)) :
    elimGramE s t ρ x (idxY j) (elimEEmbed b) = elimTE s t ρ x j b := by
  have hU : IsUnit (elimEE s t ρ x) := (elimEE_posDef s t ρ x hs ht hρ hx).isUnit
  simp only [elimGramE]
  have hrow : elimColE s t ρ x (idxY j) = fun i => elimTE s t ρ x j i := rfl
  have hcol : elimColE s t ρ x (elimEEmbed b) = fun i => elimEE s t ρ x i b := by
    funext i
    simp only [elimColE, elimEE, submatrix_apply]
    exact (MX_isSymm s t ρ x).apply _ _
  rw [hrow, hcol]
  have hcolb :
      Matrix.mulVec (elimEE s t ρ x)⁻¹ (fun i => elimEE s t ρ x i b) =
        (Pi.single b (1 : ℝ) : Option (Fin k) → ℝ) := by
    have : (fun i => elimEE s t ρ x i b) =
        Matrix.mulVec (elimEE s t ρ x) (Pi.single b (1 : ℝ)) := by
      ext i
      simp
    rw [this, mulVec_mulVec, inv_mul_of_isUnit_real hU, one_mulVec]
  rw [hcolb, dotProduct_single_one]

lemma mul_mul_col_apply {l m n o : Type*} [Fintype m] [Fintype n]
    (A : Matrix l m ℝ) (B : Matrix m n ℝ) (C : Matrix n o ℝ) (i : l) (j : o) :
    (A * B * C) i j = (fun a => A i a) ⬝ᵥ (B *ᵥ fun k => C k j) := by
  simp only [Matrix.mul_apply, sum_mul, mul_assoc, dotProduct, mulVec, mul_sum]
  exact Finset.sum_comm

lemma elimGramE_y_y (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (j ℓ : Fin p) :
    elimGramE s t ρ x (idxY j) (idxY ℓ) =
      (elimTE s t ρ x * (elimEE s t ρ x)⁻¹ * elimET s t ρ x) j ℓ := by
  have hL : elimColE s t ρ x (idxY j) = fun i => elimTE s t ρ x j i := rfl
  have hR : elimColE s t ρ x (idxY ℓ) = fun i => elimET s t ρ x i ℓ := by
    funext i
    exact (MX_isSymm s t ρ x).apply _ _
  simp only [elimGramE]
  rw [hL, hR]
  exact (mul_mul_col_apply (elimTE s t ρ x) (elimEE s t ρ x)⁻¹
    (elimET s t ρ x) j ℓ).symm

/-- EL13: `M = C₀ + extendByZero R` with `R` the `T`-Schur complement of `E`. -/
lemma M_eq_elimGramE_add_extend (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) :
    M (Xconfig s t ρ x) =
      elimGramE s t ρ x + extendByZeroT (k := k) (elimSchurR s t ρ x) := by
  ext α β
  refine elim_configIdx_cases
      (P := fun α =>
        M (Xconfig s t ρ x) α β =
          (elimGramE s t ρ x + extendByZeroT (k := k) (elimSchurR s t ρ x)) α β)
      α ?_ ?_ ?_
  · refine elim_configIdx_cases
        (P := fun β =>
          M (Xconfig s t ρ x) idxZ0 β =
            (elimGramE s t ρ x + extendByZeroT (k := k) (elimSchurR s t ρ x))
              idxZ0 β)
        β ?_ ?_ ?_
    · change M (Xconfig s t ρ x) idxZ0 idxZ0 =
          elimGramE s t ρ x idxZ0 idxZ0 +
            extendByZeroT (k := k) (elimSchurR s t ρ x) idxZ0 idxZ0
      rw [extendByZeroT_z0_left, add_zero]
      calc
        M (Xconfig s t ρ x) idxZ0 idxZ0
            = elimEE s t ρ x none none := (elimEE_none_none s t ρ x).symm
        _ = elimGramE s t ρ x (elimEEmbed none) (elimEEmbed none) :=
            (elimGramE_embed s t ρ x hs ht hρ hx none none).symm
        _ = elimGramE s t ρ x idxZ0 idxZ0 := by
            rw [elimEEmbed_none]
    · intro i
      change M (Xconfig s t ρ x) idxZ0 (idxZ i) =
          elimGramE s t ρ x idxZ0 (idxZ i) +
            extendByZeroT (k := k) (elimSchurR s t ρ x) idxZ0 (idxZ i)
      rw [extendByZeroT_z_right, add_zero]
      calc
        M (Xconfig s t ρ x) idxZ0 (idxZ i)
            = 0 := MX_z0_z s t ρ x i
        _ = elimEE s t ρ x none (some i) := (elimEE_none_some s t ρ x i).symm
        _ = elimGramE s t ρ x (elimEEmbed none) (elimEEmbed (some i)) :=
            (elimGramE_embed s t ρ x hs ht hρ hx none (some i)).symm
        _ = elimGramE s t ρ x idxZ0 (idxZ i) := by
            rw [elimEEmbed_none, elimEEmbed_some]
    · intro ℓ
      change M (Xconfig s t ρ x) idxZ0 (idxY ℓ) =
          elimGramE s t ρ x idxZ0 (idxY ℓ) +
            extendByZeroT (k := k) (elimSchurR s t ρ x) idxZ0 (idxY ℓ)
      rw [extendByZeroT_z0_left, add_zero]
      calc
        M (Xconfig s t ρ x) idxZ0 (idxY ℓ)
            = elimET s t ρ x none ℓ := rfl
        _ = elimGramE s t ρ x (elimEEmbed none) (idxY ℓ) :=
            (elimGramE_embed_y s t ρ x hs ht hρ hx none ℓ).symm
        _ = elimGramE s t ρ x idxZ0 (idxY ℓ) := by
            rw [elimEEmbed_none]
  · intro i
    refine elim_configIdx_cases
        (P := fun β =>
          M (Xconfig s t ρ x) (idxZ i) β =
            (elimGramE s t ρ x + extendByZeroT (k := k) (elimSchurR s t ρ x))
              (idxZ i) β)
        β ?_ ?_ ?_
    · change M (Xconfig s t ρ x) (idxZ i) idxZ0 =
          elimGramE s t ρ x (idxZ i) idxZ0 +
            extendByZeroT (k := k) (elimSchurR s t ρ x) (idxZ i) idxZ0
      rw [extendByZeroT_z0_right, add_zero]
      calc
        M (Xconfig s t ρ x) (idxZ i) idxZ0
            = 0 := MX_z_z0 s t ρ x i
        _ = elimEE s t ρ x (some i) none := (elimEE_some_none s t ρ x i).symm
        _ = elimGramE s t ρ x (elimEEmbed (some i)) (elimEEmbed none) :=
            (elimGramE_embed s t ρ x hs ht hρ hx (some i) none).symm
        _ = elimGramE s t ρ x (idxZ i) idxZ0 := by
            rw [elimEEmbed_some, elimEEmbed_none]
    · intro h
      change M (Xconfig s t ρ x) (idxZ i) (idxZ h) =
          elimGramE s t ρ x (idxZ i) (idxZ h) +
            extendByZeroT (k := k) (elimSchurR s t ρ x) (idxZ i) (idxZ h)
      rw [extendByZeroT_z_right, add_zero]
      calc
        M (Xconfig s t ρ x) (idxZ i) (idxZ h)
            = elimEE s t ρ x (some i) (some h) :=
              (elimEE_some_some s t ρ x i h).symm
        _ = elimGramE s t ρ x (elimEEmbed (some i)) (elimEEmbed (some h)) :=
            (elimGramE_embed s t ρ x hs ht hρ hx (some i) (some h)).symm
        _ = elimGramE s t ρ x (idxZ i) (idxZ h) := by
            rw [elimEEmbed_some, elimEEmbed_some]
    · intro ℓ
      change M (Xconfig s t ρ x) (idxZ i) (idxY ℓ) =
          elimGramE s t ρ x (idxZ i) (idxY ℓ) +
            extendByZeroT (k := k) (elimSchurR s t ρ x) (idxZ i) (idxY ℓ)
      rw [extendByZeroT_z_left, add_zero]
      calc
        M (Xconfig s t ρ x) (idxZ i) (idxY ℓ)
            = elimET s t ρ x (some i) ℓ := rfl
        _ = elimGramE s t ρ x (elimEEmbed (some i)) (idxY ℓ) :=
            (elimGramE_embed_y s t ρ x hs ht hρ hx (some i) ℓ).symm
        _ = elimGramE s t ρ x (idxZ i) (idxY ℓ) := by
            rw [elimEEmbed_some]
  · intro j
    refine elim_configIdx_cases
        (P := fun β =>
          M (Xconfig s t ρ x) (idxY j) β =
            (elimGramE s t ρ x + extendByZeroT (k := k) (elimSchurR s t ρ x))
              (idxY j) β)
        β ?_ ?_ ?_
    · change M (Xconfig s t ρ x) (idxY j) idxZ0 =
          elimGramE s t ρ x (idxY j) idxZ0 +
            extendByZeroT (k := k) (elimSchurR s t ρ x) (idxY j) idxZ0
      rw [extendByZeroT_z0_right, add_zero]
      calc
        M (Xconfig s t ρ x) (idxY j) idxZ0
            = elimTE s t ρ x j none := rfl
        _ = elimGramE s t ρ x (idxY j) (elimEEmbed none) :=
            (elimGramE_y_embed s t ρ x hs ht hρ hx j none).symm
        _ = elimGramE s t ρ x (idxY j) idxZ0 := by
            rw [elimEEmbed_none]
    · intro h
      change M (Xconfig s t ρ x) (idxY j) (idxZ h) =
          elimGramE s t ρ x (idxY j) (idxZ h) +
            extendByZeroT (k := k) (elimSchurR s t ρ x) (idxY j) (idxZ h)
      rw [extendByZeroT_z_right, add_zero]
      calc
        M (Xconfig s t ρ x) (idxY j) (idxZ h)
            = elimTE s t ρ x j (some h) := rfl
        _ = elimGramE s t ρ x (idxY j) (elimEEmbed (some h)) :=
            (elimGramE_y_embed s t ρ x hs ht hρ hx j (some h)).symm
        _ = elimGramE s t ρ x (idxY j) (idxZ h) := by
            rw [elimEEmbed_some]
    · intro ℓ
      change M (Xconfig s t ρ x) (idxY j) (idxY ℓ) =
          elimGramE s t ρ x (idxY j) (idxY ℓ) +
            extendByZeroT (k := k) (elimSchurR s t ρ x) (idxY j) (idxY ℓ)
      rw [extendByZeroT_y_y, elimGramE_y_y s t ρ x]
      simp [elimSchurR, elimTT, submatrix_apply, elimT, Matrix.sub_apply]

lemma M_eq_elimC0_add_extend (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) :
    M (Xconfig s t ρ x) =
      elimC0 s t ρ x + extendByZeroT (k := k) (elimSchurR s t ρ x) := by
  rw [elimC0_eq_elimGramE s t ρ x hs ht hρ hx,
    M_eq_elimGramE_add_extend s t ρ x hs ht hρ hx]

/-- EL14 — `lem:elimination`. -/
lemma lem_elimination (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hmono : Monotone t)
    (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j) :
    ∃ C₀ : Matrix (ConfigIdx k p) (ConfigIdx k p) ℝ,
      IsCompletelyPositive C₀ ∧
        M (Xconfig s t ρ x) =
            C₀ + extendByZeroT (k := k) (elimSchurR s t ρ x) ∧
          (elimSchurR s t ρ x).PosSemidef :=
  ⟨elimC0 s t ρ x,
    isCompletelyPositive_elimC0 s t ρ x hs ht hmono hρ hx,
    M_eq_elimC0_add_extend s t ρ x hs ht hρ hx,
    elimSchurR_posSemidef s t ρ x hs ht hρ hx⟩

end

end BollobasNikiforov

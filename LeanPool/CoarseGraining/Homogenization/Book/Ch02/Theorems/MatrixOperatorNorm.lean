/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.MultiscaleEllipticity
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Subadditivity
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Matrix Operator Norm -/

@[expose] public section

open scoped BigOperators Matrix.Norms.L2Operator

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-!
# Operator Norm API for Chapter 2 Matrices

This file gives the reusable Euclidean operator-norm API used by the public
Chapter 2 multiscale ellipticity definitions.  The explicitly named Frobenius
norm below is retained only as compatibility infrastructure for older
deterministic estimates.
-/

/-- Euclidean/L2 operator norm of a square real matrix, viewed as an operator
on finite-dimensional Euclidean space. -/
noncomputable def matrixOperatorNorm {d : ℕ} (A : Mat d) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A‖

/-- Legacy Frobenius squared norm, kept under an explicit compatibility name. -/
def matrixFrobeniusNormSq {d : ℕ} (A : Mat d) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

/-- Legacy Frobenius norm, kept under an explicit compatibility name. -/
noncomputable def matrixFrobeniusNorm {d : ℕ} (A : Mat d) : ℝ :=
  Real.sqrt (matrixFrobeniusNormSq A)

/-- Euclidean/L2 norm of a vector, compatible with the project's `vecNormSq`. -/
noncomputable def vecNorm {d : ℕ} (x : Vec d) : ℝ :=
  ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖

theorem matrixOperatorNorm_eq_l2_opNorm {d : ℕ} (A : Mat d) :
    matrixOperatorNorm A = ‖A‖ := by
  exact Matrix.l2_opNorm_toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A

theorem matrixOperatorNorm_nonneg {d : ℕ} (A : Mat d) :
    0 ≤ matrixOperatorNorm A := by
  exact norm_nonneg _

@[simp] theorem matrixOperatorNorm_zero {d : ℕ} :
    matrixOperatorNorm (0 : Mat d) = 0 := by
  simp [matrixOperatorNorm]

@[simp] theorem matrixOperatorNorm_one {d : ℕ} [NeZero d] :
    matrixOperatorNorm (1 : Mat d) = 1 := by
  simp [matrixOperatorNorm]

theorem matrixOperatorNorm_mul_le {d : ℕ} (A B : Mat d) :
    matrixOperatorNorm (A * B) ≤ matrixOperatorNorm A * matrixOperatorNorm B := by
  calc
    matrixOperatorNorm (A * B)
        = ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (A * B)‖ := rfl
    _ = ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A *
          Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) B‖ := by
        rw [map_mul]
    _ ≤ ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A‖ *
          ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) B‖ := norm_mul_le _ _
    _ = matrixOperatorNorm A * matrixOperatorNorm B := rfl

private theorem norm_toLp_comp_equiv {n : Type*} [Fintype n]
    (e : n ≃ n) (v : n → ℝ) :
    ‖(WithLp.toLp 2 (v ∘ e) : PiLp 2 (fun _ : n => ℝ))‖ =
      ‖(WithLp.toLp 2 v : PiLp 2 (fun _ : n => ℝ))‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  exact Fintype.sum_equiv e
    (fun i => ‖v (e i)‖ ^ 2) (fun i => ‖v i‖ ^ 2) (by intro i; rfl)

private theorem mulVec_reindex_self {n : Type*} [Fintype n] [DecidableEq n]
    (e : n ≃ n) (M : Matrix n n ℝ) (v : n → ℝ) :
    Matrix.mulVec (Matrix.reindex e e M) v =
      (Matrix.mulVec M (v ∘ e)) ∘ e.symm := by
  ext i
  change dotProduct (Matrix.reindex e e M i) v = dotProduct (M (e.symm i)) (v ∘ e)
  rw [dotProduct, dotProduct]
  simp [Matrix.reindex_apply]
  exact (Fintype.sum_equiv e
    (fun j => M (e.symm i) j * v (e j))
    (fun j => M (e.symm i) (e.symm j) * v j)
    (by intro j; simp)).symm

private theorem norm_toEuclideanCLM_reindex_self_le {n : Type*}
    [Fintype n] [DecidableEq n] (e : n ≃ n) (M : Matrix n n ℝ) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (Matrix.reindex e e M)‖ ≤
      ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) M‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
  intro x
  let v : n → ℝ := x.ofLp
  have hx : x = (WithLp.toLp 2 v : PiLp 2 (fun _ : n => ℝ)) := by
    simp [v]
  calc
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (Matrix.reindex e e M) x‖ =
        ‖(WithLp.toLp 2 (Matrix.mulVec (Matrix.reindex e e M) v) :
            PiLp 2 (fun _ : n => ℝ))‖ := by
          rw [hx]
          simp [Matrix.toEuclideanCLM_toLp]
    _ = ‖(WithLp.toLp 2 ((Matrix.mulVec M (v ∘ e)) ∘ e.symm) :
          PiLp 2 (fun _ : n => ℝ))‖ := by
          rw [mulVec_reindex_self e M v]
    _ = ‖(WithLp.toLp 2 (Matrix.mulVec M (v ∘ e)) :
          PiLp 2 (fun _ : n => ℝ))‖ :=
          norm_toLp_comp_equiv e.symm (Matrix.mulVec M (v ∘ e))
    _ = ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) M
          (WithLp.toLp 2 (v ∘ e) : PiLp 2 (fun _ : n => ℝ))‖ := by
          simp [Matrix.toEuclideanCLM_toLp]
    _ ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) M‖ *
        ‖(WithLp.toLp 2 (v ∘ e) : PiLp 2 (fun _ : n => ℝ))‖ :=
          (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) M).le_opNorm _
    _ = ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) M‖ * ‖x‖ := by
          rw [norm_toLp_comp_equiv e v]

/-- Reindexing both coordinates by the same equivalence preserves the
Euclidean operator norm. -/
theorem norm_toEuclideanCLM_reindex_self {n : Type*} [Fintype n] [DecidableEq n]
    (e : n ≃ n) (M : Matrix n n ℝ) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (Matrix.reindex e e M)‖ =
      ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) M‖ := by
  refine le_antisymm (norm_toEuclideanCLM_reindex_self_le e M) ?_
  have h := norm_toEuclideanCLM_reindex_self_le e.symm (Matrix.reindex e e M)
  have hre : Matrix.reindex e.symm e.symm (Matrix.reindex e e M) = M := by
    ext i j
    simp [Matrix.reindex_apply]
  simpa [hre] using h

theorem matrixOperatorNorm_inv_le_of_mul_eq_one {d : ℕ} [NeZero d]
    {A B : Mat d} (hAB : A * B = 1) (hApos : 0 < matrixOperatorNorm A) :
    (matrixOperatorNorm A)⁻¹ ≤ matrixOperatorNorm B := by
  have hmulNorm :
      matrixOperatorNorm (1 : Mat d) ≤ matrixOperatorNorm A * matrixOperatorNorm B := by
    calc
      matrixOperatorNorm (1 : Mat d)
          = matrixOperatorNorm (A * B) := by rw [hAB]
      _ ≤ matrixOperatorNorm A * matrixOperatorNorm B :=
          matrixOperatorNorm_mul_le A B
  have hOneMul : 1 ≤ matrixOperatorNorm A * matrixOperatorNorm B := by
    simpa using hmulNorm
  have hInvNonneg : 0 ≤ (matrixOperatorNorm A)⁻¹ := inv_nonneg.mpr hApos.le
  calc
    (matrixOperatorNorm A)⁻¹ = (matrixOperatorNorm A)⁻¹ * 1 := by ring
    _ ≤ (matrixOperatorNorm A)⁻¹ *
          (matrixOperatorNorm A * matrixOperatorNorm B) :=
        mul_le_mul_of_nonneg_left hOneMul hInvNonneg
    _ = matrixOperatorNorm B := by
        rw [← mul_assoc, inv_mul_cancel₀ hApos.ne']
        ring

theorem matrixOperatorNorm_diagonal {d : ℕ} (v : Fin d → ℝ) :
    matrixOperatorNorm (Matrix.diagonal v : Mat d) = ‖v‖ := by
  rw [matrixOperatorNorm_eq_l2_opNorm]
  exact Matrix.l2_opNorm_diagonal (𝕜 := ℝ) v

theorem matrixOperatorNorm_smul_one_eq_abs {d : ℕ} [NeZero d] (σ : ℝ) :
    matrixOperatorNorm (σ • (1 : Mat d)) = |σ| := by
  calc
    matrixOperatorNorm (σ • (1 : Mat d))
        = ‖σ • Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (1 : Mat d)‖ := by
            simp [matrixOperatorNorm]
    _ = |σ| * matrixOperatorNorm (1 : Mat d) := by
        rw [norm_smul, Real.norm_eq_abs]
        rfl
    _ = |σ| := by simp

theorem matrixOperatorNorm_smul_one_eq_of_nonneg {d : ℕ} [NeZero d]
    {σ : ℝ} (hσ : 0 ≤ σ) :
    matrixOperatorNorm (σ • (1 : Mat d)) = σ := by
  rw [matrixOperatorNorm_smul_one_eq_abs, abs_of_nonneg hσ]

theorem matrixFrobeniusNormSq_nonneg {d : ℕ} (A : Mat d) :
    0 ≤ matrixFrobeniusNormSq A := by
  unfold matrixFrobeniusNormSq
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem matrixFrobeniusNorm_nonneg {d : ℕ} (A : Mat d) :
    0 ≤ matrixFrobeniusNorm A := by
  exact Real.sqrt_nonneg _

theorem vecNorm_nonneg {d : ℕ} (x : Vec d) :
    0 ≤ vecNorm x := by
  exact norm_nonneg _

theorem vecNorm_sq_eq_vecNormSq {d : ℕ} (x : Vec d) :
    vecNorm x ^ 2 = vecNormSq x := by
  rw [vecNorm, EuclideanSpace.norm_sq_eq]
  simp [vecNormSq, vecDot, Real.norm_eq_abs, pow_two]

theorem vecNormSq_matVecMul_le_matrixFrobeniusNormSq_mul_vecNormSq
    {d : ℕ} (A : Mat d) (x : Vec d) :
    vecNormSq (matVecMul A x) ≤
      matrixFrobeniusNormSq A * vecNormSq x := by
  have hcalc :
      ∑ i, (∑ j, A i j * x j) ^ 2 ≤
        (∑ i, ∑ j, (A i j) ^ 2) * ∑ j, (x j) ^ 2 := by
    calc
      ∑ i, (∑ j, A i j * x j) ^ 2
          ≤ ∑ i, (∑ j, (A i j) ^ 2) * ∑ j, (x j) ^ 2 := by
              refine Finset.sum_le_sum ?_
              intro i _hi
              simpa [pow_two] using
                (Finset.sum_mul_sq_le_sq_mul_sq
                  (s := Finset.univ) (f := fun j => A i j) (g := x))
      _ = (∑ i, ∑ j, (A i j) ^ 2) * ∑ j, (x j) ^ 2 := by
            rw [Finset.sum_mul]
  simpa [vecNormSq, vecDot, matrixFrobeniusNormSq, matVecMul, pow_two] using hcalc

theorem vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm
    {d : ℕ} (A : Mat d) (x : Vec d) :
    vecNorm (matVecMul A x) ≤ matrixOperatorNorm A * vecNorm x := by
  have h :=
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A).le_opNorm
      (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))
  simpa [matrixOperatorNorm, vecNorm, matVecMul, Matrix.toEuclideanCLM_toLp,
    Matrix.mulVec] using! h

theorem vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq
    {d : ℕ} (A : Mat d) (x : Vec d) :
    vecNormSq (matVecMul A x) ≤ matrixOperatorNorm A ^ 2 * vecNormSq x := by
  have hnorm := vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm A x
  have hsq :
      vecNorm (matVecMul A x) ^ 2 ≤
        (matrixOperatorNorm A * vecNorm x) ^ 2 :=
    pow_le_pow_left₀ (vecNorm_nonneg (matVecMul A x)) hnorm 2
  calc
    vecNormSq (matVecMul A x)
        = vecNorm (matVecMul A x) ^ 2 := by rw [vecNorm_sq_eq_vecNormSq]
    _ ≤ (matrixOperatorNorm A * vecNorm x) ^ 2 := hsq
    _ = matrixOperatorNorm A ^ 2 * vecNormSq x := by
        rw [mul_pow, vecNorm_sq_eq_vecNormSq]

theorem matrixOperatorNorm_le_matrixFrobeniusNorm {d : ℕ} (A : Mat d) :
    matrixOperatorNorm A ≤ matrixFrobeniusNorm A := by
  refine ContinuousLinearMap.opNorm_le_bound _ (matrixFrobeniusNorm_nonneg A) ?_
  intro x
  let ξ : Vec d := x.ofLp
  have hsq :
      ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A x‖ ^ 2 ≤
        (matrixFrobeniusNorm A * ‖x‖) ^ 2 := by
    have hvec :
        vecNormSq (matVecMul A ξ) ≤
          matrixFrobeniusNormSq A * vecNormSq ξ :=
      vecNormSq_matVecMul_le_matrixFrobeniusNormSq_mul_vecNormSq A ξ
    calc
      ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A x‖ ^ 2
          = vecNormSq (matVecMul A ξ) := by
              have hx : x = WithLp.toLp 2 ξ := by
                simp [ξ]
              rw [← vecNorm_sq_eq_vecNormSq]
              rw [hx, Matrix.toEuclideanCLM_toLp]
              simp [vecNorm, ξ, matVecMul, Matrix.mulVec, dotProduct]
      _ ≤ matrixFrobeniusNormSq A * vecNormSq ξ := hvec
      _ = (matrixFrobeniusNorm A * ‖x‖) ^ 2 := by
          have hxnorm : vecNormSq ξ = ‖x‖ ^ 2 := by
            rw [← vecNorm_sq_eq_vecNormSq]
            simp [vecNorm, ξ]
          rw [matrixFrobeniusNorm, mul_pow,
            Real.sq_sqrt (matrixFrobeniusNormSq_nonneg A), hxnorm]
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (matrixFrobeniusNorm_nonneg A) (norm_nonneg x))).mp hsq

theorem abs_entry_le_matrixOperatorNorm {d : ℕ} (A : Mat d) (i j : Fin d) :
    |A i j| ≤ matrixOperatorNorm A := by
  let e : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (Pi.single j (1 : ℝ))
  have hcoord :
      ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A e).ofLp i‖ ≤
        ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A e‖ :=
    PiLp.norm_apply_le _ i
  have hop :
      ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A e‖ ≤
        matrixOperatorNorm A * ‖e‖ :=
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A).le_opNorm e
  have he : ‖e‖ = 1 := by
    simp [e]
  have hentry :
      ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A e).ofLp i‖ = |A i j| := by
    simp [e, Real.norm_eq_abs, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec]
  calc
    |A i j|
        = ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A e).ofLp i‖ :=
            hentry.symm
    _ ≤ ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A e‖ := hcoord
    _ ≤ matrixOperatorNorm A * ‖e‖ := hop
    _ = matrixOperatorNorm A := by simp [he]

/-- In finite dimension the legacy Frobenius norm is controlled by `d` times
the Euclidean operator norm.  This is the compatibility direction used when
old deterministic Frobenius estimates are retained as proof infrastructure. -/
theorem matrixFrobeniusNorm_le_dim_mul_matrixOperatorNorm {d : ℕ} (A : Mat d) :
    matrixFrobeniusNorm A ≤ (d : ℝ) * matrixOperatorNorm A := by
  let N : ℝ := matrixOperatorNorm A
  have hN_nonneg : 0 ≤ N := by
    simpa [N] using matrixOperatorNorm_nonneg A
  have hentry_sq :
      ∀ i j : Fin d, A i j ^ 2 ≤ N ^ 2 := by
    intro i j
    have hentry : |A i j| ≤ N := by
      simpa [N] using abs_entry_le_matrixOperatorNorm A i j
    have hsq := pow_le_pow_left₀ (abs_nonneg (A i j)) hentry 2
    simpa [sq_abs, pow_two] using hsq
  have hsum :
      matrixFrobeniusNormSq A ≤ (d : ℝ) ^ 2 * N ^ 2 := by
    calc
      matrixFrobeniusNormSq A
          = ∑ i : Fin d, ∑ j : Fin d, A i j ^ 2 := by
              rfl
      _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, N ^ 2 := by
          exact Finset.sum_le_sum fun i _ =>
            Finset.sum_le_sum fun j _ => hentry_sq i j
      _ = (d : ℝ) ^ 2 * N ^ 2 := by
          simp [Finset.sum_const, Fintype.card_fin]
          ring
  have hsq :
      matrixFrobeniusNorm A ^ 2 ≤ ((d : ℝ) * N) ^ 2 := by
    calc
      matrixFrobeniusNorm A ^ 2 = matrixFrobeniusNormSq A := by
        rw [matrixFrobeniusNorm, Real.sq_sqrt (matrixFrobeniusNormSq_nonneg A)]
      _ ≤ (d : ℝ) ^ 2 * N ^ 2 := hsum
      _ = ((d : ℝ) * N) ^ 2 := by ring
  exact (sq_le_sq₀ (matrixFrobeniusNorm_nonneg A)
    (mul_nonneg (Nat.cast_nonneg d) hN_nonneg)).mp hsq

/-- The legacy Frobenius norm is bounded by the entrywise `l¹` norm. -/
theorem matrixFrobeniusNorm_le_sum_abs_entries {d : ℕ} (A : Mat d) :
    matrixFrobeniusNorm A ≤ ∑ i : Fin d, ∑ j : Fin d, |A i j| := by
  classical
  have hsqsum :
      (∑ p : Fin d × Fin d, A p.1 p.2 ^ 2) =
        ∑ i : Fin d, ∑ j : Fin d, A i j ^ 2 := by
    simpa using
      (Finset.sum_product' (Finset.univ : Finset (Fin d))
        (Finset.univ : Finset (Fin d)) (fun i j => A i j ^ 2))
  have habssum :
      (∑ p : Fin d × Fin d, |A p.1 p.2|) =
        ∑ i : Fin d, ∑ j : Fin d, |A i j| := by
    simpa using
      (Finset.sum_product' (Finset.univ : Finset (Fin d))
        (Finset.univ : Finset (Fin d)) (fun i j => |A i j|))
  have hnonneg :
      0 ≤ ∑ p : Fin d × Fin d, |A p.1 p.2| := by
    exact Finset.sum_nonneg fun p _hp => abs_nonneg (A p.1 p.2)
  have hsq_le :
      (∑ p : Fin d × Fin d, |A p.1 p.2| ^ 2) ≤
        (∑ p : Fin d × Fin d, |A p.1 p.2|) ^ 2 := by
    exact Finset.sum_sq_le_sq_sum_of_nonneg
      (fun p _hp => abs_nonneg (A p.1 p.2))
  calc
    matrixFrobeniusNorm A =
        Real.sqrt (∑ p : Fin d × Fin d, A p.1 p.2 ^ 2) := by
      unfold matrixFrobeniusNorm matrixFrobeniusNormSq
      rw [hsqsum]
    _ = Real.sqrt (∑ p : Fin d × Fin d, |A p.1 p.2| ^ 2) := by
      simp [sq_abs]
    _ ≤ Real.sqrt ((∑ p : Fin d × Fin d, |A p.1 p.2|) ^ 2) :=
      Real.sqrt_le_sqrt hsq_le
    _ = ∑ p : Fin d × Fin d, |A p.1 p.2| := by
      simp [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]
    _ = ∑ i : Fin d, ∑ j : Fin d, |A i j| := habssum

/-- Triangle inequality for the Euclidean operator norm around a matrix
center. -/
theorem matrixOperatorNorm_le_matrixOperatorNorm_add_matrixOperatorNorm_sub
    {d : ℕ} (A B : Mat d) :
    matrixOperatorNorm A ≤ matrixOperatorNorm B + matrixOperatorNorm (A - B) := by
  have hdecomp : B + (A - B) = A := by
    ext i j
    simp
  calc
    matrixOperatorNorm A = ‖A‖ := matrixOperatorNorm_eq_l2_opNorm A
    _ = ‖B + (A - B)‖ := by rw [hdecomp]
    _ ≤ ‖B‖ + ‖A - B‖ := norm_add_le _ _
    _ = matrixOperatorNorm B + matrixOperatorNorm (A - B) := by
      rw [← matrixOperatorNorm_eq_l2_opNorm B,
        ← matrixOperatorNorm_eq_l2_opNorm (A - B)]

/-- The Euclidean operator norm around a center is controlled by the
entrywise `l¹` size of the centered matrix. -/
theorem matrixOperatorNorm_le_matrixOperatorNorm_add_sum_abs_sub_entries
    {d : ℕ} (A B : Mat d) :
    matrixOperatorNorm A ≤
      matrixOperatorNorm B + ∑ i : Fin d, ∑ j : Fin d, |A i j - B i j| := by
  calc
    matrixOperatorNorm A ≤ matrixOperatorNorm B + matrixOperatorNorm (A - B) :=
      matrixOperatorNorm_le_matrixOperatorNorm_add_matrixOperatorNorm_sub A B
    _ ≤ matrixOperatorNorm B + matrixFrobeniusNorm (A - B) :=
      add_le_add (le_refl (matrixOperatorNorm B))
        (matrixOperatorNorm_le_matrixFrobeniusNorm (A - B))
    _ ≤ matrixOperatorNorm B +
        ∑ i : Fin d, ∑ j : Fin d, |A i j - B i j| := by
      simpa [sub_eq_add_neg] using
        add_le_add (le_refl (matrixOperatorNorm B))
          (matrixFrobeniusNorm_le_sum_abs_entries (A - B))

theorem abs_vecDot_le_vecNorm_mul_vecNorm {d : ℕ} (x y : Vec d) :
    |vecDot x y| ≤ vecNorm x * vecNorm y := by
  have hsq :
      |vecDot x y| ^ 2 ≤ (vecNorm x * vecNorm y) ^ 2 := by
    rw [sq_abs, mul_pow, vecNorm_sq_eq_vecNormSq, vecNorm_sq_eq_vecNormSq]
    exact sq_vecDot_le_vecNormSq_mul_vecNormSq x y
  exact (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (vecNorm_nonneg x) (vecNorm_nonneg y))).mp hsq

theorem abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq
    {d : ℕ} (A : Mat d) (x : Vec d) :
    |vecDot x (matVecMul A x)| ≤ matrixOperatorNorm A * vecNormSq x := by
  calc
    |vecDot x (matVecMul A x)|
        ≤ vecNorm x * vecNorm (matVecMul A x) :=
            abs_vecDot_le_vecNorm_mul_vecNorm x (matVecMul A x)
    _ ≤ vecNorm x * (matrixOperatorNorm A * vecNorm x) :=
        mul_le_mul_of_nonneg_left
          (vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm A x)
          (vecNorm_nonneg x)
    _ = matrixOperatorNorm A * vecNormSq x := by
        rw [← vecNorm_sq_eq_vecNormSq]
        ring

theorem vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq_of_posSemidef
    {d : ℕ} {A : Mat d} (hA : A.PosSemidef) (x : Vec d) :
    vecDot x (matVecMul A x) ≤ matrixOperatorNorm A * vecNormSq x := by
  have hnonneg : 0 ≤ vecDot x (matVecMul A x) := by
    simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using
      hA.dotProduct_mulVec_nonneg x
  simpa [abs_of_nonneg hnonneg] using
    abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq A x

theorem vecNormSq_le_matrixOperatorNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
    {d : ℕ} {A B : Mat d} (hB : B.PosSemidef)
    (hleftInv : ∀ ξ : Vec d, matVecMul B (matVecMul A ξ) = ξ) (ξ : Vec d) :
    vecNormSq ξ ≤ matrixOperatorNorm B * vecDot ξ (matVecMul A ξ) := by
  let η : Vec d := matVecMul A ξ
  have hBsymm : B.IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hB.1
  have hBnonneg : ∀ z : Vec d, 0 ≤ vecDot z (matVecMul B z) := by
    intro z
    simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using
      hB.dotProduct_mulVec_nonneg z
  have hηeq : matVecMul B η = ξ := by
    simpa [η] using hleftInv ξ
  have hξη_nonneg : 0 ≤ vecDot ξ η := by
    have := hBnonneg η
    simpa [hηeq, vecDot_comm, η] using this
  have hcs :
      vecNormSq ξ ^ 2 ≤ vecDot ξ (matVecMul B ξ) * vecDot ξ η := by
    have hraw := sq_vecDot_matVecMul_le_of_isSymm_of_nonneg hBsymm hBnonneg ξ η
    simpa [vecNormSq, hηeq, vecDot_comm, η] using hraw
  have hfirst :
      vecDot ξ (matVecMul B ξ) ≤ matrixOperatorNorm B * vecNormSq ξ :=
    vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq_of_posSemidef hB ξ
  have hmain :
      vecNormSq ξ ^ 2 ≤
        (matrixOperatorNorm B * vecNormSq ξ) * vecDot ξ η := by
    exact le_trans hcs <| mul_le_mul_of_nonneg_right hfirst hξη_nonneg
  by_cases hx : vecNormSq ξ = 0
  · rw [hx]
    nlinarith [matrixOperatorNorm_nonneg B]
  · have hx_pos : 0 < vecNormSq ξ := by
      exact lt_of_le_of_ne (vecNormSq_nonneg ξ) (by simpa [eq_comm] using hx)
    have hnorm_nonneg : 0 ≤ matrixOperatorNorm B := matrixOperatorNorm_nonneg B
    nlinarith

theorem vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq_of_matLoewnerLE
    {d : ℕ} {A B : Mat d} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : MatLoewnerLE A B) (x : Vec d) :
    vecNormSq (matVecMul A x) ≤ matrixOperatorNorm B ^ 2 * vecNormSq x := by
  let y : Vec d := matVecMul A x
  let Z : ℝ := vecNormSq y
  let X : ℝ := vecNormSq x
  let C : ℝ := matrixOperatorNorm B
  have hAsymm : A.IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA.1
  have hAnonneg : ∀ z : Vec d, 0 ≤ vecDot z (matVecMul A z) := by
    intro z
    simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using
      hA.dotProduct_mulVec_nonneg z
  have hBnonneg : ∀ z : Vec d, 0 ≤ vecDot z (matVecMul B z) := by
    intro z
    simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using
      hB.dotProduct_mulVec_nonneg z
  have hAB' :
      ∀ z : Vec d, vecDot z (matVecMul A z) ≤ vecDot z (matVecMul B z) := by
    intro z
    have hz := hAB z
    nlinarith
  have hleft : vecDot x (matVecMul A y) = Z := by
    calc
      vecDot x (matVecMul A y) = vecDot y (matVecMul A x) :=
        vecDot_matVecMul_comm_of_isSymm hAsymm x y
      _ = Z := by
        simp [Z, y, vecNormSq]
  have hcs_raw :=
    sq_vecDot_matVecMul_le_of_isSymm_of_nonneg hAsymm hAnonneg x y
  have hcs :
      Z ^ 2 ≤ vecDot x (matVecMul A x) * vecDot y (matVecMul A y) := by
    simpa [hleft] using hcs_raw
  have hC_nonneg : 0 ≤ C := by
    simpa [C] using matrixOperatorNorm_nonneg B
  have hX_nonneg : 0 ≤ X := by
    simpa [X] using vecNormSq_nonneg x
  have hZ_nonneg : 0 ≤ Z := by
    simpa [Z, y] using vecNormSq_nonneg y
  have hAyy_nonneg : 0 ≤ vecDot y (matVecMul A y) := hAnonneg y
  have hBxx_le : vecDot x (matVecMul B x) ≤ C * X := by
    have hnonneg := hBnonneg x
    have h := abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq B x
    simpa [C, X, abs_of_nonneg hnonneg] using h
  have hByy_le : vecDot y (matVecMul B y) ≤ C * Z := by
    have hnonneg := hBnonneg y
    have h := abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq B y
    simpa [C, Z, abs_of_nonneg hnonneg] using h
  have hAxx_le : vecDot x (matVecMul A x) ≤ C * X :=
    (hAB' x).trans hBxx_le
  have hAyy_le : vecDot y (matVecMul A y) ≤ C * Z :=
    (hAB' y).trans hByy_le
  have hprod : Z ^ 2 ≤ (C * X) * (C * Z) := by
    exact hcs.trans
      (mul_le_mul hAxx_le hAyy_le hAyy_nonneg
        (mul_nonneg hC_nonneg hX_nonneg))
  have hZ_le : Z ≤ C ^ 2 * X := by
    by_cases hZ0 : Z = 0
    · rw [hZ0]
      exact mul_nonneg (sq_nonneg C) hX_nonneg
    · have hZpos : 0 < Z :=
        lt_of_le_of_ne hZ_nonneg (by simpa [eq_comm] using hZ0)
      have hprod' : Z ^ 2 ≤ C ^ 2 * X * Z := by
        nlinarith
      nlinarith
  simpa [Z, X, C, y] using hZ_le

theorem matrixOperatorNorm_le_of_matLoewnerLE_of_posSemidef
    {d : ℕ} {A B : Mat d} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : MatLoewnerLE A B) :
    matrixOperatorNorm A ≤ matrixOperatorNorm B := by
  refine ContinuousLinearMap.opNorm_le_bound _ (matrixOperatorNorm_nonneg B) ?_
  intro x
  let ξ : Vec d := x.ofLp
  have hsq :=
    vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq_of_matLoewnerLE
      hA hB hAB ξ
  have hvec : vecNorm (matVecMul A ξ) ≤ matrixOperatorNorm B * vecNorm ξ := by
    have hsq' :
        vecNorm (matVecMul A ξ) ^ 2 ≤
          (matrixOperatorNorm B * vecNorm ξ) ^ 2 := by
      calc
        vecNorm (matVecMul A ξ) ^ 2 = vecNormSq (matVecMul A ξ) :=
          vecNorm_sq_eq_vecNormSq _
        _ ≤ matrixOperatorNorm B ^ 2 * vecNormSq ξ := hsq
        _ = (matrixOperatorNorm B * vecNorm ξ) ^ 2 := by
          rw [mul_pow, vecNorm_sq_eq_vecNormSq]
    exact (sq_le_sq₀ (vecNorm_nonneg (matVecMul A ξ))
      (mul_nonneg (matrixOperatorNorm_nonneg B) (vecNorm_nonneg ξ))).mp hsq'
  simpa [matrixOperatorNorm, vecNorm, ξ, Matrix.toEuclideanCLM_toLp,
    matVecMul, Matrix.mulVec] using! hvec

theorem matrixOperatorNorm_pos_of_posDef {d : ℕ} [NeZero d] {A : Mat d}
    (hA : A.PosDef) :
    0 < matrixOperatorNorm A := by
  let i : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  have hdiag : 0 < A i i := hA.diag_pos
  have hentry := abs_entry_le_matrixOperatorNorm A i i
  have habs : 0 < |A i i| := abs_pos.mpr hdiag.ne'
  exact lt_of_lt_of_le habs hentry

theorem matrixOperatorNorm_descendantsAverageMat_le_descendantsAverage
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → Mat d) :
    matrixOperatorNorm (descendantsAverageMat Q j F) ≤
      descendantsAverage Q j (fun R => matrixOperatorNorm (F R)) := by
  classical
  let D := descendantsAtDepth Q j
  let c : ℝ := (D.card : ℝ)⁻¹
  have havg : descendantsAverageMat Q j F = c • D.sum F := by
    ext i k
    rw [Matrix.smul_apply, Matrix.sum_apply]
    simp [descendantsAverageMat, descendantsAverage, D, c]
  have hc_nonneg : 0 ≤ c := by positivity
  calc
    matrixOperatorNorm (descendantsAverageMat Q j F) =
        ‖descendantsAverageMat Q j F‖ := by
      simp [matrixOperatorNorm_eq_l2_opNorm]
    _ = ‖c • D.sum F‖ := by
      rw [havg]
    _ = |c| * ‖D.sum F‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |c| * D.sum (fun R => ‖F R‖) := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le D F) (abs_nonneg _)
    _ = c * D.sum (fun R => ‖F R‖) := by
      rw [abs_of_nonneg hc_nonneg]
    _ = descendantsAverage Q j (fun R => matrixOperatorNorm (F R)) := by
      simp [descendantsAverage, D, c, matrixOperatorNorm_eq_l2_opNorm]

end

end Ch02
end Book
end Homogenization

/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
import LeanPool.StatisticalLearningTheory.CoveringNumber
import LeanPool.StatisticalLearningTheory.HansonWright

/-!
# Random matrix theory

This file proves concentration and two-sided singular-value estimates for random matrices with
independent, mean-zero, isotropic sub-Gaussian rows.
-/

noncomputable section

namespace LeanPool.StatisticalLearningTheory

/-!
# Random Matrix Theory Basics

This file develops the random-matrix infrastructure for HDP, Theorem 4.6.1.

## Main definitions

* `RMT.matrixOperatorNorm`: the Euclidean `2 → 2` operator norm of a rectangular matrix.
* `RMT.randomMatrix`: a random rectangular matrix assembled from scalar entries.
* `RMT.matrixLargestSingularValue`: the largest singular value `s₁(A)`.
* `RMT.matrixSmallestSingularValue`: the smallest domain-indexed singular value `sₙ(A)`.
* `RMT.maxMatrixRowSubGaussianPsi2Norm`: maximum vector ψ₂ scale over the rows.
* `RMT.HasIndependentMeanZeroIsotropicSubGaussianRows`: the row assumptions in
  HDP Theorem 4.6.1.

## Main results

* `RMT.twoSidedSubgaussianMatricesHdp`: the exact proposition stated by
  HDP Theorem 4.6.1.
* `RMT.two_sided_subgaussian_matrices_hdp_of_pos`: the theorem for positive dimensions.
-/

open _root_.MeasureTheory _root_.ProbabilityTheory Real Filter
open scoped BigOperators NNReal Topology

section

namespace RMT

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Deterministic rectangular matrices -/

/-- The Euclidean `2 → 2` operator norm of a rectangular real matrix. -/
def matrixOperatorNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ‖A.toEuclideanLin.toContinuousLinearMap‖

omit [MeasurableSpace Ω] in
/-- The zero-based singular values of a real matrix, as singular values of its Euclidean map. -/
def matrixSingularValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) : ℝ :=
  A.toEuclideanLin.singularValues k

omit [MeasurableSpace Ω] in
/-- The largest singular value `s₁(A)` of a real matrix. -/
def matrixLargestSingularValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  matrixSingularValue A 0

omit [MeasurableSpace Ω] in
/-- The smallest domain-indexed singular value `sₙ(A)` of an `m × n` real matrix. -/
def matrixSmallestSingularValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  matrixSingularValue A (n - 1)

omit [MeasurableSpace Ω] in
lemma matrixSingularValue_nonneg {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ matrixSingularValue A k :=
  A.toEuclideanLin.singularValues_nonneg k

omit [MeasurableSpace Ω] in
lemma matrixSmallestSingularValue_le_largest {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    matrixSmallestSingularValue A ≤ matrixLargestSingularValue A := by
  unfold matrixSmallestSingularValue matrixLargestSingularValue matrixSingularValue
  exact A.toEuclideanLin.singularValues_antitone (Nat.zero_le (n - 1))

/-- A random rectangular matrix assembled from scalar entries. -/
def randomMatrix {m n : ℕ} (A : Fin m → Fin n → Ω → ℝ) (ω : Ω) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => A i j ω

omit [MeasurableSpace Ω] in
@[simp]
private lemma randomMatrix_apply {m n : ℕ} (A : Fin m → Fin n → Ω → ℝ) (ω : Ω)
    (i : Fin m) (j : Fin n) :
    randomMatrix A ω i j = A i j ω := rfl

omit [MeasurableSpace Ω] in
/-- The empirical covariance deviation `m⁻¹ AᵀA - Iₙ` appearing in HDP Theorem 4.6.1. -/
def sampleCovarianceDeviation {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ((m : ℝ)⁻¹) • (A.conjTranspose * A) - 1

omit [MeasurableSpace Ω] in
/-- Operator norm of the empirical covariance deviation `m⁻¹ AᵀA - Iₙ`. -/
def sampleCovarianceDeviationOperatorNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ℝ :=
  matrixOperatorNorm (sampleCovarianceDeviation A)

omit [MeasurableSpace Ω] in
/-- The Euclidean linear map associated to `AᵀA` is `A† ∘ A`. -/
lemma conjTranspose_mul_self_toEuclideanLin {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    (A.conjTranspose * A).toEuclideanLin =
      LinearMap.adjoint A.toEuclideanLin ∘ₗ A.toEuclideanLin := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint A]
  simpa [Matrix.toEuclideanLin_eq_toLin_orthonormal] using Matrix.toLin_mul
    (v₁ := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
    (v₂ := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis)
    (v₃ := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis) A.conjTranspose A

omit [MeasurableSpace Ω] in
lemma inner_conjTranspose_mul_self_toEuclideanLin {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ ((A.conjTranspose * A).toEuclideanLin x) x =
      ‖A.toEuclideanLin x‖ ^ 2 := by
  rw [conjTranspose_mul_self_toEuclideanLin]
  rw [LinearMap.comp_apply]
  rw [LinearMap.adjoint_inner_left]
  rw [real_inner_self_eq_norm_sq]

omit [MeasurableSpace Ω] in
lemma inner_sampleCovarianceDeviation_toEuclideanLin {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ ((sampleCovarianceDeviation A).toEuclideanLin x) x =
      (m : ℝ)⁻¹ * ‖A.toEuclideanLin x‖ ^ 2 - ‖x‖ ^ 2 := by
  unfold sampleCovarianceDeviation
  change inner ℝ
      (WithLp.toLp 2 (((((m : ℝ)⁻¹ • (A.conjTranspose * A) - 1).mulVec x.ofLp)))) x =
    (m : ℝ)⁻¹ * ‖A.toEuclideanLin x‖ ^ 2 - ‖x‖ ^ 2
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [PiLp.inner_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, RCLike.inner_apply, conj_trivial, smul_eq_mul]
  have hgram :
      ∑ i : Fin n, (m : ℝ)⁻¹ *
          (((A.conjTranspose * A).mulVec x.ofLp) i) * x.ofLp i =
        (m : ℝ)⁻¹ * ‖A.toEuclideanLin x‖ ^ 2 := by
    calc
      ∑ i : Fin n, (m : ℝ)⁻¹ *
          (((A.conjTranspose * A).mulVec x.ofLp) i) * x.ofLp i
          = (m : ℝ)⁻¹ * ∑ i : Fin n,
              (((A.conjTranspose * A).mulVec x.ofLp) i) * x.ofLp i := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (m : ℝ)⁻¹ * inner ℝ ((A.conjTranspose * A).toEuclideanLin x) x := by
              congr 1
              rw [show ((A.conjTranspose * A).toEuclideanLin x) =
                WithLp.toLp 2 (((A.conjTranspose * A).mulVec x.ofLp)) by rfl]
              rw [PiLp.inner_apply]
              simp only [RCLike.inner_apply, conj_trivial]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (m : ℝ)⁻¹ * ‖A.toEuclideanLin x‖ ^ 2 := by
              rw [inner_conjTranspose_mul_self_toEuclideanLin]
  have hx_sq :
      ∑ i : Fin n, x.ofLp i * x.ofLp i = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc
    ∑ x_1 : Fin n,
        x.ofLp x_1 *
        ((m : ℝ)⁻¹ * (((A.conjTranspose * A).mulVec x.ofLp) x_1) - x.ofLp x_1)
        = ∑ i : Fin n,
            (m : ℝ)⁻¹ * (((A.conjTranspose * A).mulVec x.ofLp) i) * x.ofLp i -
          ∑ i : Fin n, x.ofLp i * x.ofLp i := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = (m : ℝ)⁻¹ * ‖A.toEuclideanLin x‖ ^ 2 - ‖x‖ ^ 2 := by
          rw [hgram, hx_sq]
    _ = (m : ℝ)⁻¹ * ‖A.toEuclideanLin x‖ ^ 2 - ‖x‖ ^ 2 := rfl

omit [MeasurableSpace Ω] in
lemma sampleCovarianceDeviation_isSymm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (sampleCovarianceDeviation A).IsSymm := by
  have hgram : (A.conjTranspose * A).IsSymm := by
    rw [← Matrix.isHermitian_iff_isSymm]
    exact Matrix.isHermitian_conjTranspose_mul_self A
  refine Matrix.IsSymm.ext ?_
  intro i j
  have hji : (A.conjTranspose * A) j i = (A.conjTranspose * A) i j :=
    Matrix.IsSymm.apply hgram i j
  have hji' : (A.transpose * A) j i = (A.transpose * A) i j := by
    simpa using hji
  have hone : (1 : Matrix (Fin n) (Fin n) ℝ) j i = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    by_cases hij : i = j
    · subst j
      rfl
    · have hji_ne : j ≠ i := fun h => hij h.symm
      simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne hji_ne]
  change (((m : ℝ)⁻¹ • (A.conjTranspose * A) -
      (1 : Matrix (Fin n) (Fin n) ℝ)) j i) =
    (((m : ℝ)⁻¹ • (A.conjTranspose * A) -
      (1 : Matrix (Fin n) (Fin n) ℝ)) i j)
  calc
    (((m : ℝ)⁻¹ • (A.conjTranspose * A) -
        (1 : Matrix (Fin n) (Fin n) ℝ)) j i)
        = (m : ℝ)⁻¹ * (A.transpose * A) j i -
            (1 : Matrix (Fin n) (Fin n) ℝ) j i := by simp
    _ = (m : ℝ)⁻¹ * (A.transpose * A) i j -
            (1 : Matrix (Fin n) (Fin n) ℝ) i j := by rw [hji', hone]
    _ = (((m : ℝ)⁻¹ • (A.conjTranspose * A) -
        (1 : Matrix (Fin n) (Fin n) ℝ)) i j) := by simp

omit [MeasurableSpace Ω] in
lemma abs_inner_toEuclideanLin_le_matrixOperatorNorm_mul_norm_sq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    |inner ℝ (A.toEuclideanLin x) x| ≤ matrixOperatorNorm A * ‖x‖ ^ 2 := by
  have hAx :
      ‖A.toEuclideanLin x‖ ≤ matrixOperatorNorm A * ‖x‖ := by
    simpa [matrixOperatorNorm] using A.toEuclideanLin.toContinuousLinearMap.le_opNorm x
  calc
    |inner ℝ (A.toEuclideanLin x) x| ≤ ‖A.toEuclideanLin x‖ * ‖x‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (matrixOperatorNorm A * ‖x‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right hAx (norm_nonneg x)
    _ = matrixOperatorNorm A * ‖x‖ ^ 2 := by ring

omit [MeasurableSpace Ω] in
lemma abs_inv_mul_sq_matrixSingularValue_sub_one_le_sampleCovarianceDeviationOperatorNorm
    {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hk : k < n) :
    |(m : ℝ)⁻¹ * matrixSingularValue A k ^ 2 - 1| ≤
      sampleCovarianceDeviationOperatorNorm A := by
  let T := A.toEuclideanLin
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
    simp
  have hkfin : k < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa [hfin] using hk
  have heig :
      Module.End.HasEigenvalue (LinearMap.adjoint T ∘ₗ T) (T.singularValues k ^ 2) :=
    T.hasEigenvalue_adjoint_comp_self_sq_singularValues hkfin
  rcases heig.exists_hasEigenvector with ⟨v, hv⟩
  let r : ℝ := ‖v‖
  let y : EuclideanSpace ℝ (Fin n) := r⁻¹ • v
  have hv_ne : v ≠ 0 := hv.2
  have hr_pos : 0 < r := by
    dsimp [r]
    exact norm_pos_iff.mpr hv_ne
  have hy_norm : ‖y‖ = 1 := by
    dsimp [y]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr_pos.le)]
    exact inv_mul_cancel₀ hr_pos.ne'
  have hy_eig : (LinearMap.adjoint T ∘ₗ T) y = (T.singularValues k ^ 2) • y := by
    calc
      (LinearMap.adjoint T ∘ₗ T) y
          = r⁻¹ • ((LinearMap.adjoint T ∘ₗ T) v) := by
            dsimp [y]
            rw [map_smul, map_smul]
      _ = r⁻¹ • ((T.singularValues k ^ 2) • v) := by
            rw [hv.apply_eq_smul]
      _ = (T.singularValues k ^ 2) • y := by
            dsimp [y]
            rw [smul_smul, smul_smul]
            congr 1
            ring
  have hinner_adjoint :
      inner ℝ ((LinearMap.adjoint T ∘ₗ T) y) y = ‖T y‖ ^ 2 := by
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
  have hTy_sq : ‖T y‖ ^ 2 = matrixSingularValue A k ^ 2 := by
    calc
      ‖T y‖ ^ 2 = inner ℝ ((LinearMap.adjoint T ∘ₗ T) y) y := hinner_adjoint.symm
      _ = T.singularValues k ^ 2 := by
        rw [hy_eig, inner_smul_left, real_inner_self_eq_norm_sq, hy_norm]
        simp
      _ = matrixSingularValue A k ^ 2 := by
        rfl
  have hquad :=
    abs_inner_toEuclideanLin_le_matrixOperatorNorm_mul_norm_sq
      (sampleCovarianceDeviation A) y
  rw [inner_sampleCovarianceDeviation_toEuclideanLin, hTy_sq, hy_norm] at hquad
  simpa [sampleCovarianceDeviationOperatorNorm] using hquad

omit [MeasurableSpace Ω] in
lemma matrixSingularValue_sq_bounds_of_sampleCovarianceDeviationOperatorNorm_le
    {m n k : ℕ} (hm : 0 < m) (A : Matrix (Fin m) (Fin n) ℝ)
    {δ : ℝ} (hδ : sampleCovarianceDeviationOperatorNorm A ≤ δ) (hk : k < n) :
    (m : ℝ) * (1 - δ) ≤ matrixSingularValue A k ^ 2 ∧
      matrixSingularValue A k ^ 2 ≤ (m : ℝ) * (1 + δ) := by
  have hmR_pos : 0 < (m : ℝ) := by exact_mod_cast hm
  have habs :=
    (abs_inv_mul_sq_matrixSingularValue_sub_one_le_sampleCovarianceDeviationOperatorNorm
      (m := m) (n := n) (k := k) A hk).trans hδ
  have hbounds := abs_le.mp habs
  constructor
  · have hlower : 1 - δ ≤ (m : ℝ)⁻¹ * matrixSingularValue A k ^ 2 := by
      linarith
    calc
      (m : ℝ) * (1 - δ) ≤
          (m : ℝ) * ((m : ℝ)⁻¹ * matrixSingularValue A k ^ 2) :=
        mul_le_mul_of_nonneg_left hlower hmR_pos.le
      _ = matrixSingularValue A k ^ 2 := by
        field_simp [hmR_pos.ne']
  · have hupper : (m : ℝ)⁻¹ * matrixSingularValue A k ^ 2 ≤ 1 + δ := by
      linarith
    calc
      matrixSingularValue A k ^ 2 =
          (m : ℝ) * ((m : ℝ)⁻¹ * matrixSingularValue A k ^ 2) := by
        field_simp [hmR_pos.ne']
      _ ≤ (m : ℝ) * (1 + δ) :=
        mul_le_mul_of_nonneg_left hupper hmR_pos.le

omit [MeasurableSpace Ω] in
lemma matrixSingularValue_bounds_of_sampleCovarianceDeviationOperatorNorm_le_max
    {m n k : ℕ} (hm : 0 < m) (A : Matrix (Fin m) (Fin n) ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hdev : sampleCovarianceDeviationOperatorNorm A ≤
      max (B / √(m : ℝ)) ((B / √(m : ℝ)) ^ 2))
    (hk : k < n) :
    √(m : ℝ) - B ≤ matrixSingularValue A k ∧
      matrixSingularValue A k ≤ √(m : ℝ) + B := by
  let a : ℝ := √(m : ℝ)
  let s : ℝ := matrixSingularValue A k
  let ε : ℝ := B / a
  have hmR_pos : 0 < (m : ℝ) := by exact_mod_cast hm
  have ha_pos : 0 < a := by
    dsimp [a]
    exact sqrt_pos.mpr hmR_pos
  have ha_nonneg : 0 ≤ a := ha_pos.le
  have ha_sq : a ^ 2 = (m : ℝ) := by
    dsimp [a]
    exact sq_sqrt hmR_pos.le
  have hε_nonneg : 0 ≤ ε := div_nonneg hB ha_nonneg
  have hsq_bounds :=
    matrixSingularValue_sq_bounds_of_sampleCovarianceDeviationOperatorNorm_le
      (m := m) (n := n) (k := k) hm A hdev hk
  have hsq_lower : (m : ℝ) * (1 - max ε (ε ^ 2)) ≤ s ^ 2 := by
    simpa [s, ε, a] using hsq_bounds.1
  have hsq_upper : s ^ 2 ≤ (m : ℝ) * (1 + max ε (ε ^ 2)) := by
    simpa [s, ε, a] using hsq_bounds.2
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact matrixSingularValue_nonneg A
  have hupper_sq : s ^ 2 ≤ (a + B) ^ 2 := by
    by_cases hBa : B ≤ a
    · have hε_le_one : ε ≤ 1 := by
        dsimp [ε]
        exact div_le_one_of_le₀ hBa ha_nonneg
      have hε_sq_le : ε ^ 2 ≤ ε := by nlinarith [hε_nonneg, hε_le_one]
      have hmax : max ε (ε ^ 2) = ε := max_eq_left hε_sq_le
      have hmul : (m : ℝ) * max ε (ε ^ 2) ≤ (m : ℝ) * ε :=
        mul_le_mul_of_nonneg_left (by rw [hmax]) hmR_pos.le
      calc
        s ^ 2 ≤ (m : ℝ) * (1 + max ε (ε ^ 2)) := hsq_upper
        _ ≤ a ^ 2 * (1 + ε) := by
              rw [ha_sq]
              nlinarith
        _ = a ^ 2 + a * B := by
              dsimp [ε]
              field_simp [ha_pos.ne']
        _ ≤ (a + B) ^ 2 := by
              nlinarith [ha_nonneg, hB, sq_nonneg B]
    · have ha_le_B : a ≤ B := le_of_not_ge hBa
      have hε_ge_one : 1 ≤ ε := by
        dsimp [ε]
        exact (one_le_div ha_pos).mpr ha_le_B
      have hε_le_sq : ε ≤ ε ^ 2 := by nlinarith [hε_nonneg, hε_ge_one]
      have hmax : max ε (ε ^ 2) = ε ^ 2 := max_eq_right hε_le_sq
      calc
        s ^ 2 ≤ (m : ℝ) * (1 + max ε (ε ^ 2)) := hsq_upper
        _ ≤ a ^ 2 * (1 + ε ^ 2) := by
              rw [ha_sq, hmax]
        _ = a ^ 2 + B ^ 2 := by
              dsimp [ε]
              field_simp [ha_pos.ne']
        _ ≤ (a + B) ^ 2 := by
              nlinarith [ha_nonneg, hB]
  have hupper : s ≤ a + B :=
    le_of_sq_le_sq hupper_sq (add_nonneg ha_nonneg hB)
  have hlower : a - B ≤ s := by
    by_cases hBa : B ≤ a
    · have hε_le_one : ε ≤ 1 := by
        dsimp [ε]
        exact div_le_one_of_le₀ hBa ha_nonneg
      have hε_sq_le : ε ^ 2 ≤ ε := by nlinarith [hε_nonneg, hε_le_one]
      have hmax : max ε (ε ^ 2) = ε := max_eq_left hε_sq_le
      have hlower_sq : (a - B) ^ 2 ≤ s ^ 2 := by
        calc
          (a - B) ^ 2 ≤ a ^ 2 * (1 - ε) := by
                dsimp [ε]
                field_simp [ha_pos.ne']
                nlinarith [hB, hBa, ha_nonneg]
          _ = (m : ℝ) * (1 - max ε (ε ^ 2)) := by
                rw [ha_sq, hmax]
          _ ≤ s ^ 2 := hsq_lower
      exact le_of_sq_le_sq hlower_sq hs_nonneg
    · have hle_zero : a - B ≤ 0 := by
        exact sub_nonpos.mpr (le_of_not_ge hBa)
      exact hle_zero.trans hs_nonneg
  exact ⟨by simpa [a, s] using hlower, by simpa [a, s] using hupper⟩

omit [MeasurableSpace Ω] in
lemma singular_value_sandwich_of_sampleCovarianceDeviationOperatorNorm_le_max
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hdev : sampleCovarianceDeviationOperatorNorm A ≤
      max (B / √(m : ℝ)) ((B / √(m : ℝ)) ^ 2)) :
    √(m : ℝ) - B ≤ matrixSmallestSingularValue A ∧
      matrixSmallestSingularValue A ≤ matrixLargestSingularValue A ∧
        matrixLargestSingularValue A ≤ √(m : ℝ) + B := by
  have hsmall :=
    matrixSingularValue_bounds_of_sampleCovarianceDeviationOperatorNorm_le_max
      (m := m) (n := n) (k := n - 1) hm A hB hdev (by omega)
  have hlarge :=
    matrixSingularValue_bounds_of_sampleCovarianceDeviationOperatorNorm_le_max
      (m := m) (n := n) (k := 0) hm A hB hdev hn
  exact ⟨by simpa [matrixSmallestSingularValue] using hsmall.1,
    matrixSmallestSingularValue_le_largest A,
    by simpa [matrixLargestSingularValue] using hlarge.2⟩

omit [MeasurableSpace Ω] in
/-- The `i`-th row of a real matrix as a Euclidean vector. -/
def matrixRowVector {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j => A i j

/-! ## Matrix-specific nets -/

/-- The Euclidean unit sphere in `ℝ^n`. -/
def euclideanUnitSphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.sphere 0 1

/-- The Euclidean unit ball in `ℝ^n`. -/
def euclideanUnitBall (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.closedBall 0 1

/--
A pair of finite nets used to discretize the bilinear form
`(x, y) ↦ ⟪A x, y⟫` for an `m × n` matrix.  The underlying net notion is the generic
`IsENet` from `SLT.CoveringNumber`; this structure only packages the domain and codomain nets
needed for rectangular matrix operator norms.
-/
structure MatrixBilinearNet (m n : ℕ) (ε : ℝ) where
  /-- A finite net for the domain unit sphere. -/
  domainNet : Finset (EuclideanSpace ℝ (Fin n))
  /-- A finite net for the codomain unit sphere. -/
  codomainNet : Finset (EuclideanSpace ℝ (Fin m))
  domain_isNet : IsENet domainNet ε (euclideanUnitSphere n)
  codomain_isNet : IsENet codomainNet ε (euclideanUnitSphere m)

/--
A centered matrix bilinear net: the net points themselves lie in the corresponding unit balls.
This is the form naturally produced by finite coverings of the unit balls and used in the
Section 4.4 net argument.
-/
structure CenteredMatrixBilinearNet (m n : ℕ) (ε : ℝ) extends
    MatrixBilinearNet m n ε where
  domain_subset_unitBall : (domainNet : Set (EuclideanSpace ℝ (Fin n))) ⊆ euclideanUnitBall n
  codomain_subset_unitBall : (codomainNet : Set (EuclideanSpace ℝ (Fin m))) ⊆
    euclideanUnitBall m

omit [MeasurableSpace Ω] in
lemma norm_eq_one_of_mem_euclideanUnitSphere {n : ℕ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ euclideanUnitSphere n) :
    ‖x‖ = 1 := by
  simpa [euclideanUnitSphere, dist_eq_norm] using hx

omit [MeasurableSpace Ω] in
lemma norm_le_one_of_mem_euclideanUnitBall {n : ℕ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ euclideanUnitBall n) :
    ‖x‖ ≤ 1 := by
  simpa [euclideanUnitBall, dist_eq_norm] using hx

omit [MeasurableSpace Ω] in
lemma MatrixBilinearNet.exists_domain_near {m n : ℕ} {ε : ℝ}
    (N : MatrixBilinearNet m n ε) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ euclideanUnitSphere n) :
    ∃ x₀ ∈ N.domainNet, ‖x - x₀‖ ≤ ε := by
  obtain ⟨x₀, hx₀, hball⟩ := Set.mem_iUnion₂.mp (N.domain_isNet hx)
  exact ⟨x₀, hx₀, by simpa [dist_eq_norm] using Metric.mem_closedBall.mp hball⟩

omit [MeasurableSpace Ω] in
lemma exists_centeredMatrixBilinearNet {m n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∃ N : CenteredMatrixBilinearNet m n ε,
      (N.domainNet.card : WithTop ℕ) ≤
        coveringNumber (ε / 2) (euclideanBall 1 : Set (EuclideanSpace ℝ (Fin n))) ∧
      (N.codomainNet.card : WithTop ℕ) ≤
        coveringNumber (ε / 2) (euclideanBall 1 : Set (EuclideanSpace ℝ (Fin m))) := by
  obtain ⟨domainNet, hdomain_net_ball, hdomain_subset, hdomain_card⟩ :=
    exists_enet_subset_from_half (A := EuclideanSpace ℝ (Fin n)) (eps := ε)
      (s := (euclideanBall 1 : Set (EuclideanSpace ℝ (Fin n)))) hε
      (euclideanBall_totallyBounded (ι := Fin n) 1)
      (euclideanBall_nonempty (ι := Fin n) (by norm_num : (0 : ℝ) ≤ 1))
  obtain ⟨codomainNet, hcodomain_net_ball, hcodomain_subset, hcodomain_card⟩ :=
    exists_enet_subset_from_half (A := EuclideanSpace ℝ (Fin m)) (eps := ε)
      (s := (euclideanBall 1 : Set (EuclideanSpace ℝ (Fin m)))) hε
      (euclideanBall_totallyBounded (ι := Fin m) 1)
      (euclideanBall_nonempty (ι := Fin m) (by norm_num : (0 : ℝ) ≤ 1))
  refine ⟨
    { domainNet := domainNet
      codomainNet := codomainNet
      domain_isNet := ?_
      codomain_isNet := ?_
      domain_subset_unitBall := ?_
      codomain_subset_unitBall := ?_ },
    hdomain_card, hcodomain_card⟩
  · intro x hx
    exact hdomain_net_ball (by
      have hxnorm := norm_eq_one_of_mem_euclideanUnitSphere hx
      simpa [euclideanBall, Metric.mem_closedBall, dist_eq_norm] using hxnorm.le)
  · intro y hy
    exact hcodomain_net_ball (by
      have hynorm := norm_eq_one_of_mem_euclideanUnitSphere hy
      simpa [euclideanBall, Metric.mem_closedBall, dist_eq_norm] using hynorm.le)
  · simpa [euclideanUnitBall, euclideanBall] using hdomain_subset
  · simpa [euclideanUnitBall, euclideanBall] using hcodomain_subset

omit [MeasurableSpace Ω] in
lemma exists_quarter_centeredMatrixBilinearNet (m n : ℕ) :
    ∃ N : CenteredMatrixBilinearNet m n (1 / 4),
      (N.domainNet.card : WithTop ℕ) ≤
        coveringNumber (1 / 8) (euclideanBall 1 : Set (EuclideanSpace ℝ (Fin n))) ∧
      (N.codomainNet.card : WithTop ℕ) ≤
        coveringNumber (1 / 8) (euclideanBall 1 : Set (EuclideanSpace ℝ (Fin m))) := by
  obtain ⟨N, hdomain, hcodomain⟩ :=
    exists_centeredMatrixBilinearNet (m := m) (n := n)
      (by norm_num : 0 < (1 / 4 : ℝ))
  refine ⟨N, ?_, ?_⟩
  · simpa [show (4 : ℝ)⁻¹ / 2 = (8 : ℝ)⁻¹ by norm_num] using hdomain
  · simpa [show (4 : ℝ)⁻¹ / 2 = (8 : ℝ)⁻¹ by norm_num] using hcodomain

omit [MeasurableSpace Ω] in
lemma finset_card_le_seventeen_pow_of_card_le_euclideanBall_coveringNumber {d : ℕ}
    (hd : 0 < d) {t : Finset (EuclideanSpace ℝ (Fin d))}
    (ht :
      (t.card : WithTop ℕ) ≤
        coveringNumber (1 / 8) (euclideanBall 1 : Set (EuclideanSpace ℝ (Fin d)))) :
    (t.card : ℝ) ≤ 17 ^ d := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hcover_top :
      coveringNumber (1 / 8) (euclideanBall 1 : Set (EuclideanSpace ℝ (Fin d))) < ⊤ :=
    coveringNumber_lt_top_of_totallyBounded (by norm_num : 0 < (1 / 8 : ℝ))
      (euclideanBall_totallyBounded (ι := Fin d) 1)
  let hcover_ne_top :
      coveringNumber (1 / 8) (euclideanBall 1 : Set (EuclideanSpace ℝ (Fin d))) ≠ ⊤ :=
    ne_top_of_lt hcover_top
  have ht_nat :
      t.card ≤
        (coveringNumber (1 / 8) (euclideanBall 1 : Set (EuclideanSpace ℝ (Fin d)))).untop
          hcover_ne_top := by
    rw [← WithTop.coe_le_coe]
    rw [WithTop.coe_untop]
    exact ht
  have hcover_bound :
      (((coveringNumber (1 / 8) (euclideanBall 1 : Set (EuclideanSpace ℝ (Fin d)))).untop
          hcover_ne_top : ℕ) : ℝ) ≤ 17 ^ d := by
    have h :=
      coveringNumber_euclideanBall_le (ι := Fin d) (R := 1) (eps := 1 / 8)
        (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : 0 < (1 / 8 : ℝ))
    norm_num at h
    simpa [Fintype.card_fin] using h
  have ht_real :
      (t.card : ℝ) ≤
        (((coveringNumber (1 / 8) (euclideanBall 1 : Set (EuclideanSpace ℝ (Fin d)))).untop
          hcover_ne_top : ℕ) : ℝ) := by
    exact_mod_cast ht_nat
  exact ht_real.trans hcover_bound

omit [MeasurableSpace Ω] in
lemma centeredMatrixBilinearNet_domain_card_le_seventeen_pow {m n : ℕ} (hn : 0 < n)
    (N : CenteredMatrixBilinearNet m n (1 / 4))
    (hN :
      (N.domainNet.card : WithTop ℕ) ≤
        coveringNumber (1 / 8) (euclideanBall 1 : Set (EuclideanSpace ℝ (Fin n)))) :
    (N.domainNet.card : ℝ) ≤ 17 ^ n :=
  finset_card_le_seventeen_pow_of_card_le_euclideanBall_coveringNumber hn hN

omit [MeasurableSpace Ω] in
lemma matrix_toEuclideanLin_isSymmetric_of_isSymm {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    A.toEuclideanLin.IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.isSelfAdjoint_iff']
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint A]
  have hconj : A.conjTranspose = A := by
    ext i j
    simpa [Matrix.conjTranspose] using hA.apply i j
  rw [hconj]

omit [MeasurableSpace Ω] in
lemma matrix_toEuclideanCLM_isSymmetric_of_isSymm {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    (A.toEuclideanLin.toContinuousLinearMap).IsSymmetric := by
  have hlin := matrix_toEuclideanLin_isSymmetric_of_isSymm hA
  exact LinearMap.IsSymmetric.isSelfAdjoint
    (A := A.toEuclideanLin.toContinuousLinearMap) (by simpa using hlin) |>.isSymmetric

omit [MeasurableSpace Ω] in
lemma matrixOperatorNorm_le_of_forall_unit_abs_quadratic_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA_symm : A.IsSymm) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 →
      |inner ℝ (A.toEuclideanLin x) x| ≤ B) :
    matrixOperatorNorm A ≤ B := by
  let T := A.toEuclideanLin.toContinuousLinearMap
  have hT_symm : T.IsSymmetric := by
    simpa [T] using matrix_toEuclideanCLM_isSymmetric_of_isSymm hA_symm
  have hray : ∀ x, |T.rayleighQuotient x| ≤ B := by
    intro x
    by_cases hx : x = 0
    · simp [T, ContinuousLinearMap.rayleighQuotient, hx, hB]
    · let c : ℝ := ‖x‖⁻¹
      have hc : c ≠ 0 := by
        simp [c, norm_ne_zero_iff.mpr hx]
      let y : EuclideanSpace ℝ (Fin n) := c • x
      have hy_norm : ‖y‖ = 1 := by
        simp [y, c, norm_smul, norm_ne_zero_iff.mpr hx]
      have hy_ray : T.rayleighQuotient y = T.rayleighQuotient x := by
        simpa [y, c] using T.rayleigh_smul x (c := c) hc
      calc
        |T.rayleighQuotient x| = |T.rayleighQuotient y| := by rw [hy_ray]
        _ = |inner ℝ (A.toEuclideanLin y) y| := by
          simp [T, ContinuousLinearMap.rayleighQuotient,
            ContinuousLinearMap.reApplyInnerSelf_apply, hy_norm]
        _ ≤ B := h y hy_norm
  unfold matrixOperatorNorm
  change ‖T‖ ≤ B
  rw [T.norm_eq_iSup_rayleighQuotient hT_symm]
  exact ciSup_le hray

/--
Deterministic net reduction for symmetric operator norms. If a centered `ε`-net of the unit
sphere controls all quadratic forms `⟪Ax, x⟫`, then it controls the Euclidean operator norm.
-/
lemma matrixOperatorNorm_le_of_centered_quadratic_net {n : ℕ} {ε u : ℝ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA_symm : A.IsSymm)
    (N : CenteredMatrixBilinearNet n n ε) (hε_nonneg : 0 ≤ ε) (hε : 2 * ε < 1)
    (hu : 0 ≤ u)
    (hnet : ∀ x ∈ N.domainNet, |inner ℝ (A.toEuclideanLin x) x| ≤ u) :
    matrixOperatorNorm A ≤ u / (1 - 2 * ε) := by
  let M := matrixOperatorNorm A
  have hM_nonneg : 0 ≤ M := norm_nonneg _
  have hden : 0 < 1 - 2 * ε := by linarith
  have hstep : M ≤ u + 2 * ε * M := by
    unfold M
    refine matrixOperatorNorm_le_of_forall_unit_abs_quadratic_le A hA_symm
      (add_nonneg hu (mul_nonneg (mul_nonneg (by norm_num) hε_nonneg) hM_nonneg)) ?_
    intro x hx
    have hx_sphere : x ∈ euclideanUnitSphere n := by
      simpa [euclideanUnitSphere, dist_eq_norm] using hx
    obtain ⟨x₀, hx₀_mem, hx₀_dist⟩ := N.toMatrixBilinearNet.exists_domain_near hx_sphere
    have hx₀_norm : ‖x₀‖ ≤ 1 :=
      norm_le_one_of_mem_euclideanUnitBall (N.domain_subset_unitBall hx₀_mem)
    have hAx₀x₀ : |inner ℝ (A.toEuclideanLin x₀) x₀| ≤ u :=
      hnet x₀ hx₀_mem
    have hA_dx : ‖A.toEuclideanLin (x - x₀)‖ ≤ M * ‖x - x₀‖ := by
      simpa [M, matrixOperatorNorm] using
        A.toEuclideanLin.toContinuousLinearMap.le_opNorm (x - x₀)
    have hA_x : ‖A.toEuclideanLin x‖ ≤ M * ‖x‖ := by
      simpa [M, matrixOperatorNorm] using A.toEuclideanLin.toContinuousLinearMap.le_opNorm x
    have hterm_x :
        |inner ℝ (A.toEuclideanLin (x - x₀)) x₀| ≤ M * ε := by
      calc
        |inner ℝ (A.toEuclideanLin (x - x₀)) x₀|
            ≤ ‖A.toEuclideanLin (x - x₀)‖ * ‖x₀‖ := abs_real_inner_le_norm _ _
        _ ≤ (M * ‖x - x₀‖) * 1 := by
              exact mul_le_mul hA_dx hx₀_norm (norm_nonneg _)
                (mul_nonneg hM_nonneg (norm_nonneg _))
        _ = M * ‖x - x₀‖ := by ring
        _ ≤ M * ε := mul_le_mul_of_nonneg_left hx₀_dist hM_nonneg
    have hterm_y :
        |inner ℝ (A.toEuclideanLin x) (x - x₀)| ≤ M * ε := by
      calc
        |inner ℝ (A.toEuclideanLin x) (x - x₀)|
            ≤ ‖A.toEuclideanLin x‖ * ‖x - x₀‖ := abs_real_inner_le_norm _ _
        _ ≤ (M * ‖x‖) * ε := by
              exact mul_le_mul hA_x hx₀_dist (norm_nonneg _)
                (mul_nonneg hM_nonneg (norm_nonneg _))
        _ = M * ε := by rw [hx]; ring
    have hdecomp :
        inner ℝ (A.toEuclideanLin x) x =
          inner ℝ (A.toEuclideanLin x₀) x₀ +
            inner ℝ (A.toEuclideanLin (x - x₀)) x₀ +
              inner ℝ (A.toEuclideanLin x) (x - x₀) := by
      have hx_decomp : x₀ + (x - x₀) = x := by abel
      calc
        inner ℝ (A.toEuclideanLin x) x =
            inner ℝ (A.toEuclideanLin x) (x₀ + (x - x₀)) := by rw [hx_decomp]
        _ = inner ℝ (A.toEuclideanLin x) x₀ +
              inner ℝ (A.toEuclideanLin x) (x - x₀) := by rw [inner_add_right]
        _ = inner ℝ (A.toEuclideanLin (x₀ + (x - x₀))) x₀ +
              inner ℝ (A.toEuclideanLin x) (x - x₀) := by rw [hx_decomp]
        _ = inner ℝ (A.toEuclideanLin x₀ + A.toEuclideanLin (x - x₀)) x₀ +
              inner ℝ (A.toEuclideanLin x) (x - x₀) := by rw [map_add]
        _ = inner ℝ (A.toEuclideanLin x₀) x₀ +
              inner ℝ (A.toEuclideanLin (x - x₀)) x₀ +
                inner ℝ (A.toEuclideanLin x) (x - x₀) := by rw [inner_add_left]
    calc
      |inner ℝ (A.toEuclideanLin x) x|
          ≤ |inner ℝ (A.toEuclideanLin x₀) x₀| +
              |inner ℝ (A.toEuclideanLin (x - x₀)) x₀| +
                |inner ℝ (A.toEuclideanLin x) (x - x₀)| := by
            rw [hdecomp]
            have h₁ := abs_add_le
              (inner ℝ (A.toEuclideanLin x₀) x₀ +
                inner ℝ (A.toEuclideanLin (x - x₀)) x₀)
              (inner ℝ (A.toEuclideanLin x) (x - x₀))
            have h₂ := abs_add_le (inner ℝ (A.toEuclideanLin x₀) x₀)
              (inner ℝ (A.toEuclideanLin (x - x₀)) x₀)
            linarith
      _ ≤ u + M * ε + M * ε := by linarith
      _ = u + 2 * ε * M := by ring
  have hmul' : M * (1 - 2 * ε) ≤ u := by nlinarith
  exact (le_div_iff₀ hden).mpr (by simpa [M] using hmul')

/-- The standard `ε = 1/4` symmetric matrix-net reduction used in HDP Corollary 4.4.7. -/
lemma matrixOperatorNorm_le_two_mul_of_quarter_centered_quadratic_net {n : ℕ} {u : ℝ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA_symm : A.IsSymm)
    (N : CenteredMatrixBilinearNet n n (1 / 4)) (hu : 0 ≤ u)
    (hnet : ∀ x ∈ N.domainNet, |inner ℝ (A.toEuclideanLin x) x| ≤ u) :
    matrixOperatorNorm A ≤ 2 * u := by
  have h :=
    matrixOperatorNorm_le_of_centered_quadratic_net (A := A) (hA_symm := hA_symm) (N := N)
      (by norm_num : 0 ≤ (1 / 4 : ℝ)) (by norm_num : 2 * (1 / 4 : ℝ) < 1) hu hnet
  calc
    matrixOperatorNorm A ≤ u / (1 - 2 * (1 / 4 : ℝ)) := h
    _ = 2 * u := by ring

omit [MeasurableSpace Ω] in
lemma sampleCovarianceDeviationOperatorNorm_le_two_mul_of_quarter_centered_quadratic_net
    {m n : ℕ} {u : ℝ}
    (A : Matrix (Fin m) (Fin n) ℝ) (N : CenteredMatrixBilinearNet n n (1 / 4))
    (hu : 0 ≤ u)
    (hnet : ∀ x ∈ N.domainNet,
      |(m : ℝ)⁻¹ * ‖A.toEuclideanLin x‖ ^ 2 - ‖x‖ ^ 2| ≤ u) :
    sampleCovarianceDeviationOperatorNorm A ≤ 2 * u := by
  unfold sampleCovarianceDeviationOperatorNorm
  refine matrixOperatorNorm_le_two_mul_of_quarter_centered_quadratic_net
    (sampleCovarianceDeviation A) (sampleCovarianceDeviation_isSymm A) N hu ?_
  intro x hx
  rw [inner_sampleCovarianceDeviation_toEuclideanLin]
  exact hnet x hx

omit [MeasurableSpace Ω] in
lemma sampleCovarianceDeviationOperatorNorm_event_subset_quarter_centered_quadratic_net
    {m n : ℕ} {A : Fin m → Fin n → Ω → ℝ} {u : ℝ}
    (N : CenteredMatrixBilinearNet n n (1 / 4)) (hu : 0 ≤ u) :
    {ω | 2 * u < sampleCovarianceDeviationOperatorNorm (randomMatrix A ω)} ⊆
      ⋃ x ∈ N.domainNet,
        {ω |
          u < |(m : ℝ)⁻¹ * ‖(randomMatrix A ω).toEuclideanLin x‖ ^ 2 - ‖x‖ ^ 2|} := by
  intro ω hω
  by_contra hω_union
  have hnet : ∀ x ∈ N.domainNet,
      |(m : ℝ)⁻¹ * ‖(randomMatrix A ω).toEuclideanLin x‖ ^ 2 - ‖x‖ ^ 2| ≤ u := by
    intro x hx
    have hnot_x :
        ω ∉ {ω |
          u < |(m : ℝ)⁻¹ * ‖(randomMatrix A ω).toEuclideanLin x‖ ^ 2 - ‖x‖ ^ 2|} := by
      intro hmem
      exact hω_union (Set.mem_iUnion₂.mpr ⟨x, hx, hmem⟩)
    exact le_of_not_gt (by simpa using hnot_x)
  have hnorm :
      sampleCovarianceDeviationOperatorNorm (randomMatrix A ω) ≤ 2 * u :=
    sampleCovarianceDeviationOperatorNorm_le_two_mul_of_quarter_centered_quadratic_net
      (randomMatrix A ω) N hu hnet
  exact (not_le_of_gt hω) hnorm

/-! ## Entrywise sub-Gaussian scales -/

/-- A positive vector ψ₂/MGF scale: every one-dimensional unit projection is sub-Gaussian. -/
def HasSubGaussianVectorPsi2Bound {n : ℕ} (X : Ω → EuclideanSpace ℝ (Fin n))
    (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 →
      HasSubgaussianMGF (fun ω => inner ℝ (X ω) x) ⟨K ^ 2, sq_nonneg K⟩ μ

/-- The HDP vector ψ₂ scale, defined as the infimum over admissible projection scales. -/
def subGaussianVectorPsi2Norm {n : ℕ} (X : Ω → EuclideanSpace ℝ (Fin n))
    (μ : Measure Ω) : ℝ :=
  sInf {K : ℝ | HasSubGaussianVectorPsi2Bound X μ K}

/-- Finiteness of the vector ψ₂ scale. -/
def HasFiniteSubGaussianVectorPsi2Norm {n : ℕ} (X : Ω → EuclideanSpace ℝ (Fin n))
    (μ : Measure Ω) : Prop :=
  ∃ K : ℝ, HasSubGaussianVectorPsi2Bound X μ K

lemma subGaussianVectorPsi2Norm_nonneg {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)} {μ : Measure Ω}
    (hfin : HasFiniteSubGaussianVectorPsi2Norm X μ) :
    0 ≤ subGaussianVectorPsi2Norm X μ := by
  exact le_csInf hfin fun K hK => hK.1.le

lemma exists_hasSubGaussianVectorPsi2Bound_lt {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)} {μ : Measure Ω} {R : ℝ}
    (hfin : HasFiniteSubGaussianVectorPsi2Norm X μ)
    (hR : subGaussianVectorPsi2Norm X μ < R) :
    ∃ K : ℝ, HasSubGaussianVectorPsi2Bound X μ K ∧ K < R := by
  let S : Set ℝ := {K : ℝ | HasSubGaussianVectorPsi2Bound X μ K}
  have hne : S.Nonempty := hfin
  by_contra h
  push Not at h
  have hR_le : R ≤ sInf S := le_csInf hne fun K hK => h K hK
  exact not_lt_of_ge hR_le (by simpa [subGaussianVectorPsi2Norm, S] using hR)

lemma hasSubgaussianMGF_inner_of_subGaussianVectorPsi2Norm_lt {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)} {μ : Measure Ω} {R : ℝ}
    (hfin : HasFiniteSubGaussianVectorPsi2Norm X μ)
    (hR : subGaussianVectorPsi2Norm X μ < R)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ = 1) :
    HasSubgaussianMGF (fun ω => inner ℝ (X ω) x) ⟨R ^ 2, sq_nonneg R⟩ μ := by
  obtain ⟨K, hK, hKR⟩ := exists_hasSubGaussianVectorPsi2Bound_lt hfin hR
  have hRpos : 0 < R := lt_trans hK.1 hKR
  have hsq : K ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ hK.1.le hRpos.le).2 hKR.le
  exact hasSubgaussianMGF_mono_param (hK.2 x hx) (by
    change K ^ 2 ≤ R ^ 2
    exact hsq)

lemma hasSubgaussianMGF_inner_of_subGaussianVectorPsi2Norm_le {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)} {μ : Measure Ω} {R : ℝ}
    (hfin : HasFiniteSubGaussianVectorPsi2Norm X μ)
    (hR : subGaussianVectorPsi2Norm X μ ≤ R)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ = 1) :
    HasSubgaussianMGF (fun ω => inner ℝ (X ω) x) ⟨R ^ 2, sq_nonneg R⟩ μ where
  integrable_exp_mul t := by
    have hnorm_nonneg : 0 ≤ subGaussianVectorPsi2Norm X μ :=
      subGaussianVectorPsi2Norm_nonneg hfin
    have hlt : subGaussianVectorPsi2Norm X μ < R + 1 := by linarith
    exact (hasSubgaussianMGF_inner_of_subGaussianVectorPsi2Norm_lt hfin hlt hx).integrable_exp_mul t
  mgf_le t := by
    have hlim_const :
        Tendsto (fun _ : ℝ => mgf (fun ω => inner ℝ (X ω) x) μ t)
          (𝓝[>] (0 : ℝ)) (𝓝 (mgf (fun ω => inner ℝ (X ω) x) μ t)) :=
      tendsto_const_nhds
    have hlim_bound :
        Tendsto
          (fun ε : ℝ =>
            exp ((((⟨(R + ε) ^ 2, sq_nonneg (R + ε)⟩ : ℝ≥0) : ℝ) * t ^ 2) / 2))
          (𝓝[>] (0 : ℝ))
          (𝓝 (exp ((((⟨R ^ 2, sq_nonneg R⟩ : ℝ≥0) : ℝ) * t ^ 2) / 2))) := by
      have hcont :
          ContinuousAt (fun ε : ℝ => exp (((R + ε) ^ 2) * t ^ 2 / 2)) 0 := by
        fun_prop
      simpa only [NNReal.coe_mk, add_zero] using hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hev :
        (fun _ : ℝ => mgf (fun ω => inner ℝ (X ω) x) μ t) ≤ᶠ[𝓝[>] (0 : ℝ)]
          fun ε =>
            exp ((((⟨(R + ε) ^ 2, sq_nonneg (R + ε)⟩ : ℝ≥0) : ℝ) * t ^ 2) / 2) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hεpos : 0 < ε := by simpa using hε
      have hlt : subGaussianVectorPsi2Norm X μ < R + ε := by linarith
      exact (hasSubgaussianMGF_inner_of_subGaussianVectorPsi2Norm_lt hfin hlt hx).mgf_le t
    exact le_of_tendsto_of_tendsto hlim_const hlim_bound hev

/-- The random `i`-th row of a scalar random matrix as a Euclidean vector. -/
def randomMatrixRowVector {m n : ℕ} (A : Fin m → Fin n → Ω → ℝ) (i : Fin m) :
    Ω → EuclideanSpace ℝ (Fin n) :=
  fun ω => matrixRowVector (randomMatrix A ω) i

/-- Maximum vector ψ₂ scale of the rows of a random matrix. It is `0` for no rows. -/
def maxMatrixRowSubGaussianPsi2Norm {m n : ℕ}
    (A : Fin m → Fin n → Ω → ℝ) (μ : Measure Ω) : ℝ := by
  classical
  exact if h : (Finset.univ : Finset (Fin m)).Nonempty then
    (Finset.univ : Finset (Fin m)).sup' h fun i =>
      subGaussianVectorPsi2Norm (randomMatrixRowVector A i) μ
  else 0

lemma subGaussianVectorPsi2Norm_le_maxMatrixRowSubGaussianPsi2Norm {m n : ℕ}
    (A : Fin m → Fin n → Ω → ℝ) (μ : Measure Ω) (i : Fin m) :
    subGaussianVectorPsi2Norm (randomMatrixRowVector A i) μ ≤
      maxMatrixRowSubGaussianPsi2Norm A μ := by
  classical
  unfold maxMatrixRowSubGaussianPsi2Norm
  rw [dite_eq_left (show (Finset.univ : Finset (Fin m)).Nonempty from ⟨i, Finset.mem_univ i⟩)]
  exact Finset.le_sup'
    (f := fun i => subGaussianVectorPsi2Norm (randomMatrixRowVector A i) μ)
    (Finset.mem_univ i)

lemma row_inner_hasSubgaussianMGF_of_max_row_psi2 {m n : ℕ}
    {A : Fin m → Fin n → Ω → ℝ} {μ : Measure Ω} {K : ℝ}
    (hK_def : K = maxMatrixRowSubGaussianPsi2Norm A μ)
    (hfinite : ∀ i, HasFiniteSubGaussianVectorPsi2Norm (randomMatrixRowVector A i) μ)
    (i : Fin m) {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ = 1) :
    HasSubgaussianMGF (fun ω => inner ℝ (randomMatrixRowVector A i ω) x)
      ⟨K ^ 2, sq_nonneg K⟩ μ := by
  have hnorm_le :
      subGaussianVectorPsi2Norm (randomMatrixRowVector A i) μ ≤ K := by
    rw [hK_def]
    exact subGaussianVectorPsi2Norm_le_maxMatrixRowSubGaussianPsi2Norm A μ i
  exact hasSubgaussianMGF_inner_of_subGaussianVectorPsi2Norm_le (hfinite i) hnorm_le hx

/-! ## Fixed bilinear forms of random matrices -/


omit [MeasurableSpace Ω] in
lemma randomVector_norm_sq_eq_sum_sq {n : ℕ} (X : Fin n → Ω → ℝ) (ω : Ω) :
    ‖HansonWright.randomVector X ω‖ ^ 2 = ∑ i, X i ω ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

omit [MeasurableSpace Ω] in
lemma quadraticForm_one_eq_sum_sq {n : ℕ} (x : Fin n → ℝ) :
    HansonWright.quadraticForm (1 : Matrix (Fin n) (Fin n) ℝ) x =
      ∑ i, x i ^ 2 := by
  classical
  unfold HansonWright.quadraticForm
  calc
    ∑ i, ∑ j, (1 : Matrix (Fin n) (Fin n) ℝ) i j * x i * x j
        = ∑ i, (1 : Matrix (Fin n) (Fin n) ℝ) i i * x i * x i := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_eq_single i
            (fun j _ hji => by simp [Matrix.one_apply_ne hji.symm])
            (fun hi => (hi (Finset.mem_univ i)).elim)
    _ = ∑ i, x i ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          simp [pow_two]

omit [MeasurableSpace Ω] in
lemma randomQuadraticForm_one_eq_norm_sq {n : ℕ}
    (X : Fin n → Ω → ℝ) (ω : Ω) :
    HansonWright.randomQuadraticForm (1 : Matrix (Fin n) (Fin n) ℝ) X ω =
      ‖HansonWright.randomVector X ω‖ ^ 2 := by
  rw [HansonWright.randomQuadraticForm, quadraticForm_one_eq_sum_sq,
    randomVector_norm_sq_eq_sum_sq]

omit [MeasurableSpace Ω] in
lemma frobeniusNormSq_one {n : ℕ} :
    HansonWright.frobeniusNormSq (1 : Matrix (Fin n) (Fin n) ℝ) = n := by
  classical
  unfold HansonWright.frobeniusNormSq
  calc
    ∑ i, ∑ j, ((1 : Matrix (Fin n) (Fin n) ℝ) i j) ^ 2
        = ∑ i, ((1 : Matrix (Fin n) (Fin n) ℝ) i i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_eq_single i
            (fun j _ hji => by simp [Matrix.one_apply_ne hji.symm])
            (fun hi => (hi (Finset.mem_univ i)).elim)
    _ = ∑ _i : Fin n, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro i _
          simp
    _ = n := by simp

omit [MeasurableSpace Ω] in
lemma frobeniusNorm_one_sq {n : ℕ} :
    HansonWright.frobeniusNorm (1 : Matrix (Fin n) (Fin n) ℝ) ^ 2 = n := by
  rw [HansonWright.frobeniusNorm_sq, frobeniusNormSq_one]

omit [MeasurableSpace Ω] in
lemma toEuclideanCLM_one {n : ℕ} :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  ext x i
  simp

omit [MeasurableSpace Ω] in
lemma operatorNorm_one_le {n : ℕ} :
    HansonWright.operatorNorm (1 : Matrix (Fin n) (Fin n) ℝ) ≤ 1 := by
  unfold HansonWright.operatorNorm
  rw [toEuclideanCLM_one]
  exact ContinuousLinearMap.norm_id_le

omit [MeasurableSpace Ω] in
lemma operatorNorm_one_pos_of_pos {n : ℕ} (hn : 0 < n) :
    0 < HansonWright.operatorNorm (1 : Matrix (Fin n) (Fin n) ℝ) := by
  unfold HansonWright.operatorNorm
  let i : Fin n := ⟨0, hn⟩
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  have happly :
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
          (1 : Matrix (Fin n) (Fin n) ℝ) e = e := by
    rw [toEuclideanCLM_one]
    rfl
  have hle :=
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (1 : Matrix (Fin n) (Fin n) ℝ)).le_opNorm e
  rw [happly, he, mul_one] at hle
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hle

omit [MeasurableSpace Ω] in
lemma one_le_operatorNorm_one_of_pos {n : ℕ} (hn : 0 < n) :
    1 ≤ HansonWright.operatorNorm (1 : Matrix (Fin n) (Fin n) ℝ) := by
  unfold HansonWright.operatorNorm
  let i : Fin n := ⟨0, hn⟩
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  have happly :
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
          (1 : Matrix (Fin n) (Fin n) ℝ) e = e := by
    rw [toEuclideanCLM_one]
    rfl
  have hle :=
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (1 : Matrix (Fin n) (Fin n) ℝ)).le_opNorm e
  rw [happly, he, mul_one] at hle
  exact hle

omit [MeasurableSpace Ω] in
lemma operatorNorm_one_eq_of_pos {n : ℕ} (hn : 0 < n) :
    HansonWright.operatorNorm (1 : Matrix (Fin n) (Fin n) ℝ) = 1 :=
  le_antisymm operatorNorm_one_le (one_le_operatorNorm_one_of_pos hn)

omit [MeasurableSpace Ω] in
/-- A fixed explicit Hanson-Wright constant large enough for the local estimates used here. -/
def hdpHansonWrightConstant : ℝ :=
  64 * exp 1 ^ 2

omit [MeasurableSpace Ω] in
lemma hdpHansonWrightConstant_pos :
    0 < hdpHansonWrightConstant := by
  unfold hdpHansonWrightConstant
  positivity

omit [MeasurableSpace Ω] in
lemma hdpHansonWrightConstant_domain :
    4 * exp 1 ≤ hdpHansonWrightConstant := by
  unfold hdpHansonWrightConstant
  have hexp_ge_one : 1 ≤ exp 1 := one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
  have hmul := mul_le_mul_of_nonneg_left hexp_ge_one
    (by positivity : 0 ≤ 4 * exp 1)
  nlinarith

omit [MeasurableSpace Ω] in
lemma hdpHansonWrightConstant_diag_quad :
    8 * exp 1 ^ 3 ≤ hdpHansonWrightConstant := by
  unfold hdpHansonWrightConstant
  have hexp_le_eight : exp 1 ≤ 8 := by
    nlinarith [exp_one_lt_three.le]
  have hmul := mul_le_mul_of_nonneg_left hexp_le_eight
    (by positivity : 0 ≤ 8 * exp 1 ^ 2)
  nlinarith

omit [MeasurableSpace Ω] in
lemma hdpHansonWrightConstant_offdiag_domain :
    16 * exp 1 ≤ hdpHansonWrightConstant ^ 2 := by
  have hC_pos : 0 < hdpHansonWrightConstant := hdpHansonWrightConstant_pos
  have hexp_ge_one : 1 ≤ exp 1 := one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
  have hC_ge_sixteen : 16 * exp 1 ≤ hdpHansonWrightConstant := by
    unfold hdpHansonWrightConstant
    have hmul := mul_le_mul_of_nonneg_left hexp_ge_one
      (by positivity : 0 ≤ 16 * exp 1)
    nlinarith
  have hC_ge_one : 1 ≤ hdpHansonWrightConstant := by
    unfold hdpHansonWrightConstant
    nlinarith [hexp_ge_one, sq_nonneg (exp 1)]
  have hC_sq_ge : hdpHansonWrightConstant ≤ hdpHansonWrightConstant ^ 2 := by
    have hmul := mul_le_mul hC_ge_one (le_refl hdpHansonWrightConstant)
      hC_pos.le hC_pos.le
    simpa [pow_two] using hmul
  exact hC_ge_sixteen.trans hC_sq_ge

omit [MeasurableSpace Ω] in
lemma hdpHansonWrightConstant_offdiag_quad :
    64 * exp 1 ^ 2 ≤ hdpHansonWrightConstant := by
  rfl

/-! ## HDP entry hypotheses -/

/--
Row hypotheses in HDP Theorem 4.6.1: independent, mean-zero, sub-Gaussian, isotropic rows.

The random row `Aᵢ` is represented by `randomMatrixRowVector A i`. Isotropy is stated in
the one-dimensional marginal form `E ⟪Aᵢ, x⟫² = ‖x‖²`.
-/
structure HasIndependentMeanZeroIsotropicSubGaussianRows {m n : ℕ}
    (A : Fin m → Fin n → Ω → ℝ) (μ : Measure Ω) : Prop where
  measurable : ∀ i j, Measurable (A i j)
  independent_rows : iIndepFun (fun i : Fin m => randomMatrixRowVector A i) μ
  mean_zero : ∀ i (x : EuclideanSpace ℝ (Fin n)),
    ∫ ω, inner ℝ (randomMatrixRowVector A i ω) x ∂μ = 0
  isotropic : ∀ i (x : EuclideanSpace ℝ (Fin n)),
    ∫ ω, (inner ℝ (randomMatrixRowVector A i ω) x) ^ 2 ∂μ = ‖x‖ ^ 2
  finite_row_psi2 : ∀ i, HasFiniteSubGaussianVectorPsi2Norm (randomMatrixRowVector A i) μ

omit [MeasurableSpace Ω] in
lemma randomVector_rowProjection_eq_toEuclideanLin {m n : ℕ}
    (A : Fin m → Fin n → Ω → ℝ) (ω : Ω) (x : EuclideanSpace ℝ (Fin n)) :
    HansonWright.randomVector
        (fun i : Fin m => fun ω => inner ℝ (randomMatrixRowVector A i ω) x) ω =
      (randomMatrix A ω).toEuclideanLin x := by
  ext i
  change inner ℝ (WithLp.toLp 2 fun j => A i j ω) x =
    (WithLp.toLp 2 ((randomMatrix A ω).mulVec x.ofLp)) i
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, Matrix.mulVec, dotProduct, randomMatrix_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma HasIndependentMeanZeroIsotropicSubGaussianRows.row_projection_iIndepFun {m n : ℕ}
    {A : Fin m → Fin n → Ω → ℝ} {μ : Measure Ω}
    (hA : HasIndependentMeanZeroIsotropicSubGaussianRows A μ)
    (x : EuclideanSpace ℝ (Fin n)) :
    iIndepFun (fun i : Fin m => fun ω => inner ℝ (randomMatrixRowVector A i ω) x) μ := by
  simpa [Function.comp_def] using
    hA.independent_rows.comp (fun _ v => inner ℝ v x) (fun _ => by fun_prop)

lemma HasIndependentMeanZeroIsotropicSubGaussianRows.row_projection_second_moment_one
    {m n : ℕ} {A : Fin m → Fin n → Ω → ℝ} {μ : Measure Ω}
    (hA : HasIndependentMeanZeroIsotropicSubGaussianRows A μ)
    (i : Fin m) {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ = 1) :
    ∫ ω, (inner ℝ (randomMatrixRowVector A i ω) x) ^ 2 ∂μ = 1 := by
  simpa [hx] using hA.isotropic i x

lemma probability_compl_real_ge_one_sub {μ : Measure Ω} [IsProbabilityMeasure μ]
    (s : Set Ω) :
    1 - (μ s).toReal ≤ (μ sᶜ).toReal := by
  classical
  have hmeasure :
      μ Set.univ ≤ μ s + μ sᶜ := by
    calc
      μ Set.univ = μ (s ∪ sᶜ) := by rw [Set.union_compl_self]
      _ ≤ μ s + μ sᶜ := measure_union_le s sᶜ
  have hfinite : μ s + μ sᶜ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top μ s, measure_ne_top μ sᶜ⟩
  have hreal := ENNReal.toReal_mono hfinite hmeasure
  rw [IsProbabilityMeasure.measure_univ, ENNReal.toReal_one] at hreal
  rw [ENNReal.toReal_add (measure_ne_top μ s) (measure_ne_top μ sᶜ)] at hreal
  linarith

lemma probability_le_of_tail_real_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {B δ : ℝ}
    (htail : (μ {ω | B < X ω}).toReal ≤ δ) :
    (μ {ω | X ω ≤ B}).toReal ≥ 1 - δ := by
  have hcompl := probability_compl_real_ge_one_sub (μ := μ) {ω | B < X ω}
  have hset : {ω | B < X ω}ᶜ = {ω | X ω ≤ B} := by
    ext ω
    simp [not_lt]
  rw [hset] at hcompl
  linarith

lemma integral_randomQuadraticForm_one_eq_nat {μ : Measure Ω}
    {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX_sq_int : ∀ i, Integrable (fun ω => X i ω ^ 2) μ)
    (hsecond : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1) :
    ∫ ω, HansonWright.randomQuadraticForm (1 : Matrix (Fin n) (Fin n) ℝ) X ω ∂μ =
      (n : ℝ) := by
  have hfun :
      (fun ω => HansonWright.randomQuadraticForm (1 : Matrix (Fin n) (Fin n) ℝ) X ω) =
        fun ω => ∑ i, X i ω ^ 2 := by
    funext ω
    rw [HansonWright.randomQuadraticForm, quadraticForm_one_eq_sum_sq]
  rw [hfun]
  calc
    ∫ ω, ∑ i, X i ω ^ 2 ∂μ = ∑ i, ∫ ω, X i ω ^ 2 ∂μ := by
      rw [integral_finsetSum]
      intro i _
      exact hX_sq_int i
    _ = ∑ _i : Fin n, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hsecond i
    _ = (n : ℝ) := by simp

lemma centeredQuadraticForm_one_eq_norm_sq_sub_nat {μ : Measure Ω}
    {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX_sq_int : ∀ i, Integrable (fun ω => X i ω ^ 2) μ)
    (hsecond : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1) (ω : Ω) :
    HansonWright.centeredQuadraticForm μ (1 : Matrix (Fin n) (Fin n) ℝ) X ω =
      ‖HansonWright.randomVector X ω‖ ^ 2 - (n : ℝ) := by
  unfold HansonWright.centeredQuadraticForm
  rw [integral_randomQuadraticForm_one_eq_nat hX_sq_int hsecond,
    randomQuadraticForm_one_eq_norm_sq]

lemma one_div_four_exp_sq_le_sq_of_subgaussian_second_moment_one
    {μ : Measure Ω} {X : Ω → ℝ} {K : ℝ}
    (hK : 0 < K)
    (hX_subG : HasSubgaussianMGF X ⟨(2 * K) ^ 2, sq_nonneg (2 * K)⟩ μ)
    (hsecond : ∫ ω, X ω ^ 2 ∂μ = 1) :
    1 / (4 * exp 1 ^ 2) ≤ K ^ 2 := by
  have hCpos : 0 < (2 * K) ^ 2 := by positivity
  have hsq_le :=
    HansonWright.integral_sq_le_of_hasSubgaussianMGF_of_le
      (μ := μ) hX_subG (C0 := (2 * K) ^ 2) hCpos (by rfl)
  have hone_le : 1 ≤ exp 1 * ((2 * K) ^ 2 * exp 1) := by
    calc
      1 = ∫ ω, X ω ^ 2 ∂μ := hsecond.symm
      _ ≤ exp 1 * ((2 * K) ^ 2 * exp 1) := hsq_le
  have hone_le' : 1 ≤ 4 * exp 1 ^ 2 * K ^ 2 := by
    calc
      1 ≤ exp 1 * ((2 * K) ^ 2 * exp 1) := hone_le
      _ = 4 * exp 1 ^ 2 * K ^ 2 := by ring
  have hden_pos : 0 < 4 * exp 1 ^ 2 := by positivity
  have hone_le'' : 1 ≤ K ^ 2 * (4 * exp 1 ^ 2) := by
    nlinarith
  exact (div_le_iff₀ hden_pos).mpr hone_le''

lemma HasIndependentMeanZeroIsotropicSubGaussianRows.max_row_psi2_sq_lower
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {A : Fin m → Fin n → Ω → ℝ} {μ : Measure Ω}
    (hA : HasIndependentMeanZeroIsotropicSubGaussianRows A μ)
    {K : ℝ} (hK_def : K = maxMatrixRowSubGaussianPsi2Norm A μ) (hK : 0 < K) :
    1 / (4 * exp 1 ^ 2) ≤ K ^ 2 := by
  let i0 : Fin m := ⟨0, hm⟩
  let j0 : Fin n := ⟨0, hn⟩
  let x : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j0 (1 : ℝ)
  have hx : ‖x‖ = 1 := by
    simp [x]
  have hbase :
      HasSubgaussianMGF (fun ω => inner ℝ (randomMatrixRowVector A i0 ω) x)
        ⟨K ^ 2, sq_nonneg K⟩ μ :=
    row_inner_hasSubgaussianMGF_of_max_row_psi2
      (A := A) (μ := μ) hK_def hA.finite_row_psi2 i0 hx
  have hsubG :
      HasSubgaussianMGF (fun ω => inner ℝ (randomMatrixRowVector A i0 ω) x)
        ⟨(2 * K) ^ 2, sq_nonneg (2 * K)⟩ μ := by
    refine hasSubgaussianMGF_mono_param hbase ?_
    change K ^ 2 ≤ (2 * K) ^ 2
    nlinarith [sq_nonneg K]
  exact one_div_four_exp_sq_le_sq_of_subgaussian_second_moment_one hK hsubG
    (hA.row_projection_second_moment_one i0 hx)

theorem fixed_unit_vector_matrix_apply_sq_sub_dim_tail_of_row_subgaussian {m n : ℕ}
    (hm : 0 < m) {A : Fin m → Fin n → Ω → ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (hA : HasIndependentMeanZeroIsotropicSubGaussianRows A μ)
    {K u : ℝ} (hK_def : K = maxMatrixRowSubGaussianPsi2Norm A μ)
    (hK : 0 < K) (hu : 0 ≤ u)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ = 1) :
    (μ {ω | u ≤ |‖(randomMatrix A ω).toEuclideanLin x‖ ^ 2 - (m : ℝ)|}).toReal ≤
      2 * exp (-(1 / (4 * hdpHansonWrightConstant)) *
        min (u ^ 2 /
          (K ^ 4 * HansonWright.frobeniusNorm (1 : Matrix (Fin m) (Fin m) ℝ) ^ 2))
          (u / (K ^ 2 * HansonWright.operatorNorm (1 : Matrix (Fin m) (Fin m) ℝ)))) := by
  let X : Fin m → Ω → ℝ :=
    fun i => fun ω => inner ℝ (randomMatrixRowVector A i ω) x
  have h_indep : iIndepFun X μ := by
    dsimp [X]
    exact hA.row_projection_iIndepFun x
  have hX_subG :
      ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ := by
    intro i
    dsimp [X]
    exact row_inner_hasSubgaussianMGF_of_max_row_psi2
      (A := A) (μ := μ) hK_def hA.finite_row_psi2 i hx
  have hX_sq_int : ∀ i, Integrable (fun ω => X i ω ^ 2) μ := by
    intro i
    exact integrable_pow_of_integrable_exp_mul
      (X := X i) (t := 1) one_ne_zero
      (by simpa using (hX_subG i).integrable_exp_mul 1)
      (by simpa using (hX_subG i).integrable_exp_mul (-1)) 2
  have hsecond : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1 := by
    intro i
    dsimp [X]
    exact hA.row_projection_second_moment_one i hx
  have hF_pos : 0 <
      HansonWright.frobeniusNorm (1 : Matrix (Fin m) (Fin m) ℝ) := by
    have hsq := frobeniusNorm_one_sq (n := m)
    have hmR_pos : 0 < (m : ℝ) := by exact_mod_cast hm
    have hnonneg :=
      HansonWright.frobeniusNorm_nonneg (1 : Matrix (Fin m) (Fin m) ℝ)
    nlinarith
  have hOp_pos : 0 < HansonWright.operatorNorm (1 : Matrix (Fin m) (Fin m) ℝ) :=
    operatorNorm_one_pos_of_pos hm
  have htail :=
    HansonWright.hanson_wright_inequality (μ := μ)
      (A := (1 : Matrix (Fin m) (Fin m) ℝ)) (X := X)
      (K := K) (C := hdpHansonWrightConstant) (t := u)
      hK hdpHansonWrightConstant_pos hdpHansonWrightConstant_domain
      hdpHansonWrightConstant_diag_quad hdpHansonWrightConstant_offdiag_domain
      hdpHansonWrightConstant_offdiag_quad hF_pos hOp_pos h_indep hX_subG hu
  have hcenter_eq : ∀ ω,
      HansonWright.centeredQuadraticForm μ (1 : Matrix (Fin m) (Fin m) ℝ) X ω =
        ‖(randomMatrix A ω).toEuclideanLin x‖ ^ 2 - (m : ℝ) := by
    intro ω
    calc
      HansonWright.centeredQuadraticForm μ (1 : Matrix (Fin m) (Fin m) ℝ) X ω
          = ‖HansonWright.randomVector X ω‖ ^ 2 - (m : ℝ) := by
              exact centeredQuadraticForm_one_eq_norm_sq_sub_nat hX_sq_int hsecond ω
      _ = ‖(randomMatrix A ω).toEuclideanLin x‖ ^ 2 - (m : ℝ) := by
              rw [show HansonWright.randomVector X ω =
                (randomMatrix A ω).toEuclideanLin x by
                  dsimp [X]
                  exact randomVector_rowProjection_eq_toEuclideanLin A ω x]
  have hset :
      {ω | u ≤ |HansonWright.centeredQuadraticForm μ
          (1 : Matrix (Fin m) (Fin m) ℝ) X ω|} =
        {ω | u ≤ |‖(randomMatrix A ω).toEuclideanLin x‖ ^ 2 - (m : ℝ)|} := by
    ext ω
    simp [hcenter_eq ω]
  rw [← hset]
  exact htail

theorem fixed_unit_vector_matrix_apply_sq_sub_dim_tail_hdp {m n : ℕ}
    (hm : 0 < m) {A : Fin m → Fin n → Ω → ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (hA : HasIndependentMeanZeroIsotropicSubGaussianRows A μ)
    {K u : ℝ} (hK_def : K = maxMatrixRowSubGaussianPsi2Norm A μ)
    (hK : 0 < K) (hu : 0 ≤ u)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ = 1) :
    (μ {ω | u ≤ |‖(randomMatrix A ω).toEuclideanLin x‖ ^ 2 - (m : ℝ)|}).toReal ≤
      2 * exp (-(1 / (4 * hdpHansonWrightConstant)) *
        min (u ^ 2 / (K ^ 4 * (m : ℝ))) (u / K ^ 2)) := by
  have htail :=
    fixed_unit_vector_matrix_apply_sq_sub_dim_tail_of_row_subgaussian
      (m := m) (n := n) hm (A := A) (μ := μ) hA hK_def hK hu hx
  simpa [frobeniusNorm_one_sq (n := m), operatorNorm_one_eq_of_pos hm] using htail

theorem fixed_vector_matrix_apply_sq_sub_scaled_dim_tail_hdp {m n : ℕ}
    (hm : 0 < m) {A : Fin m → Fin n → Ω → ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (hA : HasIndependentMeanZeroIsotropicSubGaussianRows A μ)
    {K u : ℝ} (hK_def : K = maxMatrixRowSubGaussianPsi2Norm A μ)
    (hK : 0 < K) (hu : 0 < u)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ 1) :
    (μ {ω |
      u ≤ |‖(randomMatrix A ω).toEuclideanLin x‖ ^ 2 - (m : ℝ) * ‖x‖ ^ 2|}).toReal ≤
      2 * exp (-(1 / (4 * hdpHansonWrightConstant)) *
        min (u ^ 2 / (K ^ 4 * (m : ℝ))) (u / K ^ 2)) := by
  by_cases hx0 : x = 0
  · have hset :
        {ω : Ω |
          u ≤ |‖(randomMatrix A ω).toEuclideanLin x‖ ^ 2 - (m : ℝ) * ‖x‖ ^ 2|} =
          ∅ := by
      ext ω
      simp [hx0, not_le_of_gt hu]
    rw [hset, measure_empty, ENNReal.toReal_zero]
    positivity
  · let r : ℝ := ‖x‖
    let y : EuclideanSpace ℝ (Fin n) := r⁻¹ • x
    have hr_pos : 0 < r := by
      dsimp [r]
      exact norm_pos_iff.mpr hx0
    have hy : ‖y‖ = 1 := by
      dsimp [y]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr_pos.le)]
      exact inv_mul_cancel₀ hr_pos.ne'
    have hx_eq : x = r • y := by
      dsimp [y]
      rw [smul_smul, mul_inv_cancel₀ hr_pos.ne', one_smul]
    have hr_sq_le_one : r ^ 2 ≤ 1 := by
      dsimp [r]
      nlinarith [norm_nonneg x, hx]
    have hsubset :
        {ω |
          u ≤ |‖(randomMatrix A ω).toEuclideanLin x‖ ^ 2 - (m : ℝ) * ‖x‖ ^ 2|} ⊆
          {ω | u ≤ |‖(randomMatrix A ω).toEuclideanLin y‖ ^ 2 - (m : ℝ)|} := by
      intro ω hω
      let T := (randomMatrix A ω).toEuclideanLin
      have hTx : T x = r • T y := by
        rw [hx_eq, map_smul]
      have hdiff :
          ‖T x‖ ^ 2 - (m : ℝ) * ‖x‖ ^ 2 =
            r ^ 2 * (‖T y‖ ^ 2 - (m : ℝ)) := by
        rw [hTx]
        have hrnorm : ‖(r : ℝ)‖ = r := Real.norm_of_nonneg hr_pos.le
        rw [norm_smul, hrnorm]
        change (r * ‖T y‖) ^ 2 - (m : ℝ) * r ^ 2 =
          r ^ 2 * (‖T y‖ ^ 2 - (m : ℝ))
        ring
      have hdiff_abs :
          |‖T x‖ ^ 2 - (m : ℝ) * ‖x‖ ^ 2| =
            r ^ 2 * |‖T y‖ ^ 2 - (m : ℝ)| := by
        rw [hdiff, abs_mul, abs_of_nonneg (sq_nonneg r)]
      calc
        u ≤ |‖T x‖ ^ 2 - (m : ℝ) * ‖x‖ ^ 2| := hω
        _ = r ^ 2 * |‖T y‖ ^ 2 - (m : ℝ)| := hdiff_abs
        _ ≤ |‖T y‖ ^ 2 - (m : ℝ)| := by
          calc
            r ^ 2 * |‖T y‖ ^ 2 - (m : ℝ)|
                ≤ 1 * |‖T y‖ ^ 2 - (m : ℝ)| :=
                  mul_le_mul_of_nonneg_right hr_sq_le_one (abs_nonneg _)
            _ = |‖T y‖ ^ 2 - (m : ℝ)| := one_mul _
    have htail :=
      fixed_unit_vector_matrix_apply_sq_sub_dim_tail_hdp
        (m := m) (n := n) hm (A := A) (μ := μ) hA hK_def hK hu.le hy
    exact (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsubset)).trans htail

lemma sampleCovarianceDeviationOperatorNorm_tail_of_quarter_centered_quadratic_net
    {m n : ℕ} (hm : 0 < m)
    {A : Fin m → Fin n → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (N : CenteredMatrixBilinearNet n n (1 / 4))
    (hA : HasIndependentMeanZeroIsotropicSubGaussianRows A μ)
    {K u : ℝ} (hK_def : K = maxMatrixRowSubGaussianPsi2Norm A μ)
    (hK : 0 < K) (hu : 0 < u) :
    (μ {ω | 2 * u < sampleCovarianceDeviationOperatorNorm (randomMatrix A ω)}).toReal ≤
      2 * (N.domainNet.card : ℝ) *
        exp (-(1 / (4 * hdpHansonWrightConstant)) *
          min (((m : ℝ) * u) ^ 2 / (K ^ 4 * (m : ℝ))) (((m : ℝ) * u) / K ^ 2)) := by
  let tailEvent : EuclideanSpace ℝ (Fin n) → Set Ω :=
    fun x => {ω |
      (m : ℝ) * u <
        |‖(randomMatrix A ω).toEuclideanLin x‖ ^ 2 - (m : ℝ) * ‖x‖ ^ 2|}
  have hmR_pos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hthreshold_pos : 0 < (m : ℝ) * u := mul_pos hmR_pos hu
  have hsubset :
      {ω | 2 * u < sampleCovarianceDeviationOperatorNorm (randomMatrix A ω)} ⊆
        ⋃ x ∈ N.domainNet, tailEvent x := by
    intro ω hω
    have hdet :=
      sampleCovarianceDeviationOperatorNorm_event_subset_quarter_centered_quadratic_net
        (A := A) (u := u) N hu.le hω
    rcases Set.mem_iUnion₂.mp hdet with ⟨x, hx, hmem⟩
    let a : ℝ := ‖(randomMatrix A ω).toEuclideanLin x‖ ^ 2
    let b : ℝ := ‖x‖ ^ 2
    have hmem' : u < |(m : ℝ)⁻¹ * a - b| := by
      simpa [a, b] using hmem
    have hmul : (m : ℝ) * u < (m : ℝ) * |(m : ℝ)⁻¹ * a - b| :=
      mul_lt_mul_of_pos_left hmem' hmR_pos
    have hscale : (m : ℝ) * |(m : ℝ)⁻¹ * a - b| =
        |a - (m : ℝ) * b| := by
      have hinner :
          (m : ℝ) * ((m : ℝ)⁻¹ * a - b) = a - (m : ℝ) * b := by
        field_simp [hmR_pos.ne']
      have hmul_abs :
          |(m : ℝ) * ((m : ℝ)⁻¹ * a - b)| =
            (m : ℝ) * |(m : ℝ)⁻¹ * a - b| := by
        rw [abs_mul, abs_of_pos hmR_pos]
      rw [← hmul_abs, hinner]
    exact Set.mem_iUnion₂.mpr ⟨x, hx, by
      have : (m : ℝ) * u < |a - (m : ℝ) * b| := by simpa [hscale] using hmul
      simpa [tailEvent, a, b] using this⟩
  have htail_each :
      ∀ x ∈ N.domainNet, μ.real (tailEvent x) ≤
        2 * exp (-(1 / (4 * hdpHansonWrightConstant)) *
          min (((m : ℝ) * u) ^ 2 / (K ^ 4 * (m : ℝ))) (((m : ℝ) * u) / K ^ 2)) := by
    intro x hx
    have hx_norm : ‖x‖ ≤ 1 :=
      norm_le_one_of_mem_euclideanUnitBall (N.domain_subset_unitBall hx)
    have hmono :
        μ.real (tailEvent x) ≤
          (μ {ω |
            (m : ℝ) * u ≤
              |‖(randomMatrix A ω).toEuclideanLin x‖ ^ 2 - (m : ℝ) * ‖x‖ ^ 2|}).toReal := by
      refine ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono ?_)
      intro ω hω
      exact le_of_lt (by simpa [tailEvent] using hω)
    exact hmono.trans
      (fixed_vector_matrix_apply_sq_sub_scaled_dim_tail_hdp
        (m := m) (n := n) hm (A := A) (μ := μ) hA hK_def hK hthreshold_pos hx_norm)
  calc
    (μ {ω | 2 * u < sampleCovarianceDeviationOperatorNorm (randomMatrix A ω)}).toReal
        ≤ μ.real (⋃ x ∈ N.domainNet, tailEvent x) := by
          simpa [Measure.real] using
            ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsubset)
    _ ≤ ∑ x ∈ N.domainNet, μ.real (tailEvent x) :=
          measureReal_biUnion_finset_le N.domainNet tailEvent
    _ ≤ ∑ x ∈ N.domainNet,
          2 * exp (-(1 / (4 * hdpHansonWrightConstant)) *
            min (((m : ℝ) * u) ^ 2 / (K ^ 4 * (m : ℝ))) (((m : ℝ) * u) / K ^ 2)) := by
          exact Finset.sum_le_sum fun x hx => htail_each x hx
    _ = (N.domainNet.card : ℝ) *
          (2 * exp (-(1 / (4 * hdpHansonWrightConstant)) *
            min (((m : ℝ) * u) ^ 2 / (K ^ 4 * (m : ℝ))) (((m : ℝ) * u) / K ^ 2))) := by
          simp [nsmul_eq_mul]
    _ = 2 * (N.domainNet.card : ℝ) *
          exp (-(1 / (4 * hdpHansonWrightConstant)) *
            min (((m : ℝ) * u) ^ 2 / (K ^ 4 * (m : ℝ))) (((m : ℝ) * u) / K ^ 2)) := by
          ring

lemma sampleCovarianceDeviationOperatorNorm_tail_le_of_row_subgaussian
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {A : Fin m → Fin n → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hA : HasIndependentMeanZeroIsotropicSubGaussianRows A μ)
    {K u : ℝ} (hK_def : K = maxMatrixRowSubGaussianPsi2Norm A μ)
    (hK : 0 < K) (hu : 0 < u) :
    (μ {ω | 2 * u < sampleCovarianceDeviationOperatorNorm (randomMatrix A ω)}).toReal ≤
      2 * 17 ^ n *
        exp (-(1 / (4 * hdpHansonWrightConstant)) *
          min (((m : ℝ) * u) ^ 2 / (K ^ 4 * (m : ℝ))) (((m : ℝ) * u) / K ^ 2)) := by
  obtain ⟨N, hN_domain, _hN_codomain⟩ := exists_quarter_centeredMatrixBilinearNet n n
  have htail :=
    sampleCovarianceDeviationOperatorNorm_tail_of_quarter_centered_quadratic_net
      (m := m) (n := n) hm (A := A) (μ := μ) N hA hK_def hK hu
  have hcard :=
    centeredMatrixBilinearNet_domain_card_le_seventeen_pow hn N hN_domain
  have hfactor :
      2 * (N.domainNet.card : ℝ) *
          exp (-(1 / (4 * hdpHansonWrightConstant)) *
            min (((m : ℝ) * u) ^ 2 / (K ^ 4 * (m : ℝ))) (((m : ℝ) * u) / K ^ 2)) ≤
        2 * 17 ^ n *
          exp (-(1 / (4 * hdpHansonWrightConstant)) *
            min (((m : ℝ) * u) ^ 2 / (K ^ 4 * (m : ℝ))) (((m : ℝ) * u) / K ^ 2)) := by
    have hleft : 2 * (N.domainNet.card : ℝ) ≤ 2 * 17 ^ n :=
      mul_le_mul_of_nonneg_left hcard (by norm_num : (0 : ℝ) ≤ 2)
    exact mul_le_mul_of_nonneg_right hleft (le_of_lt (exp_pos _))
  exact htail.trans hfactor

omit [MeasurableSpace Ω] in
lemma seventeen_pow_le_exp_seventeen_mul (d : ℕ) :
    (17 : ℝ) ^ d ≤ exp (17 * (d : ℝ)) := by
  have h17 : (17 : ℝ) ≤ exp 17 := by
    calc
      (17 : ℝ) ≤ 17 + 1 := by norm_num
      _ ≤ exp 17 := by simpa [add_comm] using Real.add_one_le_exp 17
  induction d with
  | zero =>
      simp
  | succ d ih =>
      calc
        (17 : ℝ) ^ (d + 1) = (17 : ℝ) ^ d * 17 := by rw [pow_succ]
        _ ≤ exp (17 * (d : ℝ)) * exp 17 :=
          mul_le_mul ih h17 (by norm_num : (0 : ℝ) ≤ 17) (le_of_lt (exp_pos _))
        _ = exp (17 * (d : ℝ) + 17) := by rw [← exp_add]
        _ = exp (17 * ((d + 1 : ℕ) : ℝ)) := by
          congr 1
          norm_num [Nat.cast_add]
          ring

/-- The covariance-deviation scale used in the HDP row argument. -/
def sampleCovarianceDeviationHdpScale (m n : ℕ) (K t : ℝ) : ℝ :=
  K ^ 2 *
    (√((4 * hdpHansonWrightConstant * (17 * (n : ℝ) + t ^ 2)) / (m : ℝ)) +
      (4 * hdpHansonWrightConstant * (17 * (n : ℝ) + t ^ 2)) / (m : ℝ))

/-- An explicit absolute constant for covariance-deviation estimates. -/
def sampleCovarianceDeviationScaleConstant : ℝ :=
  68 * hdpHansonWrightConstant

/-- An explicit absolute constant for the two-sided singular-value bound. -/
def twoSidedSubgaussianMatricesConstant : ℝ :=
  4 * sampleCovarianceDeviationScaleConstant

omit [MeasurableSpace Ω] in
lemma two_mul_scale_le_max_of_scale_bounds {D C k0 X Y : ℝ}
    (hD_nonneg : 0 ≤ D) (hC_nonneg : 0 ≤ C) (hk0_pos : 0 < k0)
    (hX_nonneg : 0 ≤ X) (hY_nonneg : 0 ≤ Y) (hY_le : Y ≤ X / k0)
    (hC_D : 4 * D ≤ C) (hCk0 : 1 ≤ C * k0) (hC_sq : 4 * D ≤ C ^ 2 * k0) :
    2 * D * X + 2 * D * Y * X ≤ max (C * X) ((C * X) ^ 2) := by
  by_cases hcase : C * X ≤ 1
  · have hCX_nonneg : 0 ≤ C * X := mul_nonneg hC_nonneg hX_nonneg
    have hmax : max (C * X) ((C * X) ^ 2) = C * X := by
      exact max_eq_left (by nlinarith [hCX_nonneg, hcase])
    have hk0Y_le_X : k0 * Y ≤ X := by
      calc
        k0 * Y = Y * k0 := by ring
        _ ≤ X := (le_div_iff₀ hk0_pos).mp hY_le
    have hCk0Y_le_CX : C * k0 * Y ≤ C * X := by
      calc
        C * k0 * Y = C * (k0 * Y) := by ring
        _ ≤ C * X := mul_le_mul_of_nonneg_left hk0Y_le_X hC_nonneg
    have hY_le_one : Y ≤ 1 := by
      calc
        Y ≤ (C * k0) * Y := by
          exact le_mul_of_one_le_left hY_nonneg hCk0
        _ = C * k0 * Y := by ring
        _ ≤ C * X := hCk0Y_le_CX
        _ ≤ 1 := hcase
    rw [hmax]
    have hterm : 2 * D * Y * X ≤ 2 * D * X := by
      have hcoef : 0 ≤ 2 * D * X := by positivity
      calc
        2 * D * Y * X = (2 * D * X) * Y := by ring
        _ ≤ (2 * D * X) * 1 := mul_le_mul_of_nonneg_left hY_le_one hcoef
        _ = 2 * D * X := by ring
    calc
      2 * D * X + 2 * D * Y * X
          ≤ 2 * D * X + 2 * D * X := add_le_add (le_refl (2 * D * X)) hterm
      _ = 4 * D * X := by ring
      _ ≤ C * X := mul_le_mul_of_nonneg_right hC_D hX_nonneg
  · have hcase' : 1 ≤ C * X := le_of_not_ge hcase
    have hCX_nonneg : 0 ≤ C * X := by linarith
    have hmax : max (C * X) ((C * X) ^ 2) = (C * X) ^ 2 := by
      exact max_eq_right (by nlinarith [hCX_nonneg, hcase'])
    rw [hmax]
    have hX_le_CX2 : X ≤ C * X ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hcase' hX_nonneg
      simpa [mul_assoc, pow_two] using hmul
    have hfirst : 2 * D * X ≤ (C ^ 2 / 2) * X ^ 2 := by
      calc
        2 * D * X ≤ 2 * D * (C * X ^ 2) :=
          mul_le_mul_of_nonneg_left hX_le_CX2 (mul_nonneg (by positivity) hD_nonneg)
        _ = (2 * D * C) * X ^ 2 := by ring
        _ ≤ (C ^ 2 / 2) * X ^ 2 := by
          have hcoef : 2 * D * C ≤ C ^ 2 / 2 := by
            nlinarith [hC_D, hC_nonneg]
          exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg X)
    have hYmul_le : Y * X ≤ (X / k0) * X :=
      mul_le_mul_of_nonneg_right hY_le hX_nonneg
    have hcoef_second : 2 * D / k0 ≤ C ^ 2 / 2 := by
      rw [div_le_iff₀ hk0_pos]
      nlinarith [hC_sq]
    have hsecond : 2 * D * Y * X ≤ (C ^ 2 / 2) * X ^ 2 := by
      calc
        2 * D * Y * X = 2 * D * (Y * X) := by ring
        _ ≤ 2 * D * ((X / k0) * X) :=
          mul_le_mul_of_nonneg_left hYmul_le (mul_nonneg (by positivity) hD_nonneg)
        _ = (2 * D / k0) * X ^ 2 := by
          field_simp [hk0_pos.ne']
        _ ≤ (C ^ 2 / 2) * X ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef_second (sq_nonneg X)
    calc
      2 * D * X + 2 * D * Y * X
          ≤ (C ^ 2 / 2) * X ^ 2 + (C ^ 2 / 2) * X ^ 2 :=
            add_le_add hfirst hsecond
      _ = (C * X) ^ 2 := by ring

omit [MeasurableSpace Ω] in
lemma sampleCovarianceDeviationHdpScale_le_max_hdp_radius {m n : ℕ} (hm : 0 < m)
    {K t : ℝ} (hK : 0 < K) (ht : 0 ≤ t)
    (hK_lower : 1 / (4 * exp 1 ^ 2) ≤ K ^ 2) :
    2 * sampleCovarianceDeviationHdpScale m n K t ≤
      max ((twoSidedSubgaussianMatricesConstant * K ^ 2 * (√(n : ℝ) + t)) / √(m : ℝ))
        (((twoSidedSubgaussianMatricesConstant * K ^ 2 * (√(n : ℝ) + t)) /
          √(m : ℝ)) ^ 2) := by
  let C0 : ℝ := hdpHansonWrightConstant
  let D : ℝ := sampleCovarianceDeviationScaleConstant
  let C : ℝ := twoSidedSubgaussianMatricesConstant
  let k0 : ℝ := 1 / (4 * exp 1 ^ 2)
  let S : ℝ := √(n : ℝ) + t
  let Y : ℝ := S / √(m : ℝ)
  let X : ℝ := K ^ 2 * Y
  let q : ℝ := 4 * C0 * (17 * (n : ℝ) + t ^ 2)
  have hmR_pos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hsqrt_m_pos : 0 < √(m : ℝ) := sqrt_pos.mpr hmR_pos
  have hsqrt_m_ne : √(m : ℝ) ≠ 0 := hsqrt_m_pos.ne'
  have hsqrt_m_sq : √(m : ℝ) ^ 2 = (m : ℝ) := sq_sqrt hmR_pos.le
  have hC0_pos : 0 < C0 := by
    dsimp [C0]
    exact hdpHansonWrightConstant_pos
  have hC0_nonneg : 0 ≤ C0 := hC0_pos.le
  have hD_ge_one : 1 ≤ D := by
    dsimp [D, sampleCovarianceDeviationScaleConstant, C0]
    dsimp [hdpHansonWrightConstant]
    nlinarith [one_le_exp (by norm_num : (0 : ℝ) ≤ 1), sq_nonneg (exp 1)]
  have hD_nonneg : 0 ≤ D := le_trans (by norm_num : (0 : ℝ) ≤ 1) hD_ge_one
  have hexp_ge_one : 1 ≤ exp 1 := one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
  have hexp_sq_ge_one : 1 ≤ exp 1 ^ 2 := by
    nlinarith [hexp_ge_one, exp_pos 1]
  have hexp_sq_pos : 0 < exp 1 ^ 2 := by positivity
  have hD_ge_exp_sq : exp 1 ^ 2 ≤ D := by
    dsimp [D, sampleCovarianceDeviationScaleConstant, C0, hdpHansonWrightConstant]
    nlinarith [sq_nonneg (exp 1)]
  have hexp_ne : exp 1 ≠ 0 := (exp_pos 1).ne'
  have hC_nonneg : 0 ≤ C := by
    dsimp [C, twoSidedSubgaussianMatricesConstant]
    positivity
  have hk0_pos : 0 < k0 := by
    dsimp [k0]
    positivity
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    positivity
  have hY_nonneg : 0 ≤ Y := by
    dsimp [Y]
    positivity
  have hX_nonneg : 0 ≤ X := by
    dsimp [X]
    positivity
  have hY_le : Y ≤ X / k0 := by
    have hone_le : 1 ≤ K ^ 2 / k0 := by
      rw [le_div_iff₀ hk0_pos]
      simpa [k0] using hK_lower
    calc
      Y ≤ (K ^ 2 / k0) * Y := le_mul_of_one_le_left hY_nonneg hone_le
      _ = X / k0 := by
        dsimp [X]
        field_simp [hk0_pos.ne']
  have hC_D : 4 * D ≤ C := by
    dsimp [C, twoSidedSubgaussianMatricesConstant]
    linarith
  have hCk0 : 1 ≤ C * k0 := by
    have h_eq : C * k0 = D / exp 1 ^ 2 := by
      dsimp [C, k0, twoSidedSubgaussianMatricesConstant]
      field_simp [hexp_ne]
      ring
    rw [h_eq]
    rw [le_div_iff₀ hexp_sq_pos]
    simpa using hD_ge_exp_sq
  have hC_sq : 4 * D ≤ C ^ 2 * k0 := by
    have h_eq : C ^ 2 * k0 = 4 * D ^ 2 / exp 1 ^ 2 := by
      dsimp [C, k0, twoSidedSubgaussianMatricesConstant]
      field_simp [hexp_ne]
      ring
    rw [h_eq]
    rw [le_div_iff₀ hexp_sq_pos]
    nlinarith [hD_ge_exp_sq, hD_nonneg]
  have hS_sq_base : (n : ℝ) + t ^ 2 ≤ S ^ 2 := by
    have hsqrt_n_sq : √(n : ℝ) ^ 2 = (n : ℝ) :=
      sq_sqrt (Nat.cast_nonneg n)
    have hnt : 0 ≤ 2 * √(n : ℝ) * t := by positivity
    dsimp [S]
    nlinarith [hsqrt_n_sq, hnt]
  have hsum_le : 17 * (n : ℝ) + t ^ 2 ≤ 17 * S ^ 2 := by
    have ht_sq_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
    calc
      17 * (n : ℝ) + t ^ 2 ≤ 17 * ((n : ℝ) + t ^ 2) := by
        nlinarith
      _ ≤ 17 * S ^ 2 := mul_le_mul_of_nonneg_left hS_sq_base (by norm_num)
  have hq_le : q ≤ D * S ^ 2 := by
    have h68_le_D : 68 * C0 ≤ D := by
      dsimp [D, sampleCovarianceDeviationScaleConstant, C0]
      linarith
    calc
      q = 4 * C0 * (17 * (n : ℝ) + t ^ 2) := rfl
      _ ≤ 4 * C0 * (17 * S ^ 2) :=
        mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = 68 * C0 * S ^ 2 := by ring
      _ ≤ D * S ^ 2 := mul_le_mul_of_nonneg_right h68_le_D (sq_nonneg S)
  have hq_nonneg : 0 ≤ q := by
    dsimp [q, C0]
    positivity
  have hq_div_le : q / (m : ℝ) ≤ D * Y ^ 2 := by
    calc
      q / (m : ℝ) ≤ D * S ^ 2 / (m : ℝ) :=
        div_le_div_of_nonneg_right hq_le hmR_pos.le
      _ = D * Y ^ 2 := by
        dsimp [Y]
        field_simp [hsqrt_m_ne]
        rw [hsqrt_m_sq]
  have hsqrt_le : √(q / (m : ℝ)) ≤ D * Y := by
    have hDY_nonneg : 0 ≤ D * Y := mul_nonneg hD_nonneg hY_nonneg
    rw [sqrt_le_left hDY_nonneg]
    calc
      q / (m : ℝ) ≤ D * Y ^ 2 := hq_div_le
      _ ≤ (D * Y) ^ 2 := by
        have hD_le_Dsq : D ≤ D ^ 2 := by
          have hmul := mul_le_mul hD_ge_one (le_refl D) hD_nonneg hD_nonneg
          simpa [pow_two] using hmul
        calc
          D * Y ^ 2 ≤ D ^ 2 * Y ^ 2 :=
            mul_le_mul_of_nonneg_right hD_le_Dsq (sq_nonneg Y)
          _ = (D * Y) ^ 2 := by ring
  have hscale_pre :
      2 * sampleCovarianceDeviationHdpScale m n K t ≤ 2 * D * X + 2 * D * Y * X := by
    have hinner :
        sampleCovarianceDeviationHdpScale m n K t ≤ D * X + D * Y * X := by
      calc
        sampleCovarianceDeviationHdpScale m n K t
            = K ^ 2 * (√(q / (m : ℝ)) + q / (m : ℝ)) := by
              dsimp [sampleCovarianceDeviationHdpScale, q, C0]
        _ ≤ K ^ 2 * (D * Y + D * Y ^ 2) :=
            mul_le_mul_of_nonneg_left (add_le_add hsqrt_le hq_div_le) (sq_nonneg K)
        _ = D * X + D * Y * X := by
            dsimp [X]
            ring
    calc
      2 * sampleCovarianceDeviationHdpScale m n K t
          ≤ 2 * (D * X + D * Y * X) :=
            mul_le_mul_of_nonneg_left hinner (by norm_num)
      _ = 2 * D * X + 2 * D * Y * X := by ring
  have hmax :=
    two_mul_scale_le_max_of_scale_bounds
      (D := D) (C := C) (k0 := k0) (X := X) (Y := Y)
      hD_nonneg hC_nonneg hk0_pos hX_nonneg hY_nonneg hY_le hC_D hCk0 hC_sq
  calc
    2 * sampleCovarianceDeviationHdpScale m n K t
        ≤ 2 * D * X + 2 * D * Y * X := hscale_pre
    _ ≤ max (C * X) ((C * X) ^ 2) := hmax
    _ = max ((twoSidedSubgaussianMatricesConstant * K ^ 2 * (√(n : ℝ) + t)) /
          √(m : ℝ))
        (((twoSidedSubgaussianMatricesConstant * K ^ 2 * (√(n : ℝ) + t)) /
          √(m : ℝ)) ^ 2) := by
        dsimp [C, X, Y, S]
        ring_nf

omit [MeasurableSpace Ω] in
lemma sampleCovarianceDeviation_tail_prefactor_le {m n : ℕ} (hm : 0 < m)
    {K t : ℝ} (hK : 0 < K) :
    2 * 17 ^ n *
        exp (-(1 / (4 * hdpHansonWrightConstant)) *
          min (((m : ℝ) * sampleCovarianceDeviationHdpScale m n K t) ^ 2 /
              (K ^ 4 * (m : ℝ)))
            (((m : ℝ) * sampleCovarianceDeviationHdpScale m n K t) / K ^ 2)) ≤
      2 * exp (-(t ^ 2)) := by
  let q : ℝ := 4 * hdpHansonWrightConstant * (17 * (n : ℝ) + t ^ 2)
  let r : ℝ := q / (m : ℝ)
  let s : ℝ := √r
  let u : ℝ := sampleCovarianceDeviationHdpScale m n K t
  have hmR_pos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hC_pos : 0 < hdpHansonWrightConstant := hdpHansonWrightConstant_pos
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    have hsum : 0 ≤ 17 * (n : ℝ) + t ^ 2 := by positivity
    positivity
  have hr_nonneg : 0 ≤ r := div_nonneg hq_nonneg hmR_pos.le
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact sqrt_nonneg r
  have hs_sq : s ^ 2 = r := by
    dsimp [s]
    exact sq_sqrt hr_nonneg
  have hu_eq : u = K ^ 2 * (s + r) := by
    dsimp [u, sampleCovarianceDeviationHdpScale, q, r, s]
  have hq_eq_mr : q = (m : ℝ) * r := by
    dsimp [r]
    field_simp [hmR_pos.ne']
  have hfirst :
      q ≤ ((m : ℝ) * u) ^ 2 / (K ^ 4 * (m : ℝ)) := by
    have hv_nonneg : 0 ≤ s + r := add_nonneg hs_nonneg hr_nonneg
    have hs_le : s ≤ s + r := by linarith
    have hs_sq_le : s ^ 2 ≤ (s + r) ^ 2 :=
      (sq_le_sq₀ hs_nonneg hv_nonneg).mpr hs_le
    calc
      q = (m : ℝ) * r := hq_eq_mr
      _ = (m : ℝ) * s ^ 2 := by rw [hs_sq]
      _ ≤ (m : ℝ) * (s + r) ^ 2 := mul_le_mul_of_nonneg_left hs_sq_le hmR_pos.le
      _ = ((m : ℝ) * u) ^ 2 / (K ^ 4 * (m : ℝ)) := by
        rw [hu_eq]
        field_simp [hK.ne', hmR_pos.ne']
  have hsecond :
      q ≤ ((m : ℝ) * u) / K ^ 2 := by
    calc
      q = (m : ℝ) * r := hq_eq_mr
      _ ≤ (m : ℝ) * (s + r) := by
        have : r ≤ s + r := by linarith
        exact mul_le_mul_of_nonneg_left this hmR_pos.le
      _ = ((m : ℝ) * u) / K ^ 2 := by
        rw [hu_eq]
        field_simp [hK.ne']
  have hmin : q ≤
      min (((m : ℝ) * u) ^ 2 / (K ^ 4 * (m : ℝ))) (((m : ℝ) * u) / K ^ 2) :=
    le_min hfirst hsecond
  have hcoef_nonpos : -(1 / (4 * hdpHansonWrightConstant)) ≤ 0 := by
    have hpos : 0 ≤ 1 / (4 * hdpHansonWrightConstant) := by positivity
    linarith
  have harg :
      -(1 / (4 * hdpHansonWrightConstant)) *
          min (((m : ℝ) * u) ^ 2 / (K ^ 4 * (m : ℝ))) (((m : ℝ) * u) / K ^ 2) ≤
        -(17 * (n : ℝ) + t ^ 2) := by
    calc
      -(1 / (4 * hdpHansonWrightConstant)) *
          min (((m : ℝ) * u) ^ 2 / (K ^ 4 * (m : ℝ))) (((m : ℝ) * u) / K ^ 2)
          ≤ -(1 / (4 * hdpHansonWrightConstant)) * q :=
            mul_le_mul_of_nonpos_left hmin hcoef_nonpos
      _ = -(17 * (n : ℝ) + t ^ 2) := by
        dsimp [q]
        field_simp [hC_pos.ne']
  have htail_exp :
      exp (-(1 / (4 * hdpHansonWrightConstant)) *
          min (((m : ℝ) * u) ^ 2 / (K ^ 4 * (m : ℝ))) (((m : ℝ) * u) / K ^ 2)) ≤
        exp (-(17 * (n : ℝ) + t ^ 2)) :=
    exp_le_exp.mpr harg
  have hcard : (17 : ℝ) ^ n ≤ exp (17 * (n : ℝ)) :=
    seventeen_pow_le_exp_seventeen_mul n
  calc
    2 * 17 ^ n *
        exp (-(1 / (4 * hdpHansonWrightConstant)) *
          min (((m : ℝ) * sampleCovarianceDeviationHdpScale m n K t) ^ 2 /
              (K ^ 4 * (m : ℝ)))
            (((m : ℝ) * sampleCovarianceDeviationHdpScale m n K t) / K ^ 2))
        = 2 * (17 : ℝ) ^ n *
            exp (-(1 / (4 * hdpHansonWrightConstant)) *
              min (((m : ℝ) * u) ^ 2 / (K ^ 4 * (m : ℝ))) (((m : ℝ) * u) / K ^ 2)) := by
          simp [u]
    _ ≤ 2 * exp (17 * (n : ℝ)) * exp (-(17 * (n : ℝ) + t ^ 2)) := by
          have hleft : 2 * (17 : ℝ) ^ n ≤ 2 * exp (17 * (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hcard (by norm_num : (0 : ℝ) ≤ 2)
          exact mul_le_mul hleft htail_exp (le_of_lt (exp_pos _))
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
              (le_of_lt (exp_pos _)))
    _ = 2 * exp (-(t ^ 2)) := by
          calc
            2 * exp (17 * (n : ℝ)) * exp (-(17 * (n : ℝ) + t ^ 2))
                = 2 * (exp (17 * (n : ℝ)) * exp (-(17 * (n : ℝ) + t ^ 2))) := by
                    ring
            _ = 2 * exp (17 * (n : ℝ) + (-(17 * (n : ℝ) + t ^ 2))) := by
                    rw [← exp_add]
            _ = 2 * exp (-(t ^ 2)) := by
                    congr 1
                    ring_nf

lemma sampleCovarianceDeviationOperatorNorm_hdp_bound_of_pos {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n)
    {A : Fin m → Fin n → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hA : HasIndependentMeanZeroIsotropicSubGaussianRows A μ)
    {K : ℝ} (hK_def : K = maxMatrixRowSubGaussianPsi2Norm A μ) (hK : 0 < K) :
    ∀ t : ℝ, 0 ≤ t →
      (μ {ω |
        sampleCovarianceDeviationOperatorNorm (randomMatrix A ω) ≤
          2 * sampleCovarianceDeviationHdpScale m n K t}).toReal ≥
        1 - 2 * exp (-(t ^ 2)) := by
  intro t _ht
  let u : ℝ := sampleCovarianceDeviationHdpScale m n K t
  have hmR_pos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnR_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hq_pos :
      0 < 4 * hdpHansonWrightConstant * (17 * (n : ℝ) + t ^ 2) := by
    have h17n_pos : 0 < 17 * (n : ℝ) := mul_pos (by norm_num) hnR_pos
    have hsum_pos : 0 < 17 * (n : ℝ) + t ^ 2 := by nlinarith [sq_nonneg t]
    exact mul_pos (mul_pos (by norm_num) hdpHansonWrightConstant_pos) hsum_pos
  have hdiv_pos :
      0 < (4 * hdpHansonWrightConstant * (17 * (n : ℝ) + t ^ 2)) / (m : ℝ) :=
    div_pos hq_pos hmR_pos
  have hu : 0 < u := by
    dsimp [u, sampleCovarianceDeviationHdpScale]
    exact mul_pos (sq_pos_of_pos hK) (add_pos (sqrt_pos.mpr hdiv_pos) hdiv_pos)
  have htail :=
    sampleCovarianceDeviationOperatorNorm_tail_le_of_row_subgaussian
      (m := m) (n := n) hm hn (A := A) (μ := μ) hA
      (K := K) (u := u) hK_def hK hu
  have htail_bound :
      (μ {ω | 2 * u < sampleCovarianceDeviationOperatorNorm (randomMatrix A ω)}).toReal ≤
        2 * exp (-(t ^ 2)) := by
    exact htail.trans
      (by
        simpa [u] using
          sampleCovarianceDeviation_tail_prefactor_le (m := m) (n := n) hm (K := K) (t := t) hK)
  have hprob :=
    probability_le_of_tail_real_le
      (μ := μ) (X := fun ω => sampleCovarianceDeviationOperatorNorm (randomMatrix A ω))
      (B := 2 * u) (δ := 2 * exp (-(t ^ 2))) htail_bound
  simpa [u] using hprob

lemma singular_value_sandwich_probability_of_sampleCovarianceDeviationHdpScale
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {A : Fin m → Fin n → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hA : HasIndependentMeanZeroIsotropicSubGaussianRows A μ)
    {K B t : ℝ} (hK_def : K = maxMatrixRowSubGaussianPsi2Norm A μ)
    (hK : 0 < K) (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hscale :
      2 * sampleCovarianceDeviationHdpScale m n K t ≤
        max (B / √(m : ℝ)) ((B / √(m : ℝ)) ^ 2)) :
    (μ {ω |
      √(m : ℝ) - B ≤ matrixSmallestSingularValue (randomMatrix A ω) ∧
        matrixSmallestSingularValue (randomMatrix A ω) ≤
          matrixLargestSingularValue (randomMatrix A ω) ∧
        matrixLargestSingularValue (randomMatrix A ω) ≤ √(m : ℝ) + B}).toReal ≥
      1 - 2 * exp (-(t ^ 2)) := by
  let covEvent : Set Ω :=
    {ω | sampleCovarianceDeviationOperatorNorm (randomMatrix A ω) ≤
      2 * sampleCovarianceDeviationHdpScale m n K t}
  let svEvent : Set Ω :=
    {ω |
      √(m : ℝ) - B ≤ matrixSmallestSingularValue (randomMatrix A ω) ∧
        matrixSmallestSingularValue (randomMatrix A ω) ≤
          matrixLargestSingularValue (randomMatrix A ω) ∧
        matrixLargestSingularValue (randomMatrix A ω) ≤ √(m : ℝ) + B}
  have hcov_prob :
      (μ covEvent).toReal ≥ 1 - 2 * exp (-(t ^ 2)) := by
    simpa [covEvent] using
      sampleCovarianceDeviationOperatorNorm_hdp_bound_of_pos
        (m := m) (n := n) hm hn (A := A) (μ := μ) hA hK_def hK t ht
  have hsubset : covEvent ⊆ svEvent := by
    intro ω hω
    have hdev :
        sampleCovarianceDeviationOperatorNorm (randomMatrix A ω) ≤
          max (B / √(m : ℝ)) ((B / √(m : ℝ)) ^ 2) :=
      hω.trans hscale
    exact singular_value_sandwich_of_sampleCovarianceDeviationOperatorNorm_le_max
      (m := m) (n := n) hm hn (randomMatrix A ω) hB hdev
  have hmono : (μ covEvent).toReal ≤ (μ svEvent).toReal :=
    ENNReal.toReal_mono (measure_ne_top μ svEvent) (measure_mono hsubset)
  have hsv : (μ svEvent).toReal ≥ 1 - 2 * exp (-(t ^ 2)) := by
    linarith
  simpa [svEvent] using hsv

/-! ## Exact HDP Section 4.6 propositions -/

/--
HDP Theorem 4.6.1, "Two-sided bound on subgaussian matrices".

For an `m × n` random matrix with independent, mean-zero, sub-Gaussian, isotropic rows
`Aᵢ`, and `K = max_i ‖Aᵢ‖_{ψ₂}`, there is a positive absolute constant `C` such that for
every `t ≥ 0`, with probability at least `1 - 2 exp (-t²)`,

`√m - C K² (√n + t) ≤ sₙ(A) ≤ s₁(A) ≤ √m + C K² (√n + t)`.
-/
def twoSidedSubgaussianMatricesHdp {m n : ℕ}
    (A : Fin m → Fin n → Ω → ℝ) (μ : Measure Ω) : Prop :=
  HasIndependentMeanZeroIsotropicSubGaussianRows A μ →
    ∃ C : ℝ, 0 < C ∧
      ∀ K : ℝ, K = maxMatrixRowSubGaussianPsi2Norm A μ → 0 < K →
        ∀ t : ℝ, 0 ≤ t →
          (μ {ω |
            √(m : ℝ) - C * K ^ 2 * (√(n : ℝ) + t) ≤
                matrixSmallestSingularValue (randomMatrix A ω) ∧
              matrixSmallestSingularValue (randomMatrix A ω) ≤
                matrixLargestSingularValue (randomMatrix A ω) ∧
              matrixLargestSingularValue (randomMatrix A ω) ≤
                √(m : ℝ) + C * K ^ 2 * (√(n : ℝ) + t)}).toReal ≥
            1 - 2 * exp (-(t ^ 2))

omit [MeasurableSpace Ω] in
lemma twoSidedSubgaussianMatricesConstant_pos :
    0 < twoSidedSubgaussianMatricesConstant := by
  have hD_pos : 0 < sampleCovarianceDeviationScaleConstant := by
    dsimp [sampleCovarianceDeviationScaleConstant, hdpHansonWrightConstant]
    positivity
  dsimp [twoSidedSubgaussianMatricesConstant]
  positivity

/-- HDP Theorem 4.6.1 for positive dimensions. -/
theorem two_sided_subgaussian_matrices_hdp_of_pos {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Fin m → Fin n → Ω → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    twoSidedSubgaussianMatricesHdp A μ := by
  intro hA
  refine ⟨twoSidedSubgaussianMatricesConstant, twoSidedSubgaussianMatricesConstant_pos, ?_⟩
  intro K hK_def hK t ht
  let B : ℝ := twoSidedSubgaussianMatricesConstant * K ^ 2 * (√(n : ℝ) + t)
  have hB_nonneg : 0 ≤ B := by
    have hS_nonneg : 0 ≤ √(n : ℝ) + t := by positivity
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg twoSidedSubgaussianMatricesConstant_pos.le (sq_nonneg K)) hS_nonneg
  have hK_lower :
      1 / (4 * exp 1 ^ 2) ≤ K ^ 2 :=
    hA.max_row_psi2_sq_lower hm hn hK_def hK
  have hscale :
      2 * sampleCovarianceDeviationHdpScale m n K t ≤
        max (B / √(m : ℝ)) ((B / √(m : ℝ)) ^ 2) := by
    simpa [B, mul_assoc, mul_left_comm, mul_comm] using
      sampleCovarianceDeviationHdpScale_le_max_hdp_radius
        (m := m) (n := n) hm (K := K) (t := t) hK ht hK_lower
  simpa [B, mul_assoc, mul_left_comm, mul_comm] using
    singular_value_sandwich_probability_of_sampleCovarianceDeviationHdpScale
      (m := m) (n := n) hm hn (A := A) (μ := μ) hA hK_def hK hB_nonneg ht hscale

end RMT

end

end LeanPool.StatisticalLearningTheory

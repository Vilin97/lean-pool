/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import LeanPool.NashEmbedding.NashEmbedding.Torus.Basic
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Periodization

/-!
# Leaves for the compact Nash assembly

Self-contained facts used by the proof of `nashCompact` (reduction to `nashTorus`,
Wassermann §13):

 - A: a smooth cutoff equal to `1` on a compact set with closed support in a
      given open neighbourhood.
 - B: positivity of the quadratic form is an open condition on matrices
      (`PosDef` itself includes symmetry, hence is NOT open); on symmetric
      matrices it is equivalent to `PosDef`; symmetrization.
 - C: real-valued and matrix-valued periodization on `ℝᴺ` (from the complex
      `periodicExtension` of `NashEmbedding/Sobolev/Periodization.lean`), with
      smoothness, periodicity, agreement on the cube `[-π,π]ᴺ`, and
      preservation of positive-definiteness.
 - D: the matrix of a bilinear form on `EuclideanSpace ℝ (Fin N)`, with
      positive-definiteness transfer and the evaluation identity.
 - E: `Realizes v g` gives the Gram identity for arbitrary directions.

All leaves were proved by Aristotle (project bf61e09c, 2026-08-30).
-/

open scoped BigOperators ContDiff Manifold Topology
open Matrix NashEmbedding.Sobolev Set

noncomputable section

namespace NashEmbedding

variable {N : ℕ}

/-! ## A. Cutoff on a compact set -/

/-- **A.** A smooth cutoff `ψ : ℝᴺ → [0,1]` with `ψ = 1` on the compact set `K` and
  `ψ = 0` outside the open set `W ⊇ K`. -/
theorem exists_cutoff_compact {K W : Set (Fin N → ℝ)} (hK : IsCompact K) (hW : IsOpen W)
    (hKW : K ⊆ W) :
    ∃ ψ : (Fin N → ℝ) → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ x ∈ K, ψ x = 1) ∧ (∀ x ∉ W, ψ x = 0) ∧
      ∀ x, ψ x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨f, h1, h0, hicc⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(ℝ, Fin N → ℝ)) (n := (⊤ : ℕ∞))
      hK.isClosed (by rwa [hW.interior_eq])
  exact ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, fun x hx => h1.self_of_nhdsSet _ hx, h0, hicc⟩

/-! ## B. Positivity of the quadratic form is open -/

/-- The quadratic form written as a double sum. -/
lemma quadForm_eq_sum (M : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ) :
    x ⬝ᵥ M.mulVec x = ∑ i, ∑ j, x i * M i j * x j := by
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/-- The quadratic form is homogeneous of degree `2`. -/
lemma quadForm_smul (M : Matrix (Fin N) (Fin N) ℝ) (t : ℝ) (x : Fin N → ℝ) :
    (t • x) ⬝ᵥ M.mulVec (t • x) = t ^ 2 * (x ⬝ᵥ M.mulVec x) := by
  simp [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring

/-- The quadratic form is additive in the matrix. -/
lemma quadForm_add (M D : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ) :
    x ⬝ᵥ (M + D).mulVec x = x ⬝ᵥ M.mulVec x + x ⬝ᵥ D.mulVec x := by
  simp [add_mulVec, dotProduct_add]

/-- Crude bound for the quadratic form on the unit ball. -/
lemma abs_quadForm_le (M : Matrix (Fin N) (Fin N) ℝ) {x : Fin N → ℝ} (hx : ‖x‖ ≤ 1) :
    |x ⬝ᵥ M.mulVec x| ≤ (N : ℝ) ^ 2 * ‖M‖ := by
  have hxi : ∀ i, |x i| ≤ 1 := fun i => by
    have := norm_le_pi_norm x i; rw [Real.norm_eq_abs] at this; linarith
  have hM : ∀ i j, |M i j| ≤ ‖M‖ := fun i j => by
    have h1 : ‖M i j‖ ≤ ‖M i‖ := norm_le_pi_norm (M i) j
    have h2 : ‖M i‖ ≤ ‖M‖ := norm_le_pi_norm M i
    simpa [Real.norm_eq_abs] using h1.trans h2
  rw [quadForm_eq_sum]
  calc |∑ i, ∑ j, x i * M i j * x j| ≤ ∑ i, |∑ j, x i * M i j * x j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, ∑ _j : Fin N, ‖M‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul, abs_mul]
        calc |x i| * |M i j| * |x j| ≤ 1 * ‖M‖ * 1 := by
              gcongr <;> first | exact hxi _ | exact hM _ _
          _ = ‖M‖ := by ring
    _ = (N : ℝ) ^ 2 * ‖M‖ := by simp [Finset.sum_const, nsmul_eq_mul]; ring

/-- The quadratic form of a fixed matrix is continuous. -/
lemma continuous_quadForm (M : Matrix (Fin N) (Fin N) ℝ) :
    Continuous fun x : Fin N → ℝ => x ⬝ᵥ M.mulVec x := by
  simp only [quadForm_eq_sum]
  fun_prop

/-- **B1.** The set of real matrices with positive quadratic form is open
  (minimum over the unit sphere is continuous in `A`). -/
theorem isOpen_quadForm_pos :
    IsOpen {A : Matrix (Fin N) (Fin N) ℝ | ∀ x, x ≠ 0 → 0 < x ⬝ᵥ A.mulVec x} := by
  apply Metric.isOpen_iff.mpr
  intro A hA
  obtain ⟨c, hc0, hc⟩ : ∃ c > 0, ∀ x : Fin N → ℝ, ‖x‖ = 1 → c ≤ x ⬝ᵥ A.mulVec x := by
    rcases Set.eq_empty_or_nonempty (Metric.sphere (0 : Fin N → ℝ) 1) with he | hne
    · refine ⟨1, one_pos, fun x hx => ?_⟩
      exact absurd (show x ∈ Metric.sphere (0 : Fin N → ℝ) 1 by simpa using hx)
        (by rw [he]; exact Set.notMem_empty x)
    · obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_sphere (0 : Fin N → ℝ) 1).exists_isMinOn hne
        (continuous_quadForm A).continuousOn
      have hx₀1 : ‖x₀‖ = 1 := by simpa using hx₀
      have hx₀0 : x₀ ≠ 0 := by intro h; rw [h] at hx₀1; simp at hx₀1
      refine ⟨x₀ ⬝ᵥ A.mulVec x₀, hA x₀ hx₀0, fun x hx => ?_⟩
      exact hmin (show x ∈ Metric.sphere (0 : Fin N → ℝ) 1 by simpa using hx)
  refine ⟨c / ((N : ℝ) ^ 2 + 1), by positivity, ?_⟩
  intro B hB x hx
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set u : Fin N → ℝ := ‖x‖⁻¹ • x with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul]; simp [inv_mul_cancel₀ (ne_of_gt hxn)]
  have hxu : x = ‖x‖ • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ (ne_of_gt hxn), one_smul]
  have hBA : A + (B - A) = B := by abel
  have hbd : |u ⬝ᵥ (B - A).mulVec u| ≤ (N : ℝ) ^ 2 * ‖B - A‖ := abs_quadForm_le _ (le_of_eq hun)
  have hdist : ‖B - A‖ < c / ((N : ℝ) ^ 2 + 1) := by
    have h := hB
    simp only [Metric.mem_ball, dist_eq_norm] at h
    exact h
  have hposu : 0 < u ⬝ᵥ B.mulVec u := by
    have h1 : c ≤ u ⬝ᵥ A.mulVec u := hc u hun
    have h2 : u ⬝ᵥ B.mulVec u = u ⬝ᵥ A.mulVec u + u ⬝ᵥ (B - A).mulVec u := by
      rw [← quadForm_add, hBA]
    have h3 : -((N : ℝ) ^ 2 * ‖B - A‖) ≤ u ⬝ᵥ (B - A).mulVec u := neg_le_of_abs_le hbd
    have hpos : (0 : ℝ) < (N : ℝ) ^ 2 + 1 := by positivity
    rw [lt_div_iff₀ hpos] at hdist
    nlinarith [norm_nonneg (B - A), sq_nonneg ((N : ℝ))]
  rw [hxu, quadForm_smul]
  positivity

/-- **B2.** A symmetric matrix with positive quadratic form is positive definite. -/
theorem posDef_of_isSymm_of_quadForm_pos {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsSymm)
    (hpos : ∀ x, x ≠ 0 → 0 < x ⬝ᵥ A.mulVec x) : A.PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => by simpa using hpos x hx⟩
  show Aᴴ = A
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hA

/-- Evaluation of a matrix entry is smooth. -/
lemma contDiff_matrix_entry (i j : Fin N) :
    ContDiff ℝ ∞ fun A : Matrix (Fin N) (Fin N) ℝ => A i j :=
  (contDiff_apply ℝ ℝ j).comp (contDiff_apply ℝ (Fin N → ℝ) i)

/-- The symmetrization `(A + Aᵀ)/2`. -/
def symmetrize (A : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  (1 / 2 : ℝ) • (A + Aᵀ)

/-- **B3.** `symmetrize A` is symmetric, equals `A` when `A` is symmetric, has the same
  quadratic form as `A`, and `symmetrize` is smooth. -/
theorem symmetrize_isSymm (A : Matrix (Fin N) (Fin N) ℝ) : (symmetrize A).IsSymm := by
  show (symmetrize A)ᵀ = symmetrize A
  simp [symmetrize, Matrix.transpose_add, add_comm]

theorem symmetrize_eq_self {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsSymm) : symmetrize A = A := by
  rw [symmetrize, hA.eq]
  ext i j
  simp
  ring

theorem quadForm_symmetrize (A : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ) :
    x ⬝ᵥ (symmetrize A).mulVec x = x ⬝ᵥ A.mulVec x := by
  rw [quadForm_eq_sum, quadForm_eq_sum]
  have h : ∀ i j : Fin N, x i * (symmetrize A) i j * x j
      = (1 / 2) * (x i * A i j * x j) + (1 / 2) * (x j * A j i * x i) := by
    intro i j
    simp [symmetrize, Matrix.transpose_apply]
    ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin N))) (t := (Finset.univ : Finset (Fin N)))
    (f := fun i j => x j * A j i * x i)]
  ring

theorem contDiff_symmetrize :
    ContDiff ℝ ∞ (symmetrize : Matrix (Fin N) (Fin N) ℝ → Matrix (Fin N) (Fin N) ℝ) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  show ContDiff ℝ ∞ fun A : Matrix (Fin N) (Fin N) ℝ => (1 / 2 : ℝ) * (A i j + A j i)
  have := ((contDiff_matrix_entry (N := N) i j).add (contDiff_matrix_entry j i)).const_smul
    (1 / 2 : ℝ)
  simpa [smul_eq_mul] using this

/-! ## C. Real and matrix periodization -/

/-- The open cube `(-π, π)ᴺ`. -/
def openCube (N : ℕ) : Set (Fin N → ℝ) := {x | ∀ j, |x j| < Real.pi}

/-- Real-valued periodic extension, via the complex one. -/
def periodicExtR (N : ℕ) (φ : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  (periodicExtension N (fun y => (φ y : ℂ)) x).re

/-- **C1.** `periodicExtR` is `2πℤᴺ`-periodic. -/
theorem periodicExtR_isPeriodic2Pi (φ : (Fin N → ℝ) → ℝ) :
    IsPeriodic2Pi (periodicExtR N φ) := by
  intro x k
  simp [periodicExtR, periodicExtension_isPeriodic2Pi _ x k]

/-- **C2.** `periodicExtR` of a compactly supported smooth function is smooth. -/
theorem periodicExtR_contDiff {φ : (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hsupp : HasCompactSupport φ) : ContDiff ℝ ∞ (periodicExtR N φ) := by
  have h1 : ContDiff ℝ ∞ fun y : Fin N → ℝ => (φ y : ℂ) := Complex.ofRealCLM.contDiff.comp hφ
  have h2 : HasCompactSupport fun y : Fin N → ℝ => (φ y : ℂ) :=
    hsupp.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  exact Complex.reCLM.contDiff.comp (periodicExtension_contDiff h1 h2)

/-- **C3.** If `φ` is supported in the open cube, `periodicExtR φ = φ` on the closed cube. -/
theorem periodicExtR_eq_self_of_mem {φ : (Fin N → ℝ) → ℝ} (hsupp : ∀ x, φ x ≠ 0 → x ∈ openCube N)
    {x : Fin N → ℝ} (hx : ∀ j, |x j| ≤ Real.pi) : periodicExtR N φ x = φ x := by
  have h : periodicExtension N (fun y => (φ y : ℂ)) x = (φ x : ℂ) := by
    unfold periodicExtension
    rw [tsum_eq_single 0]
    · have h0 : periodicShift N 0 = 0 := by funext i; simp [periodicShift]
      rw [h0, add_zero]
    · intro l hl
      obtain ⟨j, hj⟩ : ∃ j, l j ≠ 0 := by
        by_contra h
        push Not at h
        exact hl (funext h)
      have hzero : φ (x + periodicShift N l) = 0 := by
        by_contra hne
        have hb := hsupp _ hne j
        have hxj := hx j
        have hl1 : (1 : ℝ) ≤ |(l j : ℝ)| := by exact_mod_cast Int.one_le_abs hj
        have hpi := Real.pi_pos
        have hcoord : (x + periodicShift N l) j = x j + 2 * Real.pi * (l j : ℝ) := by
          simp [periodicShift]
        rw [hcoord] at hb
        have h2 : |2 * Real.pi * (l j : ℝ)| = 2 * Real.pi * |(l j : ℝ)| := by
          rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * Real.pi)]
        have h3 : |2 * Real.pi * (l j : ℝ)| ≤ |x j + 2 * Real.pi * (l j : ℝ)| + |x j| :=
          calc |2 * Real.pi * (l j : ℝ)| = |(x j + 2 * Real.pi * (l j : ℝ)) - x j| := by ring_nf
            _ ≤ |x j + 2 * Real.pi * (l j : ℝ)| + |x j| := abs_sub _ _
        nlinarith
      simp [hzero]
  simp [periodicExtR, h]

/-- **C4.** Every point is congruent mod `2πℤᴺ` to a point of the closed cube. -/
theorem exists_periodicShift_mem_cube (x : Fin N → ℝ) :
    ∃ k : Fin N → ℤ, ∀ j, |(x + periodicShift N k) j| ≤ Real.pi := by
  refine ⟨fun j => -round (x j / (2 * Real.pi)), fun j => ?_⟩
  have hpi := Real.pi_pos
  have hcoord : (x + periodicShift N (fun j => -round (x j / (2 * Real.pi)))) j
      = 2 * Real.pi * (x j / (2 * Real.pi) - (round (x j / (2 * Real.pi)) : ℝ)) := by
    simp [periodicShift]
    field_simp
    ring
  rw [hcoord, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * Real.pi)]
  have := abs_sub_round (x j / (2 * Real.pi))
  nlinarith

/-- Matrix-valued periodization of `G`, for `G - 1` supported in the open cube:
  `1 + (G - 1)^{per}` entrywise. -/
def periodicMatrixExt (N : ℕ) (G : (Fin N → ℝ) → Matrix (Fin N) (Fin N) ℝ)
    (x : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  1 + Matrix.of fun i j => periodicExtR N (fun y => (G y - 1) i j) x

/-- `periodicMatrixExt` is `2πℤᴺ`-periodic (entrywise, from C1). -/
theorem periodicMatrixExt_isPeriodic2Pi (G : (Fin N → ℝ) → Matrix (Fin N) (Fin N) ℝ) :
    IsPeriodic2Pi (periodicMatrixExt N G) := by
  intro x k
  ext i j
  simp only [periodicMatrixExt, Matrix.add_apply, Matrix.of_apply]
  rw [periodicExtR_isPeriodic2Pi (fun y => (G y - 1) i j) x k]

/-- **C5.** Smooth periodic, for smooth `G` with `G - 1` compactly supported. -/
theorem periodicMatrixExt_smoothPeriodic {G : (Fin N → ℝ) → Matrix (Fin N) (Fin N) ℝ}
    (hG : ContDiff ℝ ∞ G) (hsupp : HasCompactSupport fun y => G y - 1) :
    SmoothPeriodic (periodicMatrixExt N G) := by
  refine ⟨?_, periodicMatrixExt_isPeriodic2Pi G⟩
  have hentry : ∀ i j : Fin N, ContDiff ℝ ∞ (periodicExtR N fun y => (G y - 1) i j) := by
    intro i j
    refine periodicExtR_contDiff ((contDiff_matrix_entry i j).comp (hG.sub contDiff_const)) ?_
    exact hsupp.comp_left (g := fun M : Matrix (Fin N) (Fin N) ℝ => M i j) (by simp)
  have hmat : ContDiff ℝ ∞ fun x : Fin N → ℝ =>
      Matrix.of fun i j => periodicExtR N (fun y => (G y - 1) i j) x :=
    contDiff_pi.2 fun i => contDiff_pi.2 fun j => hentry i j
  exact contDiff_const.add hmat

/-- **C6.** Agreement with `G` on the closed cube when `G - 1` is supported in the open cube. -/
theorem periodicMatrixExt_eq_of_mem {G : (Fin N → ℝ) → Matrix (Fin N) (Fin N) ℝ}
    (hsupp : ∀ y, G y - 1 ≠ 0 → y ∈ openCube N) {x : Fin N → ℝ} (hx : ∀ j, |x j| ≤ Real.pi) :
    periodicMatrixExt N G x = G x := by
  ext i j
  have h : periodicExtR N (fun y => (G y - 1) i j) x = (G x - 1) i j := by
    refine periodicExtR_eq_self_of_mem (fun y hy => hsupp y fun h0 => hy ?_) hx
    rw [h0]
    simp
  show (1 : Matrix (Fin N) (Fin N) ℝ) i j + periodicExtR N (fun y => (G y - 1) i j) x = G x i j
  rw [h, Matrix.sub_apply]
  ring

/-- **C7.** Positive-definiteness everywhere, from positive-definiteness of `G`: by C4,
  `x + 2πk` lies in the closed cube for some `k`, so by periodicity (C1) and C6,
  `periodicMatrixExt G x = periodicMatrixExt G (x + 2πk) = G (x + 2πk)`, which is PD. -/
theorem periodicMatrixExt_posDef {G : (Fin N → ℝ) → Matrix (Fin N) (Fin N) ℝ}
    (hsupp : ∀ y, G y - 1 ≠ 0 → y ∈ openCube N) (hG : ∀ y, (G y).PosDef) (x : Fin N → ℝ) :
    (periodicMatrixExt N G x).PosDef := by
  obtain ⟨k, hk⟩ := exists_periodicShift_mem_cube x
  have h1 : periodicMatrixExt N G (x + periodicShift N k) = periodicMatrixExt N G x :=
    periodicMatrixExt_isPeriodic2Pi G x k
  have h2 : periodicMatrixExt N G (x + periodicShift N k) = G (x + periodicShift N k) :=
    periodicMatrixExt_eq_of_mem hsupp hk
  rw [← h1, h2]
  exact hG _

/-! ## D. Bilinear forms on `EuclideanSpace ℝ (Fin N)` as matrices -/

/-- Expansion of a vector of `EuclideanSpace ℝ (Fin N)` in the standard basis. -/
lemma euclideanSpace_eq_sum_single (a : EuclideanSpace ℝ (Fin N)) :
    a = ∑ i, a i • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  simp [Pi.single_apply]

/-- The matrix `B (eᵢ) (eⱼ)` of a bilinear form on `ℝᴺ`. -/
def formMatrix (B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

/-- **D1.** Evaluation: `B a b = a ⬝ᵥ (formMatrix B).mulVec b`. -/
theorem formMatrix_apply (B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (a b : EuclideanSpace ℝ (Fin N)) :
    B a b = (⇑a : Fin N → ℝ) ⬝ᵥ (formMatrix B).mulVec (⇑b : Fin N → ℝ) := by
  rw [dotProduct, formMatrix]
  conv_lhs => rw [euclideanSpace_eq_sum_single a, euclideanSpace_eq_sum_single b]
  simp [map_sum, map_smul, Finset.sum_apply, mulVec, dotProduct, Finset.mul_sum, mul_comm,
    mul_left_comm]
  rw [Finset.sum_comm]

/-- **D2.** A symmetric positive-definite form has a positive-definite matrix. -/
theorem formMatrix_posDef (B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (hsymm : ∀ a b, B a b = B b a) (hpos : ∀ a, a ≠ 0 → 0 < B a a) :
    (formMatrix B).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · show (formMatrix B)ᴴ = formMatrix B
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    simp [formMatrix, Matrix.transpose_apply, hsymm]
  · intro x hx
    have ha : (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N)) ≠ 0 := by simpa using hx
    have h := hpos _ ha
    rw [formMatrix_apply] at h
    simpa using h

/-- **D3.** `formMatrix` is smooth (it is linear). -/
theorem contDiff_formMatrix :
    ContDiff ℝ ∞ (formMatrix : (EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) →
      Matrix (Fin N) (Fin N) ℝ) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  show ContDiff ℝ ∞ fun B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ =>
    B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  exact (contDiff_id.clm_apply contDiff_const).clm_apply contDiff_const

/-! ## E. The Gram identity from `Realizes` -/

/-- Expansion of a vector of `ℝⁿ` in the standard basis. -/
lemma pi_eq_sum_single {n : ℕ} (a : Fin n → ℝ) : a = ∑ i, a i • (Pi.single i 1 : Fin n → ℝ) := by
  funext j
  simp [Pi.single_apply, Finset.sum_apply]

/-- **E.** If `v` realizes `g`, then `Dv(x) a ⬝ᵥ Dv(x) b = a ⬝ᵥ g(x).mulVec b` for all
  directions `a b` (no differentiability hypothesis is needed: if `v` is not
  differentiable at `x` both sides vanish). -/
theorem realizes_fderiv_dot {n q : ℕ} {v : (Fin n → ℝ) → (Fin q → ℝ)}
    {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} (hv : Realizes v g) (x a b : Fin n → ℝ) :
    (fderiv ℝ v x a) ⬝ᵥ (fderiv ℝ v x b) = a ⬝ᵥ (g x).mulVec b := by
  conv_lhs => rw [pi_eq_sum_single a, pi_eq_sum_single b]
  rw [map_sum, map_sum]
  simp only [map_smul, sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  have h : ∀ i j : Fin n, (fderiv ℝ v x (Pi.single i 1)) ⬝ᵥ (fderiv ℝ v x (Pi.single j 1))
      = g x i j := fun i j => hv x i j
  simp only [h]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end NashEmbedding

end

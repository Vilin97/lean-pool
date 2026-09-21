/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Sylvester.HilbertSchmidtEstimate
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtFiniteRank
-- the planar trace/determinant recovery of singular values, used for the
-- source's own `2 × 2` witness at the end of this file
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.TwoDimensionalSingularValues

/-! # Operator Norm Estimate -/

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, inequality (5.2), and the source's `2 × 2` witness

## Which norms the subscripts name

Section 1 of the source fixes the notation, and it is **not** the modern
Schatten convention.  After the minimax characterisation (1.10) the paper says
"in particular, `κ₁` is equal to the bound norm of `K`, which we write
`‖K‖₁`", and (1.11) introduces the Ky Fan norms `‖K‖_ν = κ₁ + ⋯ + κ_ν`, adding
"these include the bound norm `‖·‖₁`".  So the paper's subscript `1` is the
**operator (bound) norm**, the largest singular value — not the trace norm.
The square norm carries the subscript `sq`, and is the Hilbert--Schmidt norm
`‖K‖_sq² = ∑ κ_k² = tr K⋆K`.

The printed inequalities of Section 5 are therefore

```text
(5.1)   ‖C‖_sq            ≥ δ ‖X‖_sq        -- Hilbert--Schmidt
(5.2)   ‖C‖_op √(rank C)  ≥ δ ‖X‖_op        -- operator norm
```

with `C = AX - XB`.  The source's own witness confirms the reading
numerically: for its `2 × 2` data it records `‖AX - XB‖₁ = 3√2 = 4.24…`, and
`3√2` is the operator norm of that defect, whose trace norm is `6√2`.

## Contents

* `opNorm_sylvester_le_of_pairwiseSpectrumGap` — inequality (5.2),
  derived from the compiled (5.1) by the two exact comparisons
  `‖·‖_op ≤ ‖·‖_sq` and `‖·‖_sq ≤ √(rank) ‖·‖_op`, at the same closed-operator
  generality as (5.1).  The real companion is the `_real_` variant.
* `opNorm_sylvester_le_finrank_range` — the same with the genuine
  `rank C`, i.e. `finrank` of the range, rather than an upper bound for it.
* The source's `2 × 2` witness that the constant `1` is too small in (5.2):
  `X = [[3,-3],[-3,1]]`, `A = diag(1,-1)`, `B = diag(0,2)`, `δ = 1`, for which
  `δ ‖X‖_op = 2 + √10 > 3√2 = ‖AX - XB‖_op`.

Whether `rank C` in (5.2) may be replaced by a constant is the source's own
open question and is not an obligation of this development.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta


open scoped InnerProductSpace BigOperators ENNReal


noncomputable section

universe v

/-- **Davis--Kahan inequality (5.2), closed-operator operator-norm form.**

  `δ ‖X‖ ≤ ‖C‖ √r`   whenever   `rank C ≤ r`.

The derivation is the paper's: the operator norm is below the square norm, the
square norm obeys (5.1), and a rank-`r` operator's square norm is at most
`√r` times its operator norm.  Hilbert--Schmidt membership of `C` is not a
hypothesis here — the rank bound supplies it. -/
theorem opNorm_sylvester_le_of_pairwiseSpectrumGap
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    {X C : F →L[ℂ] E}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : PairwiseSpectrumGap A B δ)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
    {r : ℕ} (hRank : C.rank ≤ (r : Cardinal)) :
    δ * ‖X‖ ≤ ‖C‖ * Real.sqrt r := by
  have hC : approximationNumberEnergy C ≠ ⊤ := approximationNumberEnergy_ne_top_of_rank_le hRank
  have hmain :=
    hilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap hA hB hδ hgap hEq hC
  calc
    δ * ‖X‖ ≤ δ * ContinuousLinearMap.hilbertSchmidtNorm X :=
      mul_le_mul_of_nonneg_left (opNorm_le_hilbertSchmidtNorm hmain.1) hδ.le
    _ ≤ ContinuousLinearMap.hilbertSchmidtNorm C := hmain.2
    _ ≤ Real.sqrt r * ‖C‖ := hilbertSchmidtNorm_le_sqrt_rank_mul_opNorm hRank
    _ = ‖C‖ * Real.sqrt r := mul_comm _ _

/-- **Inequality (5.2) over real Hilbert spaces.** -/
theorem opNorm_sylvester_real_le_of_pairwiseSpectrumGap
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {A : E →ₗ.[ℝ] E}
    {B : F →ₗ.[ℝ] F}
    {X C : F →L[ℝ] E}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ lam ∈ TauCeti.LinearPMap.realSpectrum A, ∀ α ∈ TauCeti.LinearPMap.realSpectrum B, δ ≤ |lam - α|)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
    {r : ℕ} (hRank : C.rank ≤ (r : Cardinal)) :
    δ * ‖X‖ ≤ ‖C‖ * Real.sqrt r := by
  have hC : approximationNumberEnergy C ≠ ⊤ := approximationNumberEnergy_ne_top_of_rank_le hRank
  have hmain :=
    hilbertSchmidt_sylvester_real_le_of_pairwiseSpectrumGap hA hB hδ hgap hEq hC
  calc
    δ * ‖X‖ ≤ δ * ContinuousLinearMap.hilbertSchmidtNorm X :=
      mul_le_mul_of_nonneg_left (opNorm_le_hilbertSchmidtNorm hmain.1) hδ.le
    _ ≤ ContinuousLinearMap.hilbertSchmidtNorm C := hmain.2
    _ ≤ Real.sqrt r * ‖C‖ := hilbertSchmidtNorm_le_sqrt_rank_mul_opNorm hRank
    _ = ‖C‖ * Real.sqrt r := mul_comm _ _

/-- **Inequality (5.2) with the genuine `rank C`.**

`opNorm_sylvester_le_of_pairwiseSpectrumGap` is stated against an
upper bound `r` for the rank, which is what a possibly infinite-dimensional
statement can carry.  When the ambient spaces are finite dimensional the rank
itself is available, and the printed `√(rank C)` is exactly this. -/
theorem opNorm_sylvester_le_finrank_range
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [FiniteDimensional ℂ F]
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    {X C : F →L[ℂ] E}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : PairwiseSpectrumGap A B δ)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C) :
    δ * ‖X‖ ≤
      ‖C‖ * Real.sqrt (Module.finrank ℂ (LinearMap.range (C : F →ₗ[ℂ] E))) := by
  have hRank : C.rank ≤
      ((Module.finrank ℂ (LinearMap.range (C : F →ₗ[ℂ] E)) : ℕ) : Cardinal) :=
    le_of_eq (Module.finrank_eq_rank ℂ (LinearMap.range (C : F →ₗ[ℂ] E))).symm
  exact opNorm_sylvester_le_of_pairwiseSpectrumGap hA hB hδ hgap hEq hRank

/-! ### The source's `2 × 2` witness that the constant `1` is too small

The paper writes: "certainly the constant `1` is too small, as can be seen
from `X = [[3,-3],[-3,1]]`, `A = diag(1,-1)`, `B = diag(0,2)`, `δ = 1`, for
which `δ‖X‖₁ = 2 + √10 = 5.16… > ‖AX - XB‖₁ = 3√2 = 4.24…`."

Everything printed there is compiled below: the Sylvester relation, the
eigenvalue gap `δ = 1`, both operator norms exactly, and the strict
inequality. -/

section Sharpness

/-- The real plane carrying the source's `2 × 2` witness. -/
abbrev SharpPlane52 : Type := EuclideanSpace ℝ (Fin 2)

/-- The source's `X = [[3,-3],[-3,1]]`. -/
def sharpX52 : SharpPlane52 →ₗ[ℝ] SharpPlane52 :=
  Matrix.toEuclideanLin !![(3 : ℝ), -3; -3, 1]

/-- The source's `A = diag(1,-1)`. -/
def sharpA52 : SharpPlane52 →ₗ[ℝ] SharpPlane52 :=
  Matrix.toEuclideanLin !![(1 : ℝ), 0; 0, -1]

/-- The source's `B = diag(0,2)`. -/
def sharpB52 : SharpPlane52 →ₗ[ℝ] SharpPlane52 :=
  Matrix.toEuclideanLin !![(0 : ℝ), 0; 0, 2]

/-- The defect `C = AX - XB = [[3,3],[3,-3]]`. -/
def sharpC52 : SharpPlane52 →ₗ[ℝ] SharpPlane52 :=
  Matrix.toEuclideanLin !![(3 : ℝ), 3; 3, -3]

/-- Coordinates of a matrix map at a standard basis vector: the `i`-th column. -/
theorem sharp52_entry (M : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    (Matrix.toEuclideanLin M) (EuclideanSpace.basisFun (Fin 2) ℝ i) j = M j i := by
  simp [Matrix.toLpLin_apply, EuclideanSpace.basisFun_apply, Matrix.mulVec_single]

/-- The squared Euclidean norm in the plane, entrywise. -/
theorem sharp52_norm_sq (x : SharpPlane52) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-- The real inner product in the plane, entrywise. -/
theorem sharp52_inner (x y : SharpPlane52) : ⟪x, y⟫_ℝ = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- The planar Gram trace of a matrix map is the sum of the squared entries. -/
theorem sharp52_gramTrace (M : Matrix (Fin 2) (Fin 2) ℝ) :
    TauCeti.gramTraceFinTwo (Matrix.toEuclideanLin M) =
      M 0 0 ^ 2 + M 1 0 ^ 2 + (M 0 1 ^ 2 + M 1 1 ^ 2) := by
  change ∑ i : Fin 2,
    ‖(Matrix.toEuclideanLin M) (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ^ 2 = _
  rw [Fin.sum_univ_two, sharp52_norm_sq, sharp52_norm_sq]
  rw [sharp52_entry, sharp52_entry, sharp52_entry, sharp52_entry]

/-- The planar Gram determinant of a matrix map is the squared determinant. -/
theorem sharp52_gramDet (M : Matrix (Fin 2) (Fin 2) ℝ) :
    TauCeti.gramDetFinTwo (Matrix.toEuclideanLin M) =
      (M 0 0 * M 1 1 - M 0 1 * M 1 0) ^ 2 := by
  change ‖(Matrix.toEuclideanLin M) (EuclideanSpace.basisFun (Fin 2) ℝ 0)‖ ^ 2 *
      ‖(Matrix.toEuclideanLin M) (EuclideanSpace.basisFun (Fin 2) ℝ 1)‖ ^ 2 -
      ‖⟪(Matrix.toEuclideanLin M) (EuclideanSpace.basisFun (Fin 2) ℝ 0),
        (Matrix.toEuclideanLin M) (EuclideanSpace.basisFun (Fin 2) ℝ 1)⟫_ℝ‖ ^ 2 = _
  rw [sharp52_norm_sq, sharp52_norm_sq, sharp52_inner, Real.norm_eq_abs, sq_abs]
  rw [sharp52_entry, sharp52_entry, sharp52_entry, sharp52_entry]
  ring

/-- `√10` is at least `2`, so the smaller singular value of `X` is nonnegative. -/
theorem sharp52_two_le_sqrt_ten : (2 : ℝ) ≤ Real.sqrt 10 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10), Real.sqrt_nonneg (10 : ℝ)]

/-- **The singular values of the source's `X` are `2 + √10` and `√10 - 2`.** -/
theorem sharp52_singularValues_X :
    sharpX52.singularValues =
      TauCeti.pairSingularValues (2 + Real.sqrt 10) (Real.sqrt 10 - 2) := by
  have h10 : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have htr : TauCeti.gramTraceFinTwo sharpX52 = 28 := by
    rw [show sharpX52 = Matrix.toEuclideanLin !![(3 : ℝ), -3; -3, 1] from rfl,
      sharp52_gramTrace]
    norm_num
  have hdt : TauCeti.gramDetFinTwo sharpX52 = 36 := by
    rw [show sharpX52 = Matrix.toEuclideanLin !![(3 : ℝ), -3; -3, 1] from rfl,
      sharp52_gramDet]
    norm_num
  refine TauCeti.singularValues_eq_pair_of_gram_trace_det_fin_two sharpX52
    (by nlinarith [Real.sqrt_nonneg (10 : ℝ)])
    (by linarith [sharp52_two_le_sqrt_ten])
    (by linarith [Real.sqrt_nonneg (10 : ℝ)]) ?_ ?_
  · rw [htr]; nlinarith [h10]
  · rw [hdt]; nlinarith [h10]

/-- **The singular values of the source's defect `C` are both `3√2`.** -/
theorem sharp52_singularValues_C :
    sharpC52.singularValues =
      TauCeti.pairSingularValues (3 * Real.sqrt 2) (3 * Real.sqrt 2) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ 3 * Real.sqrt 2 :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg 2)
  have htr : TauCeti.gramTraceFinTwo sharpC52 = 36 := by
    rw [show sharpC52 = Matrix.toEuclideanLin !![(3 : ℝ), 3; 3, -3] from rfl,
      sharp52_gramTrace]
    norm_num
  have hdt : TauCeti.gramDetFinTwo sharpC52 = 324 := by
    rw [show sharpC52 = Matrix.toEuclideanLin !![(3 : ℝ), 3; 3, -3] from rfl,
      sharp52_gramDet]
    norm_num
  refine TauCeti.singularValues_eq_pair_of_gram_trace_det_fin_two sharpC52
    hnn hnn le_rfl ?_ ?_
  · rw [htr]; nlinarith [h2]
  · rw [hdt]; nlinarith [h2]

/-- `‖X‖₁ = 2 + √10`, the paper's `5.16…`. -/
theorem sharp52_opNorm_X : ‖sharpX52.toContinuousLinearMap‖ = 2 + Real.sqrt 10 := by
  rw [TauCeti.opNorm_eq_singularValues_zero sharpX52 finrank_euclideanSpace_fin
    (by norm_num), sharp52_singularValues_X, TauCeti.pairSingularValues_zero]

/-- `‖AX - XB‖₁ = 3√2`, the paper's `4.24…`. -/
theorem sharp52_opNorm_C : ‖sharpC52.toContinuousLinearMap‖ = 3 * Real.sqrt 2 := by
  rw [TauCeti.opNorm_eq_singularValues_zero sharpC52 finrank_euclideanSpace_fin
    (by norm_num), sharp52_singularValues_C, TauCeti.pairSingularValues_zero]

/-- **The witness really solves the Sylvester equation**: `C = AX - XB`. -/
theorem sharp52_sylvester : sharpC52 = sharpA52 ∘ₗ sharpX52 - sharpX52 ∘ₗ sharpB52 := by
  ext x i
  fin_cases i <;>
    simp [sharpA52, sharpB52, sharpC52, sharpX52, Matrix.toLpLin_apply,
      Matrix.vecHead, Matrix.vecTail] <;>
    ring

/-- `A² = 1`, so every eigenvalue of `A` squares to one. -/
theorem sharp52_A_sq : sharpA52 ∘ₗ sharpA52 = LinearMap.id := by
  ext x i
  fin_cases i <;>
    simp [sharpA52, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]

-- `simp` closes one of the two `fin_cases` branches outright, so the trailing
-- `ring` must tolerate zero remaining goals; the seq-focus linter cannot see
-- that and misfires here.
/-- `B² = 2B`, so every eigenvalue of `B` is `0` or `2`. -/
theorem sharp52_B_sq : sharpB52 ∘ₗ sharpB52 = (2 : ℝ) • sharpB52 := by
  ext x i
  fin_cases i <;>
    simp [sharpB52, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail] <;>
    ring

/-- The eigenvalues of the source's `A` are `1` and `-1`. -/
theorem sharp52_eigenvalue_A {lam : ℝ}
    (h : Module.End.HasEigenvalue sharpA52 lam) : lam = 1 ∨ lam = -1 := by
  obtain ⟨v, hvec⟩ := h.exists_hasEigenvector
  have hv : sharpA52 v = lam • v := hvec.apply_eq_smul
  have hv0 : v ≠ 0 := hvec.2
  have hsq : (lam ^ 2) • v = v := by
    have h1 : sharpA52 (sharpA52 v) = v := congrArg (fun T => T v) sharp52_A_sq
    rw [hv, map_smul, hv, smul_smul] at h1
    rw [sq]
    exact h1
  have hzero : (lam ^ 2 - 1) • v = 0 := by
    rw [sub_smul, hsq, one_smul, sub_self]
  have : lam ^ 2 - 1 = 0 := by
    by_contra hne
    exact hv0 ((smul_eq_zero.mp hzero).resolve_left hne)
  have hfac : (lam - 1) * (lam + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with h1 | h1
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- The eigenvalues of the source's `B` are `0` and `2`. -/
theorem sharp52_eigenvalue_B {mu : ℝ}
    (h : Module.End.HasEigenvalue sharpB52 mu) : mu = 0 ∨ mu = 2 := by
  obtain ⟨v, hvec⟩ := h.exists_hasEigenvector
  have hv : sharpB52 v = mu • v := hvec.apply_eq_smul
  have hv0 : v ≠ 0 := hvec.2
  have hsq : (mu ^ 2) • v = (2 * mu) • v := by
    have h1 : sharpB52 (sharpB52 v) = (2 : ℝ) • sharpB52 v :=
      congrArg (fun T => T v) sharp52_B_sq
    rw [hv, map_smul, hv, smul_smul, smul_smul] at h1
    rw [sq]
    exact h1
  have hzero : (mu ^ 2 - 2 * mu) • v = 0 := by
    rw [sub_smul, hsq, sub_self]
  have : mu ^ 2 - 2 * mu = 0 := by
    by_contra hne
    exact hv0 ((smul_eq_zero.mp hzero).resolve_left hne)
  have hfac : mu * (mu - 2) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (by linarith)

/-- **The witness satisfies the paper's spectral hypothesis with `δ = 1`.** -/
theorem sharp52_gap {lam mu : ℝ}
    (hlam : Module.End.HasEigenvalue sharpA52 lam)
    (hmu : Module.End.HasEigenvalue sharpB52 mu) :
    (1 : ℝ) ≤ |lam - mu| := by
  rcases sharp52_eigenvalue_A hlam with rfl | rfl <;>
    rcases sharp52_eigenvalue_B hmu with rfl | rfl <;> norm_num

/-- **The constant `1` is too small in (5.2).**

`δ ‖X‖₁ = 2 + √10 = 5.16… > 3√2 = 4.24… = ‖AX - XB‖₁` for the source's
`2 × 2` data, so the rank-free inequality `‖C‖₁ ≥ δ‖X‖₁` fails.  With
`rank C = 2` the printed (5.2) survives: `√2 · 3√2 = 6 ≥ 5.16…`. -/
theorem sharp52_constant_one_too_small :
    ‖sharpC52.toContinuousLinearMap‖ < 1 * ‖sharpX52.toContinuousLinearMap‖ := by
  rw [sharp52_opNorm_X, sharp52_opNorm_C, one_mul]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h10 : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (10 : ℝ),
    sharp52_two_le_sqrt_ten]

end Sharpness

end

end ExactSinTheta
end DavisKahan
end TauCeti

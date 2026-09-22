/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.SameSequence
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.FiniteRestriction
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
import Mathlib.Analysis.InnerProductSpace.ProdL2
import LeanPool.DavisKahan.DavisKahan.Sylvester.ScalarTransport
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport

/-!
# Approximation numbers of orthogonal block sums

Davis--Kahan Lemma 6.1 needs a sharp coupling fact: weak singular-value
majorization of two pairs of operators remains true after the pairs are put in
orthogonal blocks.  A triangle inequality loses the theorem's constant and is
not an acceptable substitute.

This file develops the infinite-dimensional version.  The exact Ky Fan prefix of
an orthogonal block sum is identified with the largest split
`Fan r A + Fan (k - r) B`, which is the merge formula for two decreasing
singular-value lists.  No compactness is assumed: the proof rests on three
approximation-number estimates that hold for arbitrary bounded operators,

* `a n A ≤ a n (A ⊕ B)`, by isometric compression to a summand;
* `a (r + s) (A ⊕ B) ≤ max (a r A) (a s B)`, by taking a block-diagonal
  approximant, whose rank is at most `r + s` and whose error norm is the larger
  of the two block errors;
* `min (a i A) (a j B) ≤ a (i + j + 1) (A ⊕ B)`, by the rank-safe min--max
  principle: two independent lower witnesses of dimensions `i + 1` and `j + 1`
  span an `(i + j + 2)`-dimensional witness for the block sum,

together with two elementary greedy interleaving arguments on real sequences.
The third estimate uses the complex Courant--Fischer bridge, so the exact
prefix formula is stated over `ℂ`.  The result is phrased directly for
approximation numbers, hence applies to every Ky-Fan-dominant ideal.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace BigOperators Topology

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]

/-- Continuous orthogonal block sum on Hilbert `L²` products. -/
noncomputable def continuousOrthogonalBlockSum
    {E₀ E₁ F₀ F₁ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    (A : E₀ →L[𝕜] F₀) (B : E₁ →L[𝕜] F₁) :
    WithLp 2 (E₀ × E₁) →L[𝕜] WithLp 2 (F₀ × F₁) :=
  ((WithLp.prodContinuousLinearEquiv 2 𝕜 F₀ F₁).symm :
      (F₀ × F₁) →L[𝕜] WithLp 2 (F₀ × F₁)) ∘L
    (A.prodMap B) ∘L
    ((WithLp.prodContinuousLinearEquiv 2 𝕜 E₀ E₁) :
      WithLp 2 (E₀ × E₁) →L[𝕜] E₀ × E₁)

/-- Pointwise formula for the orthogonal block sum: it acts as `A` on the first
summand and `B` on the second. -/
@[simp]
theorem continuousOrthogonalBlockSum_apply
    {E₀ E₁ F₀ F₁ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    (A : E₀ →L[𝕜] F₀) (B : E₁ →L[𝕜] F₁)
    (x : WithLp 2 (E₀ × E₁)) :
    continuousOrthogonalBlockSum A B x =
      WithLp.toLp 2 (A x.fst, B x.snd) :=
  rfl

/-- A block sum with zero first block keeps only the second block. -/
@[simp]
theorem continuousOrthogonalBlockSum_zero_left
    {E₀ E₁ F₀ F₁ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    (B : E₁ →L[𝕜] F₁) :
    continuousOrthogonalBlockSum (0 : E₀ →L[𝕜] F₀) B =
      ((WithLp.prodContinuousLinearEquiv 2 𝕜 F₀ F₁).symm :
        (F₀ × F₁) →L[𝕜] WithLp 2 (F₀ × F₁)) ∘L
      ((0 : E₀ →L[𝕜] F₀).prodMap B) ∘L
      ((WithLp.prodContinuousLinearEquiv 2 𝕜 E₀ E₁) :
        WithLp 2 (E₀ × E₁) →L[𝕜] E₀ × E₁) :=
  rfl

section Aux

variable {E₀ E₁ F₀ F₁ : Type v}
  [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
  [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]
  [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]

/-- Isometric inclusion of the first summand into the `L²` sum. -/
def blockInl : E₀ →L[𝕜] WithLp 2 (E₀ × E₁) :=
  ((WithLp.prodContinuousLinearEquiv 2 𝕜 E₀ E₁).symm :
      (E₀ × E₁) →L[𝕜] WithLp 2 (E₀ × E₁)) ∘L ContinuousLinearMap.inl 𝕜 E₀ E₁

/-- Isometric inclusion of the second summand into the `L²` sum. -/
def blockInr : E₁ →L[𝕜] WithLp 2 (E₀ × E₁) :=
  ((WithLp.prodContinuousLinearEquiv 2 𝕜 E₀ E₁).symm :
      (E₀ × E₁) →L[𝕜] WithLp 2 (E₀ × E₁)) ∘L ContinuousLinearMap.inr 𝕜 E₀ E₁

omit [CompleteSpace E₀] [CompleteSpace E₁] in
/-- The left inclusion embeds `x` as `(x, 0)`. -/
@[simp]
theorem blockInl_apply (x : E₀) :
    (blockInl (E₁ := E₁) (𝕜 := 𝕜) x) = WithLp.toLp 2 (x, (0 : E₁)) := rfl

omit [CompleteSpace E₀] [CompleteSpace E₁] in
/-- The right inclusion embeds `y` as `(0, y)`. -/
@[simp]
theorem blockInr_apply (y : E₁) :
    (blockInr (E₀ := E₀) (𝕜 := 𝕜) y) = WithLp.toLp 2 ((0 : E₀), y) := rfl

omit [CompleteSpace E₀] [CompleteSpace E₁] in
/-- The left inclusion is norm-nonexpanding — in fact isometric, which is what makes
the block sum orthogonal rather than merely direct. -/
theorem norm_blockInl_le : ‖(blockInl : E₀ →L[𝕜] WithLp 2 (E₀ × E₁))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp

omit [CompleteSpace E₀] [CompleteSpace E₁] in
/-- The right inclusion is norm-nonexpanding. -/
theorem norm_blockInr_le : ‖(blockInr : E₁ →L[𝕜] WithLp 2 (E₀ × E₁))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp

omit [CompleteSpace F₀] [CompleteSpace F₁] in
/-- The first coordinate projection is norm-nonexpanding. -/
theorem norm_fstL_le : ‖(WithLp.fstL 2 𝕜 F₀ F₁)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have h := WithLp.prod_norm_sq_eq_of_L2 x
  have h1 : ‖x.fst‖ ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x.snd‖]
  have h2 : ‖x.fst‖ ≤ ‖x‖ := by
    exact_mod_cast le_of_sq_le_sq h1 (norm_nonneg x)
  simpa using h2

omit [CompleteSpace F₀] [CompleteSpace F₁] in
/-- The second coordinate projection is norm-nonexpanding. -/
theorem norm_sndL_le : ‖(WithLp.sndL 2 𝕜 F₀ F₁)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have h := WithLp.prod_norm_sq_eq_of_L2 x
  have h1 : ‖x.snd‖ ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x.fst‖]
  have h2 : ‖x.snd‖ ≤ ‖x‖ := by
    exact_mod_cast le_of_sq_le_sq h1 (norm_nonneg x)
  simpa using h2

omit [CompleteSpace E₀] [CompleteSpace E₁] [CompleteSpace F₀] [CompleteSpace F₁] in
/-- The first component is recovered from the block sum by an isometric
compression. -/
theorem fstL_comp_blockSum_comp_blockInl (A : E₀ →L[𝕜] F₀) (B : E₁ →L[𝕜] F₁) :
    (WithLp.fstL 2 𝕜 F₀ F₁) ∘L continuousOrthogonalBlockSum A B ∘L
        (blockInl : E₀ →L[𝕜] WithLp 2 (E₀ × E₁)) = A := by
  ext x
  simp

omit [CompleteSpace E₀] [CompleteSpace E₁] [CompleteSpace F₀] [CompleteSpace F₁] in
/-- The second component is recovered from the block sum by an isometric
compression. -/
theorem sndL_comp_blockSum_comp_blockInr (A : E₀ →L[𝕜] F₀) (B : E₁ →L[𝕜] F₁) :
    (WithLp.sndL 2 𝕜 F₀ F₁) ∘L continuousOrthogonalBlockSum A B ∘L
        (blockInr : E₁ →L[𝕜] WithLp 2 (E₀ × E₁)) = B := by
  ext x
  simp

omit [CompleteSpace E₀] [CompleteSpace E₁] [CompleteSpace F₀] [CompleteSpace F₁] in
/-- Every approximation number of a summand is dominated by the corresponding
approximation number of the block sum. -/
theorem approximationNumber_le_blockSum_left
    (A : E₀ →L[𝕜] F₀) (B : E₁ →L[𝕜] F₁) (n : ℕ) :
    A.approximationNumber n ≤
      (continuousOrthogonalBlockSum A B).approximationNumber n := by
  have h := ContinuousLinearMap.approximationNumber_comp_comp_le
    (WithLp.fstL 2 𝕜 F₀ F₁) (continuousOrthogonalBlockSum A B)
    (blockInl : E₀ →L[𝕜] WithLp 2 (E₀ × E₁)) n
  rw [fstL_comp_blockSum_comp_blockInl] at h
  refine h.trans ?_
  calc ‖(WithLp.fstL 2 𝕜 F₀ F₁)‖ *
        (continuousOrthogonalBlockSum A B).approximationNumber n *
        ‖(blockInl : E₀ →L[𝕜] WithLp 2 (E₀ × E₁))‖
      ≤ 1 * (continuousOrthogonalBlockSum A B).approximationNumber n * 1 := by
        gcongr <;>
          first
            | exact norm_fstL_le
            | exact norm_blockInl_le
            | simpa using
                ContinuousLinearMap.approximationNumber_nonneg _ _
    _ = _ := by rw [one_mul, mul_one]

omit [CompleteSpace E₀] [CompleteSpace E₁] [CompleteSpace F₀] [CompleteSpace F₁] in
/-- Every approximation number of the second summand is dominated by the
corresponding approximation number of the block sum. -/
theorem approximationNumber_le_blockSum_right
    (A : E₀ →L[𝕜] F₀) (B : E₁ →L[𝕜] F₁) (n : ℕ) :
    B.approximationNumber n ≤
      (continuousOrthogonalBlockSum A B).approximationNumber n := by
  have h := ContinuousLinearMap.approximationNumber_comp_comp_le
    (WithLp.sndL 2 𝕜 F₀ F₁) (continuousOrthogonalBlockSum A B)
    (blockInr : E₁ →L[𝕜] WithLp 2 (E₀ × E₁)) n
  rw [sndL_comp_blockSum_comp_blockInr] at h
  refine h.trans ?_
  calc ‖(WithLp.sndL 2 𝕜 F₀ F₁)‖ *
        (continuousOrthogonalBlockSum A B).approximationNumber n *
        ‖(blockInr : E₁ →L[𝕜] WithLp 2 (E₀ × E₁))‖
      ≤ 1 * (continuousOrthogonalBlockSum A B).approximationNumber n * 1 := by
        gcongr <;>
          first
            | exact norm_sndL_le
            | exact norm_blockInr_le
            | simpa using
                ContinuousLinearMap.approximationNumber_nonneg _ _
    _ = _ := by rw [one_mul, mul_one]

omit [CompleteSpace E₀] [CompleteSpace E₁] [CompleteSpace F₀] [CompleteSpace F₁] in
/-- The operator norm of a block sum is the larger of the two block norms;
only the upper bound is needed here. -/
theorem norm_continuousOrthogonalBlockSum_le
    (A : E₀ →L[𝕜] F₀) (B : E₁ →L[𝕜] F₁) :
    ‖continuousOrthogonalBlockSum A B‖ ≤ max ‖A‖ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (le_trans (norm_nonneg A) (le_max_left _ _))
  intro x
  have hgoal : ‖continuousOrthogonalBlockSum A B x‖ ≤ (max ‖A‖ ‖B‖) * ‖x‖ := by
    have hM : (0 : ℝ) ≤ max ‖A‖ ‖B‖ := le_trans (norm_nonneg A) (le_max_left _ _)
    have hx := WithLp.prod_norm_sq_eq_of_L2 x
    have hy := WithLp.prod_norm_sq_eq_of_L2 (continuousOrthogonalBlockSum A B x)
    have hfst : ‖(continuousOrthogonalBlockSum A B x).fst‖ ≤ max ‖A‖ ‖B‖ * ‖x.fst‖ := by
      have : ‖A x.fst‖ ≤ ‖A‖ * ‖x.fst‖ := A.le_opNorm _
      have h2 : ‖A‖ * ‖x.fst‖ ≤ max ‖A‖ ‖B‖ * ‖x.fst‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      simpa using this.trans h2
    have hsnd : ‖(continuousOrthogonalBlockSum A B x).snd‖ ≤ max ‖A‖ ‖B‖ * ‖x.snd‖ := by
      have : ‖B x.snd‖ ≤ ‖B‖ * ‖x.snd‖ := B.le_opNorm _
      have h2 : ‖B‖ * ‖x.snd‖ ≤ max ‖A‖ ‖B‖ * ‖x.snd‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
      simpa using this.trans h2
    have hsq : ‖continuousOrthogonalBlockSum A B x‖ ^ 2 ≤ (max ‖A‖ ‖B‖ * ‖x‖) ^ 2 := by
      rw [hy, mul_pow, hx]
      have h1 : ‖(continuousOrthogonalBlockSum A B x).fst‖ ^ 2 ≤
          (max ‖A‖ ‖B‖) ^ 2 * ‖x.fst‖ ^ 2 := by
        have := mul_pow (max ‖A‖ ‖B‖) ‖x.fst‖ 2
        nlinarith [norm_nonneg ((continuousOrthogonalBlockSum A B x).fst),
          norm_nonneg x.fst, hfst, hM]
      have h2 : ‖(continuousOrthogonalBlockSum A B x).snd‖ ^ 2 ≤
          (max ‖A‖ ‖B‖) ^ 2 * ‖x.snd‖ ^ 2 := by
        nlinarith [norm_nonneg ((continuousOrthogonalBlockSum A B x).snd),
          norm_nonneg x.snd, hsnd, hM]
      nlinarith [h1, h2]
    exact le_of_sq_le_sq hsq (mul_nonneg hM (norm_nonneg x))
  exact_mod_cast hgoal

omit [CompleteSpace E₀] [CompleteSpace E₁] [CompleteSpace F₀] [CompleteSpace F₁] in
/-- A block sum splits as a sum of two compressions, one per summand. -/
theorem continuousOrthogonalBlockSum_eq_add
    (R : E₀ →L[𝕜] F₀) (Q : E₁ →L[𝕜] F₁) :
    continuousOrthogonalBlockSum R Q =
      ((blockInl : F₀ →L[𝕜] WithLp 2 (F₀ × F₁)) ∘L R ∘L WithLp.fstL 2 𝕜 E₀ E₁) +
        ((blockInr : F₁ →L[𝕜] WithLp 2 (F₀ × F₁)) ∘L Q ∘L WithLp.sndL 2 𝕜 E₀ E₁) := by
  ext x
  apply WithLp.ofLp_injective 2
  simp

omit [CompleteSpace E₀] [CompleteSpace E₁] [CompleteSpace F₀] [CompleteSpace F₁] in
/-- Difference of block sums is the block sum of the differences. -/
theorem continuousOrthogonalBlockSum_sub
    (A R : E₀ →L[𝕜] F₀) (B Q : E₁ →L[𝕜] F₁) :
    continuousOrthogonalBlockSum A B - continuousOrthogonalBlockSum R Q =
      continuousOrthogonalBlockSum (A - R) (B - Q) := by
  ext x
  apply WithLp.ofLp_injective 2
  simp

omit [CompleteSpace E₀] [CompleteSpace E₁] [CompleteSpace F₀] [CompleteSpace F₁] in
/-- Ranks add across an orthogonal block sum. -/
theorem rank_continuousOrthogonalBlockSum_le
    (R : E₀ →L[𝕜] F₀) (Q : E₁ →L[𝕜] F₁) :
    (continuousOrthogonalBlockSum R Q).rank ≤ R.rank + Q.rank := by
  have hcomp : ∀ {G H : Type v} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
      [NormedAddCommGroup H] [NormedSpace 𝕜 H]
      {X Y : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
      (L : H →L[𝕜] Y) (T : G →L[𝕜] H) (M : X →L[𝕜] G),
      (L ∘L T ∘L M).rank ≤ T.rank := by
    intro G H _ _ _ _ X Y _ _ _ _ L T M
    change LinearMap.rank (L.toLinearMap ∘ₗ (T.toLinearMap ∘ₗ M.toLinearMap)) ≤
      LinearMap.rank T.toLinearMap
    exact (LinearMap.rank_comp_le_right _ _).trans (LinearMap.rank_comp_le_left _ _)
  rw [continuousOrthogonalBlockSum_eq_add]
  refine (LinearMap.rank_add_le _ _).trans ?_
  exact add_le_add (hcomp _ _ _) (hcomp _ _ _)

/-- Sharp interleaving bound: an allocation of `r` ranks to the first block and
`s` to the second bounds the `(r + s)`-th approximation number of the block sum
by the larger of the two block approximation numbers. -/
theorem approximationNumber_continuousOrthogonalBlockSum_le_max
    (A : E₀ →L[𝕜] F₀) (B : E₁ →L[𝕜] F₁) (r s : ℕ) :
    (continuousOrthogonalBlockSum A B).approximationNumber (r + s) ≤
      max (A.approximationNumber r) (B.approximationNumber s) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨R, hRrank, hRdist⟩ := A.exists_rank_le_norm_sub_lt_approximationNumber_add r hε
  obtain ⟨Q, hQrank, hQdist⟩ := B.exists_rank_le_norm_sub_lt_approximationNumber_add s hε
  have hrank : (continuousOrthogonalBlockSum R Q).rank ≤ ((r + s : ℕ) : Cardinal) := by
    calc (continuousOrthogonalBlockSum R Q).rank ≤ R.rank + Q.rank :=
          rank_continuousOrthogonalBlockSum_le R Q
      _ ≤ (r : Cardinal) + (s : Cardinal) := add_le_add hRrank hQrank
      _ = ((r + s : ℕ) : Cardinal) := by norm_cast
  refine le_trans
    ((continuousOrthogonalBlockSum A B).approximationNumber_le_norm_sub hrank) ?_
  rw [continuousOrthogonalBlockSum_sub]
  refine le_trans (norm_continuousOrthogonalBlockSum_le (A - R) (B - Q)) ?_
  refine max_le ?_ ?_
  · exact le_trans hRdist.le (add_le_add (le_max_left _ _) le_rfl)
  · exact le_trans hQdist.le (add_le_add (le_max_right _ _) le_rfl)

section ScalarMinMax

variable {E₀ E₁ F₀ F₁ : Type v}
  [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
  [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]
  [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]

/-- Sharp interleaving lower bound: two independent lower witnesses of sizes
`i + 1` and `j + 1` combine into an `(i + j + 2)`-dimensional witness for the
block sum. -/
theorem min_le_approximationNumber_continuousOrthogonalBlockSum
    (A : E₀ →L[𝕜] F₀) (B : E₁ →L[𝕜] F₁) (i j : ℕ) :
    min (A.approximationNumber i) (B.approximationNumber j) ≤
      (continuousOrthogonalBlockSum A B).approximationNumber (i + j + 1) := by
  classical
  by_contra hcon
  push Not at hcon
  set T := continuousOrthogonalBlockSum A B with hT
  set m : ℝ := T.approximationNumber (i + j + 1) with hm
  have hm0 : 0 ≤ m := T.approximationNumber_nonneg (i + j + 1)
  have hmA : m < A.approximationNumber i := by
    have := lt_of_lt_of_le hcon (min_le_left _ _)
    exact_mod_cast this
  have hmB : m < B.approximationNumber j := by
    have := lt_of_lt_of_le hcon (min_le_right _ _)
    exact_mod_cast this
  obtain ⟨s, hms, v, hv, hV⟩ :=
    ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.out A i hm0 hmA
  obtain ⟨t, hmt, w, hw, hW⟩ :=
    ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.out B j hm0 hmB
  -- the combined witness family
  set f : Fin (i + 1) → WithLp 2 (E₀ × E₁) := fun k => WithLp.toLp 2 (v k, 0) with hf
  set g : Fin (j + 1) → WithLp 2 (E₀ × E₁) := fun l => WithLp.toLp 2 (0, w l) with hg
  set e : Fin (i + j + 1 + 1) ≃ (Fin (i + 1) ⊕ Fin (j + 1)) :=
    (finCongr (by omega)).trans finSumFinEquiv.symm with he
  set V : Submodule 𝕜 E₀ := Submodule.span 𝕜 (Set.range v) with hVdef
  set W : Submodule 𝕜 E₁ := Submodule.span 𝕜 (Set.range w) with hWdef
  set P : Submodule 𝕜 (WithLp 2 (E₀ × E₁)) :=
    (V.comap (WithLp.fstL 2 𝕜 E₀ E₁).toLinearMap) ⊓
      (W.comap (WithLp.sndL 2 𝕜 E₀ E₁).toLinearMap) with hP
  -- linear independence of the two embedded families
  have hfindep : LinearIndependent 𝕜 f :=
    hv.map' (blockInl : E₀ →L[𝕜] WithLp 2 (E₀ × E₁)).toLinearMap
      (by
        rw [LinearMap.ker_eq_bot]
        intro a b hab
        have : WithLp.toLp 2 (a, (0 : E₁)) = WithLp.toLp 2 (b, (0 : E₁)) := hab
        simpa using congrArg (fun z => (WithLp.ofLp z).1) this)
  have hgindep : LinearIndependent 𝕜 g :=
    hw.map' (blockInr : E₁ →L[𝕜] WithLp 2 (E₀ × E₁)).toLinearMap
      (by
        rw [LinearMap.ker_eq_bot]
        intro a b hab
        have : WithLp.toLp 2 ((0 : E₀), a) = WithLp.toLp 2 ((0 : E₀), b) := hab
        simpa using congrArg (fun z => (WithLp.ofLp z).2) this)
  have hfker : Submodule.span 𝕜 (Set.range f) ≤
      LinearMap.ker (WithLp.sndL 2 𝕜 E₀ E₁).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    simp [hf, LinearMap.mem_ker]
  have hgker : Submodule.span 𝕜 (Set.range g) ≤
      LinearMap.ker (WithLp.fstL 2 𝕜 E₀ E₁).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    simp [hg, LinearMap.mem_ker]
  have hdisj : Disjoint (Submodule.span 𝕜 (Set.range f))
      (Submodule.span 𝕜 (Set.range g)) := by
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    have h1 : (WithLp.ofLp x).2 = 0 := hfker hx1
    have h2 : (WithLp.ofLp x).1 = 0 := hgker hx2
    apply WithLp.ofLp_injective 2
    exact Prod.ext (by simpa using h2) (by simpa using h1)
  have hsum : LinearIndependent 𝕜 (Sum.elim f g) := hfindep.sum_type hgindep hdisj
  have hu : LinearIndependent 𝕜 (fun k => Sum.elim f g (e k)) :=
    hsum.comp e e.injective
  -- the span of the combined family lies in the product subspace
  have hrange : Set.range (fun k => Sum.elim f g (e k)) = Set.range (Sum.elim f g) :=
    e.surjective.range_comp _
  have hspan : Submodule.span 𝕜 (Set.range (fun k => Sum.elim f g (e k))) ≤ P := by
    rw [hrange, Set.Sum.elim_range, Submodule.span_union]
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa [hf, hVdef] using Submodule.subset_span (Set.mem_range_self k)
      · simp [hf]
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      refine ⟨?_, ?_⟩
      · simp [hg]
      · simpa [hg, hWdef] using Submodule.subset_span (Set.mem_range_self l)
  -- uniform lower modulus on that span
  set μ : ℝ := min s t with hμ
  have hmμ : m < μ := lt_min hms hmt
  have hμ0 : 0 ≤ μ := hm0.trans hmμ.le
  have hlower : ∀ x ∈ Submodule.span 𝕜 (Set.range (fun k => Sum.elim f g (e k))),
      μ * ‖x‖ ≤ ‖T x‖ := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hspan hx
    have hxV : (WithLp.ofLp x).1 ∈ V := hx1
    have hxW : (WithLp.ofLp x).2 ∈ W := hx2
    have hA1 : s * ‖(WithLp.ofLp x).1‖ ≤ ‖A (WithLp.ofLp x).1‖ := hV _ hxV
    have hB1 : t * ‖(WithLp.ofLp x).2‖ ≤ ‖B (WithLp.ofLp x).2‖ := hW _ hxW
    have hμs : μ ≤ s := min_le_left _ _
    have hμt : μ ≤ t := min_le_right _ _
    have hA2 : μ * ‖(WithLp.ofLp x).1‖ ≤ ‖A (WithLp.ofLp x).1‖ :=
      le_trans (mul_le_mul_of_nonneg_right hμs (norm_nonneg _)) hA1
    have hB2 : μ * ‖(WithLp.ofLp x).2‖ ≤ ‖B (WithLp.ofLp x).2‖ :=
      le_trans (mul_le_mul_of_nonneg_right hμt (norm_nonneg _)) hB1
    have hxsq := WithLp.prod_norm_sq_eq_of_L2 x
    have hysq := WithLp.prod_norm_sq_eq_of_L2 (T x)
    have hTfst : (T x).fst = A (WithLp.ofLp x).1 := rfl
    have hTsnd : (T x).snd = B (WithLp.ofLp x).2 := rfl
    have hsq : (μ * ‖x‖) ^ 2 ≤ ‖T x‖ ^ 2 := by
      rw [hysq, hTfst, hTsnd, mul_pow, hxsq]
      have e1 : (μ * ‖(WithLp.ofLp x).1‖) ^ 2 ≤ ‖A (WithLp.ofLp x).1‖ ^ 2 := by
        apply pow_le_pow_left₀ (mul_nonneg hμ0 (norm_nonneg _)) hA2
      have e2 : (μ * ‖(WithLp.ofLp x).2‖) ^ 2 ≤ ‖B (WithLp.ofLp x).2‖ ^ 2 := by
        apply pow_le_pow_left₀ (mul_nonneg hμ0 (norm_nonneg _)) hB2
      have hx1n : ‖x.fst‖ = ‖(WithLp.ofLp x).1‖ := rfl
      have hx2n : ‖x.snd‖ = ‖(WithLp.ofLp x).2‖ := rfl
      rw [hx1n, hx2n]
      nlinarith [e1, e2, mul_pow μ ‖(WithLp.ofLp x).1‖ 2,
        mul_pow μ ‖(WithLp.ofLp x).2‖ 2]
    exact le_of_sq_le_sq hsq (norm_nonneg _)
  have hfinal : m < (T.approximationNumber (i + j + 1) : ℝ) :=
    (ContinuousLinearMap.HasMinMaxLowerBound.lt_approximationNumber_iff_exists_finiteDimensional_lowerBound
      ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.out
      T (i + j + 1) hm0).mpr ⟨μ, hmμ, _, hu, hlower⟩
  exact absurd hfinal (by rw [← hm]; exact lt_irrefl m)

end ScalarMinMax

section MergeCombinatorics

/-- Greedy interleaving: a `k`-term prefix of the merged sequence is dominated
by some split of the two source prefixes. -/
theorem exists_split_prefix_sum_le (a b c : ℕ → ℝ)
    (hc : ∀ r s, c (r + s) ≤ max (a r) (b s)) (k : ℕ) :
    ∃ r ≤ k, ∑ n ∈ Finset.range k, c n ≤
      (∑ n ∈ Finset.range r, a n) + ∑ n ∈ Finset.range (k - r), b n := by
  induction k with
  | zero => exact ⟨0, le_rfl, by simp⟩
  | succ k ih =>
    obtain ⟨r, hrk, hle⟩ := ih
    have hsplit := hc r (k - r)
    rw [Nat.add_sub_cancel' hrk] at hsplit
    rcases le_total (a r) (b (k - r)) with h | h
    · refine ⟨r, hrk.trans (Nat.le_succ k), ?_⟩
      have hck : c k ≤ b (k - r) := hsplit.trans_eq (max_eq_right h)
      have hks : k + 1 - r = (k - r) + 1 := by omega
      rw [Finset.sum_range_succ, hks, Finset.sum_range_succ]
      linarith
    · refine ⟨r + 1, by omega, ?_⟩
      have hck : c k ≤ a r := hsplit.trans_eq (max_eq_left h)
      have hks : k + 1 - (r + 1) = k - r := by omega
      rw [Finset.sum_range_succ, hks, Finset.sum_range_succ]
      linarith

/-- Every split of the two source prefixes is dominated by the merged prefix. -/
theorem split_prefix_sum_le (a b c : ℕ → ℝ)
    (ha : ∀ n, a n ≤ c n) (hb : ∀ n, b n ≤ c n)
    (hmin : ∀ i j, min (a i) (b j) ≤ c (i + j + 1)) :
    ∀ k r s, r + s = k →
      (∑ n ∈ Finset.range r, a n) + ∑ n ∈ Finset.range s, b n ≤
        ∑ n ∈ Finset.range k, c n := by
  intro k
  induction k with
  | zero =>
    intro r s hrs
    obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.mp hrs
    simp
  | succ k ih =>
    intro r s hrs
    match r, s with
    | 0, s =>
      have hsk : s = k + 1 := by omega
      subst hsk
      simp only [Finset.range_zero, Finset.sum_empty, zero_add]
      exact Finset.sum_le_sum fun n _ => hb n
    | (r + 1), 0 =>
      have hrk : r + 1 = k + 1 := by omega
      rw [hrk]
      simp only [Finset.range_zero, Finset.sum_empty, add_zero]
      exact Finset.sum_le_sum fun n _ => ha n
    | (r + 1), (s + 1) =>
      have hk : k = r + s + 1 := by omega
      have hmm := hmin r s
      rw [← hk] at hmm
      rcases le_total (a r) (b s) with h | h
      · have hck : a r ≤ c k := (min_eq_left h).symm.trans_le hmm
        have hIH := ih r (s + 1) (by omega)
        rw [Finset.sum_range_succ (f := a) (n := r), Finset.sum_range_succ (f := c) (n := k)]
        linarith
      · have hck : b s ≤ c k := (min_eq_right h).symm.trans_le hmm
        have hIH := ih (r + 1) s (by omega)
        rw [Finset.sum_range_succ (f := b) (n := s), Finset.sum_range_succ (f := c) (n := k)]
        linarith

end MergeCombinatorics

end Aux

/-- The split-prefix functional for two singular-value sequences. -/
def splitKyFanGauge
    {E₀ E₁ F₀ F₁ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    (k : ℕ) (A : E₀ →L[𝕜] F₀) (B : E₁ →L[𝕜] F₁) : ℝ :=
  Finset.sup' (Finset.range (k + 1)) (by simp)
    (fun r => kyFanApproximationGauge r A +
      kyFanApproximationGauge (k - r) B)

/-- Monotonicity of the split-prefix functional.  The two pairs are allowed to
live in different coordinate spaces, since only the two scalar Ky Fan
sequences enter the definition. -/
theorem splitKyFanGauge_mono
    {E₀ E₁ F₀ F₁ E₀' E₁' F₀' F₁' : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    [NormedAddCommGroup E₀'] [InnerProductSpace 𝕜 E₀']
    [NormedAddCommGroup E₁'] [InnerProductSpace 𝕜 E₁']
    [NormedAddCommGroup F₀'] [InnerProductSpace 𝕜 F₀']
    [NormedAddCommGroup F₁'] [InnerProductSpace 𝕜 F₁']
    {A : E₀ →L[𝕜] F₀} {C : E₀' →L[𝕜] F₀'}
    {B : E₁ →L[𝕜] F₁} {D : E₁' →L[𝕜] F₁'}
    (hA : ∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k C)
    (hB : ∀ k, kyFanApproximationGauge k B ≤ kyFanApproximationGauge k D)
    (k : ℕ) : splitKyFanGauge k A B ≤ splitKyFanGauge k C D := by
  unfold splitKyFanGauge
  apply Finset.sup'_le
  intro r hr
  refine le_trans (add_le_add (hA r) (hB (k - r))) ?_
  exact Finset.le_sup'
    (f := fun s => kyFanApproximationGauge s C +
      kyFanApproximationGauge (k - s) D) hr

/-- Exact Ky Fan prefix formula for an orthogonal block sum.

The finite-dimensional statement is the merge formula for two decreasing
singular-value lists.  In arbitrary Hilbert spaces, finite Ky Fan prefixes are
localized to finite-dimensional compressions by the exact approximation-number
min--max theorem, and the finite result is passed to the limit. -/
theorem kyFanApproximationGauge_continuousOrthogonalBlockSum
    {E₀ E₁ F₀ F₁ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
    (k : ℕ) (A : E₀ →L[𝕜] F₀) (B : E₁ →L[𝕜] F₁) :
    kyFanApproximationGauge k (continuousOrthogonalBlockSum A B) =
      splitKyFanGauge k A B := by
  classical
  set a : ℕ → ℝ := fun n => approximationSingularValue n A with ha
  set b : ℕ → ℝ := fun n => approximationSingularValue n B with hb
  set c : ℕ → ℝ := fun n =>
    approximationSingularValue n (continuousOrthogonalBlockSum A B) with hcdef
  have hac : ∀ n, a n ≤ c n := fun n => by
    have := approximationNumber_le_blockSum_left A B n
    exact_mod_cast this
  have hbc : ∀ n, b n ≤ c n := fun n => by
    have := approximationNumber_le_blockSum_right A B n
    exact_mod_cast this
  have hmax : ∀ r s, c (r + s) ≤ max (a r) (b s) := fun r s => by
    have := approximationNumber_continuousOrthogonalBlockSum_le_max A B r s
    exact_mod_cast this
  have hmin : ∀ i j, min (a i) (b j) ≤ c (i + j + 1) := fun i j => by
    have := min_le_approximationNumber_continuousOrthogonalBlockSum A B i j
    exact_mod_cast this
  apply le_antisymm
  · -- Upper bound: greedily allocate each merged singular value to whichever
    -- block currently supplies the larger one.  The resulting allocation is a
    -- split of `k` into `r` and `k - r`, hence one of the candidates.
    obtain ⟨r, hrk, hle⟩ := exists_split_prefix_sum_le a b c hmax k
    refine le_trans hle ?_
    exact Finset.le_sup'
      (f := fun r => kyFanApproximationGauge r A + kyFanApproximationGauge (k - r) B)
      (Finset.mem_range.mpr (by omega))
  · -- Lower bound: for each split, the two component witnesses combine into an
    -- orthogonal witness for the block prefix.
    unfold splitKyFanGauge
    apply Finset.sup'_le
    intro r hr
    have hrle : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    exact split_prefix_sum_le a b c hac hbc hmin k r (k - r) (by omega)

/-- Weak majorization is stable under orthogonal block sum.  This is the
infinite-dimensional singular-value content of Davis--Kahan Lemma 6.1. -/
theorem kyFanApproximationGauge_blockSum_le
    {E₀ E₁ F₀ F₁ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
    {A C : E₀ →L[𝕜] F₀} {B D : E₁ →L[𝕜] F₁}
    (hA : ∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k C)
    (hB : ∀ k, kyFanApproximationGauge k B ≤ kyFanApproximationGauge k D) :
    ∀ k, kyFanApproximationGauge k (continuousOrthogonalBlockSum A B) ≤
      kyFanApproximationGauge k (continuousOrthogonalBlockSum C D) := by
  intro k
  rw [kyFanApproximationGauge_continuousOrthogonalBlockSum,
    kyFanApproximationGauge_continuousOrthogonalBlockSum]
  exact splitKyFanGauge_mono hA hB k

/-- Recover one approximation singular value from two consecutive Ky Fan
prefixes. -/
theorem approximationSingularValue_eq_kyFan_succ_sub
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (n : ℕ) (A : E →L[𝕜] F) :
    A.approximationNumber n =
      kyFanApproximationGauge (n + 1) A - kyFanApproximationGauge n A := by
  unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
  rw [Finset.sum_range_succ]
  simp []

/-- Orthogonal block sums preserve complete singular-value equality component
by component. -/
theorem hasSameApproximationNumbers_continuousOrthogonalBlockSum
    {E₀ E₁ F₀ F₁ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
    {A C : E₀ →L[𝕜] F₀} {B D : E₁ →L[𝕜] F₁}
    (hA : ContinuousLinearMap.HasSameApproximationNumbers A C)
    (hB : ContinuousLinearMap.HasSameApproximationNumbers B D) :
    ContinuousLinearMap.HasSameApproximationNumbers
      (continuousOrthogonalBlockSum A B)
      (continuousOrthogonalBlockSum C D) := by
  intro n
  rw [approximationSingularValue_eq_kyFan_succ_sub,
    approximationSingularValue_eq_kyFan_succ_sub]
  congr 1 <;>
    rw [kyFanApproximationGauge_continuousOrthogonalBlockSum,
      kyFanApproximationGauge_continuousOrthogonalBlockSum] <;>
    apply le_antisymm
  · exact splitKyFanGauge_mono
      (fun k => le_of_eq (hA.kyFanGauge_eq k))
      (fun k => le_of_eq (hB.kyFanGauge_eq k)) _
  · exact splitKyFanGauge_mono
      (fun k => le_of_eq (hA.kyFanGauge_eq k).symm)
      (fun k => le_of_eq (hB.kyFanGauge_eq k).symm) _
  · exact splitKyFanGauge_mono
      (fun k => le_of_eq (hA.kyFanGauge_eq k))
      (fun k => le_of_eq (hB.kyFanGauge_eq k)) _
  · exact splitKyFanGauge_mono
      (fun k => le_of_eq (hA.kyFanGauge_eq k).symm)
      (fun k => le_of_eq (hB.kyFanGauge_eq k).symm) _


/-- Heterogeneous version: orthogonal block sums preserve complete singular
sequences even when the source and target coordinate spaces differ. -/
theorem sameApproximationSingularSequence_continuousOrthogonalBlockSum
    {E₀ E₁ F₀ F₁ E₀' E₁' F₀' F₁' : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
    [NormedAddCommGroup E₀'] [InnerProductSpace 𝕜 E₀'] [CompleteSpace E₀']
    [NormedAddCommGroup E₁'] [InnerProductSpace 𝕜 E₁'] [CompleteSpace E₁']
    [NormedAddCommGroup F₀'] [InnerProductSpace 𝕜 F₀'] [CompleteSpace F₀']
    [NormedAddCommGroup F₁'] [InnerProductSpace 𝕜 F₁'] [CompleteSpace F₁']
    {A : E₀ →L[𝕜] F₀} {B : E₁ →L[𝕜] F₁}
    {C : E₀' →L[𝕜] F₀'} {D : E₁' →L[𝕜] F₁'}
    (hA : ContinuousLinearMap.HasSameApproximationNumbers A C)
    (hB : ContinuousLinearMap.HasSameApproximationNumbers B D) :
    ContinuousLinearMap.HasSameApproximationNumbers
      (continuousOrthogonalBlockSum A B)
      (continuousOrthogonalBlockSum C D) := by
  intro n
  rw [approximationSingularValue_eq_kyFan_succ_sub,
    approximationSingularValue_eq_kyFan_succ_sub,
    kyFanApproximationGauge_continuousOrthogonalBlockSum,
    kyFanApproximationGauge_continuousOrthogonalBlockSum,
    kyFanApproximationGauge_continuousOrthogonalBlockSum,
    kyFanApproximationGauge_continuousOrthogonalBlockSum]
  congr 1 <;> apply le_antisymm
  · exact splitKyFanGauge_mono
      (fun k => le_of_eq (hA.kyFanGauge_eq k))
      (fun k => le_of_eq (hB.kyFanGauge_eq k)) _
  · exact splitKyFanGauge_mono
      (fun k => le_of_eq (hA.kyFanGauge_eq k).symm)
      (fun k => le_of_eq (hB.kyFanGauge_eq k).symm) _
  · exact splitKyFanGauge_mono
      (fun k => le_of_eq (hA.kyFanGauge_eq k))
      (fun k => le_of_eq (hB.kyFanGauge_eq k)) _
  · exact splitKyFanGauge_mono
      (fun k => le_of_eq (hA.kyFanGauge_eq k).symm)
      (fun k => le_of_eq (hB.kyFanGauge_eq k).symm) _

section PinchChart

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **The pinch of `A` relative to `U ⊕ Uᗮ`, charted as an orthogonal block sum.**

`Submodule.diagonalPart` discards the off-diagonal blocks but keeps the operator on the
ambient space `H`.  Read through Mathlib's isometric decomposition
`H ≃ₗᵢ WithLp 2 (U × Uᗮ)` it becomes literally the block sum of the two compressions,
which is the form the exact Ky Fan prefix formula
`kyFanApproximationGauge_continuousOrthogonalBlockSum` consumes.  Together with
`TauCeti.ApproximationNumber.kyFanApproximationGauge_conj_eq_complex` — the gauge is unchanged by
conjugation with a contraction pair — this is what turns a statement about the two
*restricted* displacements into one about the full displacement, which is Davis--Kahan
Proposition 4.3's route.

The proof is pointwise and immediate: on `toLp (u, u')` the two star projections select
`u` and `u'`, so the diagonal part returns `P_U A u + P_Uᗮ A u'`, whose chart is the pair
`(Π_U A u, Π_Uᗮ A u')`. -/
theorem orthogonalDecomposition_conj_diagonalPart
    (U : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    (A : H →L[𝕜] H) :
    (U.orthogonalDecomposition : H →L[𝕜] WithLp 2 (U × Uᗮ)) ∘L U.diagonalPart A ∘L
        (U.orthogonalDecomposition.symm : WithLp 2 (U × Uᗮ) →L[𝕜] H) =
      continuousOrthogonalBlockSum (U.orthogonalProjectionOnto ∘L A ∘L U.subtypeL)
        (Uᗮ.orthogonalProjectionOnto ∘L A ∘L Uᗮ.subtypeL) := by
  have hUU : ∀ z : H, U.orthogonalProjectionOnto (U.starProjection z) =
      U.orthogonalProjectionOnto z := by
    intro z
    apply Subtype.ext
    rw [Submodule.coe_orthogonalProjectionOnto_apply,
      Submodule.coe_orthogonalProjectionOnto_apply,
      Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem z)]
  have hOO : ∀ z : H, Uᗮ.orthogonalProjectionOnto (Uᗮ.starProjection z) =
      Uᗮ.orthogonalProjectionOnto z := by
    intro z
    apply Subtype.ext
    rw [Submodule.coe_orthogonalProjectionOnto_apply,
      Submodule.coe_orthogonalProjectionOnto_apply,
      Submodule.starProjection_eq_self_iff.mpr (Uᗮ.starProjection_apply_mem z)]
  have hUO : ∀ z : H, U.orthogonalProjectionOnto (Uᗮ.starProjection z) = 0 := fun z =>
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr (Uᗮ.starProjection_apply_mem z)
  have hOU : ∀ z : H, Uᗮ.orthogonalProjectionOnto (U.starProjection z) = 0 := fun z =>
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
      (U.le_orthogonal_orthogonal (U.starProjection_apply_mem z))
  ext w
  have hsymmcoe : ((U.orthogonalDecomposition.symm : WithLp 2 (U × Uᗮ) →L[𝕜] H)) w =
      (w.fst : H) + (w.snd : H) := Submodule.orthogonalDecomposition_symm_apply U w
  have hcoe : ∀ z : H, ((U.orthogonalDecomposition : H →L[𝕜] WithLp 2 (U × Uᗮ))) z =
      WithLp.toLp 2 (U.orthogonalProjectionOnto z, Uᗮ.orthogonalProjectionOnto z) :=
    fun z => Submodule.orthogonalDecomposition_apply U z
  have hfst : U.starProjection ((w.fst : H) + (w.snd : H)) = (w.fst : H) := by
    rw [map_add, Submodule.starProjection_eq_self_iff.mpr w.fst.2]
    have hz : U.starProjection ((w.snd : H)) = 0 := by
      have h0 : U.orthogonalProjectionOnto ((w.snd : H)) = 0 :=
        Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr w.snd.2
      rw [← Submodule.coe_orthogonalProjectionOnto_apply, h0]
      rfl
    rw [hz, add_zero]
  have hsnd : Uᗮ.starProjection ((w.fst : H) + (w.snd : H)) = (w.snd : H) := by
    rw [map_add, Submodule.starProjection_eq_self_iff.mpr w.snd.2]
    have hz : Uᗮ.starProjection ((w.fst : H)) = 0 := by
      have h0 : Uᗮ.orthogonalProjectionOnto ((w.fst : H)) = 0 :=
        Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
          (U.le_orthogonal_orthogonal w.fst.2)
      rw [← Submodule.coe_orthogonalProjectionOnto_apply, h0]
      rfl
    rw [hz, zero_add]
  have hdiag : U.diagonalPart A ((w.fst : H) + (w.snd : H)) =
      U.starProjection (A (w.fst : H)) + Uᗮ.starProjection (A (w.snd : H)) := by
    simp only [Submodule.diagonalPart, add_apply, ContinuousLinearMap.comp_apply]
    rw [hfst, hsnd]
  simp only [ContinuousLinearMap.comp_apply, hsymmcoe, hdiag, hcoe,
    continuousOrthogonalBlockSum_apply]
  refine congrArg (WithLp.toLp 2) (Prod.ext ?_ ?_)
  · simp only [map_add, hUU, hUO, add_zero]
    rfl
  · simp only [map_add, hOO, hOU, zero_add]
    rfl

end PinchChart

end

end ExactSinTheta
end DavisKahan
end TauCeti

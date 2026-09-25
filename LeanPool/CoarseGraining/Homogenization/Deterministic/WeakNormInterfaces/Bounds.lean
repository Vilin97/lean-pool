/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfaces.Definitions
public import LeanPool.CoarseGraining.Homogenization.Multiscale.CubeAverage

/-! # Bounds -/

@[expose] public section

namespace Homogenization

noncomputable section

theorem descendantsAverage_four_mul_sum_vecNormSq_cubeAverageVec_eq {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (u₁ u₂ u₃ u₄ : Vec d → Vec d) :
    descendantsAverage Q j
        (fun R =>
          4 *
            (vecNormSq (cubeAverageVec R u₁) + vecNormSq (cubeAverageVec R u₂) +
              vecNormSq (cubeAverageVec R u₃) + vecNormSq (cubeAverageVec R u₄))) =
      4 *
        (cubeBesovNegativeVectorDepthAverage Q u₁ j +
          cubeBesovNegativeVectorDepthAverage Q u₂ j +
          cubeBesovNegativeVectorDepthAverage Q u₃ j +
          cubeBesovNegativeVectorDepthAverage Q u₄ j) := by
  simpa [cubeBesovNegativeVectorDepthAverage] using
    descendantsAverage_four_mul_sum_vecNormSq_eq Q j
      (fun R => cubeAverageVec R u₁) (fun R => cubeAverageVec R u₂)
      (fun R => cubeAverageVec R u₃) (fun R => cubeAverageVec R u₄)

/--
Depthwise weighted weak-norm split for cube-indexed pieces. This is the
form used by the Section 5.3 analytic estimates before the predictor,
additivity, low-scale, and tail contributions have been represented as global
vector fields.
-/
theorem cubeBesovNegativeVectorDepthSeminorm_le_two_mul_sum_of_cubeTerms_eq
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ)
    (predictor additivity lowScale tail : TriadicCube d → Vec d)
    (hdecomp : ∀ R ∈ descendantsAtDepth Q j,
      cubeAverageVec R u =
        predictor R + additivity R + lowScale R + tail R) :
    cubeBesovNegativeVectorDepthSeminorm Q s u j ≤
      2 *
        (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            Real.sqrt (descendantsAverage Q j fun R => vecNormSq (predictor R)) +
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            Real.sqrt (descendantsAverage Q j fun R => vecNormSq (additivity R)) +
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            Real.sqrt (descendantsAverage Q j fun R => vecNormSq (lowScale R)) +
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            Real.sqrt (descendantsAverage Q j fun R => vecNormSq (tail R))) := by
  let A₁ := descendantsAverage Q j fun R => vecNormSq (predictor R)
  let A₂ := descendantsAverage Q j fun R => vecNormSq (additivity R)
  let A₃ := descendantsAverage Q j fun R => vecNormSq (lowScale R)
  let A₄ := descendantsAverage Q j fun R => vecNormSq (tail R)
  have hA₁ : 0 ≤ A₁ := by
    simpa [A₁] using descendantsAverage_vecNormSq_nonneg Q j predictor
  have hA₂ : 0 ≤ A₂ := by
    simpa [A₂] using descendantsAverage_vecNormSq_nonneg Q j additivity
  have hA₃ : 0 ≤ A₃ := by
    simpa [A₃] using descendantsAverage_vecNormSq_nonneg Q j lowScale
  have hA₄ : 0 ≤ A₄ := by
    simpa [A₄] using descendantsAverage_vecNormSq_nonneg Q j tail
  have hdepth :
      cubeBesovNegativeVectorDepthAverage Q u j ≤ 4 * (A₁ + A₂ + A₃ + A₄) := by
    have hsplit :=
      cubeBesovNegativeVectorDepthAverage_le_four_mul_sum_of_cubeAverageVec_eq
        Q u j predictor additivity lowScale tail hdecomp
    have hrewrite :
        descendantsAverage Q j
            (fun R =>
              4 *
                (vecNormSq (predictor R) + vecNormSq (additivity R) +
                  vecNormSq (lowScale R) + vecNormSq (tail R))) =
          4 * (A₁ + A₂ + A₃ + A₄) := by
      simpa [A₁, A₂, A₃, A₄] using
        descendantsAverage_four_mul_sum_vecNormSq_eq
          Q j predictor additivity lowScale tail
    exact hsplit.trans_eq hrewrite
  have hsqrt :
      Real.sqrt (cubeBesovNegativeVectorDepthAverage Q u j) ≤
        2 * (Real.sqrt A₁ + Real.sqrt A₂ + Real.sqrt A₃ + Real.sqrt A₄) :=
    (Real.sqrt_le_sqrt hdepth).trans
      (sqrt_four_mul_sum_le_two_mul_sum_sqrt hA₁ hA₂ hA₃ hA₄)
  have hweight_nonneg :
      0 ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  unfold cubeBesovNegativeVectorDepthSeminorm
  calc
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        Real.sqrt (cubeBesovNegativeVectorDepthAverage Q u j)
        ≤
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            (2 * (Real.sqrt A₁ + Real.sqrt A₂ + Real.sqrt A₃ + Real.sqrt A₄)) := by
          exact mul_le_mul_of_nonneg_left hsqrt hweight_nonneg
    _ =
      2 *
        (Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt A₁ +
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt A₂ +
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt A₃ +
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt A₄) := by
          ring

/--
Low-scale constant-tail split at one depth. If the descendant averages of `w`
are the averages of `u` plus a fixed vector `c`, then the depth contribution
of `w` is bounded by the depth contribution of `u` plus the constant tail.
-/
theorem cubeBesovNegativeVectorDepthSeminorm_le_two_mul_self_add_const_of_cubeAverageVec_eq
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (j : ℕ)
    (w u : Vec d → Vec d) (c : Vec d)
    (hdecomp : ∀ R ∈ descendantsAtDepth Q j,
      cubeAverageVec R w = cubeAverageVec R u + c) :
    cubeBesovNegativeVectorDepthSeminorm Q s w j ≤
      2 *
        (cubeBesovNegativeVectorDepthSeminorm Q s u j +
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt (vecNormSq c)) := by
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  let A : ℝ := cubeBesovNegativeVectorDepthAverage Q u j
  let B : ℝ := vecNormSq c
  have hA : 0 ≤ A := by
    simpa [A] using cubeBesovNegativeVectorDepthAverage_nonneg Q u j
  have hB : 0 ≤ B := by
    simpa [B] using vecNormSq_nonneg c
  have havg :
      cubeBesovNegativeVectorDepthAverage Q w j ≤ 2 * (A + B) := by
    have hcard : ((D.card : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q j))
    unfold cubeBesovNegativeVectorDepthAverage descendantsAverage
    change
      ((D.card : ℝ)⁻¹) * ∑ R ∈ D, vecNormSq (cubeAverageVec R w) ≤
        2 *
          (((D.card : ℝ)⁻¹) * ∑ R ∈ D, vecNormSq (cubeAverageVec R u) +
            vecNormSq c)
    calc
      ((D.card : ℝ)⁻¹) * ∑ R ∈ D, vecNormSq (cubeAverageVec R w)
          ≤
            ((D.card : ℝ)⁻¹) *
              ∑ R ∈ D,
                2 * (vecNormSq (cubeAverageVec R u) + vecNormSq c) := by
            refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (by positivity))
            refine Finset.sum_le_sum ?_
            intro R hR
            rw [hdecomp R hR]
            exact vecNormSq_add_le (cubeAverageVec R u) c
      _ =
        2 *
          (((D.card : ℝ)⁻¹) * ∑ R ∈ D, vecNormSq (cubeAverageVec R u) +
            vecNormSq c) := by
          rw [← Finset.mul_sum]
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
          calc
            ((D.card : ℝ)⁻¹) *
                (2 *
                  ((∑ R ∈ D, vecNormSq (cubeAverageVec R u)) +
                    (D.card : ℝ) * vecNormSq c))
                =
              2 *
                (((D.card : ℝ)⁻¹) * ∑ R ∈ D, vecNormSq (cubeAverageVec R u) +
                  ((D.card : ℝ)⁻¹ * (D.card : ℝ)) * vecNormSq c) := by
                ring
            _ =
              2 *
                (((D.card : ℝ)⁻¹) * ∑ R ∈ D, vecNormSq (cubeAverageVec R u) +
                  vecNormSq c) := by
                rw [inv_mul_cancel₀ hcard]
                ring
  have htwo_le_four : 2 * (A + B) ≤ 4 * (A + B + 0 + 0) := by
    nlinarith [hA, hB]
  have hsqrt_tail :
      Real.sqrt (4 * (A + B + 0 + 0)) ≤
        2 * (Real.sqrt A + Real.sqrt B) := by
    simpa using
      sqrt_four_mul_sum_le_two_mul_sum_sqrt hA hB
        (by norm_num : 0 ≤ (0 : ℝ)) (by norm_num : 0 ≤ (0 : ℝ))
  have hsqrt :
      Real.sqrt (cubeBesovNegativeVectorDepthAverage Q w j) ≤
        2 * (Real.sqrt A + Real.sqrt B) :=
    (Real.sqrt_le_sqrt (havg.trans htwo_le_four)).trans hsqrt_tail
  have hweight_nonneg :
      0 ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  unfold cubeBesovNegativeVectorDepthSeminorm
  calc
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        Real.sqrt (cubeBesovNegativeVectorDepthAverage Q w j)
        ≤
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            (2 * (Real.sqrt A + Real.sqrt B)) := by
          exact mul_le_mul_of_nonneg_left hsqrt hweight_nonneg
    _ =
      2 *
        (Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt A +
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt B) := by
          ring

/--
Depthwise weak-norm triangle inequality obtained from a four-term decomposition
of descendant cube averages.
-/
theorem cubeBesovNegativeVectorDepthSeminorm_le_two_mul_sum_of_cubeAverageVec_eq
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (j : ℕ)
    (u u₁ u₂ u₃ u₄ : Vec d → Vec d)
    (hdecomp : ∀ R ∈ descendantsAtDepth Q j,
      cubeAverageVec R u =
        cubeAverageVec R u₁ + cubeAverageVec R u₂ +
          cubeAverageVec R u₃ + cubeAverageVec R u₄) :
    cubeBesovNegativeVectorDepthSeminorm Q s u j ≤
      2 *
        (cubeBesovNegativeVectorDepthSeminorm Q s u₁ j +
          cubeBesovNegativeVectorDepthSeminorm Q s u₂ j +
          cubeBesovNegativeVectorDepthSeminorm Q s u₃ j +
          cubeBesovNegativeVectorDepthSeminorm Q s u₄ j) := by
  let A₁ := cubeBesovNegativeVectorDepthAverage Q u₁ j
  let A₂ := cubeBesovNegativeVectorDepthAverage Q u₂ j
  let A₃ := cubeBesovNegativeVectorDepthAverage Q u₃ j
  let A₄ := cubeBesovNegativeVectorDepthAverage Q u₄ j
  have hA₁ : 0 ≤ A₁ := by
    simpa [A₁] using cubeBesovNegativeVectorDepthAverage_nonneg Q u₁ j
  have hA₂ : 0 ≤ A₂ := by
    simpa [A₂] using cubeBesovNegativeVectorDepthAverage_nonneg Q u₂ j
  have hA₃ : 0 ≤ A₃ := by
    simpa [A₃] using cubeBesovNegativeVectorDepthAverage_nonneg Q u₃ j
  have hA₄ : 0 ≤ A₄ := by
    simpa [A₄] using cubeBesovNegativeVectorDepthAverage_nonneg Q u₄ j
  have hdepth :
      cubeBesovNegativeVectorDepthAverage Q u j ≤ 4 * (A₁ + A₂ + A₃ + A₄) := by
    have hsplit :=
      cubeBesovNegativeVectorDepthAverage_le_four_mul_sum_of_cubeAverageVec_eq
        Q u j
        (fun R => cubeAverageVec R u₁)
        (fun R => cubeAverageVec R u₂)
        (fun R => cubeAverageVec R u₃)
        (fun R => cubeAverageVec R u₄)
        hdecomp
    have hrewrite :
        descendantsAverage Q j
            (fun R =>
              4 *
                (vecNormSq (cubeAverageVec R u₁) + vecNormSq (cubeAverageVec R u₂) +
                  vecNormSq (cubeAverageVec R u₃) + vecNormSq (cubeAverageVec R u₄))) =
          4 * (A₁ + A₂ + A₃ + A₄) := by
      simpa [A₁, A₂, A₃, A₄] using
        descendantsAverage_four_mul_sum_vecNormSq_cubeAverageVec_eq Q j u₁ u₂ u₃ u₄
    exact hsplit.trans_eq hrewrite
  have hsqrt :
      Real.sqrt (cubeBesovNegativeVectorDepthAverage Q u j) ≤
        2 * (Real.sqrt A₁ + Real.sqrt A₂ + Real.sqrt A₃ + Real.sqrt A₄) :=
    (Real.sqrt_le_sqrt hdepth).trans
      (sqrt_four_mul_sum_le_two_mul_sum_sqrt hA₁ hA₂ hA₃ hA₄)
  have hweight_nonneg :
      0 ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  unfold cubeBesovNegativeVectorDepthSeminorm
  calc
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        Real.sqrt (cubeBesovNegativeVectorDepthAverage Q u j)
        ≤
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            (2 * (Real.sqrt A₁ + Real.sqrt A₂ + Real.sqrt A₃ + Real.sqrt A₄)) := by
          exact mul_le_mul_of_nonneg_left hsqrt hweight_nonneg
    _ =
      2 *
        (Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt A₁ +
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt A₂ +
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt A₃ +
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt A₄) := by
          ring

theorem cubeBesovNegativeVectorPartialSeminorm_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d) :
    0 ≤ cubeBesovNegativeVectorPartialSeminorm Q s N u := by
  unfold cubeBesovNegativeVectorPartialSeminorm
  simpa using
    Finset.sum_nonneg
      (fun j _ => cubeBesovNegativeVectorDepthSeminorm_nonneg Q s u j)

/--
Finite `q = 1` weak-norm control from depthwise descendant-average controls.
This is the direct weighted-sum form of the negative Besov estimate: no
ellipticity constants or Ch5 packaging enter.
-/
theorem cubeBesovNegativeVectorPartialSeminorm_le_of_depthAverage_le {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d) {A : ℕ → ℝ}
    (hA : ∀ j ∈ Finset.range (N + 1),
      cubeBesovNegativeVectorDepthAverage Q u j ≤ A j) :
    cubeBesovNegativeVectorPartialSeminorm Q s N u ≤
      ∑ j ∈ Finset.range (N + 1),
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt (A j) := by
  unfold cubeBesovNegativeVectorPartialSeminorm
  refine Finset.sum_le_sum ?_
  intro j hj
  exact cubeBesovNegativeVectorDepthSeminorm_le_of_depthAverage_le Q s u j (hA j hj)

/--
Finite `q = 1` negative weak-norm bound from a four-term decomposition of
the descendant cube averages at every depth.
-/
theorem cubeBesovNegativeVectorPartialSeminorm_le_of_four_term_depthAverage_decomposition
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d)
    (predictor additivity lowScale tail : ℕ → TriadicCube d → Vec d)
    (hdecomp : ∀ j ∈ Finset.range (N + 1), ∀ R ∈ descendantsAtDepth Q j,
      cubeAverageVec R u =
        predictor j R + additivity j R + lowScale j R + tail j R) :
    cubeBesovNegativeVectorPartialSeminorm Q s N u ≤
      ∑ j ∈ Finset.range (N + 1),
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          Real.sqrt
            (descendantsAverage Q j fun R =>
              4 *
                (vecNormSq (predictor j R) + vecNormSq (additivity j R) +
                  vecNormSq (lowScale j R) + vecNormSq (tail j R))) := by
  refine cubeBesovNegativeVectorPartialSeminorm_le_of_depthAverage_le Q s N u ?_
  intro j hj
  exact
    cubeBesovNegativeVectorDepthAverage_le_four_mul_sum_of_cubeAverageVec_eq
      Q u j (predictor j) (additivity j) (lowScale j) (tail j)
      (hdecomp j hj)

/--
Finite `q = 1` negative weak-norm split for cube-indexed analytic pieces at
each depth. This is the note-facing weighted Cauchy/Minkowski step for the
four contributions in the Section 5.3 maximizer estimate.
-/
theorem cubeBesovNegativeVectorPartialSeminorm_le_two_mul_sum_of_cubeTerms_eq
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d)
    (predictor additivity lowScale tail : ℕ → TriadicCube d → Vec d)
    (hdecomp : ∀ j ∈ Finset.range (N + 1), ∀ R ∈ descendantsAtDepth Q j,
      cubeAverageVec R u =
        predictor j R + additivity j R + lowScale j R + tail j R) :
    cubeBesovNegativeVectorPartialSeminorm Q s N u ≤
      2 *
        ((∑ j ∈ Finset.range (N + 1),
            Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              Real.sqrt (descendantsAverage Q j fun R => vecNormSq (predictor j R))) +
          (∑ j ∈ Finset.range (N + 1),
            Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              Real.sqrt (descendantsAverage Q j fun R => vecNormSq (additivity j R))) +
          (∑ j ∈ Finset.range (N + 1),
            Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              Real.sqrt (descendantsAverage Q j fun R => vecNormSq (lowScale j R))) +
          (∑ j ∈ Finset.range (N + 1),
            Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              Real.sqrt (descendantsAverage Q j fun R => vecNormSq (tail j R)))) := by
  unfold cubeBesovNegativeVectorPartialSeminorm
  calc
    Finset.sum (Finset.range (N + 1))
        (fun j => cubeBesovNegativeVectorDepthSeminorm Q s u j)
        ≤
          Finset.sum (Finset.range (N + 1))
            (fun j =>
              2 *
                (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                    Real.sqrt
                      (descendantsAverage Q j fun R => vecNormSq (predictor j R)) +
                  Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                    Real.sqrt
                      (descendantsAverage Q j fun R => vecNormSq (additivity j R)) +
                  Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                    Real.sqrt
                      (descendantsAverage Q j fun R => vecNormSq (lowScale j R)) +
                  Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                    Real.sqrt
                      (descendantsAverage Q j fun R => vecNormSq (tail j R)))) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          exact
            cubeBesovNegativeVectorDepthSeminorm_le_two_mul_sum_of_cubeTerms_eq
              Q s u j (predictor j) (additivity j) (lowScale j) (tail j)
              (hdecomp j hj)
    _ =
      2 *
        ((∑ j ∈ Finset.range (N + 1),
            Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              Real.sqrt (descendantsAverage Q j fun R => vecNormSq (predictor j R))) +
          (∑ j ∈ Finset.range (N + 1),
            Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              Real.sqrt (descendantsAverage Q j fun R => vecNormSq (additivity j R))) +
          (∑ j ∈ Finset.range (N + 1),
            Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              Real.sqrt (descendantsAverage Q j fun R => vecNormSq (lowScale j R))) +
          (∑ j ∈ Finset.range (N + 1),
            Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              Real.sqrt (descendantsAverage Q j fun R => vecNormSq (tail j R)))) := by
          rw [← Finset.mul_sum]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]

/--
Finite high/low split for the negative weak norm. On the selected depths
`high`, a four-term cube-indexed decomposition is used; on the complementary
depths the original depth contribution is left untouched. This is the finite
form of the high-scale/low-scale split in the Section 5.3 maximizer proof.
-/
theorem cubeBesovNegativeVectorPartialSeminorm_le_cubeTerms_on_filter_add_complement
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d)
    (high : ℕ → Prop) [DecidablePred high]
    (predictor additivity lowScale tail : ℕ → TriadicCube d → Vec d)
    (hdecomp : ∀ j ∈ Finset.range (N + 1), high j →
      ∀ R ∈ descendantsAtDepth Q j,
        cubeAverageVec R u =
          predictor j R + additivity j R + lowScale j R + tail j R) :
    cubeBesovNegativeVectorPartialSeminorm Q s N u ≤
      (∑ j ∈ (Finset.range (N + 1)).filter high,
          2 *
            (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                Real.sqrt
                  (descendantsAverage Q j fun R => vecNormSq (predictor j R)) +
              Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                Real.sqrt
                  (descendantsAverage Q j fun R => vecNormSq (additivity j R)) +
              Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                Real.sqrt
                  (descendantsAverage Q j fun R => vecNormSq (lowScale j R)) +
              Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                Real.sqrt
                  (descendantsAverage Q j fun R => vecNormSq (tail j R)))) +
        ∑ j ∈ (Finset.range (N + 1)).filter (fun j => ¬ high j),
          cubeBesovNegativeVectorDepthSeminorm Q s u j := by
  let S : Finset ℕ := Finset.range (N + 1)
  let highContribution : ℕ → ℝ := fun j =>
    2 *
      (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          Real.sqrt (descendantsAverage Q j fun R => vecNormSq (predictor j R)) +
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          Real.sqrt (descendantsAverage Q j fun R => vecNormSq (additivity j R)) +
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          Real.sqrt (descendantsAverage Q j fun R => vecNormSq (lowScale j R)) +
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          Real.sqrt (descendantsAverage Q j fun R => vecNormSq (tail j R)))
  have hhigh :
      (∑ j ∈ S.filter high, cubeBesovNegativeVectorDepthSeminorm Q s u j) ≤
        ∑ j ∈ S.filter high, highContribution j := by
    refine Finset.sum_le_sum ?_
    intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjS, hjHigh⟩
    exact
      cubeBesovNegativeVectorDepthSeminorm_le_two_mul_sum_of_cubeTerms_eq
        Q s u j (predictor j) (additivity j) (lowScale j) (tail j)
        (hdecomp j (by simpa [S] using hjS) hjHigh)
  unfold cubeBesovNegativeVectorPartialSeminorm
  calc
    Finset.sum (Finset.range (N + 1))
        (fun j => cubeBesovNegativeVectorDepthSeminorm Q s u j)
        =
          (∑ j ∈ S.filter high, cubeBesovNegativeVectorDepthSeminorm Q s u j) +
            ∑ j ∈ S.filter (fun j => ¬ high j),
              cubeBesovNegativeVectorDepthSeminorm Q s u j := by
          simpa [S] using
            (Finset.sum_filter_add_sum_filter_not S high
              (fun j => cubeBesovNegativeVectorDepthSeminorm Q s u j)).symm
    _ ≤
          (∑ j ∈ S.filter high, highContribution j) +
            ∑ j ∈ S.filter (fun j => ¬ high j),
              cubeBesovNegativeVectorDepthSeminorm Q s u j := by
          exact add_le_add hhigh le_rfl
    _ =
      (∑ j ∈ (Finset.range (N + 1)).filter high,
          2 *
            (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                Real.sqrt
                  (descendantsAverage Q j fun R => vecNormSq (predictor j R)) +
              Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                Real.sqrt
                  (descendantsAverage Q j fun R => vecNormSq (additivity j R)) +
              Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                Real.sqrt
                  (descendantsAverage Q j fun R => vecNormSq (lowScale j R)) +
              Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                Real.sqrt
                  (descendantsAverage Q j fun R => vecNormSq (tail j R)))) +
        ∑ j ∈ (Finset.range (N + 1)).filter (fun j => ¬ high j),
          cubeBesovNegativeVectorDepthSeminorm Q s u j := by
          simp [S, highContribution]

/--
Filtered low-scale constant-tail estimate. On a selected set of depths, if the
averages of `w` equal the averages of `u` plus a fixed vector `c`, then the
filtered contribution of `w` is controlled by the filtered contribution of `u`
and the weighted constant tail.
-/
theorem sum_filter_cubeBesovNegativeVectorDepthSeminorm_le_two_mul_self_add_const_of_cubeAverageVec_eq
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ)
    (low : ℕ → Prop) [DecidablePred low]
    (w u : Vec d → Vec d) (c : Vec d)
    (hdecomp : ∀ j ∈ Finset.range (N + 1), low j →
      ∀ R ∈ descendantsAtDepth Q j,
        cubeAverageVec R w = cubeAverageVec R u + c) :
    (∑ j ∈ (Finset.range (N + 1)).filter low,
        cubeBesovNegativeVectorDepthSeminorm Q s w j) ≤
      2 *
        ((∑ j ∈ (Finset.range (N + 1)).filter low,
            cubeBesovNegativeVectorDepthSeminorm Q s u j) +
          ∑ j ∈ (Finset.range (N + 1)).filter low,
            Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt (vecNormSq c)) := by
  let F : Finset ℕ := (Finset.range (N + 1)).filter low
  calc
    (∑ j ∈ (Finset.range (N + 1)).filter low,
        cubeBesovNegativeVectorDepthSeminorm Q s w j)
        =
          ∑ j ∈ F, cubeBesovNegativeVectorDepthSeminorm Q s w j := by
          rfl
    _ ≤
          ∑ j ∈ F,
            2 *
              (cubeBesovNegativeVectorDepthSeminorm Q s u j +
                Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt (vecNormSq c)) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          rcases Finset.mem_filter.mp hj with ⟨hjRange, hjLow⟩
          exact
            cubeBesovNegativeVectorDepthSeminorm_le_two_mul_self_add_const_of_cubeAverageVec_eq
              Q s j w u c (hdecomp j hjRange hjLow)
    _ =
      2 *
        ((∑ j ∈ (Finset.range (N + 1)).filter low,
            cubeBesovNegativeVectorDepthSeminorm Q s u j) +
          ∑ j ∈ (Finset.range (N + 1)).filter low,
            Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt (vecNormSq c)) := by
          rw [← Finset.mul_sum]
          rw [Finset.sum_add_distrib]

theorem sum_filter_triadic_weight_mul_const_sqrt_eq
    {d : ℕ} (s : ℝ) (N : ℕ)
    (low : ℕ → Prop) [DecidablePred low] (c : Vec d) :
    (∑ j ∈ (Finset.range (N + 1)).filter low,
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt (vecNormSq c)) =
      (∑ j ∈ (Finset.range (N + 1)).filter low,
        Real.rpow (3 : ℝ) (-s * (j : ℝ))) * Real.sqrt (vecNormSq c) := by
  rw [Finset.sum_mul]

theorem sum_filter_triadic_weight_mul_const_sqrt_le_of_weight_sum_le
    {d : ℕ} (s : ℝ) (N : ℕ)
    (low : ℕ → Prop) [DecidablePred low] (c : Vec d) {tailWeight : ℝ}
    (hWeight :
      (∑ j ∈ (Finset.range (N + 1)).filter low,
        Real.rpow (3 : ℝ) (-s * (j : ℝ))) ≤ tailWeight) :
    (∑ j ∈ (Finset.range (N + 1)).filter low,
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt (vecNormSq c)) ≤
      tailWeight * Real.sqrt (vecNormSq c) := by
  rw [sum_filter_triadic_weight_mul_const_sqrt_eq s N low c]
  exact mul_le_mul_of_nonneg_right hWeight (Real.sqrt_nonneg _)

theorem sum_range_filter_not_lt_triadic_weight_mul_const_sqrt_le_geometric_tail
    {d : ℕ} (s : ℝ) (N L : ℕ) (c : Vec d) (hs : 0 < s) :
    (∑ j ∈ (Finset.range (N + 1)).filter (fun j => ¬ j < L),
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt (vecNormSq c)) ≤
      (Real.rpow (3 : ℝ) (-s * (L : ℝ)) *
          (1 - Real.rpow (3 : ℝ) (-s))⁻¹) *
        Real.sqrt (vecNormSq c) :=
  sum_filter_triadic_weight_mul_const_sqrt_le_of_weight_sum_le
    (s := s) (N := N) (low := fun j => ¬ j < L) c
    (sum_range_filter_not_lt_triadicDepthWeight_le_geometric_tail s N L hs)

/--
Finite high-scale decomposition plus low-scale constant-tail split. This is a
closer finite Lean analogue of the first displayed split in the deterministic
maximizer proof: high depths get the analytic four-term decomposition, while
low depths become a raw low-scale norm plus the `p₀`/`q₀` constant tail.
-/
theorem cubeBesovNegativeVectorPartialSeminorm_le_cubeTerms_on_filter_add_low_self_add_const
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ)
    (w lowField : Vec d → Vec d) (c : Vec d)
    (high : ℕ → Prop) [DecidablePred high]
    (predictor additivity lowScale tail : ℕ → TriadicCube d → Vec d)
    (hhigh : ∀ j ∈ Finset.range (N + 1), high j →
      ∀ R ∈ descendantsAtDepth Q j,
        cubeAverageVec R w =
          predictor j R + additivity j R + lowScale j R + tail j R)
    (hlow : ∀ j ∈ Finset.range (N + 1), ¬ high j →
      ∀ R ∈ descendantsAtDepth Q j,
        cubeAverageVec R w = cubeAverageVec R lowField + c) :
    cubeBesovNegativeVectorPartialSeminorm Q s N w ≤
      (∑ j ∈ (Finset.range (N + 1)).filter high,
          2 *
            (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                Real.sqrt
                  (descendantsAverage Q j fun R => vecNormSq (predictor j R)) +
              Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                Real.sqrt
                  (descendantsAverage Q j fun R => vecNormSq (additivity j R)) +
              Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                Real.sqrt
                  (descendantsAverage Q j fun R => vecNormSq (lowScale j R)) +
              Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                Real.sqrt
                  (descendantsAverage Q j fun R => vecNormSq (tail j R)))) +
        2 *
          ((∑ j ∈ (Finset.range (N + 1)).filter (fun j => ¬ high j),
              cubeBesovNegativeVectorDepthSeminorm Q s lowField j) +
            ∑ j ∈ (Finset.range (N + 1)).filter (fun j => ¬ high j),
              Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt (vecNormSq c)) := by
  have hsplit :=
    cubeBesovNegativeVectorPartialSeminorm_le_cubeTerms_on_filter_add_complement
      Q s N w high predictor additivity lowScale tail hhigh
  have hlow_sum :=
    sum_filter_cubeBesovNegativeVectorDepthSeminorm_le_two_mul_self_add_const_of_cubeAverageVec_eq
      Q s N (fun j => ¬ high j) w lowField c hlow
  exact hsplit.trans (add_le_add le_rfl hlow_sum)

/--
Cutoff version of the finite maximizer weak-norm split. Depths `j < L` are
controlled by the four analytic cube-indexed pieces, while depths `L ≤ j`
contribute a raw low-scale norm and a geometric constant tail.
-/
theorem cubeBesovNegativeVectorPartialSeminorm_le_cubeTerms_below_cutoff_add_low_self_add_geometric_const
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N L : ℕ)
    (w lowField : Vec d → Vec d) (c : Vec d)
    (predictor additivity lowScale tail : ℕ → TriadicCube d → Vec d)
    (hs : 0 < s)
    (hhigh : ∀ j ∈ Finset.range (N + 1), j < L →
      ∀ R ∈ descendantsAtDepth Q j,
        cubeAverageVec R w =
          predictor j R + additivity j R + lowScale j R + tail j R)
    (hlow : ∀ j ∈ Finset.range (N + 1), L ≤ j →
      ∀ R ∈ descendantsAtDepth Q j,
        cubeAverageVec R w = cubeAverageVec R lowField + c) :
    cubeBesovNegativeVectorPartialSeminorm Q s N w ≤
      (∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L),
          2 *
            (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                Real.sqrt
                  (descendantsAverage Q j fun R => vecNormSq (predictor j R)) +
              Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                Real.sqrt
                  (descendantsAverage Q j fun R => vecNormSq (additivity j R)) +
              Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                Real.sqrt
                  (descendantsAverage Q j fun R => vecNormSq (lowScale j R)) +
              Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                Real.sqrt
                  (descendantsAverage Q j fun R => vecNormSq (tail j R)))) +
        2 *
          ((∑ j ∈ (Finset.range (N + 1)).filter (fun j => ¬ j < L),
              cubeBesovNegativeVectorDepthSeminorm Q s lowField j) +
            (Real.rpow (3 : ℝ) (-s * (L : ℝ)) *
                (1 - Real.rpow (3 : ℝ) (-s))⁻¹) *
              Real.sqrt (vecNormSq c)) := by
  have hbase :=
    cubeBesovNegativeVectorPartialSeminorm_le_cubeTerms_on_filter_add_low_self_add_const
      Q s N w lowField c (fun j => j < L) predictor additivity lowScale tail
      hhigh
      (by
        intro j hj hnot
        exact hlow j hj (not_lt.mp hnot))
  have htail :=
    sum_range_filter_not_lt_triadic_weight_mul_const_sqrt_le_geometric_tail
      (d := d) s N L c hs
  refine hbase.trans ?_
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl htail) (by norm_num : 0 ≤ (2 : ℝ)))

/--
Finite cutoff maximizer estimate with the high-scale analytic pieces already
converted to shifted weak-norm gap sums.  This combines the four-term
cube-average decomposition, the low-scale constant-tail split, and the
depthwise estimates with growth factors `3^{s'j}`.
-/
theorem cubeBesovNegativeVectorPartialSeminorm_le_shifted_gap_sums_below_cutoff_add_low_self_add_geometric_const
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N L : ℕ)
    (w lowField : Vec d → Vec d) (c : Vec d)
    (predictor additivity lowScale tail : ℕ → TriadicCube d → Vec d)
    (sPred sAdd sLow sTail Cpred Cadd Clow Ctail : ℝ)
    (predGap addGap lowGap tailGap : ℕ → ℝ)
    (hs : 0 < s)
    (hCpred : 0 ≤ Cpred) (hCadd : 0 ≤ Cadd)
    (hClow : 0 ≤ Clow) (hCtail : 0 ≤ Ctail)
    (hhigh : ∀ j ∈ Finset.range (N + 1), j < L →
      ∀ R ∈ descendantsAtDepth Q j,
        cubeAverageVec R w =
          predictor j R + additivity j R + lowScale j R + tail j R)
    (hlow : ∀ j ∈ Finset.range (N + 1), L ≤ j →
      ∀ R ∈ descendantsAtDepth Q j,
        cubeAverageVec R w = cubeAverageVec R lowField + c)
    (hPred : ∀ j ∈ (Finset.range (N + 1)).filter (fun j => j < L),
      descendantsAverage Q j (fun R => vecNormSq (predictor j R)) ≤
        (Cpred * Real.rpow (3 : ℝ) (sPred * (j : ℝ))) ^ 2 * predGap j)
    (hAdd : ∀ j ∈ (Finset.range (N + 1)).filter (fun j => j < L),
      descendantsAverage Q j (fun R => vecNormSq (additivity j R)) ≤
        (Cadd * Real.rpow (3 : ℝ) (sAdd * (j : ℝ))) ^ 2 * addGap j)
    (hLow : ∀ j ∈ (Finset.range (N + 1)).filter (fun j => j < L),
      descendantsAverage Q j (fun R => vecNormSq (lowScale j R)) ≤
        (Clow * Real.rpow (3 : ℝ) (sLow * (j : ℝ))) ^ 2 * lowGap j)
    (hTail : ∀ j ∈ (Finset.range (N + 1)).filter (fun j => j < L),
      descendantsAverage Q j (fun R => vecNormSq (tail j R)) ≤
        (Ctail * Real.rpow (3 : ℝ) (sTail * (j : ℝ))) ^ 2 * tailGap j) :
    cubeBesovNegativeVectorPartialSeminorm Q s N w ≤
      2 *
        (Cpred *
            ∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L),
              Real.rpow (3 : ℝ) (-(s - sPred) * (j : ℝ)) *
                Real.sqrt (predGap j) +
          Cadd *
            ∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L),
              Real.rpow (3 : ℝ) (-(s - sAdd) * (j : ℝ)) *
                Real.sqrt (addGap j) +
          Clow *
            ∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L),
              Real.rpow (3 : ℝ) (-(s - sLow) * (j : ℝ)) *
                Real.sqrt (lowGap j) +
          Ctail *
            ∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L),
              Real.rpow (3 : ℝ) (-(s - sTail) * (j : ℝ)) *
                Real.sqrt (tailGap j)) +
        2 *
          ((∑ j ∈ (Finset.range (N + 1)).filter (fun j => ¬ j < L),
              cubeBesovNegativeVectorDepthSeminorm Q s lowField j) +
            (Real.rpow (3 : ℝ) (-s * (L : ℝ)) *
                (1 - Real.rpow (3 : ℝ) (-s))⁻¹) *
              Real.sqrt (vecNormSq c)) := by
  let high : Finset ℕ := (Finset.range (N + 1)).filter (fun j => j < L)
  let low : Finset ℕ := (Finset.range (N + 1)).filter (fun j => ¬ j < L)
  let predTerm : ℕ → ℝ := fun j =>
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      Real.sqrt (descendantsAverage Q j fun R => vecNormSq (predictor j R))
  let addTerm : ℕ → ℝ := fun j =>
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      Real.sqrt (descendantsAverage Q j fun R => vecNormSq (additivity j R))
  let lowTerm : ℕ → ℝ := fun j =>
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      Real.sqrt (descendantsAverage Q j fun R => vecNormSq (lowScale j R))
  let tailTerm : ℕ → ℝ := fun j =>
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      Real.sqrt (descendantsAverage Q j fun R => vecNormSq (tail j R))
  let predShifted : ℝ :=
    ∑ j ∈ high,
      Real.rpow (3 : ℝ) (-(s - sPred) * (j : ℝ)) * Real.sqrt (predGap j)
  let addShifted : ℝ :=
    ∑ j ∈ high,
      Real.rpow (3 : ℝ) (-(s - sAdd) * (j : ℝ)) * Real.sqrt (addGap j)
  let lowShifted : ℝ :=
    ∑ j ∈ high,
      Real.rpow (3 : ℝ) (-(s - sLow) * (j : ℝ)) * Real.sqrt (lowGap j)
  let tailShifted : ℝ :=
    ∑ j ∈ high,
      Real.rpow (3 : ℝ) (-(s - sTail) * (j : ℝ)) * Real.sqrt (tailGap j)
  let lowRemainder : ℝ :=
    ∑ j ∈ low, cubeBesovNegativeVectorDepthSeminorm Q s lowField j
  let tailRemainder : ℝ :=
    (Real.rpow (3 : ℝ) (-s * (L : ℝ)) *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹) *
      Real.sqrt (vecNormSq c)
  have hsplit :=
    cubeBesovNegativeVectorPartialSeminorm_le_cubeTerms_below_cutoff_add_low_self_add_geometric_const
      Q s N L w lowField c predictor additivity lowScale tail hs hhigh hlow
  have hPredSum :
      (∑ j ∈ high, predTerm j) ≤ Cpred * predShifted := by
    simpa [high, predTerm, predShifted] using
      sum_filter_triadicDepthWeight_mul_sqrt_descendantsAverage_vecNormSq_le_const_mul_shifted_weighted_sqrt
        (Q := Q) (s := s) (s' := sPred) (C := Cpred) (N := N)
        (high := fun j => j < L) (component := predictor) (gap := predGap)
        hCpred hPred
  have hAddSum :
      (∑ j ∈ high, addTerm j) ≤ Cadd * addShifted := by
    simpa [high, addTerm, addShifted] using
      sum_filter_triadicDepthWeight_mul_sqrt_descendantsAverage_vecNormSq_le_const_mul_shifted_weighted_sqrt
        (Q := Q) (s := s) (s' := sAdd) (C := Cadd) (N := N)
        (high := fun j => j < L) (component := additivity) (gap := addGap)
        hCadd hAdd
  have hLowSum :
      (∑ j ∈ high, lowTerm j) ≤ Clow * lowShifted := by
    simpa [high, lowTerm, lowShifted] using
      sum_filter_triadicDepthWeight_mul_sqrt_descendantsAverage_vecNormSq_le_const_mul_shifted_weighted_sqrt
        (Q := Q) (s := s) (s' := sLow) (C := Clow) (N := N)
        (high := fun j => j < L) (component := lowScale) (gap := lowGap)
        hClow hLow
  have hTailSum :
      (∑ j ∈ high, tailTerm j) ≤ Ctail * tailShifted := by
    simpa [high, tailTerm, tailShifted] using
      sum_filter_triadicDepthWeight_mul_sqrt_descendantsAverage_vecNormSq_le_const_mul_shifted_weighted_sqrt
        (Q := Q) (s := s) (s' := sTail) (C := Ctail) (N := N)
        (high := fun j => j < L) (component := tail) (gap := tailGap)
        hCtail hTail
  have hHighEq :
      (∑ j ∈ high,
          2 * (predTerm j + addTerm j + lowTerm j + tailTerm j)) =
        2 *
          ((∑ j ∈ high, predTerm j) + (∑ j ∈ high, addTerm j) +
            (∑ j ∈ high, lowTerm j) + (∑ j ∈ high, tailTerm j)) := by
    calc
      (∑ j ∈ high,
          2 * (predTerm j + addTerm j + lowTerm j + tailTerm j))
          =
        ∑ j ∈ high,
          (2 * predTerm j + 2 * addTerm j + 2 * lowTerm j + 2 * tailTerm j) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        ring
      _ =
        (∑ j ∈ high, 2 * predTerm j) +
          (∑ j ∈ high, 2 * addTerm j) +
          (∑ j ∈ high, 2 * lowTerm j) +
          (∑ j ∈ high, 2 * tailTerm j) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_add_distrib]
      _ =
        2 *
          ((∑ j ∈ high, predTerm j) + (∑ j ∈ high, addTerm j) +
            (∑ j ∈ high, lowTerm j) + (∑ j ∈ high, tailTerm j)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.mul_sum]
        ring
  have hHigh :
      (∑ j ∈ high,
          2 * (predTerm j + addTerm j + lowTerm j + tailTerm j)) ≤
        2 * (Cpred * predShifted + Cadd * addShifted +
          Clow * lowShifted + Ctail * tailShifted) := by
    rw [hHighEq]
    have hPieces :
        (∑ j ∈ high, predTerm j) + (∑ j ∈ high, addTerm j) +
            (∑ j ∈ high, lowTerm j) + (∑ j ∈ high, tailTerm j) ≤
          Cpred * predShifted + Cadd * addShifted +
            Clow * lowShifted + Ctail * tailShifted := by
      nlinarith [hPredSum, hAddSum, hLowSum, hTailSum]
    exact mul_le_mul_of_nonneg_left hPieces (by norm_num : 0 ≤ (2 : ℝ))
  have htotal :
      (∑ j ∈ high,
          2 * (predTerm j + addTerm j + lowTerm j + tailTerm j)) +
          2 * (lowRemainder + tailRemainder) ≤
        2 * (Cpred * predShifted + Cadd * addShifted +
          Clow * lowShifted + Ctail * tailShifted) +
          2 * (lowRemainder + tailRemainder) := by
    exact add_le_add hHigh le_rfl
  exact hsplit.trans (by
    simpa [high, low, predTerm, addTerm, lowTerm, tailTerm, predShifted,
      addShifted, lowShifted, tailShifted, lowRemainder, tailRemainder] using htotal)

/--
Finite `q = 1` negative weak-norm split from a four-term decomposition of all
descendant cube averages. This is the weighted weak-norm Cauchy/Minkowski step
needed in the Section 5.3 weak-norm estimate.
-/
theorem cubeBesovNegativeVectorPartialSeminorm_le_two_mul_sum_of_cubeAverageVec_eq
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ)
    (u u₁ u₂ u₃ u₄ : Vec d → Vec d)
    (hdecomp : ∀ j ∈ Finset.range (N + 1), ∀ R ∈ descendantsAtDepth Q j,
      cubeAverageVec R u =
        cubeAverageVec R u₁ + cubeAverageVec R u₂ +
          cubeAverageVec R u₃ + cubeAverageVec R u₄) :
    cubeBesovNegativeVectorPartialSeminorm Q s N u ≤
      2 *
        (cubeBesovNegativeVectorPartialSeminorm Q s N u₁ +
          cubeBesovNegativeVectorPartialSeminorm Q s N u₂ +
          cubeBesovNegativeVectorPartialSeminorm Q s N u₃ +
          cubeBesovNegativeVectorPartialSeminorm Q s N u₄) := by
  unfold cubeBesovNegativeVectorPartialSeminorm
  calc
    Finset.sum (Finset.range (N + 1))
        (fun j => cubeBesovNegativeVectorDepthSeminorm Q s u j)
        ≤
          Finset.sum (Finset.range (N + 1))
            (fun j =>
              2 *
                (cubeBesovNegativeVectorDepthSeminorm Q s u₁ j +
                  cubeBesovNegativeVectorDepthSeminorm Q s u₂ j +
                  cubeBesovNegativeVectorDepthSeminorm Q s u₃ j +
                  cubeBesovNegativeVectorDepthSeminorm Q s u₄ j)) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          exact
            cubeBesovNegativeVectorDepthSeminorm_le_two_mul_sum_of_cubeAverageVec_eq
              Q s j u u₁ u₂ u₃ u₄ (hdecomp j hj)
    _ =
      2 *
        (Finset.sum (Finset.range (N + 1))
            (fun j => cubeBesovNegativeVectorDepthSeminorm Q s u₁ j) +
          Finset.sum (Finset.range (N + 1))
            (fun j => cubeBesovNegativeVectorDepthSeminorm Q s u₂ j) +
          Finset.sum (Finset.range (N + 1))
            (fun j => cubeBesovNegativeVectorDepthSeminorm Q s u₃ j) +
          Finset.sum (Finset.range (N + 1))
            (fun j => cubeBesovNegativeVectorDepthSeminorm Q s u₄ j)) := by
          rw [← Finset.mul_sum]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]

theorem cubeBesovNegativeVectorPartialSeminormTwo_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d) :
    0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s N u := by
  unfold cubeBesovNegativeVectorPartialSeminormTwo
  exact Real.sqrt_nonneg _

theorem sq_cubeBesovNegativeVectorPartialSeminormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 =
      Finset.sum (Finset.range (N + 1)) fun j =>
        (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2 := by
  unfold cubeBesovNegativeVectorPartialSeminormTwo
  simpa [pow_two] using
    Real.sq_sqrt
      (Finset.sum_nonneg fun j _ => sq_nonneg (cubeBesovNegativeVectorDepthSeminorm Q s u j))

theorem cubeBesovNegativeVectorPartialSeminormTwo_anti_mono_exponent {d : ℕ}
    (Q : TriadicCube d) {a b : ℝ} (hab : a ≤ b)
    (N : ℕ) (u : Vec d → Vec d) :
    cubeBesovNegativeVectorPartialSeminormTwo Q b N u ≤
      cubeBesovNegativeVectorPartialSeminormTwo Q a N u := by
  unfold cubeBesovNegativeVectorPartialSeminormTwo
  refine Real.sqrt_le_sqrt ?_
  refine Finset.sum_le_sum ?_
  intro j hj
  exact pow_le_pow_left₀
    (cubeBesovNegativeVectorDepthSeminorm_nonneg Q b u j)
    (cubeBesovNegativeVectorDepthSeminorm_anti_mono_exponent Q hab u j)
    2

theorem finset_sqrt_sum_sq_le_sum_of_nonneg {ι : Type*} (s : Finset ι) (A : ι → ℝ)
    (hA : ∀ i ∈ s, 0 ≤ A i) :
    Real.sqrt (∑ i ∈ s, (A i) ^ 2) ≤ ∑ i ∈ s, A i := by
  have hsq :
      ∑ i ∈ s, (A i) ^ 2 ≤ (∑ i ∈ s, A i) ^ 2 := by
    simpa [pow_two] using Finset.sum_sq_le_sq_sum_of_nonneg hA
  have hsum_nonneg : 0 ≤ ∑ i ∈ s, A i :=
    Finset.sum_nonneg hA
  calc
    Real.sqrt (∑ i ∈ s, (A i) ^ 2)
        ≤ Real.sqrt ((∑ i ∈ s, A i) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ∑ i ∈ s, A i := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hsum_nonneg]

theorem cubeBesovNegativeVectorPartialSeminormTwo_le_partialSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N u ≤
      cubeBesovNegativeVectorPartialSeminorm Q s N u := by
  unfold cubeBesovNegativeVectorPartialSeminormTwo cubeBesovNegativeVectorPartialSeminorm
  exact finset_sqrt_sum_sq_le_sum_of_nonneg
    (Finset.range (N + 1))
    (fun j => cubeBesovNegativeVectorDepthSeminorm Q s u j)
    (fun j _ => cubeBesovNegativeVectorDepthSeminorm_nonneg Q s u j)

theorem cubeBesovNegativeVectorSeminorm_le_of_partialBound {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) {B : ℝ}
    (hB : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N u ≤ B) :
    cubeBesovNegativeVectorSeminorm Q s u ≤ B := by
  unfold cubeBesovNegativeVectorSeminorm
  refine csSup_le ?_ ?_
  · exact ⟨cubeBesovNegativeVectorPartialSeminorm Q s 0 u, ⟨0, rfl⟩⟩
  · rintro x ⟨N, rfl⟩
    exact hB N

theorem cubeBesovNegativeVectorPartialSeminorm_le_seminorm_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminorm Q s N u))
    (N : ℕ) :
    cubeBesovNegativeVectorPartialSeminorm Q s N u ≤
      cubeBesovNegativeVectorSeminorm Q s u := by
  unfold cubeBesovNegativeVectorSeminorm
  exact le_csSup hBdd ⟨N, rfl⟩

theorem cubeBesovNegativeVectorSeminorm_nonneg_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminorm Q s N u)) :
    0 ≤ cubeBesovNegativeVectorSeminorm Q s u := by
  have h0_le :
      cubeBesovNegativeVectorPartialSeminorm Q s 0 u ≤
        cubeBesovNegativeVectorSeminorm Q s u :=
    cubeBesovNegativeVectorPartialSeminorm_le_seminorm_of_bddAbove Q s u hBdd 0
  exact (cubeBesovNegativeVectorPartialSeminorm_nonneg Q s 0 u).trans h0_le

theorem cubeBesovNegativeVectorSeminormTwo_le_of_partialBound {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) {B : ℝ}
    (hB : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo Q s N u ≤ B) :
    cubeBesovNegativeVectorSeminormTwo Q s u ≤ B := by
  unfold cubeBesovNegativeVectorSeminormTwo
  refine csSup_le ?_ ?_
  · exact ⟨cubeBesovNegativeVectorPartialSeminormTwo Q s 0 u, ⟨0, rfl⟩⟩
  · rintro x ⟨N, rfl⟩
    exact hB N

theorem cubeBesovNegativeVectorSeminormTwo_anti_mono_exponent_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) {a b : ℝ} (hab : a ≤ b) (u : Vec d → Vec d)
    (hBdd : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q a N u)) :
    cubeBesovNegativeVectorSeminormTwo Q b u ≤
      cubeBesovNegativeVectorSeminormTwo Q a u := by
  refine cubeBesovNegativeVectorSeminormTwo_le_of_partialBound Q b u ?_
  intro N
  exact (cubeBesovNegativeVectorPartialSeminormTwo_anti_mono_exponent Q hab N u).trans
    (le_csSup hBdd ⟨N, rfl⟩)

theorem cubeBesovNegativeVectorSeminormTwo_le_of_qone_partialBound {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) {B : ℝ}
    (hB : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N u ≤ B) :
    cubeBesovNegativeVectorSeminormTwo Q s u ≤ B :=
  cubeBesovNegativeVectorSeminormTwo_le_of_partialBound Q s u fun N =>
    (cubeBesovNegativeVectorPartialSeminormTwo_le_partialSeminorm Q s N u).trans (hB N)

end

end Homogenization

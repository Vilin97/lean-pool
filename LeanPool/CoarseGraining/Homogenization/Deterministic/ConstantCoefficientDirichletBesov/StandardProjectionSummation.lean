/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.DiscreteConvolution

/-! # Standard Projection Summation -/

namespace Homogenization

noncomputable section

open scoped ENNReal BigOperators

/-!
# Summing geometric-tail depth estimates

The sharp boundary comparison gives a one-depth estimate whose hard term is a
lower-triangular geometric tail of ordinary positive depth seminorms.  This
file converts such one-depth estimates into finite `q = 2` positive Besov
estimates.
-/

/-- If every overlapping depth contribution is controlled by the same-depth
ordinary contribution plus a lower-triangular geometric tail of ordinary depth
contributions, then the finite overlapping `q = 2` seminorm is controlled by
the ordinary finite `q = 2` seminorm with the corresponding geometric loss. -/
theorem sq_cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_of_depth_geometric_tail
    {d : ℕ} (Q : TriadicCube d) (t : ℝ) (N : ℕ) (u : Vec d → Vec d)
    {A B r : ℝ}
    (hB_nonneg : 0 ≤ B)
    (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1)
    (hdepth :
      ∀ j ∈ Finset.range (N + 1),
        (cubeBesovOverlappingPositiveVectorDepthSeminorm Q t u j) ^ 2 ≤
          A * (cubeBesovPositiveVectorDepthSeminorm Q t u j) ^ 2 +
            B *
              (∑ m ∈ Finset.range j,
                r ^ (j - m) *
                  cubeBesovPositiveVectorDepthSeminorm Q t u m) ^ 2) :
    (cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q t N u) ^ 2
      ≤
        (A + B * ((1 - r)⁻¹) ^ 2) *
          (cubeBesovPositiveVectorPartialSeminormTwo Q t N u) ^ 2 := by
  rw [sq_cubeBesovOverlappingPositiveVectorPartialSeminormTwo,
    sq_cubeBesovPositiveVectorPartialSeminormTwo]
  exact
    sq_sum_le_of_le_add_geometric_convolution_sq
      (N := N) (A := A) (B := B) (r := r)
      (x := fun j => cubeBesovOverlappingPositiveVectorDepthSeminorm Q t u j)
      (a := fun j => cubeBesovPositiveVectorDepthSeminorm Q t u j)
      hB_nonneg hr_nonneg hr_lt_one hdepth

/-- Square-root form of
`sq_cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_of_depth_geometric_tail`. -/
theorem cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_sqrt_loss_of_depth_geometric_tail
    {d : ℕ} (Q : TriadicCube d) (t : ℝ) (N : ℕ) (u : Vec d → Vec d)
    {A B r : ℝ}
    (hB_nonneg : 0 ≤ B)
    (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1)
    (hloss_nonneg : 0 ≤ A + B * ((1 - r)⁻¹) ^ 2)
    (hdepth :
      ∀ j ∈ Finset.range (N + 1),
        (cubeBesovOverlappingPositiveVectorDepthSeminorm Q t u j) ^ 2 ≤
          A * (cubeBesovPositiveVectorDepthSeminorm Q t u j) ^ 2 +
            B *
              (∑ m ∈ Finset.range j,
                r ^ (j - m) *
                  cubeBesovPositiveVectorDepthSeminorm Q t u m) ^ 2) :
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q t N u
      ≤
        Real.sqrt (A + B * ((1 - r)⁻¹) ^ 2) *
          cubeBesovPositiveVectorPartialSeminormTwo Q t N u := by
  have hsq :=
    sq_cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_of_depth_geometric_tail
      (Q := Q) (t := t) (N := N) (u := u)
      (A := A) (B := B) (r := r)
      hB_nonneg hr_nonneg hr_lt_one hdepth
  have hleft_nonneg :
      0 ≤ cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q t N u :=
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo_nonneg Q t N u
  have hright_nonneg :
      0 ≤ Real.sqrt (A + B * ((1 - r)⁻¹) ^ 2) *
        cubeBesovPositiveVectorPartialSeminormTwo Q t N u := by
    exact mul_nonneg (Real.sqrt_nonneg _)
      (cubeBesovPositiveVectorPartialSeminormTwo_nonneg Q t N u)
  refine (sq_le_sq₀ hleft_nonneg hright_nonneg).1 ?_
  calc
    (cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q t N u) ^ 2
        ≤
          (A + B * ((1 - r)⁻¹) ^ 2) *
            (cubeBesovPositiveVectorPartialSeminormTwo Q t N u) ^ 2 := hsq
    _ =
          (Real.sqrt (A + B * ((1 - r)⁻¹) ^ 2) *
            cubeBesovPositiveVectorPartialSeminormTwo Q t N u) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hloss_nonneg]

end

end Homogenization

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Basic
import LeanPool.CoarseGraining.Homogenization.Multiscale.CubeAverage
import Mathlib.Algebra.Order.Field.GeomSum

/-! # Definitions -/

namespace Homogenization

noncomputable section

/-!
# Deterministic vector-valued weak norm interfaces

This file isolates the Chapter-3 negative-seminorm surface we need for
coarse-grained estimates without touching the active scalar Besov files.

The definitions are the note-normalized `q = 1`, `p = 2` vector-field
quantities corresponding to

`3^{-s m} [F]_{B^{-s}_{2,1}(Q)}`

when `Q` has scale `m`.
-/

open scoped BigOperators

/-- The depth-`j` block-average square for a vector field on a parent cube `Q`. -/
noncomputable def cubeBesovNegativeVectorDepthAverage {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ) : ℝ :=
  descendantsAverage Q j fun R => vecNormSq (cubeAverageVec R u)

/-- The note-normalized negative depth seminorm. For a parent cube of scale `m`,
this is the depth-`j` contribution with weight `3^{-s j}`. -/
noncomputable def cubeBesovNegativeVectorDepthSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ) : ℝ :=
  Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
    Real.sqrt (cubeBesovNegativeVectorDepthAverage Q u j)

/-- The finite-depth `q = 1` negative seminorm for vector fields. -/
noncomputable def cubeBesovNegativeVectorPartialSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d) : ℝ :=
  Finset.sum (Finset.range (N + 1)) fun j =>
    cubeBesovNegativeVectorDepthSeminorm Q s u j

/-- The finite-depth `q = 2` negative seminorm for vector fields. -/
noncomputable def cubeBesovNegativeVectorPartialSeminormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d) : ℝ :=
  Real.sqrt <|
    Finset.sum (Finset.range (N + 1)) fun j =>
      (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2

/-- The full note-normalized `q = 1` negative seminorm for vector fields. -/
noncomputable def cubeBesovNegativeVectorSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) : ℝ :=
  sSup (Set.range fun N : ℕ => cubeBesovNegativeVectorPartialSeminorm Q s N u)

/-- The full note-normalized `q = 2` negative seminorm for vector fields. -/
noncomputable def cubeBesovNegativeVectorSeminormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) : ℝ :=
  sSup (Set.range fun N : ℕ => cubeBesovNegativeVectorPartialSeminormTwo Q s N u)

theorem cubeBesovNegativeVectorDepthAverage_nonneg {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ) :
    0 ≤ cubeBesovNegativeVectorDepthAverage Q u j := by
  unfold cubeBesovNegativeVectorDepthAverage
  exact descendantsAverage_nonneg Q j _ fun R hR => vecNormSq_nonneg (cubeAverageVec R u)

/-- Scalar square-root subadditivity in the two-term form used below. -/
theorem sqrt_add_le_add_sqrt_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  constructor
  · exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- Four-term scalar square-root subadditivity with the Cauchy factor `2`. -/
theorem sqrt_four_mul_sum_le_two_mul_sum_sqrt
    {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt (4 * (a + b + c + d)) ≤
      2 * (Real.sqrt a + Real.sqrt b + Real.sqrt c + Real.sqrt d) := by
  have hab : 0 ≤ a + b := add_nonneg ha hb
  have hcd : 0 ≤ c + d := add_nonneg hc hd
  have hsqrt_sum :
      Real.sqrt (a + b + c + d) ≤
        Real.sqrt a + Real.sqrt b + Real.sqrt c + Real.sqrt d := by
    calc
      Real.sqrt (a + b + c + d)
          = Real.sqrt ((a + b) + (c + d)) := by ring_nf
      _ ≤ Real.sqrt (a + b) + Real.sqrt (c + d) :=
          sqrt_add_le_add_sqrt_of_nonneg hab hcd
      _ ≤ (Real.sqrt a + Real.sqrt b) + (Real.sqrt c + Real.sqrt d) :=
          add_le_add
            (sqrt_add_le_add_sqrt_of_nonneg ha hb)
            (sqrt_add_le_add_sqrt_of_nonneg hc hd)
      _ = Real.sqrt a + Real.sqrt b + Real.sqrt c + Real.sqrt d := by ring
  have hroot_four : Real.sqrt (4 : ℝ) = 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num : 0 ≤ (4 : ℝ)) (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  calc
    Real.sqrt (4 * (a + b + c + d))
        = 2 * Real.sqrt (a + b + c + d) := by
            rw [Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)), hroot_four]
    _ ≤ 2 * (Real.sqrt a + Real.sqrt b + Real.sqrt c + Real.sqrt d) := by
          nlinarith

theorem weighted_sqrt_sum_le_const_mul_weighted_sqrt_sum_of_le_const_sq_mul
    {ι : Type*} (I : Finset ι) (weight value bound : ι → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hweight : ∀ i ∈ I, 0 ≤ weight i)
    (hvalue : ∀ i ∈ I, value i ≤ C ^ 2 * bound i) :
    (∑ i ∈ I, weight i * Real.sqrt (value i)) ≤
      C * ∑ i ∈ I, weight i * Real.sqrt (bound i) := by
  calc
    (∑ i ∈ I, weight i * Real.sqrt (value i))
        ≤ ∑ i ∈ I, weight i * (C * Real.sqrt (bound i)) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hsqrt :
              Real.sqrt (value i) ≤ C * Real.sqrt (bound i) := by
            calc
              Real.sqrt (value i) ≤ Real.sqrt (C ^ 2 * bound i) :=
                Real.sqrt_le_sqrt (hvalue i hi)
              _ = C * Real.sqrt (bound i) := by
                rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq_eq_abs,
                  abs_of_nonneg hC]
          exact mul_le_mul_of_nonneg_left hsqrt (hweight i hi)
    _ = C * ∑ i ∈ I, weight i * Real.sqrt (bound i) := by
          calc
            ∑ i ∈ I, weight i * (C * Real.sqrt (bound i))
                = ∑ i ∈ I, C * (weight i * Real.sqrt (bound i)) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
            _ = C * ∑ i ∈ I, weight i * Real.sqrt (bound i) := by
                rw [Finset.mul_sum]

theorem weighted_sqrt_sum_le_weighted_coeff_sqrt_sum_of_le_sq_mul
    {ι : Type*} (I : Finset ι) (weight value bound coeff : ι → ℝ)
    (hcoeff : ∀ i ∈ I, 0 ≤ coeff i)
    (hweight : ∀ i ∈ I, 0 ≤ weight i)
    (hvalue : ∀ i ∈ I, value i ≤ (coeff i) ^ 2 * bound i) :
    (∑ i ∈ I, weight i * Real.sqrt (value i)) ≤
      ∑ i ∈ I, weight i * (coeff i * Real.sqrt (bound i)) := by
  refine Finset.sum_le_sum ?_
  intro i hi
  have hsqrt :
      Real.sqrt (value i) ≤ coeff i * Real.sqrt (bound i) := by
    calc
      Real.sqrt (value i) ≤ Real.sqrt ((coeff i) ^ 2 * bound i) :=
        Real.sqrt_le_sqrt (hvalue i hi)
      _ = coeff i * Real.sqrt (bound i) := by
        rw [Real.sqrt_mul (sq_nonneg (coeff i)), Real.sqrt_sq_eq_abs,
          abs_of_nonneg (hcoeff i hi)]
  exact mul_le_mul_of_nonneg_left hsqrt (hweight i hi)

theorem triadicDepthWeight_eq_pow (s : ℝ) (j : ℕ) :
    Real.rpow (3 : ℝ) (-(s * (j : ℝ))) =
      (Real.rpow (3 : ℝ) (-s)) ^ j := by
  calc
    Real.rpow (3 : ℝ) (-(s * (j : ℝ)))
        = Real.rpow (3 : ℝ) ((-s) * (j : ℝ)) := by ring_nf
    _ = Real.rpow (Real.rpow (3 : ℝ) (-s)) (j : ℝ) := by
          exact Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) (-s) (j : ℝ)
    _ = (Real.rpow (3 : ℝ) (-s)) ^ j := by
          exact Real.rpow_natCast (Real.rpow (3 : ℝ) (-s)) j

theorem triadicDepthWeight_nonneg (s : ℝ) (j : ℕ) :
    0 ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) :=
  Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _

theorem triadicDepthWeight_mul_growth_eq (s s' : ℝ) (j : ℕ) :
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        Real.rpow (3 : ℝ) (s' * (j : ℝ)) =
      Real.rpow (3 : ℝ) (-(s - s') * (j : ℝ)) := by
  calc
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        Real.rpow (3 : ℝ) (s' * (j : ℝ))
        = Real.rpow (3 : ℝ) (-s * (j : ℝ) + s' * (j : ℝ)) := by
          exact (Real.rpow_add (by norm_num : 0 < (3 : ℝ)) _ _).symm
    _ = Real.rpow (3 : ℝ) (-(s - s') * (j : ℝ)) := by
          congr 1
          ring

theorem triadicDepthWeight_mul_const_growth_eq (C s s' : ℝ) (j : ℕ) :
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        (C * Real.rpow (3 : ℝ) (s' * (j : ℝ))) =
      C * Real.rpow (3 : ℝ) (-(s - s') * (j : ℝ)) := by
  calc
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        (C * Real.rpow (3 : ℝ) (s' * (j : ℝ)))
        =
          C *
            (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              Real.rpow (3 : ℝ) (s' * (j : ℝ))) := by
          ring
    _ = C * Real.rpow (3 : ℝ) (-(s - s') * (j : ℝ)) := by
          rw [triadicDepthWeight_mul_growth_eq]

/--
If a cube-indexed contribution has a depthwise squared bound with growth
`C^2 * 3^{2s'j}`, then its `B^{-s}` weighted square-root sum is controlled by
the shifted `B^{-(s-s')}` weighted square-root sum of the controlling gap.

This is the deterministic algebraic core behind the Section 5.3 mismatch and
additivity-gap estimates: the analytic input is only the depthwise squared
bound, and the conclusion performs the `3^{-sj} 3^{s'j} = 3^{-(s-s')j}`
weight shift.
-/
theorem sum_filter_triadicDepthWeight_mul_sqrt_descendantsAverage_vecNormSq_le_const_mul_shifted_weighted_sqrt
    {d : ℕ} (Q : TriadicCube d) (s s' C : ℝ) (N : ℕ)
    (high : ℕ → Prop) [DecidablePred high]
    (component : ℕ → TriadicCube d → Vec d) (gap : ℕ → ℝ)
    (hC : 0 ≤ C)
    (hbound : ∀ j ∈ (Finset.range (N + 1)).filter high,
      descendantsAverage Q j (fun R => vecNormSq (component j R)) ≤
        (C * Real.rpow (3 : ℝ) (s' * (j : ℝ))) ^ 2 * gap j) :
    (∑ j ∈ (Finset.range (N + 1)).filter high,
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          Real.sqrt (descendantsAverage Q j fun R => vecNormSq (component j R))) ≤
      C *
        ∑ j ∈ (Finset.range (N + 1)).filter high,
          Real.rpow (3 : ℝ) (-(s - s') * (j : ℝ)) * Real.sqrt (gap j) := by
  let I : Finset ℕ := (Finset.range (N + 1)).filter high
  have hcoeff :
      ∀ j ∈ I, 0 ≤ C * Real.rpow (3 : ℝ) (s' * (j : ℝ)) := by
    intro j hj
    exact mul_nonneg hC (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hweight :
      ∀ j ∈ I, 0 ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) := by
    intro j hj
    exact triadicDepthWeight_nonneg s j
  have hbase :
      (∑ j ∈ I,
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            Real.sqrt (descendantsAverage Q j fun R => vecNormSq (component j R))) ≤
        ∑ j ∈ I,
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            ((C * Real.rpow (3 : ℝ) (s' * (j : ℝ))) * Real.sqrt (gap j)) :=
    weighted_sqrt_sum_le_weighted_coeff_sqrt_sum_of_le_sq_mul I
      (fun j => Real.rpow (3 : ℝ) (-s * (j : ℝ)))
      (fun j => descendantsAverage Q j fun R => vecNormSq (component j R))
      gap
      (fun j => C * Real.rpow (3 : ℝ) (s' * (j : ℝ)))
      hcoeff hweight hbound
  calc
    (∑ j ∈ (Finset.range (N + 1)).filter high,
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          Real.sqrt (descendantsAverage Q j fun R => vecNormSq (component j R)))
        ≤
          ∑ j ∈ I,
            Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              ((C * Real.rpow (3 : ℝ) (s' * (j : ℝ))) * Real.sqrt (gap j)) := by
          exact hbase
    _ =
      C *
        ∑ j ∈ I,
          Real.rpow (3 : ℝ) (-(s - s') * (j : ℝ)) * Real.sqrt (gap j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j hj
        calc
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              ((C * Real.rpow (3 : ℝ) (s' * (j : ℝ))) * Real.sqrt (gap j))
              =
            (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                (C * Real.rpow (3 : ℝ) (s' * (j : ℝ)))) *
              Real.sqrt (gap j) := by
            ring
          _ = (C * Real.rpow (3 : ℝ) (-(s - s') * (j : ℝ))) *
              Real.sqrt (gap j) := by
            rw [triadicDepthWeight_mul_const_growth_eq]
          _ = C *
              (Real.rpow (3 : ℝ) (-(s - s') * (j : ℝ)) * Real.sqrt (gap j)) := by
            ring
    _ =
      C *
        ∑ j ∈ (Finset.range (N + 1)).filter high,
          Real.rpow (3 : ℝ) (-(s - s') * (j : ℝ)) * Real.sqrt (gap j) := by
        rfl

theorem sum_filter_triadicDepthWeight_le_geometric_inv
    (s : ℝ) (N : ℕ) (low : ℕ → Prop) [DecidablePred low] (hs : 0 < s) :
    (∑ j ∈ (Finset.range (N + 1)).filter low,
        Real.rpow (3 : ℝ) (-s * (j : ℝ))) ≤
      (1 - Real.rpow (3 : ℝ) (-s))⁻¹ := by
  let r : ℝ := Real.rpow (3 : ℝ) (-s)
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (by linarith)
  calc
    (∑ j ∈ (Finset.range (N + 1)).filter low,
        Real.rpow (3 : ℝ) (-s * (j : ℝ)))
        ≤ ∑ j ∈ Finset.range (N + 1), Real.rpow (3 : ℝ) (-s * (j : ℝ)) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset low (Finset.range (N + 1)))
            (by
              intro j hjRange hjNotMem
              exact triadicDepthWeight_nonneg s j)
    _ = ∑ j ∈ Finset.range (N + 1), r ^ j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simpa [r] using triadicDepthWeight_eq_pow s j
    _ ≤ (1 - r)⁻¹ := by
          rw [Finset.range_eq_Ico]
          have hgeom :=
            geom_sum_Ico_le_of_lt_one (x := r) (m := 0) (n := N + 1)
              hr_nonneg hr_lt_one
          have hrhs : r ^ (0 : ℕ) / (1 - r) = (1 - r)⁻¹ := by
            simp [div_eq_mul_inv]
          exact hgeom.trans_eq hrhs

theorem sum_range_filter_ge_triadicDepthWeight_le_geometric_tail
    (s : ℝ) (N L : ℕ) (hs : 0 < s) :
    (∑ j ∈ (Finset.range (N + 1)).filter (fun j => L ≤ j),
        Real.rpow (3 : ℝ) (-s * (j : ℝ))) ≤
      Real.rpow (3 : ℝ) (-s * (L : ℝ)) *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹ := by
  let r : ℝ := Real.rpow (3 : ℝ) (-s)
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (by linarith)
  have hfilter :
      (Finset.range (N + 1)).filter (fun j => L ≤ j) = Finset.Ico L (N + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · intro h
      exact ⟨h.2, h.1⟩
    · intro h
      exact ⟨h.2, h.1⟩
  calc
    (∑ j ∈ (Finset.range (N + 1)).filter (fun j => L ≤ j),
        Real.rpow (3 : ℝ) (-s * (j : ℝ)))
        = ∑ j ∈ Finset.Ico L (N + 1), Real.rpow (3 : ℝ) (-s * (j : ℝ)) := by
          rw [hfilter]
    _ = ∑ j ∈ Finset.Ico L (N + 1), r ^ j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simpa [r] using triadicDepthWeight_eq_pow s j
    _ ≤ r ^ L / (1 - r) := by
          exact geom_sum_Ico_le_of_lt_one hr_nonneg hr_lt_one
    _ =
      Real.rpow (3 : ℝ) (-s * (L : ℝ)) *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹ := by
          have hL : r ^ L = Real.rpow (3 : ℝ) (-(s * (L : ℝ))) := by
            simpa [r] using (triadicDepthWeight_eq_pow s L).symm
          rw [hL]
          rw [div_eq_mul_inv]
          dsimp [r]
          congr 1
          ring_nf

theorem sum_range_filter_not_lt_triadicDepthWeight_le_geometric_tail
    (s : ℝ) (N L : ℕ) (hs : 0 < s) :
    (∑ j ∈ (Finset.range (N + 1)).filter (fun j => ¬ j < L),
        Real.rpow (3 : ℝ) (-s * (j : ℝ))) ≤
      Real.rpow (3 : ℝ) (-s * (L : ℝ)) *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹ := by
  simpa [not_lt] using sum_range_filter_ge_triadicDepthWeight_le_geometric_tail s N L hs

/--
Depthwise four-term Cauchy split for the negative weak-norm block average.
If each descendant cube average decomposes into four vector terms, then the
depth average is controlled by the average of the four squared sizes.
-/
theorem cubeBesovNegativeVectorDepthAverage_le_four_mul_sum_of_cubeAverageVec_eq {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ)
    (predictor additivity lowScale tail : TriadicCube d → Vec d)
    (hdecomp : ∀ R ∈ descendantsAtDepth Q j,
      cubeAverageVec R u =
        predictor R + additivity R + lowScale R + tail R) :
    cubeBesovNegativeVectorDepthAverage Q u j ≤
      descendantsAverage Q j fun R =>
        4 *
          (vecNormSq (predictor R) + vecNormSq (additivity R) +
            vecNormSq (lowScale R) + vecNormSq (tail R)) := by
  unfold cubeBesovNegativeVectorDepthAverage descendantsAverage
  refine mul_le_mul_of_nonneg_left ?_ ?_
  · refine Finset.sum_le_sum ?_
    intro R hR
    rw [hdecomp R hR]
    exact vecNormSq_four_add_le (predictor R) (additivity R) (lowScale R) (tail R)
  · exact inv_nonneg.mpr (by positivity)

theorem cubeBesovNegativeVectorDepthSeminorm_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ) :
    0 ≤ cubeBesovNegativeVectorDepthSeminorm Q s u j := by
  unfold cubeBesovNegativeVectorDepthSeminorm
  refine mul_nonneg ?_ ?_
  · exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  · exact Real.sqrt_nonneg _

theorem cubeBesovNegativeVectorDepthSeminorm_anti_mono_exponent {d : ℕ}
    (Q : TriadicCube d) {a b : ℝ} (hab : a ≤ b)
    (u : Vec d → Vec d) (j : ℕ) :
    cubeBesovNegativeVectorDepthSeminorm Q b u j ≤
      cubeBesovNegativeVectorDepthSeminorm Q a u j := by
  have hmul : a * (j : ℝ) ≤ b * (j : ℝ) :=
    mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg j)
  have hexp : -b * (j : ℝ) ≤ -a * (j : ℝ) := by
    nlinarith
  have hweight :
      Real.rpow (3 : ℝ) (-b * (j : ℝ)) ≤
        Real.rpow (3 : ℝ) (-a * (j : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) hexp
  unfold cubeBesovNegativeVectorDepthSeminorm
  exact mul_le_mul_of_nonneg_right hweight (Real.sqrt_nonneg _)

theorem cubeBesovNegativeVectorPartialSeminorm_anti_mono_exponent {d : ℕ}
    (Q : TriadicCube d) {a b : ℝ} (hab : a ≤ b)
    (N : ℕ) (u : Vec d → Vec d) :
    cubeBesovNegativeVectorPartialSeminorm Q b N u ≤
      cubeBesovNegativeVectorPartialSeminorm Q a N u := by
  unfold cubeBesovNegativeVectorPartialSeminorm
  exact Finset.sum_le_sum fun j _ =>
    cubeBesovNegativeVectorDepthSeminorm_anti_mono_exponent Q hab u j

/-- Exact depthwise conversion between two negative-Besov exponents. -/
theorem cubeBesovNegativeVectorDepthSeminorm_eq_gap_mul {d : ℕ}
    (Q : TriadicCube d) (a b : ℝ) (u : Vec d → Vec d) (j : ℕ) :
    cubeBesovNegativeVectorDepthSeminorm Q a u j =
      Real.rpow (3 : ℝ) (-(a - b) * (j : ℝ)) *
        cubeBesovNegativeVectorDepthSeminorm Q b u j := by
  unfold cubeBesovNegativeVectorDepthSeminorm
  calc
    Real.rpow (3 : ℝ) (-a * (j : ℝ)) *
        Real.sqrt (cubeBesovNegativeVectorDepthAverage Q u j)
        =
      (Real.rpow (3 : ℝ) (-(a - b) * (j : ℝ)) *
        Real.rpow (3 : ℝ) (-b * (j : ℝ))) *
        Real.sqrt (cubeBesovNegativeVectorDepthAverage Q u j) := by
        congr 1
        calc
          Real.rpow (3 : ℝ) (-a * (j : ℝ)) =
              Real.rpow (3 : ℝ) (-(a - b) * (j : ℝ) + -b * (j : ℝ)) := by
            congr 1
            ring
          _ =
              Real.rpow (3 : ℝ) (-(a - b) * (j : ℝ)) *
                Real.rpow (3 : ℝ) (-b * (j : ℝ)) := by
            exact Real.rpow_add (by norm_num : (0 : ℝ) < 3)
              (-(a - b) * (j : ℝ)) (-b * (j : ℝ))
    _ =
      Real.rpow (3 : ℝ) (-(a - b) * (j : ℝ)) *
        (Real.rpow (3 : ℝ) (-b * (j : ℝ)) *
          Real.sqrt (cubeBesovNegativeVectorDepthAverage Q u j)) := by
        ring

/-- Finite-depth Cauchy conversion from the `q = 1` negative seminorm at a
larger exponent to the `q = 2` negative seminorm at a smaller exponent. -/
theorem cubeBesovNegativeVectorPartialSeminorm_le_gap_sqrt_mul_partialSeminormTwo
    {d : ℕ} (Q : TriadicCube d) (a b : ℝ) (N : ℕ) (u : Vec d → Vec d) :
    cubeBesovNegativeVectorPartialSeminorm Q a N u ≤
      Real.sqrt
          (Finset.sum (Finset.range (N + 1)) fun j =>
            (Real.rpow (3 : ℝ) (-(a - b) * (j : ℝ))) ^ (2 : ℕ)) *
        cubeBesovNegativeVectorPartialSeminormTwo Q b N u := by
  calc
    cubeBesovNegativeVectorPartialSeminorm Q a N u =
        ∑ j ∈ Finset.range (N + 1),
          Real.rpow (3 : ℝ) (-(a - b) * (j : ℝ)) *
            cubeBesovNegativeVectorDepthSeminorm Q b u j := by
        unfold cubeBesovNegativeVectorPartialSeminorm
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [cubeBesovNegativeVectorDepthSeminorm_eq_gap_mul]
    _ ≤
        Real.sqrt
            (∑ j ∈ Finset.range (N + 1),
              (Real.rpow (3 : ℝ) (-(a - b) * (j : ℝ))) ^ (2 : ℕ)) *
          Real.sqrt
            (∑ j ∈ Finset.range (N + 1),
              (cubeBesovNegativeVectorDepthSeminorm Q b u j) ^ (2 : ℕ)) :=
        Real.sum_mul_le_sqrt_mul_sqrt (Finset.range (N + 1))
          (fun j => Real.rpow (3 : ℝ) (-(a - b) * (j : ℝ)))
          (fun j => cubeBesovNegativeVectorDepthSeminorm Q b u j)
    _ =
        Real.sqrt
            (Finset.sum (Finset.range (N + 1)) fun j =>
              (Real.rpow (3 : ℝ) (-(a - b) * (j : ℝ))) ^ (2 : ℕ)) *
          cubeBesovNegativeVectorPartialSeminormTwo Q b N u := by
        unfold cubeBesovNegativeVectorPartialSeminormTwo
        rfl

/-- Geometric-loss version of the finite-depth `q = 1` to `q = 2` conversion. -/
theorem cubeBesovNegativeVectorPartialSeminorm_le_gap_geometric_mul_partialSeminormTwo
    {d : ℕ} (Q : TriadicCube d) {a b : ℝ} (hgap : 0 < a - b)
    (N : ℕ) (u : Vec d → Vec d) :
    cubeBesovNegativeVectorPartialSeminorm Q a N u ≤
      Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * (a - b)))⁻¹) *
        cubeBesovNegativeVectorPartialSeminormTwo Q b N u := by
  have hsum :
      Finset.sum (Finset.range (N + 1)) (fun j =>
          (Real.rpow (3 : ℝ) (-(a - b) * (j : ℝ))) ^ (2 : ℕ)) ≤
        (1 - Real.rpow (3 : ℝ) (-2 * (a - b)))⁻¹ := by
    have hrewrite :
        (Finset.sum (Finset.range (N + 1)) fun j =>
          (Real.rpow (3 : ℝ) (-(a - b) * (j : ℝ))) ^ (2 : ℕ)) =
        ∑ j ∈ Finset.range (N + 1),
          Real.rpow (3 : ℝ) (-(2 * (a - b)) * (j : ℝ)) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      calc
        (Real.rpow (3 : ℝ) (-(a - b) * (j : ℝ))) ^ (2 : ℕ)
            =
          Real.rpow (3 : ℝ) ((-(a - b) * (j : ℝ)) * (2 : ℝ)) := by
            rw [← Real.rpow_natCast]
            exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)
              (-(a - b) * (j : ℝ)) (2 : ℝ)).symm
        _ = Real.rpow (3 : ℝ) (-(2 * (a - b)) * (j : ℝ)) := by
            congr 1
            ring
    rw [hrewrite]
    simpa using
      (sum_filter_triadicDepthWeight_le_geometric_inv
        (2 * (a - b)) N (fun _ : ℕ => True) (by nlinarith))
  have hpartial :=
    cubeBesovNegativeVectorPartialSeminorm_le_gap_sqrt_mul_partialSeminormTwo
      Q a b N u
  have hroot :
      Real.sqrt
          (Finset.sum (Finset.range (N + 1)) fun j =>
            (Real.rpow (3 : ℝ) (-(a - b) * (j : ℝ))) ^ (2 : ℕ)) ≤
        Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * (a - b)))⁻¹) :=
    Real.sqrt_le_sqrt hsum
  have htwo_nonneg :
      0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q b N u := by
    unfold cubeBesovNegativeVectorPartialSeminormTwo
    exact Real.sqrt_nonneg _
  exact hpartial.trans (mul_le_mul_of_nonneg_right hroot htwo_nonneg)

theorem cubeBesovNegativeVectorPartialSeminorm_scale_compare_of_le {d : ℕ}
    (Q : TriadicCube d) {r t : ℝ} (ht : t ≤ r)
    (N : ℕ) (F : Vec d → Vec d) :
    cubeBesovScaleWeight (-r) Q *
        cubeBesovNegativeVectorPartialSeminorm Q r N F ≤
      cubeBesovScaleWeight (-(r - t)) Q *
        (cubeBesovScaleWeight (-t) Q *
          cubeBesovNegativeVectorPartialSeminorm Q t N F) := by
  have hmono :
      cubeBesovNegativeVectorPartialSeminorm Q r N F ≤
        cubeBesovNegativeVectorPartialSeminorm Q t N F :=
    cubeBesovNegativeVectorPartialSeminorm_anti_mono_exponent Q ht N F
  have hscale_nonneg : 0 ≤ cubeBesovScaleWeight (-r) Q :=
    cubeBesovScaleWeight_nonneg (-r) Q
  have hweighted :
      cubeBesovScaleWeight (-r) Q *
          cubeBesovNegativeVectorPartialSeminorm Q r N F ≤
        cubeBesovScaleWeight (-r) Q *
          cubeBesovNegativeVectorPartialSeminorm Q t N F :=
    mul_le_mul_of_nonneg_left hmono hscale_nonneg
  have hscale :
      cubeBesovScaleWeight (-(r - t)) Q * cubeBesovScaleWeight (-t) Q =
        cubeBesovScaleWeight (-r) Q := by
    rw [cubeBesovScaleWeight_mul_eq_scaleWeight_add]
    ring_nf
  calc
    cubeBesovScaleWeight (-r) Q *
        cubeBesovNegativeVectorPartialSeminorm Q r N F
        ≤ cubeBesovScaleWeight (-r) Q *
            cubeBesovNegativeVectorPartialSeminorm Q t N F := hweighted
    _ = cubeBesovScaleWeight (-(r - t)) Q *
        (cubeBesovScaleWeight (-t) Q *
          cubeBesovNegativeVectorPartialSeminorm Q t N F) := by
          rw [← hscale]
          ring

theorem cubeBesovNegativeVectorPartialSeminorm_flux_scale_compare {d : ℕ}
    (Q : TriadicCube d) {s t : ℝ} (hst : s + t ≤ 1)
    (N : ℕ) (F : Vec d → Vec d) :
    cubeBesovScaleWeight (-(1 - s)) Q *
        cubeBesovNegativeVectorPartialSeminorm Q (1 - s) N F ≤
      cubeBesovScaleWeight (-(1 - s - t)) Q *
        (cubeBesovScaleWeight (-t) Q *
          cubeBesovNegativeVectorPartialSeminorm Q t N F) := by
  have ht_le : t ≤ 1 - s := by linarith
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    cubeBesovNegativeVectorPartialSeminorm_scale_compare_of_le
      Q (r := 1 - s) (t := t) ht_le N F

/--
Turn a bound for one descendant-average block into the corresponding weighted
negative-Besov depth bound. This is the analytic insertion point used by the
Section 5.3 weak-norm estimates after the local Caccioppoli/Besov argument has
produced depthwise controls.
-/
theorem cubeBesovNegativeVectorDepthSeminorm_le_of_depthAverage_le {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ) {A : ℝ}
    (hA : cubeBesovNegativeVectorDepthAverage Q u j ≤ A) :
    cubeBesovNegativeVectorDepthSeminorm Q s u j ≤
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt A := by
  unfold cubeBesovNegativeVectorDepthSeminorm
  exact
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hA)
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)

theorem descendantsAverage_vecNormSq_nonneg {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (v : TriadicCube d → Vec d) :
    0 ≤ descendantsAverage Q j fun R => vecNormSq (v R) := by
  exact descendantsAverage_nonneg Q j _ fun R _ => vecNormSq_nonneg (v R)

theorem sqrt_descendantsAverage_vecNormSq_const_smul_eq {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (c : ℝ) (V : TriadicCube d → Vec d)
    (hc : 0 ≤ c) :
    Real.sqrt (descendantsAverage Q j fun R => vecNormSq (c • V R)) =
      c * Real.sqrt (descendantsAverage Q j fun R => vecNormSq (V R)) := by
  have havg :
      descendantsAverage Q j (fun R => vecNormSq (c • V R)) =
        c ^ 2 * descendantsAverage Q j (fun R => vecNormSq (V R)) := by
    simp_rw [vecNormSq_smul]
    unfold descendantsAverage
    simp [Finset.mul_sum]
    ring_nf
  rw [havg, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs,
    abs_of_nonneg hc]

theorem descendantsAverage_const_eq {d : ℕ} (Q : TriadicCube d) (j : ℕ) (c : ℝ) :
    descendantsAverage Q j (fun _ => c) = c := by
  classical
  change ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      (descendantsAtDepth Q j).sum (fun _ => c) = c
  have hD : (descendantsAtDepth Q j).Nonempty := descendantsAtDepth_nonempty Q j
  have hcard : (((descendantsAtDepth Q j).card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hD)
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

theorem descendantsAverage_four_mul_sum_vecNormSq_eq {d : ℕ}
    (Q : TriadicCube d) (j : ℕ)
    (v₁ v₂ v₃ v₄ : TriadicCube d → Vec d) :
    descendantsAverage Q j
        (fun R =>
          4 *
            (vecNormSq (v₁ R) + vecNormSq (v₂ R) +
              vecNormSq (v₃ R) + vecNormSq (v₄ R))) =
      4 *
        (descendantsAverage Q j (fun R => vecNormSq (v₁ R)) +
          descendantsAverage Q j (fun R => vecNormSq (v₂ R)) +
          descendantsAverage Q j (fun R => vecNormSq (v₃ R)) +
          descendantsAverage Q j (fun R => vecNormSq (v₄ R))) := by
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  calc
    descendantsAverage Q j
        (fun R =>
          4 *
            (vecNormSq (v₁ R) + vecNormSq (v₂ R) +
              vecNormSq (v₃ R) + vecNormSq (v₄ R)))
        =
          ((D.card : ℝ)⁻¹) *
            ∑ R ∈ D,
              4 *
                (vecNormSq (v₁ R) + vecNormSq (v₂ R) +
                  vecNormSq (v₃ R) + vecNormSq (v₄ R)) := by
          rfl
    _ =
          ((D.card : ℝ)⁻¹) *
            (4 * ∑ R ∈ D,
              (vecNormSq (v₁ R) + vecNormSq (v₂ R) +
                vecNormSq (v₃ R) + vecNormSq (v₄ R))) := by
          rw [← Finset.mul_sum]
    _ =
          4 *
            (((D.card : ℝ)⁻¹) *
              ∑ R ∈ D,
                (vecNormSq (v₁ R) + vecNormSq (v₂ R) +
                  vecNormSq (v₃ R) + vecNormSq (v₄ R))) := by
          ring
    _ =
          4 *
            (((D.card : ℝ)⁻¹) *
              ((∑ R ∈ D, vecNormSq (v₁ R)) +
                (∑ R ∈ D, vecNormSq (v₂ R)) +
                (∑ R ∈ D, vecNormSq (v₃ R)) +
                (∑ R ∈ D, vecNormSq (v₄ R)))) := by
          congr 1
          congr 1
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ =
      4 *
        (descendantsAverage Q j (fun R => vecNormSq (v₁ R)) +
          descendantsAverage Q j (fun R => vecNormSq (v₂ R)) +
          descendantsAverage Q j (fun R => vecNormSq (v₃ R)) +
          descendantsAverage Q j (fun R => vecNormSq (v₄ R))) := by
          simp [descendantsAverage, D]
          ring

end

end Homogenization

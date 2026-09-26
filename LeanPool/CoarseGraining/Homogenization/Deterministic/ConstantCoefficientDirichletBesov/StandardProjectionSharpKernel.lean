/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.StandardProjectionBoundaryNeighborCount
public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.StandardProjectionSummation
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.Regularity

/-! # Standard Projection Sharp Kernel -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal BigOperators

/-!
# The sharp boundary tail as a geometric kernel input

The one-depth sharp boundary estimate leaves a concrete tail over coarser
standard projection depths.  This file names that tail and connects any
geometric-kernel bound for it to the finite positive Besov summation theorem.
-/

/-- MemLp closure hypotheses needed by the sharp-boundary standard projection
comparison.  These are bookkeeping assumptions: the analytic content is in the
finite bridge below. -/
structure SharpBoundaryProjectionMemLp {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) : Prop where
  residual :
    ∀ j : ℕ,
      MeasureTheory.MemLp (fun x => u x - cubeProjectionVec Q j u x)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q)
  residual_overlap :
    ∀ j : ℕ, ∀ S ∈ overlapCentersAtDepth Q j,
      MeasureTheory.MemLp (fun x => u x - cubeProjectionVec Q j u x)
        (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)
  projection_overlap :
    ∀ j : ℕ, ∀ S ∈ overlapCentersAtDepth Q j,
      MeasureTheory.MemLp (cubeProjectionVec Q j u)
        (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)
  projection_zero_overlap :
    ∀ j : ℕ, ∀ S ∈ overlapCentersAtDepth Q j,
      MeasureTheory.MemLp (cubeProjectionVec Q 0 u)
        (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)
  projection_gap_overlap :
    ∀ j : ℕ, ∀ S ∈ overlapCentersAtDepth Q j,
      MeasureTheory.MemLp (cubeProjectionGapVec Q 0 j u)
        (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)
  increment_overlap :
    ∀ j : ℕ, ∀ S ∈ overlapCentersAtDepth Q j, ∀ m ∈ Finset.range j,
      MeasureTheory.MemLp (cubeIncrementVec Q (m + 1) u)
        (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)
  parent :
    ∀ j : ℕ, ∀ m ∈ Finset.range j, ∀ T ∈ descendantsAtDepth Q m,
      MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure T)

/-- The vector standard projection is `L²` on its parent cube. -/
theorem cubeProjectionVec_memLp_normalizedCubeMeasure {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (u : Vec d → Vec d) :
    MeasureTheory.MemLp (cubeProjectionVec Q j u) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
  refine MeasureTheory.MemLp.of_eval ?_
  intro i
  simpa [cubeProjectionVec] using
    (cubeProjection_memLp Q j (2 : ℝ≥0∞) (fun x => u x i))

/-- The vector standard projection restricts to every admissible overlap cube. -/
theorem cubeProjectionVec_memLp_normalizedOverlapCubeMeasure {d : ℕ}
    {Q S : TriadicCube d} {j k : ℕ} (u : Vec d → Vec d)
    (hS : S ∈ overlapCentersAtDepth Q j) :
    MeasureTheory.MemLp (cubeProjectionVec Q k u) (2 : ℝ≥0∞)
      (normalizedOverlapCubeMeasure S) :=
  memLp_normalizedOverlapCubeMeasure_of_memLp_normalizedCubeMeasure hS
    (cubeProjectionVec_memLp_normalizedCubeMeasure Q k u)

/-- The vector projection residual is `L²` on the parent cube. -/
theorem cubeProjectionVec_residual_memLp_normalizedCubeMeasure {d : ℕ}
    {Q : TriadicCube d} (j : ℕ) {u : Vec d → Vec d}
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    MeasureTheory.MemLp (fun x => u x - cubeProjectionVec Q j u x)
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
  hu.sub (cubeProjectionVec_memLp_normalizedCubeMeasure Q j u)

/-- The vector projection residual restricts to every admissible overlap cube. -/
theorem cubeProjectionVec_residual_memLp_normalizedOverlapCubeMeasure {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} {u : Vec d → Vec d}
    (hS : S ∈ overlapCentersAtDepth Q j)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    MeasureTheory.MemLp (fun x => u x - cubeProjectionVec Q j u x)
      (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S) :=
  memLp_normalizedOverlapCubeMeasure_of_memLp_normalizedCubeMeasure hS
    (cubeProjectionVec_residual_memLp_normalizedCubeMeasure j hu)

/-- A vector projection gap is the difference of two vector projections. -/
theorem cubeProjectionGapVec_memLp_normalizedCubeMeasure {d : ℕ}
    (Q : TriadicCube d) (j n : ℕ) (u : Vec d → Vec d) :
    MeasureTheory.MemLp (cubeProjectionGapVec Q j n u) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
  rw [cubeProjectionGapVec_eq_sub_cubeProjectionVec]
  exact
    (cubeProjectionVec_memLp_normalizedCubeMeasure Q (j + n) u).sub
      (cubeProjectionVec_memLp_normalizedCubeMeasure Q j u)

/-- A vector projection gap restricts to every admissible overlap cube. -/
theorem cubeProjectionGapVec_memLp_normalizedOverlapCubeMeasure {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} (n : ℕ) (u : Vec d → Vec d)
    (hS : S ∈ overlapCentersAtDepth Q j) :
    MeasureTheory.MemLp (cubeProjectionGapVec Q 0 n u) (2 : ℝ≥0∞)
      (normalizedOverlapCubeMeasure S) :=
  memLp_normalizedOverlapCubeMeasure_of_memLp_normalizedCubeMeasure hS
    (cubeProjectionGapVec_memLp_normalizedCubeMeasure Q 0 n u)

/-- The vector martingale increment is the difference of consecutive vector
standard projections. -/
theorem cubeIncrementVec_succ_eq_sub_cubeProjectionVec {d : ℕ}
    (Q : TriadicCube d) (m : ℕ) (u : Vec d → Vec d) :
    cubeIncrementVec Q (m + 1) u =
      fun x => cubeProjectionVec Q (m + 1) u x - cubeProjectionVec Q m u x := by
  funext x i
  simp [cubeIncrementVec, cubeProjectionVec, cubeIncrement_succ]

/-- A vector martingale increment is `L²` on the parent cube. -/
theorem cubeIncrementVec_memLp_normalizedCubeMeasure {d : ℕ}
    (Q : TriadicCube d) (m : ℕ) (u : Vec d → Vec d) :
    MeasureTheory.MemLp (cubeIncrementVec Q (m + 1) u) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
  rw [cubeIncrementVec_succ_eq_sub_cubeProjectionVec]
  exact
    (cubeProjectionVec_memLp_normalizedCubeMeasure Q (m + 1) u).sub
      (cubeProjectionVec_memLp_normalizedCubeMeasure Q m u)

/-- A vector martingale increment restricts to every admissible overlap cube. -/
theorem cubeIncrementVec_memLp_normalizedOverlapCubeMeasure {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} (m : ℕ) (u : Vec d → Vec d)
    (hS : S ∈ overlapCentersAtDepth Q j) :
    MeasureTheory.MemLp (cubeIncrementVec Q (m + 1) u) (2 : ℝ≥0∞)
      (normalizedOverlapCubeMeasure S) :=
  memLp_normalizedOverlapCubeMeasure_of_memLp_normalizedCubeMeasure hS
    (cubeIncrementVec_memLp_normalizedCubeMeasure Q m u)

/-- The sharp-boundary projection `MemLp` closure package follows from parent
`L²` membership.  All projection, gap, and increment fields are finite-depth
piecewise constants, and all overlap cubes are measured by restriction from
the parent cube. -/
theorem SharpBoundaryProjectionMemLp.of_memLp {d : ℕ}
    {Q : TriadicCube d} {u : Vec d → Vec d}
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    SharpBoundaryProjectionMemLp Q u where
  residual j :=
    cubeProjectionVec_residual_memLp_normalizedCubeMeasure j hu
  residual_overlap _j _S hS :=
    cubeProjectionVec_residual_memLp_normalizedOverlapCubeMeasure hS hu
  projection_overlap j _S hS :=
    cubeProjectionVec_memLp_normalizedOverlapCubeMeasure (j := j) (k := j) u hS
  projection_zero_overlap j _S hS :=
    cubeProjectionVec_memLp_normalizedOverlapCubeMeasure (j := j) (k := 0) u hS
  projection_gap_overlap j _S hS :=
    cubeProjectionGapVec_memLp_normalizedOverlapCubeMeasure (j := j) j u hS
  increment_overlap j _S hS m _hm :=
    cubeIncrementVec_memLp_normalizedOverlapCubeMeasure (j := j) m u hS
  parent _j _m _hm _T hT :=
    memLp_on_descendant_of_memLp_generic hT hu

/-- Positive triadic depth weights as powers of the one-step weight. -/
theorem triadicPositiveDepthWeight_eq_pow (t : ℝ) (j : ℕ) :
    Real.rpow (3 : ℝ) (t * (j : ℝ)) =
      (Real.rpow (3 : ℝ) t) ^ j := by
  calc
    Real.rpow (3 : ℝ) (t * (j : ℝ))
        = Real.rpow (Real.rpow (3 : ℝ) t) (j : ℝ) := by
          exact Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) t (j : ℝ)
    _ = (Real.rpow (3 : ℝ) t) ^ j := by
          exact Real.rpow_natCast (Real.rpow (3 : ℝ) t) j

/-- Dimension-only constant in the sharp boundary kernel. -/
noncomputable def sharpBoundaryKernelConstant (d : ℕ) : ℝ :=
  Real.sqrt
    (4 *
      (((3 ^ d * (3 ^ d * (2 * d))) : ℕ) : ℝ) *
        ((3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ)))

/-- The square-root surface/volume ratio in one gap of the sharp boundary
kernel.  For positive dimension this is `3^{-1/2}`. -/
noncomputable def sharpBoundaryKernelRatio (d : ℕ) : ℝ :=
  Real.sqrt ((((3 ^ (d - 1) : ℕ) : ℝ) / ((3 ^ d : ℕ) : ℝ)))

/-- One-gap kernel base before replacing the dimension ratio by `3^{-1/2}`. -/
noncomputable def sharpBoundaryKernelBase (d : ℕ) (t : ℝ) : ℝ :=
  Real.rpow (3 : ℝ) t * sharpBoundaryKernelRatio d

/-- The explicit finite-depth sharp-boundary loss.  For positive dimension and
`t < 1/2`, the denominator is finite because
`sharpBoundaryKernelBase d t = 3^(t - 1/2) < 1`. -/
noncomputable def sharpBoundaryKernelLoss (d : ℕ) (t : ℝ) : ℝ :=
  8 * (3 ^ d : ℝ) +
    (4 * (sharpBoundaryKernelConstant d) ^ 2) *
      ((1 - sharpBoundaryKernelBase d t)⁻¹) ^ 2

theorem sharpBoundaryKernelConstant_nonneg (d : ℕ) :
    0 ≤ sharpBoundaryKernelConstant d := by
  unfold sharpBoundaryKernelConstant
  exact Real.sqrt_nonneg _

theorem sharpBoundaryKernelRatio_nonneg (d : ℕ) :
    0 ≤ sharpBoundaryKernelRatio d := by
  unfold sharpBoundaryKernelRatio
  exact Real.sqrt_nonneg _

theorem sharpBoundaryKernelBase_nonneg (d : ℕ) (t : ℝ) :
    0 ≤ sharpBoundaryKernelBase d t := by
  unfold sharpBoundaryKernelBase
  exact mul_nonneg
    (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    (sharpBoundaryKernelRatio_nonneg d)

theorem sharpBoundaryKernelLoss_nonneg (d : ℕ) (t : ℝ) :
    0 ≤ sharpBoundaryKernelLoss d t := by
  unfold sharpBoundaryKernelLoss
  exact add_nonneg
    (mul_nonneg (by norm_num) (by positivity))
    (mul_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg (sharpBoundaryKernelConstant d)))
      (sq_nonneg _))

theorem sharpBoundaryKernelRatio_eq {d : ℕ} [NeZero d] :
    sharpBoundaryKernelRatio d = Real.rpow (3 : ℝ) (-(1 / 2 : ℝ)) := by
  unfold sharpBoundaryKernelRatio
  have hdpos : 0 < d := Nat.pos_of_neZero d
  have hpow_nat : (3 ^ d : ℕ) = 3 ^ (d - 1) * 3 := by
    rw [← pow_succ]
    congr 1
    omega
  have hpow_real :
      (((3 ^ d : ℕ) : ℝ)) = (((3 ^ (d - 1) : ℕ) : ℝ)) * 3 := by
    exact_mod_cast hpow_nat
  have hratio :
      (((3 ^ (d - 1) : ℕ) : ℝ) / ((3 ^ d : ℕ) : ℝ)) = (3 : ℝ)⁻¹ := by
    rw [hpow_real]
    field_simp [show (((3 ^ (d - 1) : ℕ) : ℝ) ≠ 0) by positivity]
  rw [hratio]
  rw [Real.sqrt_eq_rpow]
  exact (Real.rpow_neg_eq_inv_rpow (3 : ℝ) (1 / 2 : ℝ)).symm

theorem sharpBoundaryKernelBase_eq {d : ℕ} [NeZero d] (t : ℝ) :
    sharpBoundaryKernelBase d t = Real.rpow (3 : ℝ) (t - 1 / 2) := by
  unfold sharpBoundaryKernelBase
  rw [sharpBoundaryKernelRatio_eq]
  calc
    Real.rpow (3 : ℝ) t * Real.rpow (3 : ℝ) (-(1 / 2 : ℝ))
        = Real.rpow (3 : ℝ) (t + -(1 / 2 : ℝ)) := by
          exact (Real.rpow_add (by norm_num : (0 : ℝ) < 3) t (-(1 / 2 : ℝ))).symm
    _ = Real.rpow (3 : ℝ) (t - 1 / 2) := by ring_nf

theorem sharpBoundaryKernelBase_lt_one {d : ℕ} [NeZero d] {t : ℝ}
    (ht : t < 1 / 2) :
    sharpBoundaryKernelBase d t < 1 := by
  rw [sharpBoundaryKernelBase_eq]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by norm_num : (1 : ℝ) < 3) (by linarith)

private theorem sqrt_div_pow_sq_eq_pow_div_pow {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    ((Real.sqrt a / Real.sqrt b) ^ n) ^ 2 = (a / b) ^ n := by
  have hsquare : (Real.sqrt a / Real.sqrt b) ^ 2 = a / b := by
    rw [div_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]
  calc
    ((Real.sqrt a / Real.sqrt b) ^ n) ^ 2
        = ((Real.sqrt a / Real.sqrt b) ^ 2) ^ n := by
          rw [← pow_mul, ← pow_mul]
          congr 1
          omega
    _ = (a / b) ^ n := by
          rw [hsquare]

/-- The `m`th summand in the sharp boundary tail at depth `j`. -/
noncomputable def sharpBoundaryDepthTailTerm {d : ℕ}
    (Q : TriadicCube d) (t : ℝ) (u : Vec d → Vec d) (j m : ℕ) : ℝ :=
  Real.rpow (3 : ℝ) (t * (j : ℝ)) *
    Real.sqrt
      ((((3 ^ d) ^ j : ℕ) : ℝ)⁻¹ *
        (4 *
          (((3 ^ d * (3 ^ d *
              (2 * d * (3 ^ (d - 1)) ^ (j - m))) : ℕ) : ℝ) *
            ((3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) *
              ((descendantsAtDepth Q m).card : ℝ) *
                cubeBesovPositiveVectorDepthAverage Q u m))))

/-- The sharp boundary tail appearing in the one-depth hard comparison. -/
noncomputable def sharpBoundaryDepthTail {d : ℕ}
    (Q : TriadicCube d) (t : ℝ) (u : Vec d → Vec d) (j : ℕ) : ℝ :=
  ∑ m ∈ Finset.range j, sharpBoundaryDepthTailTerm Q t u j m

theorem sharpBoundaryDepthTailTerm_nonneg {d : ℕ}
    (Q : TriadicCube d) (t : ℝ) (u : Vec d → Vec d) (j m : ℕ) :
    0 ≤ sharpBoundaryDepthTailTerm Q t u j m := by
  unfold sharpBoundaryDepthTailTerm
  exact mul_nonneg
    (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    (Real.sqrt_nonneg _)

/-- Single-summand scale arithmetic for the sharp boundary tail, in the clean
`j = m + n` form. -/
theorem sharpBoundaryDepthTailTerm_le_kernelBase_add {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (t : ℝ) (u : Vec d → Vec d) (m n : ℕ) :
    sharpBoundaryDepthTailTerm Q t u (m + n) m ≤
      sharpBoundaryKernelConstant d * (sharpBoundaryKernelBase d t) ^ n *
        cubeBesovPositiveVectorDepthSeminorm Q t u m := by
  have hL : 0 ≤ sharpBoundaryDepthTailTerm Q t u (m + n) m :=
    sharpBoundaryDepthTailTerm_nonneg Q t u (m + n) m
  have hR :
      0 ≤ sharpBoundaryKernelConstant d * (sharpBoundaryKernelBase d t) ^ n *
        cubeBesovPositiveVectorDepthSeminorm Q t u m := by
    exact mul_nonneg
      (mul_nonneg (sharpBoundaryKernelConstant_nonneg d)
        (pow_nonneg (sharpBoundaryKernelBase_nonneg d t) _))
      (cubeBesovPositiveVectorDepthSeminorm_nonneg Q t u m)
  refine (sq_le_sq₀ hL hR).1 ?_
  unfold sharpBoundaryDepthTailTerm sharpBoundaryKernelConstant
    sharpBoundaryKernelBase cubeBesovPositiveVectorDepthSeminorm
    sharpBoundaryKernelRatio
  have hA : 0 ≤ cubeBesovPositiveVectorDepthAverage Q u m :=
    cubeBesovPositiveVectorDepthAverage_nonneg Q u m
  simp [mul_pow, descendantsAtDepth_card, Fintype.card_fin, Real.sq_sqrt, hA]
  rw [Real.sq_sqrt (by positivity)]
  rw [Real.sq_sqrt (by positivity)]
  have hweight_mn :
      (3 : ℝ) ^ (t * ((m : ℝ) + (n : ℝ))) =
        (Real.rpow (3 : ℝ) t) ^ (m + n) := by
    rw [← Nat.cast_add]
    exact triadicPositiveDepthWeight_eq_pow t (m + n)
  have hweight_m :
      (3 : ℝ) ^ (t * (m : ℝ)) = (Real.rpow (3 : ℝ) t) ^ m :=
    triadicPositiveDepthWeight_eq_pow t m
  rw [hweight_mn, hweight_m]
  rw [sqrt_div_pow_sq_eq_pow_div_pow
    (by positivity : 0 ≤ (3 ^ (d - 1) : ℝ))
    (by positivity : 0 ≤ (3 ^ d : ℝ)) n]
  rw [pow_add (Real.rpow (3 : ℝ) t) m n]
  rw [pow_add ((3 : ℝ) ^ d) m n]
  rw [div_pow]
  field_simp [pow_ne_zero n (by positivity : ((3 : ℝ) ^ d) ≠ 0),
    pow_ne_zero m (by positivity : ((3 : ℝ) ^ d) ≠ 0)]
  change
    ((Real.rpow (3 : ℝ) t) ^ n) ^ 2 * (d : ℝ) ^ 2 *
        cubeBesovPositiveVectorDepthAverage Q u m ≤
      (d : ℝ) ^ 2 * cubeBesovPositiveVectorDepthAverage Q u m *
        (((Real.rpow (3 : ℝ) t) ^ n) ^ 2)
  ring_nf
  exact le_rfl

/-- Single-summand scale arithmetic for the sharp boundary tail. -/
theorem sharpBoundaryDepthTailTerm_le_kernelBase {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (t : ℝ) (u : Vec d → Vec d) {j m : ℕ}
    (hmj : m ≤ j) :
    sharpBoundaryDepthTailTerm Q t u j m ≤
      sharpBoundaryKernelConstant d * (sharpBoundaryKernelBase d t) ^ (j - m) *
        cubeBesovPositiveVectorDepthSeminorm Q t u m := by
  have hj : m + (j - m) = j := Nat.add_sub_of_le hmj
  simpa [hj] using
    sharpBoundaryDepthTailTerm_le_kernelBase_add
      (Q := Q) (t := t) (u := u) m (j - m)

theorem sharpBoundaryDepthTail_nonneg {d : ℕ}
    (Q : TriadicCube d) (t : ℝ) (u : Vec d → Vec d) (j : ℕ) :
    0 ≤ sharpBoundaryDepthTail Q t u j := by
  unfold sharpBoundaryDepthTail
  refine Finset.sum_nonneg ?_
  intro m _hm
  exact sharpBoundaryDepthTailTerm_nonneg Q t u j m

/-- Summing termwise geometric bounds gives the sharp-tail geometric kernel
bound. -/
theorem sharpBoundaryDepthTail_le_geometric_convolution_of_forall_term_le
    {d : ℕ} (Q : TriadicCube d) (t : ℝ) (u : Vec d → Vec d) (j : ℕ)
    {C r : ℝ}
    (hterm :
      ∀ m ∈ Finset.range j,
        sharpBoundaryDepthTailTerm Q t u j m ≤
          C * (r ^ (j - m) *
            cubeBesovPositiveVectorDepthSeminorm Q t u m)) :
    sharpBoundaryDepthTail Q t u j ≤
      C *
        (∑ m ∈ Finset.range j,
          r ^ (j - m) * cubeBesovPositiveVectorDepthSeminorm Q t u m) := by
  unfold sharpBoundaryDepthTail
  calc
    ∑ m ∈ Finset.range j, sharpBoundaryDepthTailTerm Q t u j m
        ≤
          ∑ m ∈ Finset.range j,
            C * (r ^ (j - m) *
              cubeBesovPositiveVectorDepthSeminorm Q t u m) := by
          exact Finset.sum_le_sum hterm
    _ =
          C *
            (∑ m ∈ Finset.range j,
              r ^ (j - m) *
                cubeBesovPositiveVectorDepthSeminorm Q t u m) := by
          rw [Finset.mul_sum]

/-- Named form of the one-depth hard comparison using
`sharpBoundaryDepthTail`. -/
theorem sq_cubeBesovOverlappingPositiveVectorDepthSeminorm_le_standard_add_sharpBoundaryDepthTail
    {d : ℕ} (Q : TriadicCube d) (t : ℝ) (u : Vec d → Vec d) (j : ℕ)
    (hres :
      MeasureTheory.MemLp (fun x => u x - cubeProjectionVec Q j u x)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hresLoc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (fun x => u x - cubeProjectionVec Q j u x)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hprojLoc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionVec Q j u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hzeroLoc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionVec Q 0 u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hgapLoc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionGapVec Q 0 j u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hincLoc :
      ∀ S ∈ overlapCentersAtDepth Q j, ∀ m ∈ Finset.range j,
        MeasureTheory.MemLp (cubeIncrementVec Q (m + 1) u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (huParent :
      ∀ m ∈ Finset.range j, ∀ T ∈ descendantsAtDepth Q m,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure T)) :
    (cubeBesovOverlappingPositiveVectorDepthSeminorm Q t u j) ^ 2 ≤
      8 * (3 ^ d : ℝ) * (cubeBesovPositiveVectorDepthSeminorm Q t u j) ^ 2 +
        4 * (sharpBoundaryDepthTail Q t u j) ^ 2 := by
  simpa [sharpBoundaryDepthTail, sharpBoundaryDepthTailTerm] using
    sq_cubeBesovOverlappingPositiveVectorDepthSeminorm_le_standard_add_sharpBoundary_sum
      Q t u j hres hresLoc hprojLoc hzeroLoc hgapLoc hincLoc huParent

/-- If the named sharp boundary tail is bounded by a geometric convolution of
ordinary positive depth seminorms, then the finite overlapping positive
seminorm is bounded by the ordinary finite positive seminorm. -/
theorem sq_cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_of_sharpBoundaryDepthTail_kernel
    {d : ℕ} (Q : TriadicCube d) (t : ℝ) (N : ℕ) (u : Vec d → Vec d)
    {C r : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1)
    (hres :
      ∀ j ∈ Finset.range (N + 1),
        MeasureTheory.MemLp (fun x => u x - cubeProjectionVec Q j u x)
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hresLoc :
      ∀ j ∈ Finset.range (N + 1), ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (fun x => u x - cubeProjectionVec Q j u x)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hprojLoc :
      ∀ j ∈ Finset.range (N + 1), ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionVec Q j u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hzeroLoc :
      ∀ j ∈ Finset.range (N + 1), ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionVec Q 0 u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hgapLoc :
      ∀ j ∈ Finset.range (N + 1), ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionGapVec Q 0 j u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hincLoc :
      ∀ j ∈ Finset.range (N + 1), ∀ S ∈ overlapCentersAtDepth Q j,
        ∀ m ∈ Finset.range j,
          MeasureTheory.MemLp (cubeIncrementVec Q (m + 1) u)
            (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (huParent :
      ∀ j ∈ Finset.range (N + 1), ∀ m ∈ Finset.range j,
        ∀ T ∈ descendantsAtDepth Q m,
          MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure T))
    (hkernel :
      ∀ j ∈ Finset.range (N + 1),
        sharpBoundaryDepthTail Q t u j ≤
          C *
            (∑ m ∈ Finset.range j,
              r ^ (j - m) *
                cubeBesovPositiveVectorDepthSeminorm Q t u m)) :
    (cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q t N u) ^ 2
      ≤
        (8 * (3 ^ d : ℝ) + (4 * C ^ 2) * ((1 - r)⁻¹) ^ 2) *
          (cubeBesovPositiveVectorPartialSeminormTwo Q t N u) ^ 2 := by
  refine
    sq_cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_of_depth_geometric_tail
      (Q := Q) (t := t) (N := N) (u := u)
      (A := 8 * (3 ^ d : ℝ)) (B := 4 * C ^ 2) (r := r)
      ?_ hr_nonneg hr_lt_one ?_
  · exact mul_nonneg (by norm_num) (sq_nonneg C)
  · intro j hj
    let conv : ℝ :=
      ∑ m ∈ Finset.range j,
        r ^ (j - m) * cubeBesovPositiveVectorDepthSeminorm Q t u m
    have hbase :=
      sq_cubeBesovOverlappingPositiveVectorDepthSeminorm_le_standard_add_sharpBoundaryDepthTail
        Q t u j (hres j hj) (hresLoc j hj) (hprojLoc j hj)
        (hzeroLoc j hj) (hgapLoc j hj) (hincLoc j hj) (huParent j hj)
    have hconv_nonneg : 0 ≤ conv := by
      dsimp [conv]
      refine Finset.sum_nonneg ?_
      intro m _hm
      exact mul_nonneg (pow_nonneg hr_nonneg _)
        (cubeBesovPositiveVectorDepthSeminorm_nonneg Q t u m)
    have htail_sq :
        4 * (sharpBoundaryDepthTail Q t u j) ^ 2 ≤
          (4 * C ^ 2) * conv ^ 2 := by
      have htail_le : sharpBoundaryDepthTail Q t u j ≤ C * conv := by
        simpa [conv] using hkernel j hj
      have hsq :
          (sharpBoundaryDepthTail Q t u j) ^ 2 ≤ (C * conv) ^ 2 :=
        (sq_le_sq₀
          (sharpBoundaryDepthTail_nonneg Q t u j)
          (mul_nonneg hC_nonneg hconv_nonneg)).mpr htail_le
      calc
        4 * (sharpBoundaryDepthTail Q t u j) ^ 2
            ≤ 4 * (C * conv) ^ 2 := by
              exact mul_le_mul_of_nonneg_left hsq (by norm_num)
        _ = (4 * C ^ 2) * conv ^ 2 := by
              ring
    calc
      (cubeBesovOverlappingPositiveVectorDepthSeminorm Q t u j) ^ 2
          ≤
            8 * (3 ^ d : ℝ) *
                (cubeBesovPositiveVectorDepthSeminorm Q t u j) ^ 2 +
              4 * (sharpBoundaryDepthTail Q t u j) ^ 2 := hbase
      _ ≤
            8 * (3 ^ d : ℝ) *
                (cubeBesovPositiveVectorDepthSeminorm Q t u j) ^ 2 +
              (4 * C ^ 2) * conv ^ 2 := by
            exact add_le_add le_rfl htail_sq
      _ =
            8 * (3 ^ d : ℝ) *
                (cubeBesovPositiveVectorDepthSeminorm Q t u j) ^ 2 +
              (4 * C ^ 2) *
                (∑ m ∈ Finset.range j,
                  r ^ (j - m) *
                    cubeBesovPositiveVectorDepthSeminorm Q t u m) ^ 2 := by
            rfl

/-- Version of
`sq_cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_of_sharpBoundaryDepthTail_kernel`
where the geometric kernel bound is supplied term-by-term with the canonical
sharp boundary kernel base.  The only remaining input is the local
single-summand scale arithmetic estimate. -/
theorem sq_cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_of_sharpBoundaryDepthTailTerm_kernel
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (t : ℝ) (N : ℕ) (u : Vec d → Vec d)
    {C : ℝ}
    (ht : t < 1 / 2)
    (hC_nonneg : 0 ≤ C)
    (hres :
      ∀ j ∈ Finset.range (N + 1),
        MeasureTheory.MemLp (fun x => u x - cubeProjectionVec Q j u x)
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hresLoc :
      ∀ j ∈ Finset.range (N + 1), ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (fun x => u x - cubeProjectionVec Q j u x)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hprojLoc :
      ∀ j ∈ Finset.range (N + 1), ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionVec Q j u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hzeroLoc :
      ∀ j ∈ Finset.range (N + 1), ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionVec Q 0 u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hgapLoc :
      ∀ j ∈ Finset.range (N + 1), ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionGapVec Q 0 j u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hincLoc :
      ∀ j ∈ Finset.range (N + 1), ∀ S ∈ overlapCentersAtDepth Q j,
        ∀ m ∈ Finset.range j,
          MeasureTheory.MemLp (cubeIncrementVec Q (m + 1) u)
            (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (huParent :
      ∀ j ∈ Finset.range (N + 1), ∀ m ∈ Finset.range j,
        ∀ T ∈ descendantsAtDepth Q m,
          MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure T))
    (hterm :
      ∀ j ∈ Finset.range (N + 1), ∀ m ∈ Finset.range j,
        sharpBoundaryDepthTailTerm Q t u j m ≤
          C * (sharpBoundaryKernelBase d t) ^ (j - m) *
            cubeBesovPositiveVectorDepthSeminorm Q t u m) :
    (cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q t N u) ^ 2
      ≤
        (8 * (3 ^ d : ℝ) +
            (4 * C ^ 2) * ((1 - sharpBoundaryKernelBase d t)⁻¹) ^ 2) *
          (cubeBesovPositiveVectorPartialSeminormTwo Q t N u) ^ 2 := by
  refine
    sq_cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_of_sharpBoundaryDepthTail_kernel
      (Q := Q) (t := t) (N := N) (u := u)
      (C := C) (r := sharpBoundaryKernelBase d t)
      hC_nonneg (sharpBoundaryKernelBase_nonneg d t)
      (sharpBoundaryKernelBase_lt_one (d := d) (t := t) ht)
      hres hresLoc hprojLoc hzeroLoc hgapLoc hincLoc huParent ?_
  intro j hj
  exact
    sharpBoundaryDepthTail_le_geometric_convolution_of_forall_term_le
      Q t u j
      (C := C) (r := sharpBoundaryKernelBase d t)
      (fun m hm => by
        calc
          sharpBoundaryDepthTailTerm Q t u j m
              ≤ C * (sharpBoundaryKernelBase d t) ^ (j - m) *
                  cubeBesovPositiveVectorDepthSeminorm Q t u m :=
                hterm j hj m hm
          _ =
              C * ((sharpBoundaryKernelBase d t) ^ (j - m) *
                cubeBesovPositiveVectorDepthSeminorm Q t u m) := by
                ring)

/-- Closed finite partial bridge for the sharp boundary branch.  The
overlapping exponent must satisfy `t < 1/2`, exactly because the sharp boundary
kernel has base `3^(t - 1/2)`. -/
theorem sq_cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_sharpBoundaryKernel
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (t : ℝ) (N : ℕ) (u : Vec d → Vec d)
    (ht : t < 1 / 2)
    (hres :
      ∀ j ∈ Finset.range (N + 1),
        MeasureTheory.MemLp (fun x => u x - cubeProjectionVec Q j u x)
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hresLoc :
      ∀ j ∈ Finset.range (N + 1), ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (fun x => u x - cubeProjectionVec Q j u x)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hprojLoc :
      ∀ j ∈ Finset.range (N + 1), ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionVec Q j u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hzeroLoc :
      ∀ j ∈ Finset.range (N + 1), ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionVec Q 0 u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hgapLoc :
      ∀ j ∈ Finset.range (N + 1), ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionGapVec Q 0 j u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hincLoc :
      ∀ j ∈ Finset.range (N + 1), ∀ S ∈ overlapCentersAtDepth Q j,
        ∀ m ∈ Finset.range j,
          MeasureTheory.MemLp (cubeIncrementVec Q (m + 1) u)
            (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (huParent :
      ∀ j ∈ Finset.range (N + 1), ∀ m ∈ Finset.range j,
        ∀ T ∈ descendantsAtDepth Q m,
          MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure T)) :
    (cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q t N u) ^ 2
      ≤
        (8 * (3 ^ d : ℝ) +
            (4 * (sharpBoundaryKernelConstant d) ^ 2) *
              ((1 - sharpBoundaryKernelBase d t)⁻¹) ^ 2) *
          (cubeBesovPositiveVectorPartialSeminormTwo Q t N u) ^ 2 := by
  exact
    sq_cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_of_sharpBoundaryDepthTailTerm_kernel
      (Q := Q) (t := t) (N := N) (u := u)
      (C := sharpBoundaryKernelConstant d)
      ht (sharpBoundaryKernelConstant_nonneg d)
      hres hresLoc hprojLoc hzeroLoc hgapLoc hincLoc huParent
      (fun j _hj m hm =>
        sharpBoundaryDepthTailTerm_le_kernelBase
          (Q := Q) (t := t) (u := u)
          (j := j) (m := m)
          (Nat.le_of_lt (Finset.mem_range.mp hm)))

/-- Square-root form of
`sq_cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_sharpBoundaryKernel`. -/
theorem cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_sqrt_sharpBoundaryKernel
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (t : ℝ) (N : ℕ) (u : Vec d → Vec d)
    (ht : t < 1 / 2)
    (hres :
      ∀ j ∈ Finset.range (N + 1),
        MeasureTheory.MemLp (fun x => u x - cubeProjectionVec Q j u x)
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hresLoc :
      ∀ j ∈ Finset.range (N + 1), ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (fun x => u x - cubeProjectionVec Q j u x)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hprojLoc :
      ∀ j ∈ Finset.range (N + 1), ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionVec Q j u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hzeroLoc :
      ∀ j ∈ Finset.range (N + 1), ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionVec Q 0 u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hgapLoc :
      ∀ j ∈ Finset.range (N + 1), ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionGapVec Q 0 j u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hincLoc :
      ∀ j ∈ Finset.range (N + 1), ∀ S ∈ overlapCentersAtDepth Q j,
        ∀ m ∈ Finset.range j,
          MeasureTheory.MemLp (cubeIncrementVec Q (m + 1) u)
            (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (huParent :
      ∀ j ∈ Finset.range (N + 1), ∀ m ∈ Finset.range j,
        ∀ T ∈ descendantsAtDepth Q m,
          MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure T)) :
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q t N u
      ≤
        Real.sqrt
          (8 * (3 ^ d : ℝ) +
            (4 * (sharpBoundaryKernelConstant d) ^ 2) *
              ((1 - sharpBoundaryKernelBase d t)⁻¹) ^ 2) *
          cubeBesovPositiveVectorPartialSeminormTwo Q t N u := by
  let L : ℝ :=
    8 * (3 ^ d : ℝ) +
      (4 * (sharpBoundaryKernelConstant d) ^ 2) *
        ((1 - sharpBoundaryKernelBase d t)⁻¹) ^ 2
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact add_nonneg
      (mul_nonneg (by norm_num) (by positivity))
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg (sharpBoundaryKernelConstant d)))
        (sq_nonneg _))
  have hsq :=
    sq_cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_sharpBoundaryKernel
      Q t N u ht hres hresLoc hprojLoc hzeroLoc hgapLoc hincLoc huParent
  have hleft_nonneg :
      0 ≤ cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q t N u :=
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo_nonneg Q t N u
  have hright_nonneg :
      0 ≤ Real.sqrt L * cubeBesovPositiveVectorPartialSeminormTwo Q t N u := by
    exact mul_nonneg (Real.sqrt_nonneg _)
      (cubeBesovPositiveVectorPartialSeminormTwo_nonneg Q t N u)
  refine (sq_le_sq₀ hleft_nonneg hright_nonneg).1 ?_
  calc
    (cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q t N u) ^ 2
        ≤
          L * (cubeBesovPositiveVectorPartialSeminormTwo Q t N u) ^ 2 := by
          simpa [L] using hsq
    _ =
          (Real.sqrt L * cubeBesovPositiveVectorPartialSeminormTwo Q t N u) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hL_nonneg]

/-- Full overlapping regularity from ordinary positive regularity and the
sharp-boundary projection MemLp closure package. -/
theorem CubeVectorOverlappingBesovHRegularity.of_sharpBoundaryKernel
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {t : ℝ} {u : Vec d → Vec d}
    (ht : t < 1 / 2)
    (hstd : CubeVectorBesovHRegularity Q t u)
    (hmem : SharpBoundaryProjectionMemLp Q u) :
    CubeVectorOverlappingBesovHRegularity Q t u := by
  refine ⟨hstd.memLp, ?_⟩
  rcases hstd.partialSeminorms_bddAbove with ⟨B, hB⟩
  let L : ℝ :=
    8 * (3 ^ d : ℝ) +
      (4 * (sharpBoundaryKernelConstant d) ^ 2) *
        ((1 - sharpBoundaryKernelBase d t)⁻¹) ^ 2
  refine ⟨Real.sqrt L * B, ?_⟩
  rintro x ⟨N, rfl⟩
  have hpartial :=
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_sqrt_sharpBoundaryKernel
      Q t N u ht
      (fun j _hj => hmem.residual j)
      (fun j _hj => hmem.residual_overlap j)
      (fun j _hj => hmem.projection_overlap j)
      (fun j _hj => hmem.projection_zero_overlap j)
      (fun j _hj => hmem.projection_gap_overlap j)
      (fun j _hj => hmem.increment_overlap j)
      (fun j _hj => hmem.parent j)
  calc
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q t N u
        ≤ Real.sqrt L * cubeBesovPositiveVectorPartialSeminormTwo Q t N u := by
          simpa [L] using hpartial
    _ ≤ Real.sqrt L * B := by
          exact mul_le_mul_of_nonneg_left
            (hB ⟨N, rfl⟩)
            (Real.sqrt_nonneg _)

/-- Full seminorm form of the sharp-boundary comparison. -/
theorem cubeBesovOverlappingPositiveVectorSeminormTwo_le_sqrt_sharpBoundaryKernel
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (t : ℝ) (u : Vec d → Vec d)
    (ht : t < 1 / 2)
    (hstd : CubeVectorBesovHRegularity Q t u)
    (hmem : SharpBoundaryProjectionMemLp Q u) :
    cubeBesovOverlappingPositiveVectorSeminormTwo Q t u ≤
      Real.sqrt (sharpBoundaryKernelLoss d t) *
        cubeBesovPositiveVectorSeminormTwo Q t u := by
  refine cubeBesovOverlappingPositiveVectorSeminormTwo_le_of_partialBound Q t u ?_
  intro N
  have hpartial :=
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_sqrt_sharpBoundaryKernel
      Q t N u ht
      (fun j _hj => hmem.residual j)
      (fun j _hj => hmem.residual_overlap j)
      (fun j _hj => hmem.projection_overlap j)
      (fun j _hj => hmem.projection_zero_overlap j)
      (fun j _hj => hmem.projection_gap_overlap j)
      (fun j _hj => hmem.increment_overlap j)
      (fun j _hj => hmem.parent j)
  calc
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q t N u
        ≤ Real.sqrt (sharpBoundaryKernelLoss d t) *
            cubeBesovPositiveVectorPartialSeminormTwo Q t N u := by
          simpa [sharpBoundaryKernelLoss] using hpartial
    _ ≤ Real.sqrt (sharpBoundaryKernelLoss d t) *
          cubeBesovPositiveVectorSeminormTwo Q t u := by
          exact mul_le_mul_of_nonneg_left
            (by
              unfold cubeBesovPositiveVectorSeminormTwo
              exact le_csSup hstd.partialSeminorms_bddAbove ⟨N, rfl⟩)
            (Real.sqrt_nonneg _)

/-- Full norm form of the sharp-boundary comparison.  The average part is
common to the two positive norms, so the seminorm loss becomes `1 + sqrt L`
on the full norm. -/
theorem cubeBesovOverlappingPositiveVectorNormTwo_le_one_add_sqrt_sharpBoundaryKernel
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (t : ℝ) (u : Vec d → Vec d)
    (ht : t < 1 / 2)
    (hstd : CubeVectorBesovHRegularity Q t u)
    (hmem : SharpBoundaryProjectionMemLp Q u) :
    cubeBesovOverlappingPositiveVectorNormTwo Q t u ≤
      (1 + Real.sqrt (sharpBoundaryKernelLoss d t)) *
        cubeBesovPositiveVectorNormTwo Q t u := by
  let A : ℝ := Real.sqrt (vecNormSq (cubeAverageVec Q u))
  let B : ℝ := cubeBesovPositiveVectorSeminormTwo Q t u
  let C : ℝ := Real.sqrt (sharpBoundaryKernelLoss d t)
  have hsem :
      cubeBesovOverlappingPositiveVectorSeminormTwo Q t u ≤ C * B := by
    simpa [B, C] using
      cubeBesovOverlappingPositiveVectorSeminormTwo_le_sqrt_sharpBoundaryKernel
        Q t u ht hstd hmem
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Real.sqrt_nonneg _
  have hB : 0 ≤ B := by
    dsimp [B]
    unfold cubeBesovPositiveVectorSeminormTwo
    have h0_le :
        cubeBesovPositiveVectorPartialSeminormTwo Q t 0 u ≤
          sSup (Set.range fun N : ℕ =>
            cubeBesovPositiveVectorPartialSeminormTwo Q t N u) :=
      le_csSup hstd.partialSeminorms_bddAbove ⟨0, rfl⟩
    exact (cubeBesovPositiveVectorPartialSeminormTwo_nonneg Q t 0 u).trans h0_le
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Real.sqrt_nonneg _
  unfold cubeBesovOverlappingPositiveVectorNormTwo cubeBesovPositiveVectorNormTwo
  change
    A + cubeBesovOverlappingPositiveVectorSeminormTwo Q t u ≤
      (1 + C) * (A + B)
  calc
    A + cubeBesovOverlappingPositiveVectorSeminormTwo Q t u
        ≤ A + C * B := by
          exact add_le_add le_rfl hsem
    _ ≤ A + C * B + (B + C * A) := by
          exact le_add_of_nonneg_right
            (add_nonneg hB (mul_nonneg hC hA))
    _ = (1 + C) * (A + B) := by ring

end

end Homogenization

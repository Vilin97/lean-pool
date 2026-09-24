/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Profile
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Quantitative smooth cutoffs for round balls

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This independent port uses the native `Fin d → ℝ` carrier and an
explicit Euclidean squared distance.

## Main definitions

* `euclideanBall` and `euclideanClosedBall`: round balls for the explicit
  Euclidean norm.
* `canonicalBallCutoff`: a smooth cutoff with a midpoint support collar.

## Main results

* `canonicalBallCutoff_smooth`, `canonicalBallCutoff_eq_one_on_inner`, and
  `canonicalBallCutoff_tsupport_subset_outer` give the qualitative cutoff
  properties.
* `canonicalBallCutoff_gradient_bound` gives the explicit bound
  `32 / (R - r)`.
-/

@[expose] public section

open Set

noncomputable section

namespace CKN

/-- Euclidean squared distance on native vectors. -/
def euclideanSqDist {d : ℕ} (x y : Vec d) : ℝ :=
  vecNormSq (x - y)

/-- The explicit round Euclidean open ball. -/
def euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ < R ^ 2}

/-- The explicit round Euclidean closed ball. -/
def euclideanClosedBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ ≤ R ^ 2}

@[simp]
theorem euclideanSqDist_self {d : ℕ} (x : Vec d) :
    euclideanSqDist x x = 0 := by
  simp [euclideanSqDist, vecNormSq, vecDot]

theorem mem_euclideanBall_iff_vecEuclideanNorm_lt {d : ℕ}
    {x₀ x : Vec d} {R : ℝ} (hR : 0 < R) :
    x ∈ euclideanBall x₀ R ↔
      vecEuclideanNorm (x - x₀) < R := by
  change vecNormSq (x - x₀) < R ^ 2 ↔
    Real.sqrt (vecNormSq (x - x₀)) < R
  exact (Real.sqrt_lt' hR).symm

theorem mem_euclideanClosedBall_iff_vecEuclideanNorm_le {d : ℕ}
    {x₀ x : Vec d} {R : ℝ} (hR : 0 ≤ R) :
    x ∈ euclideanClosedBall x₀ R ↔
      vecEuclideanNorm (x - x₀) ≤ R := by
  change vecNormSq (x - x₀) ≤ R ^ 2 ↔
    Real.sqrt (vecNormSq (x - x₀)) ≤ R
  exact (Real.sqrt_le_left hR).symm

theorem contDiff_vecNormSq {d : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => vecNormSq x) := by
  unfold vecNormSq vecDot
  exact ContDiff.sum (s := Finset.univ) fun i _hi =>
    (contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i)

theorem contDiff_euclideanSqDist_left {d : ℕ} (x₀ : Vec d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec d => euclideanSqDist x x₀) := by
  unfold euclideanSqDist
  exact contDiff_vecNormSq.comp (contDiff_id.sub contDiff_const)

theorem isClosed_euclideanClosedBall {d : ℕ} (x₀ : Vec d) (R : ℝ) :
    IsClosed (euclideanClosedBall x₀ R) := by
  change IsClosed
    ((fun x : Vec d => euclideanSqDist x x₀) ⁻¹' Iic (R ^ 2))
  exact isClosed_Iic.preimage (contDiff_euclideanSqDist_left x₀).continuous

theorem sq_coord_sub_le_euclideanSqDist {d : ℕ}
    (x y : Vec d) (i : Fin d) :
    (x i - y i) ^ 2 ≤ euclideanSqDist x y := by
  simpa [euclideanSqDist, Pi.sub_apply] using
    sq_apply_le_vecNormSq (x - y) i

/-- A round closed ball is contained in the inherited supremum-metric closed
ball with the same nonnegative radius. -/
theorem euclideanClosedBall_subset_supClosedBall {d : ℕ}
    {x₀ : Vec d} {R : ℝ} (hR : 0 ≤ R) :
    euclideanClosedBall x₀ R ⊆ Metric.closedBall x₀ R := by
  intro x hx
  rw [Metric.mem_closedBall, dist_pi_le_iff hR]
  intro i
  have hsqi : (x i - x₀ i) ^ 2 ≤ R ^ 2 :=
    (sq_coord_sub_le_euclideanSqDist x x₀ i).trans hx
  have habs : |x i - x₀ i| ≤ R :=
    abs_le_of_sq_le_sq hsqi hR
  simpa [Real.dist_eq, abs_sub_comm] using habs

theorem isCompact_euclideanClosedBall {d : ℕ}
    (x₀ : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (euclideanClosedBall x₀ R) :=
  (ProperSpace.isCompact_closedBall x₀ R).of_isClosed_subset
    (isClosed_euclideanClosedBall x₀ R)
    (euclideanClosedBall_subset_supClosedBall hR)

theorem euclideanClosedBall_subset_euclideanBall {d : ℕ}
    {x₀ : Vec d} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    euclideanClosedBall x₀ r ⊆ euclideanBall x₀ R := by
  intro x hx
  change euclideanSqDist x x₀ < R ^ 2
  change euclideanSqDist x x₀ ≤ r ^ 2 at hx
  nlinarith only [hx, hr, hrR]

/-- The strict midpoint radius keeps the support inside the outer ball. -/
def ballCutoffMidRadius (r R : ℝ) : ℝ :=
  (r + R) / 2

/-- Squared-radius interpolation variable for a round cutoff. -/
def ballCutoffArgument {d : ℕ}
    (x₀ : Vec d) (r s : ℝ) (x : Vec d) : ℝ :=
  (s ^ 2 - euclideanSqDist x x₀) / (s ^ 2 - r ^ 2)

/-- The canonical ball cutoff, with a midpoint support collar. -/
def canonicalBallCutoff {d : ℕ}
    (x₀ : Vec d) (r R : ℝ) : Vec d → ℝ :=
  smoothTransitionProfile ∘
    ballCutoffArgument x₀ r (ballCutoffMidRadius r R)

def ballCutoffWithSupportRadius {d : ℕ}
    (x₀ : Vec d) (r s : ℝ) : Vec d → ℝ :=
  smoothTransitionProfile ∘ ballCutoffArgument x₀ r s

private theorem ballCutoffArgument_den_pos {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r < s) :
    0 < s ^ 2 - r ^ 2 := by
  have hs : 0 < s := lt_of_le_of_lt hr hrs
  calc
    0 < (s - r) * (s + r) :=
      mul_pos (sub_pos.mpr hrs) (add_pos_of_pos_of_nonneg hs hr)
    _ = s ^ 2 - r ^ 2 := by
      ring

private theorem inner_lt_ballCutoffMidRadius {r R : ℝ}
    (hrR : r < R) :
    r < ballCutoffMidRadius r R := by
  unfold ballCutoffMidRadius
  linarith only [hrR]

private theorem ballCutoffMidRadius_lt_outer {r R : ℝ}
    (hrR : r < R) :
    ballCutoffMidRadius r R < R := by
  unfold ballCutoffMidRadius
  linarith only [hrR]

private theorem ballCutoffMidRadius_nonneg {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) :
    0 ≤ ballCutoffMidRadius r R := by
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  unfold ballCutoffMidRadius
  positivity

private theorem ballCutoffMidRadius_sub_inner {r R : ℝ} :
    ballCutoffMidRadius r R - r = (R - r) / 2 := by
  unfold ballCutoffMidRadius
  ring

private theorem fderiv_coord_sub_const_apply_basisVec {d : ℕ}
    (i j : Fin d) (c x : Vec d) :
    (fderiv ℝ (fun y : Vec d => y i - c i) x) (basisVec j) =
      if j = i then 1 else 0 := by
  rw [fderiv_sub_const]
  change
    (fderiv ℝ (⇑(ContinuousLinearMap.proj (R := ℝ) i)) x)
        (basisVec j) =
      _
  rw [ContinuousLinearMap.fderiv]
  simp [basisVec_apply, eq_comm]

private theorem fderiv_coord_sub_const_sq_apply_basisVec {d : ℕ}
    (i j : Fin d) (c x : Vec d) :
    (fderiv ℝ (fun y : Vec d => (y i - c i) ^ 2) x)
        (basisVec j) =
      2 * (x i - c i) * (if j = i then 1 else 0) := by
  rw [fderiv_fun_pow]
  · simp [fderiv_coord_sub_const_apply_basisVec, pow_one,
      smul_eq_mul]
  · fun_prop

private theorem fderiv_euclideanSqDist_apply_basisVec {d : ℕ}
    (x₀ x : Vec d) (j : Fin d) :
    (fderiv ℝ (fun y : Vec d => euclideanSqDist y x₀) x)
        (basisVec j) =
      2 * (x j - x₀ j) := by
  have hfun :
      (fun y : Vec d => euclideanSqDist y x₀) =
        fun y : Vec d => ∑ i : Fin d, (y i - x₀ i) ^ 2 := by
    funext y
    simp only [euclideanSqDist, vecNormSq_eq_sum_sq, Pi.sub_apply]
  rw [hfun, fderiv_fun_sum]
  · simp [fderiv_coord_sub_const_sq_apply_basisVec]
  · intro i _hi
    fun_prop

private theorem fderiv_ballCutoffArgument_apply_basisVec {d : ℕ}
    (x₀ : Vec d) (r s : ℝ) (j : Fin d) (x : Vec d) :
    (fderiv ℝ (ballCutoffArgument x₀ r s) x) (basisVec j) =
      (-(2 * (x j - x₀ j))) / (s ^ 2 - r ^ 2) := by
  unfold ballCutoffArgument
  simp only [div_eq_mul_inv]
  rw [fderiv_mul_const]
  · rw [fderiv_const_sub]
    simp [fderiv_euclideanSqDist_apply_basisVec, neg_mul]
    ring
  · exact
      ((contDiff_const.sub
        (contDiff_euclideanSqDist_left x₀)).differentiable
          (by simp)) x

private theorem ballCutoffArgument_contDiff {d : ℕ}
    {x₀ : Vec d} {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s) :
    ContDiff ℝ (⊤ : ℕ∞)
      (ballCutoffArgument x₀ r s) := by
  unfold ballCutoffArgument
  exact
    (contDiff_const.sub (contDiff_euclideanSqDist_left x₀)).div
      contDiff_const
      (fun _ => (ballCutoffArgument_den_pos hr hrs).ne')

private theorem ballCutoffWithSupportRadius_smooth {d : ℕ}
    {x₀ : Vec d} {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s) :
    ContDiff ℝ (⊤ : ℕ∞)
      (ballCutoffWithSupportRadius x₀ r s) := by
  exact smoothTransitionProfile.smooth.comp
    (ballCutoffArgument_contDiff hr hrs)

private theorem ballCutoffWithSupportRadius_eq_one {d : ℕ}
    {x₀ : Vec d} {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s)
    {x : Vec d} (hx : x ∈ euclideanBall x₀ r) :
    ballCutoffWithSupportRadius x₀ r s x = 1 := by
  apply smoothTransitionProfile.one_of_one_le
  unfold ballCutoffArgument
  have hden := ballCutoffArgument_den_pos hr hrs
  rw [one_le_div hden]
  change euclideanSqDist x x₀ < r ^ 2 at hx
  linarith only [hx]

private theorem ballCutoffWithSupportRadius_eq_zero_of_not_mem_closedBall
    {d : ℕ} {x₀ : Vec d} {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r < s) {x : Vec d}
    (hx : x ∉ euclideanClosedBall x₀ s) :
    ballCutoffWithSupportRadius x₀ r s x = 0 := by
  apply smoothTransitionProfile.zero_of_nonpos
  unfold ballCutoffArgument
  have hdenNonneg :
      0 ≤ s ^ 2 - r ^ 2 :=
    (ballCutoffArgument_den_pos hr hrs).le
  have hnumNonpos :
      s ^ 2 - euclideanSqDist x x₀ ≤ 0 := by
    change ¬euclideanSqDist x x₀ ≤ s ^ 2 at hx
    exact sub_nonpos.mpr (le_of_lt (not_le.mp hx))
  exact div_nonpos_of_nonpos_of_nonneg hnumNonpos hdenNonneg

private theorem ballCutoffWithSupportRadius_support_subset_closedBall
    {d : ℕ} {x₀ : Vec d} {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r < s) :
    Function.support (ballCutoffWithSupportRadius x₀ r s) ⊆
      euclideanClosedBall x₀ s := by
  intro x hx
  by_contra hnot
  exact hx
    (ballCutoffWithSupportRadius_eq_zero_of_not_mem_closedBall
      hr hrs hnot)

private theorem ballCutoffWithSupportRadius_tsupport_subset_closedBall
    {d : ℕ} {x₀ : Vec d} {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r < s) :
    tsupport (ballCutoffWithSupportRadius x₀ r s) ⊆
      euclideanClosedBall x₀ s :=
  closure_minimal
    (ballCutoffWithSupportRadius_support_subset_closedBall hr hrs)
    (isClosed_euclideanClosedBall x₀ s)

private theorem ballCutoffWithSupportRadius_hasCompactSupport
    {d : ℕ} {x₀ : Vec d} {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r < s) :
    HasCompactSupport (ballCutoffWithSupportRadius x₀ r s) := by
  have hs : 0 ≤ s := (lt_of_le_of_lt hr hrs).le
  exact HasCompactSupport.of_support_subset_isCompact
    (isCompact_euclideanClosedBall x₀ hs)
    (ballCutoffWithSupportRadius_support_subset_closedBall hr hrs)

private theorem classicalGradient_ballCutoffArgument {d : ℕ}
    (x₀ : Vec d) (r s : ℝ) (x : Vec d) :
    classicalGradient (ballCutoffArgument x₀ r s) x =
      (-(2 / (s ^ 2 - r ^ 2))) • (x - x₀) := by
  funext i
  rw [classicalGradient_apply,
    fderiv_ballCutoffArgument_apply_basisVec]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

private theorem ballCutoffArgument_gradient_bound_of_mem_closedBall
    {d : ℕ} {x₀ : Vec d} {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r < s) {x : Vec d}
    (hx : x ∈ euclideanClosedBall x₀ s) :
    vecEuclideanNorm
        (classicalGradient (ballCutoffArgument x₀ r s) x) ≤
      2 / (s - r) := by
  have hs : 0 < s := lt_of_le_of_lt hr hrs
  have hgap : 0 < s - r := sub_pos.mpr hrs
  have hsum : 0 < s + r := add_pos_of_pos_of_nonneg hs hr
  have hden : 0 < s ^ 2 - r ^ 2 :=
    ballCutoffArgument_den_pos hr hrs
  have hnorm :
      vecEuclideanNorm (x - x₀) ≤ s :=
    (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hs.le).mp hx
  have hcoef :
      |-(2 / (s ^ 2 - r ^ 2))| =
        2 / (s ^ 2 - r ^ 2) := by
    rw [abs_neg, abs_of_pos (div_pos (by norm_num) hden)]
  rw [classicalGradient_ballCutoffArgument,
    vecEuclideanNorm_smul, hcoef]
  calc
    2 / (s ^ 2 - r ^ 2) * vecEuclideanNorm (x - x₀)
        ≤ 2 / (s ^ 2 - r ^ 2) * s :=
      mul_le_mul_of_nonneg_left hnorm
        (div_nonneg (by norm_num) hden.le)
    _ = (2 / (s - r)) * (s / (s + r)) := by
      have hdenEq :
          s ^ 2 - r ^ 2 = (s - r) * (s + r) := by
        ring
      rw [hdenEq]
      field_simp [hgap.ne', hsum.ne']
    _ ≤ (2 / (s - r)) * 1 :=
      mul_le_mul_of_nonneg_left
        ((div_le_one hsum).mpr (by linarith only [hr]))
        (div_nonneg (by norm_num) hgap.le)
    _ = 2 / (s - r) := by
      ring

private theorem classicalGradient_ballCutoffWithSupportRadius {d : ℕ}
    {x₀ : Vec d} {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s)
    (x : Vec d) :
    classicalGradient (ballCutoffWithSupportRadius x₀ r s) x =
      deriv smoothTransitionProfile (ballCutoffArgument x₀ r s x) •
        classicalGradient (ballCutoffArgument x₀ r s) x := by
  have hProfile :
      DifferentiableAt ℝ smoothTransitionProfile
        (ballCutoffArgument x₀ r s x) :=
    smoothTransitionProfile.smooth.differentiable (by simp) _
  have hArgument :
      DifferentiableAt ℝ (ballCutoffArgument x₀ r s) x :=
    (ballCutoffArgument_contDiff hr hrs).differentiable (by simp) x
  funext i
  change
    (fderiv ℝ
        (fun y =>
          smoothTransitionProfile (ballCutoffArgument x₀ r s y)) x)
        (basisVec i) =
      _
  rw [fderiv_fun_comp x hProfile hArgument]
  simp only [ContinuousLinearMap.comp_apply, fderiv_eq_deriv_mul,
    Pi.smul_apply, smul_eq_mul, classicalGradient_apply]

private theorem ballCutoffWithSupportRadius_gradient_bound_of_mem_closedBall
    {d : ℕ} {x₀ : Vec d} {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r < s) {x : Vec d}
    (hx : x ∈ euclideanClosedBall x₀ s) :
    vecEuclideanNorm
        (classicalGradient (ballCutoffWithSupportRadius x₀ r s) x) ≤
      16 / (s - r) := by
  rw [classicalGradient_ballCutoffWithSupportRadius hr hrs,
    vecEuclideanNorm_smul]
  calc
    |deriv smoothTransitionProfile
          (ballCutoffArgument x₀ r s x)| *
        vecEuclideanNorm
          (classicalGradient (ballCutoffArgument x₀ r s) x)
        ≤
      8 *
        vecEuclideanNorm
          (classicalGradient (ballCutoffArgument x₀ r s) x) :=
      mul_le_mul_of_nonneg_right
        (smoothTransitionProfile.abs_deriv_le_eight _)
        (vecEuclideanNorm_nonneg _)
    _ ≤ 8 * (2 / (s - r)) :=
      mul_le_mul_of_nonneg_left
        (ballCutoffArgument_gradient_bound_of_mem_closedBall
          hr hrs hx)
        (by norm_num)
    _ = 16 / (s - r) := by
      ring

/-- The canonical midpoint-collar cutoff is smooth to every order. -/
theorem canonicalBallCutoff_smooth {d : ℕ}
    (x₀ : Vec d) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    ContDiff ℝ (⊤ : ℕ∞) (canonicalBallCutoff x₀ r R) := by
  simpa [canonicalBallCutoff, ballCutoffWithSupportRadius] using
    ballCutoffWithSupportRadius_smooth
      (x₀ := x₀) hr
        (inner_lt_ballCutoffMidRadius hrR)

/-- The canonical midpoint-collar cutoff is nonnegative. -/
theorem canonicalBallCutoff_nonneg {d : ℕ}
    (x₀ : Vec d) (r R : ℝ) (x : Vec d) :
    0 ≤ canonicalBallCutoff x₀ r R x :=
  smoothTransitionProfile.nonneg _

/-- The canonical midpoint-collar cutoff is at most one. -/
theorem canonicalBallCutoff_le_one {d : ℕ}
    (x₀ : Vec d) (r R : ℝ) (x : Vec d) :
    canonicalBallCutoff x₀ r R x ≤ 1 :=
  smoothTransitionProfile.le_one _

/-- The canonical midpoint-collar cutoff equals one on the inner open ball. -/
theorem canonicalBallCutoff_eq_one_on_inner {d : ℕ}
    {x₀ : Vec d} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {x : Vec d} (hx : x ∈ euclideanBall x₀ r) :
    canonicalBallCutoff x₀ r R x = 1 := by
  simpa [canonicalBallCutoff, ballCutoffWithSupportRadius] using
    ballCutoffWithSupportRadius_eq_one
      hr (inner_lt_ballCutoffMidRadius hrR) hx

/-- The topological support lies inside the outer open ball. -/
theorem canonicalBallCutoff_tsupport_subset_outer {d : ℕ}
    {x₀ : Vec d} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    tsupport (canonicalBallCutoff x₀ r R) ⊆
      euclideanBall x₀ R := by
  have hclosed :
      tsupport
          (ballCutoffWithSupportRadius x₀ r
            (ballCutoffMidRadius r R)) ⊆
        euclideanClosedBall x₀ (ballCutoffMidRadius r R) :=
    ballCutoffWithSupportRadius_tsupport_subset_closedBall
      hr (inner_lt_ballCutoffMidRadius hrR)
  have hstrict :
      euclideanClosedBall x₀ (ballCutoffMidRadius r R) ⊆
        euclideanBall x₀ R :=
    euclideanClosedBall_subset_euclideanBall
      (ballCutoffMidRadius_nonneg hr hrR)
      (ballCutoffMidRadius_lt_outer hrR)
  simpa [canonicalBallCutoff, ballCutoffWithSupportRadius] using
    hclosed.trans hstrict

/-- The canonical midpoint-collar cutoff has compact support. -/
theorem canonicalBallCutoff_hasCompactSupport {d : ℕ}
    {x₀ : Vec d} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    HasCompactSupport (canonicalBallCutoff x₀ r R) := by
  simpa [canonicalBallCutoff, ballCutoffWithSupportRadius] using
    ballCutoffWithSupportRadius_hasCompactSupport
      (x₀ := x₀) hr
        (inner_lt_ballCutoffMidRadius hrR)

/-- The midpoint-collar cutoff has the explicit bound `32 / (R - r)`. -/
theorem canonicalBallCutoff_gradient_bound {d : ℕ}
    {x₀ : Vec d} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (x : Vec d) :
    vecEuclideanNorm
        (classicalGradient (canonicalBallCutoff x₀ r R) x) ≤
      32 / (R - r) := by
  let s := ballCutoffMidRadius r R
  have hrs : r < s := by
    exact inner_lt_ballCutoffMidRadius hrR
  have hsGap : s - r = (R - r) / 2 := by
    exact ballCutoffMidRadius_sub_inner
  change
    vecEuclideanNorm
        (classicalGradient
          (ballCutoffWithSupportRadius x₀ r s) x) ≤
      32 / (R - r)
  by_cases hx : x ∈ euclideanClosedBall x₀ s
  · calc
      vecEuclideanNorm
          (classicalGradient
            (ballCutoffWithSupportRadius x₀ r s) x)
          ≤ 16 / (s - r) :=
        ballCutoffWithSupportRadius_gradient_bound_of_mem_closedBall
          hr hrs hx
      _ = 32 / (R - r) := by
        rw [hsGap]
        field_simp [(sub_pos.mpr hrR).ne']
        ring
  · have hxTSupport :
        x ∉ tsupport (ballCutoffWithSupportRadius x₀ r s) :=
      fun hxs =>
        hx
          (ballCutoffWithSupportRadius_tsupport_subset_closedBall
            hr hrs hxs)
    have hfderiv :
        fderiv ℝ (ballCutoffWithSupportRadius x₀ r s) x = 0 :=
      fderiv_of_notMem_tsupport ℝ hxTSupport
    have hgradient :
        classicalGradient
            (ballCutoffWithSupportRadius x₀ r s) x =
          0 := by
      funext i
      rw [classicalGradient_apply, hfderiv]
      exact zero_apply _
    rw [hgradient,
      (vecEuclideanNorm_eq_zero_iff.mpr rfl)]
    exact div_nonneg (by norm_num) (sub_pos.mpr hrR).le

end CKN

/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanDuhamelHessian
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.FiniteCoordinateFrechet
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Operator packaging of the Euclidean Duhamel Hessian

The full coordinate gradient and Hessian are assembled here as continuous
linear maps on `Fin n → ℝ`.  This removes the diagonal-only obstruction to a
genuine parabolic second jet: the packaged Hessian contains every mixed entry,
is continuous in space, has a global operator-norm bound, and represents every
actual iterated coordinate derivative proved in the preceding module.
-/

@[expose] public noncomputable section
open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

section OperatorPackaging

-- These more-specific instances prevent typeclass search from getting stuck
-- while recursively constructing the normed structure on a curried bilinear
-- operator space.
local instance coordinateDualNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance coordinateBilinearNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance coordinateBilinearContinuousAdd {n : ℕ} :
    ContinuousAdd ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  IsTopologicalAddGroup.toContinuousAdd

/-- A coefficient vector as a continuous linear functional on finite
coordinate space. -/
def coordinateLinearFunctional {n : ℕ} (a : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ k : Fin n, a k • ContinuousLinearMap.proj k

@[simp] theorem coordinateLinearFunctional_apply {n : ℕ}
    (a v : Fin n → ℝ) :
    coordinateLinearFunctional a v = ∑ k : Fin n, a k * v k := by
  simp [coordinateLinearFunctional]

@[simp] theorem coordinateLinearFunctional_single {n : ℕ}
    (a : Fin n → ℝ) (j : Fin n) :
    coordinateLinearFunctional a (Pi.single j 1) = a j := by
  classical
  rw [coordinateLinearFunctional_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · simp

/-- A coordinate projection has operator norm at most one for the sup norm. -/
lemma norm_coordinateProjection_le {n : ℕ} (k : Fin n) :
    ‖(ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [one_mul, ContinuousLinearMap.proj_apply] using
    ((pi_norm_le_iff_of_nonneg (norm_nonneg v)).mp le_rfl k)

/-- The `l¹` coefficient bound for the coordinate functional. -/
lemma norm_coordinateLinearFunctional_le {n : ℕ} (a : Fin n → ℝ) :
    ‖coordinateLinearFunctional a‖ ≤ ∑ k : Fin n, |a k| := by
  rw [coordinateLinearFunctional]
  calc
    ‖∑ k : Fin n, a k • (ContinuousLinearMap.proj k :
        (Fin n → ℝ) →L[ℝ] ℝ)‖ ≤
        ∑ k : Fin n, ‖a k • (ContinuousLinearMap.proj k :
          (Fin n → ℝ) →L[ℝ] ℝ)‖ := norm_sum_le _ _
    _ ≤ ∑ k : Fin n, |a k| := by
      gcongr with k
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg (a k))
        (norm_coordinateProjection_le k))

/-- Rank-one coordinate bilinear form, curried as a linear map into the dual. -/
def coordinateRankOne {n : ℕ} (j k : Fin n) :
    (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ) :=
  (ContinuousLinearMap.proj j).smulRight (ContinuousLinearMap.proj k)

@[simp] theorem coordinateRankOne_apply {n : ℕ} (j k : Fin n)
    (v w : Fin n → ℝ) : coordinateRankOne j k v w = v j * w k := by
  simp [coordinateRankOne, ContinuousLinearMap.smulRight_apply]

lemma norm_coordinateRankOne_le {n : ℕ} (j k : Fin n) :
    ‖coordinateRankOne j k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  unfold coordinateRankOne
  simp only [ContinuousLinearMap.smulRight_apply]
  apply le_trans (norm_smul_le (v j) (ContinuousLinearMap.proj k))
  rw [one_mul]
  calc
    ‖v j‖ * ‖(ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ)‖ ≤
        ‖v‖ * 1 := mul_le_mul
      ((pi_norm_le_iff_of_nonneg (norm_nonneg v)).mp le_rfl j)
      (norm_coordinateProjection_le k) (norm_nonneg _) (norm_nonneg _)
    _ = ‖v‖ := mul_one _

/-- A coordinate matrix as a curried continuous bilinear form. -/
def coordinateHessianCLM {n : ℕ} (A : Fin n → Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ) :=
  ∑ j : Fin n, ∑ k : Fin n, A j k • coordinateRankOne j k

@[simp] theorem coordinateHessianCLM_apply {n : ℕ}
    (A : Fin n → Fin n → ℝ) (v w : Fin n → ℝ) :
    coordinateHessianCLM A v w =
      ∑ j : Fin n, ∑ k : Fin n, A j k * (v j * w k) := by
  simp [coordinateHessianCLM, coordinateRankOne,
    ContinuousLinearMap.smulRight_apply]

/-- The operator norm is bounded by the sum of absolute coordinate entries. -/
lemma norm_coordinateHessianCLM_le {n : ℕ} (A : Fin n → Fin n → ℝ) :
    ‖coordinateHessianCLM A‖ ≤
      ∑ j : Fin n, ∑ k : Fin n, |A j k| := by
  rw [coordinateHessianCLM]
  calc
    ‖∑ j : Fin n, ∑ k : Fin n, A j k • coordinateRankOne j k‖ ≤
        ∑ j : Fin n, ‖∑ k : Fin n, A j k • coordinateRankOne j k‖ :=
      by simpa using (norm_sum_le Finset.univ
        (fun j => ∑ k : Fin n, A j k • coordinateRankOne j k))
    _ ≤ ∑ j : Fin n, ∑ k : Fin n, ‖A j k • coordinateRankOne j k‖ := by
      gcongr with j
      simpa using (norm_sum_le Finset.univ
        (fun k => A j k • coordinateRankOne j k))
    _ ≤ ∑ j : Fin n, ∑ k : Fin n, |A j k| := by
      gcongr with j k
      calc
        ‖A j k • coordinateRankOne j k‖ ≤
            ‖A j k‖ * ‖coordinateRankOne j k‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ |A j k| := by
          rw [Real.norm_eq_abs]
          exact mul_le_of_le_one_right (abs_nonneg (A j k))
            (norm_coordinateRankOne_le j k)

/-- Transposition swaps the arguments of the packaged Hessian. -/
theorem coordinateHessianCLM_transpose_apply {n : ℕ}
    (A : Fin n → Fin n → ℝ) (v w : Fin n → ℝ) :
    coordinateHessianCLM (fun j k => A k j) v w =
      coordinateHessianCLM A w v := by
  simp only [coordinateHessianCLM_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The heat Hessian kernel is symmetric in its two derivative indices. -/
theorem heatHessianKernelEntryND_comm {n : ℕ} (t : ℝ)
    (z : Fin n → ℝ) (j k : Fin n) :
    heatHessianKernelEntryND t z j k = heatHessianKernelEntryND t z k j := by
  unfold heatHessianKernelEntryND
  by_cases hjk : j = k
  · subst j
    rfl
  · have hkj : k ≠ j := Ne.symm hjk
    simp only [if_neg hjk, if_neg hkj]
    ring

theorem heatDuhamelHessianEntryND_comm {n : ℕ} (t₀ t : ℝ)
    (q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (j k : Fin n) (x : Fin n → ℝ) :
    heatDuhamelHessianEntryND t₀ t q j k x =
      heatDuhamelHessianEntryND t₀ t q k j x := by
  unfold heatDuhamelHessianEntryND heatHessianEntryConvolutionND
  apply intervalIntegral.integral_congr
  intro s _
  apply integral_congr_ae
  filter_upwards with y
  rw [heatHessianKernelEntryND_comm (t - s) (x - y) j k]

/-- The spatial gradient of the Duhamel potential, packaged as a continuous
linear functional. -/
def heatDuhamelGradientCLM {n : ℕ} (t₀ t : ℝ)
    (q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (x : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  coordinateLinearFunctional (fun k => heatDuhamelGradientCoordND t₀ t q k x)

@[simp] theorem heatDuhamelGradientCLM_apply {n : ℕ} (t₀ t : ℝ)
    (q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (x v : Fin n → ℝ) :
    heatDuhamelGradientCLM t₀ t q x v =
      ∑ k : Fin n, heatDuhamelGradientCoordND t₀ t q k x * v k := by
  simp [heatDuhamelGradientCLM]

/-- The spatial Hessian of the Duhamel potential, packaged as a continuous
linear map into the continuous dual. -/
def heatDuhamelHessianCLM
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ) :=
  coordinateHessianCLM (fun j k =>
    heatDuhamelHessianEntryNDbcf hT hr0 hq hH hqb hqholder j k x)

@[simp] theorem heatDuhamelHessianCLM_apply
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x v w : Fin n → ℝ) :
    heatDuhamelHessianCLM hT hr0 hq hH hqb hqholder x v w =
      ∑ j : Fin n, ∑ k : Fin n,
        heatDuhamelHessianEntryND t₀ t q j k x * (v j * w k) := by
  simp [heatDuhamelHessianCLM]

/-- The packaged Duhamel Hessian is symmetric. -/
theorem heatDuhamelHessianCLM_comm
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x v w : Fin n → ℝ) :
    heatDuhamelHessianCLM hT hr0 hq hH hqb hqholder x v w =
      heatDuhamelHessianCLM hT hr0 hq hH hqb hqholder x w v := by
  simp only [heatDuhamelHessianCLM_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [heatDuhamelHessianEntryND_comm]
  ring

/-- The operator-valued Hessian is continuous in space. -/
theorem continuous_heatDuhamelHessianCLM
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    Continuous (heatDuhamelHessianCLM hT hr0 hq hH hqb hqholder) := by
  unfold heatDuhamelHessianCLM coordinateHessianCLM
  apply continuous_finsetSum
  intro j _
  apply continuous_finsetSum
  intro k _
  exact (heatDuhamelHessianEntryNDbcf hT hr0 hq hH hqb hqholder j k).continuous.smul
    continuous_const

end OperatorPackaging

/-- A fixed output coordinate of the Duhamel gradient has the corresponding
column of the Hessian as its genuine Frechet derivative. -/
theorem hasFDerivAt_heatDuhamelGradientCoordND
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (k : Fin n) (x : Fin n → ℝ) :
    HasFDerivAt (heatDuhamelGradientCoordND t₀ t q k)
      (coordinateLinearFunctional (fun j =>
        heatDuhamelHessianEntryNDbcf hT hr0 hq hH hqb hqholder j k x)) x := by
  classical
  refine hasFDerivAt_of_continuous_coordinate_derivatives
    (heatDuhamelGradientCoordND t₀ t q k)
    (fun z => coordinateLinearFunctional (fun j =>
      heatDuhamelHessianEntryNDbcf hT hr0 hq hH hqb hqholder j k z)) ?_ ?_ x
  · unfold coordinateLinearFunctional
    apply continuous_finsetSum
    intro j _
    exact (heatDuhamelHessianEntryNDbcf
      hT hr0 hq hH hqb hqholder j k).continuous.smul continuous_const
  · intro z j
    have h := (hasDerivAt_heatDuhamelGradientCoordND_entry
      hT hr0 hq hH hqb hqholder z j k).hasFDerivAt
    have hval : coordinateLinearFunctional (fun i =>
        heatDuhamelHessianEntryNDbcf hT hr0 hq hH hqb hqholder i k z)
        (Pi.single j 1) = heatDuhamelHessianEntryND t₀ t q j k z := by
      exact coordinateLinearFunctional_single _ j
    rw [hval]
    exact h

/-- The operator-valued Duhamel gradient is continuous in space. -/
theorem continuous_heatDuhamelGradientCLM
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    Continuous (heatDuhamelGradientCLM t₀ t q) := by
  unfold heatDuhamelGradientCLM coordinateLinearFunctional
  apply continuous_finsetSum
  intro k _
  exact (continuous_iff_continuousAt.mpr fun x =>
    (hasFDerivAt_heatDuhamelGradientCoordND
      hT hr0 hq hH hqb hqholder k x).continuousAt).smul continuous_const

/-- The Duhamel potential has the packaged spatial gradient as its genuine
Frechet derivative. -/
theorem hasFDerivAt_heatDuhamelND
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    HasFDerivAt (fun z : Fin n → ℝ => ∫ s in t₀..t,
      heatSemigroupND (t - s) (q s) z)
      (heatDuhamelGradientCLM t₀ t q x) x := by
  classical
  apply hasFDerivAt_of_continuous_coordinate_derivatives
  · exact continuous_heatDuhamelGradientCLM
      hT hr0 hq hH hqb hqholder
  · intro z k
    have h := (hasDerivAt_heatDuhamelND_coord hT hq hqb z k).hasFDerivAt
    have hval : heatDuhamelGradientCLM t₀ t q z (Pi.single k 1) =
        heatDuhamelGradientCoordND t₀ t q k z := by
      exact coordinateLinearFunctional_single _ k
    rw [hval]
    simpa only [heatDuhamelGradientCoordND] using h

/-- The operator-valued spatial gradient has the packaged Hessian as its
genuine Frechet derivative. -/
theorem hasFDerivAt_heatDuhamelGradientCLM
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    HasFDerivAt (heatDuhamelGradientCLM t₀ t q)
      (heatDuhamelHessianCLM hT hr0 hq hH hqb hqholder x) x := by
  classical
  apply hasFDerivAt_of_continuous_coordinate_derivatives
  · exact continuous_heatDuhamelHessianCLM
      hT hr0 hq hH hqb hqholder
  · intro z j
    have hderiv : HasDerivAt
        (fun a => heatDuhamelGradientCLM t₀ t q (Function.update z j a))
        (∑ k : Fin n, heatDuhamelHessianEntryND t₀ t q j k z •
          (ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ)) (z j) := by
      unfold heatDuhamelGradientCLM coordinateLinearFunctional
      have hfun : (fun a => ∑ k : Fin n,
          heatDuhamelGradientCoordND t₀ t q k (Function.update z j a) •
            (ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ)) =
          ∑ k : Fin n, fun a => heatDuhamelGradientCoordND t₀ t q k
            (Function.update z j a) •
              (ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ) := by
        funext a
        simp only [Finset.sum_apply]
      rw [hfun]
      exact HasDerivAt.sum (u := Finset.univ) fun k _ =>
        (hasDerivAt_heatDuhamelGradientCoordND_entry
          hT hr0 hq hH hqb hqholder z j k).smul_const
            (ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ)
    have h := hderiv.hasFDerivAt
    simpa [heatDuhamelHessianCLM, coordinateHessianCLM, coordinateRankOne,
      coordinateLinearFunctional, Pi.single_apply] using h

/-- At every fixed final time, the Euclidean Duhamel potential is genuinely
twice continuously Frechet differentiable in space. -/
theorem contDiff_two_heatDuhamelND
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    ContDiff ℝ 2 (fun z : Fin n → ℝ => ∫ s in t₀..t,
      heatSemigroupND (t - s) (q s) z) := by
  apply (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
  refine ⟨heatDuhamelGradientCLM t₀ t q, ?_,
    hasFDerivAt_heatDuhamelND hT hr0 hq hH hqb hqholder⟩
  exact contDiff_one_iff_hasFDerivAt.mpr
    ⟨heatDuhamelHessianCLM hT hr0 hq hH hqb hqholder,
      continuous_heatDuhamelHessianCLM hT hr0 hq hH hqb hqholder,
      hasFDerivAt_heatDuhamelGradientCLM hT hr0 hq hH hqb hqholder⟩

section RemainingOperatorPackaging

local instance remainingCoordinateDualNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance remainingCoordinateBilinearNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance remainingCoordinateBilinearContinuousAdd {n : ℕ} :
    ContinuousAdd ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  IsTopologicalAddGroup.toContinuousAdd

/-- Global operator-norm bound by the finite sum of the bundled entry norms. -/
theorem norm_heatDuhamelHessianCLM_le
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    ‖heatDuhamelHessianCLM hT hr0 hq hH hqb hqholder x‖ ≤
      ∑ j : Fin n, ∑ k : Fin n,
        ‖heatDuhamelHessianEntryNDbcf hT hr0 hq hH hqb hqholder j k‖ := by
  apply (norm_coordinateHessianCLM_le (fun j k =>
    heatDuhamelHessianEntryNDbcf hT hr0 hq hH hqb hqholder j k x)).trans
  gcongr with j k
  simpa only [Real.norm_eq_abs] using
    (heatDuhamelHessianEntryNDbcf hT hr0 hq hH hqb hqholder j k).norm_coe_le_norm x

/-- Every coordinate entry of the operator Hessian is an actual iterated
derivative of the Duhamel potential. -/
theorem hasDerivAt_partial_heatDuhamelND_coord_eq_hessianCLM
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) {j k : Fin n} (hjk : j ≠ k) :
    HasDerivAt
      (fun a => deriv (fun b => ∫ s in t₀..t,
        heatSemigroupND (t - s) (q s)
          (Function.update (Function.update x j a) k b))
        ((Function.update x j a) k))
      (heatDuhamelHessianCLM hT hr0 hq hH hqb hqholder x
        (Pi.single j 1) (Pi.single k 1)) (x j) := by
  have h := hasDerivAt_partial_heatDuhamelND_coord_offdiag
    hT hr0 hq hH hqb hqholder x hjk
  convert h using 1
  simp only [heatDuhamelHessianCLM_apply, Pi.single_apply]
  classical
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hk
      exact (hk (Finset.mem_univ k)).elim
  · intro a _ ha
    simp [ha]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

end RemainingOperatorPackaging

end AnalyticPDE
end RicciFlow

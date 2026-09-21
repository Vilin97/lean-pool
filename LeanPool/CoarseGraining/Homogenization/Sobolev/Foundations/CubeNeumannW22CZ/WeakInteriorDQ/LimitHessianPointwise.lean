/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.SmoothPointwise

/-! # Limit Hessian Pointwise -/

namespace Homogenization

open scoped ENNReal Manifold Topology

noncomputable section

namespace WeakPoissonEquationOn

variable {d : ℕ} {V : Set (Vec d)}

/-!
# Hlim-free limiting Hessian representatives

The theorems in `LimitHessian.lean` deliberately take the smooth-test pairing
limit as a hypothesis.  `SmoothPointwise.lean` proves that hypothesis from the
standard small-step geometry.  This file packages the combination in an
existence form that downstream interior `H²` estimates can consume without
threading a separate `hlim`.
-/

/-- Under the standard local DQ geometry, each Hessian coordinate of `uQ`
exists on the open inner cube as a weak derivative of `uQ.grad i`; the
representative inherits the same explicit quotient-Hessian bound. -/
theorem exists_openCubeInnerOpenCubeLimitHessianRieszRep_hasWeakPartialDerivOn_grad_of_step_abs
    {Q : TriadicCube d} {uQ : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (h : WeakPoissonEquationOn (openCubeSet Q) uQ f)
    (hf : MemScalarL2 (openCubeSet Q) f)
    (hV : IsOpenBoundedConvexDomain V)
    (stepSeq : ℕ → ℝ) (hstep_ne : ∀ n, stepSeq n ≠ 0)
    (hstep_tendsto : Filter.Tendsto stepSeq Filter.atTop (nhds 0))
    (i j : Fin d)
    {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν ≤ σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1)
    (hstep_abs : ∀ n, |stepSeq n| ≤ (σ₁ - ν) * cubeRadius Q)
    (hρ₁_nonneg : 0 ≤ ρ₁) :
    ∃ R : ScalarL2 (scaledOpenCubeSet Q ρ₁),
      ‖R‖ ≤
          openCubeInnerQuotientHessianSmoothTestBound
            (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ ∧
        HasWeakPartialDerivOn (scaledOpenCubeSet Q ρ₁) j
          (fun x => uQ.grad x i) (fun x => R x) := by
  let hlim : OpenCubeInnerHessianPairingTendsto (ρ₁ := ρ₁) uQ V stepSeq i j :=
    openCubeInnerHessianPairingTendsto_of_smooth_pointwise_bound_of_step_abs
      uQ V stepSeq i j hinnerV hVν hν_nonneg hνσ hσ₁_lt_one
      hstep_abs hstep_tendsto hstep_ne
  let R : ScalarL2 (scaledOpenCubeSet Q ρ₁) :=
    openCubeInnerOpenCubeLimitHessianRieszRep
      h hf hV stepSeq hstep_ne i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
      hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim
  refine ⟨R, ?_, ?_⟩
  · simpa [R] using
      norm_openCubeInnerOpenCubeLimitHessianRieszRep_le
        h hf hV stepSeq hstep_ne i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
        hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim hρ₁_nonneg
  · simpa [R] using
      openCubeInnerOpenCubeLimitHessianRieszRep_hasWeakPartialDerivOn_grad
        h hf hV stepSeq hstep_ne i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
        hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim hρ₁_nonneg

/-- Bundle the coordinate-wise limiting representatives into a weak Hessian
witness for the restriction of `uQ` to the open inner cube. -/
theorem exists_hasWeakHessianOn_restrict_of_step_abs
    {Q : TriadicCube d} {uQ : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (h : WeakPoissonEquationOn (openCubeSet Q) uQ f)
    (hf : MemScalarL2 (openCubeSet Q) f)
    (hV : IsOpenBoundedConvexDomain V)
    (stepSeq : ℕ → ℝ) (hstep_ne : ∀ n, stepSeq n ≠ 0)
    (hstep_tendsto : Filter.Tendsto stepSeq Filter.atTop (nhds 0))
    {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν ≤ σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1)
    (hstep_abs : ∀ n, |stepSeq n| ≤ (σ₁ - ν) * cubeRadius Q)
    (hρ₁_nonneg : 0 ≤ ρ₁) :
    ∃ uS : H1Function (scaledOpenCubeSet Q ρ₁),
      uS.toFun = uQ.toFun ∧
        uS.grad = uQ.grad ∧
          ∃ H : HasWeakHessianOn (scaledOpenCubeSet Q ρ₁) uS,
            ∀ i j : Fin d,
              ‖H.hessCoordToScalarL2 i j‖ ≤
                openCubeInnerQuotientHessianSmoothTestBound
                  (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ := by
  have hσ₁_nonneg : 0 ≤ σ₁ := hν_nonneg.trans hνσ
  have hVU : V ⊆ openCubeSet Q := by
    intro x hx
    exact
      scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one
        Q hν_nonneg (lt_of_le_of_lt hνσ hσ₁_lt_one) (hVν hx)
  have hSU : scaledOpenCubeSet Q ρ₁ ⊆ openCubeSet Q :=
    (scaledOpenCubeSet_subset_scaledClosedCubeSet Q ρ₁).trans (hinnerV.trans hVU)
  let uS : H1Function (scaledOpenCubeSet Q ρ₁) :=
    uQ.restrict (isOpen_scaledOpenCubeSet Q ρ₁) hSU
  have hexists :
      ∀ i j : Fin d,
        ∃ R : ScalarL2 (scaledOpenCubeSet Q ρ₁),
          ‖R‖ ≤
              openCubeInnerQuotientHessianSmoothTestBound
                (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ ∧
            HasWeakPartialDerivOn (scaledOpenCubeSet Q ρ₁) j
              (fun x => uQ.grad x i) (fun x => R x) := by
    intro i j
    exact
      exists_openCubeInnerOpenCubeLimitHessianRieszRep_hasWeakPartialDerivOn_grad_of_step_abs
        h hf hV stepSeq hstep_ne hstep_tendsto i j η hη_sub hinnerV θ hVν
        hν_nonneg hνσ hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hρ₁_nonneg
  let R : Fin d → Fin d → ScalarL2 (scaledOpenCubeSet Q ρ₁) :=
    fun i j => Classical.choose (hexists i j)
  have hR_bound :
      ∀ i j : Fin d,
        ‖R i j‖ ≤
          openCubeInnerQuotientHessianSmoothTestBound
            (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ := by
    intro i j
    exact (Classical.choose_spec (hexists i j)).1
  have hR_weak :
      ∀ i j : Fin d,
        HasWeakPartialDerivOn (scaledOpenCubeSet Q ρ₁) j
          (fun x => uQ.grad x i) (fun x => R i j x) := by
    intro i j
    exact (Classical.choose_spec (hexists i j)).2
  let H : HasWeakHessianOn (scaledOpenCubeSet Q ρ₁) uS :=
    { hess := fun i j x => R i j x
      hess_memL2 := by
        intro i j
        simpa [MemScalarL2, volumeMeasureOn, R] using
          (MeasureTheory.Lp.memLp (R i j))
      weak_second := by
        intro i j
        simpa [uS, H1Function.restrict] using hR_weak i j }
  refine ⟨uS, by simp [uS, H1Function.restrict], by simp [uS, H1Function.restrict], H, ?_⟩
  intro i j
  have hcoord : H.hessCoordToScalarL2 i j = R i j := by
    apply MeasureTheory.Lp.ext
    filter_upwards [Homogenization.coeFn_toScalarL2 (H.hess_memL2 i j)] with x hx
    simpa [HasWeakHessianOn.hessCoordToScalarL2, H, R] using hx
  simpa [hcoord] using hR_bound i j

/-- Sum-form version of the bundled weak Hessian estimate. -/
theorem exists_hasWeakHessianOn_restrict_hessianCoordL2NormSum_le_of_step_abs
    {Q : TriadicCube d} {uQ : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (h : WeakPoissonEquationOn (openCubeSet Q) uQ f)
    (hf : MemScalarL2 (openCubeSet Q) f)
    (hV : IsOpenBoundedConvexDomain V)
    (stepSeq : ℕ → ℝ) (hstep_ne : ∀ n, stepSeq n ≠ 0)
    (hstep_tendsto : Filter.Tendsto stepSeq Filter.atTop (nhds 0))
    {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν ≤ σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1)
    (hstep_abs : ∀ n, |stepSeq n| ≤ (σ₁ - ν) * cubeRadius Q)
    (hρ₁_nonneg : 0 ≤ ρ₁) :
    ∃ uS : H1Function (scaledOpenCubeSet Q ρ₁),
      uS.toFun = uQ.toFun ∧
        uS.grad = uQ.grad ∧
          ∃ H : HasWeakHessianOn (scaledOpenCubeSet Q ρ₁) uS,
            H.hessianCoordL2NormSum ≤
              ∑ i : Fin d, ∑ _j : Fin d,
                openCubeInnerQuotientHessianSmoothTestBound
                  (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ := by
  obtain ⟨uS, huS_fun, huS_grad, H, hcoord⟩ :=
    exists_hasWeakHessianOn_restrict_of_step_abs
      h hf hV stepSeq hstep_ne hstep_tendsto η hη_sub hinnerV θ hVν
      hν_nonneg hνσ hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hρ₁_nonneg
  refine ⟨uS, huS_fun, huS_grad, H, ?_⟩
  unfold HasWeakHessianOn.hessianCoordL2NormSum
  exact Finset.sum_le_sum fun i _ =>
    Finset.sum_le_sum fun j _ => hcoord i j

/-- Sum-form weak Hessian estimate with a canonical small-step sequence chosen
from the strict geometric margin between the ambient convex set and the cutoff
support scale. -/
theorem exists_hasWeakHessianOn_restrict_hessianCoordL2NormSum_le_of_strict_inner_margin
    {Q : TriadicCube d} {uQ : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (h : WeakPoissonEquationOn (openCubeSet Q) uQ f)
    (hf : MemScalarL2 (openCubeSet Q) f)
    (hV : IsOpenBoundedConvexDomain V)
    {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν < σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1)
    (hρ₁_nonneg : 0 ≤ ρ₁) :
    ∃ uS : H1Function (scaledOpenCubeSet Q ρ₁),
      uS.toFun = uQ.toFun ∧
        uS.grad = uQ.grad ∧
          ∃ H : HasWeakHessianOn (scaledOpenCubeSet Q ρ₁) uS,
            H.hessianCoordL2NormSum ≤
              ∑ i : Fin d, ∑ _j : Fin d,
                openCubeInnerQuotientHessianSmoothTestBound
                  (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ := by
  let margin : ℝ := (σ₁ - ν) * cubeRadius Q
  let stepSeq : ℕ → ℝ := fun n => margin / ((n : ℝ) + 1)
  have hmargin_pos : 0 < margin := by
    exact mul_pos (sub_pos.mpr hνσ) (cubeRadius_pos Q)
  have hmargin_nonneg : 0 ≤ margin := le_of_lt hmargin_pos
  have hstep_ne : ∀ n, stepSeq n ≠ 0 := by
    intro n
    have hden_pos : 0 < (n : ℝ) + 1 := by positivity
    exact div_ne_zero hmargin_pos.ne' hden_pos.ne'
  have hstep_tendsto : Filter.Tendsto stepSeq Filter.atTop (nhds 0) := by
    have hbase :
        Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
          Filter.atTop (nhds (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hmul := hbase.const_mul margin
    simpa [stepSeq, div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hstep_abs : ∀ n, |stepSeq n| ≤ (σ₁ - ν) * cubeRadius Q := by
    intro n
    have hden_pos : 0 < (n : ℝ) + 1 := by positivity
    have hden_ge_one : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
      linarith
    have hstep_nonneg : 0 ≤ stepSeq n :=
      div_nonneg hmargin_nonneg (le_of_lt hden_pos)
    calc
      |stepSeq n| = stepSeq n := abs_of_nonneg hstep_nonneg
      _ ≤ margin := by
        change margin / ((n : ℝ) + 1) ≤ margin
        rw [div_le_iff₀ hden_pos]
        nlinarith [hmargin_nonneg, hden_ge_one]
      _ = (σ₁ - ν) * cubeRadius Q := rfl
  exact
    exists_hasWeakHessianOn_restrict_hessianCoordL2NormSum_le_of_step_abs
      h hf hV stepSeq hstep_ne hstep_tendsto η hη_sub hinnerV θ hVν
      hν_nonneg (le_of_lt hνσ) hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one
      hstep_abs hρ₁_nonneg

end WeakPoissonEquationOn

end

end Homogenization

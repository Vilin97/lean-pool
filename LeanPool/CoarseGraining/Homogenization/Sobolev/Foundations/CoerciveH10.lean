/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveSmooth

/-! # Coercive H10 -/

namespace Homogenization

namespace H10Function

variable {d : ℕ} {U : Set (Vec d)}

/-- Package an `H¹₀` function's `n`th smooth compactly supported approximation as
an `H¹` function on an open domain. -/
noncomputable def approxH1 (hU : IsOpen U) (u : H10Function U) (n : ℕ) : H1Function U :=
  H1Function.ofContDiff hU ((u.approx_smooth n).of_le (by simp)) (u.approx_hasCompactSupport n)

theorem approx_memL2_sub_toH1_memL2
    (hU : IsOpen U) (u : H10Function U) (n : ℕ) :
    MeasureTheory.MemLp (fun x => u.approx n x - u.toH1Function x) 2 (volumeMeasureOn U) := by
  simpa [approxH1, H1Function.ofContDiff] using!
    ((approxH1 hU u n).memL2.sub u.toH1Function.memL2)

theorem approx_grad_memL2_sub_toH1_grad_memL2
    (hU : IsOpen U) (u : H10Function U) (n : ℕ) (i : Fin d) :
    MeasureTheory.MemLp
      (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
      2 (volumeMeasureOn U) := by
  simpa [approxH1, H1Function.ofContDiff] using!
    (((approxH1 hU u n).grad_memL2 i).sub (u.toH1Function.grad_memL2 i))

theorem tendsto_approxH1_toScalarL2
    (hU : IsOpen U) (u : H10Function U) :
    Filter.Tendsto (fun n => (approxH1 hU u n).toScalarL2) Filter.atTop
      (nhds u.toH1Function.toScalarL2) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hdist :
      (fun n => dist ((approxH1 hU u n).toScalarL2) u.toH1Function.toScalarL2) =
        fun n =>
          ENNReal.toReal
            (MeasureTheory.eLpNorm
              (fun x => u.approx n x - u.toH1Function x) 2 (volumeMeasureOn U)) := by
    funext n
    let v := approxH1 hU u n
    have hedist0 :
        edist v.toScalarL2 u.toH1Function.toScalarL2 =
          MeasureTheory.eLpNorm (u.approx n - u.toH1Function.toFun) 2 (volumeMeasureOn U) := by
      simp [v, approxH1, H1Function.toScalarL2, Homogenization.toScalarL2, H1Function.ofContDiff]
    have hedist :
        edist v.toScalarL2 u.toH1Function.toScalarL2 =
          MeasureTheory.eLpNorm (fun x => u.approx n x - u.toH1Function x) 2 (volumeMeasureOn U) := by
      calc
        edist v.toScalarL2 u.toH1Function.toScalarL2
          = MeasureTheory.eLpNorm (u.approx n - u.toH1Function.toFun) 2 (volumeMeasureOn U) := hedist0
        _ = MeasureTheory.eLpNorm (fun x => u.approx n x - u.toH1Function x) 2 (volumeMeasureOn U) := by
            rfl
    rw [MeasureTheory.Lp.dist_edist, hedist]
  rw [hdist]
  exact (ENNReal.tendsto_toReal_zero_iff
    (fun n => (approx_memL2_sub_toH1_memL2 (hU := hU) (u := u) n).eLpNorm_lt_top.ne)).2 u.tendsto_approx

theorem tendsto_approxH1_gradCoordToScalarL2
    (hU : IsOpen U) (u : H10Function U) (i : Fin d) :
    Filter.Tendsto (fun n => (approxH1 hU u n).gradCoordToScalarL2 i) Filter.atTop
      (nhds (u.toH1Function.gradCoordToScalarL2 i)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hdist :
      (fun n => dist ((approxH1 hU u n).gradCoordToScalarL2 i) (u.toH1Function.gradCoordToScalarL2 i)) =
        fun n =>
          ENNReal.toReal
            (MeasureTheory.eLpNorm
              (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
              2 (volumeMeasureOn U)) := by
    funext n
    let v := approxH1 hU u n
    have hedist0 :
        edist (v.gradCoordToScalarL2 i) (u.toH1Function.gradCoordToScalarL2 i) =
          MeasureTheory.eLpNorm
            ((fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) - fun x => u.toH1Function.grad x i)
            2 (volumeMeasureOn U) := by
      simp [v, approxH1, H1Function.gradCoordToScalarL2, Homogenization.toScalarL2,
        H1Function.ofContDiff]
    have hedist :
        edist (v.gradCoordToScalarL2 i) (u.toH1Function.gradCoordToScalarL2 i) =
          MeasureTheory.eLpNorm
            (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
            2 (volumeMeasureOn U) := by
      calc
        edist (v.gradCoordToScalarL2 i) (u.toH1Function.gradCoordToScalarL2 i)
          = MeasureTheory.eLpNorm
              ((fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) - fun x => u.toH1Function.grad x i)
              2 (volumeMeasureOn U) := hedist0
        _ = MeasureTheory.eLpNorm
              (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
              2 (volumeMeasureOn U) := by
              rfl
    rw [MeasureTheory.Lp.dist_edist, hedist]
  rw [hdist]
  exact (ENNReal.tendsto_toReal_zero_iff
    (fun n => (approx_grad_memL2_sub_toH1_grad_memL2 (hU := hU) (u := u) n i).eLpNorm_lt_top.ne)).2
      (u.tendsto_approx_grad i)

theorem tendsto_approxH1_gradientCoordL2NormSum
    (hU : IsOpen U) (u : H10Function U) :
    Filter.Tendsto (fun n => (approxH1 hU u n).gradientCoordL2NormSum) Filter.atTop
      (nhds u.toH1Function.gradientCoordL2NormSum) := by
  simpa [H1Function.gradientCoordL2NormSum] using
    tendsto_finsetSum Finset.univ
      (fun i _ =>
        (continuous_norm.tendsto _).comp
          (tendsto_approxH1_gradCoordToScalarL2 (hU := hU) (u := u) i))

/-- On bounded open convex domains, the `H¹₀` approximation package yields the
coercive estimate proved for smooth compactly supported functions in dimensions
`d ≥ 3`. -/
theorem valueL2Norm_le_sobolevConst_mul_gradientCoordL2NormSum_of_isOpenBoundedConvexDomain
    (hU : IsOpenBoundedConvexDomain U) (hd : 2 < d) (u : H10Function U) :
    ‖u.toH1Function.toScalarL2‖ ≤
      (MeasureTheory.eLpNormLESNormFDerivOfLeConst
        (F := ℝ) (μ := MeasureTheory.volume) (s := U) (p := 2) (q := 2) : ℝ) *
        u.toH1Function.gradientCoordL2NormSum := by
  let C : ℝ := MeasureTheory.eLpNormLESNormFDerivOfLeConst
    (F := ℝ) (μ := MeasureTheory.volume) (s := U) (p := 2) (q := 2)
  let ψ : ℕ → H1Function U := approxH1 hU.isOpen u
  have hψ_bound :
      ∀ n, ‖(ψ n).toScalarL2‖ ≤ C * (ψ n).gradientCoordL2NormSum := by
    intro n
    simpa [ψ, C, approxH1] using
      (H1Function.valueL2Norm_le_sobolevConst_mul_gradientCoordL2NormSum_ofContDiff
        (U := U) hU.isOpen hU.isBoundedDomain
        (hf := u.approx_smooth n)
        (hf_supp := u.approx_hasCompactSupport n)
        (hf_sub := u.approx_support_subset n)
        hd)
  have hleft :
      Filter.Tendsto (fun n => ‖(ψ n).toScalarL2‖) Filter.atTop
        (nhds ‖u.toH1Function.toScalarL2‖) := by
    simpa [ψ] using!
      ((continuous_norm.tendsto _).comp
        (tendsto_approxH1_toScalarL2 (hU := hU.isOpen) (u := u)))
  have hright_grad :
      Filter.Tendsto (fun n => (ψ n).gradientCoordL2NormSum) Filter.atTop
        (nhds u.toH1Function.gradientCoordL2NormSum) := by
    simpa [ψ] using
      (tendsto_approxH1_gradientCoordL2NormSum (hU := hU.isOpen) (u := u))
  have hright :
      Filter.Tendsto (fun n => C * (ψ n).gradientCoordL2NormSum) Filter.atTop
        (nhds (C * u.toH1Function.gradientCoordL2NormSum)) :=
    tendsto_const_nhds.mul hright_grad
  exact le_of_tendsto_of_tendsto' hleft hright hψ_bound

/-- A coarser but more directly typed `H¹₀` coercive estimate, obtained by
bounding the coordinate-gradient sum by the repo's existing vector `L²` norm. -/
theorem valueL2Norm_le_sobolevConst_mul_gradientL2Norm_of_isOpenBoundedConvexDomain
    (hU : IsOpenBoundedConvexDomain U) (hd : 2 < d) (u : H10Function U) :
    ‖u.toH1Function.toScalarL2‖ ≤
      ((MeasureTheory.eLpNormLESNormFDerivOfLeConst
          (F := ℝ) (μ := MeasureTheory.volume) (s := U) (p := 2) (q := 2) : ℝ) * d) *
        ‖u.toH1Function.gradToVectorL2‖ := by
  let C : ℝ := MeasureTheory.eLpNormLESNormFDerivOfLeConst
    (F := ℝ) (μ := MeasureTheory.volume) (s := U) (p := 2) (q := 2)
  have hbase :=
    valueL2Norm_le_sobolevConst_mul_gradientCoordL2NormSum_of_isOpenBoundedConvexDomain hU hd u
  have hcoord := u.toH1Function.gradientCoordL2NormSum_le
  have hC_nonneg : 0 ≤ C := by
    change 0 ≤ (MeasureTheory.eLpNormLESNormFDerivOfLeConst
      (F := ℝ) (μ := MeasureTheory.volume) (s := U) (p := 2) (q := 2) : ℝ)
    positivity
  calc
    ‖u.toH1Function.toScalarL2‖ ≤ C * u.toH1Function.gradientCoordL2NormSum := by
      simpa [C] using hbase
    _ ≤ C * (d * ‖u.toH1Function.gradToVectorL2‖) := by
      exact mul_le_mul_of_nonneg_left hcoord hC_nonneg
    _ = (C * d) * ‖u.toH1Function.gradToVectorL2‖ := by ring

/-- On a bounded open convex domain, an `H¹₀` function with zero gradient
`L²` class has zero value `L²` class. -/
theorem toScalarL2_eq_zero_of_gradToVectorL2_eq_zero_of_isOpenBoundedConvexDomain
    (hU : IsOpenBoundedConvexDomain U) (hd : 2 < d) (u : H10Function U)
    (hgrad : u.toH1Function.gradToVectorL2 = 0) :
    u.toH1Function.toScalarL2 = 0 := by
  have hbound :=
    valueL2Norm_le_sobolevConst_mul_gradientL2Norm_of_isOpenBoundedConvexDomain hU hd u
  rw [hgrad, norm_zero, mul_zero] at hbound
  exact norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))

/-- On a bounded open convex domain, an `H¹₀` function with zero weak gradient
has zero value `L²` class. -/
theorem toScalarL2_eq_zero_of_grad_eq_zero_of_isOpenBoundedConvexDomain
    (hU : IsOpenBoundedConvexDomain U) (hd : 2 < d) (u : H10Function U)
    (hgrad : u.toH1Function.grad = 0) :
    u.toH1Function.toScalarL2 = 0 := by
  apply toScalarL2_eq_zero_of_gradToVectorL2_eq_zero_of_isOpenBoundedConvexDomain hU hd u
  apply MeasureTheory.Lp.ext
  filter_upwards
      [H1Function.coeFn_gradToVectorL2 u.toH1Function,
        MeasureTheory.Lp.coeFn_zero (E := Vec d) (p := (2 : ENNReal)) (μ := volumeMeasureOn U)]
    with x hx hzero
  rw [hx, hgrad, hzero]

/-- Existential constant form of the bounded-open-convex `H¹₀` coercive
estimate in dimensions `d ≥ 3`. -/
theorem exists_valueL2_bound_of_isOpenBoundedConvexDomain
    (hU : IsOpenBoundedConvexDomain U) (hd : 2 < d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : H10Function U,
        ‖u.toH1Function.toScalarL2‖ ≤ C * u.toH1Function.gradientCoordL2NormSum := by
  refine ⟨MeasureTheory.eLpNormLESNormFDerivOfLeConst
      (F := ℝ) (μ := MeasureTheory.volume) (s := U) (p := 2) (q := 2), by positivity, ?_⟩
  intro u
  exact valueL2Norm_le_sobolevConst_mul_gradientCoordL2NormSum_of_isOpenBoundedConvexDomain
    hU hd u

end H10Function

end Homogenization

/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.R.SingleIntegral.UnitInterval
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.DominatedIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Joint analyticity of Carlson's single integral

The beta endpoint exponents, Dirichlet parameters, and slit-plane nodes may all vary
holomorphically. A beta density with smaller positive endpoint exponents supplies the
local integrable bound. This is the convergent seed for the joint continuation in §6.8.
-/

open Complex MeasureTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Joint analytic dependence of the beta-weighted single integral under analytic
substitutions, on its endpoint convergence domain and the full product slit plane. -/
theorem analyticOnNhd_carlsonRUnitIntervalIntegral_comp
    {U : Set (κ → ℂ)} {a a' : (κ → ℂ) → ℂ} {b z : (κ → ℂ) → ι → ℂ}
    (hU : IsOpen U) (ha : AnalyticOnNhd ℂ a U) (ha' : AnalyticOnNhd ℂ a' U)
    (hb : AnalyticOnNhd ℂ b U) (hz : AnalyticOnNhd ℂ z U)
    (hpos : ∀ p ∈ U, 0 < (a p).re ∧ 0 < (a' p).re)
    (hslit : ∀ p ∈ U, z p ∈ carlsonRSlitDomain) :
    AnalyticOnNhd ℂ (fun p => carlsonRUnitIntervalIntegral (a p) (a' p) (b p) (z p)) U := by
  let H : ((κ → ℂ) × ℂ) → ℂ := fun v =>
    v.2 ^ (a v.1 - 1) * (1 - v.2) ^ (a' v.1 - 1) *
      ∏ i, ((1 - v.2) + v.2 * z v.1 i) ^ (-b v.1 i)
  let F : (κ → ℂ) → ℝ → ℂ := fun p u => H (p, (u : ℂ))
  have hH (p : κ → ℂ) (hp : p ∈ U) (u : ℝ) (hu : u ∈ Ioo 0 1) :
      AnalyticAt ℂ H (p, (u : ℂ)) := by
    have hcoord (g : (κ → ℂ) → ι → ℂ) (hg : AnalyticOnNhd ℂ g U) (i : ι) :
        AnalyticAt ℂ (fun v : (κ → ℂ) × ℂ => g v.1 i) (p, (u : ℂ)) :=
      ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt (g p)).comp_of_eq
        ((hg p hp).comp_of_eq (analyticAt_fst (p := (p, (u : ℂ)))) rfl) rfl
    have hsnd : AnalyticAt ℂ (fun v : (κ → ℂ) × ℂ => v.2) (p, (u : ℂ)) := analyticAt_snd
    have haf : AnalyticAt ℂ (fun v : (κ → ℂ) × ℂ => a v.1) (p, (u : ℂ)) :=
      (ha p hp).comp_of_eq analyticAt_fst rfl
    have haf' : AnalyticAt ℂ (fun v : (κ → ℂ) × ℂ => a' v.1) (p, (u : ℂ)) :=
      (ha' p hp).comp_of_eq analyticAt_fst rfl
    have hu₀ : (u : ℂ) ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl hu.1)
    have hu₁ : (1 - u : ℂ) ∈ slitPlane := by
      apply mem_slitPlane_iff.mpr
      exact Or.inl (by simpa using sub_pos.mpr hu.2)
    apply ((hsnd.cpow (haf.sub analyticAt_const) hu₀).mul
      ((analyticAt_const.sub hsnd).cpow (haf'.sub analyticAt_const) hu₁)).mul
    apply Finset.analyticAt_fun_prod
    intro i _
    exact ((analyticAt_const.sub hsnd).add
      (hsnd.mul (hcoord z hz i))).cpow (hcoord b hb i |>.neg)
        (carlsonRSegment_mem_slitPlane (hslit p hp) ⟨hu.1.le, hu.2.le⟩ i)
  have hFcont (p : κ → ℂ) (hp : p ∈ U) : ContinuousOn (F p) (Ioo 0 1) := by
    intro u hu
    change ContinuousWithinAt (fun v : ℝ => H (p, (v : ℂ))) (Ioo 0 1) u
    exact ((hH p hp u hu).continuousAt.comp_of_eq
      (show ContinuousAt (fun v : ℝ => (p, (v : ℂ))) u by fun_prop) rfl).continuousWithinAt
  have hDcont (p : κ → ℂ) (hp : p ∈ U) :
      ContinuousOn (fun u : ℝ => fderiv ℂ (F · u) p) (Ioo 0 1) := by
    have heq (u : ℝ) (hu : u ∈ Ioo 0 1) :
        fderiv ℂ (F · u) p = (fderiv ℂ H (p, (u : ℂ))).comp
          (ContinuousLinearMap.inl ℂ (κ → ℂ) ℂ) := by
      exact ((hH p hp u hu).differentiableAt.hasFDerivAt.comp p
        (hasFDerivAt_prodMk_left (𝕜 := ℂ) p (u : ℂ))).fderiv
    apply ContinuousOn.congr _ heq
    intro u hu
    exact (((hH p hp u hu).fderiv.continuousAt.comp_of_eq
      (show ContinuousAt (fun v : ℝ => (p, (v : ℂ))) u by fun_prop) rfl).clm_comp
        continuousAt_const).continuousWithinAt
  change AnalyticOnNhd ℂ (fun p => ∫ u, F p u ∂volume.restrict (Ioo 0 1)) U
  apply analyticOnNhd_integral_of_locally_dominated hU
    (fun p hp => (hFcont p hp).aestronglyMeasurable measurableSet_Ioo)
    (fun p hp => (hDcont p hp).aestronglyMeasurable measurableSet_Ioo)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
    intro p hp
    exact (hH p hp u hu).comp_of_eq (by fun_prop) rfl
  · intro p hp
    let A : ℂ := ((a p).re / 2 : ℝ)
    let B : ℂ := ((a' p).re / 2 : ℝ)
    have hA : 0 < A.re := by simpa [A] using half_pos (hpos p hp).1
    have hB : 0 < B.re := by simpa [B] using half_pos (hpos p hp).2
    have hevent : ∀ᶠ q in nhds p, q ∈ U ∧ A.re < (a q).re ∧ B.re < (a' q).re := by
      filter_upwards [hU.mem_nhds hp,
        (Complex.continuous_re.continuousAt.comp (ha p hp).continuousAt).eventually_const_lt
          (show A.re < (a p).re by simpa [A] using half_lt_self (hpos p hp).1),
        (Complex.continuous_re.continuousAt.comp (ha' p hp).continuousAt).eventually_const_lt
          (show B.re < (a' p).re by simpa [B] using half_lt_self (hpos p hp).2)] with q hq hqa hqb
      exact ⟨hq, hqa, hqb⟩
    obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hevent
    let K : Set ((κ → ℂ) × ℝ) := Metric.closedBall p r ×ˢ Icc 0 1
    let kernel : ((κ → ℂ) × ℝ) → ℂ := fun v =>
      ∏ i, ((1 - v.2 : ℂ) + (v.2 : ℂ) * z v.1 i) ^ (-b v.1 i)
    have hkernel : ContinuousOn kernel K := by
      have hcoord (g : (κ → ℂ) → ι → ℂ) (hg : AnalyticOnNhd ℂ g U) (i : ι) :
          ContinuousOn (fun v : (κ → ℂ) × ℝ => g v.1 i) K :=
        (continuous_apply i).comp_continuousOn
          (hg.continuousOn.comp continuous_fst.continuousOn (fun v hv => (hball hv.1).1))
      apply continuousOn_finsetProd
      intro i _
      have hu : Continuous (fun v : (κ → ℂ) × ℝ => (v.2 : ℂ)) := by fun_prop
      exact ((continuousOn_const.sub hu.continuousOn).add
        (hu.continuousOn.mul (hcoord z hz i))).cpow (hcoord b hb i |>.neg)
          (fun v hv => carlsonRSegment_mem_slitPlane (hslit v.1 (hball hv.1).1) hv.2 i)
    obtain ⟨C, hC⟩ := ((isCompact_closedBall p r).prod isCompact_Icc).bddAbove_image hkernel.norm
    let W : ℝ → ℂ := fun u => (u : ℂ) ^ (A - 1) * (1 - u : ℂ) ^ (B - 1)
    have hW : Integrable W (volume.restrict (Ioo 0 1)) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp (betaIntegral_convergent hA hB)
    refine ⟨Metric.closedBall p r, (fun u => ‖W u‖ * max C 0),
      Metric.closedBall_mem_nhds p hr, hW.norm.mul_const _, ?_⟩
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
    intro q hq
    have hpow (x : ℝ) (hx : 0 < x) (hx₁ : x ≤ 1) (v w : ℂ) (hvw : v.re ≤ w.re) :
        ‖(x : ℂ) ^ (w - 1)‖ ≤ ‖(x : ℂ) ^ (v - 1)‖ := by
      rw [norm_cpow_eq_rpow_re_of_pos hx, norm_cpow_eq_rpow_re_of_pos hx]
      exact Real.rpow_le_rpow_of_exponent_ge hx hx₁ (by simpa using sub_le_sub_right hvw 1)
    have h₀ := hpow u hu.1 hu.2.le A (a q) (hball hq).2.1.le
    have h₁ := hpow (1 - u) (sub_pos.mpr hu.2) (by linarith [hu.1]) B (a' q)
      (hball hq).2.2.le
    have hK : ‖kernel (q, u)‖ ≤ max C 0 :=
      (hC (mem_image_of_mem _ (show (q, u) ∈ K from ⟨hq, hu.1.le, hu.2.le⟩))).trans
        (le_max_left _ _)
    change ‖((u : ℂ) ^ (a q - 1) * (1 - u : ℂ) ^ (a' q - 1)) * kernel (q, u)‖ ≤ _
    rw [norm_mul]
    apply mul_le_mul _ hK (norm_nonneg _) (norm_nonneg _)
    dsimp only [W]
    rw [norm_mul, norm_mul]
    apply mul_le_mul h₀ _ (norm_nonneg _) (norm_nonneg _)
    simpa only [Complex.ofReal_sub, Complex.ofReal_one] using h₁

end DirichletTransform

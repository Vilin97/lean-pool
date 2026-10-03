/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.Definitions
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.WeakGradientClosure

/-!
# Zero extension of the `H¹₀` graph

This file realizes the supported smooth approximation built into an
`H10Function` as a global weak-gradient graph: both the value and gradient
are extended by zero outside the original domain.  The argument uses the
given `H¹₀` approximants and finite-exponent graph closure, without any cube,
trace, dilation, or PDE input.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace H10Function

private theorem memLp_indicator_of_memLpOn {d : ℕ} {U : Set (Vec d)}
    {p : ℝ≥0∞} {f : Vec d → ℝ} (hU : MeasurableSet U)
    (hf : MemLp f p (volume.restrict U)) :
    MemLp (Set.indicator U f) p volume := by
  exact (MeasureTheory.memLp_indicator_iff_restrict hU).2 hf

/-- The literal zero extension of the value representative of an `H¹₀`
function. -/
def zeroExtension {d : ℕ} {U : Set (Vec d)} (u : H10Function U) : Vec d → ℝ :=
  Set.indicator U u.toH1Function.toFun

/-- The literal zero extension of the gradient representative of an `H¹₀`
function. -/
def zeroExtensionGrad {d : ℕ} {U : Set (Vec d)} (u : H10Function U) :
    Vec d → Vec d :=
  Set.indicator U u.toH1Function.grad

@[simp] theorem zeroExtension_apply_of_mem {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) {x : Vec d} (hx : x ∈ U) :
    u.zeroExtension x = u.toH1Function.toFun x := by
  simp only [zeroExtension, Set.indicator_of_mem hx]

@[simp] theorem zeroExtension_apply_of_not_mem {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) {x : Vec d} (hx : x ∉ U) :
    u.zeroExtension x = 0 := by
  simp only [zeroExtension, Set.indicator_of_notMem hx]

@[simp] theorem zeroExtensionGrad_apply_of_mem {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) {x : Vec d} (hx : x ∈ U) :
    u.zeroExtensionGrad x = u.toH1Function.grad x := by
  simp only [zeroExtensionGrad, Set.indicator_of_mem hx]

@[simp] theorem zeroExtensionGrad_apply_of_not_mem {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) {x : Vec d} (hx : x ∉ U) :
    u.zeroExtensionGrad x = 0 := by
  simp only [zeroExtensionGrad, Set.indicator_of_notMem hx]

/-- Restricted `L^p` membership transports exactly to the global zero
extension. -/
theorem memLp_zeroExtension {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) {p : ℝ≥0∞} (hU : MeasurableSet U)
    (hu : MemLp u.toH1Function.toFun p (volume.restrict U)) :
    MemLp u.zeroExtension p volume := by
  exact memLp_indicator_of_memLpOn hU hu

/-- Restricted coordinatewise `L^p` membership transports exactly to the
global zero-extended gradient. -/
theorem gradMemLp_zeroExtensionGrad {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) {p : ℝ≥0∞} (hU : MeasurableSet U)
    (hDu : GradMemLpOn U p u.toH1Function.grad) :
    GradMemLpOn Set.univ p u.zeroExtensionGrad := by
  intro i
  change MemLp (fun x => u.zeroExtensionGrad x i) p (volume.restrict Set.univ)
  rw [Measure.restrict_univ]
  have hcoord : (fun x => u.zeroExtensionGrad x i) =
      Set.indicator U (fun x => u.toH1Function.grad x i) := by
    funext x
    by_cases hx : x ∈ U
    · simp only [zeroExtensionGrad, Set.indicator_of_mem hx]
    · simp only [zeroExtensionGrad, Set.indicator_of_notMem hx, Pi.zero_apply]
  rw [hcoord]
  exact memLp_indicator_of_memLpOn hU (hDu i)

private theorem approx_eq_zero_of_not_mem {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) (n : ℕ) {x : Vec d} (hx : x ∉ U) :
    u.approx n x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hx_support
  exact hx (u.approx_support_subset n hx_support)

private theorem fderiv_approx_apply_eq_zero_of_not_mem {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) (n : ℕ) (i : Fin d) {x : Vec d} (hx : x ∉ U) :
    (fderiv ℝ (u.approx n) x) (basisVec i) = 0 := by
  have hx_support : x ∉ tsupport (u.approx n) := fun hx_support =>
    hx (u.approx_support_subset n hx_support)
  have hzero : u.approx n =ᶠ[𝓝 x] 0 :=
    (isClosed_tsupport (f := u.approx n)).isOpen_compl.eventually_mem hx_support |>.mono
      (fun y hy => image_eq_zero_of_notMem_tsupport hy)
  rw [hzero.fderiv_eq]
  simp only [fderiv_zero, Pi.zero_apply, zero_apply]

private theorem approx_sub_zeroExtension_eq_indicator_sub {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) (n : ℕ) :
    (fun x => u.approx n x - u.zeroExtension x) =
      Set.indicator U (fun x => u.approx n x - u.toH1Function.toFun x) := by
  funext x
  by_cases hx : x ∈ U
  · simp only [Set.indicator_of_mem hx, u.zeroExtension_apply_of_mem hx]
  · rw [Set.indicator_of_notMem hx, u.zeroExtension_apply_of_not_mem hx,
      sub_zero, u.approx_eq_zero_of_not_mem n hx]

private theorem fderiv_approx_sub_zeroExtensionGrad_eq_indicator_sub
    {d : ℕ} {U : Set (Vec d)} (u : H10Function U) (n : ℕ) (i : Fin d) :
    (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.zeroExtensionGrad x i) =
      Set.indicator U
        (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i) := by
  funext x
  by_cases hx : x ∈ U
  · simp only [Set.indicator_of_mem hx, u.zeroExtensionGrad_apply_of_mem hx]
  · rw [Set.indicator_of_notMem hx, u.zeroExtensionGrad_apply_of_not_mem hx,
      Pi.zero_apply, sub_zero, u.fderiv_approx_apply_eq_zero_of_not_mem n i hx]

/-- The literal zero extensions of an `H¹₀` value and gradient form a global
weak-gradient graph. -/
theorem hasWeakGradientOn_univ_zeroExtension {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) (hU : MeasurableSet U) :
    HasWeakGradientOn Set.univ u.zeroExtension u.zeroExtensionGrad := by
  apply HasWeakGradientOn.of_tendsto_eLpNorm_finiteLp FiniteLpExponent.two
  · simpa only [Measure.restrict_univ] using!
      u.memLp_zeroExtension hU u.toH1Function.memL2
  · simpa only [Measure.restrict_univ] using!
      u.gradMemLp_zeroExtensionGrad hU u.toH1Function.gradMemL2
  · intro n
    exact ((u.approx_smooth n).continuous.memLp_of_hasCompactSupport
      (u.approx_hasCompactSupport n))
  · intro n i
    have hcont : Continuous (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) := by
      exact ((u.approx_smooth n).continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hsupp : HasCompactSupport
        (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) := by
      simpa only using (u.approx_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (basisVec i)
    exact hcont.memLp_of_hasCompactSupport hsupp
  · intro n
    exact HasWeakGradientOn.of_contDiff ((u.approx_smooth n).of_le (by norm_num))
  · have htend : Tendsto
        (fun n => eLpNorm (fun x => u.approx n x - u.zeroExtension x) 2 volume)
        atTop (nhds 0) := by
      refine u.tendsto_approx.congr (fun n => ?_)
      rw [u.approx_sub_zeroExtension_eq_indicator_sub n,
        MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hU]
    simpa only [Measure.restrict_univ] using! htend
  · intro i
    have htend : Tendsto
        (fun n => eLpNorm
          (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.zeroExtensionGrad x i)
          2 volume) atTop (nhds 0) := by
      refine (u.tendsto_approx_grad i).congr (fun n => ?_)
      rw [u.fderiv_approx_sub_zeroExtensionGrad_eq_indicator_sub n i,
        MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hU]
    simpa only [Measure.restrict_univ] using! htend

/-- An `H¹₀` function on a measurable set is canonically transported to every
open superset by its literal zero extension. -/
def extendByZeroToOpenSuperset {d : ℕ} {U V : Set (Vec d)}
    (u : H10Function U) (hU : MeasurableSet U) (hV : IsOpen V) (hUV : U ⊆ V) :
    H10Function V :=
  { toH1Function :=
      { toFun := u.zeroExtension
        grad := u.zeroExtensionGrad
        memL2 := by
          have hu_global : MemLp u.zeroExtension 2 volume :=
            u.memLp_zeroExtension hU u.toH1Function.memL2
          simpa only [Measure.restrict_univ] using hu_global.restrict V
        gradMemL2 := by
          have hDu_global : GradMemLpOn Set.univ 2 u.zeroExtensionGrad :=
            u.gradMemLp_zeroExtensionGrad hU u.toH1Function.gradMemL2
          exact gradMemLpOn_mono (Set.subset_univ V) hDu_global
        hasWeakGradient :=
          (u.hasWeakGradientOn_univ_zeroExtension hU).restrict hV (Set.subset_univ V) }
    approx := u.approx
    approx_smooth := u.approx_smooth
    approx_hasCompactSupport := u.approx_hasCompactSupport
    approx_support_subset := fun n => (u.approx_support_subset n).trans hUV
    tendsto_approx := by
      refine u.tendsto_approx.congr (fun n => ?_)
      rw [u.approx_sub_zeroExtension_eq_indicator_sub n,
        MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hU,
        Measure.restrict_restrict_of_subset hUV]
    tendsto_approx_grad := by
      intro i
      refine (u.tendsto_approx_grad i).congr (fun n => ?_)
      rw [u.fderiv_approx_sub_zeroExtensionGrad_eq_indicator_sub n i,
        MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hU,
        Measure.restrict_restrict_of_subset hUV] }

@[simp] theorem extendByZeroToOpenSuperset_toFun {d : ℕ} {U V : Set (Vec d)}
    (u : H10Function U) (hU : MeasurableSet U) (hV : IsOpen V) (hUV : U ⊆ V) :
    (u.extendByZeroToOpenSuperset hU hV hUV).toH1Function.toFun = u.zeroExtension :=
  rfl

@[simp] theorem extendByZeroToOpenSuperset_grad {d : ℕ} {U V : Set (Vec d)}
    (u : H10Function U) (hU : MeasurableSet U) (hV : IsOpen V) (hUV : U ⊆ V) :
    (u.extendByZeroToOpenSuperset hU hV hUV).toH1Function.grad = u.zeroExtensionGrad :=
  rfl

end H10Function

end
end Homogenization

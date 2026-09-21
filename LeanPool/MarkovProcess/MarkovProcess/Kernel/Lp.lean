/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Kernel.LpFinite
import LeanPool.MarkovProcess.MarkovProcess.Kernel.LpTop
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Kernel integral operators on real `Lᵖ`

This file packages the raw kernel integral as continuous linear contractions on
finite-exponent and infinite-exponent real `Lᵖ` spaces.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

private instance fact_one_le_coe_nnreal (p : NNReal) [Fact (1 ≤ p)] :
    Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast Fact.out⟩

/- Head-class caches for the `Lᵖ` carrier.  Without them every normed-group
class search on `↥(Lp ℝ p μ)` first tries `AddSubgroup.seminormedAddCommGroup`
and burns a failing search for `SeminormedAddCommGroup (α →ₘ[μ] ℝ)`. -/
private noncomputable instance cacheSeminormedLp (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (μ : Measure α) : SeminormedAddCommGroup (Lp ℝ p μ) := inferInstance

private noncomputable instance cacheAddCommMonoidLp (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (μ : Measure α) : AddCommMonoid (Lp ℝ p μ) := inferInstance

private noncomputable instance cacheModuleLp (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (μ : Measure α) : Module ℝ (Lp ℝ p μ) := inferInstance

private noncomputable instance cacheTopologicalSpaceLp (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (μ : Measure α) : TopologicalSpace (Lp ℝ p μ) := inferInstance

private theorem ae_integrable_kernel_finite {μ : Measure α} {κ : Kernel α α}
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ) {p : NNReal}
    (hp : 1 ≤ p) (f : Lp ℝ (p : ℝ≥0∞) μ) : ∀ᵐ x ∂μ, Integrable f (κ x) := by
  let : IsFiniteKernel κ := hκ.isFiniteKernel
  have hfComp : MemLp f p (κ ∘ₘ μ) := (Lp.memLp f).mono_measure hκμ
  have hFiberEq := Measure.ae_ae_of_ae_comp hfComp.1.ae_eq_mk
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast ne_of_gt (zero_lt_one.trans_le hp)
  have hpowInt := hfComp.integrable_norm_rpow hp0 ENNReal.coe_ne_top
  have hFiberInt := Measure.ae_integrable_of_integrable_comp hpowInt
  filter_upwards [hFiberEq, hFiberInt] with x hxEq hxInt
  have hxEq' : f =ᵐ[κ x] hfComp.1.mk f := hxEq
  have hxMeas : AEStronglyMeasurable f (κ x) :=
    hfComp.1.stronglyMeasurable_mk.aestronglyMeasurable.congr hxEq'.symm
  have hxMemLp : MemLp f p (κ x) :=
    (integrable_norm_rpow_iff hxMeas hp0 ENNReal.coe_ne_top).mp hxInt
  exact hxMemLp.integrable (by exact_mod_cast hp)

private theorem ae_integrable_kernel_top {μ : Measure α} {κ : Kernel α α}
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ)
    (f : Lp ℝ ∞ μ) : ∀ᵐ x ∂μ, Integrable f (κ x) := by
  have hCtop : eLpNormEssSup f μ ≠ ∞ := by
    rw [← eLpNorm_exponent_top]
    exact (Lp.memLp f).2.ne
  have hCcoe : ((eLpNormEssSup f μ).toNNReal : ℝ≥0∞) = eLpNormEssSup f μ :=
    ENNReal.coe_toNNReal hCtop
  have hFiberEq : ∀ᵐ x ∂μ, f =ᵐ[κ x] (Lp.aestronglyMeasurable f).mk f :=
    ae_ae_kernel_of_comp_le hκμ (Lp.aestronglyMeasurable f).ae_eq_mk
  have hBound := ae_ae_kernel_of_comp_le hκμ (enorm_ae_le_eLpNormEssSup f μ)
  let : IsFiniteKernel κ := hκ.isFiniteKernel
  filter_upwards [hFiberEq, hBound] with x hxEq hxBound
  have hxAS : AEStronglyMeasurable f (κ x) :=
    (Lp.aestronglyMeasurable f).stronglyMeasurable_mk.aestronglyMeasurable.congr hxEq.symm
  apply MemLp.integrable (q := ∞) le_top
  apply memLp_top_of_bound_enorm hxAS (eLpNormEssSup f μ).toNNReal
  simpa only [hCcoe] using hxBound

private theorem kernelIntegral_add_ae {μ : Measure α} {κ : Kernel α α}
    {f g : α → ℝ} (hf : ∀ᵐ x ∂μ, Integrable f (κ x))
    (hg : ∀ᵐ x ∂μ, Integrable g (κ x)) :
    kernelIntegral κ (f + g) =ᵐ[μ] kernelIntegral κ f + kernelIntegral κ g := by
  filter_upwards [hf, hg] with x hfx hgx
  exact integral_add hfx hgx

/-- The kernel integral as a contraction on finite-exponent real `Lᵖ`. -/
noncomputable def kernelLpFinite (μ : Measure α) (κ : Kernel α α)
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ) (p : NNReal)
    [Fact (1 ≤ p)] : Lp ℝ (p : ℝ≥0∞) μ →L[ℝ] Lp ℝ (p : ℝ≥0∞) μ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (MemLp.kernelIntegral hκ hκμ Fact.out (Lp.memLp f)).toLp
        (kernelIntegral κ f)
      map_add' := fun f g ↦ by
        apply Lp.ext
        refine (MemLp.coeFn_toLp _).trans ?_
        refine (kernelIntegral_congr_ae hκμ (Lp.coeFn_add f g)).trans ?_
        exact (kernelIntegral_add_ae
          (ae_integrable_kernel_finite hκ hκμ Fact.out f)
          (ae_integrable_kernel_finite hκ hκμ Fact.out g)).trans
          (((MemLp.coeFn_toLp _).add (MemLp.coeFn_toLp _)).symm.trans
            (Lp.coeFn_add _ _).symm)
      map_smul' := fun c f ↦ by
        apply Lp.ext
        refine (MemLp.coeFn_toLp _).trans ?_
        refine (kernelIntegral_congr_ae hκμ (Lp.coeFn_smul c f)).trans ?_
        have hsmul : kernelIntegral κ (c • f) =ᵐ[μ]
            c • kernelIntegral κ f := by
          filter_upwards with x
          unfold kernelIntegral
          simpa only [Pi.smul_apply, smul_eq_mul] using
            (integral_smul c (fun y ↦ f y) :
              (∫ y, c • f y ∂κ x) = c • ∫ y, f y ∂κ x)
        refine hsmul.trans ?_
        exact ((MemLp.coeFn_toLp
          (MemLp.kernelIntegral hκ hκμ Fact.out (Lp.memLp f))).symm.const_smul c).trans
          (Lp.coeFn_smul c _).symm }
    1 fun f ↦ by
      change ‖(MemLp.kernelIntegral hκ hκμ Fact.out (Lp.memLp f)).toLp
        (kernelIntegral κ f)‖ ≤ 1 * ‖f‖
      rw [Lp.norm_toLp, Lp.norm_def, one_mul]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
        (eLpNorm_kernelIntegral_le hκ hκμ Fact.out (Lp.memLp f))

/-- The finite-exponent operator is represented by the raw kernel integral. -/
theorem coeFn_kernelLpFinite (μ : Measure α) (κ : Kernel α α)
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ) (p : NNReal)
    [Fact (1 ≤ p)] (f : Lp ℝ (p : ℝ≥0∞) μ) :
    kernelLpFinite μ κ hκ hκμ p f =ᵐ[μ] kernelIntegral κ f := by
  rw [kernelLpFinite, LinearMap.mkContinuous_apply]
  exact MemLp.coeFn_toLp
    (MemLp.kernelIntegral hκ hκμ Fact.out (Lp.memLp f))

/-- The finite-exponent operator contracts the norm of every input. -/
theorem norm_kernelLpFinite_apply_le (μ : Measure α) (κ : Kernel α α)
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ) (p : NNReal)
    [Fact (1 ≤ p)] (f : Lp ℝ (p : ℝ≥0∞) μ) :
    ‖kernelLpFinite μ κ hκ hκμ p f‖ ≤ ‖f‖ := by
  change ‖(MemLp.kernelIntegral hκ hκμ Fact.out (Lp.memLp f)).toLp
    (kernelIntegral κ f)‖ ≤ ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_kernelIntegral_le hκ hκμ Fact.out (Lp.memLp f))

/-- The finite-exponent kernel operator has operator norm at most one. -/
theorem norm_kernelLpFinite_le (μ : Measure α) (κ : Kernel α α)
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ) (p : NNReal)
    [Fact (1 ≤ p)] : ‖kernelLpFinite μ κ hκ hκμ p‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using norm_kernelLpFinite_apply_le μ κ hκ hκμ p f

/-- The kernel integral as a contraction on real `L^∞`. -/
noncomputable def kernelLpTop (μ : Measure α) (κ : Kernel α α)
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ) :
    Lp ℝ ∞ μ →L[ℝ] Lp ℝ ∞ μ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (MemLp.kernelIntegral_top hκ hκμ (Lp.memLp f)).toLp
        (kernelIntegral κ f)
      map_add' := fun f g ↦ by
        apply Lp.ext
        refine (MemLp.coeFn_toLp _).trans ?_
        refine (kernelIntegral_congr_ae hκμ (Lp.coeFn_add f g)).trans ?_
        exact (kernelIntegral_add_ae
          (ae_integrable_kernel_top hκ hκμ f)
          (ae_integrable_kernel_top hκ hκμ g)).trans
          (((MemLp.coeFn_toLp _).add (MemLp.coeFn_toLp _)).symm.trans
            (Lp.coeFn_add _ _).symm)
      map_smul' := fun c f ↦ by
        apply Lp.ext
        refine (MemLp.coeFn_toLp _).trans ?_
        refine (kernelIntegral_congr_ae hκμ (Lp.coeFn_smul c f)).trans ?_
        have hsmul : kernelIntegral κ (c • f) =ᵐ[μ]
            c • kernelIntegral κ f := by
          filter_upwards with x
          unfold kernelIntegral
          simpa only [Pi.smul_apply, smul_eq_mul] using
            (integral_smul c (fun y ↦ f y) :
              (∫ y, c • f y ∂κ x) = c • ∫ y, f y ∂κ x)
        refine hsmul.trans ?_
        exact ((MemLp.coeFn_toLp
          (MemLp.kernelIntegral_top hκ hκμ (Lp.memLp f))).symm.const_smul c).trans
          (Lp.coeFn_smul c _).symm }
    1 fun f ↦ by
      change ‖(MemLp.kernelIntegral_top hκ hκμ (Lp.memLp f)).toLp
        (kernelIntegral κ f)‖ ≤ 1 * ‖f‖
      rw [Lp.norm_toLp, Lp.norm_def, one_mul]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
        (eLpNorm_kernelIntegral_top_le hκ hκμ f)

/-- The infinite-exponent operator is represented by the raw kernel integral. -/
theorem coeFn_kernelLpTop (μ : Measure α) (κ : Kernel α α)
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ) (f : Lp ℝ ∞ μ) :
    kernelLpTop μ κ hκ hκμ f =ᵐ[μ] kernelIntegral κ f := by
  rw [kernelLpTop, LinearMap.mkContinuous_apply]
  exact MemLp.coeFn_toLp (MemLp.kernelIntegral_top hκ hκμ (Lp.memLp f))

/-- The infinite-exponent operator contracts the norm of every input. -/
theorem norm_kernelLpTop_apply_le (μ : Measure α) (κ : Kernel α α)
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ) (f : Lp ℝ ∞ μ) :
    ‖kernelLpTop μ κ hκ hκμ f‖ ≤ ‖f‖ := by
  change ‖(MemLp.kernelIntegral_top hκ hκμ (Lp.memLp f)).toLp
    (kernelIntegral κ f)‖ ≤ ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_kernelIntegral_top_le hκ hκμ f)

/-- The infinite-exponent kernel operator has operator norm at most one. -/
theorem norm_kernelLpTop_le (μ : Measure α) (κ : Kernel α α)
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ) :
    ‖kernelLpTop μ κ hκ hκμ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using norm_kernelLpTop_apply_le μ κ hκ hκμ f

end MarkovProcess

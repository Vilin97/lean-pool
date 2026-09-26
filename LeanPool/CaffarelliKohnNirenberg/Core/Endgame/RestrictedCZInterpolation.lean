/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.RestrictedInterpolationAE
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.RawCZBridge
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.PowerNormTransport
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondStrong

/-! # Interpolation of the actual raw L² operator

The completed L² operator supplies measurability, a.e. sublinearity, and
the strong endpoint. Only its restricted weak estimate remains an analytic
input to the intermediate-exponent estimate.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Endgame

/-- The raw operator interpolates on the intersection of Lᵖ and L² using
the actual L² endpoint and only a restricted weak estimate. -/
theorem raw_rieszSecond_interpolation_of_weak
    {i j : Fin 3} (hL2 : RieszSecondL2Input i j) {A₁ p : ℝ}
    (hweak : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal A₁ * (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (hA₁ : 0 ≤ A₁) (hp1 : 1 < p) (hp2 : p < 2)
    {f : Vec3 → ℝ} (hf : Measurable f)
    (hfp : MemLp f (ENNReal.ofReal p) volume) (hf2 : MemLp f 2 volume) :
    ∫⁻ x, absE (rieszSecondL2RawOperator hL2 f) x ^ p ≤
      ENNReal.ofReal (rieszSecondInterpolationConstant A₁ 1 p) *
        ∫⁻ x, absE f x ^ p := by
  exact interpolation_weak11_strong22_of_l2_classes_ae
    (fun _f _g _hf _hInt hf₂ _hg hg₂ => raw_rieszSecond_sublinear_ae hL2 hf₂ hg₂)
    (fun _f _hf hf₂ => rieszSecondL2RawOperator_measurable hL2 hf₂)
    hweak (fun _f _hf hf₂ => raw_rieszSecond_strong_two hL2 hf₂)
    hA₁ hp1 hp2 hf hfp hf2

/-- The intermediate power estimate respects a.e. representatives, so
the original input needs only its two finite Lp memberships. -/
theorem raw_rieszSecond_interpolation_of_weak_ae
    {i j : Fin 3} (hL2 : RieszSecondL2Input i j) {A₁ p : ℝ}
    (hweak : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal A₁ * (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (hA₁ : 0 ≤ A₁) (hp1 : 1 < p) (hp2 : p < 2)
    {f : Vec3 → ℝ}
    (hfp : MemLp f (ENNReal.ofReal p) volume) (hf2 : MemLp f 2 volume) :
    ∫⁻ x, absE (rieszSecondL2RawOperator hL2 f) x ^ p ≤
      ENNReal.ofReal (rieszSecondInterpolationConstant A₁ 1 p) *
        ∫⁻ x, absE f x ^ p := by
  let hm := hfp.aestronglyMeasurable.aemeasurable
  have hfm := (memLp_congr_ae hm.ae_eq_mk).mp hfp
  have hf2m := (memLp_congr_ae hm.ae_eq_mk).mp hf2
  have h := raw_rieszSecond_interpolation_of_weak hL2 hweak hA₁ hp1 hp2
    hm.measurable_mk hfm hf2m
  have hout := raw_rieszSecond_congr_ae hL2 hf2 hf2m hm.ae_eq_mk
  have houtI := lintegral_congr_ae
    (hout.fun_comp (fun x : ℝ => ENNReal.ofReal |x| ^ p))
  have hinI := lintegral_congr_ae
    (hm.ae_eq_mk.fun_comp (fun x : ℝ => ENNReal.ofReal |x| ^ p))
  simp only [Function.comp_apply] at houtI hinI
  simpa only [absE, ← houtI, ← hinI] using h

/-- The actual raw operator maps the dense intersection to Lᵖ and obeys
the explicit interpolated seminorm estimate. -/
theorem raw_rieszSecond_memLp_and_bound_of_weak
    {i j : Fin 3} (hL2 : RieszSecondL2Input i j) {A₁ p : ℝ}
    (hweak : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal A₁ * (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (hA₁ : 0 ≤ A₁) (hp1 : 1 < p) (hp2 : p < 2)
    {f : Vec3 → ℝ}
    (hfp : MemLp f (ENNReal.ofReal p) volume) (hf2 : MemLp f 2 volume) :
    MemLp (rieszSecondL2RawOperator hL2 f) (ENNReal.ofReal p) volume ∧
      eLpNorm (rieszSecondL2RawOperator hL2 f) (ENNReal.ofReal p) volume ≤
        (ENNReal.ofReal (rieszSecondInterpolationConstant A₁ 1 p)) ^ (1 / p) *
          eLpNorm f (ENNReal.ofReal p) volume := by
  have h := raw_rieszSecond_interpolation_of_weak_ae hL2 hweak hA₁ hp1 hp2 hfp hf2
  have hm : AEStronglyMeasurable (rieszSecondL2RawOperator hL2 f) volume :=
    (rieszSecondL2RawOperator_measurable hL2 hf2).aestronglyMeasurable
  have hp : 0 < p := by linarith only [hp1]
  exact ⟨memLp_of_absE_power_bound hfp hm hp h,
    eLpNorm_bound_of_absE_power_bound hfp.aestronglyMeasurable hm hp h⟩

/-- The dense-class bound in the real Lp norm convention, with the
same explicit interpolation coefficient. -/
theorem raw_rieszSecond_toLp_bound_of_weak
    {i j : Fin 3} (hL2 : RieszSecondL2Input i j) {A₁ p : ℝ}
    (hweak : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal A₁ * (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (hA₁ : 0 ≤ A₁) (hp1 : 1 < p) (hp2 : p < 2)
    {f : Vec3 → ℝ}
    (hfp : MemLp f (ENNReal.ofReal p) volume) (hf2 : MemLp f 2 volume)
    (hTf : MemLp (rieszSecondL2RawOperator hL2 f) (ENNReal.ofReal p) volume) :
    ‖hTf.toLp (rieszSecondL2RawOperator hL2 f)‖ ≤
      (rieszSecondInterpolationConstant A₁ 1 p) ^ (1 / p) * ‖hfp.toLp f‖ := by
  have hp : 0 < p := by linarith only [hp1]
  have hden1 : 0 < p - 1 := by linarith only [hp1]
  have hden2 : 0 < 2 - p := by linarith only [hp2]
  have hC : 0 ≤ rieszSecondInterpolationConstant A₁ 1 p := by
    unfold rieszSecondInterpolationConstant
    positivity
  have hbound := (raw_rieszSecond_memLp_and_bound_of_weak
    hL2 hweak hA₁ hp1 hp2 hfp hf2).2
  have hfinite : (ENNReal.ofReal (rieszSecondInterpolationConstant A₁ 1 p) ^
      (1 / p) * eLpNorm f (ENNReal.ofReal p) volume) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hp.le)
        ENNReal.ofReal_ne_top).ne hfp.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono hfinite hbound
  simpa only [Lp.norm_toLp, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hC] using hreal

end CKN.Core.Endgame

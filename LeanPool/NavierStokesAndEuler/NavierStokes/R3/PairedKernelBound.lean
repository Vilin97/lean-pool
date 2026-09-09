/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonSetup
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# An integrable majorant for the paired commutator kernel

Hölder's inequality with exponents `4/3` and `4` controls each kernel
section. Pairing the resulting uniform bound with an `L¹` function also
proves integrability on the product space, so Fubini is applicable.
These results do not assume or construct a singular integral operator.
-/

@[expose] public section



noncomputable section


open MeasureTheory
open scoped ENNReal

namespace NavierStokesR3.PairedKernelBound

open ProblemStatement Comparison

private theorem measurePreserving_reflect_translate (x : Space) :
    MeasurePreserving (fun y : Space => x - y) volume volume := by
  have hneg : MeasurePreserving (fun y : Space => -y) volume volume :=
    (LinearIsometryEquiv.neg ℝ : Space ≃ₗᵢ[ℝ] Space).measurePreserving
  simpa only [Function.comp_def, sub_eq_add_neg] using
    (measurePreserving_add_left volume x).comp hneg

private instance fourThirds_four_holder :
    ENNReal.HolderTriple (4 / 3 : ℝ≥0∞) 4 1 where
  inv_add_inv_eq_inv := by
    rw [ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    rw [← one_div (4 : ℝ≥0∞)]
    rw [ENNReal.div_add_div_same]
    norm_num [ENNReal.div_self]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- The real `L¹` comparison norm is the integral of the pointwise norm. -/
theorem lpNorm_one_eq_integral_norm {f : Space → E}
    (hf : AEStronglyMeasurable f volume) :
    comparisonLpNorm 1 f = ∫ x, ‖f x‖ := by
  rw [comparisonLpNorm, eLpNorm_one_eq_lintegral_enorm,
    integral_norm_eq_lintegral_enorm hf]

/-- Nonnegative constant factors pass through the real comparison norm. -/
theorem lpNorm_const_smul_of_nonneg {f : Space → E} {p : ℝ≥0∞}
    {D : ℝ} (hD : 0 ≤ D) :
    comparisonLpNorm p (fun x => D • f x) = D * comparisonLpNorm p f := by
  change (eLpNorm (D • f) p volume).toReal = D * (eLpNorm f p volume).toReal
  rw [eLpNorm_const_smul, ENNReal.toReal_mul]
  simp [Real.norm_eq_abs, abs_of_nonneg hD]

omit [NormedSpace ℝ E] in
/-- A reflected translate has the same `Lᵖ` norm. -/
theorem lpNorm_sub_left {k : Space → E} {p : ℝ≥0∞}
    (hk : AEStronglyMeasurable k volume) (x : Space) :
    comparisonLpNorm p (fun y => k (x - y)) = comparisonLpNorm p k := by
  unfold comparisonLpNorm
  congr 1
  exact eLpNorm_comp_measurePreserving hk (measurePreserving_reflect_translate x)

/-- Hölder provides both integrability and the estimate for vector-valued data. -/
theorem integrable_smul_and_integral_norm_le
    {k : Space → ℝ} {r : Space → E} (hk : MemLp k (4 / 3) volume)
    (hr : MemLp r 4 volume) :
    Integrable (fun y => k y • r y) volume ∧
      (∫ y, ‖k y • r y‖) ≤ comparisonLpNorm (4 / 3) k * comparisonLpNorm 4 r := by
  have hbound : eLpNorm (fun y => k y • r y) 1 volume ≤
      eLpNorm k (4 / 3) volume * eLpNorm r 4 volume :=
    eLpNorm_smul_le_mul_eLpNorm (𝕜 := ℝ) (p := 4 / 3) (q := 4) (r := 1)
      hr.aestronglyMeasurable hk.aestronglyMeasurable
  have hmul : MemLp (fun y => k y • r y) 1 volume :=
    ⟨hk.aestronglyMeasurable.smul hr.aestronglyMeasurable,
      hbound.trans_lt (ENNReal.mul_lt_top hk.eLpNorm_lt_top hr.eLpNorm_lt_top)⟩
  refine ⟨memLp_one_iff_integrable.mp hmul, ?_⟩
  rw [← lpNorm_one_eq_integral_norm hmul.aestronglyMeasurable]
  simpa only [comparisonLpNorm, ENNReal.toReal_mul] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top hk.eLpNorm_ne_top hr.eLpNorm_ne_top) hbound

/-- The scalar multiplication estimate in ordinary real multiplication notation. -/
theorem integrable_mul_and_integral_norm_le
    {k r : Space → ℝ} (hk : MemLp k (4 / 3) volume)
    (hr : MemLp r 4 volume) :
    Integrable (fun y => k y * r y) volume ∧
      (∫ y, ‖k y * r y‖) ≤ comparisonLpNorm (4 / 3) k * comparisonLpNorm 4 r := by
  simpa only [smul_eq_mul] using integrable_smul_and_integral_norm_le hk hr

/-- A single measurable section can be dominated almost everywhere; no
jointly measurable extension of that section is required. -/
theorem dominated_section_memLp_and_lpNorm_le
    {m k : Space → ℝ} (x : Space) (hm : AEStronglyMeasurable m volume)
    (hk : MemLp k (4 / 3) volume)
    (hbound : ∀ᵐ y ∂volume, ‖m y‖ ≤ k (x - y)) :
    MemLp m (4 / 3) volume ∧ comparisonLpNorm (4 / 3) m ≤ comparisonLpNorm (4 / 3) k := by
  have hbound' : eLpNorm m (4 / 3) volume ≤ eLpNorm k (4 / 3) volume := by
    calc
      eLpNorm m (4 / 3) volume ≤
          eLpNorm (fun y => k (x - y)) (4 / 3) volume :=
        eLpNorm_mono_ae_real hbound
      _ = eLpNorm k (4 / 3) volume :=
        eLpNorm_comp_measurePreserving hk.aestronglyMeasurable
          (measurePreserving_reflect_translate x)
  exact ⟨⟨hm, hbound'.trans_lt hk.eLpNorm_lt_top⟩,
    ENNReal.toReal_mono hk.eLpNorm_ne_top hbound'⟩

/-- Hölder for one section dominated by a translated `L^(4/3)` majorant. -/
theorem dominated_section_integrable_and_integral_norm_le
    {m k : Space → ℝ} {r : Space → E} (x : Space)
    (hm : AEStronglyMeasurable m volume)
    (hk : MemLp k (4 / 3) volume) (hr : MemLp r 4 volume)
    (hbound : ∀ᵐ y ∂volume, ‖m y‖ ≤ k (x - y)) :
    Integrable (fun y => m y • r y) volume ∧
      (∫ y, ‖m y • r y‖) ≤ comparisonLpNorm (4 / 3) k * comparisonLpNorm 4 r := by
  obtain ⟨hmLp, hnorm⟩ := dominated_section_memLp_and_lpNorm_le x hm hk hbound
  obtain ⟨hint, hmul⟩ := integrable_smul_and_integral_norm_le hmLp hr
  exact ⟨hint, hmul.trans (mul_le_mul_of_nonneg_right hnorm ENNReal.toReal_nonneg)⟩

/-- The single-section estimate with an explicit nonnegative constant. -/
theorem dominated_section_integrable_and_integral_norm_le_scaled
    {m k : Space → ℝ} {r : Space → E} {D : ℝ} (x : Space)
    (hm : AEStronglyMeasurable m volume)
    (hk : MemLp k (4 / 3) volume) (hr : MemLp r 4 volume)
    (hD : 0 ≤ D) (hbound : ∀ᵐ y ∂volume, ‖m y‖ ≤ D * k (x - y)) :
    Integrable (fun y => m y • r y) volume ∧
      (∫ y, ‖m y • r y‖) ≤ D * comparisonLpNorm (4 / 3) k * comparisonLpNorm 4 r := by
  obtain ⟨hint, hnorm⟩ := dominated_section_integrable_and_integral_norm_le
    x hm (hk.const_mul D) hr hbound
  refine ⟨hint, ?_⟩
  have hscale : comparisonLpNorm (4 / 3) (fun y => D * k y) = D * comparisonLpNorm (4 / 3) k :=
    lpNorm_const_smul_of_nonneg hD
  rwa [hscale] at hnorm

/-- A measurable kernel section dominated by a reflected translate of an
`L^(4/3)` function has a uniform `L^(4/3)` bound. -/
theorem section_memLp_and_lpNorm_le
    {K : Space → Space → ℝ} {k : Space → ℝ}
    (hK : Measurable (Function.uncurry K))
    (hk : MemLp k (4 / 3) volume)
    (hbound : ∀ x y, ‖K x y‖ ≤ k (x - y)) (x : Space) :
    MemLp (K x) (4 / 3) volume ∧ comparisonLpNorm (4 / 3) (K x) ≤ comparisonLpNorm (4 / 3) k := by
  exact dominated_section_memLp_and_lpNorm_le x
    (hK.comp measurable_prodMk_left).aestronglyMeasurable hk
    (Filter.Eventually.of_forall (hbound x))

/-- Each paired section is genuinely Bochner integrable, with a bound
independent of the outer variable. -/
theorem section_integrable_and_integral_norm_le
    {K : Space → Space → ℝ} {k : Space → ℝ} {r : Space → E}
    (hK : Measurable (Function.uncurry K))
    (hk : MemLp k (4 / 3) volume) (hr : MemLp r 4 volume)
    (hbound : ∀ x y, ‖K x y‖ ≤ k (x - y)) (x : Space) :
    Integrable (fun y => K x y • r y) volume ∧
      (∫ y, ‖K x y • r y‖) ≤ comparisonLpNorm (4 / 3) k * comparisonLpNorm 4 r := by
  exact dominated_section_integrable_and_integral_norm_le x
    (hK.comp measurable_prodMk_left).aestronglyMeasurable hk hr
    (Filter.Eventually.of_forall (hbound x))

/-- A scaled majorant gives the corresponding scaled uniform section bound. -/
theorem section_integrable_and_integral_norm_le_scaled
    {K : Space → Space → ℝ} {k : Space → ℝ} {r : Space → E} {D : ℝ}
    (hK : Measurable (Function.uncurry K))
    (hk : MemLp k (4 / 3) volume) (hr : MemLp r 4 volume)
    (hD : 0 ≤ D) (hbound : ∀ x y, ‖K x y‖ ≤ D * k (x - y)) (x : Space) :
    Integrable (fun y => K x y • r y) volume ∧
      (∫ y, ‖K x y • r y‖) ≤ D * comparisonLpNorm (4 / 3) k * comparisonLpNorm 4 r := by
  exact dominated_section_integrable_and_integral_norm_le_scaled x
    (hK.comp measurable_prodMk_left).aestronglyMeasurable hk hr hD
    (Filter.Eventually.of_forall (hbound x))

/-- Pairing with an `L¹` function proves integrability on the whole product
space, not just existence of the iterated Bochner integral. -/
theorem integrable_paired_kernel
    {K : Space → Space → ℝ} {k g : Space → ℝ} {r : Space → E}
    (hK : Measurable (Function.uncurry K))
    (hk : MemLp k (4 / 3) volume) (hr : MemLp r 4 volume)
    (hg : Integrable g volume) (hbound : ∀ x y, ‖K x y‖ ≤ k (x - y)) :
    Integrable (fun z : Space × Space => g z.1 • (K z.1 z.2 • r z.2))
      ((volume : Measure Space).prod volume) := by
  have hmeas : AEStronglyMeasurable
      (fun z : Space × Space => g z.1 • (K z.1 z.2 • r z.2))
      ((volume : Measure Space).prod volume) :=
    hg.aestronglyMeasurable.comp_fst.smul
      (hK.aestronglyMeasurable.smul hr.aestronglyMeasurable.comp_snd)
  apply (integrable_prod_iff hmeas).mpr
  constructor
  · refine Filter.Eventually.of_forall fun x => ?_
    exact memLp_one_iff_integrable.mp
      ((memLp_one_iff_integrable.mpr
        (section_integrable_and_integral_norm_le hK hk hr hbound x).1).const_smul (g x))
  · refine (hg.norm.mul_const (comparisonLpNorm (4 / 3) k * comparisonLpNorm 4 r)).mono'
      hmeas.norm.integral_prod_right' ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
    simpa only [norm_smul, integral_const_mul] using
      mul_le_mul_of_nonneg_left
        (section_integrable_and_integral_norm_le hK hk hr hbound x).2 (norm_nonneg (g x))

/-- The outer integral in the paired expression is integrable. -/
theorem integrable_pairing
    {K : Space → Space → ℝ} {k g : Space → ℝ} {r : Space → E}
    (hK : Measurable (Function.uncurry K))
    (hk : MemLp k (4 / 3) volume) (hr : MemLp r 4 volume)
    (hg : Integrable g volume) (hbound : ∀ x y, ‖K x y‖ ≤ k (x - y)) :
    Integrable (fun x => g x • ∫ y, K x y • r y) volume := by
  simpa only [integral_smul] using
    (integrable_paired_kernel hK hk hr hg hbound).integral_prod_left

/-- The paired kernel estimate for vector-valued data. In particular this
applies to complex test functions through their real scalar action. -/
theorem norm_paired_kernel_le
    {K : Space → Space → ℝ} {k g : Space → ℝ} {r : Space → E}
    (hK : Measurable (Function.uncurry K))
    (hk : MemLp k (4 / 3) volume) (hr : MemLp r 4 volume)
    (hg : Integrable g volume) (hbound : ∀ x y, ‖K x y‖ ≤ k (x - y)) :
    ‖∫ x, g x • ∫ y, K x y • r y‖ ≤
      comparisonLpNorm 1 g * comparisonLpNorm (4 / 3) k * comparisonLpNorm 4 r := by
  have houter := integrable_pairing hK hk hr hg hbound
  calc
    ‖∫ x, g x • ∫ y, K x y • r y‖ ≤ ∫ x, ‖g x • ∫ y, K x y • r y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖g x‖ * (comparisonLpNorm (4 / 3) k * comparisonLpNorm 4 r) := by
      apply integral_mono_ae houter.norm (hg.norm.mul_const _)
      refine Filter.Eventually.of_forall fun x => ?_
      dsimp only
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left
        ((norm_integral_le_integral_norm _).trans
          (section_integrable_and_integral_norm_le hK hk hr hbound x).2)
        (norm_nonneg (g x))
    _ = comparisonLpNorm 1 g * comparisonLpNorm (4 / 3) k * comparisonLpNorm 4 r := by
      rw [integral_mul_const, ← lpNorm_one_eq_integral_norm hg.aestronglyMeasurable]
      exact (mul_assoc _ _ _).symm

/-- Explicit constants in the kernel bound pass through the pairing bound. -/
theorem norm_paired_kernel_le_scaled
    {K : Space → Space → ℝ} {k g : Space → ℝ} {r : Space → E} {D : ℝ}
    (hK : Measurable (Function.uncurry K))
    (hk : MemLp k (4 / 3) volume) (hr : MemLp r 4 volume)
    (hg : Integrable g volume) (hD : 0 ≤ D)
    (hbound : ∀ x y, ‖K x y‖ ≤ D * k (x - y)) :
    ‖∫ x, g x • ∫ y, K x y • r y‖ ≤
      D * comparisonLpNorm 1 g * comparisonLpNorm (4 / 3) k * comparisonLpNorm 4 r := by
  have hscale : comparisonLpNorm (4 / 3) (fun y => D * k y) = D * comparisonLpNorm (4 / 3) k :=
    lpNorm_const_smul_of_nonneg hD
  calc
    ‖∫ x, g x • ∫ y, K x y • r y‖ ≤
        comparisonLpNorm 1 g * comparisonLpNorm (4 / 3) (fun y => D * k y) * comparisonLpNorm 4 r :=
      norm_paired_kernel_le hK (hk.const_mul D) hr hg hbound
    _ = D * comparisonLpNorm 1 g * comparisonLpNorm (4 / 3) k * comparisonLpNorm 4 r := by
        rw [hscale]; ring

/-- Fubini for the paired expression follows from actual product integrability. -/
theorem integral_pairing_swap
    {K : Space → Space → ℝ} {k g : Space → ℝ} {r : Space → E}
    (hK : Measurable (Function.uncurry K))
    (hk : MemLp k (4 / 3) volume) (hr : MemLp r 4 volume)
    (hg : Integrable g volume) (hbound : ∀ x y, ‖K x y‖ ≤ k (x - y)) :
    (∫ x, g x • ∫ y, K x y • r y) =
      ∫ y, ∫ x, g x • (K x y • r y) := by
  calc
    (∫ x, g x • ∫ y, K x y • r y) = ∫ x, ∫ y, g x • (K x y • r y) := by
      simp only [integral_smul]
    _ = _ := integral_integral_swap (integrable_paired_kernel hK hk hr hg hbound)

/-- The direct convolution specialization needs only measurability of the
kernel and finite `L^(4/3)`, `L⁴`, and `L¹` norms. -/
theorem norm_convolution_pairing_le
    {k g : Space → ℝ} {r : Space → E}
    (hkm : Measurable k) (hk : MemLp k (4 / 3) volume)
    (hr : MemLp r 4 volume) (hg : Integrable g volume) :
    ‖∫ x, g x • ∫ y, k (x - y) • r y‖ ≤
      comparisonLpNorm 1 g * comparisonLpNorm (4 / 3) k * comparisonLpNorm 4 r := by
  simpa only [comparisonLpNorm, eLpNorm_norm] using
    norm_paired_kernel_le (K := fun x y => k (x - y))
      (hkm.comp (measurable_fst.sub measurable_snd)) hk.norm hr hg
      (fun _ _ => le_rfl)

/-- The requested real-valued paired convolution inequality. -/
theorem abs_convolution_pairing_le
    {k g r : Space → ℝ} (hkm : Measurable k)
    (hk : MemLp k (4 / 3) volume) (hr : MemLp r 4 volume)
    (hg : Integrable g volume) :
    |∫ x, g x * ∫ y, k (x - y) * r y| ≤
      comparisonLpNorm 1 g * comparisonLpNorm (4 / 3) k * comparisonLpNorm 4 r := by
  simpa only [smul_eq_mul, Real.norm_eq_abs] using
    norm_convolution_pairing_le hkm hk hr hg

end NavierStokesR3.PairedKernelBound

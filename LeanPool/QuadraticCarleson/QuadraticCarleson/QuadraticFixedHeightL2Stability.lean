/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticFixedHeightAveragingNorm
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Stability of the genuine fixed-height quadratic maximal operator

The real-modulation supremum is unchanged, pointwise everywhere, by changing
the input on a null set. Its real-valued representative has the same L² decay
and satisfies a quantitative difference estimate. These are consequences of
the proved c = 2 estimate, not additional hypotheses on the operator.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson

/-- Null modifications of the input do not change any output point. -/
theorem paperFixedHeightQuadraticMaximal_congr_ae (height : ℕ)
    {f g : ℝ → ℂ} (hfg : f =ᵐ[volume] g) :
    paperFixedHeightQuadraticMaximal height f =
      paperFixedHeightQuadraticMaximal height g := by
  rw [paperFixedHeightQuadraticMaximal_eq_real, paperFixedHeightQuadraticMaximal_eq_real]
  funext x
  apply iSup_congr
  intro lam
  congr 1
  exact integral_congr_ae (hfg.mono fun t ht ↦ by dsimp only; rw [ht])

theorem hasCompactSupport_fixedHeightQuadraticKernel
    (lam : ℝ) (height : ℕ) (hlam : lam ≠ 0) :
    HasCompactSupport (fixedHeightQuadraticKernel lam height hlam) := by
  exact (hasCompactSupport_complex_dyadicPsi
    (oscillatoryScaleIndex lam height hlam)).mul_right

/-- At every point the individual integrals are genuine Bochner integrals. -/
theorem integrable_fixedHeightQuadraticKernel_row (height : ℕ)
    (lam : ℝ) (hlam : lam ≠ 0) {f : ℝ → ℂ} (hf : MemLp f 2) (x : ℝ) :
    Integrable (fun t ↦ fixedHeightQuadraticKernel lam height hlam (x - t) * f t) :=
  integrable_convolution_row_of_memLp (continuous_fixedHeightQuadraticKernel lam height hlam)
    (hasCompactSupport_fixedHeightQuadraticKernel lam height hlam) hf x

theorem paperFixedHeightQuadraticMaximal_add_le (height : ℕ)
    {f g : ℝ → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) (x : ℝ) :
    paperFixedHeightQuadraticMaximal height (f + g) x ≤
      paperFixedHeightQuadraticMaximal height f x +
        paperFixedHeightQuadraticMaximal height g x := by
  simp only [paperFixedHeightQuadraticMaximal_eq_real, realFixedHeightQuadraticMaximal]
  apply iSup_le
  intro lam
  simp only [Pi.add_apply, mul_add]
  rw [integral_add (integrable_fixedHeightQuadraticKernel_row height _ _ hf x)
    (integrable_fixedHeightQuadraticKernel_row height _ _ hg x)]
  exact (enorm_add_le _ _).trans (add_le_add
    (le_iSup (fun lam : {lam : ℝ // lam ≠ 0} ↦
      ‖∫ t, fixedHeightQuadraticKernel lam.val height lam.property (x - t) * f t‖ₑ) lam)
    (le_iSup (fun lam : {lam : ℝ // lam ≠ 0} ↦
      ‖∫ t, fixedHeightQuadraticKernel lam.val height lam.property (x - t) * g t‖ₑ) lam))

theorem paperFixedHeightQuadraticMaximal_neg (height : ℕ) (f : ℝ → ℂ) :
    paperFixedHeightQuadraticMaximal height (-f) =
      paperFixedHeightQuadraticMaximal height f := by
  funext x
  simp only [paperFixedHeightQuadraticMaximal_eq_real, realFixedHeightQuadraticMaximal,
    Pi.neg_apply, mul_neg, integral_neg, enorm_neg]

/-- Exact complex scalar homogeneity of the unrestricted real supremum. -/
theorem paperFixedHeightQuadraticMaximal_const_mul (height : ℕ)
    (f : ℝ → ℂ) (c : ℂ) (x : ℝ) :
    paperFixedHeightQuadraticMaximal height (fun t ↦ c * f t) x =
      ‖c‖ₑ * paperFixedHeightQuadraticMaximal height f x := by
  simp only [paperFixedHeightQuadraticMaximal_eq_real, realFixedHeightQuadraticMaximal]
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro lam
  have hi : (∫ t, fixedHeightQuadraticKernel lam.val height lam.property (x - t) *
      (c * f t)) = c * ∫ t,
        fixedHeightQuadraticKernel lam.val height lam.property (x - t) * f t := by
    simp_rw [mul_left_comm _ c]
    exact integral_const_mul c _
  rw [hi, enorm_mul]

theorem paperFixedHeightQuadraticMaximal_le_add_sub (height : ℕ)
    {f g : ℝ → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) (x : ℝ) :
    paperFixedHeightQuadraticMaximal height f x ≤
      paperFixedHeightQuadraticMaximal height g x +
        paperFixedHeightQuadraticMaximal height (f - g) x := by
  have h := paperFixedHeightQuadraticMaximal_add_le height hg (hf.sub hg) x
  simpa only [add_sub_cancel] using h

theorem ae_paperFixedHeightQuadraticMaximal_lt_top (height : ℕ)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    ∀ᵐ x, paperFixedHeightQuadraticMaximal height f x < ∞ := by
  have hnorm := (memLp_paperFixedHeightQuadraticMaximal height hf).eLpNorm_lt_top
  have hsq : (∫⁻ x, paperFixedHeightQuadraticMaximal height f x ^ 2) < ∞ := by
    simpa only [eLpNorm_two_sq_lintegral _
      (measurable_paperFixedHeightQuadraticMaximal height hf).aestronglyMeasurable,
        enorm_eq_self] using
      ENNReal.pow_lt_top (n := 2) hnorm
  have ha := ae_lt_top
    ((measurable_paperFixedHeightQuadraticMaximal height hf).pow_const 2) hsq.ne
  filter_upwards [ha] with x hx
  simpa only [ENNReal.pow_lt_top_iff, OfNat.ofNat_ne_zero, or_false] using hx

/-- The ordinary real-valued representative; its value at infinite outputs
is irrelevant since the preceding theorem proves their nullity. -/
noncomputable def paperFixedHeightQuadraticMaximalReal
    (height : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  (paperFixedHeightQuadraticMaximal height f x).toReal

theorem measurable_paperFixedHeightQuadraticMaximalReal (height : ℕ)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    Measurable (paperFixedHeightQuadraticMaximalReal height f) :=
  (measurable_paperFixedHeightQuadraticMaximal height hf).ennreal_toReal

theorem memLp_paperFixedHeightQuadraticMaximalReal (height : ℕ)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    MemLp (paperFixedHeightQuadraticMaximalReal height f) 2 := by
  apply (memLp_paperFixedHeightQuadraticMaximal height hf).of_le_enorm
    (measurable_paperFixedHeightQuadraticMaximalReal height hf).aestronglyMeasurable
  filter_upwards [] with x
  simp only [paperFixedHeightQuadraticMaximalReal, enorm_eq_self, Real.enorm_eq_ofReal_abs,
    abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

theorem paperFixedHeightQuadraticMaximalReal_eLpNorm_eq (height : ℕ)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    eLpNorm (paperFixedHeightQuadraticMaximalReal height f) 2 =
      eLpNorm (paperFixedHeightQuadraticMaximal height f) 2 := by
  apply eLpNorm_congr_enorm_ae
    (measurable_paperFixedHeightQuadraticMaximalReal height hf).aestronglyMeasurable
    (measurable_paperFixedHeightQuadraticMaximal height hf).aestronglyMeasurable
  filter_upwards [ae_paperFixedHeightQuadraticMaximal_lt_top height hf] with x hx
  exact Real.enorm_toReal hx.ne

/-- The familiar pointwise difference bound holds on a common conull set;
no continuity is claimed across modulation-scale jumps. -/
theorem ae_abs_paperFixedHeightQuadraticMaximalReal_sub_le (height : ℕ)
    {f g : ℝ → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) :
    ∀ᵐ x, |paperFixedHeightQuadraticMaximalReal height f x -
      paperFixedHeightQuadraticMaximalReal height g x| ≤
        paperFixedHeightQuadraticMaximalReal height (f - g) x := by
  filter_upwards [ae_paperFixedHeightQuadraticMaximal_lt_top height hf,
    ae_paperFixedHeightQuadraticMaximal_lt_top height hg,
    ae_paperFixedHeightQuadraticMaximal_lt_top height (hf.sub hg)] with x hfx hgx hd
  have h₁ := paperFixedHeightQuadraticMaximal_le_add_sub height hf hg x
  have h₂ := paperFixedHeightQuadraticMaximal_le_add_sub height hg hf x
  have hneg : paperFixedHeightQuadraticMaximal height (g - f) =
      paperFixedHeightQuadraticMaximal height (f - g) := by
    rw [← neg_sub f g, paperFixedHeightQuadraticMaximal_neg]
  rw [hneg] at h₂
  have ht₁ := (ENNReal.toReal_le_toReal hfx.ne (ENNReal.add_ne_top.mpr
    ⟨hgx.ne, hd.ne⟩)).mpr h₁
  have ht₂ := (ENNReal.toReal_le_toReal hgx.ne (ENNReal.add_ne_top.mpr
    ⟨hfx.ne, hd.ne⟩)).mpr h₂
  rw [ENNReal.toReal_add hgx.ne hd.ne] at ht₁
  rw [ENNReal.toReal_add hfx.ne hd.ne] at ht₂
  dsimp only [paperFixedHeightQuadraticMaximalReal]
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- L² stability with exactly the proved fixed-height decay constant. -/
theorem paperFixedHeightQuadraticMaximalReal_sub_eLpNorm_decay (height : ℕ)
    {f g : ℝ → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) :
    eLpNorm (paperFixedHeightQuadraticMaximalReal height f -
      paperFixedHeightQuadraticMaximalReal height g) 2 ≤
        ENNReal.ofReal (fixedHeightL2DecayConstant *
          (2 : ℝ) ^ (-(height : ℝ) / 10)) * eLpNorm (f - g) 2 := by
  have hbound := paperFixedHeightQuadraticMaximal_eLpNorm_decay height
    (f := f - g) (hf.sub hg)
  apply le_trans _ hbound
  apply eLpNorm_mono_enorm_ae
    ((measurable_paperFixedHeightQuadraticMaximalReal height hf).aestronglyMeasurable.sub
      (measurable_paperFixedHeightQuadraticMaximalReal height hg).aestronglyMeasurable)
  filter_upwards [ae_abs_paperFixedHeightQuadraticMaximalReal_sub_le height hf hg]
    with x hx
  simp only [Pi.sub_apply, Real.enorm_eq_ofReal_abs, enorm_eq_self]
  exact (ENNReal.ofReal_le_ofReal hx).trans ENNReal.ofReal_toReal_le

/-- The actual maximal operator on equivalence classes of L² functions. -/
noncomputable def paperFixedHeightQuadraticMaximalLp (height : ℕ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℝ 2 (volume : Measure ℝ) :=
  (memLp_paperFixedHeightQuadraticMaximalReal height (Lp.memLp f)).toLp
    (paperFixedHeightQuadraticMaximalReal height f)

/-- This representative is the genuine real-modulation supremum almost
everywhere, rather than an abstract extension chosen from a dense domain. -/
theorem paperFixedHeightQuadraticMaximalLp_coeFn (height : ℕ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (paperFixedHeightQuadraticMaximalLp height f : ℝ → ℝ) =ᵐ[volume]
      paperFixedHeightQuadraticMaximalReal height f :=
  MemLp.coeFn_toLp _

/-- The L² map agrees with the original formula for every L² input, including
inputs that are only almost everywhere strongly measurable. -/
theorem paperFixedHeightQuadraticMaximalLp_toLp_coeFn (height : ℕ)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    (paperFixedHeightQuadraticMaximalLp height (hf.toLp f) : ℝ → ℝ) =ᵐ[volume]
      paperFixedHeightQuadraticMaximalReal height f := by
  have h := paperFixedHeightQuadraticMaximal_congr_ae height hf.coeFn_toLp
  apply (paperFixedHeightQuadraticMaximalLp_coeFn height (hf.toLp f)).trans
  exact Filter.Eventually.of_forall fun x ↦ congrArg ENNReal.toReal (congrFun h x)

theorem paperFixedHeightQuadraticMaximalLp_enorm_decay (height : ℕ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖paperFixedHeightQuadraticMaximalLp height f‖ₑ ≤
      ENNReal.ofReal (fixedHeightL2DecayConstant *
        (2 : ℝ) ^ (-(height : ℝ) / 10)) * ‖f‖ₑ := by
  rw [paperFixedHeightQuadraticMaximalLp, Lp.enorm_toLp, Lp.enorm_def,
    paperFixedHeightQuadraticMaximalReal_eLpNorm_eq height (Lp.memLp f)]
  exact paperFixedHeightQuadraticMaximal_eLpNorm_decay height (Lp.memLp f)

/-- Quantitative Lipschitz continuity in L², retaining the c = 2 decay. -/
theorem lipschitzWith_paperFixedHeightQuadraticMaximalLp (height : ℕ) :
    LipschitzWith (Real.toNNReal (fixedHeightL2DecayConstant *
      (2 : ℝ) ^ (-(height : ℝ) / 10)))
        (paperFixedHeightQuadraticMaximalLp height) := by
  intro f g
  change edist ((memLp_paperFixedHeightQuadraticMaximalReal height (Lp.memLp f)).toLp _)
    ((memLp_paperFixedHeightQuadraticMaximalReal height (Lp.memLp g)).toLp _) ≤ _
  rw [Lp.edist_toLp_toLp, Lp.edist_def]
  exact paperFixedHeightQuadraticMaximalReal_sub_eLpNorm_decay height
    (f := (f : ℝ → ℂ)) (g := (g : ℝ → ℂ)) (Lp.memLp f) (Lp.memLp g)

theorem continuous_paperFixedHeightQuadraticMaximalLp (height : ℕ) :
    Continuous (paperFixedHeightQuadraticMaximalLp height) :=
  (lipschitzWith_paperFixedHeightQuadraticMaximalLp height).continuous

end QuadraticCarleson

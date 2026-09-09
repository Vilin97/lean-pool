/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SpatialBorelExtension
public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowExpansionResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalCoordinateBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ProfileHistories
public import LeanPool.NavierStokesAndEuler.NavierStokes.SolenoidalDiagonal
import LeanPool.NavierStokesAndEuler.NavierStokes.DiagonalJetBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Constructing the slow asymptotic base from smooth coefficient data

The cutoff-stage bounds are derived from compactness of actual derivatives on
a normalized coordinate set. They are not assumptions on the output series.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.SlowBorelBase

open Set Filter Function
open scoped Topology ContDiff BigOperators

/-- Inner: an abbreviation for `ℝ × ℝ`. -/
abbrev Inner := ℝ × ℝ
/-- Chart: an abbreviation for `ℝ × Inner`. -/
abbrev Chart := ℝ × Inner

/-- Scale map, given by `SpatialBorelExtension.timeScale q`. -/
noncomputable def scaleMap (q : ℝ) : Chart →L[ℝ] Chart :=
  SpatialBorelExtension.timeScale q

@[simp] theorem scaleMap_apply (q : ℝ) (y : Chart) : scaleMap q y = (q * y.1, y.2) := rfl

/-- Local power, given by `SmoothCutoffs.cutoff (4 * (q - 1)) * q ^ b`. -/
noncomputable def localPower (b q : ℝ) : ℝ := SmoothCutoffs.cutoff (4 * (q - 1)) * q ^ b

theorem localPower_smooth (b : ℝ) : ContDiff ℝ ∞ (localPower b) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hq : 0 < q
  · exact (((SmoothCutoffs.cutoff_contDiff).comp
      (contDiff_const.mul (contDiff_id.sub contDiff_const))).contDiffAt).mul
      (contDiffAt_id.rpow_const_of_ne hq.ne')
  · have hq' : q < 1 / 2 := by linarith
    have he : localPower b =ᶠ[𝓝 q] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds hq'] with r hr
      change r < 1 / 2 at hr
      have habs : 1 ≤ |4 * (r - 1)| := by
        have := neg_le_abs (4 * (r - 1))
        linarith
      simp only [localPower, SmoothCutoffs.cutoff_zero_of_one_le_abs habs, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem localPower_eventually_eq (b : ℝ) : localPower b =ᶠ[𝓝 1] (fun q : ℝ => q ^ b) := by
  filter_upwards [Metric.ball_mem_nhds (1 : ℝ) (by norm_num : 0 < (1 / 8 : ℝ))] with q hq
  have habs : |4 * (q - 1)| ≤ 1 / 2 := by
    simp only [Metric.mem_ball, Real.dist_eq] at hq
    rw [abs_mul]
    norm_num
    linarith
  simp only [localPower, SmoothCutoffs.cutoff_one_of_abs_le habs, one_mul]

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Power coefficient, given by `y.1 ^ b • f y.2`. -/
noncomputable def powerCoefficient (b : ℝ) (f : Inner → V) (y : Chart) : V := y.1 ^ b • f y.2

/-- Power stage, given by `SmoothCutoffs.scaledCutoff c y.1 • powerCoefficient b f y`. -/
noncomputable def powerStage (c b : ℝ) (f : Inner → V) (y : Chart) : V :=
  SmoothCutoffs.scaledCutoff c y.1 • powerCoefficient b f y

/-- Template, given by `SmoothCutoffs.cutoff (c * y.1) • (localPower b y.1 • f y.2)`. -/
noncomputable def template (c b : ℝ) (f : Inner → V) (y : Chart) : V :=
  SmoothCutoffs.cutoff (c * y.1) • (localPower b y.1 • f y.2)

/-- Joint template, given by `template z.1 b f z.2`. -/
noncomputable def jointTemplate (b : ℝ) (f : Inner → V) (z : ℝ × Chart) : V :=
  template z.1 b f z.2

theorem powerCoefficient_smoothAt {f : Inner → V} (hf : ContDiff ℝ ∞ f)
    (b : ℝ) {y : Chart} (hy : 0 < y.1) : ContDiffAt ℝ ∞ (powerCoefficient b f) y :=
  (contDiffAt_fst.rpow_const_of_ne hy.ne').smul (hf.contDiffAt.comp y contDiffAt_snd)

theorem powerStage_smoothAt {f : Inner → V} (hf : ContDiff ℝ ∞ f)
    (c b : ℝ) {y : Chart} (hy : 0 < y.1) : ContDiffAt ℝ ∞ (powerStage c b f) y :=
  ((SmoothCutoffs.scaledCutoff_contDiff c).comp contDiff_fst).contDiffAt.smul
    (powerCoefficient_smoothAt hf b hy)

theorem template_smooth {f : Inner → V} (hf : ContDiff ℝ ∞ f) (c b : ℝ) :
    ContDiff ℝ ∞ (template c b f) :=
  (SmoothCutoffs.cutoff_contDiff.comp (contDiff_const.mul contDiff_fst)).smul
    (((localPower_smooth b).comp contDiff_fst).smul (hf.comp contDiff_snd))

theorem jointTemplate_smooth {f : Inner → V} (hf : ContDiff ℝ ∞ f) (b : ℝ) :
    ContDiff ℝ ∞ (jointTemplate b f) :=
  (SmoothCutoffs.cutoff_contDiff.comp (contDiff_fst.mul contDiff_snd.fst)).smul
    (((localPower_smooth b).comp contDiff_snd.fst).smul (hf.comp contDiff_snd.snd))

/-- The scale is one extra parameter. Restricting an actual full derivative to
the chart directions bounds the actual derivative at that fixed scale. -/
theorem template_jet_bound_by_joint {f : Inner → V} (hf : ContDiff ℝ ∞ f)
    (c b : ℝ) (m : ℕ) (y : Chart) :
    ‖iteratedFDeriv ℝ m (template c b f) y‖ ≤
      ‖iteratedFDeriv ℝ m (jointTemplate b f) (c, y)‖ *
        ‖ContinuousLinearMap.inr ℝ ℝ Chart‖ ^ m := by
  let L := ContinuousLinearMap.inr ℝ ℝ Chart
  let G : ℝ × Chart → V := fun z => jointTemplate b f (z + (c, 0))
  have hG : ContDiff ℝ ∞ G := (jointTemplate_smooth hf b).comp (contDiff_id.add contDiff_const)
  have he : template c b f = G ∘ L := by
    funext z
    simp [G, L, jointTemplate, template]
  rw [he, L.iteratedFDeriv_comp_right hG y
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)]
  have hshift : iteratedFDeriv ℝ m G (L y) =
      iteratedFDeriv ℝ m (jointTemplate b f) (c, y) := by
    dsimp only [G]
    rw [iteratedFDeriv_comp_add_right]
    simp [L]
  calc
    _ ≤ ‖iteratedFDeriv ℝ m G (L y)‖ * ∏ _ : Fin m, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = _ := by rw [hshift]; simp [L]

/-- A compactness bound for actual normalized derivatives, uniform in every
active cutoff scale c∈[0,1]. No stage derivative estimate is supplied. -/
theorem exists_template_jet_bound {f : Inner → V} (hf : ContDiff ℝ ∞ f)
    (b : ℝ) {K : Set Inner} (hK : IsCompact K) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c ∈ Icc (0 : ℝ) 1, ∀ w ∈ K,
      ‖iteratedFDeriv ℝ m (template c b f) (1, w)‖ ≤ C := by
  have hc : IsCompact (Icc (0 : ℝ) 1 ×ˢ (({1} : Set ℝ) ×ˢ K)) :=
    isCompact_Icc.prod (isCompact_singleton.prod hK)
  have hj : Continuous (iteratedFDeriv ℝ m (jointTemplate b f)) :=
    (jointTemplate_smooth hf b).continuous_iteratedFDeriv
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)
  obtain ⟨D, hD⟩ := hc.exists_bound_of_continuousOn hj.continuousOn
  let C := max (D * ‖ContinuousLinearMap.inr ℝ ℝ Chart‖ ^ m) 0 + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro c hc w hw
  refine (template_jet_bound_by_joint hf c b m (1, w)).trans ?_
  have hb := mul_le_mul_of_nonneg_right (hD (c, (1, w)) ⟨hc, rfl, hw⟩)
    (pow_nonneg (norm_nonneg (ContinuousLinearMap.inr ℝ ℝ Chart)) m)
  exact hb.trans (by
      dsimp [C]; linarith [le_max_left (D * ‖ContinuousLinearMap.inr ℝ ℝ Chart‖ ^ m) 0])

/-- Jets in the chart obtained by freezing the scale at the evaluation point
and replacing q by q·s. The inner variables are left unscaled. -/
noncomputable def blownJet (m : ℕ) (F : Chart → V) (y : Chart) :=
  iteratedFDeriv ℝ m (F ∘ scaleMap y.1) (1, y.2)

theorem powerStage_scale_germ (c b : ℝ) (f : Inner → V) {q : ℝ}
    (hq : 0 < q) (w : Inner) :
    powerStage c b f ∘ scaleMap q =ᶠ[𝓝 (1, w)]
      (fun y => q ^ b • template (c * q) b f y) := by
  have hp : ∀ᶠ y : Chart in 𝓝 (1, w), 0 < y.1 :=
    continuous_fst.continuousAt (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hl : ∀ᶠ y : Chart in 𝓝 (1, w), localPower b y.1 = y.1 ^ b :=
    (localPower_eventually_eq b).comp_tendsto continuous_fst.continuousAt
  filter_upwards [hp, hl] with y hy hyl
  simp only [Function.comp_apply, scaleMap_apply, powerStage, powerCoefficient,
    SmoothCutoffs.scaledCutoff, template, hyl, Real.mul_rpow hq.le hy.le, smul_smul]
  rw [← mul_assoc c q y.1]
  congr 1
  ring

theorem powerStage_germ (c b : ℝ) (f : Inner → V) {q : ℝ}
    (hq : 0 < q) (w : Inner) :
    powerStage c b f =ᶠ[𝓝 (q, w)]
      (fun y => q ^ b • template (c * q) b f (scaleMap q⁻¹ y)) := by
  have hinv : scaleMap q⁻¹ (q, w) = (1, w) := by simp [hq.ne']
  have ht : Tendsto (scaleMap q⁻¹) (𝓝 (q, w)) (𝓝 (1, w)) := by
    rw [← hinv]
    exact (scaleMap q⁻¹).continuous.continuousAt
  have he := (powerStage_scale_germ c b f hq w).comp_tendsto ht
  filter_upwards [he] with y hy
  simpa only [Function.comp_apply, scaleMap_apply, ← mul_assoc,
    mul_inv_cancel₀ hq.ne', one_mul, Prod.mk.eta] using hy

theorem powerStage_blown_bound {f : Inner → V} (hf : ContDiff ℝ ∞ f)
    (c b : ℝ) {q C : ℝ} (hq : 0 < q) (w : Inner) (m : ℕ)
    (hb : ‖iteratedFDeriv ℝ m (template (c * q) b f) (1, w)‖ ≤ C) :
    ‖blownJet m (powerStage c b f) (q, w)‖ ≤ C * q ^ b := by
  have he := (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (powerStage_scale_germ c b f hq w) m).self_of_nhds
  unfold blownJet
  rw [he, iteratedFDeriv_const_smul_apply'
    ((template_smooth hf (c * q) b).contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl m))]
  rw [norm_smul (q ^ b : ℝ) (iteratedFDeriv ℝ m (template (c * q) b f) (1, w)),
    Real.norm_of_nonneg (Real.rpow_nonneg hq.le b)]
  exact (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hq.le b)).trans_eq (mul_comm _ _)

theorem powerStage_jet_bound {f : Inner → V} (hf : ContDiff ℝ ∞ f)
    (c b : ℝ) {q C : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hC : 0 ≤ C)
    (w : Inner) (m : ℕ)
    (hb : ‖iteratedFDeriv ℝ m (template (c * q) b f) (1, w)‖ ≤ C) :
    ‖iteratedFDeriv ℝ m (powerStage c b f) (q, w)‖ ≤ C * q ^ (b - m) := by
  let L := scaleMap q⁻¹
  have ht := template_smooth hf (c * q) b
  have hm : (m : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl m
  have he := (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (powerStage_germ c b f hq w) m).self_of_nhds
  change ‖iteratedFDeriv ℝ m (powerStage c b f) (q, w)‖ ≤ _
  rw [he]
  change ‖iteratedFDeriv ℝ m (q ^ b • (template (c * q) b f ∘ L)) (q, w)‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply ((ht.comp L.contDiff).contDiffAt.of_le hm),
    norm_smul (q ^ b : ℝ) (iteratedFDeriv ℝ m (template (c * q) b f ∘ L) (q, w)),
    Real.norm_of_nonneg (Real.rpow_nonneg hq.le b),
    L.iteratedFDeriv_comp_right ht (q, w) hm]
  have hL : ‖L‖ ≤ q⁻¹ := SpatialBorelExtension.norm_timeScale_le ((one_le_inv₀ hq).2 hq1)
  have hLp : L (q, w) = (1, w) := by simp [L, hq.ne']
  rw [hLp]
  calc
    _ ≤ q ^ b * (‖iteratedFDeriv ℝ m (template (c * q) b f) (1, w)‖ *
        ∏ _ : Fin m, ‖L‖) := mul_le_mul_of_nonneg_left
      (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) (Real.rpow_nonneg hq.le b)
    _ = q ^ b * (‖iteratedFDeriv ℝ m (template (c * q) b f) (1, w)‖ * ‖L‖ ^ m) := by simp
    _ ≤ q ^ b * (C * (q⁻¹) ^ m) := mul_le_mul_of_nonneg_left
      (mul_le_mul hb (pow_le_pow_left₀ (norm_nonneg _) hL m)
        (pow_nonneg (norm_nonneg _) m) hC) (Real.rpow_nonneg hq.le b)
    _ = C * q ^ (b - m) := by
      rw [Real.rpow_sub hq, Real.rpow_natCast, inv_pow]
      ring

theorem powerStage_eventually_zero (c b : ℝ) (f : Inner → V) {q : ℝ}
    (hcq : 1 < c * q) (w : Inner) : powerStage c b f =ᶠ[𝓝 (q, w)] (fun _ => 0) := by
  have hz := SmoothCutoffs.scaledCutoff_eventually_zero
    (show 1 < |c * q| from hcq.trans_le (le_abs_self _))
  have he := hz.comp_tendsto (continuous_fst.continuousAt :
    Tendsto (fun y : Chart => y.1) (𝓝 (q, w)) (𝓝 q))
  filter_upwards [he] with y hy
  change SmoothCutoffs.scaledCutoff c y.1 = 0 at hy
  simp only [powerStage, hy, zero_smul]

theorem powerStage_jet_zero (c b : ℝ) (f : Inner → V) {q : ℝ}
    (hcq : 1 < c * q) (w : Inner) (m : ℕ) :
    iteratedFDeriv ℝ m (powerStage c b f) (q, w) = 0 := by
  have he := (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (powerStage_eventually_zero c b f hcq w) m).self_of_nhds
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using he

theorem powerStage_blown_zero (c b : ℝ) (f : Inner → V) {q : ℝ}
    (hcq : 1 < c * q) (w : Inner) (m : ℕ) :
    blownJet m (powerStage c b f) (q, w) = 0 := by
  have hmap : scaleMap q (1, w) = (q, w) := by simp
  have ht : Tendsto (scaleMap q) (𝓝 (1, w)) (𝓝 (q, w)) := by
    rw [← hmap]
    exact (scaleMap q).continuous.continuousAt
  have he := (powerStage_eventually_zero c b f hcq w).comp_tendsto ht
  have hj := (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq he m).self_of_nhds
  simpa only [blownJet, Function.comp_def, iteratedFDeriv_fun_zero, Pi.zero_apply] using hj

/-- The order-zero coefficient is kept uncut. This sequence contains only the
positive corrections, with a zero placeholder at index zero. -/
noncomputable def positiveCoefficient (h : ℝ) (f : ℕ → Inner → V) (j : ℕ) : Chart → V :=
  if j = 0 then (fun _ => 0) else powerCoefficient (2 * h * j) (f j)

/-- Slow stage, given by `SolenoidalDiagonal.cutStage (fun j => (a j : ℝ)) Prod.fst
(positiveCoefficient h f)`. -/
noncomputable def slowStage (a : ℕ → ℕ) (h : ℝ) (f : ℕ → Inner → V) : ℕ → Chart → V :=
  SolenoidalDiagonal.cutStage (fun j => (a j : ℝ)) Prod.fst (positiveCoefficient h f)

/-- Positive sum, given by `SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) Prod.fst
(positiveCoefficient h f)`. -/
noncomputable def positiveSum (a : ℕ → ℕ) (h : ℝ) (f : ℕ → Inner → V) : Chart → V :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) Prod.fst (positiveCoefficient h f)

/-- Slow sum, given by `f 0 y.2 + positiveSum a h f y`. -/
noncomputable def slowSum (a : ℕ → ℕ) (h : ℝ) (f : ℕ → Inner → V) (y : Chart) : V :=
  f 0 y.2 + positiveSum a h f y

/-- Cut prefix, given by `f 0 y.2 + ∑ j ∈ Finset.range (J + 1), slowStage a h f j y`. -/
noncomputable def cutPrefix (a : ℕ → ℕ) (h : ℝ) (f : ℕ → Inner → V)
    (J : ℕ) (y : Chart) : V :=
  f 0 y.2 + ∑ j ∈ Finset.range (J + 1), slowStage a h f j y

/-- Uncut prefix, given by `f 0 y.2 + ∑ j ∈ Finset.range (J + 1), positiveCoefficient h f j y`. -/
noncomputable def uncutPrefix (h : ℝ) (f : ℕ → Inner → V) (J : ℕ) (y : Chart) : V :=
  f 0 y.2 + ∑ j ∈ Finset.range (J + 1), positiveCoefficient h f j y

@[simp] theorem slowStage_zero (a : ℕ → ℕ) (h : ℝ) (f : ℕ → Inner → V) :
    slowStage a h f 0 = 0 := by
  funext y
  simp [slowStage, SolenoidalDiagonal.cutStage, positiveCoefficient]

theorem slowStage_eq {j : ℕ} (hj : j ≠ 0) (a : ℕ → ℕ) (h : ℝ)
    (f : ℕ → Inner → V) : slowStage a h f j = powerStage (a j) (2 * h * j) (f j) := by
  funext y
  simp only [slowStage, SolenoidalDiagonal.cutStage, positiveCoefficient, hj, ite_false,
    powerStage]

theorem positiveCoefficient_smoothAt {f : ℕ → Inner → V}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (h : ℝ) (j : ℕ) {y : Chart} (hy : 0 < y.1) :
    ContDiffAt ℝ ∞ (positiveCoefficient h f j) y := by
  unfold positiveCoefficient
  split_ifs
  · exact contDiffAt_const
  · exact powerCoefficient_smoothAt (hf j) _ hy

theorem slowStage_smoothAt {f : ℕ → Inner → V}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (a : ℕ → ℕ) (h : ℝ) (j : ℕ)
    {y : Chart} (hy : 0 < y.1) : ContDiffAt ℝ ∞ (slowStage a h f j) y :=
  SolenoidalDiagonal.cutStage_contDiffAt contDiffAt_fst
    (fun j => positiveCoefficient_smoothAt hf h j hy) j

/-- The quantitative properties proved by choosing the cutoff scales from the
actual coefficient derivatives. These are later reused without repeating the
compactness and numerical selection arguments. -/
structure AdmissibleScales (h : ℝ) (f : ℕ → Inner → V) (K : Set Inner)
    (a : ℕ → ℕ) : Prop where
  positive : ∀ j, 0 < a j
  doubling : ∀ j, 2 * a j ≤ a (j + 1)
  strictMono : StrictMono a
  ordinary : ∀ j, 1 ≤ j → ∀ m, m ≤ j + 2 → ∀ q : ℝ, 0 < q → q ≤ 1 →
    ∀ w ∈ K, ‖iteratedFDeriv ℝ m (slowStage a h f j) (q, w)‖ ≤
      (1 / 2 : ℝ) ^ j * q ^ (h * j - m)
  blown : ∀ j, 1 ≤ j → ∀ m, m ≤ j + 2 → ∀ q : ℝ, 0 < q → q ≤ 1 →
    ∀ w ∈ K, ‖blownJet m (slowStage a h f j) (q, w)‖ ≤
      (1 / 2 : ℝ) ^ j * q ^ (h * j)

/-- A single doubling schedule enforces every finite jet requirement in both
ordinary and rescaled coordinates. Its only analytic input is smoothness of
the individual coefficients on a fixed compact inner-coordinate set. -/
theorem exists_admissibleScales {f : ℕ → Inner → V}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) {h : ℝ} (hh : 0 < h)
    {K : Set Inner} (hK : IsCompact K) (B : ℕ) :
    ∃ a : ℕ → ℕ, B ≤ a 0 ∧ AdmissibleScales h f K a := by
  classical
  choose C hCpos hC using fun j m => exists_template_jet_bound (hf j) (2 * h * j) hK m
  have hg : ∀ j : ℕ, 1 ≤ j → 0 < 2 * h * j := by
    intro j hj
    have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    positivity
  obtain ⟨a, haB, hapos, hadouble, hamono, _, hasmall⟩ :=
    DiagonalScale.exists_diagonal_scales C (fun _ _ => 0) (fun j => 2 * h * j) hg B
  have habsorb : ∀ j, 1 ≤ j → ∀ m, m ≤ j + 2 → ∀ q : ℝ,
      0 < q → q ≤ 1 / (a j : ℝ) →
      C j m * q ^ (h * j) ≤ (1 / 2 : ℝ) ^ j := by
    intro j hj m hm q hq hqa
    have hb := hasmall j hj m hm q hq hqa
    have he : 2 * h * (j : ℝ) / 2 = h * j := by ring
    simpa only [DiagonalScale.logPowerWeight, Real.rpow_zero, mul_one, he,
      abs_of_nonneg (mul_nonneg (hCpos j m).le (Real.rpow_nonneg hq.le _))] using hb
  refine ⟨a, haB, hapos, hadouble, hamono, ?_, ?_⟩
  · intro j hj m hm q hq hq1 w hw
    rw [slowStage_eq (by omega)]
    by_cases hactive : (a j : ℝ) * q ≤ 1
    · have hac : (0 : ℝ) < a j := by exact_mod_cast hapos j
      have hqa : q ≤ 1 / (a j : ℝ) := (le_div_iff₀ hac).2 (by nlinarith)
      have ht := hC j m ((a j : ℝ) * q) ⟨mul_nonneg hac.le hq.le, hactive⟩ w hw
      refine (powerStage_jet_bound (hf j) (a j) (2 * h * j) hq hq1
        (hCpos j m).le w m ht).trans ?_
      have he : 2 * h * (j : ℝ) - m = h * j + (h * j - m) := by ring
      rw [he, Real.rpow_add hq, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (habsorb j hj m hm q hq hqa)
        (Real.rpow_nonneg hq.le _)
    · rw [powerStage_jet_zero (a j) (2 * h * j) (f j) (lt_of_not_ge hactive) w m,
        norm_zero]
      positivity
  · intro j hj m hm q hq hq1 w hw
    rw [slowStage_eq (by omega)]
    by_cases hactive : (a j : ℝ) * q ≤ 1
    · have hac : (0 : ℝ) < a j := by exact_mod_cast hapos j
      have hqa : q ≤ 1 / (a j : ℝ) := (le_div_iff₀ hac).2 (by nlinarith)
      have ht := hC j m ((a j : ℝ) * q) ⟨mul_nonneg hac.le hq.le, hactive⟩ w hw
      refine (powerStage_blown_bound (hf j) (a j) (2 * h * j) hq w m ht).trans ?_
      have he : 2 * h * (j : ℝ) = h * j + h * j := by ring
      rw [he, Real.rpow_add hq, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (habsorb j hj m hm q hq hqa)
        (Real.rpow_nonneg hq.le _)
    · rw [powerStage_blown_zero (a j) (2 * h * j) (f j) (lt_of_not_ge hactive) w m,
        norm_zero]
      positivity

theorem slowStage_locally_zero {a : ℕ → ℕ} (ha : StrictMono a)
    (h : ℝ) (f : ℕ → Inner → V) {y : Chart} (hy : 0 < y.1) :
    ∃ N : ℕ, ∀ᶠ z in 𝓝 y, ∀ j : ℕ, N ≤ j → slowStage a h f j z = 0 :=
  SolenoidalDiagonal.eventually_zero_tail (SolenoidalDiagonal.realScales_tendsto ha)
    continuous_fst.continuousAt hy (positiveCoefficient h f)

theorem positiveSum_smoothAt {a : ℕ → ℕ} (ha : StrictMono a)
    {f : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j)) (h : ℝ)
    {y : Chart} (hy : 0 < y.1) : ContDiffAt ℝ ∞ (positiveSum a h f) y :=
  SolenoidalDiagonal.potentialSum_contDiffAt (SolenoidalDiagonal.realScales_tendsto ha)
    hy contDiffAt_fst (fun j => positiveCoefficient_smoothAt hf h j hy)

theorem slowSum_smoothAt {a : ℕ → ℕ} (ha : StrictMono a)
    {f : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j)) (h : ℝ)
    {y : Chart} (hy : 0 < y.1) : ContDiffAt ℝ ∞ (slowSum a h f) y :=
  ((hf 0).comp contDiff_snd).contDiffAt.add (positiveSum_smoothAt ha hf h hy)

theorem slowSum_smoothOn {a : ℕ → ℕ} (ha : StrictMono a)
    {f : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j)) (h : ℝ) :
    ContDiffOn ℝ ∞ (slowSum a h f) {y | 0 < y.1} :=
  fun _ hy => (slowSum_smoothAt ha hf h hy).contDiffWithinAt

/-- Actual ordinary derivatives of the infinite sum minus a cut prefix. -/
theorem ordinary_tail_bound {a : ℕ → ℕ} {h : ℝ} (hh : 0 < h)
    {f : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j))
    {K : Set Inner} (ha : AdmissibleScales h f K a)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) {w : Inner} (hw : w ∈ K)
    (J m : ℕ) (hm : m ≤ J + 3) :
    ‖iteratedFDeriv ℝ m (fun y => slowSum a h f y - cutPrefix a h f J y) (q, w)‖ ≤
      (1 / 2 : ℝ) ^ J * q ^ (h * (J + 1) - m) := by
  have hg : Monotone (fun j : ℕ => h * j) := fun i j hij =>
    mul_le_mul_of_nonneg_left (by exact_mod_cast hij) hh.le
  have hb := DiagonalJetBounds.norm_tsum_sub_prefix_jet_le
    (slowStage_locally_zero ha.strictMono h f hq)
    (fun j => slowStage_smoothAt hf a h j hq) (fun j => h * j) hg
    (m : ℝ) q hq hq1 J m (fun j hj =>
      ha.ordinary j (by omega) m (by omega) q hq hq1 w hw)
  simpa only [slowSum, cutPrefix, positiveSum, SolenoidalDiagonal.potentialSum,
    slowStage, add_sub_add_left_eq_sub, Nat.cast_add, Nat.cast_one] using hb

/-- Actual derivatives after freezing the dilation at the evaluation scale.
The same one schedule works for every eventually prescribed jet order. -/
theorem blown_tail_bound {a : ℕ → ℕ} {h : ℝ} (hh : 0 < h)
    {f : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j))
    {K : Set Inner} (ha : AdmissibleScales h f K a)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) {w : Inner} (hw : w ∈ K)
    (J m : ℕ) (hm : m ≤ J + 3) :
    ‖blownJet m (fun y => slowSum a h f y - cutPrefix a h f J y) (q, w)‖ ≤
      (1 / 2 : ℝ) ^ J * q ^ (h * (J + 1)) := by
  have hmap : scaleMap q (1, w) = (q, w) := by simp
  have ht : Tendsto (scaleMap q) (𝓝 (1, w)) (𝓝 (q, w)) := by
    rw [← hmap]
    exact (scaleMap q).continuous.continuousAt
  obtain ⟨N, hN⟩ := slowStage_locally_zero ha.strictMono h f hq (y := (q, w))
  have hloc : ∃ N : ℕ, ∀ᶠ z in 𝓝 (1, w), ∀ j : ℕ, N ≤ j →
      (slowStage a h f j ∘ scaleMap q) z = 0 := ⟨N, ht.eventually hN⟩
  have hs : ∀ j, ContDiffAt ℝ ∞ (slowStage a h f j ∘ scaleMap q) (1, w) := by
    intro j
    apply ContDiffAt.comp
    · rw [hmap]
      exact slowStage_smoothAt hf a h j hq
    · exact (scaleMap q).contDiff.contDiffAt
  have hg : Monotone (fun j : ℕ => h * j) := fun i j hij =>
    mul_le_mul_of_nonneg_left (by exact_mod_cast hij) hh.le
  have hb := DiagonalJetBounds.norm_tsum_sub_prefix_jet_le hloc hs (fun j => h * j)
    hg 0 q hq hq1 J m (fun j hj => by
      simpa only [sub_zero, blownJet] using ha.blown j (by omega) m (by omega) q hq hq1 w hw)
  simpa only [slowSum, cutPrefix, positiveSum, SolenoidalDiagonal.potentialSum,
    slowStage, blownJet, Function.comp_def, add_sub_add_left_eq_sub,
    sub_zero, Nat.cast_add, Nat.cast_one] using hb

theorem cutPrefix_eventually_uncut (a : ℕ → ℕ) (h : ℝ)
    (f : ℕ → Inner → V) (J : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : Chart, |y.1| < δ →
      cutPrefix a h f J =ᶠ[𝓝 y] uncutPrefix h f J := by
  obtain ⟨δ, hδ, hb⟩ := DiagonalJetBounds.partialPotential_eventuallyEq_uncut
    (fun j => (a j : ℝ)) Prod.fst (positiveCoefficient h f) (J + 1)
  refine ⟨δ, hδ, fun y hy => ?_⟩
  filter_upwards [hb y continuous_fst.continuousAt hy] with z hz
  exact congrArg (fun v => f 0 z.2 + v) hz

/-- Every requested finite ordinary jet has a sufficiently late *uncut *
prefix with any prescribed remainder power. The prefix depends on both
requests; this does not assert that one fixed tail is flat to all orders. -/
theorem exists_ordinary_uncut_tail {a : ℕ → ℕ} {h : ℝ} (hh : 0 < h)
    {f : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j))
    {K : Set Inner} (ha : AdmissibleScales h f K a) (M Jmin : ℕ) (P : ℝ) :
    ∃ J : ℕ, Jmin ≤ J ∧ M ≤ J ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ m ≤ M, ∀ q : ℝ, 0 < q → q < δ → ∀ w ∈ K,
        ‖iteratedFDeriv ℝ m (fun y => slowSum a h f y - uncutPrefix h f J y) (q, w)‖ ≤
          (1 / 2 : ℝ) ^ J * q ^ P := by
  have htop : Tendsto (fun j : ℕ => h * j) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hh
  obtain ⟨J, hJmin, hJM, hgain⟩ :=
    DiagonalJetBounds.exists_prefix_gain (fun j => h * j) (fun m => (m : ℝ)) htop M Jmin P
  obtain ⟨δ, hδ, hprefix⟩ := cutPrefix_eventually_uncut a h f J
  refine ⟨J, hJmin, hJM, min δ 1, lt_min hδ (by norm_num), ?_⟩
  intro m hm q hq hsmall w hw
  have hq1 : q ≤ 1 := (hsmall.trans_le (min_le_right _ _)).le
  have hp := hprefix (q, w) (by simpa only [abs_of_pos hq] using
    (hsmall.trans_le (min_le_left _ _)))
  have hdiff : (fun y => slowSum a h f y - cutPrefix a h f J y) =ᶠ[𝓝 (q, w)]
      (fun y => slowSum a h f y - uncutPrefix h f J y) :=
    hp.mono (fun y hy => congrArg (fun z => slowSum a h f y - z) hy)
  have he := (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq hdiff m).self_of_nhds
  rw [← he]
  exact (ordinary_tail_bound hh hf ha hq hq1 hw J m (by omega)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hq hq1 (by simpa using hgain m hm)) (by positivity))

theorem exists_blown_uncut_tail {a : ℕ → ℕ} {h : ℝ} (hh : 0 < h)
    {f : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j))
    {K : Set Inner} (ha : AdmissibleScales h f K a) (M Jmin : ℕ) (P : ℝ) :
    ∃ J : ℕ, Jmin ≤ J ∧ M ≤ J ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ m ≤ M, ∀ q : ℝ, 0 < q → q < δ → ∀ w ∈ K,
        ‖blownJet m (fun y => slowSum a h f y - uncutPrefix h f J y) (q, w)‖ ≤
          (1 / 2 : ℝ) ^ J * q ^ P := by
  have htop : Tendsto (fun j : ℕ => h * j) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hh
  obtain ⟨J, hJmin, hJM, hgain⟩ :=
    DiagonalJetBounds.exists_prefix_gain (fun j => h * j) (fun _ => 0) htop M Jmin P
  obtain ⟨δ, hδ, hprefix⟩ := cutPrefix_eventually_uncut a h f J
  refine ⟨J, hJmin, hJM, min δ 1, lt_min hδ (by norm_num), ?_⟩
  intro m hm q hq hsmall w hw
  have hq1 : q ≤ 1 := (hsmall.trans_le (min_le_right _ _)).le
  have hp := hprefix (q, w) (by simpa only [abs_of_pos hq] using
    (hsmall.trans_le (min_le_left _ _)))
  have hmap : scaleMap q (1, w) = (q, w) := by simp
  have ht : Tendsto (scaleMap q) (𝓝 (1, w)) (𝓝 (q, w)) := by
    rw [← hmap]
    exact (scaleMap q).continuous.continuousAt
  have hdiff : (fun y => slowSum a h f y - cutPrefix a h f J y) =ᶠ[𝓝 (q, w)]
      (fun y => slowSum a h f y - uncutPrefix h f J y) :=
    hp.mono (fun y hy => congrArg (fun z => slowSum a h f y - z) hy)
  have he := (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (hdiff.comp_tendsto ht) m).self_of_nhds
  change ‖iteratedFDeriv ℝ m _ (1, w)‖ ≤ _
  rw [← he]
  exact (blown_tail_bound hh hf ha hq hq1 hw J m (by omega)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hq hq1 (by simpa using hgain m hm)) (by positivity))

/-- A fixed stage keeps its full q^(2hj) order. Only the tail estimates spend
half this gain to absorb coefficient growth. -/
theorem exists_stage_blown_power_bound {f : ℕ → Inner → V}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) {K : Set Inner} (hK : IsCompact K)
    (a : ℕ → ℕ) (h : ℝ) (j m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 < q → ∀ w ∈ K,
      ‖blownJet m (slowStage a h f j) (q, w)‖ ≤ C * q ^ (2 * h * j) := by
  obtain ⟨C, hC, hb⟩ := exists_template_jet_bound (hf j) (2 * h * j) hK m
  refine ⟨C, hC, fun q hq w hw => ?_⟩
  by_cases hj : j = 0
  · subst j
    simp [blownJet, slowStage_zero, Function.comp_def, hC.le]
  rw [slowStage_eq hj]
  by_cases hactive : (a j : ℝ) * q ≤ 1
  · exact powerStage_blown_bound (hf j) (a j) (2 * h * j) hq w m
      (hb _ ⟨mul_nonneg (Nat.cast_nonneg _) hq.le, hactive⟩ w hw)
  · rw [powerStage_blown_zero (a j) (2 * h * j) (f j) (lt_of_not_ge hactive) w m,
      norm_zero]
    positivity

theorem blownJet_sum {ι : Type*} (s : Finset ι) (F : ι → Chart → V)
    {q : ℝ} {w : Inner} (hF : ∀ i ∈ s, ContDiffAt ℝ ∞ (F i) (q, w)) (m : ℕ) :
    blownJet m (fun y => ∑ i ∈ s, F i y) (q, w) =
      ∑ i ∈ s, blownJet m (F i) (q, w) := by
  have hs : ∀ i ∈ s, ContDiffWithinAt ℝ m (F i ∘ scaleMap q) univ (1, w) := by
    intro i hi
    have hm : (m : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl m
    apply ContDiffAt.contDiffWithinAt
    apply ContDiffAt.of_le _ hm
    apply ContDiffAt.comp
    · simpa only [scaleMap_apply, mul_one] using hF i hi
    · exact (scaleMap q).contDiff.contDiffAt
  simpa only [blownJet, Function.comp_def, iteratedFDerivWithin_univ] using
    iteratedFDerivWithin_fun_sum_apply uniqueDiffOn_univ (mem_univ (1, w)) hs

theorem norm_blownJet_le_sub_add {F G : Chart → V} {q : ℝ} {w : Inner}
    (hF : ContDiffAt ℝ ∞ F (q, w)) (hG : ContDiffAt ℝ ∞ G (q, w)) (m : ℕ) :
    ‖blownJet m F (q, w)‖ ≤
      ‖blownJet m (fun y => F y - G y) (q, w)‖ + ‖blownJet m G (q, w)‖ := by
  have hFc : ContDiffAt ℝ ∞ (F ∘ scaleMap q) (1, w) := by
    apply ContDiffAt.comp
    · simpa only [scaleMap_apply, mul_one] using hF
    · exact (scaleMap q).contDiff.contDiffAt
  have hGc : ContDiffAt ℝ ∞ (G ∘ scaleMap q) (1, w) := by
    apply ContDiffAt.comp
    · simpa only [scaleMap_apply, mul_one] using hG
    · exact (scaleMap q).contDiff.contDiffAt
  have hm : (m : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl m
  have hid : blownJet m (fun y => F y - G y) (q, w) =
      blownJet m F (q, w) - blownJet m G (q, w) := by
    have hadd := fun_iteratedFDeriv_add_apply (hFc.of_le hm) (hGc.neg.of_le hm)
    have hneg : iteratedFDeriv ℝ m (fun y => -(G ∘ scaleMap q) y) (1, w) =
        -iteratedFDeriv ℝ m (G ∘ scaleMap q) (1, w) := by
      change iteratedFDeriv ℝ m (-(G ∘ scaleMap q)) (1, w) = _
      exact iteratedFDeriv_neg_apply
    rw [hneg] at hadd
    simpa only [blownJet, Function.comp_def, sub_eq_add_neg] using hadd
  rw [hid]
  simpa only [add_comm] using norm_le_insert' (blownJet m F (q, w)) (blownJet m G (q, w))

/-- The normalized correction is O(q^(2h)) in every fixed blown-up jet.
This estimates derivatives of the actual sum; no bound on its tail is assumed. -/
theorem normalized_correction_bound {a : ℕ → ℕ} {h : ℝ} (hh : 0 < h)
    {f : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j))
    {K : Set Inner} (hK : IsCompact K) (ha : AdmissibleScales h f K a) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 < q → q ≤ 1 → ∀ w ∈ K,
      ‖blownJet m (fun y => slowSum a h f y - f 0 y.2) (q, w)‖ ≤ C * q ^ (2 * h) := by
  classical
  let J := max m 1
  choose C hC hCb using fun j => exists_stage_blown_power_bound hf hK a h j m
  let D := ∑ j ∈ Finset.range (J + 1), C j
  have hD : 0 ≤ D := Finset.sum_nonneg (fun j _ => (hC j).le)
  refine ⟨D + (1 / 2 : ℝ) ^ J, by positivity, ?_⟩
  intro q hq hq1 w hw
  let P : Chart → V := fun y => ∑ j ∈ Finset.range (J + 1), slowStage a h f j y
  have hs : ContDiffAt ℝ ∞ P (q, w) :=
    ContDiffAt.sum (fun j _ => slowStage_smoothAt hf a h j hq)
  have hP : ‖blownJet m P (q, w)‖ ≤ D * q ^ (2 * h) := by
    rw [blownJet_sum _ _ (fun j _ => slowStage_smoothAt hf a h j hq) m]
    calc
      _ ≤ ∑ j ∈ Finset.range (J + 1), ‖blownJet m (slowStage a h f j) (q, w)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (J + 1), C j * q ^ (2 * h) := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hj0 : j = 0
        · subst j
          simp only [slowStage_zero, blownJet, Function.comp_def, Pi.zero_apply,
            iteratedFDeriv_fun_zero, norm_zero]
          exact mul_nonneg (hC 0).le (Real.rpow_nonneg hq.le _)
        · refine (hCb j q hq w hw).trans (mul_le_mul_of_nonneg_left ?_ (hC j).le)
          apply Real.rpow_le_rpow_of_exponent_ge hq hq1
          have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
          nlinarith
      _ = D * q ^ (2 * h) := by rw [Finset.sum_mul]
  have hT : ‖blownJet m (fun y => positiveSum a h f y - P y) (q, w)‖ ≤
      (1 / 2 : ℝ) ^ J * q ^ (2 * h) := by
    have hb := blown_tail_bound hh hf ha hq hq1 hw J m (by dsimp [J]; omega)
    have he : (fun y => slowSum a h f y - cutPrefix a h f J y) =
        (fun y => positiveSum a h f y - P y) := by
      funext y
      simp only [slowSum, cutPrefix, P, add_sub_add_left_eq_sub]
    rw [he] at hb
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    apply Real.rpow_le_rpow_of_exponent_ge hq hq1
    have hJ : (1 : ℝ) ≤ J := by exact_mod_cast (le_max_right m 1)
    nlinarith
  have he : (fun y => slowSum a h f y - f 0 y.2) = positiveSum a h f := by
    funext y
    simp [slowSum]
  rw [he]
  exact (norm_blownJet_le_sub_add (positiveSum_smoothAt ha.strictMono hf h hq) hs m).trans
    ((add_le_add hT hP).trans_eq (by ring))

section PhysicalCoordinates

/-- Inner box, given by `Icc lo hi ×ˢ Icc (-1) 1`. -/
noncomputable def innerBox (lo hi : ℝ) : Set Inner := Icc lo hi ×ˢ Icc (-1) 1

theorem innerBox_isCompact (lo hi : ℝ) : IsCompact (innerBox lo hi) :=
  isCompact_Icc.prod isCompact_Icc

/-- Physical chart as an element of `Chart`. -/
noncomputable def physicalChart (h : ℝ) (p : Chart) : Chart :=
  (PhysicalCoordinateBounds.physicalQ (2 * h) p,
    (PhysicalCoordinateBounds.physicalX (2 * h) p,
      PhysicalCoordinateBounds.physicalEta (2 * h) p))

theorem physicalChart_smoothAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Chart} (hp : p.1 < 1) : ContDiffAt ℝ ∞ (physicalChart h) p := by
  have ha : 0 < 2 * h := by positivity
  have ha1 : 2 * h < 1 := by linarith
  exact (PhysicalCoordinateBounds.physicalQ_contDiffAt ha ha1 hp).prodMk
    ((PhysicalCoordinateBounds.physicalX_contDiffAt ha ha1 hp).prodMk
      (PhysicalCoordinateBounds.physicalEta_contDiffAt ha ha1 hp))

theorem physicalChart_positive {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Chart} (hp : p.1 < 1) : 0 < (physicalChart h p).1 :=
  PhysicalCoordinateBounds.physicalQ_pos (by positivity) (by linarith) hp

theorem physicalChart_inner_mem {h lo hi : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Chart} (hp : p.1 < 1)
    (hX : PhysicalCoordinateBounds.physicalX (2 * h) p ∈ Icc lo hi) :
    (physicalChart h p).2 ∈ innerBox lo hi := by
  have he := PhysicalCoordinateBounds.physicalEta_abs_lt_one
    (by positivity : 0 < 2 * h) (by linarith : 2 * h < 1) hp
  exact ⟨hX, (abs_lt.mp he).1.le, (abs_lt.mp he).2.le⟩

private theorem iteratedFDeriv_pair {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : E → G} {x : E} {k : ℕ}
    (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x) :
    iteratedFDeriv ℝ k (fun y => (f y, g y)) x =
      (iteratedFDeriv ℝ k f x).prod (iteratedFDeriv ℝ k g x) := by
  have h1 := (ContinuousLinearMap.fst ℝ F G).iteratedFDeriv_comp_left (hf.prodMk hg) le_rfl
  have h2 := (ContinuousLinearMap.snd ℝ F G).iteratedFDeriv_comp_left (hf.prodMk hg) le_rfl
  apply ContinuousMultilinearMap.ext
  intro v
  apply Prod.ext
  · exact (congrArg (fun M => M v) h1).symm
  · exact (congrArg (fun M => M v) h2).symm

/-- The actual similarity-coordinate map loses at most one q-power per
physical derivative, uniformly on a fixed bounded X range. -/
theorem physicalChart_jet_bound {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (lo hi : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Chart, p.1 < 1 → (physicalChart h p).1 ≤ 1 →
      (physicalChart h p).2.1 ∈ Icc lo hi →
      ‖iteratedFDeriv ℝ n (physicalChart h) p‖ ≤ C * (physicalChart h p).1 ^ (-(n : ℝ)) := by
  have ha : 0 < 2 * h := by positivity
  have ha1 : 2 * h < 1 := by linarith
  obtain ⟨C, hC, hb⟩ := PhysicalCoordinateBounds.physical_coordinate_derivative_bounds
    ha ha1 lo hi 1 n
  refine ⟨C, hC, fun p hp hq1 hX => ?_⟩
  have hq := (PhysicalCoordinateBounds.physicalQ_contDiffAt ha ha1 hp).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hx := (PhysicalCoordinateBounds.physicalX_contDiffAt ha ha1 hp).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have he := (PhysicalCoordinateBounds.physicalEta_contDiffAt ha ha1 hp).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  obtain ⟨bq, be, bx⟩ := hb p hp hq1 hX
  change ‖iteratedFDeriv ℝ n (fun y =>
    (PhysicalCoordinateBounds.physicalQ (2 * h) y,
      (PhysicalCoordinateBounds.physicalX (2 * h) y,
        PhysicalCoordinateBounds.physicalEta (2 * h) y))) p‖ ≤ _
  rw [iteratedFDeriv_pair hq (hx.prodMk he), iteratedFDeriv_pair hx he,
    ContinuousMultilinearMap.opNorm_prod, ContinuousMultilinearMap.opNorm_prod]
  exact max_le bq (max_le bx be)

theorem physicalChart_finite_bound {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (lo hi : ℝ) (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ p : Chart, p.1 < 1 → (physicalChart h p).1 ≤ 1 →
      (physicalChart h p).2.1 ∈ Icc lo hi → ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i (physicalChart h) p‖ ≤ (D / (physicalChart h p).1) ^ i := by
  classical
  choose C hC hb using fun i => physicalChart_jet_bound hh hh1 lo hi i
  let D := 1 + ∑ i ∈ Finset.range (n + 1), C i
  have hD : 1 ≤ D := by
    dsimp [D]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => (hC i).le))
  refine ⟨D, hD, fun p hp hq1 hX i hi hin => ?_⟩
  have hq := physicalChart_positive hh hh1 hp
  have hCi : C i ≤ D := by
    have hsum := Finset.single_le_sum (fun j _ => (hC j).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hin))
    dsimp [D]
    linarith
  have hDp : D ≤ D ^ i := by
    simpa only [pow_one] using pow_le_pow_right₀ hD hi
  calc
    _ ≤ C i * (physicalChart h p).1 ^ (-(i : ℝ)) := hb i p hp hq1 hX
    _ ≤ D ^ i * (physicalChart h p).1 ^ (-(i : ℝ)) :=
      mul_le_mul_of_nonneg_right (hCi.trans hDp) (Real.rpow_nonneg hq.le _)
    _ = (D / (physicalChart h p).1) ^ i := by
      rw [Real.rpow_neg hq.le, Real.rpow_natCast, div_pow]
      ring

/-- A quantitative chain rule on the actual positive-time domain. -/
theorem physical_composition_bound {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {F : Chart → V} (hF : ContDiffOn ℝ ∞ F {y | 0 < y.1})
    {p : Chart} (hp : p.1 < 1) (n : ℕ) {C D : ℝ}
    (hC : ∀ i ≤ n, ‖iteratedFDeriv ℝ i F (physicalChart h p)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i (physicalChart h) p‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (F ∘ physicalChart h) p‖ ≤ n.factorial * C * D ^ n := by
  have ht : IsOpen {y : Chart | 0 < y.1} := isOpen_lt continuous_const continuous_fst
  have hs : IsOpen {p : Chart | p.1 < 1} := isOpen_lt continuous_fst continuous_const
  have hc : ContDiffOn ℝ ∞ (physicalChart h) {p : Chart | p.1 < 1} :=
    fun p hp => (physicalChart_smoothAt hh hh1 hp).contDiffWithinAt
  have hmap : MapsTo (physicalChart h) {p : Chart | p.1 < 1} {y : Chart | 0 < y.1} :=
    fun p hp => physicalChart_positive hh hh1 hp
  have hb := norm_iteratedFDerivWithin_comp_le hF hc
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) ht.uniqueDiffOn hs.uniqueDiffOn hmap hp
    (fun i hi => by simpa only [iteratedFDerivWithin_of_isOpen i ht (hmap hp)] using hC i hi)
    (fun i hi hin => by simpa only [iteratedFDerivWithin_of_isOpen i hs hp] using hD i hi hin)
  simpa only [iteratedFDerivWithin_of_isOpen n hs hp] using hb

/-- Actual physical derivatives of a tail have arbitrary prescribed decay
after choosing the prefix for that derivative order and requested power. -/
theorem exists_physical_uncut_tail {a : ℕ → ℕ} {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j)) (lo hi : ℝ)
    (ha : AdmissibleScales h f (innerBox lo hi) a) (m Jmin : ℕ) (P : ℝ) :
    ∃ J : ℕ, Jmin ≤ J ∧ m ≤ J ∧ ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ p : Chart, p.1 < 1 → (physicalChart h p).1 < δ →
        (physicalChart h p).2.1 ∈ Icc lo hi →
        ‖iteratedFDeriv ℝ m
          ((fun y => slowSum a h f y - uncutPrefix h f J y) ∘ physicalChart h) p‖ ≤
            C * (physicalChart h p).1 ^ P := by
  obtain ⟨J, hJmin, hJm, δ, hδ, hb⟩ := exists_ordinary_uncut_tail hh hf ha m Jmin (P + m)
  obtain ⟨D, hD, hDb⟩ := physicalChart_finite_bound hh hh1 lo hi m
  let C := (m.factorial : ℝ) * (1 / 2 : ℝ) ^ J * D ^ m
  refine ⟨J, hJmin, hJm, min δ 1, C, lt_min hδ (by norm_num), ?_, ?_⟩
  · dsimp [C]
    have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
    positivity
  intro p hp hsmall hX
  have hq := physicalChart_positive hh hh1 hp
  have hq1 : (physicalChart h p).1 ≤ 1 := (hsmall.trans_le (min_le_right _ _)).le
  have hw := physicalChart_inner_mem hh hh1 hp hX
  have hFs : ContDiffOn ℝ ∞ (fun y => slowSum a h f y - uncutPrefix h f J y)
      {y | 0 < y.1} := by
    apply (slowSum_smoothOn ha.strictMono hf h).sub
    intro y hy
    apply ContDiffAt.contDiffWithinAt
    apply ((hf 0).comp contDiff_snd).contDiffAt.add
    exact ContDiffAt.sum (fun j _ => positiveCoefficient_smoothAt hf h j hy)
  have hbound := physical_composition_bound hh hh1 hFs hp m
    (C := (1 / 2 : ℝ) ^ J * (physicalChart h p).1 ^ (P + m))
    (D := D / (physicalChart h p).1)
    (fun i hi => hb i hi _ hq (hsmall.trans_le (min_le_left _ _)) _ hw)
    (hDb p hp hq1 hX)
  refine hbound.trans_eq ?_
  dsimp [C]
  rw [Real.rpow_add hq, Real.rpow_natCast, div_pow]
  have hqn : (physicalChart h p).1 ^ m ≠ 0 := pow_ne_zero m hq.ne'
  field_simp [hq.ne', hqn]; simp [← mul_pow]
  congr 1
  field_simp

end PhysicalCoordinates

section PhysicalProfiles

@[simp] theorem physicalChart_eq (h : ℝ) (p : Chart) :
    physicalChart h p = (SimilarityProfile.q h p, SimilarityProfile.inner h p) := rfl

/-- Restoring a fixed leading q-power after summing the normalized data. -/
noncomputable def physicalProfile (a : ℕ → ℕ) (h b : ℝ) (f : ℕ → Inner → V)
    (p : Chart) : V := (physicalChart h p).1 ^ b • slowSum a h f (physicalChart h p)

theorem physicalProfile_smoothAt {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {f : ℕ → Inner → V}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (b : ℝ) {p : Chart} (hp : p.1 < 1) :
    ContDiffAt ℝ ∞ (physicalProfile a h b f) p := by
  have hc := physicalChart_smoothAt hh hh1 hp
  exact (hc.fst.rpow_const_of_ne (physicalChart_positive hh hh1 hp).ne').smul
    ((slowSum_smoothAt ha hf h (physicalChart_positive hh hh1 hp)).comp p hc)

theorem physicalProfile_smoothOn {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {f : ℕ → Inner → V}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (b : ℝ) :
    ContDiffOn ℝ ∞ (physicalProfile a h b f) (Iio 1 ×ˢ (univ : Set Inner)) :=
  fun _ hp => (physicalProfile_smoothAt ha hh hh1 hf b hp.1).contDiffWithinAt

/-- Coefficient weight, with branches according to `j = 0`. -/
noncomputable def coefficientWeight (a : ℕ → ℕ) (h q : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else SmoothCutoffs.scaledCutoff (a j) q * q ^ (2 * h * j)

/-- For a fixed positive q, a single finite set represents every coefficient
family, at every inner point. This is independent of the coefficient values. -/
theorem slowSum_finite_at_scale {a : ℕ → ℕ} (ha : StrictMono a) (h : ℝ)
    {q : ℝ} (hq : 0 < q) : ∃ N : ℕ, ∀ f : ℕ → Inner → ℝ, ∀ w : Inner,
      slowSum a h f (q, w) = f 0 w +
        ∑ j ∈ Finset.range N, coefficientWeight a h q j * f j w := by
  obtain ⟨N, hN⟩ := SmoothCutoffs.scaledCutoffs_zero_on_common_neighborhood
    (fun j => (a j : ℝ)) (SolenoidalDiagonal.realScales_tendsto ha) hq
  refine ⟨N, fun f w => ?_⟩
  change f 0 w + ∑' j, slowStage a h f j (q, w) = _
  rw [tsum_eq_sum (s := Finset.range N) (fun j hj => by
    have hn : N ≤ j := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hj)
    simp only [slowStage, SolenoidalDiagonal.cutStage, hN j hn q (half_lt_self hq), zero_smul])]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hz : j = 0
  · subst j
    simp [coefficientWeight]
  · simp only [slowStage, SolenoidalDiagonal.cutStage, positiveCoefficient, coefficientWeight,
      hz, ite_false, powerCoefficient, smul_eq_mul]
    ring

/-- Differentiation in X commutes with the actual locally finite series.
The cutoff depends only on q, so no radial cutoff term appears. -/
theorem hasDerivAt_slowSum_X {a : ℕ → ℕ} (ha : StrictMono a) (h : ℝ)
    {f : ℕ → Inner → ℝ} (hf : ∀ j, ContDiff ℝ ∞ (f j))
    {q : ℝ} (hq : 0 < q) (X eta : ℝ) :
    HasDerivAt (fun x => slowSum a h f (q, (x, eta)))
      (slowSum a h (fun j => SimilarityProfile.partialX (f j)) (q, (X, eta))) X := by
  obtain ⟨N, hN⟩ := slowSum_finite_at_scale ha h hq
  have hd : ∀ j, HasDerivAt (fun x => f j (x, eta))
      (SimilarityProfile.partialX (f j) (X, eta)) X := by
    intro j
    exact ((hf j).differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt X
      ((hasDerivAt_id X).prodMk (hasDerivAt_const X eta))
  have ht := (hd 0).add (HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.range N) =>
    (hd j).const_mul (coefficientWeight a h q j)))
  convert! ht using 1
  · funext x
    exact hN f (x, eta)
  · exact hN (fun j => SimilarityProfile.partialX (f j)) (X, eta)

theorem hasDerivAt_physicalProfile_s {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {f : ℕ → Inner → ℝ}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (b : ℝ) {p : Chart} (hp : p.1 < 1) :
    HasDerivAt (fun s => physicalProfile a h b f (p.1, (s, p.2.2)))
      (physicalProfile a h (b - 1) (fun j => SimilarityProfile.partialX (f j)) p) p.2.1 := by
  have hq := SimilarityProfile.q_pos hh hh1 hp
  have hx : HasDerivAt (fun s => s / SimilarityProfile.q h p)
      (1 / SimilarityProfile.q h p) p.2.1 := (hasDerivAt_id _).div_const _
  have hc := (hasDerivAt_slowSum_X ha h hf hq (SimilarityProfile.X h p)
    (SimilarityProfile.eta h p)).comp p.2.1 hx
  have hm := hc.const_mul (SimilarityProfile.q h p ^ b)
  have he : SimilarityProfile.q h p ^ b *
      (slowSum a h (fun j => SimilarityProfile.partialX (f j))
        (SimilarityProfile.q h p, SimilarityProfile.inner h p) * (1 / SimilarityProfile.q h p)) =
      physicalProfile a h (b - 1) (fun j => SimilarityProfile.partialX (f j)) p := by
    simp only [physicalProfile, physicalChart_eq, smul_eq_mul,
      Real.rpow_sub_one hq.ne']
    ring
  exact hm.congr_deriv he

theorem partialS_physicalProfile {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {f : ℕ → Inner → ℝ}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (b : ℝ) {p : Chart} (hp : p.1 < 1) :
    AxisymmetricFields.partialS (physicalProfile a h b f) p =
      physicalProfile a h (b - 1) (fun j => SimilarityProfile.partialX (f j)) p := by
  have hd := ((physicalProfile_smoothAt ha hh hh1 hf b hp).differentiableAt (by simp)).hasFDerivAt
  have hc := hd.comp_hasDerivAt p.2.1 ((hasDerivAt_const p.2.1 p.1).prodMk
    ((hasDerivAt_id p.2.1).prodMk (hasDerivAt_const p.2.1 p.2.2)))
  exact hc.unique (hasDerivAt_physicalProfile_s ha hh hh1 hf b hp)

end PhysicalProfiles

section PoweredTails

/-- Physical uncut prefix, given by `(physicalChart h p).1 ^ b • uncutPrefix h f J
(physicalChart h p)`. -/
noncomputable def physicalUncutPrefix (h b : ℝ) (f : ℕ → Inner → V) (J : ℕ)
    (p : Chart) : V := (physicalChart h p).1 ^ b • uncutPrefix h f J (physicalChart h p)

theorem uncutPrefix_smoothOn {f : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (h : ℝ) (J : ℕ) : ContDiffOn ℝ ∞ (uncutPrefix h f J) {y | 0 < y.1} := by
  intro y hy
  apply ContDiffAt.contDiffWithinAt
  apply ((hf 0).comp contDiff_snd).contDiffAt.add
  exact ContDiffAt.sum (fun j _ => positiveCoefficient_smoothAt hf h j hy)

theorem norm_smul_jet_le_on {F : Chart → ℝ} {G : Chart → V} {U : Set Chart}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G U)
    {p : Chart} (hp : p ∈ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => F y • G y) p‖ ≤
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i F p‖ * ‖iteratedFDeriv ℝ (m - i) G p‖ := by
  have hb := norm_iteratedFDerivWithin_smul_le hF hG hU.uniqueDiffOn hp
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)
  simpa only [iteratedFDerivWithin_of_isOpen _ hU hp] using hb

/-- Restoring any fixed leading q-power preserves arbitrary-order asymptotic
summation. All products and derivatives here are the actual physical ones. -/
theorem powered_physical_tail_of_chart_bound {a : ℕ → ℕ} {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j)) (lo hi b : ℝ)
    (ha : StrictMono a) (J M : ℕ) (P E δ : ℝ) (hE : 0 ≤ E) (hδ : 0 < δ)
    (hb : ∀ m ≤ M, ∀ q : ℝ, 0 < q → q < δ → ∀ w ∈ innerBox lo hi,
      ‖iteratedFDeriv ℝ m (fun y => slowSum a h f y - uncutPrefix h f J y) (q, w)‖ ≤
        E * q ^ (P - b + M)) :
    ∃ δ' C : ℝ, 0 < δ' ∧ 0 < C ∧
      ∀ m ≤ M, ∀ p : Chart, p.1 < 1 → (physicalChart h p).1 < δ' →
        (physicalChart h p).2.1 ∈ Icc lo hi →
        ‖iteratedFDeriv ℝ m
          (fun y => physicalProfile a h b f y - physicalUncutPrefix h b f J y) p‖ ≤
            C * (physicalChart h p).1 ^ P := by
  classical
  let S := P - b + M
  obtain ⟨D, hD, hDb⟩ := physicalChart_finite_bound hh hh1 lo hi M
  choose A hA hAb using fun i => PhysicalCoordinateBounds.physical_power_derivative_bound
    (by positivity : 0 < 2 * h) (by linarith : 2 * h < 1) b lo hi 1 i
  let K : ℕ → ℕ → ℝ := fun m i => (m.choose i : ℝ) * A i *
    ((m - i).factorial : ℝ) * E * D ^ (m - i)
  let C := (∑ m ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (m + 1), K m i) + 1
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hKn : ∀ m i, 0 ≤ K m i := by
    intro m i
    have := hA i
    dsimp [K]
    positivity
  have hCn : 0 < C := by
    have := Finset.sum_nonneg (s := Finset.range (M + 1))
      (fun m _ => Finset.sum_nonneg (s := Finset.range (m + 1)) (fun i _ => hKn m i))
    dsimp [C]
    linarith
  refine ⟨min δ 1, C, lt_min hδ (by norm_num), hCn, ?_⟩
  intro m hm p hp hsmall hX
  let q := (physicalChart h p).1
  have hq : 0 < q := physicalChart_positive hh hh1 hp
  have hq1 : q ≤ 1 := (hsmall.trans_le (min_le_right _ _)).le
  have hw := physicalChart_inner_mem hh hh1 hp hX
  let F : Chart → V := fun y => slowSum a h f y - uncutPrefix h f J y
  have hF : ContDiffOn ℝ ∞ F {y | 0 < y.1} :=
    (slowSum_smoothOn ha hf h).sub (uncutPrefix_smoothOn hf h J)
  have hU : IsOpen {y : Chart | y.1 < 1} := isOpen_lt continuous_fst continuous_const
  have hPow : ContDiffOn ℝ ∞ (fun y : Chart => (physicalChart h y).1 ^ b) {y | y.1 < 1} := by
    intro y hy
    exact (((physicalChart_smoothAt hh hh1 hy).fst).rpow_const_of_ne
      (physicalChart_positive hh hh1 hy).ne').contDiffWithinAt
  have hFc : ContDiffOn ℝ ∞ (F ∘ physicalChart h) {y | y.1 < 1} := by
    intro y hy
    exact ((hF.contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds
      (physicalChart_positive hh hh1 hy))).comp y
        (physicalChart_smoothAt hh hh1 hy)).contDiffWithinAt
  have heq : (fun y => physicalProfile a h b f y - physicalUncutPrefix h b f J y) =
      (fun y => (physicalChart h y).1 ^ b • (F ∘ physicalChart h) y) := by
    funext y
    simp only [physicalProfile, physicalUncutPrefix, F, Function.comp_apply, smul_sub]
  rw [heq]
  refine (norm_smul_jet_le_on hU hPow hFc hp m).trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (m + 1), K m i * q ^ (P + M - m) := by
      apply Finset.sum_le_sum
      intro i hi
      have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hFi := physical_composition_bound hh hh1 hF hp (m - i)
        (C := E * q ^ S) (D := D / q)
        (fun k hk => hb k (by omega) _ hq (hsmall.trans_le (min_le_left _ _)) _ hw)
        (fun k hk hki => hDb p hp hq1 hX k hk (by omega))
      have hAi : ‖iteratedFDeriv ℝ i (fun y : Chart => (physicalChart h y).1 ^ b) p‖ ≤
          A i * q ^ (b - i) := hAb i p hp hq1 hX
      have hi0 : 0 ≤ (m.choose i : ℝ) := by positivity
      have hAi0 := (hA i).le
      refine (mul_le_mul (mul_le_mul_of_nonneg_left hAi hi0) hFi
        (norm_nonneg _) (by positivity)).trans_eq ?_
      have hpow : q ^ (b - i) * q ^ S / q ^ (m - i) = q ^ (P + M - m) := by
        rw [← Real.rpow_natCast q (m - i), ← Real.rpow_add hq, ← Real.rpow_sub hq]
        congr 1
        rw [Nat.cast_sub him]
        dsimp [S]
        ring
      dsimp only [K]
      calc
        _ = ((m.choose i : ℝ) * A i * ((m - i).factorial : ℝ) *
            E * D ^ (m - i)) *
              (q ^ (b - i) * q ^ S / q ^ (m - i)) := by rw [div_pow]; ring
        _ = _ := by rw [hpow]
    _ = (∑ i ∈ Finset.range (m + 1), K m i) * q ^ (P + M - m) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ i ∈ Finset.range (m + 1), K m i) * q ^ P := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun i _ => hKn m i))
      apply Real.rpow_le_rpow_of_exponent_ge hq hq1
      have hmR : (m : ℝ) ≤ M := by exact_mod_cast hm
      linarith
    _ ≤ C * q ^ P := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hq.le _)
      have hsingle := Finset.single_le_sum
        (fun k (_ : k ∈ Finset.range (M + 1)) =>
          Finset.sum_nonneg (s := Finset.range (k + 1)) (fun i _ => hKn k i))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
      dsimp [C]
      linarith

theorem exists_powered_physical_tail_finite {a : ℕ → ℕ} {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j)) (lo hi b : ℝ)
    (ha : AdmissibleScales h f (innerBox lo hi) a) (M Jmin : ℕ) (P : ℝ) :
    ∃ J : ℕ, Jmin ≤ J ∧ M ≤ J ∧ ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ m ≤ M, ∀ p : Chart, p.1 < 1 → (physicalChart h p).1 < δ →
        (physicalChart h p).2.1 ∈ Icc lo hi →
        ‖iteratedFDeriv ℝ m
          (fun y => physicalProfile a h b f y - physicalUncutPrefix h b f J y) p‖ ≤
            C * (physicalChart h p).1 ^ P := by
  obtain ⟨J, hJmin, hJM, δ, hδ, hb⟩ :=
    exists_ordinary_uncut_tail hh hf ha M Jmin (P - b + M)
  obtain ⟨δ', C, hδ', hC, hbound⟩ := powered_physical_tail_of_chart_bound
    hh hh1 hf lo hi b ha.strictMono J M P ((1 / 2 : ℝ) ^ J) δ (by positivity) hδ hb
  exact ⟨J, hJmin, hJM, δ', C, hδ', hC, hbound⟩

theorem exists_powered_physical_tail {a : ℕ → ℕ} {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j)) (lo hi b : ℝ)
    (ha : AdmissibleScales h f (innerBox lo hi) a) (m Jmin : ℕ) (P : ℝ) :
    ∃ J : ℕ, Jmin ≤ J ∧ m ≤ J ∧ ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ p : Chart, p.1 < 1 → (physicalChart h p).1 < δ →
        (physicalChart h p).2.1 ∈ Icc lo hi →
        ‖iteratedFDeriv ℝ m
          (fun y => physicalProfile a h b f y - physicalUncutPrefix h b f J y) p‖ ≤
            C * (physicalChart h p).1 ^ P := by
  obtain ⟨J, hJ, hJm, δ, C, hδ, hC, hb⟩ :=
    exists_powered_physical_tail_finite hh hh1 hf lo hi b ha m Jmin P
  exact ⟨J, hJ, hJm, δ, C, hδ, hC, hb m le_rfl⟩

end PoweredTails

section LinearMaps

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem slowStage_map (L : V →L[ℝ] W) (a : ℕ → ℕ) (h : ℝ)
    (f : ℕ → Inner → V) (j : ℕ) :
    slowStage a h (fun n w => L (f n w)) j = L ∘ slowStage a h f j := by
  funext y
  by_cases hj : j = 0
  · subst j
    simp
  · simp [slowStage, SolenoidalDiagonal.cutStage, positiveCoefficient, hj,
      powerCoefficient]

theorem slowSum_map (L : V →L[ℝ] W) {a : ℕ → ℕ} (ha : StrictMono a)
    (h : ℝ) (f : ℕ → Inner → V) {y : Chart} (hy : 0 < y.1) :
    slowSum a h (fun n w => L (f n w)) y = L (slowSum a h f y) := by
  have hs := SolenoidalDiagonal.summable_cutStage
    (SolenoidalDiagonal.realScales_tendsto ha) continuous_fst.continuousAt hy
    (positiveCoefficient h f)
  have hss : Summable (fun j => slowStage a h f j y) := hs
  change L (f 0 y.2) + ∑' j, slowStage a h (fun n w => L (f n w)) j y =
    L (f 0 y.2 + ∑' j, slowStage a h f j y)
  rw [L.map_add, L.map_tsum hss]
  congr 1
  apply tsum_congr
  intro j
  rw [slowStage_map]
  rfl

theorem norm_jet_map_le (L : V →L[ℝ] W) {F : Chart → V} {y : Chart}
    (hF : ContDiffAt ℝ ∞ F y) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (L ∘ F) y‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ m F y‖ := by
  rw [L.iteratedFDeriv_comp_left hF (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)]
  exact L.norm_compContinuousMultilinearMap_le _

theorem AdmissibleScales.map {a : ℕ → ℕ} {h : ℝ} {f : ℕ → Inner → V} {K : Set Inner}
    (ha : AdmissibleScales h f K a) (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (L : V →L[ℝ] W) (hL : ‖L‖ ≤ 1) :
    AdmissibleScales h (fun j w => L (f j w)) K a := by
  refine ⟨ha.positive, ha.doubling, ha.strictMono, ?_, ?_⟩
  · intro j hj m hm q hq hq1 w hw
    rw [slowStage_map]
    exact (norm_jet_map_le L (slowStage_smoothAt hf a h j hq) m).trans
      ((mul_le_of_le_one_left (norm_nonneg _) hL).trans (ha.ordinary j hj m hm q hq hq1 w hw))
  · intro j hj m hm q hq hq1 w hw
    rw [slowStage_map]
    have hs : ContDiffAt ℝ ∞ (slowStage a h f j ∘ scaleMap q) (1, w) := by
      apply ContDiffAt.comp
      · simpa only [scaleMap_apply, mul_one] using slowStage_smoothAt hf a h j (y := (q, w)) hq
      · exact (scaleMap q).contDiff.contDiffAt
    exact (norm_jet_map_le L hs m).trans
      ((mul_le_of_le_one_left (norm_nonneg _) hL).trans (ha.blown j hj m hm q hq hq1 w hw))

end LinearMaps

section BaseFields

/-- Smooth coefficient data before asymptotic summation. The radial and swirl
potentials below are constructed by actual integration from these data. -/
structure Coefficients where
  /-- Axial of `Coefficients`, of type `ℕ → Inner → ℝ`. -/
  axial : ℕ → Inner → ℝ
  /-- Phi of `Coefficients`, of type `ℕ → Inner → ℝ`. -/
  phi : ℕ → Inner → ℝ
  /-- Pressure field of `Coefficients`, of type `ℕ → Inner → ℝ`. -/
  pressure : ℕ → Inner → ℝ
  /-- Stress theta of `Coefficients`, of type `ℕ → Inner → ℝ`. -/
  stressTheta : ℕ → Inner → ℝ
  /-- Stress axial of `Coefficients`, of type `ℕ → Inner → ℝ`. -/
  stressAxial : ℕ → Inner → ℝ

/-- Smooth coefficients data, collecting `axial`, `phi`, `pressure`, `stressTheta`,
`stressAxial`. -/
structure SmoothCoefficients (d : Coefficients) : Prop where
  axial : ∀ j, ContDiff ℝ ∞ (d.axial j)
  phi : ∀ j, ContDiff ℝ ∞ (d.phi j)
  pressure : ∀ j, ContDiff ℝ ∞ (d.pressure j)
  stressTheta : ∀ j, ContDiff ℝ ∞ (d.stressTheta j)
  stressAxial : ∀ j, ContDiff ℝ ∞ (d.stressAxial j)

/-- Global radial domain, bundling `carrier`, `isOpen`, `scale_mem`. -/
noncomputable def globalRadialDomain : ProfileHistories.RadialDomain where
  carrier := univ
  isOpen := isOpen_univ
  scale_mem := by intro p hp t ht; trivial

theorem average_smooth {f : Inner → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (ProfileHistories.average f) :=
  contDiffOn_univ.mp (ProfileHistories.average_smooth globalRadialDomain hf.contDiffOn)

theorem primitive_smooth {f : Inner → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (ProfileHistories.primitive f) :=
  contDiffOn_univ.mp (ProfileHistories.primitive_smooth globalRadialDomain hf.contDiffOn)

theorem partialX_primitive {f : Inner → ℝ} (hf : ContDiff ℝ ∞ f) :
    SimilarityProfile.partialX (ProfileHistories.primitive f) = f := by
  funext w
  exact ProfileHistories.radialPartial_primitive globalRadialDomain hf.contDiffOn (mem_univ w)

/-- Bundle: an abbreviation for `Fin 7 → ℝ`. -/
abbrev Bundle := Fin 7 → ℝ

/-- One bundle forces one common cutoff schedule for the streams, angular
data, pressure, and both stress components. -/
noncomputable def coefficientBundle (C : ℝ) (d : Coefficients) (j : ℕ) (w : Inner) : Bundle :=
  ![ProfileHistories.average (d.axial j) w,
    -C⁻¹ * ProfileHistories.primitive (d.phi j) w,
    d.pressure j w, d.stressTheta j w, d.stressAxial j w, d.axial j w, d.phi j w]

theorem coefficientBundle_smooth {d : Coefficients} (hd : SmoothCoefficients d)
    (C : ℝ) (j : ℕ) : ContDiff ℝ ∞ (coefficientBundle C d j) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact average_smooth (hd.axial j)
  · exact contDiff_const.mul (primitive_smooth (hd.phi j))
  · exact hd.pressure j
  · exact hd.stressTheta j
  · exact hd.stressAxial j
  · exact hd.axial j
  · exact hd.phi j

/-- Bundle component, defined pointwise by `coefficientBundle C d j w i`. -/
noncomputable def bundleComponent (C : ℝ) (d : Coefficients) (i : Fin 7) : ℕ → Inner → ℝ :=
  fun j w => coefficientBundle C d j w i

theorem bundleComponent_smooth {d : Coefficients} (hd : SmoothCoefficients d)
    (C : ℝ) (i : Fin 7) (j : ℕ) : ContDiff ℝ ∞ (bundleComponent C d i j) :=
  contDiff_pi.mp (coefficientBundle_smooth hd C j) i

theorem admissible_component {a : ℕ → ℕ} {h C : ℝ} {d : Coefficients}
    (hd : SmoothCoefficients d) {K : Set Inner}
    (ha : AdmissibleScales h (coefficientBundle C d) K a) (i : Fin 7) :
    AdmissibleScales h (bundleComponent C d i) K a := by
  apply ha.map (coefficientBundle_smooth hd C) (ContinuousLinearMap.proj i)
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm v i

/-- H=S/s, with its smooth value at the axis provided by the radial average. -/
noncomputable def streamFactor (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) : Chart → ℝ :=
  physicalProfile a h (-CoordinateAlgebra.A h) (bundleComponent C d 0)

/-- Swirl potential, given by `physicalProfile a h (1 / 2 - CoordinateAlgebra.A h)
(bundleComponent C d 1)`. -/
noncomputable def swirlPotential (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) : Chart → ℝ :=
  physicalProfile a h (1 / 2 - CoordinateAlgebra.A h) (bundleComponent C d 1)

/-- Integrated stream, given by `p.2.1 * streamFactor a h C d p`. -/
noncomputable def integratedStream (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients)
    (p : Chart) : ℝ := p.2.1 * streamFactor a h C d p

/-- Base velocity, given by `AxisymmetricFields.velocity (streamFactor a h C d) (swirlPotential
a h C d)`. -/
noncomputable def baseVelocity (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) :
    ProblemStatement.VelocityField :=
  AxisymmetricFields.velocity (streamFactor a h C d) (swirlPotential a h C d)

/-- Base pressure, defined pointwise by `physicalProfile a h (-2 * CoordinateAlgebra.A h)
(bundleComponent C d 2) (AxisymmetricFields.profilePoint z.1 z.2)`. -/
noncomputable def basePressure (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) :
    ProblemStatement.PressureField := fun z =>
  physicalProfile a h (-2 * CoordinateAlgebra.A h) (bundleComponent C d 2)
    (AxisymmetricFields.profilePoint z.1 z.2)

/-- Base stress theta, given by `physicalProfile a h (-CoordinateAlgebra.A h - 1 / 2)
(bundleComponent C d 3)`. -/
noncomputable def baseStressTheta (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) : Chart → ℝ :=
  physicalProfile a h (-CoordinateAlgebra.A h - 1 / 2) (bundleComponent C d 3)

/-- Base stress axial, given by `physicalProfile a h (-CoordinateAlgebra.A h - 1 / 2)
(bundleComponent C d 4)`. -/
noncomputable def baseStressAxial (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) : Chart → ℝ :=
  physicalProfile a h (-CoordinateAlgebra.A h - 1 / 2) (bundleComponent C d 4)

theorem baseVelocity_smooth {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d) (C : ℝ) :
    ContDiffOn ℝ ∞ (baseVelocity a h C d) (Iio 1 ×ˢ (univ : Set ProblemStatement.Space)) :=
  AxisymmetricFields.contDiffOn_velocity
    (physicalProfile_smoothOn ha hh hh1 (bundleComponent_smooth hd C 0) _)
    (physicalProfile_smoothOn ha hh hh1 (bundleComponent_smooth hd C 1) _) (by simp)

/-- Exact Cartesian incompressibility, including the axis, follows from the
actual curl of the asymptotically summed potentials. -/
theorem baseVelocity_divergence_zero {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d) (C : ℝ)
    {t : ℝ} (ht : t < 1) (x : ProblemStatement.Space) :
    ProblemStatement.spatialDivergence (baseVelocity a h C d) t x = 0 :=
  AxisymmetricFields.divergence_velocity_on
    ((physicalProfile_smoothOn ha hh hh1 (bundleComponent_smooth hd C 0) _).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    ((physicalProfile_smoothOn ha hh hh1 (bundleComponent_smooth hd C 1) _).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) ht x

/-- Existence of the shared schedule and the actual smooth, exactly
solenoidal base uses only the supplied smooth coefficient sequence. -/
theorem exists_base_fields {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) (C lo hi : ℝ) (B : ℕ) :
    ∃ a : ℕ → ℕ, B ≤ a 0 ∧ AdmissibleScales h (coefficientBundle C d) (innerBox lo hi) a ∧
      ContDiffOn ℝ ∞ (baseVelocity a h C d) (Iio 1 ×ˢ (univ : Set ProblemStatement.Space)) ∧
      ∀ t : ℝ, t < 1 → ∀ x : ProblemStatement.Space,
        ProblemStatement.spatialDivergence (baseVelocity a h C d) t x = 0 := by
  obtain ⟨a, haB, ha⟩ := exists_admissibleScales (coefficientBundle_smooth hd C) hh
    (innerBox_isCompact lo hi) B
  exact ⟨a, haB, ha, baseVelocity_smooth ha.strictMono hh hh1 hd C,
    fun _ ht x => baseVelocity_divergence_zero ha.strictMono hh hh1 hd C ht x⟩

end BaseFields

section CoefficientIdentification

theorem uncutPrefix_eq_sum (h : ℝ) (f : ℕ → Inner → V) (J : ℕ) (y : Chart) :
    uncutPrefix h f J y =
      ∑ j ∈ Finset.range (J + 1), powerCoefficient (2 * h * j) (f j) y := by
  induction J with
  | zero => simp [uncutPrefix, positiveCoefficient, powerCoefficient]
  | succ J ih =>
      change f 0 y.2 + ∑ j ∈ Finset.range ((J + 1) + 1), positiveCoefficient h f j y = _
      rw [Finset.sum_range_succ, ← add_assoc]
      change uncutPrefix h f J y + positiveCoefficient h f (J + 1) y = _
      rw [ih]
      conv_rhs => rw [Finset.sum_range_succ]
      simp only [positiveCoefficient, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]

/-- The uncut physical prefix is the same finite expansion used in the
explicit coefficient residual calculation. -/
theorem physicalUncutPrefix_eq_finiteProfile {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (b : ℝ) (f : ℕ → Inner → ℝ) (J : ℕ) {p : Chart} (hp : p.1 < 1) :
    physicalUncutPrefix h b f J p = SlowExpansionResidual.finiteProfile J h b f p := by
  rw [physicalUncutPrefix, uncutPrefix_eq_sum]
  simp only [physicalChart_eq, smul_eq_mul, Finset.mul_sum, SlowExpansionResidual.finiteProfile,
    SimilarityProfile.pullback, powerCoefficient]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Real.rpow_add (SimilarityProfile.q_pos hh hh1 hp)]
  have he : 2 * h * (j : ℝ) = SlowExpansionResidual.slowOrder h j := by
    unfold SlowExpansionResidual.slowOrder
    ring
  rw [he]
  ring

theorem slowSum_inner_mul {a : ℕ → ℕ} (ha : StrictMono a) (h : ℝ)
    (f : ℕ → Inner → ℝ) (r : Inner → ℝ) {y : Chart} (hy : 0 < y.1) :
    slowSum a h (fun j w => r w * f j w) y = r y.2 * slowSum a h f y := by
  obtain ⟨N, hN⟩ := slowSum_finite_at_scale ha h hy
  rw [hN _ y.2, hN f y.2, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The integrated stream is literally the cut sum of q^(1−A+λj) times
the radial primitives, with its smooth axis factor retained. -/
theorem integratedStream_eq_primitive {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (C : ℝ) (d : Coefficients)
    {p : Chart} (hp : p.1 < 1) :
    integratedStream a h C d p =
      physicalProfile a h (1 - CoordinateAlgebra.A h)
        (fun j => ProfileHistories.primitive (d.axial j)) p := by
  have he : (fun j => ProfileHistories.primitive (d.axial j)) =
      (fun j w => w.1 * ProfileHistories.average (d.axial j) w) := by
    funext j w
    exact ProfileHistories.primitive_eq_mul_average _ _
  rw [he, physicalProfile, slowSum_inner_mul ha h _ _ (physicalChart_positive hh hh1 hp)]
  change p.2.1 * ((physicalChart h p).1 ^ (-CoordinateAlgebra.A h) *
    slowSum a h (fun j => ProfileHistories.average (d.axial j)) (physicalChart h p)) = _
  rw [physicalChart_eq]
  change p.2.1 * (SimilarityProfile.q h p ^ (-CoordinateAlgebra.A h) * _) =
    SimilarityProfile.q h p ^ (1 - CoordinateAlgebra.A h) *
      (SimilarityProfile.X h p * _)
  rw [show 1 - CoordinateAlgebra.A h = 1 + -CoordinateAlgebra.A h by ring,
    Real.rpow_add (SimilarityProfile.q_pos hh hh1 hp), Real.rpow_one]
  unfold SimilarityProfile.X
  field_simp [(SimilarityProfile.q_pos hh hh1 hp).ne']

theorem partialS_integratedStream {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d)
    (C : ℝ) {p : Chart} (hp : p.1 < 1) :
    AxisymmetricFields.partialS (integratedStream a h C d) p =
      physicalProfile a h (-CoordinateAlgebra.A h) d.axial p := by
  have he : integratedStream a h C d =ᶠ[𝓝 p]
      physicalProfile a h (1 - CoordinateAlgebra.A h)
        (fun j => ProfileHistories.primitive (d.axial j)) := by
    filter_upwards [continuousAt_fst.eventually (Iio_mem_nhds hp)] with y hy
    exact integratedStream_eq_primitive ha hh hh1 C d hy
  change fderiv ℝ (integratedStream a h C d) p (0, (1, 0)) = _
  rw [he.fderiv_eq]
  change AxisymmetricFields.partialS
    (physicalProfile a h (1 - CoordinateAlgebra.A h)
      (fun j => ProfileHistories.primitive (d.axial j))) p = _
  rw [partialS_physicalProfile ha hh hh1 (fun j => primitive_smooth (hd.axial j)) _ hp]
  simp_rw [partialX_primitive (hd.axial _)]
  rw [show 1 - CoordinateAlgebra.A h - 1 = -CoordinateAlgebra.A h by ring]

theorem partialS_radial_mul {H : Chart → ℝ} {p : Chart} (hH : DifferentiableAt ℝ H p) :
    AxisymmetricFields.partialS (fun y => y.2.1 * H y) p =
      H p + p.2.1 * AxisymmetricFields.partialS H p := by
  have hs : HasFDerivAt (fun y : Chart => y.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Inner)) p :=
    (hasFDerivAt_fst).comp p hasFDerivAt_snd
  unfold AxisymmetricFields.partialS
  rw [(hs.fun_mul hH.hasFDerivAt).fderiv]
  simp
  ring

/-- The actual axial component is the direct cut sum of the axial profiles;
the derivative of the integrated stream has been computed, not postulated. -/
theorem baseVelocity_axial {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d)
    (C : ℝ) {t : ℝ} (ht : t < 1) (x : ProblemStatement.Space) :
    baseVelocity a h C d (t, x) 2 =
      physicalProfile a h (-CoordinateAlgebra.A h) d.axial (AxisymmetricFields.profilePoint t x) :=
          by
  have hH := (physicalProfile_smoothAt ha hh hh1 (bundleComponent_smooth hd C 0)
    (-CoordinateAlgebra.A h) (p := AxisymmetricFields.profilePoint t x) ht).differentiableAt (by
        simp)
  have hK := (physicalProfile_smoothAt ha hh hh1 (bundleComponent_smooth hd C 1)
    (1 / 2 - CoordinateAlgebra.A h) (p := AxisymmetricFields.profilePoint t x) ht).differentiableAt
        (by
        simp)
  change DifferentiableAt ℝ (streamFactor a h C d) (AxisymmetricFields.profilePoint t x) at hH
  change DifferentiableAt ℝ (swirlPotential a h C d) (AxisymmetricFields.profilePoint t x) at hK
  rw [baseVelocity, AxisymmetricFields.velocity_two _ _ _ _ hH hK]
  exact (partialS_radial_mul hH).symm.trans (partialS_integratedStream ha hh hh1 hd C ht)

theorem partialX_swirl_primitive {f : Inner → ℝ} (hf : ContDiff ℝ ∞ f) (C : ℝ) :
    SimilarityProfile.partialX (fun w => -C⁻¹ * ProfileHistories.primitive f w) =
      (fun w => -C⁻¹ * f w) := by
  funext w
  unfold SimilarityProfile.partialX
  rw [fderiv_const_mul ((primitive_smooth hf).differentiable (by simp)).differentiableAt]
  change -C⁻¹ * SimilarityProfile.partialX (ProfileHistories.primitive f) w = _
  rw [partialX_primitive hf]

theorem partialS_swirlPotential {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d)
    (C : ℝ) {p : Chart} (hp : p.1 < 1) :
    AxisymmetricFields.partialS (swirlPotential a h C d) p =
      -C⁻¹ * physicalProfile a h (-CoordinateAlgebra.A h - 1 / 2) d.phi p := by
  rw [swirlPotential, partialS_physicalProfile ha hh hh1 (bundleComponent_smooth hd C 1) _ hp]
  change physicalProfile a h (1 / 2 - CoordinateAlgebra.A h - 1)
    (fun j => SimilarityProfile.partialX (fun w => -C⁻¹ * ProfileHistories.primitive (d.phi j) w))
        p = _
  simp_rw [partialX_swirl_primitive (hd.phi _) C]
  rw [show 1 / 2 - CoordinateAlgebra.A h - 1 = -CoordinateAlgebra.A h - 1 / 2 by ring]
  unfold physicalProfile
  rw [slowSum_inner_mul ha h d.phi (fun _ => -C⁻¹) (physicalChart_positive hh hh1 hp)]
  simp only [smul_eq_mul]
  ring

end CoefficientIdentification

section CartesianTails

theorem physicalUncutPrefix_smoothAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j)) (b : ℝ) (J : ℕ)
    {p : Chart} (hp : p.1 < 1) : ContDiffAt ℝ ∞ (physicalUncutPrefix h b f J) p := by
  have hc := physicalChart_smoothAt hh hh1 hp
  have hi := (uncutPrefix_smoothOn hf h J).contDiffAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds (physicalChart_positive hh hh1 hp))
  exact (hc.fst.rpow_const_of_ne (physicalChart_positive hh hh1 hp).ne').smul (hi.comp p hc)

theorem compact_jet_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → V} {U K : Set E} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hK : IsCompact K) (hKU : K ⊆ U) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ K, ‖iteratedFDeriv ℝ m F x‖ ≤ C := by
  have hc := (hF.continuousOn_iteratedFDerivWithin (m := m)
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) hU.uniqueDiffOn).mono hKU
  have he : ContinuousOn (iteratedFDeriv ℝ m F) K := by
    apply hc.congr
    intro x hx
    exact (iteratedFDerivWithin_of_isOpen m hU (hKU hx)).symm
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn he
  exact ⟨max 1 C, le_max_left _ _, fun x hx => (hC x hx).trans (le_max_right _ _)⟩

theorem compact_map_finite_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → V} (hF : ContDiff ℝ ∞ F) {K : Set E} (hK : IsCompact K) (M : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ x ∈ K, ∀ i, 1 ≤ i → i ≤ M →
      ‖iteratedFDeriv ℝ i F x‖ ≤ D ^ i := by
  classical
  choose C hC hCb using fun i => compact_jet_bound isOpen_univ hF.contDiffOn hK
    (subset_univ K) i
  let D := 1 + ∑ i ∈ Finset.range (M + 1), C i
  have hD : 1 ≤ D := by
    dsimp [D]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => (zero_le_one.trans (hC i))))
  refine ⟨D, hD, fun x hx i hi hiM => ?_⟩
  have hCi : C i ≤ D := by
    have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (M + 1)) =>
      zero_le_one.trans (hC j)) (Finset.mem_range.mpr (Nat.lt_succ_of_le hiM))
    dsimp [D]
    linarith
  refine (hCb i x hx).trans (hCi.trans ?_)
  simpa only [pow_one] using pow_le_pow_right₀ hD hi

/-- Cartesian chart, given by `physicalChart h (AxisymmetricFields.profilePoint z.1 z.2)`. -/
noncomputable def cartesianChart (h : ℝ) (z : ProblemStatement.SpaceTime) : Chart :=
  physicalChart h (AxisymmetricFields.profilePoint z.1 z.2)

/-- Cartesian profile, given by `physicalProfile a h b f (AxisymmetricFields.profilePoint z.1
z.2)`. -/
noncomputable def cartesianProfile (a : ℕ → ℕ) (h b : ℝ) (f : ℕ → Inner → V)
    (z : ProblemStatement.SpaceTime) : V :=
  physicalProfile a h b f (AxisymmetricFields.profilePoint z.1 z.2)

/-- Cartesian uncut prefix, given by `physicalUncutPrefix h b f J
(AxisymmetricFields.profilePoint z.1 z.2)`. -/
noncomputable def cartesianUncutPrefix (h b : ℝ) (f : ℕ → Inner → V) (J : ℕ)
    (z : ProblemStatement.SpaceTime) : V :=
  physicalUncutPrefix h b f J (AxisymmetricFields.profilePoint z.1 z.2)

/-- The map `(t,x)↦(t,(|x_perp|²/2,x₃))` is smooth at the axis. On any fixed
compact Cartesian set its derivatives have finite bounds, so the proved
physical-profile tail estimates imply actual Cartesian space-time estimates. -/
theorem exists_cartesian_profile_tail {a : ℕ → ℕ} {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j)) (lo hi b : ℝ)
    (ha : AdmissibleScales h f (innerBox lo hi) a)
    {K : Set ProblemStatement.SpaceTime} (hK : IsCompact K) (m Jmin : ℕ) (P : ℝ) :
    ∃ J : ℕ, Jmin ≤ J ∧ m ≤ J ∧ ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ z ∈ K, z.1 < 1 → (cartesianChart h z).1 < δ →
        (cartesianChart h z).2.1 ∈ Icc lo hi →
        ‖iteratedFDeriv ℝ m
          (fun y => cartesianProfile a h b f y - cartesianUncutPrefix h b f J y) z‖ ≤
            C * (cartesianChart h z).1 ^ P := by
  obtain ⟨J, hJmin, hJm, δ, C, hδ, hC, hb⟩ :=
    exists_powered_physical_tail_finite hh hh1 hf lo hi b ha m Jmin P
  let G : ProblemStatement.SpaceTime → Chart := fun z => AxisymmetricFields.profilePoint z.1 z.2
  have hG : ContDiff ℝ ∞ G := AxisymmetricFields.contDiff_profilePoint
  obtain ⟨D, hD, hDb⟩ := compact_map_finite_bound hG hK m
  let B := (m.factorial : ℝ) * C * D ^ m
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  refine ⟨J, hJmin, hJm, δ, B, hδ, by dsimp [B]; positivity, ?_⟩
  intro z hz hzt hq hX
  let F : Chart → V := fun p => physicalProfile a h b f p - physicalUncutPrefix h b f J p
  have hU : IsOpen {p : Chart | p.1 < 1} := isOpen_lt continuous_fst continuous_const
  have hS : IsOpen {p : ProblemStatement.SpaceTime | p.1 < 1} :=
    isOpen_lt continuous_fst continuous_const
  have hF : ContDiffOn ℝ ∞ F {p | p.1 < 1} := by
    intro p hp
    exact ((physicalProfile_smoothAt ha.strictMono hh hh1 hf b hp).sub
      (physicalUncutPrefix_smoothAt hh hh1 hf b J hp)).contDiffWithinAt
  have hmaps : MapsTo G {p | p.1 < 1} {p | p.1 < 1} := fun _ hp => hp
  have hc := norm_iteratedFDerivWithin_comp_le hF hG.contDiffOn
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) hU.uniqueDiffOn hS.uniqueDiffOn hmaps hzt
    (C := C * (cartesianChart h z).1 ^ P) (D := D)
    (fun i hi => by
      rw [iteratedFDerivWithin_of_isOpen i hU hzt]
      exact hb i hi (G z) hzt hq hX)
    (fun i hi him => by
      rw [iteratedFDerivWithin_of_isOpen i hS hzt]
      exact hDb z hz i hi him)
  rw [iteratedFDerivWithin_of_isOpen m hS hzt] at hc
  exact hc.trans_eq (by dsimp [B]; ring)

end CartesianTails

section NormalizedTangential

/-- Multiplication by a smooth fixed inner-coordinate factor preserves the
derived q^(2h) bound. This handles the radius factor on an active annulus. -/
theorem normalized_correction_smul_inner {a : ℕ → ℕ} {h : ℝ} (hh : 0 < h)
    {f : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j))
    {K U : Set Inner} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (ha : AdmissibleScales h f K a) {r : Inner → ℝ} (hr : ContDiffOn ℝ ∞ r U)
    (m : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 < q → q ≤ 1 → ∀ w ∈ K,
      ‖blownJet m (fun y => r y.2 • (slowSum a h f y - f 0 y.2)) (q, w)‖ ≤
        C * q ^ (2 * h) := by
  classical
  let R : Chart → ℝ := fun y => r y.2
  have hR : ContDiffOn ℝ ∞ R (univ ×ˢ U) :=
    hr.comp contDiffOn_snd (fun y hy => hy.2)
  have hc : IsCompact (({1} : Set ℝ) ×ˢ K) := isCompact_singleton.prod hK
  have hcU : ({1} : Set ℝ) ×ˢ K ⊆ univ ×ˢ U := fun _ hy => ⟨mem_univ _, hKU hy.2⟩
  choose A hA hAb using fun i => compact_jet_bound (isOpen_univ.prod hU) hR hc hcU i
  choose B hB hBb using fun i => normalized_correction_bound hh hf hK ha i
  let C := (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * A i * B (m - i)) + 1
  have hsum : 0 ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * A i * B (m - i) := by
    apply Finset.sum_nonneg
    intro i hi
    have hAi := zero_le_one.trans (hA i)
    have hBi := (hB (m - i)).le
    positivity
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro q hq hq1 w hw
  let F : Chart → V := fun y => slowSum a h f y - f 0 y.2
  have hFs {y : Chart} (hy : 0 < y.1) : ContDiffAt ℝ ∞ F y :=
    (slowSum_smoothAt ha.strictMono hf h hy).sub (((hf 0).comp contDiff_snd).contDiffAt)
  have hFc : ContDiffOn ℝ ∞ (F ∘ scaleMap q) (Ioi 0 ×ˢ U) := by
    intro y hy
    apply ContDiffAt.contDiffWithinAt
    exact (hFs (mul_pos hq hy.1)).comp y (scaleMap q).contDiff.contDiffAt
  have hRp : ContDiffOn ℝ ∞ R (Ioi 0 ×ˢ U) := hR.mono (prod_mono (subset_univ _) Subset.rfl)
  have hpoint : ((1 : ℝ), w) ∈ Ioi 0 ×ˢ U := ⟨by norm_num, hKU hw⟩
  have hb := norm_smul_jet_le_on (isOpen_Ioi.prod hU) hRp hFc hpoint m
  change ‖iteratedFDeriv ℝ m (fun y => R y • (F ∘ scaleMap q) y) (1, w)‖ ≤ _
  refine hb.trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (m + 1), ((m.choose i : ℝ) * A i * B (m - i)) * q ^ (2 * h) := by
      apply Finset.sum_le_sum
      intro i hi
      have hAi : ‖iteratedFDeriv ℝ i R (1, w)‖ ≤ A i := hAb i (1, w) ⟨rfl, hw⟩
      have hBi : ‖iteratedFDeriv ℝ (m - i) (F ∘ scaleMap q) (1, w)‖ ≤
          B (m - i) * q ^ (2 * h) := hBb (m - i) q hq hq1 w hw
      have hAi0 := zero_le_one.trans (hA i)
      refine (mul_le_mul (mul_le_mul_of_nonneg_left hAi (by positivity)) hBi
        (norm_nonneg _) (by positivity)).trans_eq ?_
      ring
    _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * A i * B (m - i)) * q ^ (2 * h) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ C * q ^ (2 * h) := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
      (Real.rpow_nonneg hq.le _)

/-- Normalized swirl, given by `Real.sqrt (2 * y.2.1) / C * slowSum a h d.phi y`. -/
noncomputable def normalizedSwirl (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients)
    (y : Chart) : ℝ := Real.sqrt (2 * y.2.1) / C * slowSum a h d.phi y

/-- Leading swirl, given by `Real.sqrt (2 * w.1) / C * d.phi 0 w`. -/
noncomputable def leadingSwirl (C : ℝ) (d : Coefficients) (w : Inner) : ℝ :=
  Real.sqrt (2 * w.1) / C * d.phi 0 w

/-- Both normalized tangential components have the claimed O(q^(2h))
correction on every fixed active annulus, in every fixed blown-up jet. -/
theorem normalized_tangential_bounds {a : ℕ → ℕ} {h C lo hi : ℝ}
    (hh : 0 < h) (hlo : 0 < lo) {d : Coefficients} (hd : SmoothCoefficients d)
    (ha : AdmissibleScales h (coefficientBundle C d) (innerBox lo hi) a) (m : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ q : ℝ, 0 < q → q ≤ 1 → ∀ w ∈ innerBox lo hi,
      ‖blownJet m (fun y => normalizedSwirl a h C d y - leadingSwirl C d y.2) (q, w)‖ ≤
        B * q ^ (2 * h) ∧
      ‖blownJet m (fun y => slowSum a h d.axial y - d.axial 0 y.2) (q, w)‖ ≤
        B * q ^ (2 * h) := by
  have hphi : AdmissibleScales h d.phi (innerBox lo hi) a := admissible_component hd ha 6
  have hax : AdmissibleScales h d.axial (innerBox lo hi) a := admissible_component hd ha 5
  have hU : IsOpen {w : Inner | 0 < w.1} := isOpen_lt continuous_const continuous_fst
  have hr : ContDiffOn ℝ ∞ (fun w : Inner => Real.sqrt (2 * w.1) / C) {w | 0 < w.1} := by
    intro w hw
    exact (((contDiffAt_const.mul contDiffAt_fst).sqrt
      (ne_of_gt (mul_pos (by norm_num) hw))).div_const C).contDiffWithinAt
  have hKU : innerBox lo hi ⊆ {w : Inner | 0 < w.1} := fun _ hw => hlo.trans_le hw.1.1
  obtain ⟨A, hA, hAb⟩ := normalized_correction_smul_inner hh hd.phi
    (innerBox_isCompact lo hi) hU hKU hphi hr m
  obtain ⟨B, hB, hBb⟩ := normalized_correction_bound hh hd.axial (innerBox_isCompact lo hi) hax m
  refine ⟨A + B, add_pos hA hB, fun q hq hq1 w hw => ⟨?_, ?_⟩⟩
  · have heq : (fun y => normalizedSwirl a h C d y - leadingSwirl C d y.2) =
        (fun y => (Real.sqrt (2 * y.2.1) / C) • (slowSum a h d.phi y - d.phi 0 y.2)) := by
      funext y
      simp only [normalizedSwirl, leadingSwirl, smul_eq_mul, mul_sub]
    rw [heq]
    exact (hAb q hq hq1 w hw).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hB.le) (Real.rpow_nonneg hq.le _))
  · exact (hBb q hq hq1 w hw).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left hA.le) (Real.rpow_nonneg hq.le _))

end NormalizedTangential

section PhysicalIdentification

theorem baseVelocity_angularMoment {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d)
    (C : ℝ) {t : ℝ} (ht : t < 1) (x : ProblemStatement.Space) :
    -x 1 * baseVelocity a h C d (t, x) 0 + x 0 * baseVelocity a h C d (t, x) 1 =
      (2 * AxisymmetricFields.radialEnergy x) * C⁻¹ *
        physicalProfile a h (-CoordinateAlgebra.A h - 1 / 2) d.phi
          (AxisymmetricFields.profilePoint t x) := by
  have hH : DifferentiableAt ℝ (streamFactor a h C d) (AxisymmetricFields.profilePoint t x) :=
    (physicalProfile_smoothAt ha hh hh1 (bundleComponent_smooth hd C 0)
      (-CoordinateAlgebra.A h) ht).differentiableAt (by simp)
  have hK : DifferentiableAt ℝ (swirlPotential a h C d) (AxisymmetricFields.profilePoint t x) :=
    (physicalProfile_smoothAt ha hh hh1 (bundleComponent_smooth hd C 1)
      (1 / 2 - CoordinateAlgebra.A h) ht).differentiableAt (by simp)
  rw [baseVelocity, AxisymmetricFields.velocity_zero _ _ _ _ hH hK,
    AxisymmetricFields.velocity_one _ _ _ _ hH hK,
    partialS_swirlPotential ha hh hh1 hd C ht]
  unfold AxisymmetricFields.radialEnergy
  ring

/-- `normalizedSwirl` is the actual q^A-normalized tangential velocity:
the displayed Cartesian angular momentum is r times q^(-A) times that value.
The identity includes the axis without division by r. -/
theorem angularMoment_eq_normalizedSwirl {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d)
    (C : ℝ) {t : ℝ} (ht : t < 1) (x : ProblemStatement.Space) :
    -x 1 * baseVelocity a h C d (t, x) 0 + x 0 * baseVelocity a h C d (t, x) 1 =
      Real.sqrt (2 * AxisymmetricFields.radialEnergy x) *
        (cartesianChart h (t, x)).1 ^ (-CoordinateAlgebra.A h) *
          normalizedSwirl a h C d (cartesianChart h (t, x)) := by
  rw [baseVelocity_angularMoment ha hh hh1 hd C ht]
  let p := AxisymmetricFields.profilePoint t x
  let q := (physicalChart h p).1
  let s := AxisymmetricFields.radialEnergy x
  let v := slowSum a h d.phi (physicalChart h p)
  have hq : 0 < q := physicalChart_positive hh hh1 ht
  have hs : 0 ≤ 2 * s := mul_nonneg (by norm_num) (AxisymmetricFields.radialEnergy_nonneg x)
  have hsqrt : Real.sqrt (2 * s) ^ 2 = 2 * s := Real.sq_sqrt hs
  change (2 * s) * C⁻¹ * (q ^ (-CoordinateAlgebra.A h - 1 / 2) * v) =
    Real.sqrt (2 * s) * q ^ (-CoordinateAlgebra.A h) *
      (Real.sqrt (2 * (s / q)) / C * v)
  symm
  calc
    _ = Real.sqrt (2 * s) ^ 2 * C⁻¹ *
        (q ^ (-CoordinateAlgebra.A h) / q ^ (1 / 2 : ℝ)) * v := by
      rw [show 2 * (s / q) = (2 * s) / q by ring, Real.sqrt_div hs q,
        Real.sqrt_eq_rpow q]
      ring
    _ = _ := by
      rw [hsqrt, Real.rpow_sub hq]
      ring

/-- Smooth fixed inner weights, including reciprocal annular weights on
compact subsets where they are smooth, preserve the proved tensor estimate.
This is an interior weighted statement; it does not presume the edge bounds. -/
theorem normalized_stress_weighted_compact {a : ℕ → ℕ} {h C : ℝ}
    (hh : 0 < h) {d : Coefficients} (hd : SmoothCoefficients d)
    {K U : Set Inner} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (ha : AdmissibleScales h (coefficientBundle C d) K a)
    {r : Inner → ℝ} (hr : ContDiffOn ℝ ∞ r U) (m : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ q : ℝ, 0 < q → q ≤ 1 → ∀ w ∈ K,
      ‖blownJet m (fun y => r y.2 * (slowSum a h d.stressTheta y - d.stressTheta 0 y.2))
        (q, w)‖ ≤ B * q ^ h ∧
      ‖blownJet m (fun y => r y.2 * (slowSum a h d.stressAxial y - d.stressAxial 0 y.2))
        (q, w)‖ ≤ B * q ^ h := by
  have htheta : AdmissibleScales h d.stressTheta K a := admissible_component hd ha 3
  have haxial : AdmissibleScales h d.stressAxial K a := admissible_component hd ha 4
  obtain ⟨A, hA, hAb⟩ := normalized_correction_smul_inner hh hd.stressTheta hK hU hKU htheta hr m
  obtain ⟨B, hB, hBb⟩ := normalized_correction_smul_inner hh hd.stressAxial hK hU hKU haxial hr m
  refine ⟨A + B, add_pos hA hB, fun q hq hq1 w hw => ?_⟩
  have hp : q ^ (2 * h) ≤ q ^ h := Real.rpow_le_rpow_of_exponent_ge hq hq1 (by linarith)
  refine ⟨(hAb q hq hq1 w hw).trans ?_, (hBb q hq hq1 w hw).trans ?_⟩
  · exact (mul_le_mul_of_nonneg_left hp hA.le).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB.le) (Real.rpow_nonneg hq.le _))
  · exact (mul_le_mul_of_nonneg_left hp hB.le).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA.le) (Real.rpow_nonneg hq.le _))

end PhysicalIdentification

section FixedPrefixes

/-- The same cutoff plateau works for every derivative of a fixed prefix.
The estimate itself retains the derivative-dependent power loss. -/
theorem uncut_fixed_prefix_bound {a : ℕ → ℕ} {h : ℝ} (hh : 0 < h)
    {f : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j)) {K : Set Inner}
    (ha : AdmissibleScales h f K a) (J : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ m, m ≤ J + 3 →
      ∀ q : ℝ, 0 < q → q < δ → ∀ w ∈ K,
        ‖iteratedFDeriv ℝ m (fun y => slowSum a h f y - uncutPrefix h f J y) (q, w)‖ ≤
          (1 / 2 : ℝ) ^ J * q ^ (h * (J + 1) - m) := by
  obtain ⟨δ, hδ, hprefix⟩ := cutPrefix_eventually_uncut a h f J
  refine ⟨min δ 1, lt_min hδ (by norm_num), min_le_right _ _, ?_⟩
  intro m hm q hq hsmall w hw
  have hq1 : q ≤ 1 := (hsmall.trans_le (min_le_right _ _)).le
  have hp := hprefix (q, w) (by simpa only [abs_of_pos hq] using
    (hsmall.trans_le (min_le_left _ _)))
  have he : (fun y => slowSum a h f y - cutPrefix a h f J y) =ᶠ[𝓝 (q, w)]
      (fun y => slowSum a h f y - uncutPrefix h f J y) :=
    hp.mono (fun y hy => congrArg (fun z => slowSum a h f y - z) hy)
  rw [← (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq he m).self_of_nhds]
  exact ordinary_tail_bound hh hf ha hq hq1 hw J m hm

/-- A fixed prefix has a growing, finite remainder order. This interface
permits one common truncation across finitely many field components and
leading powers. It still does not call a fixed tail flat to all orders. -/
theorem powered_fixed_prefix_bound {a : ℕ → ℕ} {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j)) (lo hi b : ℝ)
    (ha : AdmissibleScales h f (innerBox lo hi) a) (J M : ℕ) (hMJ : M ≤ J + 3) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ m ≤ M, ∀ p : Chart, p.1 < 1 →
      (physicalChart h p).1 < δ → (physicalChart h p).2.1 ∈ Icc lo hi →
      ‖iteratedFDeriv ℝ m
        (fun y => physicalProfile a h b f y - physicalUncutPrefix h b f J y) p‖ ≤
          C * (physicalChart h p).1 ^ (h * (J + 1) + b - 2 * M) := by
  obtain ⟨δ, hδ, hδ1, hb⟩ := uncut_fixed_prefix_bound hh hf ha J
  apply powered_physical_tail_of_chart_bound hh hh1 hf lo hi b ha.strictMono J M
    (h * (J + 1) + b - 2 * M) ((1 / 2 : ℝ) ^ J) δ (by positivity) hδ
  intro m hm q hq hsmall w hw
  refine (hb m (hm.trans hMJ) q hq hsmall w hw).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_ge hq (hsmall.le.trans hδ1)
  have hmR : (m : ℝ) ≤ M := by exact_mod_cast hm
  linarith

end FixedPrefixes

end NavierStokes.SlowBorelBase

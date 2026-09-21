/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Truncation.ChainRule
import LeanPool.CoarseGraining.Homogenization.Sobolev.Truncation.WeakGradientLimit
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Convergence
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.WeakDerivSmoothing
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.SmoothRepresentative
import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.BasicLemmas
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Approx -/

namespace Homogenization

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-!
# The C¹ chain rule for `H¹` via mollification

`hasWeakGradientOn_comp_of_deriv_bounded`: for `u ∈ H¹(U)` and `G` of class `C¹`
with `|G'| ≤ M`, the composite `G ∘ u` has weak gradient `G'(u) · ∇u`.
-/

/-! ### One-sided smooth approximators `G_δ → (·−c)₊` -/

/-- Smooth step: `0` for `t ≤ c+δ`, `1` for `t ≥ c+2δ`, in `[0,1]`. -/
noncomputable def gStep (c δ t : ℝ) : ℝ := Real.smoothTransition ((t - c) / δ - 1)

/-- One-sided smooth approximant to `(·−c)₊`, an antiderivative of `gStep`. -/
noncomputable def GApprox (c δ t : ℝ) : ℝ := ∫ s in c..t, gStep c δ s

theorem gStep_contDiff (c δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (gStep c δ) :=
  Real.smoothTransition.contDiff.comp
    (((contDiff_id.sub contDiff_const).div_const δ).sub contDiff_const)

theorem gStep_continuous (c δ : ℝ) : Continuous (gStep c δ) := (gStep_contDiff c δ).continuous

theorem gStep_nonneg (c δ t : ℝ) : 0 ≤ gStep c δ t := Real.smoothTransition.nonneg _

theorem gStep_le_one (c δ t : ℝ) : gStep c δ t ≤ 1 := Real.smoothTransition.le_one _

theorem gStep_eq_zero {c δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ c + δ) : gStep c δ t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  rw [sub_nonpos, div_le_one hδ]; linarith

theorem gStep_eq_one {c δ t : ℝ} (hδ : 0 < δ) (ht : c + 2 * δ ≤ t) : gStep c δ t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_sub_iff_add_le, le_div_iff₀ hδ]; linarith

theorem gStep_intervalIntegrable (c δ a b : ℝ) :
    IntervalIntegrable (gStep c δ) volume a b := (gStep_continuous c δ).intervalIntegrable a b

theorem GApprox_hasDerivAt (c δ t : ℝ) : HasDerivAt (GApprox c δ) (gStep c δ t) t :=
  intervalIntegral.integral_hasDerivAt_right (gStep_intervalIntegrable c δ c t)
    ((gStep_continuous c δ).stronglyMeasurableAtFilter _ _)
    (gStep_continuous c δ).continuousAt

theorem deriv_GApprox (c δ : ℝ) : deriv (GApprox c δ) = gStep c δ := by
  funext t; exact (GApprox_hasDerivAt c δ t).deriv

theorem GApprox_contDiff_one (c δ : ℝ) : ContDiff ℝ 1 (GApprox c δ) := by
  rw [contDiff_one_iff_deriv]
  exact ⟨fun t => (GApprox_hasDerivAt c δ t).differentiableAt,
    by rw [deriv_GApprox]; exact gStep_continuous c δ⟩

theorem abs_deriv_GApprox_le (c δ t : ℝ) : |deriv (GApprox c δ) t| ≤ 1 := by
  rw [deriv_GApprox, abs_of_nonneg (gStep_nonneg c δ t)]; exact gStep_le_one c δ t

/-- The pointwise derivative limit: `gStep c δₙ t → 𝟙_{t > c}` for every `t`. -/
theorem tendsto_gStep {c : ℝ} {δ : ℕ → ℝ} (hδpos : ∀ n, 0 < δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => gStep c (δ n) t) atTop (𝓝 (if c < t then 1 else 0)) := by
  by_cases hct : c < t
  · rw [if_pos hct]
    have hev : ∀ᶠ n in atTop, gStep c (δ n) t = 1 := by
      have : ∀ᶠ n in atTop, δ n < (t - c) / 2 :=
        (tendsto_order.1 hδ).2 _ (by linarith)
      filter_upwards [this] with n hn
      exact gStep_eq_one (hδpos n) (by linarith)
    exact Tendsto.congr' (hev.mono fun n hn => hn.symm) tendsto_const_nhds
  · rw [if_neg hct]
    have hev : ∀ᶠ n in atTop, gStep c (δ n) t = 0 :=
      Filter.Eventually.of_forall fun n =>
        gStep_eq_zero (hδpos n) (by push Not at hct; linarith [(hδpos n).le])
    exact Tendsto.congr' (hev.mono fun n hn => hn.symm) tendsto_const_nhds

theorem abs_GApprox_le (c δ t : ℝ) : |GApprox c δ t| ≤ |t - c| := by
  rw [GApprox, ← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ => ?_)).trans
    (one_mul _).le
  rw [Real.norm_eq_abs, abs_of_nonneg (gStep_nonneg c δ s)]
  exact gStep_le_one c δ s

/-- Uniform closeness of the approximant to the positive part. -/
theorem abs_GApprox_sub_le {c δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    |GApprox c δ t - max (t - c) 0| ≤ 2 * δ := by
  rcases le_or_gt t c with htc | htc
  · -- `t ≤ c`: the approximant vanishes.
    have hzero : GApprox c δ t = 0 := by
      rw [GApprox, ← intervalIntegral.integral_zero (a := c) (b := t) (μ := volume)]
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_ge htc] at hs
      exact gStep_eq_zero hδ (by linarith [hs.2, (le_of_lt hδ)])
    rw [hzero, max_eq_right (by linarith), sub_zero, abs_zero]; linarith
  · -- `c < t`: split the integral at `c + 2δ`.
    rw [max_eq_left (by linarith)]
    have hle : GApprox c δ t ≤ t - c := by
      rw [GApprox]
      calc ∫ s in c..t, gStep c δ s ≤ ∫ _ in c..t, (1 : ℝ) :=
            intervalIntegral.integral_mono_on htc.le (gStep_intervalIntegrable c δ c t)
              (intervalIntegrable_const) (fun s _ => gStep_le_one c δ s)
        _ = t - c := by rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    have hge : t - c - 2 * δ ≤ GApprox c δ t := by
      by_cases h2 : c + 2 * δ ≤ t
      · have hsplit : GApprox c δ t
            = (∫ s in c..(c + 2 * δ), gStep c δ s) + ∫ s in (c + 2 * δ)..t, gStep c δ s := by
          rw [GApprox]
          exact (intervalIntegral.integral_add_adjacent_intervals
            (gStep_intervalIntegrable c δ _ _) (gStep_intervalIntegrable c δ _ _)).symm
        have htail : (∫ s in (c + 2 * δ)..t, gStep c δ s) = t - (c + 2 * δ) := by
          rw [show (∫ s in (c + 2 * δ)..t, gStep c δ s) = ∫ _ in (c + 2 * δ)..t, (1 : ℝ) from
            intervalIntegral.integral_congr
              (fun s hs => by
                rw [Set.uIcc_of_le h2] at hs
                exact gStep_eq_one hδ hs.1),
            intervalIntegral.integral_const, smul_eq_mul, mul_one]
        have hhead : 0 ≤ ∫ s in c..(c + 2 * δ), gStep c δ s :=
          intervalIntegral.integral_nonneg (by linarith) (fun s _ => gStep_nonneg c δ s)
        rw [hsplit, htail]; linarith
      · push Not at h2
        have hpos : 0 ≤ GApprox c δ t :=
          intervalIntegral.integral_nonneg htc.le (fun s _ => gStep_nonneg c δ s)
        linarith
    rw [abs_le]; constructor <;> linarith

end Homogenization

namespace Homogenization

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-- **C¹ chain rule (weak-gradient form).** -/
theorem hasWeakGradientOn_comp_of_deriv_bounded
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M) (hderiv : ∀ t, |deriv G t| ≤ M) :
    HasWeakGradientOn U (fun x => G (u.toFun x))
      (fun x i => deriv G (u.toFun x) * u.grad x i) := by
  -- `G` is `M`-Lipschitz and differentiable.
  have hGdiff : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hGlip : LipschitzWith M.toNNReal G := lipschitzWith_of_abs_deriv_le hM hGdiff hderiv
  have : IsFiniteMeasure (volumeMeasureOn U) := hU.isBoundedDomain.isFiniteMeasure_restrict_volume
  -- Empty domain: the pairing identity is trivial.
  rcases U.eq_empty_or_nonempty with hempty | hne
  · subst hempty
    intro i φ _ _ _
    simp
  -- A closed ball inside `U`.
  obtain ⟨x0, hx0U⟩ := hne
  obtain ⟨r0, hr0, hball0⟩ := Metric.isOpen_iff.mp hU.isOpen x0 hx0U
  set r : ℝ := r0 / 2 with hr_def
  have hr : 0 < r := by positivity
  have hball : Metric.closedBall x0 r ⊆ U := by
    refine (Metric.closedBall_subset_ball ?_).trans hball0
    rw [hr_def]; linarith
  set ρ : Vec d → ℝ := unitConvexApproxKernel (d := d) with hρ_def
  have hρ : IsConvexApproxKernel ρ := isConvexApproxKernel_unitConvexApproxKernel
  -- Scale sequence shifted to land in `(0,1)`.
  set e : ℕ → ℝ := fun n => unitConvexApproxScale (n + 1) with he_def
  have he_pos : ∀ n, 0 < e n := by
    intro n; simp only [he_def, unitConvexApproxScale]; positivity
  have he_lt : ∀ n, e n < 1 := by
    intro n
    simp only [he_def, unitConvexApproxScale]
    rw [div_lt_one (by positivity)]
    have : (0:ℝ) ≤ (n:ℝ) := by positivity
    push_cast; linarith
  have he_le : ∀ n, e n ≤ 1 := fun n => (he_lt n).le
  have he_tendsto : Tendsto e atTop (𝓝 0) :=
    tendsto_unitConvexApproxScale_zero.comp (tendsto_add_atTop_nat 1)
  -- The globally-smooth representative sequence.
  set w : ℕ → Vec d → ℝ := fun n => convexApproxSmoothRepresentative U ρ u.toFun x0 r (e n)
    with hw_def
  have hw_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (w n) := fun n =>
    contDiff_convexApproxSmoothRepresentative hU.isOpen.measurableSet hρ one_le_two u.memL2 hr
      (he_pos n)
  -- On `U`, `w n` agrees with the smoothing sequence `unitConvexApproxSequence u (n+1)`.
  have hw_eq : ∀ n, ∀ x ∈ U, w n x = unitConvexApproxSequence u.toFun x0 r (n + 1) x := by
    intro n x hx
    simpa [hw_def, unitConvexApproxSequence, he_def] using
      convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem hU hρ hx hball hr
        (he_pos n) (he_lt n)
  -- Local integrability of `u` and its gradient (for the smoothing weak-gradient identity).
  have huLoc : LocallyIntegrableOn u.toFun U volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (u.memL2.locallyIntegrable one_le_two)
  have hDuLoc : ∀ j : Fin d, LocallyIntegrableOn (fun x => u.grad x j) U volume :=
    fun j => locallyIntegrableOn_of_locallyIntegrable_restrict
      ((u.gradMemL2 j).locallyIntegrable one_le_two)
  -- Transport of a weak partial derivative along agreement on `U`.
  have htransport : ∀ (i : Fin d) (f g h : Vec d → ℝ), (∀ x ∈ U, f x = g x) →
      HasWeakPartialDerivOn U i g h → HasWeakPartialDerivOn U i f h := by
    intro i f g h hfg hg φ hφ hφc hφs
    rw [← hg φ hφ hφc hφs]
    exact setIntegral_congr_fun hU.isOpen.measurableSet
      (fun x hx => by rw [hfg x hx])
  intro i
  -- Per-`n` classical `i`-partial of `w n` and the composite gradient.
  set Dwn : ℕ → Vec d → ℝ := fun n x => (fderiv ℝ (w n) x) (basisVec i) with hDwn_def
  set un : ℕ → Vec d → ℝ := fun n x => G (w n x) with hun_def
  set gn : ℕ → Vec d → ℝ := fun n x => deriv G (w n x) * Dwn n x with hgn_def
  set smi : ℕ → Vec d → ℝ :=
    fun n => convexApproxSmoothing ρ (fun y => u.grad y i) x0 r (e n) with hsmi_def
  -- Each `G ∘ w n` is `C¹`, with weak `i`-partial `gn n`.
  have hweak_n : ∀ n, HasWeakPartialDerivOn U i (un n) (gn n) := by
    intro n
    have hGwn : ContDiff ℝ 1 (fun x => G (w n x)) :=
      hG.comp ((hw_smooth n).of_le (by norm_num))
    have h := (HasWeakGradientOn.of_contDiff (U := U) hGwn) i
    have heq : (fun x => (fderiv ℝ (fun y => G (w n y)) x) (basisVec i)) = gn n := by
      funext x
      rw [fderiv_comp_basisVec hGdiff.differentiableAt
        ((hw_smooth n).differentiable (by norm_num)).differentiableAt]
    rwa [heq] at h
  -- The `(1−ε)` bridge: classical `∂ᵢ(w n) =ᵃᵉ (1−e n)·smoothing(∂ᵢu)` on `U`.
  have hbridge : ∀ n, Dwn n =ᵐ[volumeMeasureOn U] (fun x => (1 - e n) * smi n x) := by
    intro n
    have hDwn_weak : HasWeakPartialDerivOn U i (w n) (Dwn n) :=
      (HasWeakGradientOn.of_contDiff (U := U) ((hw_smooth n).of_le (by norm_num))) i
    have hsm_weak0 :=
      (HasWeakGradientOn.convexApproxSmoothing hU huLoc hDuLoc u.hasWeakGradient hρ hball hr.le
        (he_pos n).le (he_lt n)) i
    -- transport smoothing's weak partial to `w n` (they agree on `U`).
    have hsm_weak : HasWeakPartialDerivOn U i (w n) (fun x => (1 - e n) * smi n x) := by
      refine htransport i (w n) (convexApproxSmoothing ρ u.toFun x0 r (e n)) _ ?_ hsm_weak0
      intro x hx
      simpa [hw_def, unitConvexApproxSequence, he_def] using hw_eq n x hx
    -- local integrability of both candidate derivatives.
    have hDwn_cont : Continuous (Dwn n) := by
      simpa [hDwn_def] using
        ((hw_smooth n).continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hDwn_loc : LocallyIntegrableOn (Dwn n) U volume :=
      hDwn_cont.continuousOn.locallyIntegrableOn hU.isOpen.measurableSet
    have hsm_loc : LocallyIntegrableOn (fun x => (1 - e n) * smi n x) U volume := by
      have hrepr_smooth : ContDiff ℝ (⊤ : ℕ∞)
          (convexApproxSmoothRepresentative U ρ (fun y => u.grad y i) x0 r (e n)) :=
        contDiff_convexApproxSmoothRepresentative hU.isOpen.measurableSet hρ one_le_two
          (u.gradMemL2 i) hr (he_pos n)
      have hbase : ContinuousOn
          (fun x => (1 - e n) *
            convexApproxSmoothRepresentative U ρ (fun y => u.grad y i) x0 r (e n) x) U :=
        (continuous_const.mul hrepr_smooth.continuous).continuousOn
      have hcont : ContinuousOn (fun x => (1 - e n) * smi n x) U := by
        refine hbase.congr ?_
        intro x hx
        simp only [hsmi_def]
        rw [convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem hU hρ hx hball hr
          (he_pos n) (he_lt n)]
      exact hcont.locallyIntegrableOn hU.isOpen.measurableSet
    exact HasWeakPartialDerivOn.ae_eq hU.isOpen hDwn_loc hsm_loc hDwn_weak hsm_weak
  -- Numeric facts.
  have h2t : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h12 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  -- `L²` membership of a `C¹`-image.
  have hG0lip : LipschitzWith M.toNNReal (fun t => G t - G 0) := by
    intro a b; simpa [edist_sub_right] using hGlip a b
  have hcompL2 : ∀ v : Vec d → ℝ, MemLp v 2 (volumeMeasureOn U) →
      MemLp (fun x => G (v x)) 2 (volumeMeasureOn U) := by
    intro v hv
    have h1 : MemLp (fun x => G (v x) - G 0) 2 (volumeMeasureOn U) :=
      hG0lip.comp_memLp (by simp) hv
    have h2 : MemLp (fun _ : Vec d => G 0) 2 (volumeMeasureOn U) := memLp_const _
    refine (h1.add h2).ae_eq ?_
    filter_upwards with x
    simp
  -- Continuity of `deriv G` and measurability of composites.
  have hderivG_cont : Continuous (deriv G) := hG.continuous_deriv (by norm_num)
  have haesm_comp : ∀ v : Vec d → ℝ, AEStronglyMeasurable v (volumeMeasureOn U) →
      AEStronglyMeasurable (fun x => deriv G (v x)) (volumeMeasureOn U) :=
    fun v hv => hderivG_cont.comp_aestronglyMeasurable hv
  -- `L²` membership of `w n`, `Dwn n`, `un n`, `gn n`, and the two targets.
  have hwn_memL2 : ∀ n, MemLp (w n) 2 (volumeMeasureOn U) := by
    intro n
    have hsm := memLpOn_convexApproxSmoothing hU hρ h12 h2t u.memL2 hball hr (he_pos n) (he_lt n)
    refine hsm.ae_eq ?_
    filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
    simpa [unitConvexApproxSequence, he_def, hρ_def] using (hw_eq n x hx).symm
  have hun_memL2 : ∀ n, MemLp (un n) 2 (volumeMeasureOn U) :=
    fun n => hcompL2 (w n) (hwn_memL2 n)
  have hsmi_memL2 : ∀ n, MemLp (smi n) 2 (volumeMeasureOn U) := by
    intro n
    simpa [hsmi_def] using
      memLpOn_convexApproxSmoothing hU hρ h12 h2t (u.gradMemL2 i) hball hr (he_pos n) (he_lt n)
  have hDwn_memL2 : ∀ n, MemLp (Dwn n) 2 (volumeMeasureOn U) := fun n =>
    ((hsmi_memL2 n).const_mul (1 - e n)).ae_eq (hbridge n).symm
  have hgn_memL2 : ∀ n, MemLp (gn n) 2 (volumeMeasureOn U) := by
    intro n
    refine MemLp.of_le ((hDwn_memL2 n).const_mul M) ?_ ?_
    · exact (haesm_comp (w n) (hw_smooth n).continuous.aestronglyMeasurable).mul
        (hDwn_memL2 n).1
    · filter_upwards with x
      simp only [hgn_def, norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (by rw [abs_of_nonneg hM]; exact hderiv (w n x)) (abs_nonneg _)
  have hGu_memL2 : MemLp (fun x => G (u.toFun x)) 2 (volumeMeasureOn U) :=
    hcompL2 u.toFun u.memL2
  have hg_memL2 : MemLp (fun x => deriv G (u.toFun x) * u.grad x i) 2 (volumeMeasureOn U) := by
    refine MemLp.of_le ((u.gradMemL2 i).const_mul M) ?_ ?_
    · exact (haesm_comp u.toFun u.memL2.1).mul (u.gradMemL2 i).1
    · filter_upwards with x
      simp only [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (by rw [abs_of_nonneg hM]; exact hderiv (u.toFun x)) (abs_nonneg _)
  -- L² convergence `w n → u` (function side).
  have hwu_L2 : Tendsto
      (fun n => eLpNorm (fun x => w n x - u.toFun x) 2 (volumeMeasureOn U)) atTop (𝓝 0) := by
    have hbase :=
      (tendsto_eLpNorm_sub_zero_unitConvexApproxSequence_of_memLpOn hU h12 h2t u.memL2 hball hr).comp
        (tendsto_add_atTop_nat 1)
    refine hbase.congr (fun n => ?_)
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
    rw [hw_eq n x hx]
  -- a.e.-convergent subsequence.
  obtain ⟨σ, hσ_mono, hσ_ae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      (fun n => (hw_smooth n).continuous.aestronglyMeasurable) u.memL2.1
      hwu_L2).exists_seq_tendsto_ae
  -- L² convergence of the smoothing of `∂ᵢu`.
  have hsmi_conv : Tendsto
      (fun n => eLpNorm (fun x => smi n x - u.grad x i) 2 (volumeMeasureOn U)) atTop (𝓝 0) := by
    have hbase :=
      (tendsto_eLpNorm_sub_zero_unitConvexApproxSequence_of_memLpOn hU h12 h2t (u.gradMemL2 i)
        hball hr).comp (tendsto_add_atTop_nat 1)
    refine hbase.congr (fun n => ?_)
    apply eLpNorm_congr_ae
    filter_upwards with x
    simp only [hsmi_def, unitConvexApproxSequence, he_def, hρ_def]
  -- **Goal 1.** `∂ᵢ(w n) → ∂ᵢu` in `L²` via the `(1−e n)` bridge.
  set C : ℝ≥0∞ := eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn U) with hC
  have hC_ne_top : C ≠ ⊤ := (u.gradMemL2 i).eLpNorm_ne_top
  have hDwn_conv : Tendsto
      (fun n => eLpNorm (fun x => Dwn n x - u.grad x i) 2 (volumeMeasureOn U)) atTop (𝓝 0) := by
    have hbound : ∀ n,
        eLpNorm (fun x => Dwn n x - u.grad x i) 2 (volumeMeasureOn U)
          ≤ ENNReal.ofReal (1 - e n) *
              eLpNorm (fun x => smi n x - u.grad x i) 2 (volumeMeasureOn U)
            + ENNReal.ofReal (e n) * C := by
      intro n
      have hae : (fun x => Dwn n x - u.grad x i) =ᵐ[volumeMeasureOn U]
          (fun x => (1 - e n) * (smi n x - u.grad x i) - e n * u.grad x i) := by
        filter_upwards [hbridge n] with x hx
        rw [hx]; ring
      have hmeasA : AEStronglyMeasurable
          (fun x => (1 - e n) * (smi n x - u.grad x i)) (volumeMeasureOn U) :=
        ((hsmi_memL2 n).1.sub (u.gradMemL2 i).1).const_mul _
      have hmeasB : AEStronglyMeasurable
          (fun x => e n * u.grad x i) (volumeMeasureOn U) := (u.gradMemL2 i).1.const_mul _
      have hA : eLpNorm (fun x => (1 - e n) * (smi n x - u.grad x i)) 2 (volumeMeasureOn U)
          = ENNReal.ofReal (1 - e n) *
              eLpNorm (fun x => smi n x - u.grad x i) 2 (volumeMeasureOn U) := by
        rw [show (fun x => (1 - e n) * (smi n x - u.grad x i))
              = (1 - e n) • (fun x => smi n x - u.grad x i) from rfl,
          eLpNorm_const_smul, Real.enorm_eq_ofReal (by linarith [he_le n])]
      have hB : eLpNorm (fun x => e n * u.grad x i) 2 (volumeMeasureOn U)
          = ENNReal.ofReal (e n) * C := by
        rw [show (fun x => e n * u.grad x i) = e n • (fun x => u.grad x i) from rfl,
          eLpNorm_const_smul, Real.enorm_eq_ofReal (he_pos n).le, hC]
      rw [eLpNorm_congr_ae hae]
      calc eLpNorm
              (fun x => (1 - e n) * (smi n x - u.grad x i) - e n * u.grad x i) 2 (volumeMeasureOn U)
          ≤ eLpNorm (fun x => (1 - e n) * (smi n x - u.grad x i)) 2 (volumeMeasureOn U)
              + eLpNorm (fun x => e n * u.grad x i) 2 (volumeMeasureOn U) :=
            eLpNorm_sub_le hmeasA hmeasB h12
        _ = _ := by rw [hA, hB]
    have hofR1 : Tendsto (fun n => ENNReal.ofReal (1 - e n)) atTop (𝓝 1) := by
      have : Tendsto (fun n => (1 : ℝ) - e n) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.sub he_tendsto
      simpa using! (ENNReal.continuous_ofReal.tendsto 1).comp this
    have hofR0 : Tendsto (fun n => ENNReal.ofReal (e n)) atTop (𝓝 0) := by
      simpa using! (ENNReal.continuous_ofReal.tendsto 0).comp he_tendsto
    have hrhs : Tendsto
        (fun n => ENNReal.ofReal (1 - e n) *
            eLpNorm (fun x => smi n x - u.grad x i) 2 (volumeMeasureOn U)
          + ENNReal.ofReal (e n) * C) atTop (𝓝 0) := by
      have h1 := ENNReal.Tendsto.mul hofR1 (Or.inl one_ne_zero) hsmi_conv (Or.inr (by norm_num))
      have h2 := ENNReal.Tendsto.mul hofR0 (Or.inr hC_ne_top) tendsto_const_nhds
        (Or.inr (by norm_num))
      simpa using h1.add h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs
      (fun n => zero_le) hbound
  -- Function-side convergence `G ∘ w (σ k) → G ∘ u` in `L²`.
  have hun_conv : Tendsto
      (fun k => eLpNorm (fun x => un (σ k) x - G (u.toFun x)) 2 (volumeMeasureOn U))
      atTop (𝓝 0) := by
    have hle : ∀ k, eLpNorm (fun x => un (σ k) x - G (u.toFun x)) 2 (volumeMeasureOn U)
        ≤ ENNReal.ofReal M *
            eLpNorm (fun x => w (σ k) x - u.toFun x) 2 (volumeMeasureOn U) := by
      intro k
      simpa [hun_def] using eLpNorm_comp_sub_le_of_lipschitz hM hGlip (w (σ k)) u.toFun
    have hrhs : Tendsto
        (fun k => ENNReal.ofReal M *
          eLpNorm (fun x => w (σ k) x - u.toFun x) 2 (volumeMeasureOn U)) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal M)
        (hwu_L2.comp hσ_mono.tendsto_atTop) (Or.inr ENNReal.ofReal_ne_top)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs
      (fun k => zero_le) hle
  -- Gradient-side convergence `gn (σ k) → G'(u)·∂ᵢu` in `L²` (Term A + Term B).
  have hgn_conv : Tendsto
      (fun k => eLpNorm (fun x => gn (σ k) x - deriv G (u.toFun x) * u.grad x i) 2
        (volumeMeasureOn U)) atTop (𝓝 0) := by
    -- Term B via dominated convergence.
    set TB : ℕ → Vec d → ℝ :=
      fun k x => (deriv G (w (σ k) x) - deriv G (u.toFun x)) * u.grad x i with hTB_def
    have hTB_conv : Tendsto
        (fun k => eLpNorm (fun x => TB k x) 2 (volumeMeasureOn U)) atTop (𝓝 0) := by
      have hmeasTB : ∀ k, AEStronglyMeasurable (TB k) (volumeMeasureOn U) := fun k =>
        ((haesm_comp (w (σ k)) (hw_smooth (σ k)).continuous.aestronglyMeasurable).sub
          (haesm_comp u.toFun u.memL2.1)).mul (u.gradMemL2 i).1
      have hdom : MemLp (fun x => ‖(2 * M) * u.grad x i‖) 2 (volumeMeasureOn U) :=
        ((u.gradMemL2 i).const_mul (2 * M)).norm
      have hbnd : ∀ k, ∀ᵐ x ∂(volumeMeasureOn U), ‖TB k x‖ ≤ ‖(2 * M) * u.grad x i‖ := by
        intro k
        filter_upwards with x
        rw [hTB_def, norm_mul, norm_mul]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * M)]
        calc |deriv G (w (σ k) x) - deriv G (u.toFun x)|
            ≤ |deriv G (w (σ k) x)| + |deriv G (u.toFun x)| := abs_sub _ _
          _ ≤ M + M := add_le_add (hderiv _) (hderiv _)
          _ = 2 * M := by ring
      have hae : ∀ᵐ x ∂(volumeMeasureOn U), Tendsto (fun k => TB k x) atTop (𝓝 0) := by
        filter_upwards [hσ_ae] with x hx
        have h1 : Tendsto (fun k => deriv G (w (σ k) x)) atTop (𝓝 (deriv G (u.toFun x))) :=
          (hderivG_cont.tendsto _).comp hx
        have h2 := (h1.sub (tendsto_const_nhds (x := deriv G (u.toFun x)))).mul_const (u.grad x i)
        simpa [hTB_def] using h2
      have := tendsto_eLpNorm_two_of_tendsto_ae_of_dominated hmeasTB
        (memLp_const 0) hdom hbnd (by filter_upwards [hae] with x hx using by simpa using hx)
      simpa using this
    -- Term A dominated by `M · ‖∂ᵢw(σk) − ∂ᵢu‖`.
    have hTA_le : ∀ k,
        eLpNorm (fun x => deriv G (w (σ k) x) * (Dwn (σ k) x - u.grad x i)) 2 (volumeMeasureOn U)
          ≤ ENNReal.ofReal M *
              eLpNorm (fun x => Dwn (σ k) x - u.grad x i) 2 (volumeMeasureOn U) := by
      intro k
      have hpt : ∀ x, ‖deriv G (w (σ k) x) * (Dwn (σ k) x - u.grad x i)‖
          ≤ ‖M • (Dwn (σ k) x - u.grad x i)‖ := by
        intro x
        rw [norm_smul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs M]
        exact mul_le_mul_of_nonneg_right
          (by rw [abs_of_nonneg hM]; exact hderiv (w (σ k) x)) (abs_nonneg _)
      calc eLpNorm (fun x => deriv G (w (σ k) x) * (Dwn (σ k) x - u.grad x i)) 2 (volumeMeasureOn U)
          ≤ eLpNorm (fun x => M • (Dwn (σ k) x - u.grad x i)) 2 (volumeMeasureOn U) :=
            eLpNorm_mono hpt
        _ = ENNReal.ofReal M *
              eLpNorm (fun x => Dwn (σ k) x - u.grad x i) 2 (volumeMeasureOn U) := by
            rw [show (fun x => M • (Dwn (σ k) x - u.grad x i))
                  = M • (fun x => Dwn (σ k) x - u.grad x i) from rfl, eLpNorm_const_smul]
            simp [Real.enorm_eq_ofReal hM]
    have hTA_conv : Tendsto
        (fun k => eLpNorm (fun x => deriv G (w (σ k) x) * (Dwn (σ k) x - u.grad x i)) 2
          (volumeMeasureOn U)) atTop (𝓝 0) := by
      have hrhs : Tendsto
          (fun k => ENNReal.ofReal M *
            eLpNorm (fun x => Dwn (σ k) x - u.grad x i) 2 (volumeMeasureOn U)) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal M)
          (hDwn_conv.comp hσ_mono.tendsto_atTop) (Or.inr ENNReal.ofReal_ne_top)
        simpa using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs
        (fun k => zero_le) hTA_le
    -- Combine: the gradient difference splits into Term A plus Term B.
    have hsplit : ∀ k, eLpNorm (fun x => gn (σ k) x - deriv G (u.toFun x) * u.grad x i) 2
          (volumeMeasureOn U)
        ≤ eLpNorm (fun x => deriv G (w (σ k) x) * (Dwn (σ k) x - u.grad x i)) 2 (volumeMeasureOn U)
          + eLpNorm (fun x => TB k x) 2 (volumeMeasureOn U) := by
      intro k
      have heq : (fun x => gn (σ k) x - deriv G (u.toFun x) * u.grad x i)
          = (fun x => deriv G (w (σ k) x) * (Dwn (σ k) x - u.grad x i) + TB k x) := by
        funext x; simp only [hgn_def, hTB_def]; ring
      rw [heq]
      refine eLpNorm_add_le ?_ ?_ h12
      · exact ((haesm_comp (w (σ k)) (hw_smooth (σ k)).continuous.aestronglyMeasurable).mul
          ((hDwn_memL2 (σ k)).1.sub (u.gradMemL2 i).1))
      · exact ((haesm_comp (w (σ k)) (hw_smooth (σ k)).continuous.aestronglyMeasurable).sub
          (haesm_comp u.toFun u.memL2.1)).mul (u.gradMemL2 i).1
    have hsum : Tendsto
        (fun k => eLpNorm (fun x => deriv G (w (σ k) x) * (Dwn (σ k) x - u.grad x i)) 2
            (volumeMeasureOn U)
          + eLpNorm (fun x => TB k x) 2 (volumeMeasureOn U)) atTop (𝓝 0) := by
      simpa using hTA_conv.add hTB_conv
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun k => zero_le) hsplit
  -- Apply the L²-limit closure keystone along the subsequence.
  exact hasWeakPartialDerivOn_of_tendsto_L2
    hGu_memL2 hg_memL2 (fun k => hun_memL2 (σ k)) (fun k => hgn_memL2 (σ k))
    (fun k => hweak_n (σ k)) hun_conv hgn_conv

end Homogenization

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.BorelExtension
public import LeanPool.NavierStokesAndEuler.ForMathlib.FiniteDimensionalBumps
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Jointly smooth Taylor–Borel extension of spatially smooth jets

There is one cutoff scale per Taylor degree. Its finite list of constraints
includes all joint derivatives and all spatial localizations up to that degree.
This gives joint smoothness without imposing global bounds on the input jets.
-/

@[expose] public section

attribute [local instance] FiniteDimensional.hasContDiffBump


noncomputable section

open Set Filter Function Metric
open scoped Topology ContDiff BigOperators

namespace NavierStokes.SpatialBorelExtension

variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem nat_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)

/-- Spatial bump, bundling `rIn`, `rOut`, `rIn_pos`, `rIn_lt_rOut`. -/
def spatialBump (m : ℕ) : ContDiffBump (0 : X) where
  rIn := (m : ℝ) + 1
  rOut := (m : ℝ) + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- Spatial cutoff, given by `(spatialBump (X := X) m : X → ℝ)`. -/
def spatialCutoff (m : ℕ) : X → ℝ := (spatialBump (X := X) m : X → ℝ)

theorem spatialCutoff_contDiff (m : ℕ) : ContDiff ℝ ∞ (spatialCutoff (X := X) m) :=
  (spatialBump (X := X) m).contDiff

theorem spatialCutoff_eventually_one (m : ℕ) {x : X} (hx : ‖x‖ < (m : ℝ) + 1) :
    spatialCutoff m =ᶠ[𝓝 x] (fun _ => 1) := by
  apply (spatialBump (X := X) m).eventuallyEq_one_of_mem_ball
  simpa only [mem_ball, dist_zero_right, spatialBump] using hx

theorem spatialCutoff_zero (m : ℕ) {x : X} (hx : (m : ℝ) + 2 ≤ ‖x‖) :
    spatialCutoff m x = 0 := by
  apply (spatialBump (X := X) m).zero_of_le_dist
  simpa only [dist_zero_right, spatialBump] using hx

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
theorem exists_spatial_plateau (x : X) : ∃ m : ℕ, ‖x‖ < (m : ℝ) + 1 := by
  obtain ⟨m, hm⟩ := exists_nat_gt ‖x‖
  exact ⟨m, by linarith⟩

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
theorem exists_compact_spatial_plateau {K : Set X} (hK : IsCompact K) :
    ∃ m : ℕ, ∀ x ∈ K, ‖x‖ < (m : ℝ) + 1 := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (continuous_id.continuousOn :
    ContinuousOn (fun x : X => x) K)
  obtain ⟨m, hm⟩ := exists_nat_gt C
  exact ⟨m, fun x hx => lt_of_le_of_lt (hC x hx) (by linarith)⟩

/-- Term, given by `BorelExtension.term b j (a z.2) z.1`. -/
def term (b : ℝ) (j : ℕ) (a : X → V) (z : ℝ × X) : V :=
  BorelExtension.term b j (a z.2) z.1

/-- Localized term, given by `spatialCutoff m z.2 • term b j a z`. -/
def localizedTerm (m : ℕ) (b : ℝ) (j : ℕ) (a : X → V) (z : ℝ × X) : V :=
  spatialCutoff m z.2 • term b j a z

/-- Template, given by `localizedTerm m 1 j a`. -/
def template (m j : ℕ) (a : X → V) : ℝ × X → V := localizedTerm m 1 j a

omit [FiniteDimensional ℝ X] in
theorem term_contDiff {a : X → V} (ha : ContDiff ℝ ∞ a) (b : ℝ) (j : ℕ) :
    ContDiff ℝ ∞ (term b j a) := by
  exact ((SmoothCutoffs.scaledCutoff_contDiff b).comp contDiff_fst).smul
    (((contDiff_fst.pow j).div_const _).smul (ha.comp contDiff_snd))

theorem localizedTerm_contDiff {a : X → V} (ha : ContDiff ℝ ∞ a)
    (m : ℕ) (b : ℝ) (j : ℕ) : ContDiff ℝ ∞ (localizedTerm m b j a) :=
  ((spatialCutoff_contDiff m).comp contDiff_snd).smul (term_contDiff ha b j)

theorem template_contDiff {a : X → V} (ha : ContDiff ℝ ∞ a) (m j : ℕ) :
    ContDiff ℝ ∞ (template m j a) := localizedTerm_contDiff ha m 1 j

theorem template_hasCompactSupport (m j : ℕ) (a : X → V) :
    HasCompactSupport (template m j a) := by
  have hs : support (template m j a) ⊆
      Icc (-1 : ℝ) 1 ×ˢ closedBall (0 : X) ((m : ℝ) + 2) := by
    intro z hz
    have ht : |z.1| < 1 := by
      apply lt_of_not_ge
      intro ht
      apply hz
      simp only [template, localizedTerm, term, BorelExtension.term, one_mul,
        SmoothCutoffs.cutoff_zero_of_one_le_abs ht, zero_smul, smul_zero]
    have hx : ‖z.2‖ < (m : ℝ) + 2 := by
      apply lt_of_not_ge
      intro hx
      apply hz
      simp only [template, localizedTerm, spatialCutoff_zero m hx, zero_smul]
    exact ⟨abs_le.mp ht.le, by simpa only [mem_closedBall, dist_zero_right] using hx.le⟩
  apply (isCompact_Icc.prod (isCompact_closedBall (0 : X) ((m : ℝ) + 2))).of_isClosed_subset
    isClosed_closure
  exact closure_minimal hs (isClosed_Icc.prod isClosed_closedBall)

/-- Time scale, given by `(b • ContinuousLinearMap.fst ℝ ℝ X).prod (ContinuousLinearMap.snd ℝ ℝ
X)`. -/
def timeScale (b : ℝ) : (ℝ × X) →L[ℝ] (ℝ × X) :=
  (b • ContinuousLinearMap.fst ℝ ℝ X).prod (ContinuousLinearMap.snd ℝ ℝ X)

omit [FiniteDimensional ℝ X] in
@[simp] theorem timeScale_apply (b : ℝ) (z : ℝ × X) : timeScale b z = (b * z.1, z.2) := rfl

omit [FiniteDimensional ℝ X] in
theorem norm_timeScale_le {b : ℝ} (hb : 1 ≤ b) : ‖timeScale (X := X) b‖ ≤ b := by
  have hb0 : 0 ≤ b := le_trans zero_le_one hb
  apply ContinuousLinearMap.opNorm_le_bound _ hb0
  intro z
  simp only [timeScale_apply, Prod.norm_def, norm_mul, Real.norm_of_nonneg hb0]
  apply max_le
  · exact mul_le_mul_of_nonneg_left (le_max_left _ _) hb0
  · exact (le_max_right _ _).trans
      (le_mul_of_one_le_left (le_trans (norm_nonneg z.1) (le_max_left _ _)) hb)

theorem localizedTerm_eq_scaled {b : ℝ} (hb : b ≠ 0) (m j : ℕ) (a : X → V) :
    localizedTerm m b j a = (b ^ j)⁻¹ • (template m j a ∘ timeScale b) := by
  funext z
  simp only [localizedTerm, template, term, BorelExtension.term, BorelExtension.monomial,
    Pi.smul_apply, comp_apply, timeScale_apply, one_mul, smul_smul, mul_pow]
  congr 1
  field_simp

theorem exists_template_bound {a : X → V} (ha : ContDiff ℝ ∞ a) (m j k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ × X, ‖iteratedFDeriv ℝ k (template m j a) z‖ ≤ C := by
  obtain ⟨C, hC⟩ := ((template_hasCompactSupport m j a).iteratedFDeriv k).exists_bound_of_continuous
    ((template_contDiff ha m j).continuous_iteratedFDeriv (nat_le_infty k))
  exact ⟨max C 0, le_max_right _ _, fun z => (hC z).trans (le_max_left _ _)⟩

/-- Template bound, given by `Classical.choose (exists_template_bound ha m j k)`. -/
def templateBound {a : X → V} (ha : ContDiff ℝ ∞ a) (m j k : ℕ) : ℝ :=
  Classical.choose (exists_template_bound ha m j k)

theorem templateBound_nonneg {a : X → V} (ha : ContDiff ℝ ∞ a) (m j k : ℕ) :
    0 ≤ templateBound ha m j k := (Classical.choose_spec (exists_template_bound ha m j k)).1

theorem template_deriv_le {a : X → V} (ha : ContDiff ℝ ∞ a) (m j k : ℕ) (z : ℝ × X) :
    ‖iteratedFDeriv ℝ k (template m j a) z‖ ≤ templateBound ha m j k :=
  (Classical.choose_spec (exists_template_bound ha m j k)).2 z

theorem localizedTerm_deriv_bound {a : X → V} (ha : ContDiff ℝ ∞ a)
    {b : ℝ} (hb : 1 ≤ b) (m j k : ℕ) (z : ℝ × X) :
    ‖iteratedFDeriv ℝ k (localizedTerm m b j a) z‖ ≤
      (b ^ k / b ^ j) * templateBound ha m j k := by
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have ht := template_contDiff ha m j
  have hc : ContDiff ℝ (k : WithTop ℕ∞) (template m j a ∘ timeScale b) :=
    ht.comp_continuousLinearMap.of_le (nat_le_infty k)
  rw [localizedTerm_eq_scaled (ne_of_gt hbpos),
    iteratedFDeriv_const_smul_apply hc.contDiffAt]
  rw [norm_smul ((b ^ j)⁻¹ : ℝ) (iteratedFDeriv ℝ k (template m j a ∘ timeScale b) z),
    Real.norm_of_nonneg (by positivity : 0 ≤ (b ^ j)⁻¹),
    (timeScale b).iteratedFDeriv_comp_right ht z (nat_le_infty k)]
  have hcomp :
      ‖(iteratedFDeriv ℝ k (template m j a) (timeScale b z)).compContinuousLinearMap
        (fun _ => timeScale b)‖ ≤ templateBound ha m j k * b ^ k := by
    calc
      _ ≤ ‖iteratedFDeriv ℝ k (template m j a) (timeScale b z)‖ *
          ∏ _ : Fin k, ‖timeScale (X := X) b‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖iteratedFDeriv ℝ k (template m j a) (timeScale b z)‖ *
          ‖timeScale (X := X) b‖ ^ k := by simp
      _ ≤ templateBound ha m j k * b ^ k :=
        mul_le_mul (template_deriv_le ha m j k (timeScale b z))
          (pow_le_pow_left₀ (norm_nonneg _) (norm_timeScale_le hb) k)
          (by positivity) (templateBound_nonneg ha m j k)
  calc
    _ ≤ (b ^ j)⁻¹ * (templateBound ha m j k * b ^ k) :=
      mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ = (b ^ k / b ^ j) * templateBound ha m j k := by ring

section Family

variable (a : ℕ → X → V) (ha : ∀ j, ContDiff ℝ ∞ (a j))

/-- Each degree controls finitely many spatial windows and derivative orders. -/
def boundSum (j : ℕ) : ℝ :=
  ∑ m ∈ Finset.range j, ∑ k ∈ Finset.range j, templateBound (ha j) m j k

theorem boundSum_nonneg (j : ℕ) : 0 ≤ boundSum a ha j :=
  Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun k _ => templateBound_nonneg (ha j) m j k

theorem templateBound_le_boundSum {m j k : ℕ} (hm : m < j) (hk : k < j) :
    templateBound (ha j) m j k ≤ boundSum a ha j := by
  apply (Finset.single_le_sum (fun i _ => templateBound_nonneg (ha j) m j i)
    (Finset.mem_range.mpr hk)).trans
  exact Finset.single_le_sum
    (fun i _ => Finset.sum_nonneg fun l _ => templateBound_nonneg (ha j) i j l)
    (Finset.mem_range.mpr hm)

/-- Local scale, given by `Classical.choose (exists_nat_gt ((2 : ℝ) ^ j * boundSum a ha j))`. -/
def localScale (j : ℕ) : ℕ := Classical.choose (exists_nat_gt ((2 : ℝ) ^ j * boundSum a ha j))

theorem localScale_bound (j : ℕ) : (2 : ℝ) ^ j * boundSum a ha j < localScale a ha j :=
  Classical.choose_spec (exists_nat_gt ((2 : ℝ) ^ j * boundSum a ha j))

/-- The scale depends on the degree and the whole input family, never on the
evaluation point or on the derivative order subsequently requested. -/
def scale : ℕ → ℕ := DiagonalScale.doublingEnvelope (localScale a ha)

theorem scale_pos (j : ℕ) : 0 < scale a ha j :=
  DiagonalScale.doublingEnvelope_pos (localScale a ha) j

theorem scale_ge_one (j : ℕ) : (1 : ℝ) ≤ scale a ha j := by
  exact_mod_cast scale_pos a ha j

theorem scale_strictMono : StrictMono (scale a ha) :=
  DiagonalScale.doublingEnvelope_strictMono (localScale a ha)

theorem scale_doubling (j : ℕ) : 2 * scale a ha j ≤ scale a ha (j + 1) :=
  DiagonalScale.doublingEnvelope_growth (localScale a ha) j

theorem boundSum_le_scale (j : ℕ) : boundSum a ha j ≤ (1 / 2 : ℝ) ^ j * scale a ha j := by
  have hs : (2 : ℝ) ^ j * boundSum a ha j ≤ scale a ha j :=
    (localScale_bound a ha j).le.trans
      (by exact_mod_cast DiagonalScale.doublingEnvelope_ge (localScale a ha) j)
  calc
    boundSum a ha j = (1 / 2 : ℝ) ^ j * ((2 : ℝ) ^ j * boundSum a ha j) := by
      rw [← mul_assoc, ← mul_pow]
      norm_num
    _ ≤ (1 / 2 : ℝ) ^ j * scale a ha j := mul_le_mul_of_nonneg_left hs (by positivity)

private theorem power_ratio_le {b : ℝ} (hb : 1 ≤ b) {k j : ℕ} (hkj : k < j) :
    b ^ k / b ^ j ≤ 1 / b := by
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  apply (le_div_iff₀ hbpos).2
  calc
    (b ^ k / b ^ j) * b = b ^ (k + 1) / b ^ j := by rw [pow_succ]; ring
    _ ≤ 1 := (div_le_one (pow_pos hbpos j)).2
      (pow_le_pow_right₀ hb (Nat.succ_le_of_lt hkj))

theorem localized_derivative_tail_bound {m j k : ℕ} (hm : m < j) (hk : k < j) (z : ℝ × X) :
    ‖iteratedFDeriv ℝ k (localizedTerm m (scale a ha j) j (a j)) z‖ ≤ (1 / 2 : ℝ) ^ j := by
  have hb := scale_ge_one a ha j
  have hbpos : (0 : ℝ) < scale a ha j := lt_of_lt_of_le zero_lt_one hb
  calc
    _ ≤ (((scale a ha j : ℝ) ^ k) / (scale a ha j : ℝ) ^ j) * templateBound (ha j) m j k :=
      localizedTerm_deriv_bound (ha j) hb m j k z
    _ ≤ (1 / (scale a ha j : ℝ)) * boundSum a ha j :=
      mul_le_mul (power_ratio_le hb hk) (templateBound_le_boundSum a ha hm hk)
        (templateBound_nonneg (ha j) m j k) (by positivity)
    _ ≤ (1 / (scale a ha j : ℝ)) * ((1 / 2 : ℝ) ^ j * scale a ha j) :=
      mul_le_mul_of_nonneg_left (boundSum_le_scale a ha j) (by positivity)
    _ = (1 / 2 : ℝ) ^ j := by field_simp

/-- Majorant, with branches according to `m < j ∧ k < j`. -/
def majorant (m k j : ℕ) : ℝ :=
  if m < j ∧ k < j then (1 / 2 : ℝ) ^ j
  else (((scale a ha j : ℝ) ^ k) / (scale a ha j : ℝ) ^ j) * templateBound (ha j) m j k

theorem majorant_summable (m k : ℕ) : Summable (majorant a ha m k) := by
  apply summable_geometric_two.congr_cofinite
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_gt_atTop (max m k)] with j hj
  have hm : m < j := lt_of_le_of_lt (le_max_left _ _) hj
  have hk : k < j := lt_of_le_of_lt (le_max_right _ _) hj
  have hmk : m < j ∧ k < j := ⟨hm, hk⟩
  simp only [majorant, ite_eq_left hmk]

theorem localized_derivative_bound (m k j : ℕ) (z : ℝ × X) :
    ‖iteratedFDeriv ℝ k (localizedTerm m (scale a ha j) j (a j)) z‖ ≤ majorant a ha m k j := by
  unfold majorant
  split_ifs with h
  · exact localized_derivative_tail_bound a ha h.1 h.2 z
  · exact localizedTerm_deriv_bound (ha j) (scale_ge_one a ha j) m j k z

theorem term_eventuallyEq_localized (m : ℕ) {z : ℝ × X}
    (hz : ‖z.2‖ < (m : ℝ) + 1) (b : ℝ) (j : ℕ) (f : X → V) :
    term b j f =ᶠ[𝓝 z] localizedTerm m b j f := by
  have heq := (spatialCutoff_eventually_one m hz).comp_tendsto continuous_snd.continuousAt
  filter_upwards [heq] with w hw
  change spatialCutoff m w.2 = 1 at hw
  simp only [localizedTerm, hw, one_smul]

omit [FiniteDimensional ℝ X] in
private theorem iteratedFDeriv_eq_of_eventuallyEq {f g : (ℝ × X) → V} {z : ℝ × X}
    (h : f =ᶠ[𝓝 z] g) (k : ℕ) : iteratedFDeriv ℝ k f z = iteratedFDeriv ℝ k g z := by
  have h' : f =ᶠ[𝓝[univ] z] g := h.filter_mono nhdsWithin_le_nhds
  simpa only [iteratedFDerivWithin_univ] using
    h'.iteratedFDerivWithin_eq (𝕜 := ℝ) h.eq_of_nhds k

/-- On any fixed compact spatial set, every joint derivative has a uniform
geometric tail bound. Time is unrestricted in this estimate. -/
theorem derivative_tail_bound_on_compact {K : Set X} (hK : IsCompact K) (k : ℕ) :
    ∀ᶠ j in atTop, ∀ z : ℝ × X, z.2 ∈ K →
      ‖iteratedFDeriv ℝ k (term (scale a ha j) j (a j)) z‖ ≤ (1 / 2 : ℝ) ^ j := by
  obtain ⟨m, hm⟩ := exists_compact_spatial_plateau hK
  filter_upwards [eventually_gt_atTop (max m k)] with j hj z hz
  rw [iteratedFDeriv_eq_of_eventuallyEq
    (term_eventuallyEq_localized m (hm z.2 hz) (scale a ha j) j (a j)) k]
  exact localized_derivative_tail_bound a ha
    (lt_of_le_of_lt (le_max_left _ _) hj) (lt_of_le_of_lt (le_max_right _ _) hj) z

section Complete

variable [CompleteSpace V]

/-- Extension, given by `∑' j : ℕ, term (scale a ha j) j (a j) z`. -/
def extension (z : ℝ × X) : V := ∑' j : ℕ, term (scale a ha j) j (a j) z

/-- Localized extension, given by `∑' j : ℕ, localizedTerm m (scale a ha j) j (a j) z`. -/
def localizedExtension (m : ℕ) (z : ℝ × X) : V :=
  ∑' j : ℕ, localizedTerm m (scale a ha j) j (a j) z

/-- The defining series converges at every point; its `tsum` is never being
used merely as the default value of a divergent series. -/
theorem terms_summable (z : ℝ × X) :
    Summable (fun j : ℕ => term (scale a ha j) j (a j) z) := by
  apply Summable.of_norm_bounded_eventually_nat summable_geometric_two
  have hK : IsCompact ({z.2} : Set X) := isCompact_singleton
  filter_upwards [derivative_tail_bound_on_compact a ha hK 0] with j hj
  simpa only [norm_iteratedFDeriv_zero] using hj z (mem_singleton z.2)

theorem localized_derivatives_summable (m k : ℕ) (z : ℝ × X) :
    Summable (fun j : ℕ => iteratedFDeriv ℝ k (localizedTerm m (scale a ha j) j (a j)) z) :=
  .of_norm_bounded (majorant_summable a ha m k)
    (fun j => localized_derivative_bound a ha m k j z)

theorem localizedExtension_contDiff (m : ℕ) : ContDiff ℝ ∞ (localizedExtension a ha m) :=
  contDiff_tsum (N := ⊤) (fun j => localizedTerm_contDiff (ha j) m (scale a ha j) j)
    (fun k _ => majorant_summable a ha m k)
    (fun k j z _ => localized_derivative_bound a ha m k j z)

theorem localizedExtension_iteratedFDeriv (m k : ℕ) (z : ℝ × X) :
    iteratedFDeriv ℝ k (localizedExtension a ha m) z =
      ∑' j : ℕ, iteratedFDeriv ℝ k (localizedTerm m (scale a ha j) j (a j)) z :=
  iteratedFDeriv_tsum_apply (N := ⊤)
    (fun j => localizedTerm_contDiff (ha j) m (scale a ha j) j)
    (fun l _ => majorant_summable a ha m l)
    (fun l j w _ => localized_derivative_bound a ha m l j w) le_top z

omit [CompleteSpace V] in
theorem extension_eq_localized (m : ℕ) (z : ℝ × X) (hz : spatialCutoff m z.2 = 1) :
    extension a ha z = localizedExtension a ha m z := by
  apply tsum_congr
  intro j
  simp only [localizedTerm, hz, one_smul]

omit [CompleteSpace V] in
theorem extension_eventuallyEq_localized (m : ℕ) {z : ℝ × X}
    (hz : ‖z.2‖ < (m : ℝ) + 1) :
    extension a ha =ᶠ[𝓝 z] localizedExtension a ha m := by
  have heq := (spatialCutoff_eventually_one m hz).comp_tendsto continuous_snd.continuousAt
  filter_upwards [heq] with w hw
  exact extension_eq_localized a ha m w hw

/-- Joint smoothness in time and space follows from local equality with an
all-order uniformly convergent smooth series. -/
theorem extension_contDiff : ContDiff ℝ ∞ (extension a ha) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  obtain ⟨m, hm⟩ := exists_spatial_plateau z.2
  exact (localizedExtension_contDiff a ha m).contDiffAt.congr_of_eventuallyEq
    (extension_eventuallyEq_localized a ha m hm)

theorem derivatives_summable (k : ℕ) (z : ℝ × X) :
    Summable (fun j : ℕ => iteratedFDeriv ℝ k (term (scale a ha j) j (a j)) z) := by
  obtain ⟨m, hm⟩ := exists_spatial_plateau z.2
  apply (localized_derivatives_summable a ha m k z).congr
  intro j
  exact (iteratedFDeriv_eq_of_eventuallyEq
    (term_eventuallyEq_localized m hm (scale a ha j) j (a j)) k).symm

theorem extension_iteratedFDeriv (k : ℕ) (z : ℝ × X) :
    iteratedFDeriv ℝ k (extension a ha) z =
      ∑' j : ℕ, iteratedFDeriv ℝ k (term (scale a ha j) j (a j)) z := by
  obtain ⟨m, hm⟩ := exists_spatial_plateau z.2
  rw [iteratedFDeriv_eq_of_eventuallyEq (extension_eventuallyEq_localized a ha m hm) k,
    localizedExtension_iteratedFDeriv]
  apply tsum_congr
  intro j
  exact (iteratedFDeriv_eq_of_eventuallyEq
    (term_eventuallyEq_localized m hm (scale a ha j) j (a j)) k).symm

/-- Uniform convergence of every full derivative series on compact spatial
sets, uniformly over all real times. -/
theorem derivatives_tendstoUniformlyOn_compact {K : Set X} (hK : IsCompact K) (k : ℕ) :
    TendstoUniformlyOn
      (fun N : ℕ => fun z : ℝ × X =>
        ∑ j ∈ Finset.range N, iteratedFDeriv ℝ k (term (scale a ha j) j (a j)) z)
      (iteratedFDeriv ℝ k (extension a ha)) atTop (univ ×ˢ K) := by
  rw [show iteratedFDeriv ℝ k (extension a ha) =
    (fun z => ∑' j : ℕ, iteratedFDeriv ℝ k (term (scale a ha j) j (a j)) z)
    from funext (extension_iteratedFDeriv a ha k)]
  apply tendstoUniformlyOn_tsum_nat_eventually summable_geometric_two
  filter_upwards [derivative_tail_bound_on_compact a ha hK k] with j hj z hz
  exact hj z hz.2

omit [FiniteDimensional ℝ X] [CompleteSpace V] in
theorem time_iteratedDeriv {f : (ℝ × X) → V} (hf : ContDiff ℝ ∞ f)
    (k : ℕ) (t : ℝ) (x : X) :
    iteratedDeriv k (fun s : ℝ => f (s, x)) t =
      iteratedFDeriv ℝ k f (t, x) (fun _ : Fin k => (1, (0 : X))) := by
  let L : ℝ →L[ℝ] (ℝ × X) := ContinuousLinearMap.inl ℝ ℝ X
  let g : (ℝ × X) → V := fun z => f (z + (0, x))
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have heq : (fun s : ℝ => f (s, x)) = g ∘ L := by
    funext s
    simp [g, L]
  rw [heq, iteratedDeriv_eq_iteratedFDeriv,
    L.iteratedFDeriv_comp_right hg t (nat_le_infty k)]
  change iteratedFDeriv ℝ k (fun z => f (z + (0, x))) (t, 0)
    (fun _ : Fin k => (1, (0 : X))) = _
  rw [iteratedFDeriv_comp_add_right]
  simp

/-- All prescribed time jets hold as equalities of smooth spatial functions. -/
theorem extension_time_jets (k : ℕ) (x : X) :
    iteratedDeriv k (fun t : ℝ => extension a ha (t, x)) 0 = a k x := by
  rw [time_iteratedDeriv (extension_contDiff a ha), extension_iteratedFDeriv,
    ContinuousMultilinearMap.tsum_eval (derivatives_summable a ha k (0, x))]
  have hterm (j : ℕ) :
      iteratedFDeriv ℝ k (term (scale a ha j) j (a j)) (0, x)
        (fun _ : Fin k => (1, (0 : X))) = if k = j then a j x else 0 := by
    rw [← time_iteratedDeriv (term_contDiff (ha j) (scale a ha j) j)]
    exact BorelExtension.iteratedDeriv_term_zero (scale a ha j) j k (a j x)
  simp only [hterm]
  rw [tsum_eq_single k]
  · simp
  · intro j hj
    simp [Ne.symm hj]

/-- Taking any number of spatial derivatives of the boundary time-jet
function gives the corresponding derivative of the prescribed coefficient. -/
theorem extension_mixed_boundary_jets (k l : ℕ) (x : X) :
    iteratedFDeriv ℝ l (fun y : X =>
      iteratedDeriv k (fun t : ℝ => extension a ha (t, y)) 0) x =
      iteratedFDeriv ℝ l (a k) x := by
  rw [show (fun y : X => iteratedDeriv k (fun t : ℝ => extension a ha (t, y)) 0) = a k
    from funext (extension_time_jets a ha k)]

omit [CompleteSpace V] in
theorem extension_eq_series (z : ℝ × X) :
    extension a ha z = ∑' j : ℕ,
      (SmoothCutoffs.cutoff ((scale a ha j : ℝ) * z.1) *
        (z.1 ^ j / (j.factorial : ℝ))) • a j z.2 := by
  simp only [extension, term, BorelExtension.term, BorelExtension.monomial, smul_smul]

omit [CompleteSpace V] in
theorem extension_zero_of_one_le_abs {z : ℝ × X} (hz : 1 ≤ |z.1|) : extension a ha z = 0 := by
  calc
    extension a ha z = ∑' _ : ℕ, (0 : V) := by
      apply tsum_congr
      intro j
      have harg : 1 ≤ |(scale a ha j : ℝ) * z.1| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        exact one_le_mul_of_one_le_of_one_le (scale_ge_one a ha j) hz
      simp only [term, BorelExtension.term,
        SmoothCutoffs.cutoff_zero_of_one_le_abs harg, zero_smul]
    _ = 0 := tsum_zero

omit [CompleteSpace V] in
theorem extension_time_support : tsupport (extension a ha) ⊆ Icc (-1 : ℝ) 1 ×ˢ (univ : Set X) := by
  apply closure_minimal _ (isClosed_Icc.prod isClosed_univ)
  intro z hz
  have ht : |z.1| < 1 := lt_of_not_ge fun h => hz (extension_zero_of_one_le_abs a ha h)
  exact ⟨abs_le.mp ht.le, mem_univ _⟩

omit [CompleteSpace V] in
/-- Spatial periods of every coefficient pass to the same actual series. -/
theorem extension_add_period (p : X) (hp : ∀ j x, a j (x + p) = a j x)
    (t : ℝ) (x : X) : extension a ha (t, x + p) = extension a ha (t, x) := by
  apply tsum_congr
  intro j
  simp only [term, hp]

omit [CompleteSpace V] in
/-- A zero spatial slice of every coefficient stays identically zero. -/
theorem extension_zero_of_coefficients_zero {x : X} (hx : ∀ j, a j x = 0) (t : ℝ) :
    extension a ha (t, x) = 0 := by
  simp only [extension, term, BorelExtension.term, BorelExtension.monomial, hx,
    smul_zero, tsum_zero]

/-- Right extension, given by `extension a ha (z.1 - T, z.2)`. -/
def rightExtension (T : ℝ) (z : ℝ × X) : V := extension a ha (z.1 - T, z.2)

theorem rightExtension_contDiff (T : ℝ) : ContDiff ℝ ∞ (rightExtension a ha T) :=
  (extension_contDiff a ha).comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)

theorem rightExtension_time_jets (T : ℝ) (k : ℕ) (x : X) :
    iteratedDeriv k (fun t : ℝ => rightExtension a ha T (t, x)) T = a k x := by
  have h := congrFun (iteratedDeriv_comp_add_const k
    (fun t : ℝ => extension a ha (t, x)) (-T)) T
  simp only [add_neg_cancel] at h
  simpa only [rightExtension, sub_eq_add_neg] using h.trans (extension_time_jets a ha k x)

theorem rightExtension_right_jets (T : ℝ) (k : ℕ) (x : X) :
    iteratedDerivWithin k (fun t : ℝ => rightExtension a ha T (t, x)) (Ici T) T = a k x := by
  have hs : ContDiff ℝ ∞ (fun t : ℝ => rightExtension a ha T (t, x)) :=
    (rightExtension_contDiff a ha T).comp (contDiff_id.prodMk contDiff_const)
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin,
    iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Ici T)
      (hs.of_le (nat_le_infty k)).contDiffAt (mem_Ici.mpr le_rfl)]
  exact rightExtension_time_jets a ha T k x

omit [CompleteSpace V] in
theorem rightExtension_add_period (T : ℝ) (p : X) (hp : ∀ j x, a j (x + p) = a j x)
    (t : ℝ) (x : X) : rightExtension a ha T (t, x + p) = rightExtension a ha T (t, x) :=
  extension_add_period a ha p hp (t - T) x

omit [CompleteSpace V] in
theorem rightExtension_zero_from (T : ℝ) {t : ℝ} (ht : T + 1 ≤ t) (x : X) :
    rightExtension a ha T (t, x) = 0 := by
  apply extension_zero_of_one_le_abs
  exact (show 1 ≤ t - T by linarith).trans (le_abs_self _)

include ha in
/-- Jointly smooth realization for arbitrary smooth spatial coefficients in
a finite-dimensional space, with no global growth restriction. -/
theorem exists_smooth_extension :
    ∃ F : (ℝ × X) → V, ContDiff ℝ ∞ F ∧
      tsupport F ⊆ Icc (-1 : ℝ) 1 ×ˢ (univ : Set X) ∧
      (∀ k : ℕ, ∀ x : X, iteratedDeriv k (fun t : ℝ => F (t, x)) 0 = a k x) :=
  ⟨extension a ha, extension_contDiff a ha, extension_time_support a ha, extension_time_jets a ha⟩

end Complete
end Family

end NavierStokes.SpatialBorelExtension

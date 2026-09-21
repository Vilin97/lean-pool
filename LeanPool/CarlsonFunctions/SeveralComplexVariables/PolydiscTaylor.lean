/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.SeveralComplexVariables.CauchyCoefficients
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.LocallyUniform
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Taylor expansions on polydiscs with separate radii

The multi-index Cauchy series converges throughout its open polydisc, not merely on
the largest inscribed equal-radius ball. Convergence is uniform on smaller closed polydiscs
and locally uniform on the full open polydisc, also after mixed differentiation. Explicit
geometric-tail estimates control the remainder after any finite set of multi-indices.
Scalar Taylor coefficients also define an element of Mathlib's `MvPowerSeries`.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory Metric Set
open scoped Real Topology

namespace CarlsonFunctions.SeveralComplexVariables

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The scalar Taylor series as an existing Mathlib multivariate formal power series. -/
def holomorphicTaylorSeries (f : (Fin d → ℂ) → ℂ) (c : Fin d → ℂ) : MvPowerSeries (Fin d) ℂ :=
  fun m => (∏ i, (m i).factorial : ℂ)⁻¹ * multiIndexDeriv m f c

/-- Formal Taylor coefficients coincide with the integral Cauchy coefficients. -/
theorem coeff_holomorphicTaylorSeries {f : (Fin d → ℂ) → ℂ} {c : Fin d → ℂ}
    {R : Fin d → ℝ} (hR : ∀ i, 0 < R i)
    (hfc : ContinuousOn f (closedPolydiscWithRadii c R))
    (hfa : ∀ z ∈ closedPolydiscWithRadii c R, ∀ i,
      AnalyticAt ℂ (fun v => f (update z i v)) (z i)) (m : Fin d →₀ ℕ) :
    MvPowerSeries.coeff m (holomorphicTaylorSeries f c) = polydiscCauchyCoeffWithRadii f c R m := by
  exact (polydiscCauchyCoeffWithRadii_eq_multiIndexDeriv hR hfc hfa m).symm

/-- The ungrouped multi-index geometric expansion of the Cauchy kernel. -/
theorem hasSum_multiIndex_cauchyKernel {z c h : Fin d → ℂ}
    (hz : ∀ i, z i ≠ c i) (hh : ∀ i, ‖h i‖ < ‖z i - c i‖) :
    HasSum (fun m : Fin d → ℕ => (∏ i, h i ^ m i) * cauchyKernel m c z)
      (∏ i, (z i - (c + h) i)⁻¹) := by
  have hx : ∀ i, ‖h i / (z i - c i)‖ < 1 := by
    intro i
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (sub_ne_zero.mpr (hz i)))]
    exact hh i
  have hs := (hasSum_pi_geometric (fun i => h i / (z i - c i)) hx).mul_right
    (∏ i, (z i - c i)⁻¹)
  have hterm (m : Fin d → ℕ) : (∏ i, h i ^ m i) * cauchyKernel m c z =
      (∏ i, (h i / (z i - c i)) ^ m i) * ∏ i, (z i - c i)⁻¹ := by
    rw [cauchyKernel, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [pow_succ, div_pow, inv_pow]
    field_simp [sub_ne_zero.mpr (hz i)]
  have hconst : (∏ i, (z i - (c + h) i)⁻¹) =
      (∏ i, (1 - h i / (z i - c i))⁻¹) * ∏ i, (z i - c i)⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    have hzi : z i - c i ≠ 0 := sub_ne_zero.mpr (hz i)
    have hzih : z i - (c + h) i ≠ 0 := by
      intro heq
      have he : z i - c i = h i := by
        have H := sub_eq_zero.mp heq
        simp only [Pi.add_apply] at H
        linear_combination H
      exact (hh i).ne (congrArg norm he.symm)
    simp only [Pi.add_apply]
    field_simp [hzi, hzih]
    ring
  simpa only [hterm, hconst] using hs

omit [CompleteSpace E] in
/-- Every higher Cauchy kernel times a continuous function is integrable on its contour. -/
theorem torusIntegrable_cauchyKernel_multi {f : (Fin d → ℂ) → E}
    {c w : Fin d → ℂ} {R : Fin d → ℝ} (hR : ∀ i, 0 < R i)
    (hw : w ∈ polydiscWithRadii c R)
    (hfc : ContinuousOn f (closedPolydiscWithRadii c R)) (m : Fin d → ℕ) :
    TorusIntegrable (fun z => cauchyKernel m w z • f z) c R := by
  have hfθ : ContinuousOn (fun θ => f (torusMap c R θ))
      (Icc (0 : Fin d → ℝ) (fun _ => 2 * π)) :=
    hfc.comp (continuous_torusMapWithRadii c R).continuousOn
      (fun θ _ => torusMap_mem_closedPolydiscWithRadii (fun i => (hR i).le) θ)
  have hk : ContinuousOn (fun θ => cauchyKernel m w (torusMap c R θ))
      (Icc (0 : Fin d → ℝ) (fun _ => 2 * π)) := by
    apply continuousOn_finsetProd
    intro i hi
    apply ContinuousOn.pow
    refine (((continuous_apply i).comp (continuous_torusMapWithRadii c R)).continuousOn.sub
      continuousOn_const).inv₀ (fun θ hθ => ?_)
    exact sub_ne_zero.mpr (cauchyKernel_ne_zero_on_torusWithRadii hR
      (by simpa [dist_eq_norm] using mem_polydiscWithRadii.mp hw i))
  exact (hk.smul hfθ).integrableOn_compact isCompact_Icc

omit [CompleteSpace E] in
private theorem norm_cauchyTaylor_integrand_le {f : (Fin d → ℂ) → E}
    {c h : Fin d → ℂ} {R : Fin d → ℝ} {M : ℝ} (hR : ∀ i, 0 < R i)
    (hM : ∀ z ∈ closedPolydiscWithRadii c R, ‖f z‖ ≤ M)
    (m : Fin d → ℕ) (θ : Fin d → ℝ) :
    ‖(∏ i, h i ^ m i) • cauchyKernel m c (torusMap c R θ) • f (torusMap c R θ)‖ ≤
      (M * ∏ i, (R i)⁻¹) * ∏ i, (‖h i‖ / R i) ^ m i := by
  calc
    _ = (∏ i, ‖h i‖ ^ m i) * (∏ i, (R i)⁻¹ ^ (m i + 1)) * ‖f (torusMap c R θ)‖ := by
      simp only [norm_smul, cauchyKernel, norm_prod, norm_pow, norm_inv,
        torusMap_coord_normWithRadii (fun i => (hR i).le), mul_assoc]
    _ ≤ (∏ i, ‖h i‖ ^ m i) * (∏ i, (R i)⁻¹ ^ (m i + 1)) * M :=
      mul_le_mul_of_nonneg_left
        (hM _ (torusMap_mem_closedPolydiscWithRadii (fun i => (hR i).le) θ))
        (mul_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (norm_nonneg _) _)
          (Finset.prod_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr (hR i).le) _))
    _ = _ := by
      simp only [div_eq_mul_inv, mul_pow, pow_succ, Finset.prod_mul_distrib]
      ring

/-- The full multi-index Taylor expansion on a polydisc with separate radii. The sum
is indexed by all multi-indices, and therefore does not depend on a summation order. -/
theorem hasSum_polydiscTaylor {f : (Fin d → ℂ) → E} {c h : Fin d → ℂ}
    {R : Fin d → ℝ} {M : ℝ} (hR : ∀ i, 0 < R i) (hh : ∀ i, ‖h i‖ < R i)
    (hfc : ContinuousOn f (closedPolydiscWithRadii c R))
    (hfa : ∀ z ∈ closedPolydiscWithRadii c R, ∀ i,
      AnalyticAt ℂ (fun v => f (update z i v)) (z i))
    (hM : ∀ z ∈ closedPolydiscWithRadii c R, ‖f z‖ ≤ M) :
    HasSum (fun m : Fin d → ℕ => (∏ i, h i ^ m i) • polydiscCauchyCoeffWithRadii f c R m)
      (f (c + h)) := by
  let T (m : Fin d → ℕ) (z : Fin d → ℂ) := (∏ i, h i ^ m i) • cauchyKernel m c z • f z
  let a (m : Fin d → ℕ) := (M * ∏ i, (R i)⁻¹) * ∏ i, (‖h i‖ / R i) ^ m i
  have hq : ∀ i, ‖‖h i‖ / R i‖ < 1 := by
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) (hR i).le), div_lt_one (hR i)]
    exact hh i
  have ha : Summable a := (hasSum_pi_geometric (fun i => ‖h i‖ / R i) hq).summable.mul_left _
  have hc : c ∈ polydiscWithRadii c R := mem_polydiscWithRadii.mpr (by simpa using hR)
  have hTi (m : Fin d → ℕ) : TorusIntegrable (T m) c R :=
    (torusIntegrable_cauchyKernel_multi hR hc hfc m).smul (∏ i, h i ^ m i)
  have hs := hasSum_torusIntegral_of_uniform (g := fun z => (∏ i, (z i - (c + h) i)⁻¹) • f z)
    ha hTi (fun m θ => norm_cauchyTaylor_integrand_le hR hM m θ) (fun θ => by
      have hz : ∀ i, torusMap c R θ i ≠ c i := by
        intro i hi
        have H := torusMap_coord_normWithRadii (c := c) (fun i => (hR i).le) θ i
        rw [hi, sub_self, norm_zero] at H
        exact (hR i).ne' H.symm
      have H := hasSum_multiIndex_cauchyKernel (h := h) hz (fun i => by
        rw [torusMap_coord_normWithRadii (fun i => (hR i).le)]; exact hh i)
      simpa only [T, smul_smul, smul_eq_mul] using H.smul_const (f (torusMap c R θ)))
  have hn := hs.const_smul (((2 * π * I : ℂ) ^ d)⁻¹)
  have hterm (m : Fin d → ℕ) : (∏ i, h i ^ m i) • polydiscCauchyCoeffWithRadii f c R m =
      (((2 * π * I : ℂ) ^ d)⁻¹) • torusIntegral (T m) c R := by
    dsimp only [polydiscCauchyCoeffWithRadii, cauchyTransform, T]
    rw [torusIntegral_smul]
    exact smul_comm _ _ _
  rw [polydisc_cauchyWithRadii hR (fun i => by simpa using hh i) hfc hfa] at hn
  simpa only [hterm] using hn

omit [CompleteSpace E] in
/-- A summable geometric majorant for individual Taylor terms on a smaller closed polydisc. -/
theorem norm_polydiscTaylor_term_le {f : (Fin d → ℂ) → E} {c h : Fin d → ℂ}
    {R s : Fin d → ℝ} {M : ℝ} (hR : ∀ i, 0 < R i) (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ closedPolydiscWithRadii c R, ‖f z‖ ≤ M)
    (hh : ∀ i, ‖h i‖ ≤ s i) (m : Fin d → ℕ) :
    ‖(∏ i, h i ^ m i) • polydiscCauchyCoeffWithRadii f c R m‖ ≤
      M * ∏ i, (s i / R i) ^ m i := by
  calc
    _ ≤ (∏ i, ‖h i‖ ^ m i) * (M * ∏ i, (R i)⁻¹ ^ m i) := by
      rw [norm_smul, norm_prod]
      simp only [norm_pow]
      exact mul_le_mul_of_nonneg_left (norm_polydiscCauchyCoeffWithRadii_le hR hM m)
        (Finset.prod_nonneg fun i _ => pow_nonneg (norm_nonneg _) _)
    _ = M * ∏ i, (‖h i‖ / R i) ^ m i := by
      simp only [div_eq_mul_inv, mul_pow, Finset.prod_mul_distrib]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hM0
      apply Finset.prod_le_prod₀
      · intro i hi
        exact pow_nonneg (div_nonneg (norm_nonneg _) (hR i).le) _
      · intro i hi
        exact pow_le_pow_left₀ (div_nonneg (norm_nonneg _) (hR i).le)
          (div_le_div_of_nonneg_right (hh i) (hR i).le) _

/-- Uniform convergence of the Taylor series on every strictly smaller closed polydisc. -/
theorem hasSumUniformlyOn_polydiscTaylor {f : (Fin d → ℂ) → E} {c : Fin d → ℂ}
    {R s : Fin d → ℝ} {M : ℝ} (hR : ∀ i, 0 < R i)
    (hs : ∀ i, 0 ≤ s i) (hsR : ∀ i, s i < R i)
    (hfc : ContinuousOn f (closedPolydiscWithRadii c R))
    (hfa : ∀ z ∈ closedPolydiscWithRadii c R, ∀ i,
      AnalyticAt ℂ (fun v => f (update z i v)) (z i))
    (hM : ∀ z ∈ closedPolydiscWithRadii c R, ‖f z‖ ≤ M) :
    HasSumUniformlyOn
      (fun (m : Fin d → ℕ) h => (∏ i, h i ^ m i) • polydiscCauchyCoeffWithRadii f c R m)
      (fun h => f (c + h)) (closedPolydiscWithRadii 0 s) := by
  have hM0 : 0 ≤ M := (norm_nonneg (f c)).trans
    (hM c (mem_closedPolydiscWithRadii.mpr (by simpa using fun i => (hR i).le)))
  have hq : ∀ i, ‖s i / R i‖ < 1 := by
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hs i) (hR i).le), div_lt_one (hR i)]
    exact hsR i
  have ha := (hasSum_pi_geometric (fun i => s i / R i) hq).summable.mul_left M
  apply hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
  refine (tendstoUniformlyOn_tsum ha (fun m h hh =>
    norm_polydiscTaylor_term_le hR hM0 hM
      (fun i => by simpa using mem_closedPolydiscWithRadii.mp hh i) m)).congr_right ?_
  intro h hh
  exact (hasSum_polydiscTaylor hR (fun i =>
    (show ‖h i‖ ≤ s i by simpa using mem_closedPolydiscWithRadii.mp hh i).trans_lt (hsR i))
    hfc hfa hM).tsum_eq

/-- The multi-index Taylor expansion converges locally uniformly throughout its polydisc. -/
theorem hasSumLocallyUniformlyOn_polydiscTaylor {f : (Fin d → ℂ) → E} {c : Fin d → ℂ}
    {R : Fin d → ℝ} {M : ℝ} (hR : ∀ i, 0 < R i)
    (hfc : ContinuousOn f (closedPolydiscWithRadii c R))
    (hfa : ∀ z ∈ closedPolydiscWithRadii c R, ∀ i,
      AnalyticAt ℂ (fun v => f (update z i v)) (z i))
    (hM : ∀ z ∈ closedPolydiscWithRadii c R, ‖f z‖ ≤ M) :
    HasSumLocallyUniformlyOn
      (fun (m : Fin d → ℕ) h => (∏ i, h i ^ m i) • polydiscCauchyCoeffWithRadii f c R m)
      (fun h => f (c + h)) (polydiscWithRadii 0 R) := by
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  intro h hh
  let s (i : Fin d) := (‖h i‖ + R i) / 2
  have hhR (i) : ‖h i‖ < R i := by simpa using mem_polydiscWithRadii.mp hh i
  have hs (i) : 0 ≤ s i := by dsimp [s]; linarith [norm_nonneg (h i), hR i]
  have hsR (i) : s i < R i := by dsimp [s]; linarith [hhR i]
  have hhs : h ∈ polydiscWithRadii 0 s := mem_polydiscWithRadii.mpr (by
    intro i; simp only [Pi.zero_apply, dist_zero_right]; dsimp [s]; linarith [hhR i])
  refine ⟨closedPolydiscWithRadii 0 s, ?_,
    hasSumUniformlyOn_polydiscTaylor hR hs hsR hfc hfa hM⟩
  apply mem_nhdsWithin_of_mem_nhds
  exact Filter.mem_of_superset ((isOpen_polydiscWithRadii 0 s).mem_nhds hhs)
    (fun z hz => mem_closedPolydiscWithRadii.mpr (fun i =>
      (mem_polydiscWithRadii.mp hz i).le))

/-- A uniform remainder bound for any finite Taylor polynomial. The right-hand side is
the tail of an explicitly summable product of geometric series. -/
theorem norm_polydiscTaylor_remainder_le {f : (Fin d → ℂ) → E} {c h : Fin d → ℂ}
    {R s : Fin d → ℝ} {M : ℝ} (hR : ∀ i, 0 < R i)
    (hs : ∀ i, 0 ≤ s i) (hsR : ∀ i, s i < R i)
    (hfc : ContinuousOn f (closedPolydiscWithRadii c R))
    (hfa : ∀ z ∈ closedPolydiscWithRadii c R, ∀ i,
      AnalyticAt ℂ (fun v => f (update z i v)) (z i))
    (hM : ∀ z ∈ closedPolydiscWithRadii c R, ‖f z‖ ≤ M)
    (hh : ∀ i, ‖h i‖ ≤ s i) (t : Finset (Fin d → ℕ)) :
    ‖f (c + h) - ∑ m ∈ t, (∏ i, h i ^ m i) • polydiscCauchyCoeffWithRadii f c R m‖ ≤
      ∑' m : {m : Fin d → ℕ // m ∉ t}, M * ∏ i, (s i / R i) ^ m.val i := by
  have hM0 : 0 ≤ M := (norm_nonneg (f c)).trans
    (hM c (mem_closedPolydiscWithRadii.mpr (by simpa using fun i => (hR i).le)))
  have hq : ∀ i, ‖s i / R i‖ < 1 := by
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hs i) (hR i).le), div_lt_one (hR i)]
    exact hsR i
  have ha := (hasSum_pi_geometric (fun i => s i / R i) hq).summable.mul_left M
  have hn := Summable.of_nonneg_of_le
    (fun m => norm_nonneg ((∏ i, h i ^ m i) • polydiscCauchyCoeffWithRadii f c R m))
    (norm_polydiscTaylor_term_le hR hM0 hM hh) ha
  rw [← (hasSum_polydiscTaylor hR (fun i => (hh i).trans_lt (hsR i)) hfc hfa hM).tsum_eq,
    ← hn.of_norm.sum_add_tsum_subtype_compl t, add_sub_cancel_left]
  exact (norm_tsum_le_tsum_norm (hn.subtype _)).trans
    ((hn.subtype _).tsum_le_tsum (fun m => norm_polydiscTaylor_term_le hR hM0 hM hh m.val)
      (ha.subtype _))

/-- The geometric-tail bound written without an infinite sum: a finite polynomial is
subtracted from the product of the geometric sums. -/
theorem norm_polydiscTaylor_remainder_le_prod {f : (Fin d → ℂ) → E} {c h : Fin d → ℂ}
    {R s : Fin d → ℝ} {M : ℝ} (hR : ∀ i, 0 < R i)
    (hs : ∀ i, 0 ≤ s i) (hsR : ∀ i, s i < R i)
    (hfc : ContinuousOn f (closedPolydiscWithRadii c R))
    (hfa : ∀ z ∈ closedPolydiscWithRadii c R, ∀ i,
      AnalyticAt ℂ (fun v => f (update z i v)) (z i))
    (hM : ∀ z ∈ closedPolydiscWithRadii c R, ‖f z‖ ≤ M)
    (hh : ∀ i, ‖h i‖ ≤ s i) (t : Finset (Fin d → ℕ)) :
    ‖f (c + h) - ∑ m ∈ t, (∏ i, h i ^ m i) • polydiscCauchyCoeffWithRadii f c R m‖ ≤
      M * ((∏ i, (1 - s i / R i)⁻¹) - ∑ m ∈ t, ∏ i, (s i / R i) ^ m i) := by
  have hq : ∀ i, ‖s i / R i‖ < 1 := by
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hs i) (hR i).le), div_lt_one (hR i)]
    exact hsR i
  have ha := (hasSum_pi_geometric (fun i => s i / R i) hq).mul_left M
  have ht := ha.summable.sum_add_tsum_subtype_compl t
  rw [ha.tsum_eq, ← Finset.mul_sum] at ht
  have heq : (∑' m : {m : Fin d → ℕ // m ∉ t}, M * ∏ i, (s i / R i) ^ m.val i) =
      M * ((∏ i, (1 - s i / R i)⁻¹) - ∑ m ∈ t, ∏ i, (s i / R i) ^ m i) := by
    linarith
  exact (norm_polydiscTaylor_remainder_le hR hs hsR hfc hfa hM hh t).trans_eq heq

/-- Any mixed derivative of the separate-radius Taylor expansion is obtained by termwise
differentiation, with locally uniform convergence on the full open polydisc. -/
theorem hasSumLocallyUniformlyOn_iteratedPartialDeriv_polydiscTaylor
    {f : (Fin d → ℂ) → E} {c : Fin d → ℂ} {R : Fin d → ℝ} {M : ℝ}
    (hR : ∀ i, 0 < R i) (hfc : ContinuousOn f (closedPolydiscWithRadii c R))
    (hfa : ∀ z ∈ closedPolydiscWithRadii c R, ∀ i,
      AnalyticAt ℂ (fun v => f (update z i v)) (z i))
    (hM : ∀ z ∈ closedPolydiscWithRadii c R, ‖f z‖ ≤ M) (is : List (Fin d)) :
    HasSumLocallyUniformlyOn
      (fun m : Fin d → ℕ => iteratedPartialDerivCarlson is
        (fun h => (∏ i, h i ^ m i) • polydiscCauchyCoeffWithRadii f c R m))
      (iteratedPartialDerivCarlson is (fun h => f (c + h))) (polydiscWithRadii 0 R) := by
  apply (hasSumLocallyUniformlyOn_polydiscTaylor hR hfc hfa hM).iteratedPartialDerivCarlson
    _ (isOpen_polydiscWithRadii 0 R) is
  intro m z hz
  apply AnalyticAt.smul
  · exact Finset.analyticAt_fun_prod Finset.univ (fun i _ =>
      ((ContinuousLinearMap.proj i : (Fin d → ℂ) →L[ℂ] ℂ).analyticAt z).pow (m i))
  · exact analyticAt_const

end CarlsonFunctions.SeveralComplexVariables

end

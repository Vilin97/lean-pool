/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouContourLimit
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouUniformQuadraticDecay
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouQuadraticLittleO
public import LeanPool.Odlyzko.ExplicitFormula.SelectedHeightSequence
public import LeanPool.Odlyzko.ExplicitFormula.ZeroFreeRectangles

/-!
# Selected Height Horizontal Vanishing

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Filter MeasureTheory NumberField Real Set
open scoped Topology

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
private theorem norm_completedZetaPoleLogDeriv_le_two
    {σ t : ℝ} (ht : 1 ≤ |t|) :
    ‖completedZetaPoleLogDeriv (σ + t * I)‖ ≤ 2 := by
  have hnorm₀ : 1 ≤ ‖(σ + t * I : ℂ)‖ := by
    exact ht.trans (by
      simpa using Complex.abs_im_le_norm (σ + t * I))
  have hnorm₁ : 1 ≤ ‖(σ + t * I : ℂ) - 1‖ := by
    exact ht.trans (by
      simpa using Complex.abs_im_le_norm ((σ + t * I : ℂ) - 1))
  unfold completedZetaPoleLogDeriv
  rw [one_div, one_div]
  calc
    ‖(σ + t * I : ℂ)⁻¹ + ((σ + t * I : ℂ) - 1)⁻¹‖ ≤
        ‖(σ + t * I : ℂ)⁻¹‖ + ‖((σ + t * I : ℂ) - 1)⁻¹‖ :=
      norm_add_le _ _
    _ ≤ 1 + 1 := by
      gcongr
      · rw [norm_inv]
        exact (inv_le_one₀ (by positivity)).2 hnorm₀
      · rw [norm_inv]
        exact (inv_le_one₀ (by positivity)).2 hnorm₁
    _ = 2 := by norm_num

open Classical in
private theorem selected_positive_integrand_norm_le_weighted
    {y δ σ : ℝ} (_hδ : 0 < δ) (n : ℕ)
    (hσ : σ ∈ Icc (-1 : ℝ) 2) :
    ‖poitouTransform (regularizedScaledTartar y δ)
          (σ + completedZetaSelectedHeight K n * I) *
        (logDeriv (poleClearedCompletedDedekindZetaContinuation K)
              (σ + completedZetaSelectedHeight K n * I) -
          completedZetaPoleLogDeriv
            (σ + completedZetaSelectedHeight K n * I))‖ ≤
      (4 * completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K + 2) *
        (|completedZetaSelectedHeight K n| ^ 2 *
          ‖poitouTransform (regularizedScaledTartar y δ)
            (σ + completedZetaSelectedHeight K n * I)‖) := by
  let T := completedZetaSelectedHeight K n
  let Q := completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K
  have hTlow := (completedZetaSelectedHeight_spec K n).1
  have hTpos : 0 < T := completedZetaSelectedHeight_pos K n
  have hQ : 0 ≤ Q :=
    completedZetaSelectedHeightLogDerivativeQuadraticCoefficient_nonneg K
  have hσ' : σ ∈ Icc (-1 : ℝ) 5 := ⟨hσ.1, hσ.2.trans (by norm_num)⟩
  have hlog :=
    ((completedZetaSelectedHeight_spec K n).2.2 σ hσ').1.2
  have hpole :
      ‖completedZetaPoleLogDeriv (σ + T * I)‖ ≤ 2 :=
    norm_completedZetaPoleLogDeriv_le_two
      (by grind)
  have hheight : ((n : ℝ) + 7) ^ 2 ≤ 4 * |T| ^ 2 := by
    rw [abs_of_pos hTpos]
    nlinarith [sq_nonneg ((n : ℝ) + 7), sq_nonneg T]
  rw [norm_mul]
  calc
    ‖poitouTransform (regularizedScaledTartar y δ) (σ + T * I)‖ *
        ‖logDeriv (poleClearedCompletedDedekindZetaContinuation K)
              (σ + T * I) -
            completedZetaPoleLogDeriv (σ + T * I)‖ ≤
      ‖poitouTransform (regularizedScaledTartar y δ) (σ + T * I)‖ *
        (Q * ((n : ℝ) + 7) ^ 2 + 2) := by
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add hlog hpole)
    _ ≤ ‖poitouTransform (regularizedScaledTartar y δ) (σ + T * I)‖ *
        ((4 * Q + 2) * |T| ^ 2) := by
      gcongr
      nlinarith [mul_le_mul_of_nonneg_left hheight hQ,
        sq_nonneg |T|]
    _ = (4 * Q + 2) *
        (|T| ^ 2 *
          ‖poitouTransform (regularizedScaledTartar y δ) (σ + T * I)‖) := by
      ring

open Classical in
private theorem selected_negative_integrand_norm_le_weighted
    {y δ σ : ℝ} (_hδ : 0 < δ) (n : ℕ)
    (hσ : σ ∈ Icc (-1 : ℝ) 2) :
    ‖poitouTransform (regularizedScaledTartar y δ)
          (σ - completedZetaSelectedHeight K n * I) *
        (logDeriv (poleClearedCompletedDedekindZetaContinuation K)
              (σ - completedZetaSelectedHeight K n * I) -
          completedZetaPoleLogDeriv
            (σ - completedZetaSelectedHeight K n * I))‖ ≤
      (4 * completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K + 2) *
        (|-(completedZetaSelectedHeight K n)| ^ 2 *
          ‖poitouTransform (regularizedScaledTartar y δ)
            (σ - completedZetaSelectedHeight K n * I)‖) := by
  let T := completedZetaSelectedHeight K n
  let Q := completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K
  have hTlow := (completedZetaSelectedHeight_spec K n).1
  have hTpos : 0 < T := completedZetaSelectedHeight_pos K n
  have hQ : 0 ≤ Q :=
    completedZetaSelectedHeightLogDerivativeQuadraticCoefficient_nonneg K
  have hσ' : σ ∈ Icc (-1 : ℝ) 5 := ⟨hσ.1, hσ.2.trans (by norm_num)⟩
  have hlog :=
    ((completedZetaSelectedHeight_spec K n).2.2 σ hσ').2.2
  have hpole :
      ‖completedZetaPoleLogDeriv (σ - T * I)‖ ≤ 2 := by
    (convert norm_completedZetaPoleLogDeriv_le_two
      (σ := σ) (t := -T)
      (by grind) using 1; push_cast; ring_nf)
  have hheight : ((n : ℝ) + 7) ^ 2 ≤ 4 * |-T| ^ 2 := by
    rw [abs_neg, abs_of_pos hTpos]
    nlinarith [sq_nonneg ((n : ℝ) + 7), sq_nonneg T]
  rw [norm_mul]
  calc
    ‖poitouTransform (regularizedScaledTartar y δ) (σ - T * I)‖ *
        ‖logDeriv (poleClearedCompletedDedekindZetaContinuation K)
              (σ - T * I) -
            completedZetaPoleLogDeriv (σ - T * I)‖ ≤
      ‖poitouTransform (regularizedScaledTartar y δ) (σ - T * I)‖ *
        (Q * ((n : ℝ) + 7) ^ 2 + 2) := by
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add hlog hpole)
    _ ≤ ‖poitouTransform (regularizedScaledTartar y δ) (σ - T * I)‖ *
        ((4 * Q + 2) * |-T| ^ 2) := by
      gcongr
      nlinarith [mul_le_mul_of_nonneg_left hheight hQ,
        sq_nonneg |-T|]
    _ = (4 * Q + 2) *
        (|-T| ^ 2 *
          ‖poitouTransform (regularizedScaledTartar y δ)
            (σ - T * I)‖) := by ring

open Classical in
private theorem continuousOn_selected_positive_integrand
    {y δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ContinuousOn
      (fun σ : ℝ ↦
        poitouTransform (regularizedScaledTartar y δ)
            (σ + completedZetaSelectedHeight K n * I) *
          (logDeriv (poleClearedCompletedDedekindZetaContinuation K)
                (σ + completedZetaSelectedHeight K n * I) -
            completedZetaPoleLogDeriv
              (σ + completedZetaSelectedHeight K n * I)))
      (Icc (-1) 2) := by
  intro σ hσ
  let s : ℂ := σ + completedZetaSelectedHeight K n * I
  have hσ' : σ ∈ Icc (-1 : ℝ) 5 := ⟨hσ.1, hσ.2.trans (by norm_num)⟩
  have hsne :
      poleClearedCompletedDedekindZetaContinuation K s ≠ 0 := by
    simpa [s] using
      ((completedZetaSelectedHeight_spec K n).2.2 σ hσ').1.1
  have hs0 : s ≠ 0 := by
    intro hs
    have := congrArg Complex.im hs
    dsimp [s] at this
    simp only [ofReal_im, ofReal_re, mul_im, I_re, I_im, zero_mul, mul_one,
      zero_add] at this
    linarith [completedZetaSelectedHeight_pos K n]
  have hs1 : s - 1 ≠ 0 := by
    intro hs
    have := congrArg Complex.im hs
    dsimp [s] at this
    simp only [ofReal_im, ofReal_re, mul_im, I_re, I_im, zero_mul,
      mul_one, zero_add, sub_zero] at this
    linarith [completedZetaSelectedHeight_pos K n]
  have hsMap :
      ContinuousAt (fun x : ℝ ↦ (x : ℂ) +
        completedZetaSelectedHeight K n * I) σ := by fun_prop
  have hΦ :
      ContinuousAt
        (fun x : ℝ ↦ poitouTransform (regularizedScaledTartar y δ)
          (x + completedZetaSelectedHeight K n * I)) σ :=
    by
      simpa [Function.comp_def, s] using
        (analyticOnNhd_poitouTransform_regularizedScaledTartar hδ
          s (mem_univ s)).continuousAt.comp_of_eq hsMap (by simp [s])
  have hΞ :=
    analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K
      s (mem_univ s)
  have hlog :
      ContinuousAt
        (fun x : ℝ ↦ logDeriv
          (poleClearedCompletedDedekindZetaContinuation K)
          (x + completedZetaSelectedHeight K n * I)) σ := by
    unfold logDeriv
    simpa [Function.comp_def, s] using
      (hΞ.deriv.continuousAt.div hΞ.continuousAt hsne).comp_of_eq
        hsMap (by simp [s])
  have hpole :
      ContinuousAt
        (fun x : ℝ ↦ completedZetaPoleLogDeriv
          (x + completedZetaSelectedHeight K n * I)) σ := by
    unfold completedZetaPoleLogDeriv
    have hone : ContinuousAt (fun _ : ℝ ↦ (1 : ℂ)) σ :=
      continuousAt_const
    exact (hone.div hsMap hs0).add
      (hone.div (hsMap.sub continuousAt_const) hs1)
  exact (hΦ.mul (hlog.sub hpole)).continuousWithinAt

open Classical in
private theorem continuousOn_selected_negative_integrand
    {y δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ContinuousOn
      (fun σ : ℝ ↦
        poitouTransform (regularizedScaledTartar y δ)
            (σ - completedZetaSelectedHeight K n * I) *
          (logDeriv (poleClearedCompletedDedekindZetaContinuation K)
                (σ - completedZetaSelectedHeight K n * I) -
            completedZetaPoleLogDeriv
              (σ - completedZetaSelectedHeight K n * I)))
      (Icc (-1) 2) := by
  intro σ hσ
  let s : ℂ := σ - completedZetaSelectedHeight K n * I
  have hσ' : σ ∈ Icc (-1 : ℝ) 5 := ⟨hσ.1, hσ.2.trans (by norm_num)⟩
  have hsne :
      poleClearedCompletedDedekindZetaContinuation K s ≠ 0 := by
    simpa [s] using
      ((completedZetaSelectedHeight_spec K n).2.2 σ hσ').2.1
  have hs0 : s ≠ 0 := by
    intro hs
    have := congrArg Complex.im hs
    dsimp [s] at this
    simp only [ofReal_im, ofReal_re, mul_im, I_re, I_im, zero_mul, mul_one,
      zero_sub] at this
    linarith [completedZetaSelectedHeight_pos K n]
  have hs1 : s - 1 ≠ 0 := by
    intro hs
    have := congrArg Complex.im hs
    dsimp [s] at this
    simp only [ofReal_im, ofReal_re, mul_im, I_re, I_im, zero_mul, mul_one,
      zero_sub, sub_zero] at this
    linarith [completedZetaSelectedHeight_pos K n]
  have hsMap :
      ContinuousAt (fun x : ℝ ↦ (x : ℂ) -
        completedZetaSelectedHeight K n * I) σ := by fun_prop
  have hΦ :
      ContinuousAt
        (fun x : ℝ ↦ poitouTransform (regularizedScaledTartar y δ)
          (x - completedZetaSelectedHeight K n * I)) σ :=
    by
      simpa [Function.comp_def, s] using
        (analyticOnNhd_poitouTransform_regularizedScaledTartar hδ
          s (mem_univ s)).continuousAt.comp_of_eq hsMap (by simp [s])
  have hΞ :=
    analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K
      s (mem_univ s)
  have hlog :
      ContinuousAt
        (fun x : ℝ ↦ logDeriv
          (poleClearedCompletedDedekindZetaContinuation K)
          (x - completedZetaSelectedHeight K n * I)) σ := by
    unfold logDeriv
    simpa [Function.comp_def, s] using
      (hΞ.deriv.continuousAt.div hΞ.continuousAt hsne).comp_of_eq
        hsMap (by simp [s])
  have hpole :
      ContinuousAt
        (fun x : ℝ ↦ completedZetaPoleLogDeriv
          (x - completedZetaSelectedHeight K n * I)) σ := by
    unfold completedZetaPoleLogDeriv
    have hone : ContinuousAt (fun _ : ℝ ↦ (1 : ℂ)) σ :=
      continuousAt_const
    exact (hone.div hsMap hs0).add
      (hone.div (hsMap.sub continuousAt_const) hs1)
  exact (hΦ.mul (hlog.sub hpole)).continuousWithinAt

open Classical in
theorem tendsto_selected_positive_horizontalIntegral
    {y δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun n ↦ horizontalIntegral
        (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
          (logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
            completedZetaPoleLogDeriv s))
        (-1) 2 (completedZetaSelectedHeight K n))
      atTop (𝓝 0) := by
  let Q := completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K
  let C := regularizedPoitouStripQuadraticDecayConstant y δ (-1) 2
  let B : ℝ := (4 * Q + 2) * C
  let F : ℕ → ℝ → ℂ := fun n σ ↦
    poitouTransform (regularizedScaledTartar y δ)
        (σ + completedZetaSelectedHeight K n * I) *
      (logDeriv (poleClearedCompletedDedekindZetaContinuation K)
            (σ + completedZetaSelectedHeight K n * I) -
        completedZetaPoleLogDeriv
          (σ + completedZetaSelectedHeight K n * I))
  have hDCT :
      Tendsto (fun n ↦ ∫ σ in (-1 : ℝ)..2, F n σ) atTop (𝓝 0) := by
    have hmeas :
        ∀ᶠ n : ℕ in atTop,
          AEStronglyMeasurable (F n) (volume.restrict (uIoc (-1) 2)) :=
      Filter.Eventually.of_forall fun n ↦
        ((continuousOn_selected_positive_integrand K hδ n).mono
          (by
            grind)).aestronglyMeasurable measurableSet_uIoc
    have hbound :
        ∀ᶠ n : ℕ in atTop, ∀ᵐ σ : ℝ,
          σ ∈ uIoc (-1) 2 → ‖F n σ‖ ≤ B :=
      Filter.Eventually.of_forall fun n ↦
        Filter.Eventually.of_forall fun σ hσ ↦ by
          have hσIcc : σ ∈ Icc (-1 : ℝ) 2 := by grind
          apply (selected_positive_integrand_norm_le_weighted K hδ n
            hσIcc).trans
          have hw :=
            sq_abs_mul_norm_poitouTransform_regularized_le_strip
              hδ y (completedZetaSelectedHeight K n) hσIcc
          dsimp [B, C, Q]
          apply mul_le_mul_of_nonneg_left hw
          have hQ :=
            completedZetaSelectedHeightLogDerivativeQuadraticCoefficient_nonneg K
          linarith
    have hlim :
        ∀ᵐ σ : ℝ, σ ∈ uIoc (-1) 2 →
          Tendsto (fun n ↦ F n σ) atTop (𝓝 0) :=
      Filter.Eventually.of_forall fun σ hσ ↦ by
        have hσIcc : σ ∈ Icc (-1 : ℝ) 2 := by grind
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hweighted :=
          (tendsto_sq_abs_mul_norm_poitouTransform_regularized_atTop
            hδ y σ).comp (tendsto_completedZetaSelectedHeight_atTop K)
        have hmajor :
            Tendsto
              (fun n ↦ (4 * Q + 2) *
                (|completedZetaSelectedHeight K n| ^ 2 *
                  ‖poitouTransform (regularizedScaledTartar y δ)
                    (σ + completedZetaSelectedHeight K n * I)‖))
              atTop (𝓝 0) := by
          simpa [Q] using (tendsto_const_nhds.mul hweighted)
        simpa [F] using squeeze_zero'
          (Filter.Eventually.of_forall fun n ↦ norm_nonneg _)
          (Filter.Eventually.of_forall fun n ↦
            selected_positive_integrand_norm_le_weighted K hδ n hσIcc)
          hmajor
    have h :=
      intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (a := (-1 : ℝ)) (b := 2) (μ := volume)
        (l := atTop) (f := fun _ ↦ (0 : ℂ)) (fun _ ↦ B)
        hmeas hbound intervalIntegrable_const hlim
    simpa using h
  simpa [horizontalIntegral, F] using hDCT

open Classical in
theorem tendsto_selected_negative_horizontalIntegral
    {y δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun n ↦ horizontalIntegral
        (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
          (logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
            completedZetaPoleLogDeriv s))
        (-1) 2 (-(completedZetaSelectedHeight K n)))
      atTop (𝓝 0) := by
  let Q := completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K
  let C := regularizedPoitouStripQuadraticDecayConstant y δ (-1) 2
  let B : ℝ := (4 * Q + 2) * C
  let F : ℕ → ℝ → ℂ := fun n σ ↦
    poitouTransform (regularizedScaledTartar y δ)
        (σ - completedZetaSelectedHeight K n * I) *
      (logDeriv (poleClearedCompletedDedekindZetaContinuation K)
            (σ - completedZetaSelectedHeight K n * I) -
        completedZetaPoleLogDeriv
          (σ - completedZetaSelectedHeight K n * I))
  have hDCT :
      Tendsto (fun n ↦ ∫ σ in (-1 : ℝ)..2, F n σ) atTop (𝓝 0) := by
    have hmeas :
        ∀ᶠ n : ℕ in atTop,
          AEStronglyMeasurable (F n) (volume.restrict (uIoc (-1) 2)) :=
      Filter.Eventually.of_forall fun n ↦
        ((continuousOn_selected_negative_integrand K hδ n).mono
          (by
            grind)).aestronglyMeasurable measurableSet_uIoc
    have hbound :
        ∀ᶠ n : ℕ in atTop, ∀ᵐ σ : ℝ,
          σ ∈ uIoc (-1) 2 → ‖F n σ‖ ≤ B :=
      Filter.Eventually.of_forall fun n ↦
        Filter.Eventually.of_forall fun σ hσ ↦ by
          have hσIcc : σ ∈ Icc (-1 : ℝ) 2 := by grind
          apply (selected_negative_integrand_norm_le_weighted K hδ n
            hσIcc).trans
          have hw :=
            sq_abs_mul_norm_poitouTransform_regularized_le_strip
              hδ y (-(completedZetaSelectedHeight K n)) hσIcc
          dsimp [B, C, Q]
          have hw' :
              |-(completedZetaSelectedHeight K n)| ^ 2 *
                  ‖poitouTransform (regularizedScaledTartar y δ)
                    (σ - completedZetaSelectedHeight K n * I)‖ ≤
                regularizedPoitouStripQuadraticDecayConstant y δ (-1) 2 := by
            simpa [sub_eq_add_neg,
              regularizedPoitouStripQuadraticDecayConstant] using hw
          exact mul_le_mul_of_nonneg_left hw' (by
            have hQ :=
              completedZetaSelectedHeightLogDerivativeQuadraticCoefficient_nonneg K
            linarith)
    have hlim :
        ∀ᵐ σ : ℝ, σ ∈ uIoc (-1) 2 →
          Tendsto (fun n ↦ F n σ) atTop (𝓝 0) :=
      Filter.Eventually.of_forall fun σ hσ ↦ by
        have hσIcc : σ ∈ Icc (-1 : ℝ) 2 := by grind
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hneg :
            Tendsto (fun n ↦ -(completedZetaSelectedHeight K n))
              atTop atBot := by
          simpa [Function.comp_def] using
            tendsto_neg_atTop_atBot.comp
              (tendsto_completedZetaSelectedHeight_atTop K)
        have hweighted :=
          (tendsto_sq_abs_mul_norm_poitouTransform_regularized_atBot
            hδ y σ).comp hneg
        have hmajor :
            Tendsto
              (fun n ↦ (4 * Q + 2) *
                (|-(completedZetaSelectedHeight K n)| ^ 2 *
                  ‖poitouTransform (regularizedScaledTartar y δ)
                    (σ - completedZetaSelectedHeight K n * I)‖))
              atTop (𝓝 0) := by
          simpa [Q, sub_eq_add_neg] using
            (tendsto_const_nhds.mul hweighted)
        simpa [F] using squeeze_zero'
          (Filter.Eventually.of_forall fun n ↦ norm_nonneg _)
          (Filter.Eventually.of_forall fun n ↦
            selected_negative_integrand_norm_le_weighted K hδ n hσIcc)
          hmajor
    have h :=
      intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (a := (-1 : ℝ)) (b := 2) (μ := volume)
        (l := atTop) (f := fun _ ↦ (0 : ℂ)) (fun _ ↦ B)
        hmeas hbound intervalIntegrable_const hlim
    simpa using h
  simpa [horizontalIntegral, F, sub_eq_add_neg] using hDCT

open Classical in
theorem regularizedSubtractedHorizontalVanishing_two
    (y : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    RegularizedSubtractedHorizontalVanishing K y δ 2 := by
  let T := completedZetaSelectedHeight K
  let q : ℂ → ℂ := fun s ↦
    poitouTransform (regularizedScaledTartar y δ) s *
      (logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
        completedZetaPoleLogDeriv s)
  refine ⟨T, tendsto_completedZetaSelectedHeight_atTop K, ?_, ?_⟩
  · intro n
    refine ⟨completedZetaSelectedHeight_pos K n, ?_⟩
    intro z hz hside
    rcases hside with hleft | hright | hbottom | htop
    · apply poleClearedCompletedDedekindZetaContinuation_ne_zero_of_re_lt_zero K
      simp_all
    · apply poleClearedCompletedDedekindZetaContinuation_ne_zero_of_one_lt_re K
      simp_all
    · have hzRe : z.re ∈ Icc (-1 : ℝ) 5 :=
        ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
      have hne :=
        ((completedZetaSelectedHeight_spec K n).2.2 z.re hzRe).2.1
      rw [show z =
          (z.re : ℂ) - completedZetaSelectedHeight K n * I by
        apply Complex.ext
        · simp
        · simpa [T] using hbottom]
      simp_all
    · have hzRe : z.re ∈ Icc (-1 : ℝ) 5 :=
        ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
      have hne :=
        ((completedZetaSelectedHeight_spec K n).2.2 z.re hzRe).1.1
      rw [show z =
          (z.re : ℂ) + completedZetaSelectedHeight K n * I by
        apply Complex.ext
        · simp
        · simpa [T] using htop]
      simp_all
  · have hneg :=
      tendsto_selected_negative_horizontalIntegral K (y := y) hδ
    have hpos :=
      tendsto_selected_positive_horizontalIntegral K (y := y) hδ
    simpa [q, T, show (1 : ℝ) - 2 = -1 by norm_num] using hneg.sub hpos

open Classical in
theorem regularizedRightVerticalLowerBound_two
    {y : ℝ} (hy : y ≠ 0) :
    RegularizedRightVerticalLowerBound K y 2 := by
  apply regularizedRightVerticalLowerBound_of_forall_horizontalVanishing
    K hy (by norm_num)
  intro δ hδ
  exact regularizedSubtractedHorizontalVanishing_two K y hδ

end NumberField.Odlyzko

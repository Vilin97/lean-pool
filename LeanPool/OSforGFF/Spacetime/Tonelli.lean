/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


import LeanPool.OSforGFF.Spacetime.Basic
import LeanPool.OSforGFF.Spacetime.Decomposition
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Schwartz Tonelli Factorization

This file proves the Tonelli factorization theorem for Schwartz functions on SpaceTime,
which states that double integrals over SpaceTime can be factorized when the kernel
depends only on the time coordinates.

## Main Results

* `schwartz_tonelli_spacetime` - Tonelli factorization for Schwartz functions on SpaceTime

## References

* Hörmander, "The Analysis of Linear Partial Differential Operators I"
* Folland, "Real Analysis", Chapter 2 (Fubini-Tonelli theorem)
-/

open MeasureTheory MeasureSpace FiniteDimensional Real

/-! ### Auxiliary Lemmas -/

/-- Norm bound: ‖spacetimeDecomp.symm (t, v)‖ ≥ ‖v‖.
    This follows from: ‖x‖² = t² + ‖v‖² ≥ ‖v‖².
-/
lemma spacetimeDecomp_symm_norm_ge (t : ℝ) (v : SpatialCoords) :
    ‖spacetimeDecomp.symm (t, v)‖ ≥ ‖v‖ := by
  have h_spatial : spatialPart (spacetimeDecomp.symm (t, v)) = v :=
    congr_arg Prod.snd (spacetimeDecomp.apply_symm_apply (t, v))
  have h_time : (spacetimeDecomp.symm (t, v)) 0 = t :=
    congr_arg Prod.fst (spacetimeDecomp.apply_symm_apply (t, v))
  have h_decomp := spacetime_norm_sq_decompose (spacetimeDecomp.symm (t, v))
  rw [h_time, h_spatial] at h_decomp
  have h_sq_ge : ‖spacetimeDecomp.symm (t, v)‖^2 ≥ ‖v‖^2 := by
    rw [h_decomp]; nlinarith [sq_nonneg t]
  have h_norm_nonneg : 0 ≤ ‖spacetimeDecomp.symm (t, v)‖ := norm_nonneg _
  exact le_of_sq_le_sq h_sq_ge h_norm_nonneg

/-- Slice integrability: for fixed t, the slice is integrable over SpatialCoords. -/
lemma schwartz_slice_integrable (f : SchwartzMap SpaceTime ℂ) (t : ℝ) :
    Integrable (fun v : SpatialCoords => ‖f (spacetimeDecomp.symm (t, v))‖) volume := by
  have hST_dim : Module.finrank ℝ SpaceTime < 5 := by
    simp only [SpaceTime, finrank_euclideanSpace, Fintype.card_fin]; norm_num
  obtain ⟨C, hC_pos, hf_decay⟩ := schwartz_integrable_decay f 5 hST_dim
  have h_dom_integrable : Integrable (fun v : SpatialCoords => C / (1 + ‖v‖)^5) volume := by
    have h_dim : (Module.finrank ℝ SpatialCoords : ℝ) < 5 := by
      simp only [SpatialCoords, finrank_euclideanSpace, Fintype.card_fin]; norm_num
    have h_int := integrable_one_add_norm (E := SpatialCoords) (μ := volume) (r := 5) h_dim
    have h_eq : ∀ v : SpatialCoords, C / (1 + ‖v‖) ^ 5 = C * (1 + ‖v‖) ^ (-(5 : ℝ)) := by
      intro v
      have h_pos : 0 < 1 + ‖v‖ := by linarith [norm_nonneg v]
      have h1 : ((1 + ‖v‖) ^ 5)⁻¹ = (1 + ‖v‖) ^ (-(5 : ℝ)) := by
        rw [← Real.rpow_natCast (1 + ‖v‖) 5, ← Real.rpow_neg (le_of_lt h_pos)]; simp
      rw [div_eq_mul_inv, h1]
    simp_rw [h_eq]
    exact h_int.const_mul C
  have h_bound : ∀ v : SpatialCoords, ‖f (spacetimeDecomp.symm (t, v))‖ ≤ C / (1 + ‖v‖)^5 := by
    intro v
    have h1 := hf_decay (spacetimeDecomp.symm (t, v))
    have h_norm_ge := spacetimeDecomp_symm_norm_ge t v
    have h_bracket_ge : 1 + ‖spacetimeDecomp.symm (t, v)‖ ≥ 1 + ‖v‖ := by linarith
    have h_bracket_pos : 0 < 1 + ‖v‖ := by linarith [norm_nonneg v]
    have h_pow_le : (1 + ‖v‖)^5 ≤ (1 + ‖spacetimeDecomp.symm (t, v)‖)^5 := by
      apply pow_le_pow_left₀ (by linarith [norm_nonneg v]) h_bracket_ge
    calc ‖f (spacetimeDecomp.symm (t, v))‖
        ≤ C / (1 + ‖spacetimeDecomp.symm (t, v)‖)^5 := h1
      _ ≤ C / (1 + ‖v‖)^5 := by
          apply div_le_div_of_nonneg_left (le_of_lt hC_pos) (by positivity) h_pow_le
  apply Integrable.mono h_dom_integrable
  · have h1 : Measurable (fun v : SpatialCoords => ((t, v) : ℝ × SpatialCoords)) :=
      Measurable.prodMk measurable_const measurable_id
    have h2 : Measurable spacetimeDecomp.symm := spacetimeDecomp.symm.measurable
    have h3 : Continuous f := f.continuous
    have h4 : Continuous (fun x : SpaceTime => ‖f x‖) := h3.norm
    exact (h4.measurable.comp (h2.comp h1)).aestronglyMeasurable
  · filter_upwards with v
    simp only [Real.norm_of_nonneg (norm_nonneg _)]
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ C / (1 + ‖v‖)^5)]
    exact h_bound v

/-- Schwartz composed with spacetimeDecomp.symm is integrable on the product. -/
lemma schwartz_integrable_on_prod' (f : SchwartzMap SpaceTime ℂ) :
    Integrable (fun p : ℝ × SpatialCoords => ‖f (spacetimeDecomp.symm p)‖) := by
  have h_mp : MeasurePreserving spacetimeDecomp (volume : Measure SpaceTime) volume :=
    spacetimeDecomp_measurePreserving
  have h_int : Integrable (fun x : SpaceTime => ‖f x‖) := f.integrable.norm
  rw [← h_mp.integrable_comp_emb spacetimeDecomp.measurableEmbedding]
  convert h_int using 1
  ext x
  simp [Function.comp, MeasurableEquiv.symm_apply_apply]

/-! ### Main Theorem -/

/-- **Tonelli factorization for SpaceTime**.

For Schwartz functions f, g on SpaceTime and a bounded non-negative measurable kernel K
depending only on time coordinates, the double integral factors:

  ∫∫ ‖f x‖ · ‖g y‖ · K(x₀, y₀) dx dy = ∫∫ K(t₁, t₂) · G_f(t₁) · G_g(t₂) dt₁ dt₂

where G_f(t) = ∫ ‖f(t, v)‖ dv is the spatial integral at time t.

This is a key tool for establishing reflection positivity (OS3) bounds.
-/
theorem schwartz_tonelli_spacetime
    (f g : SchwartzMap SpaceTime ℂ)
    (K : ℝ → ℝ → ℝ)
    (hK_nn : ∀ t₁ t₂, 0 ≤ K t₁ t₂)
    (hK_meas : Measurable (Function.uncurry K))
    (hK_bdd : ∃ C : ℝ, ∀ t₁ t₂, K t₁ t₂ ≤ C) :
    let G_f := fun t => ∫ (v : SpatialCoords), ‖f (spacetimeDecomp.symm (t, v))‖
    let G_g := fun t => ∫ (v : SpatialCoords), ‖g (spacetimeDecomp.symm (t, v))‖
    (∫ x : SpaceTime, ∫ y : SpaceTime, ‖f x‖ * ‖g y‖ * K (x 0) (y 0)) =
    (∫ t₁ : ℝ, ∫ t₂ : ℝ, K t₁ t₂ * G_f t₁ * G_g t₂) := by
  intro G_f G_g
  -- Step 1: Rewrite x 0 as (spacetimeDecomp x).1
  have h_time : ∀ x : SpaceTime, x 0 = (spacetimeDecomp x).1 := by
    intro x; simp only [spacetimeDecomp_apply]
  simp_rw [h_time]
  -- Step 2: Get measure preservation
  have h_mp : MeasurePreserving spacetimeDecomp (volume : Measure SpaceTime) volume :=
    spacetimeDecomp_measurePreserving
  -- Step 3: Change variables using spacetimeDecomp
  have h_comp_symm : ∀ G : SpaceTime → ℝ,
      ∫ x : SpaceTime, G x = ∫ p : ℝ × SpatialCoords, G (spacetimeDecomp.symm p) := by
    intro G
    have h_comp : ∀ F : ℝ × SpatialCoords → ℝ,
        ∫ x : SpaceTime, F (spacetimeDecomp x) = ∫ p : ℝ × SpatialCoords, F p :=
      fun F => h_mp.integral_comp spacetimeDecomp.measurableEmbedding F
    have : G = (G ∘ spacetimeDecomp.symm) ∘ spacetimeDecomp := by
      ext x; simp [Function.comp, MeasurableEquiv.symm_apply_apply]
    rw [this]
    exact h_comp (G ∘ spacetimeDecomp.symm)
  rw [h_comp_symm]
  conv_lhs => arg 2; ext p₁; rw [h_comp_symm]
  simp only [MeasurableEquiv.apply_symm_apply]
  -- Integrability facts
  have hf_int : Integrable (fun p : ℝ × SpatialCoords => ‖f (spacetimeDecomp.symm p)‖) :=
    schwartz_integrable_on_prod' f
  have hg_int : Integrable (fun p : ℝ × SpatialCoords => ‖g (spacetimeDecomp.symm p)‖) :=
    schwartz_integrable_on_prod' g
  -- Step 4: Split each pair (t, v) and apply Fubini
  have h_split : ∀ F : ℝ × SpatialCoords → ℝ, Integrable F →
    ∫ p : ℝ × SpatialCoords, F p = ∫ t : ℝ, ∫ v : SpatialCoords, F (t, v) := by
    intro F hF
    have h_eq : (volume : Measure (ℝ × SpatialCoords)) =
        (volume : Measure ℝ).prod (volume : Measure SpatialCoords) := rfl
    rw [h_eq, MeasureTheory.integral_prod _ hF]
  -- The outer integrand as a function of p₁
  have h_outer_int : Integrable (fun p₁ : ℝ × SpatialCoords =>
      ∫ p₂ : ℝ × SpatialCoords,
        ‖f (spacetimeDecomp.symm p₁)‖ * ‖g (spacetimeDecomp.symm p₂)‖ * K p₁.1 p₂.1) := by
    obtain ⟨C, hC⟩ := hK_bdd
    have hC_pos : 0 ≤ C := le_trans (hK_nn 0 0) (hC 0 0)
    have h_prod_int : Integrable (fun p : (ℝ × SpatialCoords) × (ℝ × SpatialCoords) =>
        ‖f (spacetimeDecomp.symm p.1)‖ * ‖g (spacetimeDecomp.symm p.2)‖)
        ((volume : Measure (ℝ × SpatialCoords)).prod volume) :=
      hf_int.mul_prod hg_int
    have h_bound_int : Integrable (fun p : (ℝ × SpatialCoords) × (ℝ × SpatialCoords) =>
        C * (‖f (spacetimeDecomp.symm p.1)‖ * ‖g (spacetimeDecomp.symm p.2)‖))
        ((volume : Measure (ℝ × SpatialCoords)).prod volume) :=
      h_prod_int.const_mul C
    have h_meas : AEStronglyMeasurable (fun p : (ℝ × SpatialCoords) × (ℝ × SpatialCoords) =>
        ‖f (spacetimeDecomp.symm p.1)‖ * ‖g (spacetimeDecomp.symm p.2)‖ * K p.1.1 p.2.1)
        ((volume : Measure (ℝ × SpatialCoords)).prod volume) := by
      have h1 := h_prod_int.aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun p : (ℝ × SpatialCoords) × (ℝ × SpatialCoords) => K p.1.1
        p.2.1)
          ((volume : Measure (ℝ × SpatialCoords)).prod volume) := by
        have hK_comp : Measurable (fun p : (ℝ × SpatialCoords) × (ℝ × SpatialCoords) => (p.1.1,
          p.2.1)) :=
          Measurable.prodMk (measurable_fst.comp measurable_fst) (measurable_fst.comp
            measurable_snd)
        exact (hK_meas.comp hK_comp).aestronglyMeasurable
      exact h1.mul h2
    have h_int_product : Integrable (fun p : (ℝ × SpatialCoords) × (ℝ × SpatialCoords) =>
        ‖f (spacetimeDecomp.symm p.1)‖ * ‖g (spacetimeDecomp.symm p.2)‖ * K p.1.1 p.2.1)
        ((volume : Measure (ℝ × SpatialCoords)).prod volume) := by
      apply Integrable.mono' h_bound_int h_meas
      filter_upwards with p
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      have h_K_bound : |K p.1.1 p.2.1| ≤ C := by
        rw [abs_of_nonneg (hK_nn p.1.1 p.2.1)]
        exact hC p.1.1 p.2.1
      calc ‖f (spacetimeDecomp.symm p.1)‖ * ‖g (spacetimeDecomp.symm p.2)‖ * |K p.1.1 p.2.1|
          ≤ ‖f (spacetimeDecomp.symm p.1)‖ * ‖g (spacetimeDecomp.symm p.2)‖ * C := by
            apply mul_le_mul_of_nonneg_left h_K_bound
            exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
        _ = C * (‖f (spacetimeDecomp.symm p.1)‖ * ‖g (spacetimeDecomp.symm p.2)‖) := by ring
    exact h_int_product.integral_prod_left
  rw [h_split _ h_outer_int]
  -- For the inner integral split
  have h_inner_int : ∀ t₁ v₁, Integrable (fun p₂ : ℝ × SpatialCoords =>
      ‖f (spacetimeDecomp.symm (t₁, v₁))‖ * ‖g (spacetimeDecomp.symm p₂)‖ * K t₁ p₂.1) := by
    intro t₁ v₁
    have hg_K_int : Integrable (fun p₂ : ℝ × SpatialCoords =>
        ‖g (spacetimeDecomp.symm p₂)‖ * K t₁ p₂.1) := by
      obtain ⟨C, hC⟩ := hK_bdd
      have hC_pos : 0 ≤ C := le_trans (hK_nn t₁ 0) (hC t₁ 0)
      have h_bound_int : Integrable (fun p₂ => C * ‖g (spacetimeDecomp.symm p₂)‖) := by
        exact hg_int.const_mul C
      have h_meas : AEStronglyMeasurable (fun p₂ : ℝ × SpatialCoords =>
          ‖g (spacetimeDecomp.symm p₂)‖ * K t₁ p₂.1) volume := by
        have h1 : AEStronglyMeasurable (fun p₂ => ‖g (spacetimeDecomp.symm p₂)‖) volume :=
          hg_int.aestronglyMeasurable
        have h2 : AEStronglyMeasurable (fun p₂ : ℝ × SpatialCoords => K t₁ p₂.1) volume := by
          have h : Measurable (fun p₂ : ℝ × SpatialCoords => (t₁, p₂.1)) :=
            Measurable.prodMk measurable_const measurable_fst
          exact (hK_meas.comp h).aestronglyMeasurable
        exact h1.mul h2
      apply Integrable.mono' h_bound_int h_meas
      filter_upwards with p₂
      simp only [norm_mul, Real.norm_eq_abs]
      calc |‖g (spacetimeDecomp.symm p₂)‖| * |K t₁ p₂.1|
          = ‖g (spacetimeDecomp.symm p₂)‖ * |K t₁ p₂.1| := by simp [abs_of_nonneg (norm_nonneg _)]
        _ ≤ ‖g (spacetimeDecomp.symm p₂)‖ * C := by
            apply mul_le_mul_of_nonneg_left
            · rw [abs_of_nonneg (hK_nn t₁ p₂.1)]
              exact hC t₁ p₂.1
            · exact norm_nonneg _
        _ = C * ‖g (spacetimeDecomp.symm p₂)‖ := by ring
    have h_eq : (fun p₂ => ‖f (spacetimeDecomp.symm (t₁,
      v₁))‖ * ‖g (spacetimeDecomp.symm p₂)‖ * K t₁ p₂.1) =
        fun p₂ => ‖f (spacetimeDecomp.symm (t₁,
          v₁))‖ * (‖g (spacetimeDecomp.symm p₂)‖ * K t₁ p₂.1) := by
      ext p₂; ring
    rw [h_eq]
    exact hg_K_int.const_mul _
  conv_lhs => arg 2; ext t₁; arg 2; ext v₁; rw [h_split _ (h_inner_int t₁ v₁)]
  -- Step 5: Swap ∫ v₁ with ∫ t₂
  have h_swap : ∀ t₁ : ℝ,
    ∫ v₁ : SpatialCoords, ∫ t₂ : ℝ, ∫ v₂ : SpatialCoords,
      ‖f (spacetimeDecomp.symm (t₁, v₁))‖ * ‖g (spacetimeDecomp.symm (t₂, v₂))‖ * K t₁ t₂ =
    ∫ t₂ : ℝ, ∫ v₁ : SpatialCoords, ∫ v₂ : SpatialCoords,
      ‖f (spacetimeDecomp.symm (t₁, v₁))‖ * ‖g (spacetimeDecomp.symm (t₂, v₂))‖ * K t₁ t₂ := by
    intro t₁
    rw [integral_integral_swap]
    have hf_slice : Integrable (fun v₁ => ‖f (spacetimeDecomp.symm (t₁, v₁))‖) :=
      schwartz_slice_integrable f t₁
    have hGg_int : Integrable G_g := by
      have h_prod : Integrable (fun p : ℝ × SpatialCoords => ‖g (spacetimeDecomp.symm p)‖) :=
        schwartz_integrable_on_prod' g
      have h_vol_eq : (volume : Measure (ℝ × SpatialCoords)) =
          (volume : Measure ℝ).prod (volume : Measure SpatialCoords) := rfl
      rw [h_vol_eq] at h_prod
      exact h_prod.integral_prod_left
    have h_right_int : Integrable (fun t₂ => K t₁ t₂ * G_g t₂) := by
      obtain ⟨C, hC⟩ := hK_bdd
      have h_meas_K : Measurable (fun t₂ => K t₁ t₂) :=
        hK_meas.comp (Measurable.prodMk measurable_const measurable_id)
      have h_meas_G : AEStronglyMeasurable G_g volume := hGg_int.aestronglyMeasurable
      apply Integrable.mono' (hGg_int.const_mul C) (h_meas_K.aestronglyMeasurable.mul h_meas_G)
      filter_upwards with t₂
      simp only [Pi.mul_apply]
      rw [Real.norm_eq_abs, abs_mul]
      rw [abs_of_nonneg (hK_nn t₁ t₂)]
      rw [abs_of_nonneg]
      · apply mul_le_mul_of_nonneg_right (hC t₁ t₂)
        apply integral_nonneg
        intro
        exact norm_nonneg _
      · apply integral_nonneg
        intro
        exact norm_nonneg _
    have h_final := hf_slice.mul_prod h_right_int
    apply Integrable.congr h_final
    filter_upwards with p
    simp only [G_g]
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with v₂
    ring
  simp_rw [h_swap]
  -- Step 6: Factorize the inner integrals
  apply integral_congr_ae
  filter_upwards with t₁
  apply integral_congr_ae
  filter_upwards with t₂
  let a := fun v₁ : SpatialCoords => ‖f (spacetimeDecomp.symm (t₁, v₁))‖
  let b := fun v₂ : SpatialCoords => ‖g (spacetimeDecomp.symm (t₂, v₂))‖
  have ha_int : Integrable a := schwartz_slice_integrable f t₁
  have hb_int : Integrable b := schwartz_slice_integrable g t₂
  calc ∫ v₁, ∫ v₂, ‖f (spacetimeDecomp.symm (t₁, v₁))‖ *
        ‖g (spacetimeDecomp.symm (t₂, v₂))‖ * K t₁ t₂
    _ = ∫ v₁, ∫ v₂, K t₁ t₂ * (a v₁ * b v₂) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with v₁
        apply MeasureTheory.integral_congr_ae
        filter_upwards with v₂
        simp only [a, b]; ring
    _ = ∫ v₁, K t₁ t₂ * ∫ v₂, a v₁ * b v₂ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with v₁
        rw [← MeasureTheory.integral_const_mul]
    _ = K t₁ t₂ * ∫ v₁, ∫ v₂, a v₁ * b v₂ := by
        rw [← MeasureTheory.integral_const_mul]
    _ = K t₁ t₂ * ∫ v₁, a v₁ * ∫ v₂, b v₂ := by
        congr 1
        apply MeasureTheory.integral_congr_ae
        filter_upwards with v₁
        rw [← MeasureTheory.integral_const_mul]
    _ = K t₁ t₂ * ∫ v₁, a v₁ * G_g t₂ := by
        simp only [b, G_g]
    _ = K t₁ t₂ * (G_g t₂ * ∫ v₁, a v₁) := by
        congr 1
        have h_comm : (∫ v₁, a v₁ * G_g t₂) = G_g t₂ * ∫ v₁, a v₁ := by
          rw [← MeasureTheory.integral_const_mul]
          apply MeasureTheory.integral_congr_ae
          filter_upwards with v₁
          ring
        exact h_comm
    _ = K t₁ t₂ * (G_g t₂ * G_f t₁) := by
        simp only [a, G_f]
    _ = K t₁ t₂ * G_f t₁ * G_g t₂ := by
        ring

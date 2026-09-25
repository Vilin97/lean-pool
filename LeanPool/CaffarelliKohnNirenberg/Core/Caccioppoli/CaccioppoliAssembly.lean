/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.CaccioppoliMeanSubtraction

/-!
# Caccioppoli Assembly

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

private theorem caccioppoli_centered_time_holder
    {T : Set ℝ} {F E D : ℝ → ℝ≥0∞}
    {C E₀ D₀ V : ℝ≥0∞}
    (hD : AEMeasurable D (volume.restrict T))
    (hpoint : ∀ᵐ s ∂volume.restrict T,
      F s ^ (2 / 3 : ℝ) ≤ C * E s ^ (1 / 2 : ℝ) * D s ^ (1 / 2 : ℝ))
    (hEbound : ∀ᵐ s ∂volume.restrict T, E s ≤ E₀)
    (hDint : (∫⁻ s in T, D s) ≤ D₀)
    (hTvol : volume T ≤ V)
    (hC : C ≠ ∞) (hE₀ : E₀ ≠ ∞) :
    (∫⁻ s in T, F s) ^ (2 / 3 : ℝ) ≤
      C * E₀ ^ (1 / 2 : ℝ) * D₀ ^ (1 / 2 : ℝ) * V ^ (1 / 6 : ℝ) := by
  have hCnonneg : 0 ≤ C := by positivity
  have hE₀nonneg : 0 ≤ E₀ := by positivity
  have hD₀nonneg : 0 ≤ D₀ := by positivity
  have hVnonneg : 0 ≤ V := by positivity
  have hpow : ∀ᵐ s ∂volume.restrict T,
      F s ≤ C ^ (3 / 2 : ℝ) * E₀ ^ (3 / 4 : ℝ) * D s ^ (3 / 4 : ℝ) := by
    filter_upwards [hpoint, hEbound] with s hs hEs
    have hroot : F s = (F s ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) := by
      rw [← ENNReal.rpow_mul]
      norm_num
    rw [hroot]
    have hright :
        (C * E s ^ (1 / 2 : ℝ) * D s ^ (1 / 2 : ℝ)) ^ (3 / 2 : ℝ) ≤
          (C * E₀ ^ (1 / 2 : ℝ) * D s ^ (1 / 2 : ℝ)) ^ (3 / 2 : ℝ) := by
      apply ENNReal.rpow_le_rpow
      · gcongr
      · norm_num
    calc
      (F s ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) ≤
          (C * E s ^ (1 / 2 : ℝ) * D s ^ (1 / 2 : ℝ)) ^ (3 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hs (by norm_num)
      _ ≤ (C * E₀ ^ (1 / 2 : ℝ) * D s ^ (1 / 2 : ℝ)) ^ (3 / 2 : ℝ) := hright
      _ = C ^ (3 / 2 : ℝ) * E₀ ^ (3 / 4 : ℝ) * D s ^ (3 / 4 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num
  have hDpow :
      (∫⁻ s in T, D s ^ (3 / 4 : ℝ)) ≤
        D₀ ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ) := by
    have hconj : (4 / 3 : ℝ).HolderConjugate 4 := by
      rw [Real.holderConjugate_iff]
      constructor <;> norm_num
    have hone : AEMeasurable (fun _ : ℝ => (1 : ℝ≥0∞))
        (volume.restrict T) := measurable_const.aemeasurable
    have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq
      (volume.restrict T) hconj (hD.pow_const (3 / 4 : ℝ)) hone
    have hDpow' :
        (∫⁻ s in T, (D s ^ (3 / 4 : ℝ)) * 1) ≤
          (∫⁻ s in T, (D s ^ (3 / 4 : ℝ)) ^ (4 / 3 : ℝ)) ^
              (3 / 4 : ℝ) *
            (∫⁻ s in T, (1 : ℝ≥0∞) ^ (4 : ℝ)) ^ (1 / 4 : ℝ) := by
      convert hholder using 1
      all_goals norm_num
    have hDpow_eq :
        (∫⁻ s in T, (D s ^ (3 / 4 : ℝ)) ^ (4 / 3 : ℝ)) =
          ∫⁻ s in T, D s := by
      apply lintegral_congr_ae
      filter_upwards [] with s
      rw [← ENNReal.rpow_mul]
      norm_num
    have hOne : (∫⁻ s in T, (1 : ℝ≥0∞) ^ (4 : ℝ)) = volume T := by
      simp
    rw [hDpow_eq, hOne] at hDpow'
    calc
      ∫⁻ s in T, D s ^ (3 / 4 : ℝ) ≤
          (∫⁻ s in T, D s) ^ (3 / 4 : ℝ) * (volume T) ^ (1 / 4 : ℝ) := by
        simpa only [mul_one] using hDpow'
      _ ≤ D₀ ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ) := by
        gcongr
  have hFbound :
      (∫⁻ s in T, F s) ≤
        C ^ (3 / 2 : ℝ) * E₀ ^ (3 / 4 : ℝ) *
          (D₀ ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ)) := by
    calc
      _ ≤ ∫⁻ s in T,
          C ^ (3 / 2 : ℝ) * E₀ ^ (3 / 4 : ℝ) * D s ^ (3 / 4 : ℝ) :=
        lintegral_mono_ae hpow
      _ = C ^ (3 / 2 : ℝ) * E₀ ^ (3 / 4 : ℝ) *
          (∫⁻ s in T, D s ^ (3 / 4 : ℝ)) := by
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC)
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hE₀))]
      _ ≤ _ := by gcongr
  have hroot := ENNReal.rpow_le_rpow hFbound (by norm_num : 0 ≤ (2 / 3 : ℝ))
  calc
    (∫⁻ s in T, F s) ^ (2 / 3 : ℝ) ≤
        (C ^ (3 / 2 : ℝ) * E₀ ^ (3 / 4 : ℝ) *
          (D₀ ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ))) ^ (2 / 3 : ℝ) := hroot
    _ = C * E₀ ^ (1 / 2 : ℝ) * D₀ ^ (1 / 2 : ℝ) * V ^ (1 / 6 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        ← ENNReal.rpow_mul]
      norm_num
      ring

private theorem caccioppoli_real_slice_to_ennreal
    {B : Set Vec3} {g : Vec3 → ℝ} {R : ℝ}
    (hg : IntegrableOn g B volume)
    (hgn : 0 ≤ᵐ[volume.restrict B] g)
    (hP : (∫ x in B, g x) ^ (2 / 3 : ℝ) ≤ R) :
    (∫⁻ x in B, ENNReal.ofReal (g x)) ^ (2 / 3 : ℝ) ≤ ENNReal.ofReal R := by
  have hLtop : (∫⁻ x in B, ENNReal.ofReal (g x)) ≠ ∞ := by
    exact (lintegral_ofReal_ne_top_iff_integrable hg.aestronglyMeasurable hgn).2 hg
  have hL : (∫⁻ x in B, ENNReal.ofReal (g x)) =
      ENNReal.ofReal (∫ x in B, g x) := by
    rw [← ENNReal.ofReal_toReal hLtop]
    rw [setIntegral_eq_toReal_setLIntegral_of_nonneg hg hgn]
  have hnon : 0 ≤ ∫ x in B, g x := integral_nonneg_of_ae hgn
  rw [hL, ENNReal.ofReal_rpow_of_nonneg hnon (by norm_num)]
  exact ENNReal.ofReal_le_ofReal hP

theorem caccioppoli_centered_bound_of_slice_data
    {B : Set Vec3} {T : Set ℝ}
    {g e d : Vec3 × ℝ → ℝ} {F E D : ℝ → ℝ≥0∞}
    {E₀ D₀ V : ℝ≥0∞} {cC : ℝ}
    (hFdef : ∀ s, F s = ∫⁻ x in B, ENNReal.ofReal (g (x, s)))
    (hEdef : ∀ s, E s = ∫⁻ x in B, ENNReal.ofReal (e (x, s)))
    (hDdef : ∀ s, D s = ∫⁻ x in B, ENNReal.ofReal (d (x, s)))
    (hDmeas : AEMeasurable D (volume.restrict T))
    (hgInt : ∀ᵐ s ∂volume.restrict T, IntegrableOn (fun x => g (x, s)) B volume)
    (heInt : ∀ᵐ s ∂volume.restrict T, IntegrableOn (fun x => e (x, s)) B volume)
    (hdInt : ∀ᵐ s ∂volume.restrict T, IntegrableOn (fun x => d (x, s)) B volume)
    (hgn : ∀ᵐ s ∂volume.restrict T, 0 ≤ᵐ[volume.restrict B] fun x => g (x, s))
    (hen : ∀ᵐ s ∂volume.restrict T, 0 ≤ᵐ[volume.restrict B] fun x => e (x, s))
    (hdn : ∀ᵐ s ∂volume.restrict T, 0 ≤ᵐ[volume.restrict B] fun x => d (x, s))
    (hpoint : ∀ᵐ s ∂volume.restrict T,
      (∫ x in B, g (x, s)) ^ (2 / 3 : ℝ) ≤
        cC * (∫ x in B, e (x, s)) ^ (1 / 2 : ℝ) *
          (∫ x in B, d (x, s)) ^ (1 / 2 : ℝ))
    (hC : 0 ≤ cC) (hCtop : ENNReal.ofReal cC ≠ ∞)
    (hEbound : ∀ᵐ s ∂volume.restrict T, E s ≤ E₀)
    (hDint : (∫⁻ s in T, D s) ≤ D₀)
    (hTvol : volume T ≤ V) (hE₀ : E₀ ≠ ∞) :
    (∫⁻ s in T, F s) ^ (2 / 3 : ℝ) ≤
      ENNReal.ofReal cC * E₀ ^ (1 / 2 : ℝ) * D₀ ^ (1 / 2 : ℝ) *
        V ^ (1 / 6 : ℝ) := by
  have hpoint' : ∀ᵐ s ∂volume.restrict T,
      F s ^ (2 / 3 : ℝ) ≤ ENNReal.ofReal cC * E s ^ (1 / 2 : ℝ) *
        D s ^ (1 / 2 : ℝ) := by
    filter_upwards [hgInt, heInt, hdInt, hgn, hen, hdn, hpoint] with s hgs hes hds hgns hens hdns hp
    have hF := caccioppoli_real_slice_to_ennreal hgs hgns hp
    have heq : (∫⁻ x in B, ENNReal.ofReal (e (x, s))) =
        ENNReal.ofReal (∫ x in B, e (x, s)) := by
      rw [← ENNReal.ofReal_toReal ((lintegral_ofReal_ne_top_iff_integrable
        hes.aestronglyMeasurable hens).2 hes)]
      rw [setIntegral_eq_toReal_setLIntegral_of_nonneg hes hens]
    have hdq : (∫⁻ x in B, ENNReal.ofReal (d (x, s))) =
        ENNReal.ofReal (∫ x in B, d (x, s)) := by
      rw [← ENNReal.ofReal_toReal ((lintegral_ofReal_ne_top_iff_integrable
        hds.aestronglyMeasurable hdns).2 hds)]
      rw [setIntegral_eq_toReal_setLIntegral_of_nonneg hds hdns]
    rw [hFdef s, hEdef s, hDdef s, heq, hdq,
      ENNReal.ofReal_rpow_of_nonneg (integral_nonneg_of_ae hens) (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (integral_nonneg_of_ae hdns) (by norm_num)]
    have he_nonneg : 0 ≤ ∫ x in B, e (x, s) := integral_nonneg_of_ae hens
    have he_root_nonneg : 0 ≤ (∫ x in B, e (x, s)) ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg he_nonneg _
    rw [← ENNReal.ofReal_mul hC,
      ← ENNReal.ofReal_mul (mul_nonneg hC he_root_nonneg)]
    exact hF
  apply caccioppoli_centered_time_holder hDmeas hpoint' hEbound
    hDint hTvol hCtop hE₀

/-- The four Caccioppoli contributions assemble into the squared paper bound.

The four inequalities in `hI` are the interfaces for the four analytic
integral estimates, and `hlower` is the lower-bound step on the left side. -/
theorem caccioppoli_assemble_four_terms
    {αr βr A B G D L κ C₂₅ C₂₆ I₁ I₂ I₃ I₄ : ℝ}
    (hαr : 0 ≤ αr) (hβr : 0 ≤ βr) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hG : 0 ≤ G) (hD : 0 ≤ D) (hL : 0 ≤ L) (hκ : 0 < κ)
    (hC₂₅ : 0 ≤ C₂₅) (hC₂₆ : 0 ≤ C₂₆)
    (hlower : (αr + βr) ^ 2 ≤ I₁ + I₂ + I₃ + I₄)
    (hI₁_bound : I₁ ≤ (C₂₅ * κ * A) ^ 2)
    (hI₂_bound : I₂ ≤
      (C₂₅ * κ⁻¹ * A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) * G ^ (1 / 2 : ℝ)) ^ 2)
    (hI₃_bound : I₃ ≤
      (C₂₅ * κ⁻¹ * D * G ^ (1 / 2 : ℝ)) ^ 2)
    (hI₄_bound : I₄ ≤
      (C₂₆ * κ ^ (-1 / 2 : ℝ) * G ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ)) ^ 2) :
    αr + βr ≤
      C₂₅ * κ * A +
        C₂₅ * κ⁻¹ * A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) * G ^ (1 / 2 : ℝ) +
        C₂₅ * κ⁻¹ * D * G ^ (1 / 2 : ℝ) +
        C₂₆ * κ ^ (-1 / 2 : ℝ) * G ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) := by
  let T₁ : ℝ := C₂₅ * κ * A
  let T₂ : ℝ := C₂₅ * κ⁻¹ * A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) * G ^ (1 / 2 : ℝ)
  let T₃ : ℝ := C₂₅ * κ⁻¹ * D * G ^ (1 / 2 : ℝ)
  let T₄ : ℝ := C₂₆ * κ ^ (-1 / 2 : ℝ) * G ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ)
  have hT₁ : 0 ≤ T₁ := by positivity
  have hT₂ : 0 ≤ T₂ := by positivity
  have hT₃ : 0 ≤ T₃ := by positivity
  have hT₄ : 0 ≤ T₄ := by positivity
  have hsum : (αr + βr) ^ 2 ≤ (T₁ + T₂ + T₃ + T₄) ^ 2 := by
    apply le_trans hlower
    exact caccioppoli_square_sum_le_square_sum hT₁ hT₂ hT₃ hT₄
      hI₁_bound hI₂_bound hI₃_bound hI₄_bound
  have hleft : 0 ≤ αr + βr := add_nonneg hαr hβr
  have hright : 0 ≤ T₁ + T₂ + T₃ + T₄ := by positivity
  have hroot : αr + βr ≤ T₁ + T₂ + T₃ + T₄ := by
    nlinarith only [hsum, hleft, hright]
  simpa only [T₁, T₂, T₃, T₄] using hroot

theorem caccioppoli_raw_term_bounds
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ r ε C₂₅ C₂₆ C_PS : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hr : 0 < r)
    (hscale : r ≤ ρ / 2) (hεr : ε < r ^ 2)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hfuture : Icc t₀ (t₀ + ε) ⊆ I) (hC_PS : 0 ≤ C_PS)
    (hC₁ : ((32 + 3 * cutoffSecondDerivativeConstant) * 8000000 +
      6 * cutoffGradientConstant * 5000000) ≤ C₂₅ ^ 2)
    (hC₂ : C_PS * (1500 * cutoffGradientConstant + 900000) ≤ C₂₅ ^ 2)
    (hC₃ : 3000 * cutoffGradientConstant + 1800000 ≤ C₂₅ ^ 2)
    (hC₄ : 2000 * (4 * Real.pi / 3) ^
      (1 / (q / (q - 1)) - 1 / 3 : ℝ) ≤ C₂₆ ^ 2)
    {c : ParabolicPoint → ℝ}
    (hA : AEMeasurable (fun w => ENNReal.ofReal
      |(vec3EuclideanNorm (u w)) ^ 2 - c w|)
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)))
    (hcenter :
      (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| ^
          (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
        ENNReal.ofReal (C_PS * ρ ^ (4 / 3 : ℝ) *
          alpha u (x₀, t₀) ρ * beta u Du (x₀, t₀) ρ)) :
    caccioppoliI1HeatCutoffRaw (u := u) (x₀ := x₀) (t₀ := t₀)
        (ρ := ρ) (ε := ε) (r := r) hρ hε ≤
          (C₂₅ * (r / ρ) * alpha u (x₀, t₀) ρ) ^ 2 ∧
    caccioppoliI2HeatCutoffRaw (u := u) (c := c) (x₀ := x₀)
        (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r) hρ hε ≤
          (C₂₅ * (r / ρ)⁻¹ * alpha u (x₀, t₀) ρ ^ (1 / 2 : ℝ) *
            beta u Du (x₀, t₀) ρ ^ (1 / 2 : ℝ) *
            gamma u (x₀, t₀) ρ ^ (1 / 2 : ℝ)) ^ 2 ∧
    caccioppoliI3HeatCutoffRaw (p := p) (v := u) (x₀ := x₀)
        (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r) hρ hε ≤
          (C₂₅ * (r / ρ)⁻¹ * delta p (x₀, t₀) ρ *
            gamma u (x₀, t₀) ρ ^ (1 / 2 : ℝ)) ^ 2 ∧
    caccioppoliI4HeatCutoffRaw (u := u) (f := f) (x₀ := x₀)
        (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r) hρ hε ≤
          (C₂₆ * (r / ρ) ^ (-1 / 2 : ℝ) *
            gamma u (x₀, t₀) ρ ^ (1 / 2 : ℝ) *
            lambda q f (x₀, t₀) ρ ^ (1 / 2 : ℝ)) ^ 2 := by
  have hv := caccioppoli_velocity_integral_ne_top hsol hρ hsub
  exact ⟨
    caccioppoli_I1_heat_cutoff_raw_normalized hsol hρ hε hr hscale hεr hsub
      hfuture hC₁,
    caccioppoli_I2_heat_cutoff_raw_normalized hsol hρ hε hC_PS hr hscale hsub
      hA hcenter hv hC₂,
    caccioppoli_I3_heat_cutoff_raw_normalized hsol hρ hε hr hscale hsub hv hC₃,
    caccioppoli_I4_heat_cutoff_raw_normalized hsol hρ hε hr hεr hsub hv hC₄⟩

theorem caccioppoli_setIntegral_le_toReal_lintegral_abs
    {S Q : Set ParabolicPoint} {g : ParabolicPoint → ℝ}
    (hSQ : S ⊆ Q) (hg : IntegrableOn g Q volume) :
    ∫ z in S, g z ≤
      (∫⁻ z in Q, ENNReal.ofReal |g z|).toReal := by
  have hgS : IntegrableOn g S volume := hg.mono_set hSQ
  have hnormQ : IntegrableOn (fun z => |g z|) Q volume := hg.norm
  have hQtop : (∫⁻ z in Q, ENNReal.ofReal |g z|) ≠ ∞ := by
    exact (lintegral_ofReal_ne_top_iff_integrable hnormQ.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => abs_nonneg _))).2 hnormQ
  calc
    ∫ z in S, g z ≤ |∫ z in S, g z| := le_abs_self _
    _ ≤ (∫⁻ z in S, ENNReal.ofReal |g z|).toReal := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_lintegral_norm (μ := volume.restrict S) g)
    _ ≤ (∫⁻ z in Q, ENNReal.ofReal |g z|).toReal := by
      apply ENNReal.toReal_mono hQtop
      exact lintegral_mono_set hSQ

theorem caccioppoli_real_rpow_add_bound (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ (3 / 2 : ℝ) ≤
      (2 : ℝ) ^ (1 / 2 : ℝ) *
        (a ^ (3 / 2 : ℝ) + b ^ (3 / 2 : ℝ)) := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow
    (ENNReal.ofReal a) (ENNReal.ofReal b) (p := (3 / 2 : ℝ)) (by norm_num)
  rw [← ENNReal.ofReal_add ha hb,
    ENNReal.ofReal_rpow_of_nonneg (add_nonneg ha hb) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg ha (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg hb (by norm_num)] at h
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
    ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num)] at h
  norm_num at h
  rw [← ENNReal.ofReal_add (Real.rpow_nonneg ha (3 / 2))
      (Real.rpow_nonneg hb (3 / 2)),
    ← ENNReal.ofReal_mul (by positivity)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h


end CKN

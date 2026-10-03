/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.RawI3
public import LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds

/-!
# Raw I3 Bound

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat


noncomputable section

namespace CKN

/-- Raw pressure contribution paired with velocity and the spatial gradient of the heat cutoff. -/
@[expose]
def caccioppoliI3HeatCutoffRaw
    {p : ParabolicPoint → ℝ} {v : ParabolicPoint → Vec3}
    {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) : ℝ :=
  (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
      (2 : ℝ≥0∞) * ENNReal.ofReal |p w| *
        ENNReal.ofReal (vec3EuclideanNorm (v w)) *
        ENNReal.ofReal (∑ i, |spatialPartial (fun y : ParabolicPoint =>
          backwardHeatCutoff
            (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|)).toReal

private lemma caccioppoli_I3_heat_cutoff_raw_bound_hgrad_1 :
    ∀ {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ) (hε : 0 < ε),
      0 < r →
        r ≤ ρ / 2 →
          ∀ w ∈ parabolicCylinder x₀ t₀ ρ,
            ∑ i : Fin 3,
                |spatialPartial
                    (fun y =>
                      backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y)
                    i w| ≤
              (1500 * cutoffGradientConstant + 900000) / r ^ 2
    := by
  intro x₀ t₀ ρ ε r hρ hε hr hscale w hw
  have hraw := caccioppoli_heat_cutoff_gradient_sum_bound
    (x₀ := x₀) (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r)
    (z := w) hρ hε hr hscale hw
  have hρr : 2 * r ≤ ρ := by
    have hw' : r ≤ ρ / 2 := by
      exact hscale
    nlinarith only [hw']
  have hC : 0 ≤ cutoffGradientConstant := by
    by_contra hC'
    have hneg : cutoffGradientConstant / ρ < 0 :=
      div_neg_of_neg_of_pos (lt_of_not_ge hC') hρ
    have hbound := caccioppoli_spatial_cutoff_gradient_bound 0 ρ hρ 0
    have hnorm' : 0 ≤ vecEuclideanNorm (classicalGradient
        (mollifiedBallCutoff 0 hρ) 0) := by
      unfold vecEuclideanNorm
      positivity
    have hnorm'' : 0 ≤ vecEuclideanNorm (classicalGradient
        (mollifiedBallCutoff 0 hρ) 0) := by
      exact hnorm'
    exact (not_lt_of_ge hnorm'') (hbound.trans_lt hneg)
  have hfirst : cutoffGradientConstant / ρ * (1000 / r) ≤
      500 * cutoffGradientConstant / r ^ 2 := by
    have hρr' : 0 < ρ := hρ
    have hpos : 0 < r := hr
    have hmul : 1000 / (ρ * r) ≤ 500 / r ^ 2 := by
      apply (div_le_div_iff₀ (mul_pos hρr' hpos) (sq_pos_of_pos hpos)).2
      have hmul' := mul_le_mul_of_nonneg_right hρr hpos.le
      nlinarith only [hmul']
    calc
      cutoffGradientConstant / ρ * (1000 / r) =
          cutoffGradientConstant * (1000 / (ρ * r)) := by
        field_simp [hρr'.ne', hpos.ne']
      _ ≤ cutoffGradientConstant * (500 / r ^ 2) :=
        mul_le_mul_of_nonneg_left hmul hC
      _ = 500 * cutoffGradientConstant / r ^ 2 := by ring
  have hsecond : 300000 * r ^ 2 / r ^ 4 = 300000 / r ^ 2 := by
    field_simp [hr.ne']
  calc
    _ ≤ 3 * (500 * cutoffGradientConstant / r ^ 2 +
        300000 / r ^ 2) := by
      exact hraw.trans
        (mul_le_mul_of_nonneg_left
          (add_le_add hfirst hsecond.le) (by positivity))
    _ = (1500 * cutoffGradientConstant + 900000) / r ^ 2 := by
      field_simp [hr.ne']
      ring

private lemma caccioppoli_I3_heat_cutoff_raw_bound_hmono_2 :
    ∀ {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ)
      (hε : 0 < ε),
      0 < r →
        (∀ w ∈ parabolicCylinder x₀ t₀ ρ,
            ∑ i : Fin 3,
                |spatialPartial
                    (fun y =>
                      backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y)
                    i w| ≤
              (1500 * cutoffGradientConstant + 900000) / r ^ 2) →
          ∫⁻ (w : ParabolicPoint) in parabolicCylinder x₀ t₀ ρ,
              2 * ENNReal.ofReal |p w| * ENNReal.ofReal (vec3EuclideanNorm (u w)) *
                ENNReal.ofReal
                  (∑ i : Fin 3,
                    |spatialPartial
                        (fun y =>
                          backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y)
                        i w|) ≤
            ∫⁻ (w : ParabolicPoint) in parabolicCylinder x₀ t₀ ρ,
              ENNReal.ofReal ((3000 * cutoffGradientConstant + 1800000) / r ^ 2) *
                  ENNReal.ofReal |p w| *
                ENNReal.ofReal (vec3EuclideanNorm (u w))
    := by
  intro u p x₀ t₀ ρ ε r hρ hε hr hgrad
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (measurableSet_parabolicCylinder _ _ _)]
    with w hw
  have hg := hgrad w hw
  have hnonneg : 0 ≤ ∑ i, |spatialPartial (fun y : ParabolicPoint =>
      backwardHeatCutoff
        (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w| := by
    positivity
  have hscalar : (2 : ℝ≥0∞) * ENNReal.ofReal
      (∑ i, |spatialPartial (fun y : ParabolicPoint =>
      backwardHeatCutoff
        (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|) ≤
      ENNReal.ofReal ((3000 * cutoffGradientConstant + 1800000) / r ^ 2) := by
    calc
      (2 : ℝ≥0∞) * ENNReal.ofReal _ =
          ENNReal.ofReal (2 * (∑ i, |spatialPartial (fun y : ParabolicPoint =>
            backwardHeatCutoff
              (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|)) := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2)]
        norm_num
      _ ≤ ENNReal.ofReal ((3000 * cutoffGradientConstant + 1800000) / r ^ 2) :=
        ENNReal.ofReal_le_ofReal (by
          calc
            2 * _ ≤ 2 * ((1500 * cutoffGradientConstant + 900000) / r ^ 2) :=
              mul_le_mul_of_nonneg_left hg (by positivity)
            _ = (3000 * cutoffGradientConstant + 1800000) / r ^ 2 := by
              field_simp [hr.ne']
              ring)
  calc
    _ = (2 * ENNReal.ofReal (∑ i, |spatialPartial (fun y : ParabolicPoint =>
        backwardHeatCutoff
          (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|) *
        (ENNReal.ofReal |p w| *
          ENNReal.ofReal (vec3EuclideanNorm (u w)))) := by ring
    _ ≤ ENNReal.ofReal ((3000 * cutoffGradientConstant + 1800000) / r ^ 2) *
        (ENNReal.ofReal |p w| *
          ENNReal.ofReal (vec3EuclideanNorm (u w))) := by
      exact mul_le_mul_of_nonneg_right hscalar (by positivity)
    _ = _ := by ring

theorem caccioppoli_I3_heat_cutoff_raw_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hr : 0 < r)
    (hscale : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hvelocity :
      (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞) :
    caccioppoliI3HeatCutoffRaw (p := p) (v := u) (x₀ := x₀) (t₀ := t₀)
        (ρ := ρ) (ε := ε) (r := r) hρ hε ≤
      (3000 * cutoffGradientConstant + 1800000) *
        (ρ ^ 2 / r ^ 2) * delta p (x₀, t₀) ρ ^ 2 * gamma u (x₀, t₀) ρ := by
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hρ hsub
  have hu0 : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet Ω' J)) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).1
  have hp0 : AEStronglyMeasurable p
      (volume.restrict (spaceTimeSet Ω' J)) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).2.2.1
  have hnorm : AEStronglyMeasurable
      (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)) := by
    have hc : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
      unfold vec3EuclideanNorm
      fun_prop
    have h := (ENNReal.continuous_ofReal.comp hc).comp_aestronglyMeasurable hu0
    exact h.mono_measure (Measure.restrict_mono hcyl le_rfl)
  have hpress : AEMeasurable (fun w => ENNReal.ofReal |p w|)
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)) := by
    have hc : Continuous (fun x : ℝ => ENNReal.ofReal |x|) :=
      ENNReal.continuous_ofReal.comp continuous_abs
    exact (hc.comp_aestronglyMeasurable hp0).aemeasurable.mono_measure
      (Measure.restrict_mono hcyl le_rfl)
  have huv : AEMeasurable (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)) := hnorm.aemeasurable
  have hgrad := @caccioppoli_I3_heat_cutoff_raw_bound_hgrad_1 x₀ t₀ ρ ε r hρ hε hr hscale
  have hC : 0 ≤ 3000 * cutoffGradientConstant + 1800000 := by
    have hgradC : 0 ≤ cutoffGradientConstant := by
      by_contra hC'
      have hneg : cutoffGradientConstant / ρ < 0 :=
        div_neg_of_neg_of_pos (lt_of_not_ge hC') hρ
      have hbound := caccioppoli_spatial_cutoff_gradient_bound 0 ρ hρ 0
      have hnorm' : 0 ≤ vecEuclideanNorm (classicalGradient
          (mollifiedBallCutoff 0 hρ) 0) := by
        unfold vecEuclideanNorm
        positivity
      exact (not_lt_of_ge hnorm') (hbound.trans_lt hneg)
    positivity
  have hfactor : ENNReal.ofReal ((3000 * cutoffGradientConstant + 1800000) / r ^ 2) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have hbound :
      (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal ((3000 * cutoffGradientConstant + 1800000) / r ^ 2) *
          ENNReal.ofReal |p w| *
          ENNReal.ofReal (vec3EuclideanNorm (u w))) ≤
      ENNReal.ofReal ((3000 * cutoffGradientConstant + 1800000) / r ^ 2) *
        (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
          ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
        (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ^
          (1 / 3 : ℝ) := by
    exact caccioppoli_I3_holder hpress huv hfactor
  have hmono := @caccioppoli_I3_heat_cutoff_raw_bound_hmono_2 u p x₀ t₀ ρ ε r hρ hε hr hgrad
  have hpint := caccioppoli_I3_pressure_integral_identity hsol (x₀, t₀) hρ hsub
  have hvint := caccioppoli_I2_velocity_integral_identity
    (u := u) (z := (x₀, t₀)) (ρ := ρ) hρ hvelocity
  have hdelta : 0 ≤ delta p (x₀, t₀) ρ := by
    unfold delta
    positivity
  have hgamma : 0 ≤ gamma u (x₀, t₀) ρ := by
    unfold gamma
    positivity
  have hpint' :
      (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) =
        ENNReal.ofReal (ρ ^ 2 * delta p (x₀, t₀) ρ ^ 3) := by
    simpa only [Prod.fst, Prod.snd] using hpint
  have hvint' :
      (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) =
        ENNReal.ofReal (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3) := by
    simpa only [Prod.fst, Prod.snd] using hvint
  have hBtop :
      (ENNReal.ofReal ((3000 * cutoffGradientConstant + 1800000) / r ^ 2) *
        (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
          ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
        (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ^
            (1 / 3 : ℝ)) ≠ ∞ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hfactor
        (ENNReal.rpow_ne_top_of_nonneg (by positivity)
          (by rw [hpint']; exact ENNReal.ofReal_ne_top)))
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hvelocity)
  have hreal := ENNReal.toReal_mono hBtop (hmono.trans hbound)
  rw [hpint', hvint'] at hreal
  conv at hreal =>
    rhs
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤
        (3000 * cutoffGradientConstant + 1800000) / r ^ 2),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤
        ρ ^ 2 * delta p (x₀, t₀) ρ ^ 3),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤
        ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3)]
  have hscale :
      (ρ ^ 2 * delta p (x₀, t₀) ρ ^ 3) ^ (2 / 3 : ℝ) *
        (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3) ^ (1 / 3 : ℝ) =
      ρ ^ 2 * delta p (x₀, t₀) ρ ^ 2 * gamma u (x₀, t₀) ρ := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
    have hrho : (ρ ^ 2) ^ (1 / 3 : ℝ) = ρ ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    have hgamma' : (gamma u (x₀, t₀) ρ ^ 3) ^ (1 / 3 : ℝ) =
        gamma u (x₀, t₀) ρ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hrho, hgamma']
    have hrhoadd : ρ ^ (4 / 3 : ℝ) * ρ ^ (2 / 3 : ℝ) = ρ ^ 2 := by
      rw [← Real.rpow_add hρ]
      norm_num
    calc
      _ = (ρ ^ (4 / 3 : ℝ) * ρ ^ (2 / 3 : ℝ)) *
          delta p (x₀, t₀) ρ ^ 2 * gamma u (x₀, t₀) ρ := by ring
      _ = _ := by rw [hrhoadd]
  rw [mul_assoc, hscale] at hreal
  convert hreal using 1
  · unfold caccioppoliI3HeatCutoffRaw
    congr 1
  · ring

theorem caccioppoli_I3_heat_cutoff_raw_normalized
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ ε r C₂₅ : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hr : 0 < r)
    (hscale : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hvelocity :
      (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞)
    (hKbound :
      3000 * cutoffGradientConstant + 1800000 ≤ C₂₅ ^ 2) :
    caccioppoliI3HeatCutoffRaw (p := p) (v := u) (x₀ := x₀) (t₀ := t₀)
        (ρ := ρ) (ε := ε) (r := r) hρ hε ≤
      (C₂₅ * (r / ρ)⁻¹ * delta p (x₀, t₀) ρ *
        gamma u (x₀, t₀) ρ ^ (1 / 2 : ℝ)) ^ 2 := by
  apply caccioppoli_I3_normalization (κ := r / ρ)
    (δ := delta p (x₀, t₀) ρ) (γ := gamma u (x₀, t₀) ρ)
    (div_pos hr hρ) (by unfold delta; positivity) (by unfold gamma; positivity)
    hKbound
  calc
    _ ≤ (3000 * cutoffGradientConstant + 1800000) *
        (ρ ^ 2 / r ^ 2) * delta p (x₀, t₀) ρ ^ 2 *
          gamma u (x₀, t₀) ρ :=
      caccioppoli_I3_heat_cutoff_raw_bound hsol hρ hε hr hscale hsub hvelocity
    _ = (3000 * cutoffGradientConstant + 1800000) *
        (r / ρ)⁻¹ ^ 2 * delta p (x₀, t₀) ρ ^ 2 *
          gamma u (x₀, t₀) ρ := by
      field_simp [hρ.ne', hr.ne']

end CKN

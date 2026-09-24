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
# Raw I2 Bound

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-- Raw transport contribution after subtracting the chosen scalar energy center. -/
def caccioppoliI2HeatCutoffRaw
    {u : ParabolicPoint → Vec3} {c : ParabolicPoint → ℝ} {x₀ : Vec3} {t₀ ρ ε r : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) : ℝ :=
  (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| *
        ENNReal.ofReal (vec3EuclideanNorm (u w)) *
        ENNReal.ofReal (∑ i, |spatialPartial (fun y : ParabolicPoint =>
          backwardHeatCutoff
            (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|)).toReal

theorem caccioppoli_I2_heat_cutoff_raw_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {c : ParabolicPoint → ℝ} {x₀ : Vec3} {t₀ ρ ε r C_PS : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hC_PS : 0 ≤ C_PS)
    (hr : 0 < r) (hscale : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hA : AEMeasurable (fun w => ENNReal.ofReal
      |(vec3EuclideanNorm (u w)) ^ 2 - c w|)
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)))
    (hcenter :
      (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| ^
          (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
        ENNReal.ofReal (C_PS * ρ ^ (4 / 3 : ℝ) *
          alpha u (x₀, t₀) ρ * beta u Du (x₀, t₀) ρ))
    (hvelocity :
      (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞) :
    caccioppoliI2HeatCutoffRaw (u := u) (c := c) (x₀ := x₀) (t₀ := t₀)
        (ρ := ρ) (ε := ε) (r := r) hρ hε ≤
      (C_PS * (1500 * cutoffGradientConstant + 900000)) *
        (ρ ^ 2 / r ^ 2) * alpha u (x₀, t₀) ρ * beta u Du (x₀, t₀) ρ *
          gamma u (x₀, t₀) ρ := by
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hρ hsub
  have hu0 : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet Ω' J)) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).1
  have hu : AEMeasurable (fun w => ENNReal.ofReal
      (vec3EuclideanNorm (u w)))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)) := by
    have hc : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact ((ENNReal.continuous_ofReal.comp hc).comp_aestronglyMeasurable hu0).aemeasurable
      |>.mono_measure (Measure.restrict_mono hcyl le_rfl)
  have hC : 0 ≤ cutoffGradientConstant := by
    by_contra hC'
    have hneg : cutoffGradientConstant / ρ < 0 :=
      div_neg_of_neg_of_pos (lt_of_not_ge hC') hρ
    have hbound := caccioppoli_spatial_cutoff_gradient_bound 0 ρ hρ 0
    have hnorm : 0 ≤ vecEuclideanNorm (classicalGradient
        (mollifiedBallCutoff 0 hρ) 0) := by
      unfold vecEuclideanNorm
      positivity
    exact (not_lt_of_ge hnorm) (hbound.trans_lt hneg)
  have hgrad : ∀ w ∈ parabolicCylinder x₀ t₀ ρ,
      ∑ i, |spatialPartial (fun y : ParabolicPoint =>
        backwardHeatCutoff
          (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w| ≤
        (1500 * cutoffGradientConstant + 900000) / r ^ 2 := by
    intro w hw
    have hraw := caccioppoli_heat_cutoff_gradient_sum_bound
      (x₀ := x₀) (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r)
      (z := w) hρ hε hr hscale hw
    have hρr : 2 * r ≤ ρ := by nlinarith only [hscale]
    have hfirst : cutoffGradientConstant / ρ * (1000 / r) ≤
        500 * cutoffGradientConstant / r ^ 2 := by
      have hmul : 1000 / (ρ * r) ≤ 500 / r ^ 2 := by
        apply (div_le_div_iff₀ (mul_pos hρ hr) (sq_pos_of_pos hr)).2
        have hmul' := mul_le_mul_of_nonneg_right hρr hr.le
        nlinarith only [hmul']
      calc
        cutoffGradientConstant / ρ * (1000 / r) =
            cutoffGradientConstant * (1000 / (ρ * r)) := by
          field_simp [hρ.ne', hr.ne']
        _ ≤ cutoffGradientConstant * (500 / r ^ 2) :=
          mul_le_mul_of_nonneg_left hmul hC
        _ = 500 * cutoffGradientConstant / r ^ 2 := by ring
    have hsecond : 300000 * r ^ 2 / r ^ 4 = 300000 / r ^ 2 := by
      field_simp [hr.ne']
    exact hraw.trans (mul_le_mul_of_nonneg_left
      (add_le_add hfirst hsecond.le) (by positivity)) |>.trans_eq (by ring)
  let G : ℝ := (1500 * cutoffGradientConstant + 900000) / r ^ 2
  have hG : 0 ≤ G := by
    dsimp [G]
    positivity
  have hfactor : ENNReal.ofReal G ≠ ∞ := ENNReal.ofReal_ne_top
  have hbound :
      (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal G *
          ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| *
          ENNReal.ofReal (vec3EuclideanNorm (u w))) ≤
      ENNReal.ofReal G *
        (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| ^
            (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
        (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ^
            (1 / 3 : ℝ) := by
    exact caccioppoli_I2_holder hA hu hfactor
  have hmono :
      (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| *
          ENNReal.ofReal (vec3EuclideanNorm (u w)) *
          ENNReal.ofReal (∑ i, |spatialPartial (fun y : ParabolicPoint =>
            backwardHeatCutoff
              (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|)) ≤
      ∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal G *
          ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| *
          ENNReal.ofReal (vec3EuclideanNorm (u w)) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_parabolicCylinder _ _ _)]
      with w hw
    have hscalar : ENNReal.ofReal
        (∑ i, |spatialPartial (fun y : ParabolicPoint =>
          backwardHeatCutoff
            (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|) ≤
        ENNReal.ofReal G := ENNReal.ofReal_le_ofReal (hgrad w hw)
    calc
      _ = (ENNReal.ofReal
          (∑ i, |spatialPartial (fun y : ParabolicPoint =>
            backwardHeatCutoff
              (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|) *
          (ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| *
            ENNReal.ofReal (vec3EuclideanNorm (u w)))) := by ring
      _ ≤ ENNReal.ofReal G *
          (ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| *
            ENNReal.ofReal (vec3EuclideanNorm (u w))) :=
        mul_le_mul_of_nonneg_right hscalar (by positivity)
      _ = _ := by ring
  have hvint := caccioppoli_I2_velocity_integral_identity
    (u := u) (z := (x₀, t₀)) (ρ := ρ) hρ hvelocity
  have hvint' :
      (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) =
        ENNReal.ofReal (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3) := by
    simpa only [Prod.fst, Prod.snd] using hvint
  have hRtop :
      (ENNReal.ofReal G *
        (ENNReal.ofReal (C_PS * ρ ^ (4 / 3 : ℝ) *
          alpha u (x₀, t₀) ρ * beta u Du (x₀, t₀) ρ)) *
        (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ^
            (1 / 3 : ℝ)) ≠ ∞ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hfactor ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hvelocity)
  have hreal := ENNReal.toReal_mono hRtop
    (hmono.trans (hbound.trans (by
      gcongr
      )))
  rw [hvint'] at hreal
  have hgamma : 0 ≤ gamma u (x₀, t₀) ρ := by
    unfold gamma
    positivity
  have hα : 0 ≤ alpha u (x₀, t₀) ρ := by unfold alpha; positivity
  have hβ : 0 ≤ beta u Du (x₀, t₀) ρ := by unfold beta; positivity
  conv at hreal =>
    rhs
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ G),
      ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤
        ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3)]
  have hscale' :
      (C_PS * ρ ^ (4 / 3 : ℝ) * alpha u (x₀, t₀) ρ * beta u Du (x₀, t₀) ρ) *
        (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3) ^ (1 / 3 : ℝ) =
      C_PS * ρ ^ 2 * alpha u (x₀, t₀) ρ * beta u Du (x₀, t₀) ρ *
        gamma u (x₀, t₀) ρ := by
    have hrho : (ρ ^ 2) ^ (1 / 3 : ℝ) = ρ ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
      norm_num
    have hγ : (gamma u (x₀, t₀) ρ ^ 3) ^ (1 / 3 : ℝ) =
        gamma u (x₀, t₀) ρ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hgamma]
      norm_num
    rw [Real.mul_rpow (by positivity) (by positivity), hrho, hγ]
    have hrho' : ρ ^ (4 / 3 : ℝ) * ρ ^ (2 / 3 : ℝ) = ρ ^ 2 := by
      rw [← Real.rpow_add hρ]
      norm_num
    calc
      _ = C_PS * (ρ ^ (4 / 3 : ℝ) * ρ ^ (2 / 3 : ℝ)) *
          alpha u (x₀, t₀) ρ * beta u Du (x₀, t₀) ρ *
            gamma u (x₀, t₀) ρ := by ring
      _ = _ := by rw [hrho']
  rw [mul_assoc, hscale'] at hreal
  convert hreal using 1
  · unfold caccioppoliI2HeatCutoffRaw
    congr 1
  · dsimp [G]
    ring

theorem caccioppoli_I2_heat_cutoff_raw_normalized
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {c : ParabolicPoint → ℝ} {x₀ : Vec3} {t₀ ρ ε r C₂₅ C_PS : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hC_PS : 0 ≤ C_PS)
    (hr : 0 < r) (hscale : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hA : AEMeasurable (fun w => ENNReal.ofReal
      |(vec3EuclideanNorm (u w)) ^ 2 - c w|)
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)))
    (hcenter :
      (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| ^
          (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
        ENNReal.ofReal (C_PS * ρ ^ (4 / 3 : ℝ) *
          alpha u (x₀, t₀) ρ * beta u Du (x₀, t₀) ρ))
    (hvelocity :
      (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞)
    (hKbound :
      C_PS * (1500 * cutoffGradientConstant + 900000) ≤ C₂₅ ^ 2) :
    caccioppoliI2HeatCutoffRaw (u := u) (c := c) (x₀ := x₀) (t₀ := t₀)
        (ρ := ρ) (ε := ε) (r := r) hρ hε ≤
      (C₂₅ * (r / ρ)⁻¹ * alpha u (x₀, t₀) ρ ^ (1 / 2 : ℝ) *
        beta u Du (x₀, t₀) ρ ^ (1 / 2 : ℝ) *
        gamma u (x₀, t₀) ρ ^ (1 / 2 : ℝ)) ^ 2 := by
  apply caccioppoli_I2_normalization (κ := r / ρ)
    (α := alpha u (x₀, t₀) ρ) (β := beta u Du (x₀, t₀) ρ)
    (γ := gamma u (x₀, t₀) ρ) (div_pos hr hρ)
    (by unfold alpha; positivity) (by unfold beta; positivity)
    (by unfold gamma; positivity) hKbound
  calc
    _ ≤ C_PS * (1500 * cutoffGradientConstant + 900000) *
        (ρ ^ 2 / r ^ 2) * alpha u (x₀, t₀) ρ *
          beta u Du (x₀, t₀) ρ * gamma u (x₀, t₀) ρ :=
      caccioppoli_I2_heat_cutoff_raw_bound hsol hρ hε hC_PS hr hscale hsub hA
        hcenter hvelocity
    _ = C_PS * (1500 * cutoffGradientConstant + 900000) *
        (r / ρ)⁻¹ ^ 2 * alpha u (x₀, t₀) ρ *
          beta u Du (x₀, t₀) ρ * gamma u (x₀, t₀) ρ := by
      field_simp [hρ.ne', hr.ne']

end CKN

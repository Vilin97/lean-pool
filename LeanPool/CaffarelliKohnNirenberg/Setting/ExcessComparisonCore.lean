/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Finiteness
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Conversions
public import LeanPool.CaffarelliKohnNirenberg.Pressure.OscillationLin34
public import LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Slice
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Tsai excess quantities

The four quantities in this file use genuine averages on the one-sided
parabolic cylinder.  The velocity norm is transported to `L²` before applying
the convexity estimate, so it is the Euclidean norm used by the scale
quantities.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

/-- Tsai's velocity excess `C_tilde` on the one-sided parabolic cylinder. -/
noncomputable def tsaiVelocityExcess (u : ParabolicPoint → Vec3)
    (z : ParabolicPoint) (r : ℝ) : ℝ :=
  r⁻¹ ^ (2 : ℕ) *
    (∫ w in parabolicCylinder z.1 z.2 r,
      vec3EuclideanNorm
        (u w - ⨍ y in parabolicCylinder z.1 z.2 r, u y) ^ (3 : ℕ))

/-- Tsai's pressure excess `D_tilde` on the one-sided parabolic cylinder. -/
noncomputable def tsaiPressureExcess (p : ParabolicPoint → ℝ)
    (z : ParabolicPoint) (r : ℝ) : ℝ :=
  r⁻¹ ^ (2 : ℕ) *
    (∫ w in parabolicCylinder z.1 z.2 r,
      |p w - spatialAverage z.1 r w.2 p| ^ (3 / 2 : ℝ))

/-- Tsai's combined excess `φ`. -/
noncomputable def tsaiPhi (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (z : ParabolicPoint) (r : ℝ) : ℝ :=
  tsaiVelocityExcess u z r ^ (1 / 3 : ℝ) +
    tsaiPressureExcess p z r ^ (2 / 3 : ℝ)

/-- Tsai's drift functional `Ψ`. -/
noncomputable def tsaiPsi (u : ParabolicPoint → Vec3)
    (z : ParabolicPoint) (r : ℝ) : ℝ :=
  r * vec3EuclideanNorm (⨍ w in parabolicCylinder z.1 z.2 r, u w)

private theorem integrable_sq_of_energy
    {E : Type} [NormedAddCommGroup E]
    {v : ParabolicPoint → E} {S : Set ParabolicPoint}
    (hv : AEStronglyMeasurable v (volume.restrict S))
    (hfin : (∫⁻ z in S, ‖v z‖ₑ ^ (2 : ℝ)) < ⊤) :
    Integrable (fun z => (‖v z‖ : ℝ) ^ (2 : ℕ))
      (volume.restrict S) := by
  have hmeas : AEStronglyMeasurable
      (fun z => (‖v z‖ : ℝ) ^ (2 : ℕ)) (volume.restrict S) :=
    hv.norm.pow 2
  have hfin' : (∫⁻ z in S,
      ENNReal.ofReal ((‖v z‖ : ℝ) ^ (2 : ℕ))) ≠ ⊤ := by
    convert ne_of_lt hfin using 1
    apply lintegral_congr
    intro z
    rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
    norm_num [ENNReal.rpow_natCast]
  exact (lintegral_ofReal_ne_top_iff_integrable hmeas
    (Filter.Eventually.of_forall fun z => sq_nonneg (‖v z‖))).mp hfin'

private theorem sws_integrable_velocity_on_cylinder
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    IntegrableOn u (parabolicCylinder z.1 z.2 r) volume := by
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hr hsub
  obtain ⟨hu, -, -, -, -, henergy, -, -, -⟩ :=
    hsol.2.2.2.2.2.1 Ω' J hbox
  have huenergy : (∫⁻ w in spaceTimeSet Ω' J,
      ‖u w‖ₑ ^ (2 : ℝ)) < ⊤ := by
    exact lt_of_le_of_lt
      (lintegral_mono (fun w => le_add_right le_rfl)) henergy
  have husq := integrable_sq_of_energy hu huenergy
  let S : Set ParabolicPoint := parabolicCylinder z.1 z.2 r
  have : IsFiniteMeasure (volume.restrict S) := by
    refine ⟨?_⟩
    simpa [S] using
      (volume_parabolicCylinder_lt_top (x := z.1) (t := z.2) (r := r))
  have husqS : Integrable (fun w => (‖u w‖ : ℝ) ^ (2 : ℕ))
      (volume.restrict S) :=
    husq.mono_measure (Measure.restrict_mono hcyl le_rfl)
  have husqS' : Integrable (fun w => ‖u w‖ ^ (2 : ℝ))
      (volume.restrict S) := by
    convert husqS using 1
    funext w
    norm_num [Real.rpow_natCast]
  have huS : AEStronglyMeasurable u (volume.restrict S) :=
    hu.mono_measure (Measure.restrict_mono hcyl le_rfl)
  have huone : Integrable (fun w => ‖u w‖ ^ (1 : ℝ))
      (volume.restrict S) :=
    integrable_norm_rpow_of_le huS (p := (1 : ℝ)) (q := (2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) husqS'
  change Integrable u (volume.restrict S)
  refine ⟨huS, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have huone' : Integrable (fun w => ‖u w‖) (volume.restrict S) := by
    convert huone using 1
    funext w
    rw [Real.rpow_one]
  have hfinite :=
    (hasFiniteIntegral_iff_norm (fun w => ‖u w‖)).1 huone'.hasFiniteIntegral
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hfinite

private theorem sws_integrable_velocity_cube_on_cylinder
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    IntegrableOn (fun w => vec3EuclideanNorm (u w) ^ (3 : ℕ))
      (parabolicCylinder z.1 z.2 r) volume := by
  have hfin := caccioppoli_velocity_integral_ne_top hsol hr hsub
  have hmeasU : AEStronglyMeasurable u
      (volume.restrict (parabolicCylinder z.1 z.2 r)) := by
    obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
      hsol.1 hsol.2.1 hr hsub
    obtain ⟨hu, -, -, -, -, -, -, -, -⟩ :=
      hsol.2.2.2.2.2.1 Ω' J hbox
    exact hu.mono_measure (Measure.restrict_mono hcyl le_rfl)
  have hcont : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
    unfold vec3EuclideanNorm
    fun_prop
  have hmeas : AEStronglyMeasurable
      (fun w => vec3EuclideanNorm (u w) ^ (3 : ℕ))
      (volume.restrict (parabolicCylinder z.1 z.2 r)) :=
    (hcont.comp_aestronglyMeasurable hmeasU).pow 3
  have hfin' : (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (vec3EuclideanNorm (u w) ^ (3 : ℕ))) ≠ ⊤ := by
    convert hfin using 1
    apply lintegral_congr
    intro w
    rw [ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _) 3]
    norm_num [ENNReal.rpow_natCast]
  exact (lintegral_ofReal_ne_top_iff_integrable hmeas
    (Filter.Eventually.of_forall fun w => pow_nonneg
      (vec3EuclideanNorm_nonneg _) 3)).mp hfin'


private theorem euclidean_average_map
    {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {r : ℝ}
    (_ : IntegrableOn u (parabolicCylinder z.1 z.2 r) volume) :
    WithLp.toLp 2 (⨍ w in parabolicCylinder z.1 z.2 r, u w) =
      ⨍ w in parabolicCylinder z.1 z.2 r, WithLp.toLp 2 (u w) := by
  let L := (PiLp.continuousLinearEquiv (2 : ℝ≥0∞) ℝ
    (fun _ : Fin 3 => ℝ)).symm
  have hL : (L : Vec3 → L2Vec3) = WithLp.toLp 2 := by
    funext v
    exact rfl
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
  change L ((volume (parabolicCylinder z.1 z.2 r)).toReal⁻¹ •
      ∫ w in parabolicCylinder z.1 z.2 r, u w) =
    (volume (parabolicCylinder z.1 z.2 r)).toReal⁻¹ •
      ∫ w in parabolicCylinder z.1 z.2 r, L (u w)
  have hcomm : (∫ w in parabolicCylinder z.1 z.2 r, L (u w)) =
      L (∫ w in parabolicCylinder z.1 z.2 r, u w) := by
    exact L.integral_comp_comm (φ := u)
  rw [map_smul, hcomm]

private theorem euclidean_excess_lintegral_bound
    {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {r : ℝ}
    (hr : 0 < r)
    (hu : IntegrableOn u (parabolicCylinder z.1 z.2 r) volume)
    (hu3 : IntegrableOn (fun w => vec3EuclideanNorm (u w) ^ (3 : ℕ))
      (parabolicCylinder z.1 z.2 r) volume) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm
          (u w - ⨍ y in parabolicCylinder z.1 z.2 r, u y)) ^ (3 : ℝ)) ≤
      8 * (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) := by
  let L := (PiLp.continuousLinearEquiv (2 : ℝ≥0∞) ℝ
    (fun _ : Fin 3 => ℝ)).symm
  have hL : (L : Vec3 → L2Vec3) = WithLp.toLp 2 := by
    funext v
    exact rfl
  have hLint : IntegrableOn (fun w => L (u w))
      (parabolicCylinder z.1 z.2 r) volume := by
    exact L.toContinuousLinearMap.integrable_comp hu.integrable
  have hL3 : IntegrableOn (fun w => ‖L (u w)‖ ^ (3 : ℕ))
      (parabolicCylinder z.1 z.2 r) volume := by
    simpa only [vec3EuclideanNorm_eq_l2, hL] using hu3
  have h := setLaverage_norm_sub_setAverage_rpow_le
    (f := fun w => L (u w)) (p := (3 : ℝ)) (c := (0 : L2Vec3))
    (by norm_num) (volume_parabolicCylinder_pos hr)
    (volume_parabolicCylinder_lt_top (x := z.1) (t := z.2) (r := r))
    hLint (by simpa using hL3)
  have hmap : L (⨍ w in parabolicCylinder z.1 z.2 r, u w) =
      ⨍ w in parabolicCylinder z.1 z.2 r, L (u w) := by
    simpa only [hL] using euclidean_average_map hu
  rw [← hmap] at h
  simp only [← map_sub] at h
  rw [MeasureTheory.setLAverage_eq, MeasureTheory.setLAverage_eq] at h
  have h' := h
  norm_num [ENNReal.rpow_natCast] at h'
  have h'' :
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ‖L (u w - ⨍ y in parabolicCylinder z.1 z.2 r, u y)‖ₑ ^ (3 : ℝ)) /
        volume (parabolicCylinder z.1 z.2 r) ≤
      (8 * (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ‖L (u w)‖ₑ ^ (3 : ℝ))) / volume (parabolicCylinder z.1 z.2 r) := by
    simpa [map_sub, sub_zero, mul_div_assoc, Real.rpow_natCast] using h'
  have hvolpos := volume_parabolicCylinder_pos (x := z.1) (t := z.2) hr
  have hvoltop := volume_parabolicCylinder_lt_top (x := z.1) (t := z.2) (r := r)
  have hraw :
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ‖L (u w - ⨍ y in parabolicCylinder z.1 z.2 r, u y)‖ₑ ^ (3 : ℝ)) ≤
      8 * (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ‖L (u w)‖ₑ ^ (3 : ℝ)) := by
    calc
      _ = ((∫⁻ w in parabolicCylinder z.1 z.2 r,
          ‖L (u w - ⨍ y in parabolicCylinder z.1 z.2 r, u y)‖ₑ ^ (3 : ℝ)) /
          volume (parabolicCylinder z.1 z.2 r)) * volume (parabolicCylinder z.1 z.2 r) := by
            rw [ENNReal.div_mul_cancel hvolpos.ne' hvoltop.ne]
      _ ≤ ((8 : ℝ≥0∞) * (∫⁻ w in parabolicCylinder z.1 z.2 r,
          ‖L (u w)‖ₑ ^ (3 : ℝ)) /
          volume (parabolicCylinder z.1 z.2 r)) * volume (parabolicCylinder z.1 z.2 r) := by
            exact mul_le_mul_of_nonneg_right h'' (by positivity)
      _ = 8 * (∫⁻ w in parabolicCylinder z.1 z.2 r,
          ‖L (u w)‖ₑ ^ (3 : ℝ)) := by
            exact ENNReal.div_mul_cancel hvolpos.ne' hvoltop.ne
  convert hraw using 1 <;> simp [hL, vec3EuclideanNorm_eq_l2, ofReal_norm]

theorem tsaiVelocityExcess_le_eight_gamma_cube
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    tsaiVelocityExcess u z r ≤ 8 * gamma u z r ^ (3 : ℕ) := by
  have hu := sws_integrable_velocity_on_cylinder hsol hr hsub
  have hu3 := sws_integrable_velocity_cube_on_cylinder hsol hr hsub
  have hraw := euclidean_excess_lintegral_bound hr hu hu3
  have hcenterMeas : AEStronglyMeasurable
      (fun w => vec3EuclideanNorm
        (u w - ⨍ y in parabolicCylinder z.1 z.2 r, u y) ^ (3 : ℕ))
      (volume.restrict (parabolicCylinder z.1 z.2 r)) := by
    have huMeas := hu.aestronglyMeasurable
    have havgMeas : AEStronglyMeasurable
        (fun _ : ParabolicPoint =>
          ⨍ y in parabolicCylinder z.1 z.2 r, u y)
        (volume.restrict (parabolicCylinder z.1 z.2 r)) :=
      aestronglyMeasurable_const
    have hsub : AEStronglyMeasurable
        (fun w => u w - ⨍ y in parabolicCylinder z.1 z.2 r, u y)
        (volume.restrict (parabolicCylinder z.1 z.2 r)) :=
      huMeas.sub havgMeas
    have hcont : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact (hcont.comp_aestronglyMeasurable hsub).pow 3
  have hu3top : (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ⊤ := by
    have hfin' := (lintegral_ofReal_ne_top_iff_integrable
      hu3.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w =>
        pow_nonneg (vec3EuclideanNorm_nonneg _) 3)).2 hu3
    convert hfin' using 1
    apply lintegral_congr
    intro w
    rw [ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _) 3]
    norm_num [ENNReal.rpow_natCast]
  have hctop : (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (vec3EuclideanNorm
        (u w - ⨍ y in parabolicCylinder z.1 z.2 r, u y)) ^ (3 : ℝ)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hraw
      (ENNReal.mul_lt_top (by norm_num) hu3top.lt_top))
  have h8top : (8 : ℝ≥0∞) *
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hu3top
  have hreal8 := (ENNReal.toReal_le_toReal hctop h8top).2 hraw
  have hreal :
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm
          (u w - ⨍ y in parabolicCylinder z.1 z.2 r, u y)) ^ (3 : ℝ)).toReal ≤
      8 * (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal := by
    simpa [ENNReal.toReal_mul] using hreal8
  have hcenterTop : (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (vec3EuclideanNorm
        (u w - ⨍ y in parabolicCylinder z.1 z.2 r, u y) ^ (3 : ℕ))) ≠ ⊤ := by
    convert hctop using 1
    apply lintegral_congr
    intro w
    rw [ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _) 3]
    norm_num [ENNReal.rpow_natCast]
  have hcenterInt :=
    (lintegral_ofReal_ne_top_iff_integrable hcenterMeas
      (Filter.Eventually.of_forall fun w =>
        pow_nonneg (vec3EuclideanNorm_nonneg _) 3)).mp hcenterTop
  unfold tsaiVelocityExcess
  rw [setIntegral_eq_toReal_setLIntegral_of_nonneg hcenterInt]
  · have hcenterEq :
        (∫⁻ w in parabolicCylinder z.1 z.2 r,
          ENNReal.ofReal (vec3EuclideanNorm
            (u w - ⨍ y in parabolicCylinder z.1 z.2 r, u y) ^ (3 : ℕ))) =
        ∫⁻ w in parabolicCylinder z.1 z.2 r,
          ENNReal.ofReal (vec3EuclideanNorm
            (u w - ⨍ y in parabolicCylinder z.1 z.2 r, u y)) ^ (3 : ℝ) := by
      apply lintegral_congr
      intro w
      rw [ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _) 3]
      norm_num [ENNReal.rpow_natCast]
    rw [hcenterEq]
    have hscale : r⁻¹ ^ (2 : ℕ) = r ^ (-2 : ℝ) := by
      rw [Real.rpow_neg (le_of_lt hr)]
      norm_num [inv_pow]
    calc
      r⁻¹ ^ (2 : ℕ) *
          (∫⁻ w in parabolicCylinder z.1 z.2 r,
            ENNReal.ofReal (vec3EuclideanNorm
              (u w - ⨍ y in parabolicCylinder z.1 z.2 r, u y)) ^ (3 : ℝ)).toReal ≤
        r⁻¹ ^ (2 : ℕ) *
          (8 * (∫⁻ w in parabolicCylinder z.1 z.2 r,
            ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal) :=
        mul_le_mul_of_nonneg_left hreal (by positivity)
      _ = 8 * gamma u z r ^ (3 : ℕ) := by
        rw [hscale]
        calc
          r ^ (-2 : ℝ) *
              (8 * (∫⁻ w in parabolicCylinder z.1 z.2 r,
                ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal) =
              8 * (r ^ (-2 : ℝ) *
                (∫⁻ w in parabolicCylinder z.1 z.2 r,
                  ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal) := by ring
          _ = 8 * gamma u z r ^ (3 : ℕ) := by
            rw [← gamma_cube_eq u z r hr]
  · exact Filter.Eventually.of_forall (fun w => by
      change 0 ≤ vec3EuclideanNorm
        (u w - ⨍ y in parabolicCylinder z.1 z.2 r, u y) ^ (3 : ℕ)
      exact pow_nonneg (vec3EuclideanNorm_nonneg _) 3)

lemma meanFreeVec_eq_sub_spatialAverage
    {u : ParabolicPoint → Vec3} {x : Vec3} {r s : ℝ}
    (hu : IntegrableOn (fun y : Vec3 => u (y,s)) (vec3Ball x r) volume) :
    (fun y : Vec3 => meanFreeVec u x r s y) =
      (fun y => u (y,s) - ⨍ z in vec3Ball x r, u (z,s)) := by
  funext y; funext i
  unfold meanFreeVec meanFreeComponent
  change u (y,s) i - average (volume.restrict (vec3Ball x r)) (fun z => u (z,s) i) =
    u (y,s) i - (⨍ z in vec3Ball x r, u (z,s)) i
  congr 1
  rw [MeasureTheory.average_eq]
  simp only [MeasureTheory.measureReal_restrict_apply_univ]
  rw [MeasureTheory.setAverage_eq (μ := (volume : Measure Vec3))
    (f := fun z : Vec3 => u (z, s)) (s := vec3Ball x r)]
  rw [Pi.smul_apply]
  have hcomp := ContinuousLinearMap.integral_comp_comm
    (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ) hu
  have hcomp' := congrArg (fun v : ℝ =>
    (volume.real (vec3Ball x r))⁻¹ • v) hcomp
  simpa only [ContinuousLinearMap.proj_apply] using hcomp'

private lemma ball_vec_excess_lintegral_bound
    {u : ParabolicPoint → Vec3} {x : Vec3} {r s : ℝ}
    (hr : 0 < r)
    (hu : IntegrableOn (fun y : Vec3 => u (y,s)) (vec3Ball x r) volume)
    (hu3 : IntegrableOn (fun y : Vec3 => vec3EuclideanNorm (u (y,s)) ^ (3 : ℕ))
      (vec3Ball x r) volume) :
    (∫⁻ y in vec3Ball x r, ENNReal.ofReal
      (vec3EuclideanNorm (u (y,s) - ⨍ z in vec3Ball x r, u (z,s))) ^ (3 : ℝ)) ≤
      8 * (∫⁻ y in vec3Ball x r, ENNReal.ofReal
        (vec3EuclideanNorm (u (y,s))) ^ (3 : ℝ)) := by
  let L := (PiLp.continuousLinearEquiv (2 : ℝ≥0∞) ℝ
    (fun _ : Fin 3 => ℝ)).symm
  have hLint : IntegrableOn (fun y : Vec3 => L (u (y,s)))
      (vec3Ball x r) volume := L.toContinuousLinearMap.integrable_comp hu.integrable
  have hL3 : IntegrableOn (fun y : Vec3 => ‖L (u (y,s))‖ ^ (3 : ℕ))
      (vec3Ball x r) volume := by
    simpa only [vec3EuclideanNorm_eq_l2,
      show (L : Vec3 → L2Vec3) = WithLp.toLp 2 by rfl] using hu3
  have h := setLaverage_norm_sub_setAverage_rpow_le
    (f := fun y : Vec3 => L (u (y,s))) (p := (3 : ℝ)) (c := (0 : L2Vec3))
    (by norm_num) (volume_vec3Ball_pos hr)
    (volume_vec3Ball_lt_top (x := x) (r := r)) hLint (by simpa using hL3)
  have hmap : L (⨍ y in vec3Ball x r, u (y,s)) =
      ⨍ y in vec3Ball x r, L (u (y,s)) := by
    rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
    change L ((volume (vec3Ball x r)).toReal⁻¹ • ∫ y in vec3Ball x r, u (y,s)) =
      (volume (vec3Ball x r)).toReal⁻¹ • ∫ y in vec3Ball x r, L (u (y,s))
    rw [map_smul, L.integral_comp_comm]
  rw [← hmap] at h
  simp only [← map_sub] at h
  rw [MeasureTheory.setLAverage_eq, MeasureTheory.setLAverage_eq] at h
  have h' := h
  norm_num [ENNReal.rpow_natCast] at h'
  have h'' :
      (∫⁻ y in vec3Ball x r, ‖L (u (y,s) - ⨍ z in vec3Ball x r, u (z,s))‖ₑ ^ (3 : ℝ)) /
        volume (vec3Ball x r) ≤
      (8 * (∫⁻ y in vec3Ball x r, ‖L (u (y,s))‖ₑ ^ (3 : ℝ))) /
        volume (vec3Ball x r) := by
    simpa [map_sub, sub_zero, mul_div_assoc, Real.rpow_natCast] using h'
  have hp := volume_vec3Ball_pos (x := x) (r := r) hr
  have ht := volume_vec3Ball_lt_top (x := x) (r := r)
  have hraw :
      (∫⁻ y in vec3Ball x r, ‖L (u (y,s) - ⨍ z in vec3Ball x r, u (z,s))‖ₑ ^ (3 : ℝ)) ≤
      8 * (∫⁻ y in vec3Ball x r, ‖L (u (y,s))‖ₑ ^ (3 : ℝ)) := by
    calc
      _ = ((∫⁻ y in vec3Ball x r, ‖L (u (y,s) - ⨍ z in vec3Ball x r, u (z,s))‖ₑ ^ (3 : ℝ)) /
          volume (vec3Ball x r)) * volume (vec3Ball x r) := by rw [ENNReal.div_mul_cancel hp.ne'
            ht.ne]
      _ ≤ ((8 : ℝ≥0∞) * (∫⁻ y in vec3Ball x r, ‖L (u (y,s))‖ₑ ^ (3 : ℝ)) /
          volume (vec3Ball x r)) * volume (vec3Ball x r) := mul_le_mul_of_nonneg_right h'' (by
            positivity)
      _ = 8 * (∫⁻ y in vec3Ball x r, ‖L (u (y,s))‖ₑ ^ (3 : ℝ)) := ENNReal.div_mul_cancel hp.ne'
        ht.ne
  convert hraw using 1 <;> simp [vec3EuclideanNorm_eq_l2,
    show (L : Vec3 → L2Vec3) = WithLp.toLp 2 by rfl, ofReal_norm]

lemma meanFreeVec_aemeasurable
    {u : ParabolicPoint → Vec3} {x : Vec3} {r : ℝ} {T : Set ℝ}
    (hU : AEStronglyMeasurable u
      ((volume.restrict (vec3Ball x r)).prod (volume.restrict T))) :
    AEStronglyMeasurable (fun w : Vec3 × ℝ => meanFreeVec u x r w.2 w.1)
      ((volume.restrict (vec3Ball x r)).prod (volume.restrict T)) := by
  let μ := (volume.restrict (vec3Ball x r)).prod (volume.restrict T)
  have hcomp : ∀ i : Fin 3, AEStronglyMeasurable (fun w : Vec3 × ℝ => u w i) μ := by
    intro i
    exact (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hU
  have havg : ∀ i : Fin 3, AEStronglyMeasurable
      (fun s : ℝ => average (volume.restrict (vec3Ball x r))
        (fun y : Vec3 => u (y,s) i)) (volume.restrict T) := by
    intro i
    have hi := (hcomp i).prod_swap.integral_prod_right'
    convert hi.const_smul ((volume (vec3Ball x r)).toReal⁻¹) using 1
    · funext s
      rw [MeasureTheory.average_eq (μ := volume.restrict (vec3Ball x r))]
      simp only [MeasureTheory.measureReal_restrict_apply_univ]
      rfl
  have hcoord : ∀ i : Fin 3, AEStronglyMeasurable
      (fun w : Vec3 × ℝ => u w i - average (volume.restrict (vec3Ball x r))
        (fun y : Vec3 => u (y,w.2) i)) μ := by
    intro i
    have hsnd := Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (vec3Ball x r)) (ν := volume.restrict T)
    have hm := (havg i).comp_quasiMeasurePreserving hsnd
    change AEStronglyMeasurable ((fun w : Vec3 × ℝ => u w i) -
      (fun w : Vec3 × ℝ => average (volume.restrict (vec3Ball x r))
        (fun y : Vec3 => u (y,w.2) i))) μ
    simpa [Function.comp_def, Prod.swap_prod_mk] using (hcomp i).sub hm
  change AEStronglyMeasurable (fun w : Vec3 × ℝ => fun i =>
    u w i - average (volume.restrict (vec3Ball x r))
      (fun y : Vec3 => u (y,w.2) i)) μ
  apply aestronglyMeasurable_iff_aemeasurable.mpr
  apply aemeasurable_pi_iff.mpr
  intro i
  exact (hcoord i).aemeasurable

private lemma pressureChat_le_eight_hrawprod_1 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {r : ℝ},
      let B : Set Vec3 := vec3Ball z.1 r;
      let T : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
      (∀ᵐ (s : ℝ) ∂volume.restrict T,
          ∫⁻ (v : Vec3) in B,
              ENNReal.ofReal (vec3EuclideanNorm (meanFreeVec u z.1 r s v)) ^ (3 : ℝ) ≤
            (8 : ℝ≥0∞) *
              ∫⁻ (v : Vec3) in B, ENNReal.ofReal (vec3EuclideanNorm (u (v, s))) ^ (3 : ℝ)) →
        AEMeasurable
            (fun (w : Vec3 × ℝ) =>
              ENNReal.ofReal (vec3EuclideanNorm (meanFreeVec u z.1 r w.2 w.1)) ^ (3 : ℝ))
            ((volume.prod volume).restrict (B ×ˢ T)) →
          AEMeasurable (fun (w : Vec3 × ℝ) => ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ))
              ((volume.prod volume).restrict (B ×ˢ T)) →
            ∫⁻ (w : Vec3 × ℝ) in B ×ˢ T,
                ENNReal.ofReal (vec3EuclideanNorm (meanFreeVec u z.1 r w.2 w.1)) ^ (3 : ℝ) ≤
              (8 : ℝ≥0∞) *
                ∫⁻ (w : Vec3 × ℝ) in B ×ˢ T, ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)
    := by
  intro u z r B T hgood' hFmeas' hU3meas'
  change (∫⁻ w in B ×ˢ T, ENNReal.ofReal
    (vec3EuclideanNorm (meanFreeVec u z.1 r w.2 w.1)) ^ (3 : ℝ) ∂
      ((volume : Measure Vec3).prod (volume : Measure ℝ))) ≤
    8 * (∫⁻ w in B ×ˢ T, ENNReal.ofReal
      (vec3EuclideanNorm (u w)) ^ (3 : ℝ) ∂
      ((volume : Measure Vec3).prod (volume : Measure ℝ)))
  have hFub := setLIntegral_prod_symm
    (fun w : Vec3 × ℝ => ENNReal.ofReal
      (vec3EuclideanNorm (meanFreeVec u z.1 r w.2 w.1)) ^ (3 : ℝ)) hFmeas'
  have hU3ub := setLIntegral_prod_symm
    (fun w : Vec3 × ℝ => ENNReal.ofReal
      (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) hU3meas'
  have hFub' : (∫⁻ w in B ×ˢ T, ENNReal.ofReal
      (vec3EuclideanNorm (meanFreeVec u z.1 r w.2 w.1)) ^ (3 : ℝ) ∂
        ((volume : Measure Vec3).prod (volume : Measure ℝ))) =
      ∫⁻ s in T, ∫⁻ v in B, ENNReal.ofReal
        (vec3EuclideanNorm (meanFreeVec u z.1 r s v)) ^ (3 : ℝ) := by
    simpa only [Prod.fst, Prod.snd] using hFub
  have hU3ub' : (∫⁻ w in B ×ˢ T, ENNReal.ofReal
      (vec3EuclideanNorm (u w)) ^ (3 : ℝ) ∂
        ((volume : Measure Vec3).prod (volume : Measure ℝ))) =
      ∫⁻ s in T, ∫⁻ v in B, ENNReal.ofReal
        (vec3EuclideanNorm (u (v,s))) ^ (3 : ℝ) := by
    simpa only [Prod.fst, Prod.snd] using hU3ub
  calc
    _ = ∫⁻ s in T, ∫⁻ v in B, ENNReal.ofReal
        (vec3EuclideanNorm (meanFreeVec u z.1 r s v)) ^ (3 : ℝ) := by
          exact hFub'
    _ ≤ ∫⁻ s in T, 8 * (∫⁻ v in B, ENNReal.ofReal
        (vec3EuclideanNorm (u (v,s))) ^ (3 : ℝ)) := lintegral_mono_ae hgood'
    _ = 8 * (∫⁻ s in T, ∫⁻ v in B, ENNReal.ofReal
        (vec3EuclideanNorm (u (v,s))) ^ (3 : ℝ)) := by rw [lintegral_const_mul' 8 _ (by norm_num)]
    _ = 8 * (∫⁻ w in B ×ˢ T, ENNReal.ofReal
        (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) := by
          exact congrArg (fun x => 8 * x) hU3ub'.symm

private lemma pressureChat_le_eight_hChatMeas_2 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {r : ℝ},
      let _ : Set Vec3 := vec3Ball z.1 r;
      let T : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
      AEStronglyMeasurable (fun (w : Vec3 × ℝ) => meanFreeVec u z.1 r w.2 w.1)
          ((volume.restrict (vec3Ball z.1 r)).prod (volume.restrict T)) →
        AEStronglyMeasurable
          (fun (w : ParabolicPoint) => vec3EuclideanNorm (meanFreeVec u z.1 r w.2 w.1) ^ (3 : ℕ))
          (volume.restrict (parabolicCylinder z.1 z.2 r))
    := by
  intro u z r B T hmeanfree
  rw [parabolicCylinder, volume_parabolicPoint_eq_prod]
  change AEStronglyMeasurable
    (fun w : Vec3 × ℝ => vec3EuclideanNorm
      (meanFreeVec u z.1 r w.2 w.1) ^ (3 : ℕ))
    (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
      (B ×ˢ T))
  rw [← Measure.prod_restrict]
  simpa [B, T] using (by
    have hc : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact (hc.comp_aestronglyMeasurable hmeanfree).pow 3)

lemma pressureChat_le_eight_of_integrability
    {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {r : ℝ}
    (hr : 0 < r)
    (hu : IntegrableOn u (parabolicCylinder z.1 z.2 r) volume)
    (hu3 : IntegrableOn (fun w => vec3EuclideanNorm (u w) ^ (3 : ℕ))
      (parabolicCylinder z.1 z.2 r) volume) :
    pressureChat u z r ≤ 8 * gamma u z r ^ (3 : ℕ) := by
  let B : Set Vec3 := vec3Ball z.1 r
  let T : Set ℝ := Ioc (z.2 - r ^ 2) z.2
  have hu' : Integrable u ((volume.restrict B).prod (volume.restrict T)) := by
    rw [Measure.prod_restrict]
    change IntegrableOn u (vec3Ball z.1 r ×ˢ Ioc (z.2-r^2) z.2)
      ((volume : Measure Vec3).prod (volume : Measure ℝ))
    exact hu
  have hu3' : Integrable (fun w => vec3EuclideanNorm (u w) ^ (3 : ℕ))
      ((volume.restrict B).prod (volume.restrict T)) := by
    rw [Measure.prod_restrict]
    change IntegrableOn (fun w => vec3EuclideanNorm (u w) ^ (3 : ℕ))
      (vec3Ball z.1 r ×ˢ Ioc (z.2-r^2) z.2)
      ((volume : Measure Vec3).prod (volume : Measure ℝ))
    exact hu3
  have hUmeas := hu'.aestronglyMeasurable
  have hmeanfree := meanFreeVec_aemeasurable hUmeas
  have hFmeas : AEMeasurable (fun w : Vec3 × ℝ => ENNReal.ofReal
      (vec3EuclideanNorm (meanFreeVec u z.1 r w.2 w.1)) ^ (3 : ℝ))
      ((volume.restrict B).prod (volume.restrict T)) := by
    have hc : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact (hc.comp_aestronglyMeasurable hmeanfree).aemeasurable.ennreal_ofReal.pow_const _
  have hU3meas : AEMeasurable (fun w : Vec3 × ℝ => ENNReal.ofReal
      (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ((volume.restrict B).prod (volume.restrict T)) := by
    have hc : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact (hc.comp_aestronglyMeasurable hUmeas).aemeasurable.ennreal_ofReal.pow_const _
  have hsliceU := hu'.prod_left_ae
  have hsliceU3 := hu3'.prod_left_ae
  have hgood : ∀ᵐ s ∂volume.restrict T, (∫⁻ v in B, ENNReal.ofReal
      (vec3EuclideanNorm (u (v,s) - ⨍ w in B, u (w,s))) ^ (3 : ℝ)) ≤
      8 * (∫⁻ v in B, ENNReal.ofReal (vec3EuclideanNorm (u (v,s))) ^ (3 : ℝ)) := by
    filter_upwards [hsliceU, hsliceU3] with s hs hs3
    have hh := ball_vec_excess_lintegral_bound hr hs hs3
    exact hh
  have hgood' : ∀ᵐ s ∂volume.restrict T, (∫⁻ v in B,
      ENNReal.ofReal (vec3EuclideanNorm (meanFreeVec u z.1 r s v)) ^ (3 : ℝ)) ≤
      8 * (∫⁻ v in B, ENNReal.ofReal (vec3EuclideanNorm (u (v,s))) ^ (3 : ℝ)) := by
    filter_upwards [hgood, hsliceU] with s hs hsU
    have heq := meanFreeVec_eq_sub_spatialAverage hsU
    convert hs using 1
    · apply lintegral_congr
      intro v
      rw [congrFun heq v]
  have hFmeas' : AEMeasurable (fun w : Vec3 × ℝ => ENNReal.ofReal
      (vec3EuclideanNorm (meanFreeVec u z.1 r w.2 w.1)) ^ (3 : ℝ))
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict (B ×ˢ T)) := by
    rw [← Measure.prod_restrict]
    exact hFmeas
  have hU3meas' : AEMeasurable (fun w : Vec3 × ℝ => ENNReal.ofReal
      (vec3EuclideanNorm (u w)) ^ (3 : ℝ))
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict (B ×ˢ T)) := by
    rw [← Measure.prod_restrict]
    exact hU3meas
  have hrawprod := @pressureChat_le_eight_hrawprod_1 u z r hgood' hFmeas' hU3meas'
  have hraw : (∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal
      (vec3EuclideanNorm (meanFreeVec u z.1 r w.2 w.1)) ^ (3 : ℝ)) ≤
      8 * (∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal
        (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) := by
    rw [parabolicCylinder, volume_parabolicPoint_eq_prod]
    change (∫⁻ w in B ×ˢ T, ENNReal.ofReal
      (vec3EuclideanNorm (meanFreeVec u z.1 r w.2 w.1)) ^ (3 : ℝ) ∂
        ((volume : Measure Vec3).prod (volume : Measure ℝ))) ≤
      8 * (∫⁻ w in B ×ˢ T, ENNReal.ofReal
        (vec3EuclideanNorm (u w)) ^ (3 : ℝ) ∂
        ((volume : Measure Vec3).prod (volume : Measure ℝ)))
    exact hrawprod
  have hChatMeas := @pressureChat_le_eight_hChatMeas_2 u z r hmeanfree
  have hU3MeasCyl : AEStronglyMeasurable
      (fun w : ParabolicPoint => vec3EuclideanNorm (u w) ^ (3 : ℕ))
      (volume.restrict (parabolicCylinder z.1 z.2 r)) := by
    rw [parabolicCylinder, volume_parabolicPoint_eq_prod]
    change AEStronglyMeasurable
      (fun w : Vec3 × ℝ => vec3EuclideanNorm (u w) ^ (3 : ℕ))
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (B ×ˢ T))
    rw [← Measure.prod_restrict]
    simpa [B, T] using (by
      have hc : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
        unfold vec3EuclideanNorm
        fun_prop
      exact (hc.comp_aestronglyMeasurable hUmeas).pow 3)
  have hU3Top : (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ⊤ := by
    have h := (lintegral_ofReal_ne_top_iff_integrable hU3MeasCyl
      (Eventually.of_forall fun w =>
        pow_nonneg (vec3EuclideanNorm_nonneg (u w)) 3)).2 hu3
    convert h using 1
    apply lintegral_congr
    intro w
    rw [ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _) 3]
    norm_num [ENNReal.rpow_natCast]
  have hChatTop : (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (vec3EuclideanNorm
        (meanFreeVec u z.1 r w.2 w.1) ^ (3 : ℕ))) ≠ ⊤ := by
    have hlt := lt_of_le_of_lt hraw
      (ENNReal.mul_lt_top (by norm_num) hU3Top.lt_top)
    convert ne_of_lt hlt using 1
    apply lintegral_congr
    intro w
    rw [ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _) 3]
    norm_num [ENNReal.rpow_natCast]
  have hChatInt := (lintegral_ofReal_ne_top_iff_integrable hChatMeas
    (Eventually.of_forall fun w =>
      pow_nonneg (vec3EuclideanNorm_nonneg (meanFreeVec u z.1 r w.2 w.1)) 3)).mp hChatTop
  have h8Top : (8 : ℝ≥0∞) *
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hU3Top
  have hcenterEq : (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (vec3EuclideanNorm
        (meanFreeVec u z.1 r w.2 w.1) ^ (3 : ℕ))) =
      ∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm
          (meanFreeVec u z.1 r w.2 w.1)) ^ (3 : ℝ) := by
    apply lintegral_congr
    intro w
    rw [ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _) 3]
    norm_num [ENNReal.rpow_natCast]
  have hraw' : (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (vec3EuclideanNorm
        (meanFreeVec u z.1 r w.2 w.1) ^ (3 : ℕ))) ≤
      8 * (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) := by
    rw [hcenterEq]
    exact hraw
  have hrawReal : (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (vec3EuclideanNorm
        (meanFreeVec u z.1 r w.2 w.1)) ^ (3 : ℝ)).toReal ≤
      8 * (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal := by
    have h := (ENNReal.toReal_le_toReal hChatTop h8Top).2 hraw'
    rw [hcenterEq] at h
    rw [ENNReal.toReal_mul] at h
    simpa using h
  unfold pressureChat
  rw [setIntegral_eq_toReal_setLIntegral_of_nonneg hChatInt
    (Eventually.of_forall fun w => pow_nonneg
      (vec3EuclideanNorm_nonneg (meanFreeVec u z.1 r w.2 w.1)) 3), hcenterEq]
  have hscale : r⁻¹ ^ (2 : ℕ) = r ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hr.le]
    norm_num [inv_pow]
  rw [hscale]
  calc
    r ^ (-2 : ℝ) *
        (∫⁻ w in parabolicCylinder z.1 z.2 r,
          ENNReal.ofReal (vec3EuclideanNorm
            (meanFreeVec u z.1 r w.2 w.1)) ^ (3 : ℝ)).toReal ≤
      r ^ (-2 : ℝ) *
        (8 * (∫⁻ w in parabolicCylinder z.1 z.2 r,
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal) := by
      exact mul_le_mul_of_nonneg_left hrawReal (by positivity)
    _ = 8 * (r ^ (-2 : ℝ) *
        (∫⁻ w in parabolicCylinder z.1 z.2 r,
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal) := by ring
    _ = 8 * gamma u z r ^ (3 : ℕ) := by
      rw [← gamma_cube_eq u z r hr]

theorem pressureChat_le_eight_gamma_cube
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    pressureChat u z r ≤ 8 * gamma u z r ^ (3 : ℕ) := by
  exact pressureChat_le_eight_of_integrability hr
    (sws_integrable_velocity_on_cylinder hsol hr hsub)
    (sws_integrable_velocity_cube_on_cylinder hsol hr hsub)

/-- Integrability of the velocity on a contained parabolic cylinder. -/
theorem tsai_integrable_velocity_on_cylinder
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    IntegrableOn u (parabolicCylinder z.1 z.2 r) volume := by
  exact sws_integrable_velocity_on_cylinder hsol hr hsub

/-- Cubic velocity integrability on a contained parabolic cylinder. -/
theorem tsai_integrable_velocity_cube_on_cylinder
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    IntegrableOn (fun w => vec3EuclideanNorm (u w) ^ (3 : ℕ))
      (parabolicCylinder z.1 z.2 r) volume := by
  exact sws_integrable_velocity_cube_on_cylinder hsol hr hsub



end CKN

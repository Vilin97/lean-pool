/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.UpperSemicontinuity
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SliceIntegrability
public import LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Cylinders
public import Mathlib.MeasureTheory.Measure.ContinuousPreimage
public import Mathlib.MeasureTheory.Group.Prod
public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.ThetaUpperSemicontinuityBasic
public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.ThetaUpperSemicontinuityAlpha

/-!
# Theta Upper Semicontinuity

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN


/-- The scale quantities have the base-point semicontinuity and continuity used
in the Step 2 transfer argument. -/
theorem theta_usc_of_sws_with_alpha_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z₀ : ParabolicPoint} {rho R : ℝ} (hrho : 0 < rho) (hrhoR : rho < R)
    (hrect : euclideanClosedBall z₀.1 R ×ˢ Icc (z₀.2 - R ^ 2) z₀.2 ⊆
      spaceTimeSet Ω I) (ht₀ : z₀.2 ∈ I) :
    Filter.limsup (fun z : ParabolicPoint => alpha u z rho ^ 2) (𝓝 z₀) ≤
        (R / rho) * alpha u z₀ R ^ 2 ∧
      Tendsto (fun z => beta u Du z rho) (𝓝 z₀)
        (𝓝 (beta u Du z₀ rho)) ∧
      Tendsto (fun z => delta p z rho) (𝓝 z₀)
        (𝓝 (delta p z₀ rho)) ∧
      IsBoundedUnder (· ≤ ·) (𝓝 z₀)
        (fun z : ParabolicPoint => alpha u z rho ^ 2) := by
  have hR : 0 < R := lt_trans hrho hrhoR
  have hgap : 0 < R ^ 2 - rho ^ 2 := by nlinarith only [hR, hrho, hrhoR]
  let r : ℝ := (rho + R) / 2
  have hrr : rho < r := by dsimp [r]; linarith only [hrhoR]
  have hrrR : r < R := by dsimp [r]; linarith only [hrhoR]
  have hsub0 : closure (parabolicCylinder z₀.1 z₀.2 R) ⊆
      spaceTimeSet Ω I := by
    rw [closure_parabolicCylinder hR]
    intro z hz
    apply hrect
    exact ⟨mem_euclideanClosedBall_of_vec3Norm_le hR.le hz.1, hz.2⟩
  have hrpos : 0 < r := lt_trans hrho hrr
  have hαusc := alpha_usc_of_sws hsol hrpos hrrR
    (by nlinarith only [hR]) hrect
  have hS0 : essSup (timeSliceBallEnergy z₀.1 R ·
      (fun w => vec3EuclideanNorm (u w)))
      (volume.restrict (Ioc (z₀.2 - R ^ 2) z₀.2)) ≠ ⊤ :=
    ne_of_lt (sws_timeSliceBallEnergy_essSup_lt_top hsol hR
      (by nlinarith only [hR]) hrect)
  obtain ⟨ε, hε, hεI⟩ := Metric.mem_nhds_iff.mp
    (hsol.2.1.mem_nhds ht₀)
  let h₁ : ℝ := min (ε / 2) (R ^ 2 / 2)
  have hh₁ : 0 < h₁ := by
    dsimp [h₁]
    exact lt_min (by positivity) (by positivity)
  have hh₁R : h₁ < R ^ 2 := by
    dsimp [h₁]
    exact lt_of_le_of_lt (min_le_right _ _) (by nlinarith only [hR])
  have ht₁I : z₀.2 + h₁ ∈ I := by
    apply hεI
    apply Metric.mem_ball'.2
    rw [Real.dist_eq, show z₀.2 - (z₀.2 + h₁) = -h₁ by ring,
      abs_neg, abs_of_nonneg hh₁.le]
    dsimp [h₁]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hsubAt : ∀ {h : ℝ}, 0 ≤ h → h ≤ h₁ →
      closure (parabolicCylinder z₀.1 (z₀.2 + h) R) ⊆
        spaceTimeSet Ω I := by
    intro h hh hhh
    rw [closure_parabolicCylinder hR]
    intro z hz
    have hlow : z₀.2 - R ^ 2 ≤ z₀.2 + h - R ^ 2 := by linarith only [hh]
    have hupperI : z₀.2 + h ∈ I := by
      apply hsol.2.2.1.out ht₀ ht₁I
      exact ⟨le_add_of_nonneg_right hh, add_le_add_right hhh _⟩
    have htime : z.2 ∈ I := by
      rcases le_total z.2 z₀.2 with hleft | hright
      · exact (hrect ⟨mem_euclideanClosedBall_of_vec3Norm_le hR.le
          hz.1, ⟨by linarith only [hz.2.1, hh], hleft⟩⟩).2
      · exact hsol.2.2.1.out ht₀ hupperI ⟨hright, hz.2.2⟩
    have hspace : z.1 ∈ Ω := by
      have hz0 : (z.1, z₀.2) ∈
        euclideanClosedBall z₀.1 R ×ˢ Icc (z₀.2 - R ^ 2) z₀.2 := by
        exact ⟨mem_euclideanClosedBall_of_vec3Norm_le hR.le hz.1,
          ⟨sub_le_self _ (sq_nonneg R), le_rfl⟩⟩
      exact (hrect hz0).1
    exact ⟨hspace, htime⟩
  obtain ⟨Ωo, Jo, hboxo, hco⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hR (by
      simpa only [add_zero] using (hsubAt (h := 0) (by norm_num) hh₁.le))
  obtain ⟨Ωf, Jf, hboxf, hcf⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hR (hsubAt (h := h₁) hh₁.le le_rfl)
  let Wold : Set ParabolicPoint :=
    vec3Ball z₀.1 R ×ˢ Ioo (z₀.2 - R ^ 2) z₀.2
  let Wfuture : Set ParabolicPoint :=
    vec3Ball z₀.1 R ×ˢ Ioo (z₀.2 + h₁ - R ^ 2) (z₀.2 + h₁)
  have hWoldopen : IsOpen Wold := by
    dsimp [Wold]
    change IsOpen (parabolicHomeomorph ⁻¹'
      (vec3Ball z₀.1 R ×ˢ Ioo (z₀.2 - R ^ 2) z₀.2))
    exact (isOpen_vec3Ball _ _).prod isOpen_Ioo |>.preimage
      parabolicHomeomorph.continuous
  have hWfutureopen : IsOpen Wfuture := by
    dsimp [Wfuture]
    change IsOpen (parabolicHomeomorph ⁻¹'
      (vec3Ball z₀.1 R ×ˢ Ioo (z₀.2 + h₁ - R ^ 2) (z₀.2 + h₁)))
    exact (isOpen_vec3Ball _ _).prod isOpen_Ioo |>.preimage
      parabolicHomeomorph.continuous
  have hWoldcyl : Wold ⊆ parabolicCylinder z₀.1 z₀.2 R := by
    intro z hz
    dsimp [Wold] at hz ⊢
    exact ⟨hz.1, hz.2.1, hz.2.2.le⟩
  have hWfuturecyl : Wfuture ⊆
      parabolicCylinder z₀.1 (z₀.2 + h₁) R := by
    intro z hz
    dsimp [Wfuture] at hz ⊢
    exact ⟨hz.1, hz.2.1, hz.2.2.le⟩
  have hco0 : parabolicCylinder z₀.1 z₀.2 R ⊆ spaceTimeSet Ωo Jo := by
    simpa only [add_zero] using hco
  have hWoldbox : Wold ⊆ spaceTimeSet Ωo Jo := hWoldcyl.trans hco0
  have hWfuturebox : Wfuture ⊆ spaceTimeSet Ωf Jf := hWfuturecyl.trans hcf
  have hballo : vec3Ball z₀.1 R ⊆ Ωo := by
    intro x hx
    have hx' : ((x, z₀.2) : ParabolicPoint) ∈
        parabolicCylinder z₀.1 z₀.2 R := by
      rw [parabolicCylinder]
      exact ⟨hx, ⟨by linarith only [hh₁, hh₁R], le_rfl⟩⟩
    exact (hco0 hx').1
  have hballf : vec3Ball z₀.1 R ⊆ Ωf := by
    intro x hx
    have hx' : ((x, z₀.2 + h₁) : ParabolicPoint) ∈
        parabolicCylinder z₀.1 (z₀.2 + h₁) R := by
      rw [parabolicCylinder]
      exact ⟨hx, ⟨by linarith only [hh₁, hh₁R], le_rfl⟩⟩
    exact (hcf hx').1
  have hK : closure (parabolicCylinder z₀.1 z₀.2 rho) ⊆ Wold ∪ Wfuture := by
    rw [closure_parabolicCylinder hrho]
    intro z hz
    have hsp : z.1 ∈ vec3Ball z₀.1 R := by
      rw [mem_vec3Ball]
      exact lt_of_le_of_lt hz.1 hrhoR
    rcases lt_or_eq_of_le hz.2.2 with hlt | heq
    · exact Or.inl ⟨hsp, ⟨by linarith only [hz.2.1, hgap], hlt⟩⟩
    · exact Or.inr ⟨hsp, ⟨by linarith only [hh₁R, heq], by linarith only [hh₁, heq]⟩⟩
  let G : Set ParabolicPoint := Wold ∪ Wfuture
  have hGopen : IsOpen G := hWoldopen.union hWfutureopen
  have hgradmeasO : AEStronglyMeasurable (fun w => spatialGradientSq u Du w)
      (volume.restrict (spaceTimeSet Ωo Jo)) := by
    have hDu := (hsol.2.2.2.2.2.1 Ωo Jo hboxo).2.1
    have hc : Continuous (fun v : Fin 3 → Vec3 =>
        ∑ i, ∑ j, (v i j) ^ (2 : ℕ)) := by fun_prop
    have hm := hc.comp_aestronglyMeasurable hDu
    simpa [spatialGradientSq, Function.comp_def] using hm
  have hgradmeasF : AEStronglyMeasurable (fun w => spatialGradientSq u Du w)
      (volume.restrict (spaceTimeSet Ωf Jf)) := by
    have hDu := (hsol.2.2.2.2.2.1 Ωf Jf hboxf).2.1
    have hc : Continuous (fun v : Fin 3 → Vec3 =>
        ∑ i, ∑ j, (v i j) ^ (2 : ℕ)) := by fun_prop
    have hm := hc.comp_aestronglyMeasurable hDu
    simpa [spatialGradientSq, Function.comp_def] using hm
  have hgradIntO : IntegrableOn (fun w => spatialGradientSq u Du w) Wold volume := by
    apply gradient_integrable_of_meas hgradmeasO hWoldbox
    have hsubo : closure (parabolicCylinder z₀.1 z₀.2 R) ⊆
        spaceTimeSet Ω I := by
      simpa only [add_zero] using
        (hsubAt (h := 0) (by norm_num) hh₁.le)
    exact (ne_of_lt (lt_of_le_of_lt (lintegral_mono_set hWoldcyl)
      (sws_gradient_integral_lt_top hsol hR hsubo)))
  have hgradIntF : IntegrableOn (fun w => spatialGradientSq u Du w) Wfuture volume := by
    apply gradient_integrable_of_meas hgradmeasF hWfuturebox
    have hsubf : closure (parabolicCylinder z₀.1 (z₀.2 + h₁) R) ⊆
        spaceTimeSet Ω I := hsubAt (h := h₁) hh₁.le le_rfl
    exact (ne_of_lt (lt_of_le_of_lt (lintegral_mono_set hWfuturecyl)
      (sws_gradient_integral_lt_top hsol (z := (z₀.1, z₀.2 + h₁)) hR hsubf)))
  have hgradInt : IntegrableOn (fun w => spatialGradientSq u Du w) G volume := by
    exact hgradIntO.union hgradIntF
  have hpmeasO : AEStronglyMeasurable (fun w => |p w| ^ (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet Ωo Jo)) := by
    have hp := (hsol.2.2.2.2.2.1 Ωo Jo hboxo).2.2.1
    have hc := (Real.continuous_rpow_const
      (by norm_num : (0 : ℝ) ≤ 3 / 2)).comp continuous_abs
    exact hc.comp_aestronglyMeasurable hp
  have hpmeasF : AEStronglyMeasurable (fun w => |p w| ^ (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet Ωf Jf)) := by
    have hp := (hsol.2.2.2.2.2.1 Ωf Jf hboxf).2.2.1
    have hc := (Real.continuous_rpow_const
      (by norm_num : (0 : ℝ) ≤ 3 / 2)).comp continuous_abs
    exact hc.comp_aestronglyMeasurable hp
  have hpIntO : IntegrableOn (fun w => |p w| ^ (3 / 2 : ℝ)) Wold volume := by
    apply pressure_integrable_of_meas hpmeasO hWoldbox
    have htop := sws_pressure_integral_lt_top hsol hR (by
      simpa only [add_zero] using
        (hsubAt (h := 0) (by norm_num) hh₁.le))
    have hcongr : (∫⁻ w in parabolicCylinder z₀.1 z₀.2 R,
        ENNReal.ofReal (|p w| ^ (3 / 2 : ℝ))) =
        ∫⁻ w in parabolicCylinder z₀.1 z₀.2 R,
          ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) :=
      lintegral_congr (fun w =>
        (ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (p w))
          (by norm_num : (0 : ℝ) ≤ 3 / 2)).symm)
    rw [← hcongr] at htop
    exact (ne_of_lt (lt_of_le_of_lt (lintegral_mono_set hWoldcyl)
      htop))
  have hpIntF : IntegrableOn (fun w => |p w| ^ (3 / 2 : ℝ)) Wfuture volume := by
    apply pressure_integrable_of_meas hpmeasF hWfuturebox
    have hsubf : closure (parabolicCylinder z₀.1 (z₀.2 + h₁) R) ⊆
        spaceTimeSet Ω I := hsubAt (h := h₁) hh₁.le le_rfl
    have htop := sws_pressure_integral_lt_top hsol
      (z := (z₀.1, z₀.2 + h₁)) hR hsubf
    have hcongr : (∫⁻ w in parabolicCylinder z₀.1 (z₀.2 + h₁) R,
        ENNReal.ofReal (|p w| ^ (3 / 2 : ℝ))) =
        ∫⁻ w in parabolicCylinder z₀.1 (z₀.2 + h₁) R,
          ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) :=
      lintegral_congr (fun w =>
        (ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (p w))
          (by norm_num : (0 : ℝ) ≤ 3 / 2)).symm)
    rw [← hcongr] at htop
    have htop' : (∫⁻ w in parabolicCylinder z₀.1 (z₀.2 + h₁) R,
        ENNReal.ofReal (|p w| ^ (3 / 2 : ℝ))) < ⊤ := by
      simpa only [Prod.fst, Prod.snd] using htop
    exact (ne_of_lt (lt_of_le_of_lt (lintegral_mono_set hWfuturecyl)
      htop'))
  have hpInt : IntegrableOn (fun w => |p w| ^ (3 / 2 : ℝ)) G volume := by
    exact hpIntO.union hpIntF
  have hgradT := cylinder_integral_tendsto_of_open hGopen hrho hK hgradInt
  have hpT := cylinder_integral_tendsto_of_open hGopen hrho hK hpInt
  have hβrepr : ∀ z : ParabolicPoint,
      closure (parabolicCylinder z.1 z.2 rho) ⊆ spaceTimeSet Ω I →
      parabolicCylinder z.1 z.2 rho ⊆ G →
      beta u Du z rho =
        (rho⁻¹ * ∫ w in parabolicCylinder z.1 z.2 rho,
          spatialGradientSq u Du w) ^ (1 / 2 : ℝ) := by
    intro z hz hzg
    have hiG : Integrable (fun w => spatialGradientSq u Du w)
        (volume.restrict G) := hgradInt
    have hi := hiG.mono_measure (Measure.restrict_mono hzg le_rfl)
    have hreal := integral_spatialGradientSq_eq_beta_sq u Du z hrho hi
    have hscale : rho⁻¹ * ∫ w in parabolicCylinder z.1 z.2 rho,
        spatialGradientSq u Du w = beta u Du z rho ^ 2 := by
      rw [hreal]
      field_simp
    have hb : 0 ≤ beta u Du z rho := by unfold beta; positivity
    calc
      beta u Du z rho = (beta u Du z rho ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_nonneg hb]
      _ = (rho⁻¹ * ∫ w in parabolicCylinder z.1 z.2 rho,
          spatialGradientSq u Du w) ^ (1 / 2 : ℝ) := by rw [hscale]
  have hδrepr : ∀ z : ParabolicPoint,
      closure (parabolicCylinder z.1 z.2 rho) ⊆ spaceTimeSet Ω I →
      parabolicCylinder z.1 z.2 rho ⊆ G →
      delta p z rho =
        (rho ^ (-2 : ℝ) * ∫ w in parabolicCylinder z.1 z.2 rho,
          |p w| ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) := by
    intro z hz hzg
    have hiG : Integrable (fun w => |p w| ^ (3 / 2 : ℝ))
        (volume.restrict G) := hpInt
    have hi := hiG.mono_measure (Measure.restrict_mono hzg le_rfl)
    have hreal := integral_abs_pow_eq_delta_cube p z hrho hi
    have hscale : rho ^ (-2 : ℝ) * ∫ w in parabolicCylinder z.1 z.2 rho,
        |p w| ^ (3 / 2 : ℝ) = delta p z rho ^ 3 := by
      rw [hreal]
      have hρ2 : rho ^ (2 : ℕ) = rho ^ (2 : ℝ) := by
        exact (Real.rpow_natCast rho 2).symm
      rw [hρ2]
      calc
        rho ^ (-2 : ℝ) * (rho ^ (2 : ℝ) * delta p z rho ^ 3) =
            (rho ^ (-2 : ℝ) * rho ^ (2 : ℝ)) * delta p z rho ^ 3 := by ring
        _ = delta p z rho ^ 3 := by
          rw [← Real.rpow_add hrho]
          norm_num
    have hd : 0 ≤ delta p z rho := by unfold delta; positivity
    calc
      delta p z rho = (delta p z rho ^ 3) ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hd]
        norm_num
      _ = (rho ^ (-2 : ℝ) * ∫ w in parabolicCylinder z.1 z.2 rho,
          |p w| ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) := by rw [hscale]
  have hopen : IsOpen (spaceTimeSet Ω I) :=
    isOpen_spaceTimeSet Ω I hsol.1 hsol.2.1
  have hKbar : closure (parabolicCylinder z₀.1 z₀.2 r) ⊆
      spaceTimeSet Ω I := by
    rw [closure_parabolicCylinder hrpos]
    intro w hw
    have hrsq : r ^ 2 < R ^ 2 := by nlinarith only [hrpos, hR, hrrR]
    have hw0 : (w.1, w.2) ∈
        euclideanClosedBall z₀.1 R ×ˢ Icc (z₀.2 - R ^ 2) z₀.2 := by
      exact ⟨mem_euclideanClosedBall_of_vec3Norm_le hR.le
          (le_trans hw.1 hrrR.le), ⟨by linarith only [hw.2.1, hrsq], hw.2.2⟩⟩
    exact hrect hw0
  have hGevent : ∀ᶠ z in 𝓝 z₀,
      parabolicCylinder z.1 z.2 rho ⊆ G :=
    eventually_cylinder_subset_of_open hrho hGopen hK
  have hcarevent : ∀ᶠ z in 𝓝 z₀,
      closure (parabolicCylinder z.1 z.2 rho) ⊆ spaceTimeSet Ω I := by
    have hev := eventually_cylinder_subset_of_open hrpos hopen hKbar
    filter_upwards [hev] with z hz
    intro w hw
    apply hz
    rw [closure_parabolicCylinder hrho] at hw
    rw [parabolicCylinder]
    have hρrsq : rho ^ 2 < r ^ 2 := by nlinarith only [hrho, hrpos, hrr]
    exact ⟨lt_of_le_of_lt hw.1 hrr,
      ⟨by linarith only [hw.2.1, hρrsq], hw.2.2⟩⟩
  have hβbase : Tendsto
      (fun z => rho⁻¹ * ∫ w in parabolicCylinder z.1 z.2 rho,
        spatialGradientSq u Du w) (𝓝 z₀)
      (𝓝 (rho⁻¹ * ∫ w in parabolicCylinder z₀.1 z₀.2 rho,
        spatialGradientSq u Du w)) :=
    tendsto_const_nhds.mul hgradT
  have hδbase : Tendsto
      (fun z => rho ^ (-2 : ℝ) * ∫ w in parabolicCylinder z.1 z.2 rho,
        |p w| ^ (3 / 2 : ℝ)) (𝓝 z₀)
      (𝓝 (rho ^ (-2 : ℝ) * ∫ w in parabolicCylinder z₀.1 z₀.2 rho,
        |p w| ^ (3 / 2 : ℝ))) :=
    tendsto_const_nhds.mul hpT
  have hβpow := (Real.continuous_rpow_const
    (q := (1 / 2 : ℝ)) (by norm_num)).continuousAt.tendsto.comp hβbase
  have hδpow := (Real.continuous_rpow_const
    (q := (1 / 3 : ℝ)) (by norm_num)).continuousAt.tendsto.comp hδbase
  have hβevent : ∀ᶠ z in 𝓝 z₀,
      beta u Du z rho =
        (rho⁻¹ * ∫ w in parabolicCylinder z.1 z.2 rho,
          spatialGradientSq u Du w) ^ (1 / 2 : ℝ) := by
    filter_upwards [hcarevent, hGevent] with z hz hzG
    exact hβrepr z hz hzG
  have hδevent : ∀ᶠ z in 𝓝 z₀,
      delta p z rho =
        (rho ^ (-2 : ℝ) * ∫ w in parabolicCylinder z.1 z.2 rho,
          |p w| ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) := by
    filter_upwards [hcarevent, hGevent] with z hz hzG
    exact hδrepr z hz hzG
  have hz₀carrier : closure (parabolicCylinder z₀.1 z₀.2 rho) ⊆
      spaceTimeSet Ω I := by
    have hmono : parabolicCylinder z₀.1 z₀.2 rho ⊆
        parabolicCylinder z₀.1 z₀.2 r :=
      parabolicCylinder_mono hrho.le hrr.le
    exact (closure_mono hmono).trans hKbar
  have hz₀G : parabolicCylinder z₀.1 z₀.2 rho ⊆ G := by
    intro w hw
    simpa [G] using hK (subset_closure hw)
  have hβ₀ := hβrepr z₀ hz₀carrier hz₀G
  have hδ₀ := hδrepr z₀ hz₀carrier hz₀G
  have hβcont : Tendsto (fun z => beta u Du z rho) (𝓝 z₀)
      (𝓝 (beta u Du z₀ rho)) := by
    have hβevent' := hβevent.mono (fun z hz => hz.symm)
    have ht := hβpow.congr' hβevent'
    simpa only [hβ₀] using ht
  have hδcont : Tendsto (fun z => delta p z rho) (𝓝 z₀)
      (𝓝 (delta p z₀ rho)) := by
    have hδevent' := hδevent.mono (fun z hz => hz.symm)
    have ht := hδpow.congr' hδevent'
    simpa only [hδ₀] using ht
  let F : ℝ → ℝ := fun h =>
    (essSup (fun s => ENNReal.ofReal
      (∫ y in vec3Ball z₀.1 r,
        (vec3EuclideanNorm (u (y, s))) ^ 2))
      (volume.restrict (Ioc (z₀.2 - R ^ 2) (z₀.2 + h)))).toReal
  have hFusc : Filter.limsup F (𝓝[>] (0 : ℝ)) ≤
      (essSup (timeSliceBallEnergy z₀.1 R ·
        (fun w => vec3EuclideanNorm (u w)))
        (volume.restrict (Ioc (z₀.2 - R ^ 2) z₀.2))).toReal := by
    simpa only [F] using hαusc
  have hFnonneg : ∀ᶠ h in (𝓝[>] (0 : ℝ)), 0 ≤ F h := by
    filter_upwards [] with h
    exact ENNReal.toReal_nonneg
  have hFco : IsCoboundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) F :=
    isCoboundedUnder_le_of_eventually_le _ hFnonneg
  have hballrO : vec3Ball z₀.1 r ⊆ Ωo := by
    intro x hx
    apply hballo
    rw [mem_vec3Ball] at hx ⊢
    exact lt_trans hx hrrR
  have hballrF : vec3Ball z₀.1 r ⊆ Ωf := by
    intro x hx
    apply hballf
    rw [mem_vec3Ball] at hx ⊢
    exact lt_trans hx hrrR
  have hvelrO := velocity_slice_integrable hsol hboxo hballrO
  have hvelrF := velocity_slice_integrable hsol hboxf hballrF
  have hvelRO := velocity_slice_integrable hsol hboxo hballo
  have hvelRF := velocity_slice_integrable hsol hboxf hballf
  have hIntAt : ∀ {h : ℝ}, 0 < h → h ≤ h₁ →
      ∀ᵐ s ∂volume.restrict (Ioc (z₀.2 - R ^ 2) (z₀.2 + h)),
        IntegrableOn (fun y : Vec3 => (vec3EuclideanNorm (u (y, s))) ^ 2)
          (vec3Ball z₀.1 r) volume ∧
        IntegrableOn (fun y : Vec3 => (vec3EuclideanNorm (u (y, s))) ^ 2)
          (vec3Ball z₀.1 R) volume := by
    intro h hh hhh
    have hold : Ioc (z₀.2 - R ^ 2) z₀.2 ⊆ Jo := by
      intro s hs
      have hm : ((z₀.1, s) : ParabolicPoint) ∈
          parabolicCylinder z₀.1 z₀.2 R := by
        rw [parabolicCylinder]
        exact ⟨by rw [mem_vec3Ball]; simp [vec3EuclideanNorm_zero, hR], hs⟩
      exact (hco0 hm).2
    have hfuture : Ioc z₀.2 (z₀.2 + h) ⊆ Jf := by
      intro s hs
      have hm : ((z₀.1, s) : ParabolicPoint) ∈
          parabolicCylinder z₀.1 (z₀.2 + h₁) R := by
        rw [parabolicCylinder]
        exact ⟨by rw [mem_vec3Ball]; simp [vec3EuclideanNorm_zero, hR],
          ⟨by linarith only [hs.1, hh₁R], by linarith only [hs.2, hhh]⟩⟩
      exact (hcf hm).2
    have hu : Ioc (z₀.2 - R ^ 2) (z₀.2 + h) =
        Ioc (z₀.2 - R ^ 2) z₀.2 ∪ Ioc z₀.2 (z₀.2 + h) := by
      ext s
      constructor
      · intro hs
        by_cases hleft : s ≤ z₀.2
        · exact Or.inl ⟨hs.1, hleft⟩
        · exact Or.inr ⟨lt_of_not_ge hleft, hs.2⟩
      · rintro (hs | hs)
        · exact ⟨hs.1, le_trans hs.2 (by linarith only [hh.le])⟩
        · exact ⟨by nlinarith only [hs.1, hR], hs.2⟩
    rw [hu, ae_restrict_union_iff]
    exact ⟨ae_restrict_of_ae_restrict_of_subset hold hvelrO |>.and
        (ae_restrict_of_ae_restrict_of_subset hold hvelRO),
      ae_restrict_of_ae_restrict_of_subset hfuture hvelrF |>.and
        (ae_restrict_of_ae_restrict_of_subset hfuture hvelRF)⟩
  have hfiniteRAt : ∀ {h : ℝ}, 0 < h → h ≤ h₁ →
      essSup (fun s => ENNReal.ofReal
        (∫ y in vec3Ball z₀.1 R,
          (vec3EuclideanNorm (u (y, s))) ^ 2))
        (volume.restrict (Ioc (z₀.2 - R ^ 2) (z₀.2 + h))) ≠ ⊤ := by
    intro h hh hhh
    have hrectFull : euclideanClosedBall z₀.1 R ×ˢ
        Icc (z₀.2 - R ^ 2) (z₀.2 + h) ⊆ spaceTimeSet Ω I := by
      intro w hw
      by_cases hpast : w.2 ≤ z₀.2
      · apply hrect
        exact ⟨hw.1, ⟨hw.2.1, hpast⟩⟩
      · have hhl : h < R ^ 2 := lt_of_le_of_lt hhh hh₁R
        have hsub := hsubAt (h := h) (le_of_lt hh) hhh
        apply hsub
        rw [closure_parabolicCylinder hR]
        have heq :=
          (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR.le).1 hw.1
        have heq' : vec3EuclideanNorm (w.1 - z₀.1) ≤ R := by
          have hnorm : vecEuclideanNorm (w.1 - z₀.1) =
              vec3EuclideanNorm (w.1 - z₀.1) := by
            simp [CKN.vecEuclideanNorm, vec3EuclideanNorm, vecNormSq, vecDot]
            apply congrArg Real.sqrt
            apply Finset.sum_congr rfl
            intro i hi
            ring
          rw [← hnorm]
          exact heq
        exact ⟨heq', ⟨by linarith only [lt_of_not_ge hpast, hhl], hw.2.2⟩⟩
    have hT := sws_timeSliceBallEnergy_essSup_lt_top hsol hR
      (by nlinarith only [hR, hh]) hrectFull
    have hEq : ∀ᵐ s ∂volume.restrict
          (Ioc (z₀.2 - R ^ 2) (z₀.2 + h)),
          timeSliceBallEnergy z₀.1 R s
              (fun w => vec3EuclideanNorm (u w)) =
            ENNReal.ofReal (∫ y in vec3Ball z₀.1 R,
              (vec3EuclideanNorm (u (y, s))) ^ 2) := by
      filter_upwards [hIntAt hh hhh] with s hs
      have hsR := hs.2
      exact (time_slice_energy_eq_ofReal hsR).symm
    rw [← essSup_congr_ae hEq]
    exact ne_of_lt hT
  have hfiniteSmallAt : ∀ {h : ℝ}, 0 < h → h ≤ h₁ →
      essSup (timeSliceBallEnergy z₀.1 r ·
          (fun w => vec3EuclideanNorm (u w)))
        (volume.restrict (Ioc (z₀.2 - R ^ 2) (z₀.2 + h))) ≠ ⊤ := by
    intro h hh hhh
    have hIntAt' := hIntAt (h := h) hh hhh
    have hmono := essSup_mono_measure_and_ae
      (μ := volume.restrict (Ioc (z₀.2 - R ^ 2) (z₀.2 + h)))
      (ν := volume.restrict (Ioc (z₀.2 - R ^ 2) (z₀.2 + h))) le_rfl (by
        filter_upwards [hIntAt'] with s hs
        have hsub : vec3Ball z₀.1 r ⊆ vec3Ball z₀.1 R := by
          intro x hx
          rw [mem_vec3Ball] at hx ⊢
          exact lt_trans hx hrrR
        exact ENNReal.ofReal_le_ofReal (setIntegral_mono_set hs.2
          (Filter.Eventually.of_forall (fun x => sq_nonneg _))
          (Filter.Eventually.of_forall (fun x hx => hsub hx))))
    have hfiniteRealr := ne_of_lt (hmono.trans_lt
      (lt_top_iff_ne_top.mpr (hfiniteRAt hh hhh)))
    have hEqFixedr : ∀ᵐ s ∂volume.restrict
          (Ioc (z₀.2 - R ^ 2) (z₀.2 + h)),
          timeSliceBallEnergy z₀.1 r s
              (fun w => vec3EuclideanNorm (u w)) =
            ENNReal.ofReal (∫ x in vec3Ball z₀.1 r,
              (vec3EuclideanNorm (u (x, s))) ^ 2) := by
      filter_upwards [hIntAt'] with s hs
      exact (time_slice_energy_eq_ofReal hs.1).symm
    rw [essSup_congr_ae hEqFixedr]
    exact hfiniteRealr
  have hFbound : IsBoundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) F := by
    simpa only [F] using
      theta_usc_timeSliceEnergy_bounded hsol hR hrrR hh₁ hh₁R hsubAt hIntAt hS0
  have hEqOld : ∀ᵐ s ∂volume.restrict
        (Ioc (z₀.2 - R ^ 2) z₀.2),
        timeSliceBallEnergy z₀.1 R s
            (fun w => vec3EuclideanNorm (u w)) =
          ENNReal.ofReal (∫ y in vec3Ball z₀.1 R,
            (vec3EuclideanNorm (u (y, s))) ^ 2) := by
    have hold : Ioc (z₀.2 - R ^ 2) z₀.2 ⊆ Jo := by
      intro s hs
      have hm : ((z₀.1, s) : ParabolicPoint) ∈
          parabolicCylinder z₀.1 z₀.2 R := by
        rw [parabolicCylinder]
        exact ⟨by rw [mem_vec3Ball]; simp [vec3EuclideanNorm_zero, hR], hs⟩
      exact (hco0 hm).2
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hold hvelRO] with s hs
    exact (time_slice_energy_eq_ofReal hs).symm
  have hfiniteROld : essSup (fun s => ENNReal.ofReal
        (∫ y in vec3Ball z₀.1 R,
          (vec3EuclideanNorm (u (y, s))) ^ 2))
        (volume.restrict (Ioc (z₀.2 - R ^ 2) z₀.2)) ≠ ⊤ := by
    rw [← essSup_congr_ae hEqOld]
    exact hS0
  have htarget : (R / rho) * alpha u z₀ R ^ 2 = rho⁻¹ *
        (essSup (timeSliceBallEnergy z₀.1 R ·
          (fun w => vec3EuclideanNorm (u w)))
          (volume.restrict (Ioc (z₀.2 - R ^ 2) z₀.2))).toReal := by
    rw [alpha_sq_eq u z₀ R hR]
    simp only [timeSliceEnergyEssSup]
    field_simp [ne_of_gt hrho, ne_of_gt hR]
  have hspace : ∀ᶠ z : ParabolicPoint in 𝓝 z₀,
      z.1 ∈ vec3Ball z₀.1 (r - rho) := by
    have hz : z₀.1 ∈ vec3Ball z₀.1 (r - rho) := by
      rw [mem_vec3Ball]
      simp [vec3EuclideanNorm_zero]
      exact hrr
    exact ((isOpen_vec3Ball z₀.1 (r - rho)).preimage
      continuous_fst_parabolicPoint).mem_nhds hz
  let τ : ℝ := min (h₁ / 2) ((R ^ 2 - rho ^ 2) / 2)
  have hτ : 0 < τ := by
    dsimp [τ]
    positivity
  have hτh₁ : τ ≤ h₁ / 2 := min_le_left _ _
  have hτgap : τ ≤ (R ^ 2 - rho ^ 2) / 2 := min_le_right _ _
  have htime : ∀ᶠ z : ParabolicPoint in 𝓝 z₀,
      z.2 ∈ Ioo (z₀.2 - τ) (z₀.2 + τ) := by
    have hz : z₀.2 ∈ Ioo (z₀.2 - τ) (z₀.2 + τ) := by
      exact ⟨sub_lt_self _ hτ, lt_add_of_pos_right _ hτ⟩
    exact ((isOpen_Ioo.preimage continuous_snd_parabolicPoint).mem_nhds hz)
  have htimeMap : Tendsto (fun z : ParabolicPoint => z.2 - z₀.2)
      (𝓝 z₀ ⊓ 𝓟 {z : ParabolicPoint | z.2 > z₀.2})
      (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have ht0 : Tendsto (fun z : ParabolicPoint => z.2 - z₀.2)
          (𝓝 z₀) (𝓝 (0 : ℝ)) := by
        simpa only [sub_self] using
          ((continuous_snd_parabolicPoint.tendsto z₀).sub_const z₀.2)
      exact ht0.mono_left (show
        (𝓝 z₀ ⊓ 𝓟 {z : ParabolicPoint | z.2 > z₀.2}) ≤ 𝓝 z₀ from inf_le_left)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact sub_pos.mpr hz
  have hAlphaEventually : ∀ {y : ℝ},
      (R / rho) * alpha u z₀ R ^ 2 < y →
      ∀ᶠ z : ParabolicPoint in 𝓝 z₀, alpha u z rho ^ 2 < y := by
    intro y hy
    have hSlt :
        (essSup (timeSliceBallEnergy z₀.1 R ·
          (fun w => vec3EuclideanNorm (u w)))
          (volume.restrict (Ioc (z₀.2 - R ^ 2) z₀.2))).toReal < rho * y := by
      calc
        _ = rho * (rho⁻¹ *
            (essSup (timeSliceBallEnergy z₀.1 R ·
              (fun w => vec3EuclideanNorm (u w)))
              (volume.restrict (Ioc (z₀.2 - R ^ 2) z₀.2))).toReal) := by
                field_simp [ne_of_gt hrho]
        _ = rho * ((R / rho) * alpha u z₀ R ^ 2) := by rw [htarget]
        _ < rho * y := mul_lt_mul_of_pos_left hy hrho
    have hFy : ∀ᶠ h in (𝓝[>] (0 : ℝ)), F h < rho * y := by
      have hFy' := (Filter.limsup_le_iff' hFco hFbound).1 hFusc
        (((essSup (timeSliceBallEnergy z₀.1 R ·
          (fun w => vec3EuclideanNorm (u w)))
          (volume.restrict (Ioc (z₀.2 - R ^ 2) z₀.2))).toReal + rho * y) / 2)
        (by linarith only [hSlt])
      filter_upwards [hFy'] with h hh
      linarith only [hh, hSlt]
    have hFyCond : ∀ᶠ z : ParabolicPoint in 𝓝 z₀,
        z.2 ≤ z₀.2 ∨ F (z.2 - z₀.2) < rho * y := by
      have he : ∀ᶠ z : ParabolicPoint in
          (𝓝 z₀ ⊓ 𝓟 {z : ParabolicPoint | z.2 > z₀.2}),
          F (z.2 - z₀.2) < rho * y := htimeMap.eventually hFy
      have he' : {z : ParabolicPoint | F (z.2 - z₀.2) < rho * y} ∈
          (𝓝 z₀ ⊓ 𝓟 {z : ParabolicPoint | z.2 > z₀.2}) := he
      have he'' : {z : ParabolicPoint |
          z.2 > z₀.2 → F (z.2 - z₀.2) < rho * y} ∈ 𝓝 z₀ :=
        (mem_inf_principal).mp he'
      filter_upwards [he''] with z hz
      by_cases hpast : z.2 ≤ z₀.2
      · exact Or.inl hpast
      · exact Or.inr (hz (lt_of_not_ge hpast))
    filter_upwards [hspace, htime, hFyCond] with z hzspace hztime hzFy
    have hballr : vec3Ball z.1 rho ⊆ vec3Ball z₀.1 r := by
      intro x hx
      rw [mem_vec3Ball] at hx ⊢
      calc
        vec3EuclideanNorm (x - z₀.1) =
            vec3EuclideanNorm ((x - z.1) + (z.1 - z₀.1)) := by
              congr 1
              ring
        _ ≤ vec3EuclideanNorm (x - z.1) +
              vec3EuclideanNorm (z.1 - z₀.1) := euclidean_triangle _ _
        _ < rho + (r - rho) := add_lt_add hx hzspace
        _ = r := by ring
    by_cases hpast : z.2 ≤ z₀.2
    · have hballR : vec3Ball z.1 rho ⊆ vec3Ball z₀.1 R := by
        intro x hx
        rw [mem_vec3Ball] at hx ⊢
        calc
          vec3EuclideanNorm (x - z₀.1) =
              vec3EuclideanNorm ((x - z.1) + (z.1 - z₀.1)) := by
                congr 1
                ring
          _ ≤ vec3EuclideanNorm (x - z.1) +
                vec3EuclideanNorm (z.1 - z₀.1) := euclidean_triangle _ _
          _ < rho + (r - rho) := add_lt_add hx hzspace
          _ = r := by ring
          _ < R := hrrR
      have hinterval : Ioc (z.2 - rho ^ 2) z.2 ⊆
          Ioc (z₀.2 - R ^ 2) z₀.2 := by
        intro s hs
        have hlower : z₀.2 - R ^ 2 < z.2 - rho ^ 2 := by
          nlinarith only [hztime.1, hτgap, hgap]
        exact ⟨lt_trans hlower hs.1, le_trans hs.2 hpast⟩
      have hold : Ioc (z₀.2 - R ^ 2) z₀.2 ⊆ Jo := by
        intro s hs
        have hm : ((z₀.1, s) : ParabolicPoint) ∈
            parabolicCylinder z₀.1 z₀.2 R := by
          rw [parabolicCylinder]
          exact ⟨by rw [mem_vec3Ball]; simp [vec3EuclideanNorm_zero, hR], hs⟩
        exact (hco0 hm).2
      have hIntOld : ∀ᵐ s ∂volume.restrict
          (Ioc (z₀.2 - R ^ 2) z₀.2),
          IntegrableOn (fun y : Vec3 =>
            (vec3EuclideanNorm (u (y, s))) ^ 2)
            (vec3Ball z₀.1 R) volume :=
        ae_restrict_of_ae_restrict_of_subset hold hvelRO
      have hbound := alpha_sq_le_of_essSup hrho hballR hinterval hIntOld hS0
      have hSreal : essSup (fun s => ENNReal.ofReal
          (∫ y in vec3Ball z₀.1 R,
            (vec3EuclideanNorm (u (y, s))) ^ 2))
          (volume.restrict (Ioc (z₀.2 - R ^ 2) z₀.2)) =
          essSup (timeSliceBallEnergy z₀.1 R ·
            (fun w => vec3EuclideanNorm (u w)))
            (volume.restrict (Ioc (z₀.2 - R ^ 2) z₀.2)) :=
        (essSup_congr_ae hEqOld).symm
      rw [hSreal] at hbound
      exact hbound.trans_lt (by rw [← htarget]; exact hy)
    · have hzfuture : z₀.2 < z.2 := lt_of_not_ge hpast
      let h : ℝ := z.2 - z₀.2
      have hh : 0 < h := by dsimp [h]; exact sub_pos.mpr hzfuture
      have hhh : h ≤ h₁ := by
        dsimp [h]
        linarith only [hztime.2, hτh₁, hτ]
      have hinterval : Ioc (z.2 - rho ^ 2) z.2 ⊆
          Ioc (z₀.2 - R ^ 2) z.2 := by
        intro s hs
        have hlower : z₀.2 - R ^ 2 < z.2 - rho ^ 2 := by
          nlinarith only [hzfuture, hgap]
        exact ⟨lt_trans hlower hs.1, hs.2⟩
      have hIntFuture : ∀ᵐ s ∂volume.restrict
          (Ioc (z₀.2 - R ^ 2) z.2),
          IntegrableOn (fun y : Vec3 =>
            (vec3EuclideanNorm (u (y, s))) ^ 2)
            (vec3Ball z₀.1 r) volume := by
        have hEqtime : z₀.2 + h = z.2 := by
          dsimp [h]
          ring
        have hIntAt' := hIntAt (h := h) hh hhh
        rw [hEqtime] at hIntAt'
        filter_upwards [hIntAt'] with s hs
        exact hs.1
      have hEqtime : z₀.2 + h = z.2 := by
        dsimp [h]
        ring
      have hfiniteSmallAt' := hfiniteSmallAt (h := h) hh hhh
      rw [hEqtime] at hfiniteSmallAt'
      have hbound := alpha_sq_le_of_essSup hrho hballr hinterval hIntFuture
        hfiniteSmallAt'
      have hFy' : F h < rho * y := by
        exact hzFy.resolve_left hpast
      have hF_eq : F h =
          (essSup (fun s => ENNReal.ofReal
            (∫ y in vec3Ball z₀.1 r,
              (vec3EuclideanNorm (u (y, s))) ^ 2))
            (volume.restrict (Ioc (z₀.2 - R ^ 2) z.2))).toReal := by
        dsimp [F]
        rw [hEqtime]
      calc
        alpha u z rho ^ 2 ≤ rho⁻¹ * F h := by
          rw [hF_eq]
          exact hbound
        _ < rho⁻¹ * (rho * y) :=
          mul_lt_mul_of_pos_left hFy' (inv_pos.mpr hrho)
        _ = y := by field_simp [ne_of_gt hrho]
  have hAco : IsCoboundedUnder (· ≤ ·) (𝓝 z₀)
      (fun z : ParabolicPoint => alpha u z rho ^ 2) :=
    isCoboundedUnder_le_of_eventually_le _
      (Filter.Eventually.of_forall (fun z => sq_nonneg _))
  have hAbound : IsBoundedUnder (· ≤ ·) (𝓝 z₀)
      (fun z : ParabolicPoint => alpha u z rho ^ 2) := by
    apply isBoundedUnder_of_eventually_le
    filter_upwards [hAlphaEventually
      (y := (R / rho) * alpha u z₀ R ^ 2 + 1)
      (lt_add_of_pos_right _ (by norm_num))] with z hz
    exact hz.le
  have hAlimsup : Filter.limsup
      (fun z : ParabolicPoint => alpha u z rho ^ 2) (𝓝 z₀) ≤
      (R / rho) * alpha u z₀ R ^ 2 := by
    rw [Filter.limsup_le_iff' hAco hAbound]
    intro y hy
    filter_upwards [hAlphaEventually hy] with z hz
    exact hz.le
  exact ⟨hAlimsup, hβcont, hδcont, hAbound⟩

/-- The paper-shaped semicontinuity and continuity statement for the scale
quantities. -/
theorem theta_usc_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z₀ : ParabolicPoint} {rho R : ℝ} (hrho : 0 < rho) (hrhoR : rho < R)
    (hrect : euclideanClosedBall z₀.1 R ×ˢ Icc (z₀.2 - R ^ 2) z₀.2 ⊆
      spaceTimeSet Ω I) (ht₀ : z₀.2 ∈ I) :
    Filter.limsup (fun z : ParabolicPoint => alpha u z rho ^ 2) (𝓝 z₀) ≤
        (R / rho) * alpha u z₀ R ^ 2 ∧
      Tendsto (fun z => beta u Du z rho) (𝓝 z₀)
        (𝓝 (beta u Du z₀ rho)) ∧
      Tendsto (fun z => delta p z rho) (𝓝 z₀)
        (𝓝 (delta p z₀ rho)) := by
  have h := theta_usc_of_sws_with_alpha_bound hsol hrho hrhoR hrect ht₀
  exact ⟨h.1, h.2.1, h.2.2.1⟩

end CKN

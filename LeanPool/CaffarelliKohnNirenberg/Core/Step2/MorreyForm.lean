/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Cylinders
public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.MorreyBalls

/-!
# Morrey Form

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Parabolic.Integration
noncomputable section
namespace CKN
private theorem morreyBallNorm_le_of_cell_bound' {P τ : ℝ} {g : ParabolicPoint → ℝ}
    {K : ℝ≥0∞} (hcell : ∀ z : ParabolicPoint, ∀ r : ℝ, 0 < r → morreyBallCell P τ g z r ≤ K) :
    morreyBallNorm P τ g ≤ K := by
  unfold morreyBallNorm
  refine iSup_le fun z => iSup_le fun r => hcell z r.1 r.2
/-- Pressure coefficient controlling the small-scale Morrey integral bounds. -/
def pressureSmallConstant (M : ℝ) : ℝ≥0∞ := ENNReal.ofReal (M ^ (3 / 2 : ℝ) * (8 : ℝ) ^ (13 / 5 :
  ℝ))
/-- Gradient coefficient controlling the small-scale Morrey integral bounds. -/
def gradientSmallConstant (M : ℝ) : ℝ≥0∞ := ENNReal.ofReal (M ^ 2 * (8 : ℝ) ^ (9 / 5 : ℝ))
/-- Velocity coefficient obtained from Sobolev interpolation in the small-scale Morrey estimate.
-/
def velocitySmallConstant (M : ℝ) : ℝ≥0∞ := ((ENNReal.ofReal ((3 : ℝ) ^ ((3 : ℝ) / 2 - 1)) * 3) *
    localSobolevConstant ^ (3 / 2 : ℝ)) * ENNReal.ofReal (M ^ 3 * (2 : ℝ) ^ (1 / 2 : ℝ) *
      ((2 : ℝ) ^ (27 / 10 : ℝ) + (32 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (27 / 10 : ℝ)) * (4 : ℝ) ^ (16
        / 5 : ℝ))
private theorem negative_scale {r₀ r d : ℝ} (hr₀ : 0 < r₀) (hrr : r₀ ≤ r) (hd : 0 ≤ d) :
    (ENNReal.ofReal r) ^ (-d) ≤ (ENNReal.ofReal r₀) ^ (-d) := by
  have hr : 0 < r := lt_of_lt_of_le hr₀ hrr
  have hnn : Real.toNNReal r₀ ≤ Real.toNNReal r := Real.toNNReal_monotone hrr
  have hpos : 0 < Real.toNNReal r₀ := Real.toNNReal_pos.mpr hr₀
  have hposr : 0 < Real.toNNReal r := Real.toNNReal_pos.mpr hr
  have hnnr := NNReal.rpow_le_rpow_of_nonpos hpos hnn (neg_nonpos.mpr hd)
  change ((Real.toNNReal r : ℝ≥0∞) ^ (-d) ≤
    (Real.toNNReal r₀ : ℝ≥0∞) ^ (-d))
  rw [← ENNReal.coe_rpow_of_ne_zero (x := Real.toNNReal r)
      (y := -d) hposr.ne',
    ← ENNReal.coe_rpow_of_ne_zero (x := Real.toNNReal r₀)
      (y := -d) hpos.ne']
  exact ENNReal.coe_le_coe.mpr hnnr
private theorem cell_bound_global {p q : ℝ} {r₀ r : ℝ} {I : ℝ≥0∞}
    {g : ParabolicPoint → ℝ} {z : ParabolicPoint} (hp : 0 < p) (hpq : p ≤ q)
    (hr₀ : 0 < r₀) (hrr : r₀ ≤ r) (hI : ballPowerIntegral p g z r ≤ I) :
    morreyBallCell p q g z r ≤ (ENNReal.ofReal r₀) ^ (-(5 * (1 / p - 1 / q))) * I ^ (1 / p : ℝ) :=
      by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hd : 0 ≤ 5 * (1 / p - 1 / q) := by
    exact mul_nonneg (by norm_num)
      (sub_nonneg.mpr (one_div_le_one_div_of_le hp hpq))
  have hscale := negative_scale hr₀ hrr hd
  have hroot := ENNReal.rpow_le_rpow hI (one_div_nonneg.mpr hp.le)
  have hexp : -(5 * (1 - p / q) / p) = -(5 * (1 / p - 1 / q)) := by
    field_simp [hp.ne', hq.ne']
  unfold morreyBallCell
  rw [hexp]
  calc
    _ ≤ (ENNReal.ofReal r) ^ (-(5 * (1 / p - 1 / q))) * I ^ (1 / p : ℝ) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hscale (by positivity)
private theorem cell_bound_ennreal {p q a : ℝ} {K : ℝ≥0∞} {g : ParabolicPoint → ℝ}
    {z : ParabolicPoint} {r : ℝ} (hp : 0 < p) (hr : 0 < r) (ha0 : 0 ≤ a)
    (ha : a = 5 * (1 - p / q)) (hI : ballPowerIntegral p g z r ≤ K * ENNReal.ofReal (r ^ a)) :
    morreyBallCell p q g z r ≤ K ^ (1 / p : ℝ) := by
  unfold morreyBallCell
  have hroot := ENNReal.rpow_le_rpow hI (by positivity : 0 ≤ (1 / p : ℝ))
  have hpdiv : 0 ≤ (1 / p : ℝ) := one_div_nonneg.mpr hp.le
  have hroot' : (ballPowerIntegral p g z r) ^ (1 / p : ℝ) ≤
      K ^ (1 / p : ℝ) * (ENNReal.ofReal r) ^ (a / p : ℝ) := by
    calc
      _ ≤ (K * ENNReal.ofReal (r ^ a)) ^ (1 / p : ℝ) := hroot
      _ = K ^ (1 / p : ℝ) * (ENNReal.ofReal r) ^ (a / p : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hpdiv,
          ← ENNReal.ofReal_rpow_of_nonneg hr.le ha0, ← ENNReal.rpow_mul]
        congr 1
        ring_nf
  have hrpow : ENNReal.ofReal r ≠ 0 := ENNReal.ofReal_pos.mpr hr |>.ne'
  have hrpowtop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcancel : (ENNReal.ofReal r) ^ (-(5 * (1 - p / q) / p)) *
      (ENNReal.ofReal r) ^ (a / p : ℝ) = 1 := by
    rw [← ENNReal.rpow_add _ _ hrpow hrpowtop, ha]
    norm_num
  calc
    (ENNReal.ofReal r) ^ (-(5 * (1 - p / q) / p)) *
        (ballPowerIntegral p g z r) ^ (1 / p : ℝ) ≤
      (ENNReal.ofReal r) ^ (-(5 * (1 - p / q) / p)) *
        (K ^ (1 / p : ℝ) * (ENNReal.ofReal r) ^ (a / p : ℝ)) :=
      mul_le_mul_of_nonneg_left hroot' (by positivity)
    _ = K ^ (1 / p : ℝ) := by
      calc
        _ = K ^ (1 / p : ℝ) * ((ENNReal.ofReal r) ^
            (-(5 * (1 - p / q) / p)) * (ENNReal.ofReal r) ^ (a / p : ℝ)) := by
              ac_rfl
        _ = _ := by rw [hcancel, mul_one]
private theorem ballPowerIntegral_zero {p : ℝ} {Q : Set ParabolicPoint} {g : ParabolicPoint → ℝ}
    {z : ParabolicPoint} {r : ℝ} (hp : 0 < p) (hdis : Metric.ball z r ∩ Q = ∅) : ballPowerIntegral
      p (Q.indicator g) z r = 0 := by
  unfold ballPowerIntegral
  apply le_antisymm
  · have heq : (∫⁻ y in Metric.ball z r,
        ENNReal.ofReal |Q.indicator g y| ^ p) =
        ∫⁻ y in Metric.ball z r, (0 : ℝ≥0∞) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_ball)] with y hy
      have hyQ : y ∉ Q := by
        intro hyQ
        have : y ∈ (∅ : Set ParabolicPoint) := hdis ▸ Set.mem_inter hy hyQ
        exact this
      simp [Set.indicator_of_notMem hyQ, ENNReal.zero_rpow_of_pos hp]
    exact heq.le.trans_eq (by simp)
  · exact bot_le
private theorem local_step2_setup {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} (hsol : IsSuitableWeakSolutionIntegrable
      Ω I q u Du p f)
    {z₀ : ParabolicPoint} {r₂ M ρ : ℝ} (_ : 0 < r₂) (hρ : 0 < ρ)
    (hρsmall : 128 * ρ ≤ r₂) (hcarrier : Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I)
    (hdecay : ∀ z : ParabolicPoint, z ∈ Metric.ball z₀ r₂ → ∀ r, 0 < r → r < r₂ →
      max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤ M * r ^ (2 / 5 : ℝ))
    {Q₂ : Set ParabolicPoint} (hQ₂ : Q₂ = Metric.ball z₀ (r₂ / 4)) {z : ParabolicPoint}
    (hz : Metric.ball z ρ ∩ Q₂ ≠ ∅) :
    ∃ (w z' : ParabolicPoint) (Ω' : Set Vec3) (J : Set ℝ),
      w ∈ Metric.ball z ρ ∧ w ∈ Q₂ ∧
      z' = (w.1, w.2 + (2 * ρ) ^ 2) ∧ localBox Ω I Ω' J ∧
      Metric.ball z ρ ⊆ parabolicCylinder z'.1 z'.2 (4 * ρ) ∧
      closure (parabolicCylinder z'.1 z'.2 (8 * ρ)) ⊆ spaceTimeSet Ω I ∧
      parabolicCylinder z'.1 z'.2 (8 * ρ) ⊆ spaceTimeSet Ω' J ∧
      max (max (alpha u z' (8 * ρ)) (beta u Du z' (8 * ρ)))
        (delta p z' (8 * ρ) ^ 2) ≤ M * (8 * ρ) ^ (2 / 5 : ℝ) := by
  subst Q₂
  obtain ⟨w, hwz, hw0⟩ := Set.nonempty_iff_ne_empty.mpr hz
  let z' : ParabolicPoint := (w.1, w.2 + (2 * ρ) ^ 2)
  have hshift : dist z' w ≤ 2 * ρ := by dsimp [z']; rw [show @dist ParabolicPoint
    (@PseudoMetricSpace.toDist ParabolicPoint parabolicMetricSpace.toPseudoMetricSpace)
      ((w.1, w.2 + (2 * ρ) ^ 2) : ParabolicPoint) w = 2 * ρ from
        step2_shifted_center_dist (w := w) (r := 2 * ρ) (by positivity)]
  have hw0' : dist w z₀ < r₂ / 4 := hw0
  have hz'0 : dist z' z₀ < r₂ := by
    have htri := dist_triangle z' w z₀
    nlinarith only [htri, hshift, hw0', hρ, hρsmall]
  have hclosure : closure (parabolicCylinder z'.1 z'.2 (128 * ρ)) ⊆ Metric.ball z₀ (2 * r₂) := by
    intro y hy
    have hyc := step2_closure_cylinder_subset_closedBall (x := z'.1) (t := z'.2)
      (r := 128 * ρ) (by positivity) hy
    have htri := dist_triangle y z' z₀
    rw [Metric.mem_ball]
    nlinarith only [htri, Metric.mem_closedBall.mp hyc, hz'0, hρsmall]
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset hsol.1 hsol.2.1
    (by positivity : 0 < 128 * ρ) (hclosure.trans hcarrier)
  have hsub8 : closure (parabolicCylinder z'.1 z'.2 (8 * ρ)) ⊆ spaceTimeSet Ω I :=
    (closure_mono (parabolicCylinder_mono (by positivity)
      (by nlinarith only [hρ]))).trans (hclosure.trans hcarrier)
  have hcyl8 : parabolicCylinder z'.1 z'.2 (8 * ρ) ⊆ spaceTimeSet Ω' J :=
    (parabolicCylinder_mono (by positivity) (by nlinarith only [hρ])).trans hcyl
  have hdec := hdecay z' hz'0 (8 * ρ) (by positivity) (by nlinarith only [hρ, hρsmall])
  refine ⟨w, z', Ω', J, hwz, hw0, rfl, hbox, ?_, hsub8, hcyl8, hdec⟩
  dsimp [z']; exact step2_shifted_ball_cylinder hρ hwz
private theorem abar_real {M R : ℝ} (hM : 0 ≤ M) (hR : 0 < R) :
    ((2 * R) * (M * (2 * R) ^ (2 / 5 : ℝ)) ^ 2) ^ (1 / 2 : ℝ) = M * (2 * R) ^ (9 / 10 : ℝ) := by
  have hX : 0 ≤ 2 * R := by positivity
  have hXpos : 0 < 2 * R := by positivity
  have hA : 0 ≤ M * (2 * R) ^ (2 / 5 : ℝ) :=
    mul_nonneg hM (Real.rpow_nonneg hX _)
  have hAsqrt : ((M * (2 * R) ^ (2 / 5 : ℝ)) ^ 2) ^
      (1 / 2 : ℝ) = M * (2 * R) ^ (2 / 5 : ℝ) := by
    calc
      _ = ((M * (2 * R) ^ (2 / 5 : ℝ)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        norm_num [Real.rpow_natCast]
      _ = (M * (2 * R) ^ (2 / 5 : ℝ)) ^ ((2 : ℝ) * (1 / 2 : ℝ)) :=
        (Real.rpow_mul hA 2 (1 / 2)).symm
      _ = _ := by norm_num
  rw [Real.mul_rpow hX (sq_nonneg (M * (2 * R) ^ (2 / 5 : ℝ))), hAsqrt]
  calc
    (2 * R) ^ (1 / 2 : ℝ) * (M * (2 * R) ^ (2 / 5 : ℝ)) =
        M * ((2 * R) ^ (1 / 2 : ℝ) * (2 * R) ^ (2 / 5 : ℝ)) := by ring_nf
    _ = _ := by rw [← Real.rpow_add hXpos]; norm_num
private theorem gbar_real {M R : ℝ} (_ : 0 ≤ M) (hR : 0 < R) :
    (2 * R) * (M * (2 * R) ^ (2 / 5 : ℝ)) ^ 2 = M ^ 2 * (2 * R) ^ (9 / 5 : ℝ) := by
  have hX : 0 ≤ 2 * R := by positivity
  have hXpos : 0 < 2 * R := by positivity
  have hpow : ((2 * R) ^ (2 / 5 : ℝ)) ^ 2 =
      (2 * R) ^ (4 / 5 : ℝ) := by
    calc
      _ = ((2 * R) ^ (2 / 5 : ℝ)) ^ (2 : ℝ) := by
        norm_num [Real.rpow_natCast]
      _ = _ := by rw [← Real.rpow_mul hX]; norm_num
  rw [mul_pow, hpow]
  calc
    2 * R * (M ^ 2 * (2 * R) ^ (4 / 5 : ℝ)) =
        M ^ 2 * ((2 * R) * (2 * R) ^ (4 / 5 : ℝ)) := by ring_nf
    _ = M ^ 2 * ((2 * R) ^ (1 : ℝ) * (2 * R) ^ (4 / 5 : ℝ)) := by
      rw [Real.rpow_one]
    _ = M ^ 2 * (2 * R) ^ (9 / 5 : ℝ) := by
      rw [← Real.rpow_add hXpos]
      norm_num
private theorem decay_bounds {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {R M : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    (hsub : closure (parabolicCylinder z.1 z.2 (2 * R)) ⊆ spaceTimeSet Ω I)
    (hdec : max (max (alpha u z (2 * R)) (beta u Du z (2 * R)))
      (delta p z (2 * R) ^ 2) ≤ M * (2 * R) ^ (2 / 5 : ℝ)) :
    (essSup (fun s => ∫⁻ y in vec3Ball z.1 (2 * R), ENNReal.ofReal
      (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ))
      (volume.restrict (Set.Ioc (z.2 - R ^ 2) z.2))) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (M * (2 * R) ^ (9 / 10 : ℝ)) ∧
      (∫⁻ w in parabolicCylinder z.1 z.2 (2 * R), ENNReal.ofReal
        (spatialGradientSq u Du w)) ≤ ENNReal.ofReal (M ^ 2 * (2 * R) ^ (9 / 5 : ℝ)) := by
  have hR2 : 0 < 2 * R := by positivity
  have hD : 0 ≤ M * (2 * R) ^ (2 / 5 : ℝ) := by positivity
  have hα : alpha u z (2 * R) ≤ M * (2 * R) ^ (2 / 5 : ℝ) :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hdec)
  have hβ : beta u Du z (2 * R) ≤ M * (2 * R) ^ (2 / 5 : ℝ) :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hdec)
  have hα0 : 0 ≤ alpha u z (2 * R) := by unfold alpha; positivity
  have hβ0 : 0 ≤ beta u Du z (2 * R) := by unfold beta; positivity
  have hαsq : (2 * R) * alpha u z (2 * R) ^ 2 ≤
      (2 * R) * (M * (2 * R) ^ (2 / 5 : ℝ)) ^ 2 :=
    mul_le_mul_of_nonneg_left ((sq_le_sq₀ hα0 hD).2 hα) hR2.le
  have hβsq : (2 * R) * beta u Du z (2 * R) ^ 2 ≤
      (2 * R) * (M * (2 * R) ^ (2 / 5 : ℝ)) ^ 2 :=
    mul_le_mul_of_nonneg_left ((sq_le_sq₀ hβ0 hD).2 hβ) hR2.le
  have hEss := sws_timeSliceEnergyEssSup_eq_ofReal_alpha_sq hsol z hR2 hsub
  have hGrad := sws_lintegral_spatialGradientSq_eq_ofReal_beta_sq
    hsol z hR2 hsub
  have hTsub : Set.Ioc (z.2 - R ^ 2) z.2 ⊆
      Set.Ioc (z.2 - (2 * R) ^ 2) z.2 := by
    intro s hs
    exact ⟨by nlinarith only [hs.1, hR], hs.2⟩
  have hpoint : ∀ s, (∫⁻ y in vec3Ball z.1 (2 * R),
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)) ≤
      timeSliceBallEnergy z.1 (2 * R) s
        (fun w => vec3EuclideanNorm (u w)) := by
    intro s
    change (∫⁻ y in vec3Ball z.1 (2 * R),
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)) ≤
      ∫⁻ y in vec3Ball z.1 (2 * R),
        ‖vec3EuclideanNorm (u (y, s))‖ₑ ^ (2 : ℝ)
    apply le_of_eq
    apply lintegral_congr
    intro y
    rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg (u (y, s)))]
  have hmono := essSup_mono_measure_and_ae
    (μ := volume.restrict (Set.Ioc (z.2 - R ^ 2) z.2))
    (ν := volume.restrict (Set.Ioc (z.2 - (2 * R) ^ 2) z.2))
    (Measure.restrict_mono_set volume hTsub) (Filter.Eventually.of_forall hpoint)
  have hess := hmono.trans_eq hEss
  have hA : (essSup (fun s => ∫⁻ y in vec3Ball z.1 (2 * R),
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ))
      (volume.restrict (Set.Ioc (z.2 - R ^ 2) z.2))) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (M * (2 * R) ^ (9 / 10 : ℝ)) := by
    have hroot := ENNReal.rpow_le_rpow hess (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc
      _ ≤ (ENNReal.ofReal ((2 * R) * alpha u z (2 * R) ^ 2)) ^
          (1 / 2 : ℝ) := hroot
      _ = ENNReal.ofReal (((2 * R) * alpha u z (2 * R) ^ 2) ^
          (1 / 2 : ℝ)) := ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
      _ ≤ ENNReal.ofReal (((2 * R) *
          (M * (2 * R) ^ (2 / 5 : ℝ)) ^ 2) ^ (1 / 2 : ℝ)) := by
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
          (by positivity) hαsq (by norm_num))
      _ = _ := by rw [abar_real (by linarith only [hM]) hR]
  refine ⟨hA, ?_⟩
  calc
    _ = ENNReal.ofReal ((2 * R) * beta u Du z (2 * R) ^ 2) := hGrad
    _ ≤ ENNReal.ofReal ((2 * R) * (M * (2 * R) ^ (2 / 5 : ℝ)) ^ 2) :=
      ENNReal.ofReal_le_ofReal hβsq
    _ = _ := by rw [gbar_real (by linarith only [hM]) hR]
private theorem pressure_power_real {M ρ : ℝ} (hM : 0 ≤ M) (hρ : 0 < ρ) :
    (8 * ρ) ^ 2 * (M * (8 * ρ) ^ (2 / 5 : ℝ)) ^ (3 / 2 : ℝ) =
      M ^ (3 / 2 : ℝ) * (8 : ℝ) ^ (13 / 5 : ℝ) * ρ ^ (13 / 5 : ℝ) := by
  have hX : 0 ≤ 8 * ρ := by positivity
  have hXpos : 0 < 8 * ρ := by positivity
  rw [show (M * (8 * ρ) ^ (2 / 5 : ℝ)) ^ (3 / 2 : ℝ) =
      M ^ (3 / 2 : ℝ) * (8 * ρ) ^ (3 / 5 : ℝ) by
    rw [Real.mul_rpow hM (Real.rpow_nonneg hX _), ← Real.rpow_mul hX]
    norm_num]
  calc
    _ = M ^ (3 / 2 : ℝ) * ((8 * ρ) ^ 2 * (8 * ρ) ^ (3 / 5 : ℝ)) := by ring_nf
    _ = M ^ (3 / 2 : ℝ) * (8 * ρ) ^ (13 / 5 : ℝ) := by
      rw [show (8 * ρ) ^ 2 = (8 * ρ) ^ (2 : ℝ) by norm_num [Real.rpow_natCast],
        ← Real.rpow_add hXpos]
      norm_num
    _ = _ := by
      rw [Real.mul_rpow (by norm_num) hρ.le]
      ring_nf
private theorem pressure_small_cell {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z₀ : ParabolicPoint} {r₂ M ρ : ℝ} (hr₂ : 0 < r₂) (hM : 1 ≤ M) (hρ : 0 < ρ)
    (hρsmall : 128 * ρ ≤ r₂) (hcarrier : Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I)
    (hdecay : ∀ z : ParabolicPoint, z ∈ Metric.ball z₀ r₂ → ∀ r, 0 < r → r < r₂ →
      max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤ M * r ^ (2 / 5 : ℝ))
    {Q₂ : Set ParabolicPoint} (hQ₂ : Q₂ = Metric.ball z₀ (r₂ / 4)) {z : ParabolicPoint}
    (hz : Metric.ball z ρ ∩ Q₂ ≠ ∅) :
    ballPowerIntegral (3 / 2 : ℝ) (Q₂.indicator p) z ρ ≤
      pressureSmallConstant M * ENNReal.ofReal (ρ ^ (13 / 5 : ℝ)) := by
  obtain ⟨w, z', Ω', J, hwz, hw0, hzdef, hbox, hball, hsub8, hcyl8, hdec⟩ :=
    local_step2_setup hsol hr₂ hρ hρsmall hcarrier hdecay hQ₂ hz
  have hδsq : delta p z' (8 * ρ) ^ 2 ≤ M * (8 * ρ) ^ (2 / 5 : ℝ) :=
    (le_max_right _ _).trans hdec
  have hδ0 : 0 ≤ delta p z' (8 * ρ) := by unfold delta; positivity
  have hδcube : delta p z' (8 * ρ) ^ 3 ≤
      (M * (8 * ρ) ^ (2 / 5 : ℝ)) ^ (3 / 2 : ℝ) := by
    calc
      _ = (delta p z' (8 * ρ) ^ 2) ^ (3 / 2 : ℝ) := by
        calc
          _ = delta p z' (8 * ρ) ^ (3 : ℝ) := by
            norm_num [Real.rpow_natCast]
          _ = delta p z' (8 * ρ) ^ ((2 : ℝ) * (3 / 2 : ℝ)) := by norm_num
          _ = (delta p z' (8 * ρ) ^ (2 : ℝ)) ^ (3 / 2 : ℝ) :=
            Real.rpow_mul hδ0 2 (3 / 2)
          _ = _ := by norm_num [Real.rpow_natCast]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hδsq (by norm_num)
  have hI : ballPowerIntegral (3 / 2 : ℝ) (Q₂.indicator p) z ρ ≤
      ENNReal.ofReal ((8 * ρ) ^ 2 *
        (M * (8 * ρ) ^ (2 / 5 : ℝ)) ^ (3 / 2 : ℝ)) := by
    unfold ballPowerIntegral
    calc
      _ ≤ ∫⁻ y in Metric.ball z ρ, ENNReal.ofReal |p y| ^ (3 / 2 : ℝ) := by
        apply lintegral_mono
        intro y
        by_cases hy : y ∈ Q₂ <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
      _ ≤ ∫⁻ y in parabolicCylinder z'.1 z'.2 (8 * ρ),
          ENNReal.ofReal |p y| ^ (3 / 2 : ℝ) :=
        (lintegral_mono_set hball).trans (lintegral_mono_set
          (parabolicCylinder_mono (by positivity) (by nlinarith only [hρ])))
      _ = ENNReal.ofReal ((8 * ρ) ^ 2 * delta p z' (8 * ρ) ^ 3) :=
        sws_lintegral_abs_pow_eq_ofReal_delta_cube hsol z' (by positivity) hsub8
      _ ≤ _ := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hδcube (by positivity))
  calc
    _ ≤ ENNReal.ofReal ((8 * ρ) ^ 2 *
        (M * (8 * ρ) ^ (2 / 5 : ℝ)) ^ (3 / 2 : ℝ)) := hI
    _ = pressureSmallConstant M * ENNReal.ofReal (ρ ^ (13 / 5 : ℝ)) := by
      dsimp [pressureSmallConstant]
      rw [pressure_power_real (by linarith only [hM]) hρ,
        ENNReal.ofReal_mul (by positivity)]
private theorem gradient_small_cell {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z₀ : ParabolicPoint} {r₂ M ρ : ℝ} (hr₂ : 0 < r₂) (hM : 1 ≤ M) (hρ : 0 < ρ)
    (hρsmall : 128 * ρ ≤ r₂) (hcarrier : Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I)
    (hdecay : ∀ z : ParabolicPoint, z ∈ Metric.ball z₀ r₂ → ∀ r, 0 < r → r < r₂ →
      max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤ M * r ^ (2 / 5 : ℝ))
    {Q₂ : Set ParabolicPoint} {i j : Fin 3} (hQ₂ : Q₂ = Metric.ball z₀ (r₂ / 4))
    {z : ParabolicPoint} (hz : Metric.ball z ρ ∩ Q₂ ≠ ∅) :
    ballPowerIntegral 2 (Q₂.indicator (fun w => Du w i j)) z ρ ≤
      gradientSmallConstant M * ENNReal.ofReal (ρ ^ (9 / 5 : ℝ)) := by
  obtain ⟨w, z', Ω', J, -, -, -, -, hball, hsub8, -, hdec⟩ :=
    local_step2_setup hsol hr₂ hρ hρsmall hcarrier hdecay hQ₂ hz
  have hdec' : max (max (alpha u z' (2 * (4 * ρ)))
      (beta u Du z' (2 * (4 * ρ)))) (delta p z' (2 * (4 * ρ)) ^ 2) ≤
      M * (2 * (4 * ρ)) ^ (2 / 5 : ℝ) := by
    have hscale : 2 * (4 * ρ) = 8 * ρ := by ring
    simpa [hscale] using hdec
  have hb := decay_bounds hsol (z := z') (R := 4 * ρ) (M := M)
          (by positivity) hM (by convert hsub8 using 1; ring_nf) hdec'
  have hD : ballPowerIntegral 2 (Q₂.indicator (fun w => Du w i j)) z ρ ≤
      ∫⁻ y in parabolicCylinder z'.1 z'.2 (8 * ρ),
        ENNReal.ofReal (spatialGradientSq u Du y) := by
    unfold ballPowerIntegral
    calc
      _ ≤ ∫⁻ y in Metric.ball z ρ,
          ENNReal.ofReal (spatialGradientSq u Du y) := by
        apply lintegral_mono
        intro y
        by_cases hy : y ∈ Q₂
        · simp only [Set.indicator_of_mem hy]
          rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
          apply ENNReal.ofReal_le_ofReal
          unfold spatialGradientSq
          have hi : (Du y i j) ^ 2 ≤ ∑ k : Fin 3, ∑ l : Fin 3,
              (Du y k l) ^ 2 := by
            calc
              _ ≤ ∑ l : Fin 3, (Du y i l) ^ 2 :=
                Finset.single_le_sum (fun l _ => sq_nonneg (Du y i l))
                  (Finset.mem_univ j)
              _ ≤ _ := Finset.single_le_sum
                (fun k _ => Finset.sum_nonneg
                  (fun l _ => sq_nonneg (Du y k l))) (Finset.mem_univ i)
          simpa [sq_abs] using hi
        · simp [Set.indicator_of_notMem hy]
      _ ≤ ∫⁻ y in parabolicCylinder z'.1 z'.2 (4 * ρ),
          ENNReal.ofReal (spatialGradientSq u Du y) := lintegral_mono_set hball
      _ ≤ _ := lintegral_mono_set (parabolicCylinder_mono (by positivity)
        (by nlinarith only [hρ]))
  calc
    _ ≤ ENNReal.ofReal (M ^ 2 * (8 * ρ) ^ (9 / 5 : ℝ)) := hD.trans (by
      have hscale : 2 * (4 * ρ) = 8 * ρ := by ring
      simpa [hscale] using hb.2)
    _ = gradientSmallConstant M * ENNReal.ofReal (ρ ^ (9 / 5 : ℝ)) := by
      dsimp [gradientSmallConstant]
      rw [Real.mul_rpow (by norm_num) hρ.le,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring_nf
private theorem interp_scale_ennreal {M R : ℝ} (hM : 0 ≤ M) (hR : 0 < R) :
    (ENNReal.ofReal (M * (2 * R) ^ (9 / 10 : ℝ))) ^ (3 / 2 : ℝ) * (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
      ((ENNReal.ofReal (M ^ 2 * (2 * R) ^ (9 / 5 : ℝ))) ^ (3 / 4 : ℝ) * ENNReal.ofReal (R ^ 2) ^
        (1 / 4 : ℝ) + ENNReal.ofReal (R ^ 2) * ((Real.toNNReal (32 / R) : ℝ≥0∞) * ENNReal.ofReal
        (M * (2 * R) ^ (9 / 10 : ℝ))) ^ (3 / 2 : ℝ)) =
      ENNReal.ofReal ((M * (2 * R) ^ (9 / 10 : ℝ)) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ) * ((M ^ 2
        * (2 * R) ^ (9 / 5 : ℝ)) ^ (3 / 4 : ℝ) * (R ^ 2) ^ (1 / 4 : ℝ) + R ^ 2 * ((32 / R) * (M *
        (2 * R) ^ (9 / 10 : ℝ))) ^ (3 / 2 : ℝ))) := by
  have hto : (Real.toNNReal (32 / R) : ℝ≥0∞) = ENNReal.ofReal (32 / R) :=
    ENNReal.ofNNReal_toNNReal _
  rw [hto]
  have hA : 0 ≤ M * (2 * R) ^ (9 / 10 : ℝ) := by positivity
  have hG : 0 ≤ M ^ 2 * (2 * R) ^ (9 / 5 : ℝ) := by positivity
  have hR2 : 0 ≤ R ^ 2 := by positivity
  have h32R : 0 ≤ 32 / R := by positivity
  have hA_pow := ENNReal.ofReal_rpow_of_nonneg hA (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have htwo_pow := ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hG_pow := ENNReal.ofReal_rpow_of_nonneg hG (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have hR_pow := ENNReal.ofReal_rpow_of_nonneg hR2 (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hprod : ENNReal.ofReal (32 / R) * ENNReal.ofReal (M * (2 * R) ^
      (9 / 10 : ℝ)) = ENNReal.ofReal ((32 / R) * (M * (2 * R) ^ (9 / 10 : ℝ))) := by
    rw [← ENNReal.ofReal_mul h32R]
  have hprod_pow := ENNReal.ofReal_rpow_of_nonneg (mul_nonneg h32R hA)
    (by norm_num : (0 : ℝ) ≤ 3 / 2)
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
    hA_pow, htwo_pow, hG_pow, hR_pow, hprod, hprod_pow]
  have h₁ : ENNReal.ofReal ((M ^ 2 * (2 * R) ^ (9 / 5 : ℝ)) ^ (3 / 4 : ℝ)) *
      ENNReal.ofReal ((R ^ 2) ^ (1 / 4 : ℝ)) = ENNReal.ofReal
        ((M ^ 2 * (2 * R) ^ (9 / 5 : ℝ)) ^ (3 / 4 : ℝ) * (R ^ 2) ^ (1 / 4 : ℝ)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
  have h₂ : ENNReal.ofReal (R ^ 2) * ENNReal.ofReal
      (((32 / R) * (M * (2 * R) ^ (9 / 10 : ℝ))) ^ (3 / 2 : ℝ)) = ENNReal.ofReal
        (R ^ 2 * ((32 / R) * (M * (2 * R) ^ (9 / 10 : ℝ))) ^ (3 / 2 : ℝ)) := by
    rw [← ENNReal.ofReal_mul hR2]
  rw [h₁, h₂]
  have hs : ENNReal.ofReal ((M ^ 2 * (2 * R) ^ (9 / 5 : ℝ)) ^ (3 / 4 : ℝ) *
      (R ^ 2) ^ (1 / 4 : ℝ)) + ENNReal.ofReal (R ^ 2 *
        ((32 / R) * (M * (2 * R) ^ (9 / 10 : ℝ))) ^ (3 / 2 : ℝ)) = ENNReal.ofReal
      (((M ^ 2 * (2 * R) ^ (9 / 5 : ℝ)) ^ (3 / 4 : ℝ) * (R ^ 2) ^ (1 / 4 : ℝ)) +
        R ^ 2 * ((32 / R) * (M * (2 * R) ^ (9 / 10 : ℝ))) ^ (3 / 2 : ℝ)) := by
    rw [← ENNReal.ofReal_add] <;> positivity
  rw [hs, ← ENNReal.ofReal_mul (Real.rpow_nonneg hA _),
    ← ENNReal.ofReal_mul (by positivity)]
private theorem power_expression {M R : ℝ} (hM : 0 ≤ M) (hR : 0 < R) :
    (M * (2 * R) ^ (9 / 10 : ℝ)) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ) *
        ((M ^ 2 * (2 * R) ^ (9 / 5 : ℝ)) ^ (3 / 4 : ℝ) * (R ^ 2) ^ (1 / 4 : ℝ) +
          R ^ 2 * ((32 / R) * (M * (2 * R) ^ (9 / 10 : ℝ))) ^ (3 / 2 : ℝ)) =
      M ^ 3 * (2 : ℝ) ^ (1 / 2 : ℝ) * R ^ (16 / 5 : ℝ) *
        ((2 : ℝ) ^ (27 / 10 : ℝ) + (32 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (27 / 10 : ℝ)) := by
  have hX : 0 ≤ 2 * R := by positivity
  have hXpos : 0 < 2 * R := by positivity
  have hR0 : 0 ≤ R := hR.le
  have hMpow (a : ℝ) : (M * (2 * R) ^ (9 / 10 : ℝ)) ^ a = M ^ a *
      (2 * R) ^ ((9 / 10 : ℝ) * a) := by
    rw [Real.mul_rpow hM (Real.rpow_nonneg hX _), ← Real.rpow_mul hX]
  have hM2pow (a : ℝ) : (M ^ 2 * (2 * R) ^ (9 / 5 : ℝ)) ^ a = M ^ (2 * a) *
      (2 * R) ^ ((9 / 5 : ℝ) * a) := by
    calc
      _ = (M ^ 2) ^ a * ((2 * R) ^ (9 / 5 : ℝ)) ^ a :=
        Real.mul_rpow (sq_nonneg M) (Real.rpow_nonneg hX _)
      _ = _ := by
        have hm : (M ^ 2) ^ a = M ^ (2 * a) := by
          rw [show (M ^ 2) ^ a = (M ^ (2 : ℝ)) ^ a by norm_num [Real.rpow_natCast],
            (Real.rpow_mul hM 2 a).symm]
        rw [hm, ← Real.rpow_mul hX]
  have hprod : ((32 / R) * (M * (2 * R) ^ (9 / 10 : ℝ))) ^ (3 / 2 : ℝ) =
      (32 / R) ^ (3 / 2 : ℝ) * (M * (2 * R) ^ (9 / 10 : ℝ)) ^ (3 / 2 : ℝ) :=
    Real.mul_rpow (by positivity) (mul_nonneg hM (Real.rpow_nonneg hX _))
  have hdiv : (32 / R) ^ (3 / 2 : ℝ) = (32 : ℝ) ^ (3 / 2 : ℝ) /
      R ^ (3 / 2 : ℝ) := Real.div_rpow (by norm_num) hR0 _
  rw [hprod, hMpow, hM2pow, hdiv]
  norm_num
  ring_nf
  have hM3 : (M ^ (3 / 2 : ℝ)) ^ (2 : ℕ) = M ^ (3 : ℝ) := by
    rw [show (M ^ (3 / 2 : ℝ)) ^ (2 : ℕ) = (M ^ (3 / 2 : ℝ)) ^ (2 : ℝ) by
      norm_num [Real.rpow_natCast], (Real.rpow_mul hM (3 / 2) 2).symm]; norm_num
  have hR2 : (R ^ (2 : ℕ)) ^ (1 / 4 : ℝ) = R ^ (1 / 2 : ℝ) := by
    rw [show (R ^ (2 : ℕ)) ^ (1 / 4 : ℝ) = (R ^ (2 : ℝ)) ^ (1 / 4 : ℝ) by
      norm_num [Real.rpow_natCast], (Real.rpow_mul hR.le 2 (1 / 4)).symm]; norm_num
  have hRcancel : R ^ (2 : ℕ) * (R ^ (3 / 2 : ℝ))⁻¹ = R ^ (1 / 2 : ℝ) := by
    calc
      _ = R ^ (2 : ℝ) * (R ^ (3 / 2 : ℝ))⁻¹ := by norm_num [Real.rpow_natCast]
      _ = R ^ (2 : ℝ) * R ^ (-(3 / 2 : ℝ)) := by rw [Real.rpow_neg hR.le]
      _ = R ^ ((2 : ℝ) + (-(3 / 2 : ℝ))) :=
        (Real.rpow_add hR 2 (-(3 / 2 : ℝ))).symm
      _ = _ := by norm_num
  have h2R : ((R * 2) ^ (27 / 20 : ℝ)) ^ (2 : ℕ) =
      R ^ (27 / 10 : ℝ) * 2 ^ (27 / 10 : ℝ) := by
    rw [show ((R * 2) ^ (27 / 20 : ℝ)) ^ (2 : ℕ) =
      ((R * 2) ^ (27 / 20 : ℝ)) ^ (2 : ℝ) by norm_num [Real.rpow_natCast],
      (Real.rpow_mul (by positivity) _ _).symm, Real.mul_rpow hR.le (by norm_num)]; norm_num
  have hRterm : R ^ (2 : ℕ) * R ^ (27 / 10 : ℝ) *
      (R ^ (3 / 2 : ℝ))⁻¹ = R ^ (16 / 5 : ℝ) := by
    calc
      _ = R ^ (2 : ℝ) * R ^ (27 / 10 : ℝ) * R ^ (-(3 / 2 : ℝ)) := by
        rw [Real.rpow_neg hR.le]; norm_num [Real.rpow_natCast]
      _ = R ^ ((2 : ℝ) + 27 / 10) * R ^ (-(3 / 2 : ℝ)) := by rw [Real.rpow_add hR]
      _ = R ^ (((2 : ℝ) + 27 / 10) + (-(3 / 2 : ℝ))) :=
        (Real.rpow_add hR _ _).symm
      _ = _ := by norm_num
  have hRterm' : R ^ (27 / 10 : ℝ) * R ^ (1 / 2 : ℝ) = R ^ (16 / 5 : ℝ) := by
    rw [← Real.rpow_add hR]; norm_num
  rw [hM3, hR2, h2R]
  ring_nf
  have hfirst : M ^ 3 * R ^ 2 * R ^ (27 / 10 : ℝ) * 2 ^ (27 / 10 : ℝ) *
        2 ^ (1 / 2 : ℝ) * 32 ^ (3 / 2 : ℝ) * (R ^ (3 / 2 : ℝ))⁻¹ =
      2 ^ (27 / 10 : ℝ) * 2 ^ (1 / 2 : ℝ) * 32 ^ (3 / 2 : ℝ) * M ^ 3 * R ^ (16 / 5 : ℝ) := by
    calc
      _ = 2 ^ (27 / 10 : ℝ) * 2 ^ (1 / 2 : ℝ) * 32 ^ (3 / 2 : ℝ) *
          M ^ 3 * (R ^ 2 * R ^ (27 / 10 : ℝ) * (R ^ (3 / 2 : ℝ))⁻¹) := by ring_nf
      _ = _ := by rw [hRterm]
  have hsecond : M ^ 3 * R ^ (27 / 10 : ℝ) * 2 ^ (27 / 10 : ℝ) *
        2 ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ) = 2 ^ (27 / 10 : ℝ) *
      2 ^ (1 / 2 : ℝ) * M ^ 3 * R ^ (16 / 5 : ℝ) := by
    calc
      _ = 2 ^ (27 / 10 : ℝ) * 2 ^ (1 / 2 : ℝ) * M ^ 3 *
          (R ^ (27 / 10 : ℝ) * R ^ (1 / 2 : ℝ)) := by ring_nf
      _ = _ := by rw [hRterm']
  calc
    _ = (M ^ 3 * R ^ 2 * R ^ (27 / 10 : ℝ) * 2 ^ (27 / 10 : ℝ) *
          2 ^ (1 / 2 : ℝ) * 32 ^ (3 / 2 : ℝ) * (R ^ (3 / 2 : ℝ))⁻¹) +
        (M ^ 3 * R ^ (27 / 10 : ℝ) * 2 ^ (27 / 10 : ℝ) *
          2 ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ)) := by
      field_simp [ne_of_gt hR, ne_of_gt (Real.rpow_pos_of_pos hR _)]
      ring_nf
      norm_num [Real.rpow_natCast]
    _ = _ := by rw [hfirst, hsecond]
    _ = _ := by ring_nf
private theorem component_abs_le_vec3norm (v : Vec3) (i : Fin 3) :
    |v i| ≤ vec3EuclideanNorm v := by
  unfold vec3EuclideanNorm
  exact Real.abs_le_sqrt (Finset.single_le_sum
    (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))
private theorem velocity_small_cell {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z₀ : ParabolicPoint} {r₂ M ρ : ℝ} (hr₂ : 0 < r₂) (hM : 1 ≤ M) (hρ : 0 < ρ)
    (hρsmall : 128 * ρ ≤ r₂) (hcarrier : Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I)
    (hdecay : ∀ z : ParabolicPoint, z ∈ Metric.ball z₀ r₂ → ∀ r, 0 < r → r < r₂ →
      max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤ M * r ^ (2 / 5 : ℝ))
    {Q₂ : Set ParabolicPoint} {i : Fin 3} (hQ₂ : Q₂ = Metric.ball z₀ (r₂ / 4))
    {z : ParabolicPoint} (hz : Metric.ball z ρ ∩ Q₂ ≠ ∅) :
    ballPowerIntegral 3 (Q₂.indicator (fun w => u w i)) z ρ ≤
      velocitySmallConstant M * ENNReal.ofReal (ρ ^ (16 / 5 : ℝ)) := by
  obtain ⟨w, z', Ω', J, -, -, -, hbox, hball, hsub8, hcyl8, hdec⟩ :=
    local_step2_setup hsol hr₂ hρ hρsmall hcarrier hdecay hQ₂ hz
  have hdec' : max (max (alpha u z' (2 * (4 * ρ)))
      (beta u Du z' (2 * (4 * ρ)))) (delta p z' (2 * (4 * ρ)) ^ 2) ≤
      M * (2 * (4 * ρ)) ^ (2 / 5 : ℝ) := by
    have hscale : 2 * (4 * ρ) = 8 * ρ := by ring
    simpa [hscale] using hdec
  have hb := decay_bounds hsol (z := z') (R := 4 * ρ) (M := M) (by positivity) hM
    (by convert hsub8 using 1; ring_nf) hdec'
  have hinter := step2_cylinder_l3_bound (q := q) hsol (x := z'.1) (t := z'.2)
    (r := 4 * ρ) (by positivity) hbox (by convert hcyl8 using 1; ring_nf)
    (Abar := ENNReal.ofReal (M * (2 * (4 * ρ)) ^ (9 / 10 : ℝ)))
    (Gbar := ENNReal.ofReal (M ^ 2 * (2 * (4 * ρ)) ^ (9 / 5 : ℝ)))
    (by finiteness) (by simpa using hb.1) (by simpa using hb.2)
  have hballint : ballPowerIntegral 3 (Q₂.indicator (fun w => u w i)) z ρ ≤
      ∫⁻ y in parabolicCylinder z'.1 z'.2 (4 * ρ),
      ENNReal.ofReal (vec3EuclideanNorm (u y)) ^ (3 : ℝ) := by
    unfold ballPowerIntegral
    calc
      _ ≤ ∫⁻ y in Metric.ball z ρ,
          ENNReal.ofReal (vec3EuclideanNorm (u y)) ^ (3 : ℝ) := by
        apply lintegral_mono; intro y
        by_cases hy : y ∈ Q₂
        · simp only [Set.indicator_of_mem hy]
          exact ENNReal.rpow_le_rpow
            (ENNReal.ofReal_le_ofReal (component_abs_le_vec3norm (u y) i))
            (by norm_num)
        · simp [Set.indicator_of_notMem hy]
      _ ≤ _ := lintegral_mono_set hball
  let C : ℝ≥0∞ := (ENNReal.ofReal ((3 : ℝ) ^ ((3 : ℝ) / 2 - 1)) * 3) * localSobolevConstant ^ (3 /
    2 : ℝ)
  have hscale := interp_scale_ennreal (M := M) (R := 4 * ρ) (by linarith only [hM]) (by positivity)
  have hpower := power_expression (M := M) (R := 4 * ρ) (by linarith only [hM]) (by positivity)
  have hfour : (4 * ρ) ^ (16 / 5 : ℝ) = (4 : ℝ) ^ (16 / 5 : ℝ) * ρ ^ (16 / 5 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hρ.le]
  let E : ℝ≥0∞ := ENNReal.ofReal (M * (2 * (4 * ρ)) ^ (9 / 10 : ℝ)) ^ (3 / 2 : ℝ) *
      (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) * (ENNReal.ofReal (M ^ 2 * (2 * (4 * ρ)) ^ (9 / 5 : ℝ)) ^
        (3 / 4 : ℝ) * ENNReal.ofReal ((4 * ρ) ^ 2) ^ (1 / 4 : ℝ) + ENNReal.ofReal ((4 * ρ) ^ 2) *
          ((Real.toNNReal (32 / (4 * ρ)) : ℝ≥0∞) * ENNReal.ofReal (M * (2 * (4 * ρ)) ^ (9 / 10 :
            ℝ))) ^ (3 / 2 : ℝ))
  calc
    _ ≤ C * E := by
      exact hballint.trans (by simpa [E, C, mul_assoc] using hinter)
    _ = C * ENNReal.ofReal (M ^ 3 * (2 : ℝ) ^ (1 / 2 : ℝ) *
        ((2 : ℝ) ^ (27 / 10 : ℝ) + (32 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (27 / 10 : ℝ)) *
          (4 * ρ) ^ (16 / 5 : ℝ)) := by
      dsimp [E]
      rw [hscale]
      congr 1
      rw [hpower]
      ring_nf
    _ = velocitySmallConstant M * ENNReal.ofReal (ρ ^ (16 / 5 : ℝ)) := by
      dsimp [velocitySmallConstant, C]
      rw [hfour]
      have hof : ENNReal.ofReal (M ^ 3 * (2 : ℝ) ^ (1 / 2 : ℝ) *
          ((2 : ℝ) ^ (27 / 10 : ℝ) + (32 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (27 / 10 : ℝ)) *
          ((4 : ℝ) ^ (16 / 5 : ℝ) * ρ ^ (16 / 5 : ℝ))) = ENNReal.ofReal
          (M ^ 3 * (2 : ℝ) ^ (1 / 2 : ℝ) * ((2 : ℝ) ^ (27 / 10 : ℝ) +
            (32 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (27 / 10 : ℝ)) * (4 : ℝ) ^ (16 / 5 : ℝ)) *
            ENNReal.ofReal (ρ ^ (16 / 5 : ℝ)) := by
        have hreal : M ^ 3 * (2 : ℝ) ^ (1 / 2 : ℝ) * ((2 : ℝ) ^ (27 / 10 : ℝ) +
            (32 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (27 / 10 : ℝ)) * ((4 : ℝ) ^ (16 / 5 : ℝ) *
              ρ ^ (16 / 5 : ℝ)) = (M ^ 3 * (2 : ℝ) ^ (1 / 2 : ℝ) * ((2 : ℝ) ^ (27 / 10 : ℝ) +
                (32 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (27 / 10 : ℝ)) * (4 : ℝ) ^ (16 / 5 : ℝ)) *
              ρ ^ (16 / 5 : ℝ) := by ring_nf
        rw [hreal]
        exact ENNReal.ofReal_mul (by positivity)
      rw [hof]
      ring
private theorem ballPowerIntegral_le_of_subset {p : ℝ} {Q C : Set ParabolicPoint}
    {g : ParabolicPoint → ℝ} {F : ParabolicPoint → ℝ≥0∞} {z : ParabolicPoint} {r : ℝ}
    (hp : 0 < p) (hQ : MeasurableSet Q) (hQC : Q ⊆ C)
    (hpoint : ∀ y, ENNReal.ofReal |g y| ^ p ≤ F y) : ballPowerIntegral p (Q.indicator g) z r ≤ ∫⁻
      y in C, F y := by
  unfold ballPowerIntegral
  have hind : (fun y => ENNReal.ofReal |Q.indicator g y| ^ p) =
      Q.indicator (fun y => ENNReal.ofReal |g y| ^ p) := by
    funext y
    by_cases hy : y ∈ Q <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem,
      hy, ENNReal.zero_rpow_of_pos hp]
  rw [hind, setLIntegral_indicator hQ]
  calc
    _ ≤ ∫⁻ y in Q ∩ Metric.ball z r, F y :=
      lintegral_mono (fun y => hpoint y)
    _ ≤ _ := lintegral_mono_set (inter_subset_left.trans hQC)
private theorem cylinder_velocity_integral_lt_top {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) {x : Vec3} {t r : ℝ} (hr : 0 < r)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    (hcyl : parabolicCylinder x t (2 * r) ⊆ spaceTimeSet Ω' J)
    (hsub : closure (parabolicCylinder x t (2 * r)) ⊆ spaceTimeSet Ω I) :
    (∫⁻ w in parabolicCylinder x t r,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) < ⊤ := by
  have hEtop := sws_timeSliceEnergyEssSup_lt_top hsol (z := (x, t)) (r := 2 * r)
    (by positivity) hsub
  have hG := sws_gradient_integral_lt_top hsol (z := (x, t)) (r := 2 * r) (by positivity) hsub
  let E := essSup (fun s => ∫⁻ y in vec3Ball x (2 * r),
    ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ))
    (volume.restrict (Set.Ioc (t - r ^ 2) t))
  have hTsub : Set.Ioc (t - r ^ 2) t ⊆ Set.Ioc (t - (2 * r) ^ 2) t := by
    intro s hs; exact ⟨by nlinarith only [hs.1, hr], hs.2⟩
  have hpoint : ∀ s, (∫⁻ y in vec3Ball x (2 * r),
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)) ≤
      timeSliceBallEnergy x (2 * r) s (fun w => vec3EuclideanNorm (u w)) := by
    intro s; apply le_of_eq; apply lintegral_congr; intro y
    rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg (u (y, s)))]
  have hE : E < ⊤ := lt_of_le_of_lt
    (essSup_mono_measure_and_ae (Measure.restrict_mono_set volume hTsub)
      (Filter.Eventually.of_forall hpoint)) (by simpa [timeSliceEnergyEssSup] using hEtop)
  let A := E ^ (1 / 2 : ℝ) + 1
  let G := (∫⁻ w in parabolicCylinder x t (2 * r),
      ENNReal.ofReal (spatialGradientSq u Du w)) + 1
  have h := step2_cylinder_l3_bound hsol hr hbox hcyl (Abar := A) (Gbar := G)
    (by dsimp [A]; exact ENNReal.add_lt_top.mpr ⟨
      ENNReal.rpow_lt_top_of_nonneg (by positivity) hE.ne, ENNReal.coe_lt_top⟩)
    (by exact (by dsimp [A, E]; exact le_add_right le_rfl))
    (by dsimp [G]; exact le_add_right le_rfl)
  apply lt_of_le_of_lt h
  have hA : A < ⊤ := by
    dsimp [A]; exact ENNReal.add_lt_top.mpr ⟨
      ENNReal.rpow_lt_top_of_nonneg (by positivity) hE.ne, ENNReal.coe_lt_top⟩
  have hG' : G < ⊤ := by
    dsimp [G]
    exact ENNReal.add_lt_top.mpr ⟨hG, ENNReal.coe_lt_top⟩
  have hC : (ENNReal.ofReal ((3 : ℝ) ^ ((3 : ℝ) / 2 - 1)) * 3) *
      localSobolevConstant ^ (3 / 2 : ℝ) < ⊤ := by
    apply ENNReal.mul_lt_top
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by unfold localSobolevConstant; finiteness)
  have hsum : G ^ (3 / 4 : ℝ) * ENNReal.ofReal (r ^ 2) ^ (1 / 4 : ℝ) +
      ENNReal.ofReal (r ^ 2) * ((Real.toNNReal (32 / r) : ℝ≥0∞) * A) ^
        (3 / 2 : ℝ) < ⊤ := by
    refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
    · exact ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hG'.ne)
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
    · apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (ENNReal.mul_ne_top ENNReal.coe_ne_top hA.ne)
  apply ENNReal.mul_lt_top
  · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hC
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hA.ne))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by norm_num))
  · exact hsum
/-! The Step 2 decay certificate is converted into the three Morrey bounds. -/
theorem step2_morrey_form
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) {z₀ : ParabolicPoint} {r₂ M : ℝ}
    (hr₂ : 0 < r₂) (hM : 1 ≤ M)
    (hcarrier : Metric.ball (z₀ : ParabolicPoint) (2 * r₂) ⊆ spaceTimeSet Ω I)
    (hdecay : ∀ z : ParabolicPoint, z ∈ Metric.ball z₀ r₂ → ∀ r, 0 < r → r < r₂ →
      max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤ M * r ^ (2 / 5 : ℝ)) :
    ∃ Kᵤ K_Du Kₚ : ℝ≥0∞, Kᵤ < ⊤ ∧ K_Du < ⊤ ∧ Kₚ < ⊤ ∧
      morreyVecMem 3 (25 / 3 : ℝ) (Metric.ball z₀ (r₂ / 4)) u ∧
      (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ) (Metric.ball z₀ (r₂ / 4)) (fun z => Du z i)) ∧
      morreyBallNorm (3 / 2 : ℝ) (25 / 8 : ℝ) ((Metric.ball z₀ (r₂ / 4)).indicator p) < ⊤ ∧
      (∀ i : Fin 3, morreyBallNorm 3 (25 / 3 : ℝ) ((Metric.ball z₀ (r₂ / 4)).indicator (fun z => u
        z i)) ≤ Kᵤ) ∧
      (∀ i : Fin 3, ∀ j : Fin 3, morreyBallNorm 2 (25 / 8 : ℝ) ((Metric.ball z₀ (r₂ /
        4)).indicator (fun z => Du z i j)) ≤ K_Du) ∧
      morreyBallNorm (3 / 2 : ℝ) (25 / 8 : ℝ) ((Metric.ball z₀ (r₂ / 4)).indicator p) ≤ Kₚ := by
  let Q₂ : Set ParabolicPoint := Metric.ball z₀ (r₂ / 4)
  let r₀ : ℝ := r₂ / 128
  let zG : ParabolicPoint := (z₀.1, z₀.2 + (r₂ / 4) ^ 2)
  have hzG : dist zG z₀ = r₂ / 4 := by
    dsimp [zG]; exact step2_shifted_center_dist (w := z₀) (r := r₂ / 4) (by positivity)
  have hclose : closure (parabolicCylinder zG.1 zG.2 r₂) ⊆ Metric.ball z₀ (2 * r₂) := by
    intro y hy
    have hyc := step2_closure_cylinder_subset_closedBall (x := zG.1) (t := zG.2) (r := r₂) (by
      positivity) hy
    have htri := dist_triangle y zG z₀; rw [Metric.mem_ball]
    nlinarith only [htri, Metric.mem_closedBall.mp hyc, hzG, hr₂]
  obtain ⟨Ω', J, hbox, hcylbig⟩ := exists_localBox_of_closure_subset hsol.1 hsol.2.1 hr₂
    (hclose.trans hcarrier)
  have hcyl : parabolicCylinder zG.1 zG.2 (r₂ / 2) ⊆ spaceTimeSet Ω' J :=
    (parabolicCylinder_mono (by positivity) (by nlinarith only [hr₂])).trans hcylbig
  have hcover : Q₂ ⊆ parabolicCylinder zG.1 zG.2 (r₂ / 2) := by
    intro y hy; change y ∈ Metric.ball z₀ (r₂ / 4) at hy
    have h := metricBall_subset_parabolicCylinder_doubled z₀ (r := r₂ / 4) (by positivity) hy
    dsimp [zG]; convert h using 1; ring_nf
  let IU := ∫⁻ w in parabolicCylinder zG.1 zG.2 (r₂ / 2), ENNReal.ofReal (vec3EuclideanNorm (u w))
    ^ (3 : ℝ)
  let ID := ∫⁻ w in parabolicCylinder zG.1 zG.2 (r₂ / 2), ENNReal.ofReal (spatialGradientSq u Du w)
  let IP := ∫⁻ w in parabolicCylinder zG.1 zG.2 (r₂ / 2), ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)
  have hsubsmall : closure (parabolicCylinder zG.1 zG.2 (r₂ / 2)) ⊆ spaceTimeSet Ω I :=
    (closure_mono (parabolicCylinder_mono (by positivity) (by nlinarith only [hr₂]))).trans
      (hclose.trans hcarrier)
  have hsubhelper : closure (parabolicCylinder zG.1 zG.2 (2 * (r₂ / 2))) ⊆ spaceTimeSet Ω I := by
    apply (closure_mono (parabolicCylinder_mono (x := zG.1) (t := zG.2) (r₁ := 2 * (r₂ / 2))
      (r₂ := r₂) (by positivity) (by nlinarith only))).trans; exact hclose.trans hcarrier
  have hcylbig' : parabolicCylinder zG.1 zG.2 (2 * (r₂ / 2)) ⊆ spaceTimeSet Ω' J := by
    convert hcylbig using 1; ring_nf
  have hIU : IU < ⊤ := by
    dsimp [IU]
    exact cylinder_velocity_integral_lt_top hsol (by positivity) hbox hcylbig' hsubhelper
  have hID : ID < ⊤ := by
    dsimp [ID]
    exact sws_gradient_integral_lt_top hsol (by positivity) hsubsmall
  have hIP : IP < ⊤ := by
    dsimp [IP]
    exact sws_pressure_integral_lt_top hsol (by positivity) hsubsmall
  let KU := max ((velocitySmallConstant M) ^ (1 / 3 : ℝ))
    ((ENNReal.ofReal r₀) ^ (-(5 * (1 / 3 - 1 / (25 / 3 : ℝ)))) * IU ^ (1 / 3 : ℝ))
  let KD := max ((gradientSmallConstant M) ^ (1 / 2 : ℝ))
    ((ENNReal.ofReal r₀) ^ (-(5 * (1 / 2 - 1 / (25 / 8 : ℝ)))) * ID ^ (1 / 2 : ℝ))
  let KP := max ((pressureSmallConstant M) ^ (2 / 3 : ℝ))
    ((ENNReal.ofReal r₀) ^ (-(5 * (1 / (3 / 2) - 1 / (25 / 8 : ℝ)))) * IP ^ (2 / 3 : ℝ))
  have hr₀ : 0 < r₀ := by dsimp [r₀]; positivity
  have hC : (ENNReal.ofReal ((3 : ℝ) ^ ((3 : ℝ) / 2 - 1)) * 3) * localSobolevConstant ^ (3 / 2 :
    ℝ) < ⊤ := by
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by unfold localSobolevConstant; finiteness))
  have hVel : velocitySmallConstant M < ⊤ := by
    dsimp [velocitySmallConstant]
    exact ENNReal.mul_lt_top hC ENNReal.ofReal_lt_top
  have hGrad : gradientSmallConstant M < ⊤ := by dsimp [gradientSmallConstant]; exact
    ENNReal.ofReal_lt_top
  have hPres : pressureSmallConstant M < ⊤ := by dsimp [pressureSmallConstant]; exact
    ENNReal.ofReal_lt_top
  have hKU : KU < ⊤ := by
    dsimp [KU]
    exact max_lt (ENNReal.rpow_lt_top_of_nonneg (by positivity) hVel.ne) (by finiteness)
  have hKD : KD < ⊤ := by
    dsimp [KD]
    exact max_lt (ENNReal.rpow_lt_top_of_nonneg (by positivity) hGrad.ne) (by finiteness)
  have hKP : KP < ⊤ := by
    dsimp [KP]
    exact max_lt (ENNReal.rpow_lt_top_of_nonneg (by positivity) hPres.ne) (by finiteness)
  have hu : ∀ i : Fin 3, ∀ z : ParabolicPoint, ∀ r : ℝ, 0 < r → morreyBallCell 3 (25 / 3 : ℝ)
    (Q₂.indicator (fun w => u w i)) z r ≤ KU := by
    intro i z r hr
    by_cases hdis : Metric.ball z r ∩ Q₂ = ∅
    · unfold morreyBallCell; rw [ballPowerIntegral_zero (by norm_num) hdis]; simp
    by_cases hs : 128 * r ≤ r₂
    · exact (cell_bound_ennreal (p := 3) (q := 25 / 3) (a := 16 / 5) (K := velocitySmallConstant M)
        (g := Q₂.indicator (fun w => u w i)) (z := z) (r := r) (by norm_num) hr (by norm_num) (by
          norm_num)
        (velocity_small_cell hsol hr₂ hM hr hs hcarrier hdecay rfl hdis)).trans (le_max_left _ _)
    · have hrr : r₀ ≤ r := by dsimp [r₀]; nlinarith only [hr₂, hr, hs]
      exact (cell_bound_global (p := 3) (q := 25 / 3) (r₀ := r₀) (I := IU)
        (g := Q₂.indicator (fun w => u w i)) (z := z) (r := r) (by norm_num) (by norm_num) hr₀ hrr
        (ballPowerIntegral_le_of_subset (p := 3) (Q := Q₂) (C := parabolicCylinder zG.1 zG.2 (r₂ /
          2))
          (g := fun w => u w i) (F := fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ))
          (z := z) (r := r) (by norm_num) measurableSet_ball hcover (by
            intro y
            exact ENNReal.rpow_le_rpow
              (ENNReal.ofReal_le_ofReal (component_abs_le_vec3norm (u y) i))
              (by norm_num)))).trans
        (le_max_right _ _)
  have hDu : ∀ i : Fin 3, ∀ j : Fin 3, ∀ z : ParabolicPoint, ∀ r : ℝ, 0 < r → morreyBallCell 2 (25
    / 8 : ℝ) (Q₂.indicator (fun w => Du w i j)) z r ≤ KD := by
    intro i j z r hr
    by_cases hdis : Metric.ball z r ∩ Q₂ = ∅
    · unfold morreyBallCell; rw [ballPowerIntegral_zero (by norm_num) hdis]; simp
    by_cases hs : 128 * r ≤ r₂
    · exact (cell_bound_ennreal (p := 2) (q := 25 / 8) (a := 9 / 5) (K := gradientSmallConstant M)
        (g := Q₂.indicator (fun w => Du w i j)) (z := z) (r := r) (by norm_num) hr (by norm_num)
          (by norm_num)
        (gradient_small_cell hsol hr₂ hM hr hs hcarrier hdecay rfl hdis)).trans (le_max_left _ _)
    · have hrr : r₀ ≤ r := by dsimp [r₀]; nlinarith only [hr₂, hr, hs]
      exact (cell_bound_global (p := 2) (q := 25 / 8) (r₀ := r₀) (I := ID)
        (g := Q₂.indicator (fun w => Du w i j)) (z := z) (r := r) (by norm_num) (by norm_num) hr₀
          hrr
        (ballPowerIntegral_le_of_subset (p := 2) (Q := Q₂) (C := parabolicCylinder zG.1 zG.2 (r₂ /
          2))
          (g := fun w => Du w i j) (F := fun w => ENNReal.ofReal (spatialGradientSq u Du w)) (z :=
            z) (r := r)
          (by norm_num) measurableSet_ball hcover (by
            intro y
            rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
            exact ENNReal.ofReal_le_ofReal (by
              unfold spatialGradientSq
              have hterm : (Du y i j) ^ 2 ≤ ∑ k : Fin 3, ∑ l : Fin 3, (Du y k l) ^ 2 :=
                (Finset.single_le_sum (fun l _ => sq_nonneg (Du y i l)) (Finset.mem_univ j)).trans
                  (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg (Du y
                    k l)))
                    (Finset.mem_univ i))
              simpa [sq_abs] using hterm)))).trans
        (le_max_right _ _)
  have hp : ∀ z : ParabolicPoint, ∀ r : ℝ, 0 < r → morreyBallCell (3 / 2 : ℝ) (25 / 8 : ℝ)
    (Q₂.indicator p) z r ≤ KP := by
    intro z r hr
    by_cases hdis : Metric.ball z r ∩ Q₂ = ∅
    · unfold morreyBallCell; rw [ballPowerIntegral_zero (by norm_num) hdis]; simp
    by_cases hs : 128 * r ≤ r₂
    · exact (cell_bound_ennreal (p := 3 / 2) (q := 25 / 8) (a := 13 / 5) (K :=
      pressureSmallConstant M)
        (g := Q₂.indicator p) (z := z) (r := r) (by norm_num) hr (by norm_num) (by norm_num)
        (pressure_small_cell hsol hr₂ hM hr hs hcarrier hdecay rfl hdis)).trans (by
          dsimp [KP]
          norm_num)
    · have hrr : r₀ ≤ r := by dsimp [r₀]; nlinarith only [hr₂, hr, hs]
      exact (cell_bound_global (p := 3 / 2) (q := 25 / 8) (r₀ := r₀) (I := IP)
        (g := Q₂.indicator p) (z := z) (r := r) (by norm_num) (by norm_num) hr₀ hrr
        (ballPowerIntegral_le_of_subset (p := 3 / 2) (Q := Q₂) (C := parabolicCylinder zG.1 zG.2
          (r₂ / 2))
          (g := p) (F := fun w => ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) (z := z) (r := r)
          (by norm_num) measurableSet_ball hcover (by intro y; rfl))).trans (by
          dsimp [KP]
          norm_num)
  have hmem := step2_morrey_balls hKU hKD hKP (by simpa [Q₂] using hu) (by simpa [Q₂] using hDu)
    (by simpa [Q₂] using hp)
  refine ⟨KU, KD, KP, hKU, hKD, hKP, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Q₂] using hmem.1
  · intro i; simpa [Q₂] using hmem.2.1 i
  · simpa [Q₂] using hmem.2.2
  · intro i; exact morreyBallNorm_le_of_cell_bound' (by simpa [Q₂] using hu i)
  · intro i j; exact morreyBallNorm_le_of_cell_bound' (by simpa [Q₂] using hDu i j)
  · exact morreyBallNorm_le_of_cell_bound' (by simpa [Q₂] using hp)
end CKN

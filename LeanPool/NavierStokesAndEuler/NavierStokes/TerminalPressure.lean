/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.TerminalStress
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricHeatTail
public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothParameterIntegral
public import LeanPool.NavierStokesAndEuler.NavierStokes.TailCone

@[expose] public section

/-!
# Canonical pressure of the physical terminal heat tail

The heat parameter is the physical time `1-t`.  The pressure is the actual
improper radial integral.  Its regularity is obtained by separating the pure
heat tail from a compact taper correction.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace NavierStokes.TerminalPressure


/-- The exponent of the physical angular heat amplitude. -/
noncomputable def amplitudeExponent (h : ℝ) : ℝ := 1 / 2 + h

/-- Derivatives with respect to the actual scaled heat parameter. -/
noncomputable def heatJet (h : ℝ) (n : ℕ) (ν v : ℝ) : ℝ :=
  (2 / v) ^ n * RadialHeatProfile.profileJet (1 + h) n (2 * ν / v)

noncomputable def heatJetBound (h : ℝ) (n : ℕ) : ℝ :=
  2 ^ n * ParametricHeatTail.heatJetBound h n

noncomputable def pressureWeight (h v : ℝ) : ℝ :=
  v ^ (-2 * amplitudeExponent h - 1)

noncomputable def heatPressureJet (h : ℝ) (n : ℕ) (ν v : ℝ) : ℝ :=
  pressureWeight h v * ParametricHeatTail.jetProduct (fun i => heatJet h i ν v)
    (fun i => heatJet h i ν v) n

/-- Dimensionless pure-heat pressure integral, including the zero-diffusion endpoint. -/
noncomputable def heatPressureFactor (h ν : ℝ) : ℝ :=
  ∫ v in Ioi (1 : ℝ), pressureWeight h v * RadialHeatProfile.profile (1 + h) (2 * ν / v) ^ 2

theorem heatJet_zero (h ν v : ℝ) : heatJet h 0 ν v = RadialHeatProfile.profile (1 + h) (2 * ν / v)
  := by
  simp [heatJet, RadialHeatProfile.profileJet, RadialHeatProfile.derivativeCoeff,
    RadialHeatProfile.profile]

theorem heatJet_hasDerivWithinAt {h ν v : ℝ} (hh : 0 < h)
    (hv : 0 < v) (hν : 0 ≤ ν) (n : ℕ) :
    HasDerivWithinAt (fun u => heatJet h n u v)
      (heatJet h (n + 1) ν v) (Ici 0) ν := by
  have hi : HasDerivWithinAt (fun u : ℝ => 2 * u / v) (2 / v) (Ici 0) ν := by
    simpa using (((hasDerivAt_id ν).const_mul 2).div_const v).hasDerivWithinAt (s := Ici 0)
  have hmap : MapsTo (fun u : ℝ => 2 * u / v) (Ici 0) (Ici 0) := by
    intro u hu
    exact div_nonneg (mul_nonneg (by norm_num) hu) hv.le
  have hd := ((RadialHeatProfile.profileJet_hasDerivWithinAt (a := 1 + h)
    (by linarith) n (by positivity)).comp ν hi hmap).const_mul ((2 / v) ^ n)
  convert! hd using 1
  simp only [heatJet, pow_succ]
  ring

theorem heatJet_continuousOn {h ν : ℝ} (hh : 0 < h) (hν : 0 ≤ ν) (n : ℕ) :
    ContinuousOn (heatJet h n ν) (Ioi 0) := by
  have hi : ContinuousOn (fun v : ℝ => 2 * ν / v) (Ioi 0) :=
    continuousOn_const.div continuousOn_id (fun v hv => (show 0 < v from hv).ne')
  have hj : ContinuousOn (RadialHeatProfile.profileJet (1 + h) n) (Ici 0) :=
    continuousOn_const.mul (RadialHeatProfile.moment_continuousOn (by linarith) n)
  have hk : ContinuousOn (fun v : ℝ => (2 : ℝ) / v) (Ioi 0) :=
    continuousOn_const.div continuousOn_id (fun v hv => (show 0 < v from hv).ne')
  exact (hk.pow n).mul
      (hj.comp hi (fun v hv => div_nonneg (mul_nonneg (by norm_num) hν) hv.le))

theorem heatJetBound_nonneg {h : ℝ} (hh : 0 < h) (n : ℕ) : 0 ≤ heatJetBound h n :=
  mul_nonneg (by positivity) (ParametricHeatTail.heatJetBound_nonneg hh n)

theorem heatJet_bound {h ν v : ℝ} (hh : 0 < h) (hν : 0 ≤ ν) (hv : 1 ≤ v) (n : ℕ) :
    |heatJet h n ν v| ≤ heatJetBound h n := by
  have hvp : 0 < v := zero_lt_one.trans_le hv
  have hj : |RadialHeatProfile.profileJet (1 + h) n (2 * ν / v)| ≤ ParametricHeatTail.heatJetBound
    h n := by
    rw [← RadialHeatProfile.iteratedDerivWithin_profile (by linarith) n (by positivity)]
    exact RadialHeatProfile.profile_derivative_bound (by linarith) n (by positivity)
  have hp : (2 / v) ^ n ≤ (2 : ℝ) ^ n := by
    gcongr
    exact div_le_self (by norm_num) hv
  rw [heatJet, abs_mul, abs_of_nonneg (pow_nonneg (by positivity) n)]
  exact mul_le_mul hp hj (abs_nonneg _) (by positivity)

theorem pressureWeight_continuousOn (h : ℝ) : ContinuousOn (pressureWeight h) (Ioi 0) := by
  intro v hv
  exact (((contDiffAt_id (n := ∞)).rpow_const_of_ne (show v ≠ 0 from ne_of_gt
    hv)).continuousAt).continuousWithinAt

theorem heatPressureJet_continuousOn {h ν : ℝ} (hh : 0 < h) (hν : 0 ≤ ν) (n : ℕ) :
    ContinuousOn (heatPressureJet h n ν) (Ioi 0) :=
  (pressureWeight_continuousOn h).mul
    (ParametricHeatTail.jetProduct_continuousOn (fun i => heatJet_continuousOn hh hν i)
      (fun i => heatJet_continuousOn hh hν i) n)

theorem heatPressureJet_hasDerivWithinAt {h ν v : ℝ} (hh : 0 < h)
    (hv : 0 < v) (hν : 0 ≤ ν) (n : ℕ) :
    HasDerivWithinAt (fun u => heatPressureJet h n u v)
      (heatPressureJet h (n + 1) ν v) (Ici 0) ν :=
  (ParametricHeatTail.jetProduct_hasDerivWithinAt (fun i => heatJet_hasDerivWithinAt hh hv hν i)
    (fun i => heatJet_hasDerivWithinAt hh hv hν i) n).const_mul (pressureWeight h v)

theorem heatPressureJet_dominated {h : ℝ} (hh : 0 < h) :
    ParametricHeatTail.ChainDominated (heatPressureJet h) (volume.restrict (Ioi (1 : ℝ))) := by
  intro n L hL
  let B := ParametricHeatTail.jetProduct (heatJetBound h) (heatJetBound h) n
  refine ⟨fun v => pressureWeight h v * B, ?_, ?_⟩
  · exact (integrableOn_Ioi_rpow_of_lt
      (by dsimp [amplitudeExponent]; linarith : -2 * amplitudeExponent h - 1 < -1)
      zero_lt_one).mul_const B
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    intro ν hν
    have hBp : 0 ≤ B := ParametricHeatTail.jetProduct_nonneg (heatJetBound_nonneg hh)
      (heatJetBound_nonneg hh) n
    have hb : |ParametricHeatTail.jetProduct (fun i => heatJet h i ν v) (fun i => heatJet h i ν v)
      n| ≤ B := by
      simpa only [div_one] using ParametricHeatTail.jetProduct_bound (X := 1) le_rfl
        (heatJetBound_nonneg hh) (heatJetBound_nonneg hh)
        (fun i => by simpa only [div_one] using heatJet_bound hh hν.1 hv.le i)
        (fun i => by simpa only [div_one] using heatJet_bound hh hν.1 hv.le i) n
    rw [Real.norm_eq_abs, heatPressureJet, abs_mul, pressureWeight,
      abs_of_nonneg (Real.rpow_nonneg (zero_lt_one.trans hv).le _)]
    exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (zero_lt_one.trans hv).le _)

theorem heatPressureJet_measurable {h : ℝ} (hh : 0 < h) (n : ℕ) {ν : ℝ} (hν : 0 ≤ ν) :
    AEStronglyMeasurable (heatPressureJet h n ν) (volume.restrict (Ioi (1 : ℝ))) :=
  ((heatPressureJet_continuousOn hh hν n).mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
    measurableSet_Ioi

theorem heatPressureJet_zero (h ν v : ℝ) :
    heatPressureJet h 0 ν v = pressureWeight h v * RadialHeatProfile.profile (1 + h) (2 * ν / v) ^
      2 := by
  simp only [heatPressureJet, ParametricHeatTail.jetProduct, heatJet_zero, pow_two]

/-- Every derivative of the heat-only improper integral is dominated by an
integrable power, uniformly all the way to zero diffusion. -/
theorem heatPressureFactor_contDiffOn {h : ℝ} (hh : 0 < h) :
    ContDiffOn ℝ ∞ (heatPressureFactor h) (Ici 0) := by
  have hj : ∀ᵐ v ∂volume.restrict (Ioi (1 : ℝ)), ∀ n ν, 0 ≤ ν →
      HasDerivWithinAt (fun u => heatPressureJet h n u v)
        (heatPressureJet h (n + 1) ν v) (Ici 0) ν := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact fun n ν hν => heatPressureJet_hasDerivWithinAt hh (zero_lt_one.trans hv) hν n
  have h := ParametricHeatTail.contDiffOn_integral_chain hj
    (fun n ν hν => heatPressureJet_measurable hh n hν) (heatPressureJet_dominated hh)
  simp only [heatPressureJet_zero] at h ⊢
  exact h

/-! ## The compact taper correction -/

noncomputable def heatDensity (h ν v : ℝ) : ℝ :=
  pressureWeight h v * RadialHeatProfile.profile (1 + h) (2 * ν / v) ^ 2

noncomputable def taperedDensity (h : ℝ) (f : ℝ → ℝ) (p : ℝ × ℝ) (v : ℝ) : ℝ :=
  heatDensity h p.1 v * f (p.2 + Real.log v) ^ 2

noncomputable def deficitDensity (h : ℝ) (f : ℝ → ℝ) (p : ℝ × ℝ) (v : ℝ) : ℝ :=
  heatDensity h p.1 v * (1 - f (p.2 + Real.log v) ^ 2)

noncomputable def taperedPressureFactor (h : ℝ) (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ v in Ioi (1 : ℝ), taperedDensity h f p v

noncomputable def compactDeficit (h : ℝ) (f : ℝ → ℝ) (B : ℝ) (p : ℝ × ℝ) : ℝ :=
  (B - 1) * ∫ u in (0 : ℝ)..1, deficitDensity h f p (1 + (B - 1) * u)

theorem heatDensity_continuousOn {h ν : ℝ} (hh : 0 < h) (hν : 0 ≤ ν) :
    ContinuousOn (heatDensity h ν) (Ioi 0) := by
  have he : heatDensity h ν = heatPressureJet h 0 ν :=
    funext fun v => (heatPressureJet_zero h ν v).symm
  rw [he]
  exact heatPressureJet_continuousOn hh hν 0

theorem heatDensity_bounds {h ν v : ℝ} (hh : 0 < h) (hν : 0 ≤ ν) (hv : 0 < v) :
    0 ≤ heatDensity h ν v ∧ heatDensity h ν v ≤ pressureWeight h v := by
  have hw : 0 ≤ pressureWeight h v := Real.rpow_nonneg hv.le _
  have hH := RadialHeatProfile.profile_pos (a := 1 + h) (by linarith)
    (show 0 ≤ 2 * ν / v by positivity)
  have hH1 := RadialHeatProfile.profile_le_one (a := 1 + h) (by linarith)
    (show 0 ≤ 2 * ν / v by positivity)
  exact ⟨mul_nonneg hw (sq_nonneg _),
    (mul_le_mul_of_nonneg_left (show RadialHeatProfile.profile (1 + h) (2 * ν / v) ^ 2 ≤ 1 by
      nlinarith) hw).trans_eq (mul_one _)⟩

theorem heatDensity_integrable {h ν : ℝ} (hh : 0 < h) (hν : 0 ≤ ν) :
    IntegrableOn (heatDensity h ν) (Ioi (1 : ℝ)) := by
  apply (integrableOn_Ioi_rpow_of_lt
    (by dsimp [amplitudeExponent]; linarith : -2 * amplitudeExponent h - 1 < -1)
    zero_lt_one).mono'
  · exact ((heatDensity_continuousOn hh hν).mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [Real.norm_eq_abs, abs_of_nonneg (heatDensity_bounds hh hν (zero_lt_one.trans hv)).1]
    exact (heatDensity_bounds hh hν (zero_lt_one.trans hv)).2

theorem taperedDensity_continuousOn {h ν y : ℝ} {f : ℝ → ℝ} (hh : 0 < h)
    (hν : 0 ≤ ν) (hf : Continuous f) :
    ContinuousOn (taperedDensity h f (ν, y)) (Ioi 0) := by
  apply (heatDensity_continuousOn hh hν).mul
  exact (hf.comp_continuousOn (continuousOn_const.add
    (Real.continuousOn_log.mono (fun v hv => ne_of_gt hv)))).pow 2

theorem taperedDensity_integrable {h ν y : ℝ} {f : ℝ → ℝ} (hh : 0 < h)
    (hν : 0 ≤ ν) (hf : Continuous f) (hb : ∀ y, 0 ≤ f y ∧ f y ≤ 1) :
    IntegrableOn (taperedDensity h f (ν, y)) (Ioi (1 : ℝ)) := by
  apply (heatDensity_integrable hh hν).mono'
  · exact ((taperedDensity_continuousOn hh hν hf).mono
      (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hd := (heatDensity_bounds hh hν (zero_lt_one.trans hv)).1
    have hsq : f (y + Real.log v) ^ 2 ≤ 1 := by
      nlinarith [(hb (y + Real.log v)).1, (hb (y + Real.log v)).2]
    rw [Real.norm_eq_abs, taperedDensity, abs_of_nonneg (mul_nonneg hd (sq_nonneg _))]
    exact (mul_le_mul_of_nonneg_left hsq hd).trans_eq (mul_one _)

theorem deficitDensity_integrable {h ν y : ℝ} {f : ℝ → ℝ} (hh : 0 < h)
    (hν : 0 ≤ ν) (hf : Continuous f) (hb : ∀ y, 0 ≤ f y ∧ f y ≤ 1) :
    IntegrableOn (deficitDensity h f (ν, y)) (Ioi (1 : ℝ)) := by
  have he : deficitDensity h f (ν, y) = heatDensity h ν - taperedDensity h f (ν, y) := by
    funext v
    simp only [deficitDensity, taperedDensity, Pi.sub_apply]
    ring
  rw [he]
  exact (heatDensity_integrable hh hν).sub (taperedDensity_integrable hh hν hf hb)

theorem compactDeficit_eq_interval (h B : ℝ) (f : ℝ → ℝ) (p : ℝ × ℝ) :
    compactDeficit h f B p = ∫ v in (1 : ℝ)..B, deficitDensity h f p v := by
  simp [compactDeficit, add_comm]

theorem integral_tail_eq_interval {g : ℝ → ℝ} {a B : ℝ} (hB : a ≤ B)
    (hg : ∀ v, B < v → g v = 0) : (∫ v in Ioi a, g v) = ∫ v in a..B, g v := by
  rw [intervalIntegral.integral_of_le hB, ← Ioc_union_Ioi_eq_Ioi hB]
  exact integral_union_eq_left_of_forall measurableSet_Ioi hg

theorem deficitDensity_zero {h B Y : ℝ} {f : ℝ → ℝ} {p : ℝ × ℝ}
    (hB : 0 < B) (hy : Y ≤ p.2 + Real.log B) (hplateau : ∀ y, Y ≤ y → f y = 1)
    {v : ℝ} (hv : B < v) : deficitDensity h f p v = 0 := by
  have hyv : Y ≤ p.2 + Real.log v := hy.trans
    (add_le_add_right (Real.log_le_log hB hv.le) _)
  simp [deficitDensity, hplateau _ hyv]

theorem taperedPressureFactor_eq {h B Y : ℝ} {f : ℝ → ℝ} {p : ℝ × ℝ}
    (hh : 0 < h) (hν : 0 ≤ p.1) (hf : Continuous f)
    (hb : ∀ y, 0 ≤ f y ∧ f y ≤ 1) (hB : 1 ≤ B)
    (hy : Y ≤ p.2 + Real.log B) (hplateau : ∀ y, Y ≤ y → f y = 1) :
    taperedPressureFactor h f p = heatPressureFactor h p.1 - compactDeficit h f B p := by
  have hd := deficitDensity_integrable hh hν hf hb (y := p.2)
  have he : taperedDensity h f p = heatDensity h p.1 - deficitDensity h f p := by
    funext v
    simp only [taperedDensity, deficitDensity, Pi.sub_apply]
    ring
  rw [taperedPressureFactor, he]
  simp only [Pi.sub_apply]
  rw [integral_sub (heatDensity_integrable hh hν) hd,
    integral_tail_eq_interval hB
      (fun v hv => deficitDensity_zero (zero_lt_one.trans_le hB) hy hplateau hv),
    ← compactDeficit_eq_interval]
  rfl

theorem deficitDensity_contDiffAt {h : ℝ} {f : ℝ → ℝ} {p : ℝ × ℝ} {v : ℝ}
    (hh : 0 < h) (hf : ContDiff ℝ ∞ f) (hν : 0 < p.1) (hv : 0 < v) :
    ContDiffAt ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => deficitDensity h f z.1 z.2) (p, v) := by
  have ha : ContDiffAt ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => 2 * z.1.1 / z.2) (p, v) :=
    (contDiffAt_const.mul contDiffAt_fst.fst).div contDiffAt_snd hv.ne'
  have hH : ContDiffAt ℝ ∞ (RadialHeatProfile.profile (1 + h)) (2 * p.1 / v) :=
    (RadialHeatProfile.profile_contDiffOn (by linarith)).contDiffAt
      (Ici_mem_nhds (by positivity : 0 < 2 * p.1 / v))
  have hw : ContDiffAt ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => pressureWeight h z.2) (p, v) :=
    contDiffAt_snd.rpow_const_of_ne hv.ne'
  have hy : ContDiffAt ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => z.1.2 + Real.log z.2) (p, v) :=
    contDiffAt_fst.snd.add (contDiffAt_snd.log hv.ne')
  exact (hw.mul ((hH.comp (p, v) ha).pow 2)).mul
    (contDiffAt_const.sub ((hf.contDiffAt.comp (p, v) hy).pow 2))

theorem compactDeficit_integrand_smooth {h B : ℝ} {f : ℝ → ℝ}
    (hh : 0 < h) (hf : ContDiff ℝ ∞ f) (hB : 1 ≤ B)
    (p : ℝ × ℝ) (hν : 0 < p.1) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    ContDiffAt ℝ ∞
      (fun z : (ℝ × ℝ) × ℝ => deficitDensity h f z.1 (1 + (B - 1) * z.2)) (p, u) := by
  have hv : 0 < 1 + (B - 1) * u := by nlinarith [mul_nonneg (sub_nonneg.mpr hB) hu.1]
  exact (deficitDensity_contDiffAt hh hf hν hv).comp (p, u)
    (contDiffAt_fst.prodMk (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_snd)))

theorem compactDeficit_contDiffOn {h B : ℝ} {f : ℝ → ℝ}
    (hh : 0 < h) (hf : ContDiff ℝ ∞ f) (hB : 1 ≤ B) :
    ContDiffOn ℝ ∞ (compactDeficit h f B) {p : ℝ × ℝ | 0 < p.1} := by
  apply contDiffOn_const.mul
  apply ProfileHistories.compact_parameter_integral_smooth (isOpen_lt continuous_const
    continuous_fst)
  exact fun p hp u hu => compactDeficit_integrand_smooth hh hf hB p hp u hu

/-- Genuine joint smoothness of the tapered improper integral. Only the compact
taper correction depends on the logarithmic radial coordinate. -/
theorem taperedPressureFactor_contDiffAt {h Y : ℝ} {f : ℝ → ℝ} {p : ℝ × ℝ}
    (hh : 0 < h) (hf : ContDiff ℝ ∞ f) (hb : ∀ y, 0 ≤ f y ∧ f y ≤ 1)
    (hplateau : ∀ y, Y ≤ y → f y = 1) (hν : 0 < p.1) :
    ContDiffAt ℝ ∞ (taperedPressureFactor h f) p := by
  let B := Real.exp (max 1 (Y - p.2 + 1))
  have hB : 1 ≤ B := Real.one_le_exp (le_max_left _ _ |>.trans' zero_le_one)
  have hlog : Real.log B = max 1 (Y - p.2 + 1) := Real.log_exp _
  have hy : Y < p.2 + Real.log B := by rw [hlog]; linarith [le_max_right 1 (Y - p.2 + 1)]
  have hnear : ∀ᶠ q : ℝ × ℝ in 𝓝 p, 0 < q.1 ∧ Y < q.2 + Real.log B :=
    (continuousAt_fst.eventually (Ioi_mem_nhds hν)).and
      ((continuousAt_snd.add_const _).eventually (Ioi_mem_nhds hy))
  have he : taperedPressureFactor h f =ᶠ[𝓝 p]
      (fun q : ℝ × ℝ => heatPressureFactor h q.1 - compactDeficit h f B q) := by
    filter_upwards [hnear] with q hq
    exact taperedPressureFactor_eq hh hq.1.le hf.continuous hb hB hq.2.le hplateau
  have hheat : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => heatPressureFactor h q.1) p :=
    ((heatPressureFactor_contDiffOn hh).contDiffAt (Ici_mem_nhds hν)).comp p contDiffAt_fst
  have hdef : ContDiffAt ℝ ∞ (compactDeficit h f B) p :=
    (compactDeficit_contDiffOn hh hf hB).contDiffAt
      ((isOpen_lt continuous_const continuous_fst).mem_nhds hν)
  exact (hheat.sub hdef).congr_of_eventuallyEq he

/-! ## Actual differentiation in the logarithmic radial parameter -/

noncomputable def taperDerivativeDensity (h : ℝ) (f : ℝ → ℝ) (p : ℝ × ℝ) (v : ℝ) : ℝ :=
  heatDensity h p.1 v * f (p.2 + Real.log v) * deriv f (p.2 + Real.log v)

noncomputable def taperDerivativeIntegral (h : ℝ) (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ v in Ioi (1 : ℝ), taperDerivativeDensity h f p v

theorem parameterPartial_hasDerivAt {G : (ℝ × ℝ) → ℝ} {p : ℝ × ℝ}
    (hG : DifferentiableAt ℝ G p) :
    HasDerivAt (fun y => G (p.1, y)) (ProfileHistories.parameterPartial G p) p.2 := by
  simpa only [ProfileHistories.parameterPartial, Function.comp_def, id_eq, Prod.eta] using
    hG.hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))

theorem deficitDensity_hasDerivAt_y (h ν v y : ℝ) {f : ℝ → ℝ}
    (hf : DifferentiableAt ℝ f (y + Real.log v)) :
    HasDerivAt (fun u => deficitDensity h f (ν, u) v)
      (-2 * taperDerivativeDensity h f (ν, y) v) y := by
  have hd := (((hf.hasDerivAt.comp y ((hasDerivAt_id y).add_const (Real.log v))).pow 2).const_sub
    1).const_mul
    (heatDensity h ν v)
  convert! hd using 1
  simp only [taperDerivativeDensity, Function.comp_apply, id_eq, mul_one, pow_one,
    Nat.cast_ofNat, Nat.reduceSub]
  ring

theorem deriv_zero_after_plateau {f : ℝ → ℝ} {Y y : ℝ}
    (hplateau : ∀ x, Y ≤ x → f x = 1) (hy : Y < y) : deriv f y = 0 := by
  have he : f =ᶠ[𝓝 y] (fun _ => (1 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hy] with x hx
    exact hplateau x (show Y < x from hx).le
  simpa only [deriv_const] using he.deriv_eq

theorem taperDerivativeDensity_zero {h B Y : ℝ} {f : ℝ → ℝ} {p : ℝ × ℝ}
    (hB : 0 < B) (hy : Y ≤ p.2 + Real.log B) (hplateau : ∀ y, Y ≤ y → f y = 1)
    {v : ℝ} (hv : B < v) : taperDerivativeDensity h f p v = 0 := by
  have hyv : Y < p.2 + Real.log v := hy.trans_lt
    (add_lt_add_right (Real.log_lt_log hB hv) _)
  simp only [taperDerivativeDensity, deriv_zero_after_plateau hplateau hyv, mul_zero]

theorem compactDeficit_hasDerivAt_y {h B : ℝ} {f : ℝ → ℝ} {p : ℝ × ℝ}
    (hh : 0 < h) (hf : ContDiff ℝ ∞ f) (hB : 1 ≤ B) (hν : 0 < p.1) :
    HasDerivAt (fun y => compactDeficit h f B (p.1, y))
      (-2 * (B - 1) * ∫ u in (0 : ℝ)..1,
        taperDerivativeDensity h f p (1 + (B - 1) * u)) p.2 := by
  let G : (ℝ × ℝ) → ℝ → ℝ := fun p u => deficitDensity h f p (1 + (B - 1) * u)
  have hs : IsOpen {p : ℝ × ℝ | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hG : ∀ q ∈ {p : ℝ × ℝ | 0 < p.1}, ∀ u ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => G z.1 z.2) (q, u) :=
    fun q hq u hu => compactDeficit_integrand_smooth hh hf hB q hq u hu
  have hI := ProfileHistories.compact_parameter_integral_smooth hs hG
  have hd := (parameterPartial_hasDerivAt
    ((hI.contDiffAt (hs.mem_nhds hν)).differentiableAt (by simp))).const_mul (B - 1)
  have hpartial := ProfileHistories.compact_parameter_integral_parameterPartial hs hG hν
  have he : (∫ u in (0 : ℝ)..1, ProfileHistories.parameterPartial (fun q => G q u) p) =
      -2 * ∫ u in (0 : ℝ)..1, taperDerivativeDensity h f p (1 + (B - 1) * u) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le zero_le_one] at hu
    have hdiff : DifferentiableAt ℝ (fun q => G q u) p :=
      ((hG p hν u hu).comp p (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    exact (parameterPartial_hasDerivAt hdiff).unique
      (deficitDensity_hasDerivAt_y h p.1 (1 + (B - 1) * u) p.2
        (hf.differentiable (by simp) _))
  rw [hpartial, he] at hd
  convert! hd using 1
  ring

/-- The derivative is obtained from the defining improper integral; the
derivative integrand is compactly supported by the actual taper plateau. -/
theorem taperedPressureFactor_hasDerivAt_y {h Y : ℝ} {f : ℝ → ℝ} {p : ℝ × ℝ}
    (hh : 0 < h) (hf : ContDiff ℝ ∞ f) (hb : ∀ y, 0 ≤ f y ∧ f y ≤ 1)
    (hplateau : ∀ y, Y ≤ y → f y = 1) (hν : 0 < p.1) :
    HasDerivAt (fun y => taperedPressureFactor h f (p.1, y))
      (2 * taperDerivativeIntegral h f p) p.2 := by
  let B := Real.exp (max 1 (Y - p.2 + 1))
  have hB : 1 ≤ B := Real.one_le_exp (le_max_left _ _ |>.trans' zero_le_one)
  have hlog : Real.log B = max 1 (Y - p.2 + 1) := Real.log_exp _
  have hy : Y < p.2 + Real.log B := by rw [hlog]; linarith [le_max_right 1 (Y - p.2 + 1)]
  have he : (fun y => taperedPressureFactor h f (p.1, y)) =ᶠ[𝓝 p.2]
      (fun y => heatPressureFactor h p.1 - compactDeficit h f B (p.1, y)) := by
    filter_upwards [(continuousAt_id.add_const (Real.log B)).eventually (Ioi_mem_nhds hy)] with y
      hy'
    exact taperedPressureFactor_eq hh hν.le hf.continuous hb hB (show Y < y + Real.log B from
      hy').le hplateau
  have hi : taperDerivativeIntegral h f p =
      (B - 1) * ∫ u in (0 : ℝ)..1, taperDerivativeDensity h f p (1 + (B - 1) * u) := by
    rw [taperDerivativeIntegral, integral_tail_eq_interval hB
      (fun v hv => taperDerivativeDensity_zero (zero_lt_one.trans_le hB) hy.le hplateau hv)]
    simp [add_comm]
  have hd := (compactDeficit_hasDerivAt_y hh hf hB hν).const_sub (heatPressureFactor h p.1)
  rw [hi]
  convert! hd.congr_of_eventuallyEq he using 1
  ring

/-! ## Identification with the physical canonical pressure -/

noncomputable def pressureCoordinates (h : ℝ) (p : SimilarityProfile.PhysicalPoint) : ℝ × ℝ :=
  ((1 - p.1) / p.2.1, Real.log (SimilarityProfile.X h p))

theorem swirlCoefficient_sq (C h : ℝ) (f : ℝ → ℝ) {p : SimilarityProfile.PhysicalPoint}
    (hs : 0 < p.2.1) :
    TerminalStress.swirlCoefficient C h f p ^ 2 =
      (C ^ 2 / 2) * p.2.1 ^ (-2 * amplitudeExponent h - 1) *
        RadialHeatProfile.profile (1 + h) (2 * (1 - p.1) / p.2.1) ^ 2 *
        f (Real.log (SimilarityProfile.X h p)) ^ 2 := by
  have hexp : RadialHeatProfile.spatialExponent (1 + h) = -amplitudeExponent h := by
    unfold RadialHeatProfile.spatialExponent amplitudeExponent
    ring
  have hp : (p.2.1 ^ (-amplitudeExponent h)) ^ (2 : ℕ) = p.2.1 ^ (-2 * amplitudeExponent h) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    congr 1
    ring
  have hpow : p.2.1 ^ (-2 * amplitudeExponent h - 1) =
      p.2.1 ^ (-2 * amplitudeExponent h) / p.2.1 := by
    rw [Real.rpow_sub hs, Real.rpow_one]
  unfold TerminalStress.swirlCoefficient TerminalStress.physicalHeat
    RadialHeatProfile.spatialProfile
    TerminalStress.flattening
  rw [hexp, div_pow, mul_pow, mul_pow, mul_pow, hp,
    Real.sq_sqrt (by positivity : 0 ≤ 2 * p.2.1), hpow]
  field_simp [hs.ne']

theorem swirlCoefficient_sq_scaled (C : ℝ) {h : ℝ} (f : ℝ → ℝ)
    {p : SimilarityProfile.PhysicalPoint} (hq : 0 < SimilarityProfile.q h p)
    (hs : 0 < p.2.1) {v : ℝ} (hv : 0 < v) :
    TerminalStress.swirlCoefficient C h f (p.1, (p.2.1 * v, p.2.2)) ^ 2 =
      (C ^ 2 / 2 * p.2.1 ^ (-2 * amplitudeExponent h - 1)) *
        taperedDensity h f (pressureCoordinates h p) v := by
  rw [swirlCoefficient_sq C h f (mul_pos hs hv), Real.mul_rpow hs.le hv.le]
  have harg : 2 * (1 - p.1) / (p.2.1 * v) = 2 * ((1 - p.1) / p.2.1) / v := by ring
  have hlog : Real.log (SimilarityProfile.X h (p.1, (p.2.1 * v, p.2.2))) =
      Real.log (SimilarityProfile.X h p) + Real.log v := by
    change Real.log (p.2.1 * v / SimilarityProfile.q h p) =
      Real.log (p.2.1 / SimilarityProfile.q h p) + Real.log v
    rw [show p.2.1 * v / SimilarityProfile.q h p = (p.2.1 / SimilarityProfile.q h p) * v by ring,
      Real.log_mul (div_pos hs hq).ne' hv.ne']
  rw [harg, hlog]
  unfold taperedDensity heatDensity pressureWeight pressureCoordinates
  ring

theorem swirlCoefficient_sq_integrable (C : ℝ) {h : ℝ} {f : ℝ → ℝ}
    {p : SimilarityProfile.PhysicalPoint} (hh : 0 < h) (hh1 : h < 1 / 2)
    (ht : p.1 < 1) (hs : 0 < p.2.1) (hf : Continuous f)
    (hb : ∀ y, 0 ≤ f y ∧ f y ≤ 1) :
    IntegrableOn (fun s => TerminalStress.swirlCoefficient C h f (p.1, (s, p.2.2)) ^ 2)
      (Ioi p.2.1) := by
  have hν : 0 ≤ (pressureCoordinates h p).1 := (div_pos (sub_pos.mpr ht) hs).le
  have hi := (taperedDensity_integrable hh hν hf hb (y := (pressureCoordinates h p).2)).const_mul
    (C ^ 2 / 2 * p.2.1 ^ (-2 * amplitudeExponent h - 1))
  have hscl : IntegrableOn
      (fun v => TerminalStress.swirlCoefficient C h f (p.1, (p.2.1 * v, p.2.2)) ^ 2)
      (Ioi (1 : ℝ)) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact (swirlCoefficient_sq_scaled C f (SimilarityProfile.q_pos hh hh1 ht) hs
      (zero_lt_one.trans hv)).symm
  simpa only [mul_one] using (integrableOn_Ioi_comp_mul_left_iff
    (fun s => TerminalStress.swirlCoefficient C h f (p.1, (s, p.2.2)) ^ 2) 1 hs).mp hscl

/-- Scaling is performed in the physical radial integral. In particular the
argument of the heat profile is `2(1-t)/s`, rather than a fixed diffusion parameter. -/
theorem canonicalPressure_eq (C : ℝ) {h : ℝ} (f : ℝ → ℝ)
    {p : SimilarityProfile.PhysicalPoint} (hq : 0 < SimilarityProfile.q h p) (hs : 0 < p.2.1) :
    TerminalStress.canonicalPressure (TerminalStress.swirlCoefficient C h f) p =
      -(C ^ 2 / 2) * p.2.1 ^ (-2 * amplitudeExponent h) *
        taperedPressureFactor h f (pressureCoordinates h p) := by
  have hscl := integral_comp_mul_left_Ioi
    (fun s => TerminalStress.swirlCoefficient C h f (p.1, (s, p.2.2)) ^ 2) 1 hs
  have he : (∫ s in Ioi p.2.1,
      TerminalStress.swirlCoefficient C h f (p.1, (s, p.2.2)) ^ 2) =
      p.2.1 * (∫ v in Ioi (1 : ℝ),
        TerminalStress.swirlCoefficient C h f (p.1, (p.2.1 * v, p.2.2)) ^ 2) := by
    rw [hscl]
    simp only [mul_one, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  have hd : (∫ v in Ioi (1 : ℝ),
      TerminalStress.swirlCoefficient C h f (p.1, (p.2.1 * v, p.2.2)) ^ 2) =
      (C ^ 2 / 2 * p.2.1 ^ (-2 * amplitudeExponent h - 1)) *
        taperedPressureFactor h f (pressureCoordinates h p) := by
    rw [taperedPressureFactor, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact swirlCoefficient_sq_scaled C f hq hs (zero_lt_one.trans hv)
  rw [TerminalStress.canonicalPressure, he, hd, Real.rpow_sub hs, Real.rpow_one]
  field_simp

theorem pressureCoordinates_contDiffAt {h : ℝ} {p : SimilarityProfile.PhysicalPoint}
    (hh : 0 < h) (hh1 : h < 1 / 2) (ht : p.1 < 1) (hs : 0 < p.2.1) :
    ContDiffAt ℝ ∞ (pressureCoordinates h) p :=
  ((contDiffAt_const.sub contDiffAt_fst).div contDiffAt_snd.fst hs.ne').prodMk
    (((SimilarityProfile.inner_smoothAt hh hh1 ht).fst).log
      (div_pos hs (SimilarityProfile.q_pos hh hh1 ht)).ne')

/-- The actual canonical pressure is jointly smooth throughout the presingular,
positive-radius domain. No differentiability of the pressure is an input. -/
theorem canonicalPressure_contDiffAt (C : ℝ) {h Y : ℝ} {f : ℝ → ℝ}
    {p : SimilarityProfile.PhysicalPoint} (hh : 0 < h) (hh1 : h < 1 / 2)
    (ht : p.1 < 1) (hs : 0 < p.2.1) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ y, 0 ≤ f y ∧ f y ≤ 1) (hplateau : ∀ y, Y ≤ y → f y = 1) :
    ContDiffAt ℝ ∞ (TerminalStress.canonicalPressure (TerminalStress.swirlCoefficient C h f)) p :=
      by
  have harg : 0 < (pressureCoordinates h p).1 := div_pos (sub_pos.mpr ht) hs
  have hfac := (taperedPressureFactor_contDiffAt hh hf hb hplateau harg).comp p
    (pressureCoordinates_contDiffAt hh hh1 ht hs)
  have hm : ContDiffAt ℝ ∞ (fun p : SimilarityProfile.PhysicalPoint =>
      -(C ^ 2 / 2) * p.2.1 ^ (-2 * amplitudeExponent h)) p :=
    contDiffAt_const.mul (contDiffAt_snd.fst.rpow_const_of_ne hs.ne')
  have he : TerminalStress.canonicalPressure (TerminalStress.swirlCoefficient C h f) =ᶠ[𝓝 p]
      (fun p => -(C ^ 2 / 2) * p.2.1 ^ (-2 * amplitudeExponent h) *
        taperedPressureFactor h f (pressureCoordinates h p)) := by
    filter_upwards [continuousAt_fst.eventually (Iio_mem_nhds ht),
      continuousAt_snd.fst.eventually (Ioi_mem_nhds hs)] with q hqt hqs
    exact canonicalPressure_eq C f (SimilarityProfile.q_pos hh hh1 hqt) hqs
  exact (hm.mul hfac).congr_of_eventuallyEq he

/-! ## The axial derivative of the physical pressure -/

noncomputable def logScaleDerivative (h : ℝ) (p : SimilarityProfile.PhysicalPoint) : ℝ :=
  CoordinateAlgebra.qAxial (SimilarityProfile.q h p) h (SimilarityProfile.eta h p) /
    SimilarityProfile.q h p

theorem logX_hasDerivAt_z {h : ℝ} {p : SimilarityProfile.PhysicalPoint}
    (hh : 0 < h) (hh1 : h < 1 / 2) (ht : p.1 < 1) (hs : 0 < p.2.1) :
    HasDerivAt (fun z => Real.log (SimilarityProfile.X h (p.1, (p.2.1, z))))
      (-logScaleDerivative h p) p.2.2 := by
  have hq := SimilarityProfile.q_pos hh hh1 ht
  have hX : 0 < SimilarityProfile.X h p := div_pos hs hq
  have hd := (((hasDerivAt_const p.2.2 p.2.1).fun_div
    (SimilarityProfile.q_hasDerivAt_z hh hh1 ht) hq.ne').log hX.ne')
  change HasDerivAt (fun z => Real.log (p.2.1 / SimilarityProfile.q h (p.1, (p.2.1, z))))
    (-logScaleDerivative h p) p.2.2
  apply hd.congr_deriv
  unfold logScaleDerivative
  field_simp [hq.ne', hs.ne'] ; ring

theorem physicalHeat_sq_div (C h : ℝ) {p : SimilarityProfile.PhysicalPoint} (hs : 0 < p.2.1) :
    TerminalStress.physicalHeat C (1 + h) p ^ 2 / p.2.1 =
      C ^ 2 * p.2.1 ^ (-2 * amplitudeExponent h - 1) *
        RadialHeatProfile.profile (1 + h) (2 * (1 - p.1) / p.2.1) ^ 2 := by
  have he := swirlCoefficient_sq C h (fun _ => 1) hs
  simp only [TerminalStress.swirlCoefficient, TerminalStress.flattening, mul_one,
    one_pow, div_pow, Real.sq_sqrt (show 0 ≤ 2 * p.2.1 by positivity)] at he
  have he' := congrArg (fun a : ℝ => 2 * a) he
  convert! he' using 1 <;> ring

noncomputable def axialPressureIntegral (C h : ℝ) (f : ℝ → ℝ)
    (p : SimilarityProfile.PhysicalPoint) : ℝ :=
  ∫ s in Ioi p.2.1, TerminalStress.physicalHeat C (1 + h) (p.1, (s, p.2.2)) ^ 2 *
    f (Real.log (s / SimilarityProfile.q h p)) *
    deriv f (Real.log (s / SimilarityProfile.q h p)) / s

theorem axialPressureIntegral_eq (C : ℝ) {h : ℝ} (f : ℝ → ℝ)
    {p : SimilarityProfile.PhysicalPoint} (hq : 0 < SimilarityProfile.q h p) (hs : 0 < p.2.1) :
    axialPressureIntegral C h f p = C ^ 2 * p.2.1 ^ (-2 * amplitudeExponent h) *
      taperDerivativeIntegral h f (pressureCoordinates h p) := by
  let G : ℝ → ℝ := fun s => TerminalStress.physicalHeat C (1 + h) (p.1, (s, p.2.2)) ^ 2 *
    f (Real.log (s / SimilarityProfile.q h p)) * deriv f (Real.log (s / SimilarityProfile.q h p)) /
      s
  have he : (∫ s in Ioi p.2.1, G s) = p.2.1 * ∫ v in Ioi (1 : ℝ), G (p.2.1 * v) := by
    rw [integral_comp_mul_left_Ioi G 1 hs]
    simp only [mul_one, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  have hscale {v : ℝ} (hv : 0 < v) : G (p.2.1 * v) =
      (C ^ 2 * p.2.1 ^ (-2 * amplitudeExponent h - 1)) *
        taperDerivativeDensity h f (pressureCoordinates h p) v := by
    have hlog : Real.log (p.2.1 * v / SimilarityProfile.q h p) =
        Real.log (SimilarityProfile.X h p) + Real.log v := by
      rw [show p.2.1 * v / SimilarityProfile.q h p = (p.2.1 / SimilarityProfile.q h p) * v by ring,
        Real.log_mul (div_pos hs hq).ne' hv.ne']
      rfl
    have harg : 2 * (1 - p.1) / (p.2.1 * v) = 2 * ((1 - p.1) / p.2.1) / v := by ring
    change _ = _
    dsimp only [G]
    rw [show TerminalStress.physicalHeat C (1 + h) (p.1, (p.2.1 * v, p.2.2)) ^ 2 *
        f (Real.log (p.2.1 * v / SimilarityProfile.q h p)) *
        deriv f (Real.log (p.2.1 * v / SimilarityProfile.q h p)) / (p.2.1 * v) =
      (TerminalStress.physicalHeat C (1 + h) (p.1, (p.2.1 * v, p.2.2)) ^ 2 / (p.2.1 * v)) *
        f (Real.log (p.2.1 * v / SimilarityProfile.q h p)) *
        deriv f (Real.log (p.2.1 * v / SimilarityProfile.q h p)) by ring,
      physicalHeat_sq_div C h (mul_pos hs hv), Real.mul_rpow hs.le hv.le, harg, hlog]
    unfold taperDerivativeDensity pressureCoordinates heatDensity pressureWeight
    ring
  unfold axialPressureIntegral
  change (∫ s in Ioi p.2.1, G s) = _
  rw [he]
  have hi : (∫ v in Ioi (1 : ℝ), G (p.2.1 * v)) =
      (C ^ 2 * p.2.1 ^ (-2 * amplitudeExponent h - 1)) *
        taperDerivativeIntegral h f (pressureCoordinates h p) := by
    rw [taperDerivativeIntegral, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact hscale (zero_lt_one.trans hv)
  rw [hi, Real.rpow_sub hs, Real.rpow_one]
  field_simp [hs.ne']

theorem canonicalPressure_hasDerivAt_z (C : ℝ) {h Y : ℝ} {f : ℝ → ℝ}
    {p : SimilarityProfile.PhysicalPoint} (hh : 0 < h) (hh1 : h < 1 / 2)
    (ht : p.1 < 1) (hs : 0 < p.2.1) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ y, 0 ≤ f y ∧ f y ≤ 1) (hplateau : ∀ y, Y ≤ y → f y = 1) :
    HasDerivAt (fun z => TerminalStress.canonicalPressure
      (TerminalStress.swirlCoefficient C h f) (p.1, (p.2.1, z)))
      (logScaleDerivative h p * axialPressureIntegral C h f p) p.2.2 := by
  have hd := ((taperedPressureFactor_hasDerivAt_y (p := pressureCoordinates h p) hh hf hb hplateau
    (div_pos (sub_pos.mpr ht) hs)).comp p.2.2 (logX_hasDerivAt_z hh hh1 ht hs)).const_mul
      (-(C ^ 2 / 2) * p.2.1 ^ (-2 * amplitudeExponent h))
  have he : (fun z => TerminalStress.canonicalPressure (TerminalStress.swirlCoefficient C h f)
      (p.1, (p.2.1, z))) = fun z =>
      (-(C ^ 2 / 2) * p.2.1 ^ (-2 * amplitudeExponent h)) *
        taperedPressureFactor h f ((1 - p.1) / p.2.1,
          Real.log (SimilarityProfile.X h (p.1, (p.2.1, z)))) := by
    funext z
    exact canonicalPressure_eq C f (SimilarityProfile.q_pos hh hh1 ht) hs
  rw [he, axialPressureIntegral_eq C f (SimilarityProfile.q_pos hh hh1 ht) hs]
  convert! hd using 1
  ring

/-- Exact axial derivative of the canonical pressure, including the dependence
of the heat profile on the physical time and of the taper on `q(t,z)`. -/
theorem canonicalPressure_partialZ (C : ℝ) {h Y : ℝ} {f : ℝ → ℝ}
    {p : SimilarityProfile.PhysicalPoint} (hh : 0 < h) (hh1 : h < 1 / 2)
    (ht : p.1 < 1) (hs : 0 < p.2.1) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ y, 0 ≤ f y ∧ f y ≤ 1) (hplateau : ∀ y, Y ≤ y → f y = 1) :
    SimilarityProfile.partialZ (TerminalStress.canonicalPressure
      (TerminalStress.swirlCoefficient C h f)) p =
      logScaleDerivative h p * axialPressureIntegral C h f p := by
  have hP := (canonicalPressure_contDiffAt C hh hh1 ht hs hf hb hplateau).differentiableAt (by simp)
  have hd := hP.hasFDerivAt.comp_hasDerivAt p.2.2
    ((hasDerivAt_const p.2.2 p.1).prodMk
      ((hasDerivAt_const p.2.2 p.2.1).prodMk (hasDerivAt_id p.2.2)))
  have hd' : HasDerivAt (fun z => TerminalStress.canonicalPressure
      (TerminalStress.swirlCoefficient C h f) (p.1, (p.2.1, z)))
      (SimilarityProfile.partialZ (TerminalStress.canonicalPressure
        (TerminalStress.swirlCoefficient C h f)) p) p.2.2 := by
    simpa only [Function.comp_def, id_eq, Prod.eta, SimilarityProfile.partialZ] using hd
  exact hd'.unique (canonicalPressure_hasDerivAt_z C hh hh1 ht hs hf hb hplateau)

/-! ## Quantitative pressure estimates from monotonicity of the heat carrier -/

theorem spatialHeat_antitoneOn {h ν : ℝ} (hh : 0 < h) (hν : 0 < ν) :
    AntitoneOn (RadialHeatProfile.spatialProfile (1 + h) ν) (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro v hv
    exact (RadialHeatProfile.spatialProfile_hasDerivAt_s (by linarith) hν
      hv).continuousAt.continuousWithinAt
  · intro v hv
    have hv' : 0 < v := by simpa only [interior_Ioi, Set.mem_Ioi] using hv
    exact (RadialHeatProfile.spatialProfile_hasDerivAt_s (by linarith) hν
      hv').differentiableAt.differentiableWithinAt
  · intro v hv
    have hv' : 0 < v := by simpa only [interior_Ioi, Set.mem_Ioi] using hv
    rw [(RadialHeatProfile.spatialProfile_hasDerivAt_s (by linarith) hν hv').deriv]
    exact (RadialHeatProfile.spatialFirst_neg (by linarith) hν hv').le

theorem heatDensity_eq_profileSq (h ν : ℝ) {v : ℝ} (hv : 0 < v) :
    heatDensity h ν v = RadialHeatProfile.spatialProfile (1 + h) ν v ^ 2 / v := by
  have he := physicalHeat_sq_div 1 h (p := (1 - ν, (v, 0))) hv
  simpa only [TerminalStress.physicalHeat, one_mul, one_pow, sub_sub_cancel, heatDensity,
    pressureWeight] using he.symm

theorem taperDerivativeDensity_continuousOn {h ν y : ℝ} {f : ℝ → ℝ}
    (hh : 0 < h) (hν : 0 ≤ ν) (hf : ContDiff ℝ ∞ f) :
    ContinuousOn (taperDerivativeDensity h f (ν, y)) (Ioi 0) := by
  have hy : ContinuousOn (fun v : ℝ => y + Real.log v) (Ioi 0) :=
    continuousOn_const.add (Real.continuousOn_log.mono (fun v hv => ne_of_gt hv))
  exact ((heatDensity_continuousOn hh hν).mul (hf.continuous.comp_continuousOn hy)).mul
    ((hf.continuous_deriv (by simp)).comp_continuousOn hy)

theorem taperDerivativeIntegral_bound {h Y : ℝ} {f : ℝ → ℝ} {p : ℝ × ℝ}
    (hh : 0 < h) (hf : ContDiff ℝ ∞ f) (hb : ∀ y, 0 ≤ f y ∧ f y ≤ 1)
    (hmono : ∀ y, 0 ≤ deriv f y) (hplateau : ∀ y, Y ≤ y → f y = 1)
    (hν : 0 < p.1) :
    0 ≤ taperDerivativeIntegral h f p ∧
      taperDerivativeIntegral h f p ≤
        RadialHeatProfile.profile (1 + h) (2 * p.1) ^ 2 * (1 - f p.2) := by
  let g : ℝ → ℝ := fun v => f (p.2 + Real.log v)
  let dg : ℝ → ℝ := fun v => deriv f (p.2 + Real.log v) / v
  let K : ℝ → ℝ := RadialHeatProfile.spatialProfile (1 + h) p.1
  have hd (v : ℝ) (hv : v ∈ Ici (1 : ℝ)) : HasDerivAt g (dg v) v := by
    have hvp : 0 < v := zero_lt_one.trans_le hv
    have he := (hf.differentiable (by simp) (p.2 + Real.log v)).hasDerivAt.comp v
      ((Real.hasDerivAt_log hvp.ne').const_add p.2)
    convert! he using 1
  have hdpos (v : ℝ) (hv : v ∈ Ioi (1 : ℝ)) : 0 ≤ dg v :=
    div_nonneg (hmono _) (zero_lt_one.trans hv).le
  have hg : Tendsto g atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (Real.exp (Y - p.2))] with v hv
    have hvp : 0 < v := (Real.exp_pos _).trans_le hv
    have hl : Y - p.2 ≤ Real.log v := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (Y - p.2)) hv
    exact (hplateau (p.2 + Real.log v) (by linarith)).symm
  have hdi : IntegrableOn dg (Ioi (1 : ℝ)) := integrableOn_Ioi_deriv_of_nonneg' hd hdpos hg
  have hdi_eq : (∫ v in Ioi (1 : ℝ), dg v) = 1 - f p.2 := by
    simpa only [g, Real.log_one, add_zero] using integral_Ioi_of_hasDerivAt_of_nonneg' hd hdpos hg
  have hK1 : K 1 = RadialHeatProfile.profile (1 + h) (2 * p.1) := by
    simp only [K, RadialHeatProfile.spatialProfile, Real.one_rpow, div_one, one_mul]
  have hpoint (v : ℝ) (hv : v ∈ Ioi (1 : ℝ)) :
      0 ≤ taperDerivativeDensity h f p v ∧
      taperDerivativeDensity h f p v ≤ K 1 ^ 2 * dg v := by
    have hvp : 0 < v := zero_lt_one.trans hv
    have hKpos : 0 ≤ K v := by
      exact mul_nonneg (Real.rpow_nonneg hvp.le _)
        (RadialHeatProfile.profile_pos (a := 1 + h) (by linarith) (by positivity)).le
    have hKle : K v ≤ K 1 := spatialHeat_antitoneOn hh hν
      (show (1 : ℝ) ∈ Ioi 0 by norm_num) hvp hv.le
    have he : taperDerivativeDensity h f p v = (K v ^ 2 * f (p.2 + Real.log v)) * dg v := by
      rw [taperDerivativeDensity, heatDensity_eq_profileSq h p.1 hvp]
      dsimp only [K, dg]
      ring
    rw [he]
    constructor
    · exact mul_nonneg (mul_nonneg (sq_nonneg _) (hb _).1) (hdpos v hv)
    · apply mul_le_mul_of_nonneg_right _ (hdpos v hv)
      calc
        _ ≤ K v ^ 2 := mul_le_of_le_one_right (sq_nonneg _) (hb _).2
        _ ≤ K 1 ^ 2 := by nlinarith
  have hi : IntegrableOn (taperDerivativeDensity h f p) (Ioi (1 : ℝ)) := by
    apply (hdi.const_mul (K 1 ^ 2)).mono'
    · exact ((taperDerivativeDensity_continuousOn hh hν.le hf).mono
        (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      rw [Real.norm_eq_abs, abs_of_nonneg (hpoint v hv).1]
      exact (hpoint v hv).2
  constructor
  · exact setIntegral_nonneg measurableSet_Ioi (fun v hv => (hpoint v hv).1)
  · have hle := setIntegral_mono_on hi (hdi.const_mul (K 1 ^ 2)) measurableSet_Ioi
      (fun v hv => (hpoint v hv).2)
    simpa only [taperDerivativeIntegral, integral_const_mul, hdi_eq, hK1] using hle

theorem physicalHeat_sq (C h : ℝ) {p : SimilarityProfile.PhysicalPoint} (hs : 0 < p.2.1) :
    TerminalStress.physicalHeat C (1 + h) p ^ 2 =
      C ^ 2 * p.2.1 ^ (-2 * amplitudeExponent h) *
        RadialHeatProfile.profile (1 + h) (2 * (1 - p.1) / p.2.1) ^ 2 := by
  have he := physicalHeat_sq_div C h hs
  rw [Real.rpow_sub hs, Real.rpow_one] at he
  apply (div_left_inj' hs.ne').mp
  convert! he using 1
  ring

theorem axialPressureIntegral_bound (C : ℝ) {h Y : ℝ} {f : ℝ → ℝ}
    {p : SimilarityProfile.PhysicalPoint} (hh : 0 < h) (hh1 : h < 1 / 2)
    (ht : p.1 < 1) (hs : 0 < p.2.1) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ y, 0 ≤ f y ∧ f y ≤ 1) (hmono : ∀ y, 0 ≤ deriv f y)
    (hplateau : ∀ y, Y ≤ y → f y = 1) :
    0 ≤ axialPressureIntegral C h f p ∧ axialPressureIntegral C h f p ≤
      TerminalStress.physicalHeat C (1 + h) p ^ 2 * (1 - f (Real.log (SimilarityProfile.X h p))) :=
        by
  rw [axialPressureIntegral_eq C f (SimilarityProfile.q_pos hh hh1 ht) hs]
  have hbnd := taperDerivativeIntegral_bound (p := pressureCoordinates h p) hh hf hb hmono hplateau
    (div_pos (sub_pos.mpr ht) hs)
  have hc : 0 ≤ C ^ 2 * p.2.1 ^ (-2 * amplitudeExponent h) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _)
  constructor
  · exact mul_nonneg hc hbnd.1
  · rw [physicalHeat_sq C h hs]
    have he : 2 * (pressureCoordinates h p).1 = 2 * (1 - p.1) / p.2.1 := by
      dsimp [pressureCoordinates]
      ring
    have h := mul_le_mul_of_nonneg_left hbnd.2 hc
    simp only [he, mul_assoc] at h ⊢
    exact h

theorem canonicalPressure_partialZ_bound (C : ℝ) {h Y : ℝ} {f : ℝ → ℝ}
    {p : SimilarityProfile.PhysicalPoint} (hh : 0 < h) (hh1 : h < 1 / 2)
    (ht : p.1 < 1) (hs : 0 < p.2.1) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ y, 0 ≤ f y ∧ f y ≤ 1) (hmono : ∀ y, 0 ≤ deriv f y)
    (hplateau : ∀ y, Y ≤ y → f y = 1) :
    |SimilarityProfile.partialZ (TerminalStress.canonicalPressure
      (TerminalStress.swirlCoefficient C h f)) p| ≤
      |logScaleDerivative h p| * TerminalStress.physicalHeat C (1 + h) p ^ 2 *
        (1 - f (Real.log (SimilarityProfile.X h p))) := by
  rw [canonicalPressure_partialZ C hh hh1 ht hs hf hb hplateau, abs_mul,
    abs_of_nonneg (axialPressureIntegral_bound C hh hh1 ht hs hf hb hmono hplateau).1,
    mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (axialPressureIntegral_bound C hh hh1 ht hs hf hb hmono hplateau).2 (abs_nonneg _)

theorem logScaleDerivative_eq {h : ℝ} {p : SimilarityProfile.PhysicalPoint}
    (hq : 0 < SimilarityProfile.q h p) :
    logScaleDerivative h p = 2 * SimilarityProfile.eta h p /
      (SimilarityProfile.q h p ^ CoordinateAlgebra.D h * CoordinateAlgebra.L h
        (SimilarityProfile.eta h p)) := by
  unfold logScaleDerivative CoordinateAlgebra.qAxial
  rw [div_right_comm, mul_div_cancel_right₀ _ hq.ne']

theorem logScaleDerivative_bound {h : ℝ} {p : SimilarityProfile.PhysicalPoint}
    (hh : 0 < h) (hh1 : h < 1 / 2) (ht : p.1 < 1) :
    |logScaleDerivative h p| ≤ 2 / (1 - 2 * h) * SimilarityProfile.q h p ^ (-CoordinateAlgebra.D h)
      := by
  have hq := SimilarityProfile.q_pos hh hh1 ht
  have heta := SimilarityProfile.eta_sq_lt_one hh hh1 ht
  have heta1 : |SimilarityProfile.eta h p| ≤ 1 := by
    exact (abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
  have hL := SimilarityProfile.L_pos hh hh1 ht
  have hL0 : 1 - 2 * h ≤ CoordinateAlgebra.L h (SimilarityProfile.eta h p) := by
    unfold CoordinateAlgebra.L
    nlinarith
  have hh0 : 0 < 1 - 2 * h := by linarith
  have hpow := Real.rpow_pos_of_pos hq (CoordinateAlgebra.D h)
  rw [logScaleDerivative_eq hq, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (mul_pos hpow hL)]
  calc
    _ ≤ 2 / (SimilarityProfile.q h p ^ CoordinateAlgebra.D h * CoordinateAlgebra.L h
      (SimilarityProfile.eta h p)) := by
      exact div_le_div_of_nonneg_right (by nlinarith) (mul_pos hpow hL).le
    _ ≤ 2 / (SimilarityProfile.q h p ^ CoordinateAlgebra.D h * (1 - 2 * h)) :=
      div_le_div_of_nonneg_left (by norm_num) (mul_pos hpow hh0)
        (mul_le_mul_of_nonneg_left hL0 hpow.le)
    _ = _ := by
      rw [Real.rpow_neg hq.le]
      field_simp [hpow.ne', hh0.ne']

/-! ## The actual outgoing taper and its terminal edge estimate -/

noncomputable def outgoingTaper (d : OutgoingTail.TailData) (y0 y : ℝ) : ℝ :=
  OutgoingTail.tailShape d (y - y0)

theorem outgoingTaper_contDiff (d : OutgoingTail.TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (outgoingTaper d y0) :=
  (OutgoingTail.tailShape_contDiff d).comp (contDiff_id.sub contDiff_const)

theorem outgoingTaper_deriv (d : OutgoingTail.TailData) (y0 y : ℝ) :
    deriv (outgoingTaper d y0) y = OutgoingTail.tailShapeDeriv d (y - y0) := by
  have h := ((OutgoingTail.tailShape_hasDerivAt d (y - y0)).comp y
    ((hasDerivAt_id y).sub_const y0)).deriv
  simp only [mul_one] at h
  exact h

theorem outgoingTaper_bounds (d : OutgoingTail.TailData) (y0 y : ℝ) :
    0 ≤ outgoingTaper d y0 y ∧ outgoingTaper d y0 y ≤ 1 :=
  ⟨(OutgoingTail.tailShape_pos d _).le, (OutgoingTail.tailShape_bounds d _).2⟩

theorem outgoingTaper_deriv_nonneg (d : OutgoingTail.TailData) (y0 y : ℝ) :
    0 ≤ deriv (outgoingTaper d y0) y := by
  rw [outgoingTaper_deriv]
  exact OutgoingTail.tailShapeDeriv_nonneg d _

theorem outgoingTaper_plateau (d : OutgoingTail.TailData) (y0 y : ℝ) (hy : y0 + 3 ≤ y) :
    outgoingTaper d y0 y = 1 := OutgoingTail.tailShape_late d (by linarith)

noncomputable def outgoingPressure (C : ℝ) (d : OutgoingTail.TailData) (y0 : ℝ) :
    SimilarityProfile.PhysicalProfile :=
  TerminalStress.canonicalPressure (TerminalStress.swirlCoefficient C d.h (outgoingTaper d y0))

theorem outgoingPressure_contDiffAt (C : ℝ) (d : OutgoingTail.TailData) (y0 : ℝ)
    {p : SimilarityProfile.PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1) :
    ContDiffAt ℝ ∞ (outgoingPressure C d y0) p :=
  canonicalPressure_contDiffAt C d.h_pos d.h_lt_half ht hs (outgoingTaper_contDiff d y0)
    (outgoingTaper_bounds d y0) (outgoingTaper_plateau d y0)

/-- Fully expanded formula for the actual pressure derivative needed in the
terminal edge chart. The integration coordinate is the physical `s=r^2/2`. -/
theorem outgoingPressure_partialZ (C : ℝ) (d : OutgoingTail.TailData) (y0 : ℝ)
    {p : SimilarityProfile.PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1) :
    SimilarityProfile.partialZ (outgoingPressure C d y0) p =
      logScaleDerivative d.h p * ∫ s in Ioi p.2.1,
        TerminalStress.physicalHeat C (1 + d.h) (p.1, (s, p.2.2)) ^ 2 *
          OutgoingTail.tailShape d (Real.log (s / SimilarityProfile.q d.h p) - y0) *
          OutgoingTail.tailShapeDeriv d (Real.log (s / SimilarityProfile.q d.h p) - y0) / s := by
  have he := canonicalPressure_partialZ C d.h_pos d.h_lt_half ht hs (outgoingTaper_contDiff d y0)
    (outgoingTaper_bounds d y0) (outgoingTaper_plateau d y0)
  simpa only [outgoingPressure, axialPressureIntegral, outgoingTaper_deriv, outgoingTaper] using he

theorem outgoingPressure_partialZ_bound (C : ℝ) (d : OutgoingTail.TailData) (y0 : ℝ)
    {p : SimilarityProfile.PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1) :
    |SimilarityProfile.partialZ (outgoingPressure C d y0) p| ≤
      (2 / (1 - 2 * d.h)) * SimilarityProfile.q d.h p ^ (-CoordinateAlgebra.D d.h) *
        TerminalStress.physicalHeat C (1 + d.h) p ^ 2 *
          (1 - OutgoingTail.tailShape d (Real.log (SimilarityProfile.X d.h p) - y0)) := by
  have hb := canonicalPressure_partialZ_bound C d.h_pos d.h_lt_half ht hs
    (outgoingTaper_contDiff d y0) (outgoingTaper_bounds d y0) (outgoingTaper_deriv_nonneg d y0)
    (outgoingTaper_plateau d y0)
  apply hb.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (logScaleDerivative_bound d.h_pos d.h_lt_half ht) (sq_nonneg _))
    (sub_nonneg.mpr (outgoingTaper_bounds d y0 _).2)

theorem outgoingPressure_edge_bound (C : ℝ) (d : OutgoingTail.TailData) (y0 : ℝ)
    {p : SimilarityProfile.PhysicalPoint} {δ : ℝ} (ht : p.1 < 1) (hs : 0 < p.2.1)
    (hδ : Real.log (SimilarityProfile.X d.h p) = y0 + 3 - δ) :
    |SimilarityProfile.partialZ (outgoingPressure C d y0) p| ≤
      (2 / (1 - 2 * d.h)) * SimilarityProfile.q d.h p ^ (-CoordinateAlgebra.D d.h) *
        TerminalStress.physicalHeat C (1 + d.h) p ^ 2 *
          (d.rho * FlatCutoff.edge 4 δ * TerminalStress.taperFactor δ) := by
  have hb := outgoingPressure_partialZ_bound C d y0 ht hs
  rwa [hδ, show y0 + 3 - δ - y0 = 3 - δ by ring, TerminalStress.tailShape_deficit] at hb

/-! ## Compact support of the terminal forcing and its positive mass -/

theorem integrableOn_Ioi_of_eventually_zero {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hg : ContinuousOn g (Ioi 0)) (hz : g =ᶠ[atTop] fun _ => 0) :
    IntegrableOn g (Ioi r) := by
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.1 hz
  have hi : IntegrableOn g (Icc r (max r b)) :=
    (hg.mono (fun u hu => hr.trans_le hu.1)).integrableOn_Icc
  apply (hi.integrable_indicator measurableSet_Icc).integrableOn.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  by_cases hm : u ≤ max r b
  · simp only [indicator_of_mem (show u ∈ Icc r (max r b) from ⟨hu.le, hm⟩)]
  · rw [indicator_of_notMem (show u ∉ Icc r (max r b) from fun h => hm h.2),
      hb u ((le_max_right r b).trans (le_of_not_ge hm))]

theorem logX_radial_contDiffAt {h t z r : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (ht : t < 1) (hr : 0 < r) :
    ContDiffAt ℝ ∞ (fun u => Real.log (SimilarityProfile.X h (TerminalStress.radiusPoint t u z))) r
      := by
  have hs : 0 < (TerminalStress.radiusPoint t r z).2.1 := by
    dsimp [TerminalStress.radiusPoint]
    positivity
  have hX := (SimilarityProfile.inner_smoothAt hh hh1 (p := TerminalStress.radiusPoint t r z)
    ht).fst
  exact (hX.log (div_pos hs (SimilarityProfile.q_pos hh hh1 ht)).ne').comp r
    (TerminalStress.radiusPoint_contDiff t z).contDiffAt

theorem terminal_forcing_integrable (C : ℝ) {h t z r Y : ℝ} {f : ℝ → ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (ht : t < 1) (hr : 0 < r)
    (hf : ContDiff ℝ ∞ f) (hplateau : ∀ y, Y ≤ y → f y = 1) :
    IntegrableOn (fun u => u ^ 2 * TerminalStress.viscousResidual
      (TerminalStress.heatAmplitude C (1 + h) t)
      (TerminalStress.radialSlice (TerminalStress.flattening h f) t z) u) (Ioi r) ∧
    IntegrableOn (TerminalStress.correction (TerminalStress.heatAmplitude C (1 + h) t)
      (TerminalStress.radialSlice (TerminalStress.flattening h f) t z)) (Ioi r) ∧
    IntegrableOn (fun u => u ^ 2 * TerminalStress.timeResidual C h f t z u) (Ioi r) := by
  let K := TerminalStress.heatAmplitude C (1 + h) t
  let g := TerminalStress.radialSlice (TerminalStress.flattening h f) t z
  have hK (u : ℝ) (hu : 0 < u) : ContDiffAt ℝ ∞ K u :=
    TerminalStress.heatAmplitude_contDiffAt C (by linarith) ht hu
  have hg (u : ℝ) (hu : 0 < u) : ContDiffAt ℝ ∞ g u :=
    hf.contDiffAt.comp u (logX_radial_contDiffAt hh hh1 ht hu)
  have hgd (u : ℝ) (hu : 0 < u) : ContDiffAt ℝ ∞ (deriv g) u :=
    TerminalStress.contDiffAt_deriv (hg u hu) (by simp)
  have hgdd (u : ℝ) (hu : 0 < u) : ContDiffAt ℝ ∞ (deriv (deriv g)) u :=
    TerminalStress.contDiffAt_deriv (hgd u hu) (by simp)
  have hKd (u : ℝ) (hu : 0 < u) : ContDiffAt ℝ ∞ (deriv K) u :=
    TerminalStress.contDiffAt_deriv (hK u hu) (by simp)
  have hfp : f =ᶠ[atTop] fun _ => 1 := by
    filter_upwards [eventually_ge_atTop Y] with y hy
    exact hplateau y hy
  have hgp : g =ᶠ[atTop] fun _ => 1 := TerminalStress.radial_flattening_plateau hh hh1 ht hfp
  have hgp' := TerminalStress.deriv_eventually_zero_of_eventually_const hgp
  have hgp'' := TerminalStress.deriv_eventually_zero_of_eventually_const hgp'
  have hfp' := (TerminalStress.logX_radial_tendsto (z := z) hh hh1 ht).eventually
    (TerminalStress.deriv_eventually_zero_of_eventually_const hfp)
  refine ⟨integrableOn_Ioi_of_eventually_zero hr ?_ ?_,
    integrableOn_Ioi_of_eventually_zero hr ?_ ?_, integrableOn_Ioi_of_eventually_zero hr ?_ ?_⟩
  · intro u hu
    exact ((continuousAt_id.pow 2).mul
      (((hK u hu).continuousAt.neg.mul ((hgdd u hu).continuousAt.add
        ((hgd u hu).continuousAt.div continuousAt_id hu.ne'))).sub
          ((continuousAt_const.mul (hKd u hu).continuousAt).mul (hgd u
            hu).continuousAt))).continuousWithinAt
  · filter_upwards [hgp', hgp''] with u hu hu'
    change u ^ 2 * TerminalStress.viscousResidual K g u = 0
    simp only [TerminalStress.viscousResidual, hu, hu', zero_div, add_zero, mul_zero, sub_zero]
  · intro u hu
    exact (((continuousAt_id.mul (hK u hu).continuousAt).sub
      ((continuousAt_id.pow 2).mul (hKd u hu).continuousAt)).mul (hgd u
        hu).continuousAt).continuousWithinAt
  · filter_upwards [hgp'] with u hu
    change TerminalStress.correction K g u = 0
    simp only [TerminalStress.correction, hu, mul_zero]
  · intro u hu
    exact ((continuousAt_id.pow 2).mul
      (((hK u hu).continuousAt.mul ((hf.continuous_deriv (by simp)).continuousAt.comp
        (logX_radial_contDiffAt hh hh1 ht hu).continuousAt)).div_const _)).continuousWithinAt
  · filter_upwards [hfp'] with u hu
    simp only [TerminalStress.timeResidual, hu, mul_zero, zero_div]

theorem logX_radial_strict {h t z r R : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (ht : t < 1) (hr : 0 < r) (hrR : r < R) :
    Real.log (SimilarityProfile.X h (TerminalStress.radiusPoint t r z)) <
      Real.log (SimilarityProfile.X h (TerminalStress.radiusPoint t R z)) := by
  have hq := SimilarityProfile.q_pos hh hh1 (p := (t, (0, z))) ht
  apply Real.log_lt_log (div_pos (by dsimp [TerminalStress.radiusPoint]; positivity) hq)
  change (r ^ 2 / 2) / SimilarityProfile.q h (t, (0, z)) <
    (R ^ 2 / 2) / SimilarityProfile.q h (t, (0, z))
  apply (div_lt_div_iff_of_pos_right hq).mpr
  nlinarith

/-- A positive lower bound for the actual backward angular stress. Every tail
integrability hypothesis is discharged using the taper's genuine plateau. -/
theorem terminalStress_ge_mass {C h t z r R Y : ℝ} {f : ℝ → ℝ}
    (hC : 0 < C) (hh : 0 < h) (hh1 : h < 1 / 2) (ht : t < 1)
    (hr : 0 < r) (hrR : r ≤ R) (hf : ContDiff ℝ ∞ f) (hmono : ∀ y, 0 ≤ deriv f y)
    (hplateau : ∀ y, Y ≤ y → f y = 1)
    (hR : Y ≤ Real.log (SimilarityProfile.X h (TerminalStress.radiusPoint t R z))) :
    (r * TerminalStress.heatAmplitude C (1 + h) t R / (2 * TerminalStress.timeDenominator h t z)) *
      (1 - f (Real.log (SimilarityProfile.X h (TerminalStress.radiusPoint t r z)))) ≤
        TerminalStress.terminalStress C h f t z r := by
  let K := TerminalStress.heatAmplitude C (1 + h) t
  let g := TerminalStress.radialSlice (TerminalStress.flattening h f) t z
  have hK : ∀ u ∈ Ici r, DifferentiableAt ℝ K u := fun u hu =>
    (TerminalStress.heatAmplitude_contDiffAt C (by linarith) ht (hr.trans_le hu)).differentiableAt
      (by simp)
  have hF : ∀ u ∈ Ici r, ContDiffAt ℝ 2 g u := fun u hu =>
    TerminalStress.flattening_radial_contDiffAt hh hh1 ht (hr.trans_le hu)
      (hf.of_le (WithTop.coe_le_coe.mpr le_top))
  have hgp : g =ᶠ[atTop] fun _ => 1 := by
    apply TerminalStress.radial_flattening_plateau hh hh1 ht
    filter_upwards [eventually_ge_atTop Y] with y hy
    exact hplateau y hy
  have hlim : Tendsto g atTop (𝓝 1) := tendsto_const_nhds.congr' hgp.symm
  have hinc : ∀ u ∈ Ici r, 0 ≤ deriv g u := by
    intro u hu
    rw [(TerminalStress.flattening_radial_hasDerivAt hh hh1 ht (hr.trans_le hu)
      (hf.differentiable (by simp) _)).deriv]
    exact div_nonneg (mul_nonneg (by norm_num) (hmono _)) (hr.trans_le hu).le
  have hi := terminal_forcing_integrable C (z := z) hh hh1 ht hr hf hplateau
  have hfi : IntegrableOn (deriv g) (Ioi r) :=
    integrableOn_Ioi_deriv_of_nonneg'
      (fun u hu => ((hF u hu).differentiableAt (by norm_num)).hasDerivAt)
      (fun u hu => hinc u (show r ≤ u from le_of_lt hu)) hlim
  have hcompare : ∀ u ∈ Ioi r,
      (r ^ 3 * K R / (2 * TerminalStress.timeDenominator h t z)) * deriv g u ≤
        u ^ 2 * TerminalStress.timeResidual C h f t z u := by
    intro u hu
    by_cases huR : u ≤ R
    · exact TerminalStress.timeResidual_lower_comparison hC hh hh1 ht hr hu.le huR
        (hf.differentiable (by simp) _) (hmono _)
    · have hRu : R < u := lt_of_not_ge huR
      have hy := hR.trans_lt (logX_radial_strict hh hh1 ht (hr.trans_le hrR) hRu)
      have hdf := deriv_zero_after_plateau hplateau hy
      rw [(TerminalStress.flattening_radial_hasDerivAt hh hh1 ht (hr.trans hu)
        (hf.differentiable (by simp) _)).deriv, hdf]
      simp only [TerminalStress.timeResidual, hdf, mul_zero, zero_div, le_refl]
  have hm := TerminalStress.backwardStress_ge_mass hr hK hF hi.1 hi.2.1 hi.2.2
    (TerminalStress.boundary_tendsto_zero_of_plateau K hgp) hfi hlim
    (fun u hu => (TerminalStress.heatAmplitude_pos hC (by linarith) ht (hr.trans_le hu)).le)
    (fun u hu => (TerminalStress.heatAmplitude_deriv_neg hC (by linarith) ht (hr.trans hu)).le)
    hinc hcompare
  have he : (fun u => TerminalStress.leadingResidual C h f t u z) =
      (fun u => TerminalStress.timeResidual C h f t z u + TerminalStress.viscousResidual K g u) :=
    funext fun u => TerminalStress.leadingResidual_eq_time_add C h f t u z
  rw [TerminalStress.terminalStress, he]
  convert! hm using 1
  dsimp [K, g, TerminalStress.radialSlice, TerminalStress.flattening]
  field_simp [hr.ne', (TerminalStress.timeDenominator_pos hh hh1 (z := z) ht).ne']

/-! ## The genuine backward axial pressure stress -/

theorem canonicalPressure_partialZ_contDiffAt (C : ℝ) {h Y : ℝ} {f : ℝ → ℝ}
    {p : SimilarityProfile.PhysicalPoint} (hh : 0 < h) (hh1 : h < 1 / 2)
    (ht : p.1 < 1) (hs : 0 < p.2.1) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ y, 0 ≤ f y ∧ f y ≤ 1) (hplateau : ∀ y, Y ≤ y → f y = 1) :
    ContDiffAt ℝ ∞ (SimilarityProfile.partialZ (TerminalStress.canonicalPressure
      (TerminalStress.swirlCoefficient C h f))) p :=
  ((canonicalPressure_contDiffAt C hh hh1 ht hs hf hb hplateau).fderiv_right
    (by simp)).clm_apply contDiffAt_const

/-- Since `ds = r dr`, this is the cylindrical backward primitive with weight
`r`. It uses the actual axial derivative of the canonical pressure. -/
noncomputable def axialBackwardStress (C h : ℝ) (f : ℝ → ℝ) (t z r : ℝ) : ℝ :=
  (∫ s in Ioi (r ^ 2 / 2), SimilarityProfile.partialZ (TerminalStress.canonicalPressure
    (TerminalStress.swirlCoefficient C h f)) (t, (s, z))) / r

theorem physicalHeat_pos {C h : ℝ} {p : SimilarityProfile.PhysicalPoint}
    (hC : 0 < C) (hh : 0 < h) (ht : p.1 < 1) (hs : 0 < p.2.1) :
    0 < TerminalStress.physicalHeat C (1 + h) p := by
  exact mul_pos hC (mul_pos (Real.rpow_pos_of_pos hs _)
    (RadialHeatProfile.profile_pos (by linarith)
      (div_nonneg (mul_nonneg (by norm_num) (sub_pos.mpr ht).le) hs.le)))

theorem physicalHeat_radial_le {C h t z a s : ℝ} (hC : 0 < C) (hh : 0 < h)
    (ht : t < 1) (ha : 0 < a) (has : a ≤ s) :
    TerminalStress.physicalHeat C (1 + h) (t, (s, z)) ≤
      TerminalStress.physicalHeat C (1 + h) (t, (a, z)) :=
  mul_le_mul_of_nonneg_left (spatialHeat_antitoneOn hh (sub_pos.mpr ht) ha
    (ha.trans_le has) has) hC.le

theorem axialBackwardStress_bound {C h t z r R Y : ℝ} {f : ℝ → ℝ}
    (hC : 0 < C) (hh : 0 < h) (hh1 : h < 1 / 2) (ht : t < 1)
    (hr : 0 < r) (hrR : r ≤ R) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ y, 0 ≤ f y ∧ f y ≤ 1) (hmono : ∀ y, 0 ≤ deriv f y)
    (hplateau : ∀ y, Y ≤ y → f y = 1)
    (hR : Y ≤ Real.log (SimilarityProfile.X h (TerminalStress.radiusPoint t R z))) :
    IntegrableOn (fun s => SimilarityProfile.partialZ (TerminalStress.canonicalPressure
      (TerminalStress.swirlCoefficient C h f)) (t, (s, z))) (Ioi (r ^ 2 / 2)) ∧
    |axialBackwardStress C h f t z r| ≤ ((R ^ 2 - r ^ 2) / (2 * r)) *
      |logScaleDerivative h (TerminalStress.radiusPoint t r z)| *
      TerminalStress.heatAmplitude C (1 + h) t r ^ 2 *
      (1 - f (Real.log (SimilarityProfile.X h (TerminalStress.radiusPoint t r z)))) := by
  let p := TerminalStress.radiusPoint t r z
  let P := TerminalStress.canonicalPressure (TerminalStress.swirlCoefficient C h f)
  let g : ℝ → ℝ := fun s => SimilarityProfile.partialZ P (t, (s, z))
  let B := |logScaleDerivative h p| * TerminalStress.physicalHeat C (1 + h) p ^ 2 *
    (1 - f (Real.log (SimilarityProfile.X h p)))
  have ha : 0 < r ^ 2 / 2 := by positivity
  have hRpos : 0 < R := hr.trans_le hrR
  have hS : r ^ 2 / 2 ≤ R ^ 2 / 2 := by nlinarith
  have hq : 0 < SimilarityProfile.q h p := SimilarityProfile.q_pos hh hh1 ht
  have hmonof : Monotone f := monotone_of_deriv_nonneg (hf.differentiable (by simp)) hmono
  have hpoint (s : ℝ) (hs : r ^ 2 / 2 ≤ s) : |g s| ≤ B := by
    have hsp : 0 < s := ha.trans_le hs
    have hbound := canonicalPressure_partialZ_bound C (p := (t, (s, z))) hh hh1 ht hsp hf hb hmono
      hplateau
    have hK := physicalHeat_radial_le (z := z) hC hh ht ha hs
    change TerminalStress.physicalHeat C (1 + h) (t, (s, z)) ≤
      TerminalStress.physicalHeat C (1 + h) p at hK
    have hK0 := (physicalHeat_pos (p := (t, (s, z))) hC hh ht hsp).le
    have hKsq : TerminalStress.physicalHeat C (1 + h) (t, (s, z)) ^ 2 ≤
        TerminalStress.physicalHeat C (1 + h) p ^ 2 := by nlinarith
    have hlog : Real.log (SimilarityProfile.X h p) ≤ Real.log (SimilarityProfile.X h (t, (s, z)))
      := by
      apply Real.log_le_log (div_pos ha hq)
      exact (div_le_div_iff_of_pos_right hq).mpr hs
    have hfdec := sub_le_sub_left (hmonof hlog) 1
    exact hbound.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hKsq (abs_nonneg _)) hfdec
      (sub_nonneg.mpr (hb _).2) (mul_nonneg (abs_nonneg _) (sq_nonneg _)))
  have hzero (s : ℝ) (hs : R ^ 2 / 2 < s) : g s = 0 := by
    have hsp : 0 < s := (show 0 < R ^ 2 / 2 by positivity).trans hs
    have hy : Y ≤ Real.log (SimilarityProfile.X h (t, (s, z))) := by
      apply hR.trans
      apply Real.log_le_log (div_pos (show 0 < R ^ 2 / 2 by positivity) hq)
      exact (div_le_div_iff_of_pos_right hq).mpr hs.le
    have hbound := canonicalPressure_partialZ_bound C (p := (t, (s, z))) hh hh1 ht hsp hf hb hmono
      hplateau
    rw [hplateau _ hy, sub_self, mul_zero] at hbound
    exact abs_nonpos_iff.mp hbound
  have hcont : ContinuousOn g (Ioi 0) := by
    intro s hs
    exact (((canonicalPressure_partialZ_contDiffAt C (p := (t, (s, z))) hh hh1 ht hs hf hb
      hplateau).comp s
      (contDiffAt_const.prodMk (contDiffAt_id.prodMk
        contDiffAt_const))).continuousAt).continuousWithinAt
  have hi : IntegrableOn g (Ioi (r ^ 2 / 2)) := integrableOn_Ioi_of_eventually_zero ha hcont (by
    filter_upwards [eventually_gt_atTop (R ^ 2 / 2)] with s hs
    exact hzero s hs)
  refine ⟨hi, ?_⟩
  have hnorm : |∫ s in Ioi (r ^ 2 / 2), g s| ≤ B * (R ^ 2 / 2 - r ^ 2 / 2) := by
    rw [integral_tail_eq_interval hS hzero]
    have he := intervalIntegral.norm_integral_le_of_norm_le_const (f := g) (C := B)
      (a := r ^ 2 / 2) (b := R ^ 2 / 2)
      (fun s hs => by
        rw [uIoc_of_le hS] at hs
        simpa only [Real.norm_eq_abs] using hpoint s hs.1.le)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hS)] using he
  rw [axialBackwardStress, abs_div, abs_of_pos hr]
  calc
    _ ≤ B * (R ^ 2 / 2 - r ^ 2 / 2) / r := div_le_div_of_nonneg_right hnorm hr.le
    _ = _ := by dsimp [B, p, TerminalStress.physicalHeat, TerminalStress.heatAmplitude,
      TerminalStress.radiusPoint, RadialHeatProfile.radialProfile]; ring

/-! ## Coarse angular/axial tilt on a fixed terminal annulus -/

theorem heatProfile_antitoneOn {h : ℝ} (hh : 0 < h) :
    AntitoneOn (RadialHeatProfile.profile (1 + h)) (Ioi 0) := by
  have ha : 1 < 1 + h := by linarith
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · exact (RadialHeatProfile.profile_contDiffOn ha).continuousOn.mono Ioi_subset_Ici_self
  · intro u hu
    have hu' : 0 < u := by simpa only [interior_Ioi, Set.mem_Ioi] using hu
    exact (RadialHeatProfile.profile_hasDerivAt ha hu').differentiableAt.differentiableWithinAt
  · intro u hu
    have hu' : 0 < u := by simpa only [interior_Ioi, Set.mem_Ioi] using hu
    rw [← derivWithin_of_mem_nhds (Ici_mem_nhds hu')]
    exact (RadialHeatProfile.profile_derivWithin_neg ha hu'.le).le

theorem heatAmplitude_annulus_lower {C h t r R Λ : ℝ}
    (hC : 0 < C) (hh : 0 < h) (ht : t < 1) (hr : 0 < r) (hrR : r ≤ R)
    (hΛ : 1 ≤ Λ) (hRΛ : R ^ 2 ≤ Λ * r ^ 2) :
    Λ ^ (-amplitudeExponent h) * TerminalStress.heatAmplitude C (1 + h) t r ≤
      TerminalStress.heatAmplitude C (1 + h) t R := by
  have hR : 0 < R := hr.trans_le hrR
  have hτ : 0 < 1 - t := sub_pos.mpr ht
  have ha : 0 < r ^ 2 / 2 := by positivity
  have hb : 0 < R ^ 2 / 2 := by positivity
  have hab : r ^ 2 / 2 ≤ R ^ 2 / 2 := by nlinarith
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hpow : Λ ^ (-amplitudeExponent h) * (r ^ 2 / 2) ^ (-amplitudeExponent h) ≤
      (R ^ 2 / 2) ^ (-amplitudeExponent h) := by
    rw [← Real.mul_rpow hΛp.le ha.le]
    exact Real.rpow_le_rpow_of_nonpos hb (by nlinarith) (by dsimp [amplitudeExponent]; linarith)
  have harg : 2 * (1 - t) / (R ^ 2 / 2) ≤ 2 * (1 - t) / (r ^ 2 / 2) :=
    div_le_div_of_nonneg_left (by positivity) ha hab
  have hH := heatProfile_antitoneOn hh (div_pos (by positivity) hb) (div_pos (by positivity) ha)
    harg
  have hHa := (RadialHeatProfile.profile_pos (a := 1 + h) (by linarith)
    (show 0 ≤ 2 * (1 - t) / (r ^ 2 / 2) by positivity)).le
  have he := mul_le_mul hpow hH hHa (Real.rpow_nonneg hb.le _)
  have heC := mul_le_mul_of_nonneg_left he hC.le
  simpa only [TerminalStress.heatAmplitude, RadialHeatProfile.radialProfile_source_formula,
    amplitudeExponent, mul_assoc, mul_left_comm, mul_comm] using heC

theorem timeDenominator_le_q {h t z : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (ht : t < 1) :
    TerminalStress.timeDenominator h t z ≤ SimilarityProfile.q h (t, (0, z)) := by
  have hq := (SimilarityProfile.q_pos hh hh1 (p := (t, (0, z))) ht).le
  have hL : CoordinateAlgebra.L h (SimilarityProfile.eta h (t, (0, z))) ≤ 1 := by
    unfold CoordinateAlgebra.L
    nlinarith [sq_nonneg (SimilarityProfile.eta h (t, (0, z)))]
  exact (mul_le_mul_of_nonneg_left hL hq).trans_eq (mul_one _)

noncomputable def tiltConstant (h Λ : ℝ) : ℝ :=
  (2 / (1 - 2 * h)) * (Λ - 1) / Λ ^ (-amplitudeExponent h)

/-- Actual backward stresses satisfy the coarse tilt estimate on any fixed
annulus. The factor `q^(1-D) K` is subsequently bounded by the released amplitude. -/
theorem terminal_tilt_bound {C h t z r R Y Λ : ℝ} {f : ℝ → ℝ}
    (hC : 0 < C) (hh : 0 < h) (hh1 : h < 1 / 2) (ht : t < 1)
    (hr : 0 < r) (hrR : r ≤ R) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ y, 0 ≤ f y ∧ f y ≤ 1) (hmono : ∀ y, 0 ≤ deriv f y)
    (hplateau : ∀ y, Y ≤ y → f y = 1)
    (hR : Y ≤ Real.log (SimilarityProfile.X h (TerminalStress.radiusPoint t R z)))
    (hΛ : 1 ≤ Λ) (hRΛ : R ^ 2 ≤ Λ * r ^ 2)
    (hinside : f (Real.log (SimilarityProfile.X h (TerminalStress.radiusPoint t r z))) < 1) :
    0 < TerminalStress.terminalStress C h f t z r ∧
    |axialBackwardStress C h f t z r| / TerminalStress.terminalStress C h f t z r ≤
      tiltConstant h Λ * SimilarityProfile.q h (TerminalStress.radiusPoint t r z) ^ (1 -
        CoordinateAlgebra.D h) *
        TerminalStress.heatAmplitude C (1 + h) t r := by
  let p := TerminalStress.radiusPoint t r z
  let q := SimilarityProfile.q h p
  let K := TerminalStress.heatAmplitude C (1 + h) t r
  let E := 1 - f (Real.log (SimilarityProfile.X h p))
  let b := Λ ^ (-amplitudeExponent h)
  let c := 2 / (1 - 2 * h)
  let S := TerminalStress.terminalStress C h f t z r
  have hq : 0 < q := SimilarityProfile.q_pos hh hh1 ht
  have hK : 0 < K := TerminalStress.heatAmplitude_pos hC (by linarith) ht hr
  have hE : 0 < E := sub_pos.mpr hinside
  have hbpos : 0 < b := Real.rpow_pos_of_pos (zero_lt_one.trans_le hΛ) _
  have hc : 0 < c := div_pos (by norm_num) (by linarith)
  have hQ := TerminalStress.timeDenominator_pos (z := z) hh hh1 ht
  have hm := terminalStress_ge_mass hC hh hh1 ht hr hrR hf hmono hplateau hR
  have hcarrier := heatAmplitude_annulus_lower hC hh ht hr hrR hΛ hRΛ
  have hlow : r * b * K / (2 * q) * E ≤ S := by
    apply le_trans _ hm
    apply mul_le_mul_of_nonneg_right _ hE.le
    calc
      _ ≤ r * TerminalStress.heatAmplitude C (1 + h) t R / (2 * q) :=
        div_le_div_of_nonneg_right (by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcarrier hr.le) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left
        (mul_nonneg hr.le (TerminalStress.heatAmplitude_pos hC (by linarith) ht (hr.trans_le
          hrR)).le)
        (by positivity) (mul_le_mul_of_nonneg_left (timeDenominator_le_q hh hh1 ht) (by norm_num))
  have hS : 0 < S := (mul_pos (div_pos (mul_pos (mul_pos hr hbpos) hK) (by positivity))
    hE).trans_le hlow
  refine ⟨hS, ?_⟩
  have hax := (axialBackwardStress_bound hC hh hh1 ht hr hrR hf hb hmono hplateau hR).2
  have hlength : (R ^ 2 - r ^ 2) / (2 * r) ≤ (Λ - 1) * r / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * r)).mpr
    nlinarith
  have hB : |axialBackwardStress C h f t z r| ≤
      ((Λ - 1) * r / 2) * (c * q ^ (-CoordinateAlgebra.D h)) * K ^ 2 * E := by
    apply hax.trans
    apply mul_le_mul_of_nonneg_right _ hE.le
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg K)
    apply mul_le_mul hlength (logScaleDerivative_bound hh hh1 ht) (abs_nonneg _)
      (div_nonneg (mul_nonneg (sub_nonneg.mpr hΛ) hr.le) (by norm_num))
  let M := tiltConstant h Λ * q ^ (1 - CoordinateAlgebra.D h) * K
  have hM : 0 ≤ M := by
    exact mul_nonneg (mul_nonneg
      (div_nonneg (mul_nonneg hc.le (sub_nonneg.mpr hΛ)) hbpos.le)
      (Real.rpow_nonneg hq.le _)) hK.le
  have halg : ((Λ - 1) * r / 2) * (c * q ^ (-CoordinateAlgebra.D h)) * K ^ 2 * E =
      M * (r * b * K / (2 * q) * E) := by
    dsimp only [M, tiltConstant, b, c]
    rw [Real.rpow_sub hq, Real.rpow_one, Real.rpow_neg hq.le]
    field_simp [hq.ne', (Real.rpow_pos_of_pos hq (CoordinateAlgebra.D h)).ne',
      show Λ ^ (-amplitudeExponent h) ≠ 0 from hbpos.ne', show 1 - 2 * h ≠ 0 by linarith]
  have hfinal : |axialBackwardStress C h f t z r| ≤ M * S :=
    hB.trans (halg.trans_le (mul_le_mul_of_nonneg_left hlow hM))
  exact (div_le_iff₀ hS).mpr hfinal

/-! ## Uniform smallness from the constructed release -/

theorem outgoingAmplitude_suppressed (d : OutgoingTail.TailData) :
    HeatTailEdit.outgoingAmplitude d ≤
      4 * OutgoingTail.finalAngular d (d.releaseStart, 0) * d.h ^ 4 := by
  have hstart : OutgoingTail.tailStart d ≤ HeatTailEdit.switchStart d := by
    unfold HeatTailEdit.switchStart
    linarith
  have hlate : d.releaseStart + d.secondRampStart ≤ HeatTailEdit.switchStart d := by
    dsimp [HeatTailEdit.switchStart, OutgoingTail.tailStart, OutgoingTail.TailData.rampEnd]
    linarith [OutgoingTail.decayHold_pos d]
  have he : OutgoingTail.finalAngular d (HeatTailEdit.switchStart d, 0) =
      HeatTailEdit.outgoingAmplitude d * (1 - d.rho) := by
    rw [OutgoingTail.finalAngular_tail d 0 hstart, OutgoingTail.tailShape_early d]
    · rfl
    · unfold HeatTailEdit.switchStart
      linarith
  have hb := TailCone.finalAngular_suppressed d 0 hlate
  rw [he] at hb
  have hp := HeatTailEdit.outgoingAmplitude_pos d
  have hρ := d.rho_lt_half
  nlinarith

/-- The normalization is exactly the physical carrier normalization in
`ParametricHeatTail.physicalEdit_heat_carrier`. -/
noncomputable def releasedNormalization (d : OutgoingTail.TailData) (K : ℝ) : ℝ :=
  HeatTailEdit.outgoingAmplitude d * K ^ amplitudeExponent d.h

theorem releasedNormalization_pos (d : OutgoingTail.TailData) {K : ℝ} (hK : 0 < K) :
    0 < releasedNormalization d K :=
  mul_pos (HeatTailEdit.outgoingAmplitude_pos d) (Real.rpow_pos_of_pos hK _)

/-- The actual parametric heat edit agrees with this module's physical carrier.
The diffusion identity is proved from the physical similarity coordinates. -/
theorem physicalEdit_eq_released_carrier (d : OutgoingTail.TailData) {K : ℝ} (hK : 0 < K)
    {p : SimilarityProfile.PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1)
    (hfull : 1 / 2 ≤ Real.log (SimilarityProfile.X d.h p / K) + 1 / 5) :
    SimilarityProfile.q d.h p ^ (-amplitudeExponent d.h) *
      ParametricHeatTail.physicalEdit d K (SimilarityProfile.eta d.h p) (SimilarityProfile.X d.h p)
        =
        TerminalStress.physicalHeat (releasedNormalization d K) (1 + d.h) p *
          outgoingTaper d (Real.log K - 1 / 5) (Real.log (SimilarityProfile.X d.h p)) := by
  have hq := SimilarityProfile.q_pos d.h_pos d.h_lt_half ht
  have hτ : 1 - p.1 = SimilarityProfile.q d.h p * (1 - SimilarityProfile.eta d.h p ^ 2) :=
    SimilarityCoordinates.tau_coordinate_identity (by linarith [d.h_pos])
      (by linarith [d.h_lt_half]) (p := (1 - p.1, p.2.2)) (sub_pos.mpr ht)
  have hν : ParametricHeatTail.diffusion (SimilarityProfile.eta d.h p) =
      (1 - p.1) / SimilarityProfile.q d.h p := by
    rw [hτ]
    unfold ParametricHeatTail.diffusion
    field_simp [hq.ne']
  have he := ParametricHeatTail.physicalEdit_heat_carrier d hK hq hs hν hfull
  have hlog : Real.log (SimilarityProfile.X d.h p / K) + 1 / 5 =
      Real.log (SimilarityProfile.X d.h p) - (Real.log K - 1 / 5) := by
    unfold SimilarityProfile.X
    rw [Real.log_div (div_pos hs hq).ne' hK.ne']
    ring
  simp only [SimilarityProfile.X] at hlog
  rw [hlog] at he
  simpa only [SimilarityProfile.X, TerminalStress.physicalHeat, releasedNormalization,
    outgoingTaper, HeatTailEdit.exponent, amplitudeExponent] using he

theorem released_heat_bound (d : OutgoingTail.TailData) {K : ℝ} (hK : 0 < K)
    {p : SimilarityProfile.PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1)
    (hX : K ≤ SimilarityProfile.X d.h p) :
    SimilarityProfile.q d.h p ^ (1 - CoordinateAlgebra.D d.h) *
      TerminalStress.physicalHeat (releasedNormalization d K) (1 + d.h) p ≤
        HeatTailEdit.outgoingAmplitude d := by
  let A := amplitudeExponent d.h
  let q := SimilarityProfile.q d.h p
  have hq : 0 < q := SimilarityProfile.q_pos d.h_pos d.h_lt_half ht
  have hτ : 0 < 1 - p.1 := sub_pos.mpr ht
  have hA : 0 ≤ A := by dsimp [A, amplitudeExponent]; linarith [d.h_pos]
  have hKq : K * q ≤ p.2.1 := (le_div_iff₀ hq).mp hX
  have hratio : (K * q) ^ A / p.2.1 ^ A ≤ 1 := by
    apply (div_le_one (Real.rpow_pos_of_pos hs A)).mpr
    exact Real.rpow_le_rpow (mul_pos hK hq).le hKq hA
  have hratio0 : 0 ≤ (K * q) ^ A / p.2.1 ^ A := by positivity
  have hH := RadialHeatProfile.profile_le_one (a := 1 + d.h) (by linarith [d.h_pos])
    (show 0 ≤ 2 * (1 - p.1) / p.2.1 by positivity)
  have hH0 := (RadialHeatProfile.profile_pos (a := 1 + d.h) (by linarith [d.h_pos])
    (show 0 ≤ 2 * (1 - p.1) / p.2.1 by positivity)).le
  have hexp : 1 - CoordinateAlgebra.D d.h = A := by
    dsimp [CoordinateAlgebra.D, A, amplitudeExponent]
    ring
  have hexp' : RadialHeatProfile.spatialExponent (1 + d.h) = -A := by
    dsimp [RadialHeatProfile.spatialExponent, A, amplitudeExponent]
    ring
  calc
    _ = HeatTailEdit.outgoingAmplitude d * ((K * q) ^ A / p.2.1 ^ A) *
        RadialHeatProfile.profile (1 + d.h) (2 * (1 - p.1) / p.2.1) := by
      rw [hexp]
      unfold TerminalStress.physicalHeat RadialHeatProfile.spatialProfile releasedNormalization
      rw [hexp', Real.rpow_neg hs.le, Real.mul_rpow hK.le hq.le]
      dsimp only [A, q]
      ring
    _ ≤ HeatTailEdit.outgoingAmplitude d * 1 * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hratio (HeatTailEdit.outgoingAmplitude_pos d).le)
        hH hH0 (mul_nonneg (HeatTailEdit.outgoingAmplitude_pos d).le (by norm_num))
    _ = _ := by ring

theorem tiltConstant_uniform {h Λ : ℝ} (hh : 0 < h) (hh4 : h ≤ 1 / 4) (hΛ : 1 ≤ Λ) :
    tiltConstant h Λ ≤ 4 * Λ * (Λ - 1) := by
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hc : 2 / (1 - 2 * h) ≤ 4 := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - 2 * h)).mpr
    linarith
  have hp : Λ⁻¹ ≤ Λ ^ (-amplitudeExponent h) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hΛ (by dsimp [amplitudeExponent]; linarith)
  unfold tiltConstant
  calc
    _ ≤ 4 * (Λ - 1) / Λ ^ (-amplitudeExponent h) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr hΛ))
        (Real.rpow_nonneg hΛp.le _)
    _ ≤ 4 * (Λ - 1) / Λ⁻¹ :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (sub_nonneg.mpr hΛ)) (inv_pos.mpr hΛp) hp
    _ = _ := by rw [div_inv_eq_mul]; ring

theorem outgoingTaper_lt_one (d : OutgoingTail.TailData) {y0 y : ℝ} (hy : y < y0 + 3) :
    outgoingTaper d y0 y < 1 := by
  have hδ : 0 < y0 + 3 - y := by linarith
  have he := TerminalStress.tailShape_deficit d (y0 + 3 - y)
  have hp := mul_pos (mul_pos d.rho_pos (FlatCutoff.edge_pos 4 hδ))
    (TerminalStress.taperFactor_pos (y0 + 3 - y))
  rw [show 3 - (y0 + 3 - y) = y - y0 by ring] at he
  change OutgoingTail.tailShape d (y - y0) < 1
  linarith

/-- The bound is uniform in spacetime, in the terminal scale `K`, and in the
distance to the edge. The released amplitude contributes the proved factor `h^4`. -/
theorem released_terminal_tilt (d : OutgoingTail.TailData) {K y0 t z r R Λ : ℝ}
    (hK : 0 < K) (hh4 : d.h ≤ 1 / 4) (ht : t < 1) (hr : 0 < r) (hrR : r ≤ R)
    (hΛ : 1 ≤ Λ) (hRΛ : R ^ 2 ≤ Λ * r ^ 2)
    (hX : K ≤ SimilarityProfile.X d.h (TerminalStress.radiusPoint t r z))
    (hR : y0 + 3 ≤ Real.log (SimilarityProfile.X d.h (TerminalStress.radiusPoint t R z)))
    (hinside : Real.log (SimilarityProfile.X d.h (TerminalStress.radiusPoint t r z)) < y0 + 3) :
    0 < TerminalStress.terminalStress (releasedNormalization d K) d.h (outgoingTaper d y0) t z r ∧
    |axialBackwardStress (releasedNormalization d K) d.h (outgoingTaper d y0) t z r| /
      TerminalStress.terminalStress (releasedNormalization d K) d.h (outgoingTaper d y0) t z r ≤
        16 * Λ * (Λ - 1) * OutgoingTail.finalAngular d (d.releaseStart, 0) * d.h ^ 4 := by
  have hb := terminal_tilt_bound (releasedNormalization_pos d hK) d.h_pos d.h_lt_half ht hr hrR
    (outgoingTaper_contDiff d y0) (outgoingTaper_bounds d y0) (outgoingTaper_deriv_nonneg d y0)
    (outgoingTaper_plateau d y0) hR hΛ hRΛ (outgoingTaper_lt_one d hinside)
  refine ⟨hb.1, hb.2.trans ?_⟩
  have hc := tiltConstant_uniform d.h_pos hh4 hΛ
  have hΛp : 0 ≤ Λ := zero_le_one.trans hΛ
  have hΛsub : 0 ≤ Λ - 1 := sub_nonneg.mpr hΛ
  have hheat := released_heat_bound d hK (p := TerminalStress.radiusPoint t r z) ht
    (by dsimp [TerminalStress.radiusPoint]; positivity) hX
  have hp : 0 ≤ SimilarityProfile.q d.h (TerminalStress.radiusPoint t r z) ^ (1 -
    CoordinateAlgebra.D d.h) *
      TerminalStress.heatAmplitude (releasedNormalization d K) (1 + d.h) t r := by
    exact mul_nonneg (Real.rpow_nonneg (SimilarityProfile.q_pos d.h_pos d.h_lt_half ht).le _)
      (TerminalStress.heatAmplitude_pos (releasedNormalization_pos d hK) (by linarith [d.h_pos]) ht
        hr).le
  calc
    _ ≤ (4 * Λ * (Λ - 1)) * HeatTailEdit.outgoingAmplitude d := by
      rw [mul_assoc]
      exact mul_le_mul hc hheat hp (by positivity)
    _ ≤ (4 * Λ * (Λ - 1)) *
        (4 * OutgoingTail.finalAngular d (d.releaseStart, 0) * d.h ^ 4) :=
      mul_le_mul_of_nonneg_left (outgoingAmplitude_suppressed d) (by positivity)
    _ = _ := by ring

theorem released_terminal_tilt_small (d : OutgoingTail.TailData) {K y0 t z r R Λ ε : ℝ}
    (hK : 0 < K) (hh4 : d.h ≤ 1 / 4) (ht : t < 1) (hr : 0 < r) (hrR : r ≤ R)
    (hΛ : 1 ≤ Λ) (hRΛ : R ^ 2 ≤ Λ * r ^ 2)
    (hX : K ≤ SimilarityProfile.X d.h (TerminalStress.radiusPoint t r z))
    (hR : y0 + 3 ≤ Real.log (SimilarityProfile.X d.h (TerminalStress.radiusPoint t R z)))
    (hinside : Real.log (SimilarityProfile.X d.h (TerminalStress.radiusPoint t r z)) < y0 + 3)
    (hsmall : d.h ≤ ε / (1 + 16 * Λ * (Λ - 1) * OutgoingTail.finalAngular d (d.releaseStart, 0))) :
    |axialBackwardStress (releasedNormalization d K) d.h (outgoingTaper d y0) t z r| /
      TerminalStress.terminalStress (releasedNormalization d K) d.h (outgoingTaper d y0) t z r ≤ ε
        := by
  have hb := (released_terminal_tilt d hK hh4 ht hr hrR hΛ hRΛ hX hR hinside).2
  let B := 16 * Λ * (Λ - 1) * OutgoingTail.finalAngular d (d.releaseStart, 0)
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hΛ))
    (sub_nonneg.mpr hΛ)) (OutgoingTail.finalAngular_pos d _).le
  have hh1 : d.h ≤ 1 := by linarith
  have hhpow : d.h ^ 4 ≤ d.h := by
    calc
      _ = d.h * d.h ^ 3 := by ring
      _ ≤ d.h * 1 ^ 3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ d.h_pos.le hh1 3) d.h_pos.le
      _ = _ := by ring
  have hs : d.h * (1 + B) ≤ ε := (le_div_iff₀ (by linarith : 0 < 1 + B)).mp hsmall
  apply hb.trans
  change B * d.h ^ 4 ≤ ε
  nlinarith [mul_le_mul_of_nonneg_left hhpow hB, d.h_pos]

/-- Full physical residual formula after discharging the pressure regularity
and improper-integral assumptions. The axial viscosity of the swirl is retained. -/
theorem outgoing_navierStokesResidual (C : ℝ) (d : OutgoingTail.TailData) (y0 : ℝ)
    {t : ℝ} {x : ProblemStatement.Space} (ht : t < 1)
    (hs : 0 < AxisymmetricFields.radialEnergy x) :
    ProblemStatement.navierStokesResidual
      (TerminalStress.terminalVelocity C d.h (outgoingTaper d y0))
      (TerminalStress.terminalPressure C d.h (outgoingTaper d y0)) t x =
      AxisymmetricResidual.pack
        (-x 1 / Real.sqrt (2 * AxisymmetricFields.radialEnergy x) *
          (TerminalStress.leadingResidual C d.h (outgoingTaper d y0) t
            (Real.sqrt (2 * AxisymmetricFields.radialEnergy x)) (x 2) -
          TerminalStress.axialViscosity C d.h (outgoingTaper d y0) (AxisymmetricFields.profilePoint
            t x)))
        (x 0 / Real.sqrt (2 * AxisymmetricFields.radialEnergy x) *
          (TerminalStress.leadingResidual C d.h (outgoingTaper d y0) t
            (Real.sqrt (2 * AxisymmetricFields.radialEnergy x)) (x 2) -
          TerminalStress.axialViscosity C d.h (outgoingTaper d y0) (AxisymmetricFields.profilePoint
            t x)))
        (SimilarityProfile.partialZ (outgoingPressure C d y0) (AxisymmetricFields.profilePoint t
          x)) := by
  let a := AxisymmetricFields.radialEnergy x / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hi := swirlCoefficient_sq_integrable C (p := (t, (a, x 2))) d.h_pos d.h_lt_half ht ha
    (outgoingTaper_contDiff d y0).continuous (outgoingTaper_bounds d y0)
  have hc : ContinuousOn (fun s => TerminalStress.swirlCoefficient C d.h (outgoingTaper d y0)
      (t, (s, x 2)) ^ 2) (Ioi a) := by
    intro s hs'
    have hlocal := TerminalStress.swirlCoefficient_contDiffAt C
      (p := (t, (s, x 2))) (f := outgoingTaper d y0) d.h_pos d.h_lt_half ht (ha.trans hs')
      ((outgoingTaper_contDiff d y0).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
    exact (((hlocal.comp s (contDiffAt_const.prodMk
      (contDiffAt_id.prodMk contDiffAt_const))).continuousAt).pow 2).continuousWithinAt
  exact TerminalStress.terminal_navierStokesResidual C d.h_pos d.h_lt_half ht hs
    ((outgoingTaper_contDiff d y0).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
    (show a < AxisymmetricFields.radialEnergy x by dsimp [a]; linarith) hi hc
    ((outgoingPressure_contDiffAt C d y0 ht hs).differentiableAt (by simp))

/-- The backward axial primitive has the required cylindrical divergence,
computed from actual derivatives of the canonical pressure. -/
theorem axialBackwardStress_divergence {C h t z r R Y : ℝ} {f : ℝ → ℝ}
    (hC : 0 < C) (hh : 0 < h) (hh1 : h < 1 / 2) (ht : t < 1)
    (hr : 0 < r) (hrR : r ≤ R) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ y, 0 ≤ f y ∧ f y ≤ 1) (hmono : ∀ y, 0 ≤ deriv f y)
    (hplateau : ∀ y, Y ≤ y → f y = 1)
    (hR : Y ≤ Real.log (SimilarityProfile.X h (TerminalStress.radiusPoint t R z))) :
    deriv (axialBackwardStress C h f t z) r + axialBackwardStress C h f t z r / r =
      -SimilarityProfile.partialZ (TerminalStress.canonicalPressure
        (TerminalStress.swirlCoefficient C h f)) (TerminalStress.radiusPoint t r z) := by
  let g : ℝ → ℝ := fun s => SimilarityProfile.partialZ (TerminalStress.canonicalPressure
    (TerminalStress.swirlCoefficient C h f)) (t, (s, z))
  have ha : 0 < (r / 2) ^ 2 / 2 := by positivity
  have hab : (r / 2) ^ 2 / 2 < r ^ 2 / 2 := by nlinarith [sq_pos_of_pos hr]
  have hi : IntegrableOn g (Ioi ((r / 2) ^ 2 / 2)) :=
    (axialBackwardStress_bound hC hh hh1 ht (by positivity : 0 < r / 2)
      (by linarith : r / 2 ≤ R) hf hb hmono hplateau hR).1
  have hc : ContinuousOn g (Ioi ((r / 2) ^ 2 / 2)) := by
    intro s hs
    exact (((canonicalPressure_partialZ_contDiffAt C (p := (t, (s, z))) hh hh1 ht
      (ha.trans hs) hf hb hplateau).comp s
        (contDiffAt_const.prodMk (contDiffAt_id.prodMk
          contDiffAt_const))).continuousAt).continuousWithinAt
  have hd := (TerminalStress.neg_tailIntegral_hasDerivAt hab hi hc).fun_neg
  simp only [neg_neg] at hd
  have hdr := hd.comp r (RadialHeatProfile.radiusSquared_hasDerivAt r)
  have hquot := hdr.fun_div (hasDerivAt_id r) hr.ne'
  change HasDerivAt (axialBackwardStress C h f t z) _ r at hquot
  rw [hquot.deriv]
  change _ = -g (r ^ 2 / 2)
  dsimp only [axialBackwardStress, Function.comp_apply, id_eq]
  field_simp [hr.ne'] ; ring

end NavierStokes.TerminalPressure

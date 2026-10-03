/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Analytic.Energy.Component
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The integrals over `c ∈ (0, ∞)` with the weight `g = (1/3, 5/3, 4/3)`
(the proof notes (8′), the proof notes, Lemma 12):

    ∫ g ρ_c(t) dc = rhoA a t,   ∫ g (1 − c/u_c)/2 dc = massA a,   ∫ g w_c(x) dc = Wt |x|,
    ∫ g kC a c dc = ellA a + 2 log(a/2)(massA a − 1).

Each by one generic statement (`integral_gtil`): `g = 1/3 + (4/3)1_{c≥1} − (1/3)1_{c≥5}` and
`∫_{(α,∞)} Φ' = L − Φ(α)`. The antiderivatives are `−G/(4π)`, `(c − u_c)/2`, `(c/2)log(1 +
x²/c²) + |x| atan(c/|x|)`
and `−J` (FstarDefs). -/

public section

open Real MeasureTheory Set Filter Topology

namespace Zeta32.Analytic.EnergyI
noncomputable section

theorem gtil_eq (c : ℝ) :
    gtil c = 1/3 + (4/3) * (Ici (1:ℝ)).indicator 1 c - (1/3) * (Ici (5:ℝ)).indicator 1 c := by
  unfold gtil
  by_cases h1 : c < 1
  · have h5 : c < 5 := by linarith
    simp [h1, show ¬ (1:ℝ) ≤ c by linarith, show ¬ (5:ℝ) ≤ c by linarith, Set.indicator]
  · by_cases h5 : c < 5
    · simp [h1, h5, show (1:ℝ) ≤ c by linarith, show ¬ (5:ℝ) ≤ c by linarith, Set.indicator];
      norm_num
    · simp [h1, h5, show (1:ℝ) ≤ c by linarith, show (5:ℝ) ≤ c by linarith, Set.indicator]

theorem gtil_pos (c : ℝ) : 0 < gtil c := by
  unfold gtil; split_ifs <;> norm_num

theorem measurable_gtil : Measurable gtil := by
  have : gtil = fun c => 1/3 + (4/3) * (Ici (1:ℝ)).indicator 1 c - (1/3) * (Ici (5:ℝ)).indicator
    1 c :=
    funext gtil_eq
  rw [this]
  exact ((measurable_const.add (measurable_const.mul
    (measurable_one.indicator measurableSet_Ici))).sub (measurable_const.mul
    (measurable_one.indicator measurableSet_Ici)))

theorem setIntegral_Ioi_indicator {F : ℝ → ℝ} {α : ℝ} (hα : 0 ≤ α) :
    ∫ c in Ioi (0:ℝ), (Ici α).indicator 1 c * F c = ∫ c in Ioi α, F c := by
  have e : (fun c => (Ici α).indicator 1 c * F c) = (Ici α).indicator F := by
    funext c; by_cases h : c ∈ Ici α <;> simp [h]
  rw [e, setIntegral_indicator measurableSet_Ici]
  rcases hα.lt_or_eq with hα | hα
  · rw [show Ioi (0:ℝ) ∩ Ici α = Ici α by
      ext c; simp only [mem_inter_iff, mem_Ioi, mem_Ici]; constructor
      · exact fun h => h.2
      · exact fun h => ⟨hα.trans_le h, h⟩]
    exact integral_Ici_eq_integral_Ioi
  · subst hα
    have hs : Ioi (0:ℝ) ∩ Ici 0 = Ioi 0 := by
      ext c; simp only [mem_inter_iff, mem_Ioi, mem_Ici]
      exact ⟨fun h => h.1, fun h => ⟨h, h.le⟩⟩
    rw [hs]

/-- The generic `g`-integral. -/
theorem integral_gtil {F Φ : ℝ → ℝ} {L : ℝ} (hcont : ContinuousWithinAt Φ (Ici 0) 0)
    (hderiv : ∀ c ∈ Ioi (0 : ℝ), HasDerivAt Φ (F c) c) (hint : IntegrableOn F (Ioi 0))
    (hlim : Tendsto Φ atTop (𝓝 L)) :
    IntegrableOn (fun c => gtil c * F c) (Ioi 0) ∧
      ∫ c in Ioi (0:ℝ), gtil c * F c = (4/3) * L - (1/3) * Φ 0 - (4/3) * Φ 1 + (1/3) * Φ 5 := by
  have hI : ∀ α : ℝ, 0 < α → ∫ c in Ioi α, F c = L - Φ α := by
    intro α hα
    exact integral_Ioi_of_hasDerivAt_of_tendsto
      (hderiv α hα).continuousAt.continuousWithinAt
      (fun c hc => hderiv c (hα.trans hc)) (hint.mono_set (Ioi_subset_Ioi hα.le)) hlim
  have hI0 : ∫ c in Ioi (0:ℝ), F c = L - Φ 0 :=
    integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  have hind : ∀ α : ℝ, IntegrableOn (fun c => (Ici α).indicator 1 c * F c) (Ioi 0) := by
    intro α
    have e : (fun c => (Ici α).indicator 1 c * F c) = (Ici α).indicator F := by
      funext c; by_cases h : c ∈ Ici α <;> simp [h]
    rw [e]; exact hint.indicator measurableSet_Ici
  have e : (fun c => gtil c * F c) = fun c => (1/3) * F c + (4/3) * ((Ici (1:ℝ)).indicator 1 c *
    F c) -
      (1/3) * ((Ici (5:ℝ)).indicator 1 c * F c) := by
    funext c; rw [gtil_eq]; ring
  have hint' : IntegrableOn (fun c => gtil c * F c) (Ioi 0) := by
    rw [e]; exact ((hint.const_mul _).add ((hind 1).const_mul _)).sub ((hind 5).const_mul _)
  refine ⟨hint', ?_⟩
  have i1 : IntegrableOn (fun c => (1/3) * F c + (4/3) * ((Ici (1:ℝ)).indicator 1 c * F c)) (Ioi
    0) :=
    (hint.const_mul _).add ((hind 1).const_mul _)
  have i2 : IntegrableOn (fun c => (1/3) * ((Ici (5:ℝ)).indicator 1 c * F c)) (Ioi 0) :=
    (hind 5).const_mul _
  have i3 : IntegrableOn (fun c => (1/3) * F c) (Ioi 0) := hint.const_mul _
  have i4 : IntegrableOn (fun c => (4/3) * ((Ici (1:ℝ)).indicator 1 c * F c)) (Ioi 0) :=
    (hind 1).const_mul _
  rw [e, integral_sub i1 i2, integral_add i3 i4, integral_const_mul, integral_const_mul,
    integral_const_mul, setIntegral_Ioi_indicator (by norm_num), setIntegral_Ioi_indicator (by
      norm_num),
    hI0, hI 1 one_pos, hI 5 (by norm_num)]
  ring

section uC
variable {a : ℝ}

theorem hasDerivAt_uC (ha : 0 < a) (c : ℝ) : HasDerivAt (fun c => uC a c) (c / uC a c) c := by
  have h := ((hasDerivAt_pow 2 c).add_const (a^2)).sqrt (by positivity)
  unfold uC
  convert h using 1
  have : 0 < √(c^2 + a^2) := Real.sqrt_pos.mpr (by positivity)
  field_simp
  push_cast; ring

theorem continuous_uC (a : ℝ) : Continuous (fun c => uC a c) := by
  unfold uC; fun_prop

theorem uC_zero (ha : 0 < a) : uC a 0 = a := by
  unfold uC; simp [Real.sqrt_sq ha.le]

theorem tendsto_uC_sub (ha : 0 < a) : Tendsto (fun c => uC a c - c) atTop (𝓝 0) := by
  have h : ∀ c : ℝ, 0 < c → uC a c - c = a^2 / (uC a c + c) := by
    intro c hc
    have hu := uC_pos ha c
    have h2 := uC_sq a c
    field_simp
    nlinarith
  have hden : Tendsto (fun c => uC a c + c) atTop atTop := by
    exact tendsto_atTop_mono (fun c => by simp only [id]; linarith [(uC_pos ha c).le]) tendsto_id
  have := hden.inv_tendsto_atTop.const_mul (a^2)
  rw [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  rw [h c hc]; simp [div_eq_mul_inv]

theorem tendsto_uC_atTop (ha : 0 < a) : Tendsto (fun c => uC a c) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_id
  filter_upwards [eventually_ge_atTop 0] with c hc
  exact (c_lt_uC ha hc).le

end uC

section mass
variable {a : ℝ}

/-- `∫ g (1 − c/u_c)/2 dc = massA a`. -/
theorem integral_gtil_mass (ha : 0 < a) :
    IntegrableOn (fun c => gtil c * ((1 - c / uC a c) / 2)) (Ioi 0) ∧
      ∫ c in Ioi (0:ℝ), gtil c * ((1 - c / uC a c) / 2) = massA a := by
  have hderiv : ∀ c : ℝ, HasDerivAt (fun c => (c - uC a c) / 2) ((1 - c / uC a c) / 2) c := by
    intro c
    exact ((hasDerivAt_id c).sub (hasDerivAt_uC ha c)).div_const 2
  have hnn : ∀ c ∈ Ioi (0:ℝ), 0 ≤ (1 - c / uC a c) / 2 := by
    intro c hc
    have := c_lt_uC ha (le_of_lt hc)
    have hu := uC_pos ha c
    have : c / uC a c ≤ 1 := by rw [div_le_one hu]; linarith
    linarith
  have hlim : Tendsto (fun c => (c - uC a c) / 2) atTop (𝓝 0) := by
    have := (tendsto_uC_sub ha).neg.div_const 2
    simp only [neg_sub, neg_zero, zero_div] at this
    exact this
  have hint := integrableOn_Ioi_deriv_of_nonneg (hderiv 0).continuousAt.continuousWithinAt
    (fun c _ => hderiv c) hnn hlim
  obtain ⟨h1, h2⟩ := integral_gtil (hderiv 0).continuousAt.continuousWithinAt
    (fun c _ => hderiv c) hint hlim
  refine ⟨h1, ?_⟩
  rw [h2, uC_zero ha]
  unfold massA uC
  norm_num
  ring

end mass

section rho
variable {a t : ℝ}

theorem hasDerivAt_Gfun (ha : 0 < a) (ht0 : t ≠ 0) (hta : |t| < a) (c : ℝ) :
    HasDerivAt (fun c => -Gfun a c t / (4 * π)) (rhoC a c t) c := by
  set s := √(a^2 - t^2) with hsdef
  have hs2 : s^2 = a^2 - t^2 := Real.sq_sqrt (by nlinarith [sq_abs t, abs_nonneg t])
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsa : s < a := by
    have : s^2 < a^2 := by
      rw [hs2]
      have := pow_pos (abs_pos.mpr ht0) 2
      rw [sq_abs] at this
      linarith
    nlinarith
  have hU := uC_pos ha c
  have hU2 := uC_sq a c
  have haU : a ≤ uC a c := by nlinarith
  have hD : uC a c - s ≠ 0 := by linarith
  have hQ : (uC a c + s) / (uC a c - s) ≠ 0 := (div_pos (by linarith) (by linarith)).ne'
  have h := ((((hasDerivAt_uC ha c).add_const s).div ((hasDerivAt_uC ha c).sub_const s) hD).log
    hQ).neg.div_const
    (4 * π)
  have e : (fun c => -Gfun a c t / (4 * π)) = fun c => -Real.log ((uC a c + s) / (uC a c - s)) /
    (4 * π) := by
    funext c; rfl
  rw [e]
  convert h using 1
  simp only [Pi.div_apply]
  have ht2 : t^2 + c^2 = (uC a c - s) * (uC a c + s) := by nlinarith
  unfold rhoC
  rw [← hsdef, ht2]
  have hpi : 0 < π := Real.pi_pos
  have h1 : 0 < uC a c + s := by linarith
  have h2 : 0 < uC a c - s := by linarith
  field_simp
  ring

theorem tendsto_Gfun (ha : 0 < a) (t : ℝ) :
    Tendsto (fun c => -Gfun a c t / (4 * π)) atTop (𝓝 0) := by
  set s := √(a^2 - t^2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hden : Tendsto (fun c => uC a c - s) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_uC_atTop ha)
  have hq : Tendsto (fun c => 1 + 2 * s / (uC a c - s)) atTop (𝓝 1) := by
    have := (hden.inv_tendsto_atTop.const_mul (2 * s)).const_add 1
    simpa [div_eq_mul_inv, mul_assoc] using this
  have hlog := ((Real.continuousAt_log one_ne_zero).tendsto.comp hq).neg.div_const (4 * π)
  simp only [Real.log_one, neg_zero, zero_div] at hlog
  refine hlog.congr' ?_
  filter_upwards [hden.eventually_gt_atTop 0] with c hc
  simp only [Function.comp, Gfun]
  congr 3
  change 1 + 2 * s / (uC a c - s) = (uC a c + s) / (uC a c - s)
  field_simp; ring

/-- `rhoA a t = ∫ g ρ_c(t) dc` for `0 < |t| < a`. -/
theorem integral_gtil_rhoC (ha : 0 < a) (ht0 : t ≠ 0) (hta : |t| < a) :
    IntegrableOn (fun c => gtil c * rhoC a c t) (Ioi 0) ∧
      ∫ c in Ioi (0:ℝ), gtil c * rhoC a c t = rhoA a t := by
  have hderiv := hasDerivAt_Gfun ha ht0 hta
  have hnn : ∀ c ∈ Ioi (0:ℝ), 0 ≤ rhoC a c t := by
    intro c hc
    unfold rhoC
    have := uC_pos ha c
    have : 0 < t^2 + c^2 := by have := mem_Ioi.mp hc; positivity
    exact div_nonneg (mul_nonneg (le_of_lt (mem_Ioi.mp hc)) (Real.sqrt_nonneg _)) (by positivity)
  have hint := integrableOn_Ioi_deriv_of_nonneg (hderiv 0).continuousAt.continuousWithinAt
    (fun c _ => hderiv c) hnn (tendsto_Gfun ha t)
  obtain ⟨h1, h2⟩ := integral_gtil (hderiv 0).continuousAt.continuousWithinAt
    (fun c _ => hderiv c) hint (tendsto_Gfun ha t)
  refine ⟨h1, ?_⟩
  rw [h2]
  unfold rhoA
  ring

end rho

section Wt
variable {x : ℝ}

/-- Antiderivative of `wC · x` in `c` (`y = |x| > 0`). -/
def PhiW (y c : ℝ) : ℝ := c / 2 * Real.log (c^2 + y^2) - c * Real.log c + y * Real.arctan (c / y)

theorem hasDerivAt_PhiW {y : ℝ} (hy : 0 < y) {c : ℝ} (hc : 0 < c) :
    HasDerivAt (PhiW y) (Real.log (1 + y^2 / c^2) / 2) c := by
  have h1 := ((hasDerivAt_id c).div_const 2).mul (((hasDerivAt_pow 2 c).add_const (y^2)).log
    (by positivity))
  have h2 := (hasDerivAt_id c).mul (Real.hasDerivAt_log hc.ne')
  have h3 := ((hasDerivAt_id c).div_const y).arctan.const_mul y
  have h := (h1.sub h2).add h3
  have e : PhiW y = fun c => id c / 2 * Real.log (c^2 + y^2) - id c * Real.log c +
      y * Real.arctan (id c / y) := by funext c; rfl
  rw [e]
  convert h using 1
  rw [show 1 + y^2 / c^2 = (c^2 + y^2) / c^2 by field_simp, Real.log_div (by positivity) (by
    positivity),
    Real.log_pow]
  simp only [id]
  field_simp
  push_cast
  ring

theorem continuous_PhiW {y : ℝ} (hy : 0 < y) : Continuous (PhiW y) := by
  have : PhiW y = fun c => c / 2 * Real.log (c^2 + y^2) - c * Real.log c + y * Real.arctan (c /
    y) := rfl
  rw [this]
  refine ((continuous_id.div_const 2).mul ((by fun_prop : Continuous fun c : ℝ => c^2 + y^2).log
    (fun c => by positivity))).sub Real.continuous_mul_log |>.add ?_
  fun_prop

theorem tendsto_PhiW {y : ℝ} (hy : 0 < y) : Tendsto (PhiW y) atTop (𝓝 (y * (π / 2))) := by
  have ha : Tendsto (fun c => y * Real.arctan (c / y)) atTop (𝓝 (y * (π / 2))) :=
    (tendsto_nhds_of_tendsto_nhdsWithin (Real.tendsto_arctan_atTop.comp
      (tendsto_id.atTop_div_const hy))).const_mul y
  have hb : Tendsto (fun c => c / 2 * Real.log (c^2 + y^2) - c * Real.log c) atTop (𝓝 0) := by
    have hup : Tendsto (fun c : ℝ => y^2 / (2 * c)) atTop (𝓝 0) := by
      have := (tendsto_id.const_mul_atTop (show (0:ℝ) < 2 by
        norm_num)).inv_tendsto_atTop.const_mul (y^2)
      simpa [div_eq_mul_inv, mul_comm] using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with c hc
      rw [show c / 2 * Real.log (c^2 + y^2) - c * Real.log c = c / 2 * Real.log (1 + y^2 / c^2) by
        rw [show 1 + y^2 / c^2 = (c^2 + y^2) / c^2 by field_simp, Real.log_div (by positivity)
          (by positivity), Real.log_pow]; push_cast; ring]
      have h0 : 0 ≤ y^2 / c^2 := by positivity
      exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
    · filter_upwards [eventually_gt_atTop 0] with c hc
      rw [show c / 2 * Real.log (c^2 + y^2) - c * Real.log c = c / 2 * Real.log (1 + y^2 / c^2) by
        rw [show 1 + y^2 / c^2 = (c^2 + y^2) / c^2 by field_simp, Real.log_div (by positivity)
          (by positivity), Real.log_pow]; push_cast; ring]
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + y^2 / c^2 by positivity)
      calc c / 2 * Real.log (1 + y^2 / c^2) ≤ c / 2 * (y^2 / c^2) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = y^2 / (2 * c) := by field_simp
  have := hb.add ha
  simp only [zero_add] at this
  exact this.congr fun c => by unfold PhiW; ring

/-- `Wt |x| = ∫ g w_c(x) dc`. -/
theorem integral_gtil_wC (x : ℝ) :
    IntegrableOn (fun c => gtil c * wC c x) (Ioi 0) ∧
      ∫ c in Ioi (0:ℝ), gtil c * wC c x = Wt |x| := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    have : (fun c => gtil c * wC c 0) = fun _ => 0 := by funext c; simp [wC]
    rw [this]
    exact ⟨integrableOn_zero, by simp [Wt]⟩
  set y := |x| with hydef
  have hy : 0 < y := abs_pos.mpr hx
  have hw : ∀ c, wC c x = Real.log (1 + y^2 / c^2) / 2 := by
    intro c; unfold wC; rw [hydef, sq_abs]
  simp_rw [hw]
  have hderiv : ∀ c ∈ Ioi (0:ℝ), HasDerivAt (PhiW y) (Real.log (1 + y^2 / c^2) / 2) c :=
    fun c hc => hasDerivAt_PhiW hy hc
  have hcont : ContinuousWithinAt (PhiW y) (Ici 0) 0 :=
    (continuous_PhiW hy).continuousAt.continuousWithinAt
  have hnn : ∀ c ∈ Ioi (0:ℝ), 0 ≤ Real.log (1 + y^2 / c^2) / 2 := by
    intro c _
    have : 0 ≤ y^2 / c^2 := by positivity
    have := Real.log_nonneg (show (1:ℝ) ≤ 1 + y^2 / c^2 by linarith)
    linarith
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnn (tendsto_PhiW hy)
  obtain ⟨h1, h2⟩ := integral_gtil hcont hderiv hint (tendsto_PhiW hy)
  refine ⟨h1, ?_⟩
  rw [h2]
  have h0 : PhiW y 0 = 0 := by simp [PhiW]
  have hP1 : PhiW y 1 = Real.log (1 + y^2) / 2 + y * Real.arctan (1 / y) := by
    simp [PhiW]; ring
  have hP5 : PhiW y 5 = 5 / 2 * Real.log (1 + y^2 / 25) + y * Real.arctan (5 / y) := by
    unfold PhiW
    have : Real.log (5^2 + y^2) = Real.log (1 + y^2 / 25) + 2 * Real.log 5 := by
      rw [show (5:ℝ)^2 + y^2 = (1 + y^2 / 25) * 5^2 by ring, Real.log_mul (by positivity)
        (by positivity), Real.log_pow]; push_cast; ring
    rw [this]; ring
  rw [h0, hP1, hP5]
  unfold Wt
  ring

end Wt

section ell
variable {a : ℝ}

/-- Antiderivative of `log(2c/(c + u_c))`: `−J`. -/
def PhiJ (a c : ℝ) : ℝ := c * Real.log 2 + c * Real.log c - c * Real.log (c + uC a c) + uC a c - c

theorem PhiJ_eq_neg_Jfun (ha : 0 < a) {c : ℝ} (hc : 0 ≤ c) : PhiJ a c = -Jfun a c := by
  unfold PhiJ Jfun
  have hu := uC_pos ha c
  rcases hc.lt_or_eq with hc | hc
  · rw [show √(c^2 + a^2) = uC a c from rfl, Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) hc.ne']
    ring
  · subst hc; simp [uC]

theorem hasDerivAt_PhiJ (ha : 0 < a) {c : ℝ} (hc : 0 < c) :
    HasDerivAt (PhiJ a) (Real.log (2 * c / (uC a c + c))) c := by
  have hu := uC_pos ha c
  have hcu : 0 < c + uC a c := by linarith
  have h1 := (hasDerivAt_id c).mul_const (Real.log 2)
  have h2 := (hasDerivAt_id c).mul (Real.hasDerivAt_log hc.ne')
  have h3 := (hasDerivAt_id c).mul (((hasDerivAt_id c).add (hasDerivAt_uC ha c)).log hcu.ne')
  have h := (((h1.add h2).sub h3).add (hasDerivAt_uC ha c)).sub (hasDerivAt_id c)
  have e : PhiJ a = fun c => id c * Real.log 2 + id c * Real.log c -
      id c * Real.log (id c + uC a c) + uC a c - id c := by funext c; rfl
  rw [e]
  convert h using 1
  simp only [Pi.add_apply, id]
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) hc.ne', add_comm
    (uC a c) c]
  field_simp
  ring

theorem continuous_PhiJ (ha : 0 < a) : Continuous (PhiJ a) := by
  have hcu : ∀ c : ℝ, c + uC a c ≠ 0 := by
    intro c
    have h := uC_sq a c
    have hu := uC_pos ha c
    have : |c| < uC a c := by
      have : c^2 < uC a c ^ 2 := by rw [h]; nlinarith
      exact abs_lt_of_sq_lt_sq this hu.le
    have := neg_abs_le c
    intro h0; linarith
  have : PhiJ a = fun c => c * Real.log 2 + c * Real.log c - c * Real.log (c + uC a c) + uC a c
    - c :=
    rfl
  rw [this]
  have hu := continuous_uC a
  exact ((((continuous_id.mul continuous_const).add Real.continuous_mul_log).sub
    (continuous_id.mul ((continuous_id.add hu).log hcu))).add hu).sub continuous_id

theorem tendsto_PhiJ (ha : 0 < a) : Tendsto (PhiJ a) atTop (𝓝 0) := by
  have hsub := tendsto_uC_sub ha
  have hmain : Tendsto (fun c => c * Real.log (2 * c / (c + uC a c))) atTop (𝓝 0) := by
    have hlow : Tendsto (fun c => -(uC a c - c) / 2) atTop (𝓝 0) := by
      simpa using hsub.neg.div_const 2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with c hc
      have hu := uC_pos ha c
      have hv : 0 < 2 * c / (c + uC a c) := by positivity
      have := Real.one_sub_inv_le_log_of_pos hv
      have e : 1 - (2 * c / (c + uC a c))⁻¹ = -(uC a c - c) / (2 * c) := by field_simp; ring
      rw [e] at this
      calc -(uC a c - c) / 2 = c * (-(uC a c - c) / (2 * c)) := by field_simp
        _ ≤ c * Real.log (2 * c / (c + uC a c)) := mul_le_mul_of_nonneg_left this hc.le
    · filter_upwards [eventually_gt_atTop 0] with c hc
      have hu := uC_pos ha c
      have hlt := c_lt_uC ha hc.le
      have : Real.log (2 * c / (c + uC a c)) ≤ 0 :=
        Real.log_nonpos (by positivity) ((div_le_one (by positivity)).mpr (by linarith))
      exact mul_nonpos_of_nonneg_of_nonpos hc.le this
  have := hmain.add hsub
  simp only [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  have hu := uC_pos ha c
  unfold PhiJ
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) hc.ne']
  ring

/-- `∫ g kC dc = ellA a + 2 log(a/2)(massA a − 1)`. -/
theorem integral_gtil_kC (ha : 0 < a) :
    IntegrableOn (fun c => gtil c * kC a c) (Ioi 0) ∧
      ∫ c in Ioi (0:ℝ), gtil c * kC a c = ellA a + 2 * Real.log (a / 2) * (massA a - 1) := by
  have hderiv : ∀ c ∈ Ioi (0:ℝ), HasDerivAt (PhiJ a) (Real.log (2 * c / (uC a c + c))) c :=
    fun c hc => hasDerivAt_PhiJ ha hc
  have hcont : ContinuousWithinAt (PhiJ a) (Ici 0) 0 :=
    (continuous_PhiJ ha).continuousAt.continuousWithinAt
  have hnp : ∀ c ∈ Ioi (0:ℝ), 0 ≤ -Real.log (2 * c / (uC a c + c)) := by
    intro c hc
    have hc := mem_Ioi.mp hc
    have hu := uC_pos ha c
    have hlt := c_lt_uC ha hc.le
    have : Real.log (2 * c / (uC a c + c)) ≤ 0 :=
      Real.log_nonpos (by positivity) ((div_le_one (by positivity)).mpr (by linarith))
    linarith
  have hlimneg : Tendsto (fun c => -PhiJ a c) atTop (𝓝 0) := by
    simpa using (tendsto_PhiJ ha).neg
  have hintneg := integrableOn_Ioi_deriv_of_nonneg (g := fun c => -PhiJ a c) hcont.neg
    (fun c hc => (hderiv c hc).neg) hnp hlimneg
  have hint : IntegrableOn (fun c => Real.log (2 * c / (uC a c + c))) (Ioi 0) := by
    simpa using hintneg.neg
  obtain ⟨h1, h2⟩ := integral_gtil hcont hderiv hint (tendsto_PhiJ ha)
  obtain ⟨m1, m2⟩ := integral_gtil_mass ha
  have hpt : ∀ c ∈ Ioi (0:ℝ), gtil c * kC a c =
      gtil c * Real.log (2 * c / (uC a c + c)) + 2 * Real.log (a / 2) * (gtil c * ((1 - c / uC a
        c) / 2)) := by
    intro c hc
    have hc := mem_Ioi.mp hc
    have hu := uC_pos ha c
    unfold kC
    rw [show a * c / (uC a c + c) = (a / 2) * (2 * c / (uC a c + c)) by field_simp,
      Real.log_mul (by positivity) (by positivity)]
    field_simp
    ring
  have hint2 : IntegrableOn (fun c => gtil c * Real.log (2 * c / (uC a c + c)) +
      2 * Real.log (a / 2) * (gtil c * ((1 - c / uC a c) / 2))) (Ioi 0) := h1.add (m1.const_mul _)
  refine ⟨hint2.congr_fun (fun c hc => (hpt c hc).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add h1 (m1.const_mul _),
    integral_const_mul,
    h2, m2, PhiJ_eq_neg_Jfun ha le_rfl, PhiJ_eq_neg_Jfun ha zero_le_one,
    PhiJ_eq_neg_Jfun ha (by norm_num : (0:ℝ) ≤ 5)]
  unfold ellA
  ring

end ell

end
end Zeta32.Analytic.EnergyI

end

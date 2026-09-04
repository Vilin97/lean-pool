/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.SteinIdentity

/-!
# Test functions for the exponential transfer identity

This file formalizes the two test functions used in the exponential transfer
identity.  They are written with `max` and `min`; for positive `c,d` this is
equivalent to the corresponding indicator notation and makes global
continuity transparent.
-/

open Real Set Filter Topology MeasureTheory

namespace Feige

namespace TransferTestFunctions

/-- `φ(x) = (1 - exp (-x/d)) 1_{x ≥ 0}` for `d > 0`. -/
noncomputable def transferPhi (d x : ℝ) : ℝ :=
  max 0 (1 - exp (-x / d))

/-- `ψ(x) = 1_{x ≥ 0} + exp (x/c) 1_{x < 0}` for `c > 0`. -/
noncomputable def transferPsi (c x : ℝ) : ℝ :=
  min 1 (exp (x / c))

theorem transferPhi_of_nonneg {d x : ℝ} (hd : 0 < d) (hx : 0 ≤ x) :
    transferPhi d x = 1 - exp (-x / d) := by
  rw [transferPhi, max_eq_right]
  exact sub_nonneg.mpr (exp_le_one_iff.mpr (by
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx) hd.le))

theorem transferPhi_of_nonpos {d x : ℝ} (hd : 0 < d) (hx : x ≤ 0) :
    transferPhi d x = 0 := by
  rw [transferPhi, max_eq_left]
  exact sub_nonpos.mpr (one_le_exp_iff.mpr (by
    exact div_nonneg (neg_nonneg.mpr hx) hd.le))

theorem transferPsi_of_nonneg {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    transferPsi c x = 1 := by
  rw [transferPsi, min_eq_left]
  exact one_le_exp_iff.mpr (div_nonneg hx hc.le)

theorem transferPsi_of_nonpos {c x : ℝ} (hc : 0 < c) (hx : x ≤ 0) :
    transferPsi c x = exp (x / c) := by
  rw [transferPsi, min_eq_right]
  exact exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg hx hc.le)

/-- `φ` is continuous, including at its joining point zero. -/
theorem continuous_transferPhi (d : ℝ) : Continuous (transferPhi d) := by
  unfold transferPhi
  fun_prop

/-- `ψ` is continuous, including at its joining point zero. -/
theorem continuous_transferPsi (c : ℝ) : Continuous (transferPsi c) := by
  unfold transferPsi
  fun_prop

theorem transferPhi_nonneg (d x : ℝ) : 0 ≤ transferPhi d x :=
  le_max_left _ _

theorem transferPhi_le_one {d x : ℝ} (hd : 0 < d) :
    transferPhi d x ≤ 1 := by
  by_cases hx : 0 ≤ x
  · rw [transferPhi_of_nonneg hd hx]
    linarith [exp_pos (-x / d)]
  · rw [transferPhi_of_nonpos hd (le_of_not_ge hx)]
    norm_num

theorem transferPsi_nonneg (c x : ℝ) : 0 ≤ transferPsi c x := by
  exact le_min zero_le_one (exp_pos _).le

theorem transferPsi_le_one (c x : ℝ) : transferPsi c x ≤ 1 :=
  min_le_left _ _

theorem norm_transferPhi_le_one {d : ℝ} (hd : 0 < d) (x : ℝ) :
    ‖transferPhi d x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (transferPhi_nonneg d x)]
  exact transferPhi_le_one hd

theorem norm_transferPsi_le_one (c x : ℝ) :
    ‖transferPsi c x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (transferPsi_nonneg c x)]
  exact transferPsi_le_one c x

/-- Exponential-weight integrability required by the Stein identity. -/
theorem integrableOn_transferPhi_affine_mul_exp
    {d : ℝ} (hd : 0 < d) (y a : ℝ) :
    IntegrableOn
      (fun e : ℝ => transferPhi d (y + a * e) * exp (-e)) (Ioi 0) :=
  Feige.ExponentialStein.integrableOn_comp_mul_exp
    (continuous_transferPhi d) (norm_transferPhi_le_one hd) y a

theorem integrableOn_transferPsi_affine_mul_exp
    (c y a : ℝ) :
    IntegrableOn
      (fun e : ℝ => transferPsi c (y + a * e) * exp (-e)) (Ioi 0) :=
  Feige.ExponentialStein.integrableOn_comp_mul_exp
    (continuous_transferPsi c) (norm_transferPsi_le_one c) y a

/-- Exponential damping supplies the boundary term at infinity. -/
theorem tendsto_transferPhi_affine_mul_exp_atTop
    {d : ℝ} (hd : 0 < d) (y a : ℝ) :
    Tendsto (fun e : ℝ => transferPhi d (y + a * e) * exp (-e))
      atTop (𝓝 0) :=
  Feige.ExponentialStein.tendsto_comp_mul_exp_atTop
    (norm_transferPhi_le_one hd) y a

theorem tendsto_transferPsi_affine_mul_exp_atTop
    (c y a : ℝ) :
    Tendsto (fun e : ℝ => transferPsi c (y + a * e) * exp (-e))
      atTop (𝓝 0) :=
  Feige.ExponentialStein.tendsto_comp_mul_exp_atTop
    (norm_transferPsi_le_one c) y a

/-- Derivative of `φ` on the positive half-line. -/
theorem hasDerivAt_transferPhi_of_pos
    {d x : ℝ} (hd : 0 < d) (hx : 0 < x) :
    HasDerivAt (transferPhi d) (exp (-x / d) / d) x := by
  have hloc : ∀ᶠ z in 𝓝 x, 0 ≤ z := eventually_ge_nhds hx
  apply HasDerivAt.congr_of_eventuallyEq
    (show HasDerivAt (fun z : ℝ => 1 - exp (-z / d))
        (exp (-x / d) / d) x by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using
        ((((hasDerivAt_id x).div_const d).neg).exp.const_sub (1 : ℝ)))
  filter_upwards [hloc] with z hz
  exact transferPhi_of_nonneg hd hz

/-- Derivative of `φ` on the negative half-line. -/
theorem hasDerivAt_transferPhi_of_neg
    {d x : ℝ} (hd : 0 < d) (hx : x < 0) :
    HasDerivAt (transferPhi d) 0 x := by
  apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const x 0)
  filter_upwards [eventually_le_nhds hx] with z hz
  exact transferPhi_of_nonpos hd hz

/-- Derivative of `ψ` on the positive half-line. -/
theorem hasDerivAt_transferPsi_of_pos
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    HasDerivAt (transferPsi c) 0 x := by
  apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const x 1)
  filter_upwards [eventually_ge_nhds hx] with z hz
  exact transferPsi_of_nonneg hc hz

/-- Derivative of `ψ` on the negative half-line. -/
theorem hasDerivAt_transferPsi_of_neg
    {c x : ℝ} (hc : 0 < c) (hx : x < 0) :
    HasDerivAt (transferPsi c) (exp (x / c) / c) x := by
  have hloc : ∀ᶠ z in 𝓝 x, z ≤ 0 := eventually_le_nhds hx
  apply HasDerivAt.congr_of_eventuallyEq
    (show HasDerivAt (fun z : ℝ => exp (z / c))
        (exp (x / c) / c) x by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using
        (((hasDerivAt_id x).div_const c).exp))
  filter_upwards [hloc] with z hz
  exact transferPsi_of_nonpos hc hz

/-- Away from zero, `φ'` has the piecewise formula used by the transfer
identity. -/
theorem hasDerivAt_transferPhi_of_ne_zero
    {d x : ℝ} (hd : 0 < d) (hx : x ≠ 0) :
    HasDerivAt (transferPhi d)
      (if 0 < x then exp (-x / d) / d else 0) x := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · rw [ite_eq_right (not_lt_of_ge hxneg.le)]
    exact hasDerivAt_transferPhi_of_neg hd hxneg
  · rw [ite_eq_left hxpos]
    exact hasDerivAt_transferPhi_of_pos hd hxpos

/-- Away from zero, `ψ'` has the piecewise formula used by the transfer
identity. -/
theorem hasDerivAt_transferPsi_of_ne_zero
    {c x : ℝ} (hc : 0 < c) (hx : x ≠ 0) :
    HasDerivAt (transferPsi c)
      (if x < 0 then exp (x / c) / c else 0) x := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · rw [ite_eq_left hxneg]
    exact hasDerivAt_transferPsi_of_neg hc hxneg
  · rw [ite_eq_right (not_lt_of_ge hxpos.le)]
    exact hasDerivAt_transferPsi_of_pos hc hxpos

/-- The a.e. derivative used when applying Stein's identity to `φ`. -/
noncomputable def transferPhiDeriv (d x : ℝ) : ℝ :=
  if 0 < x then exp (-x / d) / d else 0

/-- The a.e. derivative used when applying Stein's identity to `ψ`. -/
noncomputable def transferPsiDeriv (c x : ℝ) : ℝ :=
  if x < 0 then exp (x / c) / c else 0

theorem measurable_transferPhiDeriv (d : ℝ) :
    Measurable (transferPhiDeriv d) := by
  unfold transferPhiDeriv
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (by fun_prop) measurable_const

theorem measurable_transferPsiDeriv (c : ℝ) :
    Measurable (transferPsiDeriv c) := by
  unfold transferPsiDeriv
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    (by fun_prop) measurable_const

theorem norm_transferPhiDeriv_le {d : ℝ} (hd : 0 < d) (x : ℝ) :
    ‖transferPhiDeriv d x‖ ≤ 1 / d := by
  unfold transferPhiDeriv
  split_ifs with hx
  · rw [Real.norm_eq_abs, abs_of_pos (div_pos (exp_pos _) hd)]
    exact div_le_div_of_nonneg_right
      (exp_le_one_iff.mpr (by
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx.le) hd.le))
      hd.le
  · simp [hd.le]

theorem norm_transferPsiDeriv_le {c : ℝ} (hc : 0 < c) (x : ℝ) :
    ‖transferPsiDeriv c x‖ ≤ 1 / c := by
  unfold transferPsiDeriv
  split_ifs with hx
  · rw [Real.norm_eq_abs, abs_of_pos (div_pos (exp_pos _) hc)]
    exact div_le_div_of_nonneg_right
      (exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg hx.le hc.le))
      hc.le
  · simp [hc.le]

/-- Weighted integrability of the formal derivative of `φ` along an
affine path. -/
theorem integrableOn_transferPhiDeriv_affine_mul_exp
    {d : ℝ} (hd : 0 < d) (y a : ℝ) :
    IntegrableOn
      (fun e : ℝ => a * transferPhiDeriv d (y + a * e) * exp (-e))
      (Ioi 0) := by
  have hdom := (exp_neg_integrableOn_Ioi 0 one_pos).const_mul (|a| / d)
  apply hdom.mono'
  · exact (((measurable_const.mul
      ((measurable_transferPhiDeriv d).comp
        (measurable_const.add (measurable_const.mul measurable_id)))).mul
          (measurable_exp.comp measurable_id.neg)).aestronglyMeasurable)
  · filter_upwards with e
    rw [norm_mul, norm_mul, Real.norm_eq_abs, norm_of_nonneg (exp_pos _).le]
    calc
      |a| * ‖transferPhiDeriv d (y + a * e)‖ * exp (-e) ≤
          |a| * (1 / d) * exp (-e) := by
            gcongr
            exact norm_transferPhiDeriv_le hd _
      _ = |a| / d * exp (-1 * e) := by simp [div_eq_mul_inv]

/-- Weighted integrability of the formal derivative of `ψ`. -/
theorem integrableOn_transferPsiDeriv_affine_mul_exp
    {c : ℝ} (hc : 0 < c) (y a : ℝ) :
    IntegrableOn
      (fun e : ℝ => a * transferPsiDeriv c (y + a * e) * exp (-e))
      (Ioi 0) := by
  have hdom := (exp_neg_integrableOn_Ioi 0 one_pos).const_mul (|a| / c)
  apply hdom.mono'
  · exact (((measurable_const.mul
      ((measurable_transferPsiDeriv c).comp
        (measurable_const.add (measurable_const.mul measurable_id)))).mul
          (measurable_exp.comp measurable_id.neg)).aestronglyMeasurable)
  · filter_upwards with e
    rw [norm_mul, norm_mul, Real.norm_eq_abs, norm_of_nonneg (exp_pos _).le]
    calc
      |a| * ‖transferPsiDeriv c (y + a * e)‖ * exp (-e) ≤
          |a| * (1 / c) * exp (-e) := by
            gcongr
            exact norm_transferPsiDeriv_le hc _
      _ = |a| / c * exp (-1 * e) := by simp [div_eq_mul_inv]

/-- The formal derivative of `φ` is integrable on every finite
interval. -/
theorem intervalIntegrable_transferPhiDeriv_affine
    {d : ℝ} (hd : 0 < d) (y a r s : ℝ) (hrs : r ≤ s) :
    IntervalIntegrable
      (fun e : ℝ => a * transferPhiDeriv d (y + a * e))
      volume r s := by
  rw [intervalIntegrable_iff]
  rw [uIoc_of_le hrs]
  apply volume.integrableOn_of_bounded measure_Ioc_lt_top.ne
    ((measurable_const.mul
      ((measurable_transferPhiDeriv d).comp
        (measurable_const.add
          (measurable_const.mul measurable_id)))).aestronglyMeasurable)
  all_goals
    filter_upwards with e
    calc
      ‖a * transferPhiDeriv d (y + a * e)‖ =
          |a| * ‖transferPhiDeriv d (y + a * e)‖ := by
            rw [norm_mul, Real.norm_eq_abs]
      _ ≤ |a| * (1 / d) :=
        mul_le_mul_of_nonneg_left (norm_transferPhiDeriv_le hd _) (abs_nonneg a)

/-- The formal derivative of `ψ` is integrable on every finite
interval. -/
theorem intervalIntegrable_transferPsiDeriv_affine
    {c : ℝ} (hc : 0 < c) (y a r s : ℝ) (hrs : r ≤ s) :
    IntervalIntegrable
      (fun e : ℝ => a * transferPsiDeriv c (y + a * e))
      volume r s := by
  rw [intervalIntegrable_iff]
  rw [uIoc_of_le hrs]
  apply volume.integrableOn_of_bounded measure_Ioc_lt_top.ne
    ((measurable_const.mul
      ((measurable_transferPsiDeriv c).comp
        (measurable_const.add
          (measurable_const.mul measurable_id)))).aestronglyMeasurable)
  all_goals
    filter_upwards with e
    calc
      ‖a * transferPsiDeriv c (y + a * e)‖ =
          |a| * ‖transferPsiDeriv c (y + a * e)‖ := by
            rw [norm_mul, Real.norm_eq_abs]
      _ ≤ |a| * (1 / c) :=
        mul_le_mul_of_nonneg_left (norm_transferPsiDeriv_le hc _) (abs_nonneg a)

/-- An affine path hits the exceptional point zero only on a null set,
so the composite `φ (y + a e)` has the expected derivative a.e. -/
theorem ae_hasDerivAt_transferPhi_comp_affine
    {d y a : ℝ} (hd : 0 < d) (ha : a ≠ 0) :
    ∀ᵐ e : ℝ,
      HasDerivAt (transferPhi d ∘ fun t : ℝ => y + a * t)
        (a * transferPhiDeriv d (y + a * e)) e := by
  have hnull : volume {e : ℝ | y + a * e = 0} = 0 := by
    have hset : {e : ℝ | y + a * e = 0} = {-y / a} := by
      ext e
      simp only [mem_ofPred_eq, mem_singleton_iff]
      constructor <;> intro h
      · apply (eq_div_iff ha).2
        linarith
      · rw [h]
        field_simp
        ring
    rw [hset]
    simp
  have hae : ∀ᵐ e : ℝ, y + a * e ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  filter_upwards [hae] with e he
  have haff : HasDerivAt (fun t : ℝ => y + a * t) a e := by
    simpa using
      ((hasDerivAt_const_mul a :
        HasDerivAt (fun t : ℝ => a * t) a e).const_add y)
  simpa [transferPhiDeriv, mul_comm] using
    (hasDerivAt_transferPhi_of_ne_zero hd he).comp e haff

/-- The analogous a.e. composite derivative statement for `ψ`. -/
theorem ae_hasDerivAt_transferPsi_comp_affine
    {c y a : ℝ} (hc : 0 < c) (ha : a ≠ 0) :
    ∀ᵐ e : ℝ,
      HasDerivAt (transferPsi c ∘ fun t : ℝ => y + a * t)
        (a * transferPsiDeriv c (y + a * e)) e := by
  have hnull : volume {e : ℝ | y + a * e = 0} = 0 := by
    have hset : {e : ℝ | y + a * e = 0} = {-y / a} := by
      ext e
      simp only [mem_ofPred_eq, mem_singleton_iff]
      constructor <;> intro h
      · apply (eq_div_iff ha).2
        linarith
      · rw [h]
        field_simp
        ring
    rw [hset]
    simp
  have hae : ∀ᵐ e : ℝ, y + a * e ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  filter_upwards [hae] with e he
  have haff : HasDerivAt (fun t : ℝ => y + a * t) a e := by
    simpa using
      ((hasDerivAt_const_mul a :
        HasDerivAt (fun t : ℝ => a * t) a e).const_add y)
  simpa [transferPsiDeriv, mul_comm] using
    (hasDerivAt_transferPsi_of_ne_zero hc he).comp e haff

/-- Fixed-`y`, positive-scale one-sided Stein identity for the first test
function.  The proof splits according to whether the unique affine kink
`-y/a` lies in the positive half-line. -/
theorem transferPhi_stein_fixed
    {d y a : ℝ} (hd : 0 < d) (ha : a ≠ 0) :
    (∫ e : ℝ in Ioi 0, transferPhi d (y + a * e) * exp (-e)) -
        transferPhi d y =
      ∫ e : ℝ in Ioi 0,
        a * transferPhiDeriv d (y + a * e) * exp (-e) := by
  let u : ℝ → ℝ := transferPhi d ∘ fun e => y + a * e
  let du : ℝ → ℝ := fun e => a * transferPhiDeriv d (y + a * e)
  let v : ℝ → ℝ := fun e => exp (-e)
  let dv : ℝ → ℝ := fun e => -exp (-e)
  have hucont : Continuous u := by
    exact (continuous_transferPhi d).comp
      (continuous_const.add (continuous_const.mul continuous_id))
  have hvcont : Continuous v := by
    exact continuous_exp.comp continuous_id.neg
  have hvderiv : ∀ e, 0 < e → HasDerivAt v (dv e) e := by
    intro e _
    simpa [v, dv] using ((hasDerivAt_id e).neg.exp)
  have hu_deriv : ∀ e, 0 < e → y + a * e ≠ 0 →
      HasDerivAt u (du e) e := by
    intro e _ he
    have haff : HasDerivAt (fun t : ℝ => y + a * t) a e := by
      simpa using
        ((hasDerivAt_const_mul a :
          HasDerivAt (fun t : ℝ => a * t) a e).const_add y)
    simpa [u, du, transferPhiDeriv, mul_comm] using
      (hasDerivAt_transferPhi_of_ne_zero hd he).comp e haff
  have hu_int := integrableOn_transferPhi_affine_mul_exp hd y a
  have hdu_int := integrableOn_transferPhiDeriv_affine_mul_exp hd y a
  have huvNeg_int : IntegrableOn (u * dv) (Ioi (0 : ℝ)) := by
    rw [show u * dv =
      fun e => -(transferPhi d (y + a * e) * exp (-e)) by
        funext e
        simp [u, dv]]
    exact hu_int.neg
  have hduv_int : IntegrableOn (du * v) (Ioi (0 : ℝ)) := by
    rw [show du * v =
      fun e => a * transferPhiDeriv d (y + a * e) * exp (-e) by
        funext e
        rfl]
    exact hdu_int
  have htop : Tendsto (u * v) atTop (𝓝 (0 : ℝ)) := by
    rw [show u * v =
      fun e => transferPhi d (y + a * e) * exp (-e) by
        funext e
        rfl]
    exact tendsto_transferPhi_affine_mul_exp_atTop hd y a
  by_cases hk : 0 < -y / a
  · have huk : ∀ e, 0 < e → e ≠ -y / a → HasDerivAt u (du e) e := by
      intro e he hne
      apply hu_deriv e he
      intro hzero
      apply hne
      apply (eq_div_iff ha).2
      linarith
    have huFin : IntervalIntegrable du volume 0 (-y / a) := by
      exact intervalIntegrable_transferPhiDeriv_affine hd y a 0 (-y / a) hk.le
    have hvFin : IntervalIntegrable dv volume 0 (-y / a) := by
      have hdv : Continuous dv := by
        simp only [dv]
        fun_prop
      exact hdv.intervalIntegrable 0 (-y / a)
    have hip := Feige.ExponentialStein.integral_Ioi_mul_deriv_one_kink
      (u := u) (v := v) (u' := du) (v' := dv)
      (k := -y / a) (a' := transferPhi d y) (b' := 0)
      hk hucont hvcont huk hvderiv huFin hvFin
      huvNeg_int hduv_int (by simp [u, v]) htop
    dsimp [u, du, v, dv] at hip
    simp_rw [mul_neg] at hip
    rw [integral_neg] at hip
    linear_combination -hip
  · have huall : ∀ e ∈ Ioi (0 : ℝ), HasDerivAt u (du e) e := by
      intro e he
      apply hu_deriv e he
      intro hzero
      apply hk
      rw [show -y / a = e by
        apply (div_eq_iff ha).2
        linarith]
      exact he
    have hzero : Tendsto (u * v) (𝓝[>] (0 : ℝ))
        (𝓝 (transferPhi d y)) := by
      have hc : Tendsto (u * v) (𝓝 (0 : ℝ)) (𝓝 ((u * v) 0)) :=
        (hucont.mul hvcont).continuousAt
      have hc' : Tendsto (u * v) (𝓝[>] (0 : ℝ)) (𝓝 ((u * v) 0)) :=
        hc.mono_left inf_le_left
      rw [show (u * v) 0 = transferPhi d y by simp [u, v]] at hc'
      exact hc'
    have hip := integral_Ioi_mul_deriv_eq_deriv_mul
      (a := 0) (a' := transferPhi d y) (b' := 0)
      huall hvderiv huvNeg_int hduv_int hzero htop
    dsimp [u, du, v, dv] at hip
    simp_rw [mul_neg] at hip
    rw [integral_neg] at hip
    linear_combination -hip

/-- Fixed-`y`, positive-scale one-sided Stein identity for `ψ`. -/
theorem transferPsi_stein_fixed
    {c y a : ℝ} (hc : 0 < c) (ha : a ≠ 0) :
    (∫ e : ℝ in Ioi 0, transferPsi c (y + a * e) * exp (-e)) -
        transferPsi c y =
      ∫ e : ℝ in Ioi 0,
        a * transferPsiDeriv c (y + a * e) * exp (-e) := by
  let u : ℝ → ℝ := transferPsi c ∘ fun e => y + a * e
  let du : ℝ → ℝ := fun e => a * transferPsiDeriv c (y + a * e)
  let v : ℝ → ℝ := fun e => exp (-e)
  let dv : ℝ → ℝ := fun e => -exp (-e)
  have hucont : Continuous u := by
    exact (continuous_transferPsi c).comp
      (continuous_const.add (continuous_const.mul continuous_id))
  have hvcont : Continuous v := by
    exact continuous_exp.comp continuous_id.neg
  have hvderiv : ∀ e, 0 < e → HasDerivAt v (dv e) e := by
    intro e _
    simpa [v, dv] using ((hasDerivAt_id e).neg.exp)
  have hu_deriv : ∀ e, 0 < e → y + a * e ≠ 0 →
      HasDerivAt u (du e) e := by
    intro e _ he
    have haff : HasDerivAt (fun t : ℝ => y + a * t) a e := by
      simpa using
        ((hasDerivAt_const_mul a :
          HasDerivAt (fun t : ℝ => a * t) a e).const_add y)
    simpa [u, du, transferPsiDeriv, mul_comm] using
      (hasDerivAt_transferPsi_of_ne_zero hc he).comp e haff
  have hu_int := integrableOn_transferPsi_affine_mul_exp c y a
  have hdu_int := integrableOn_transferPsiDeriv_affine_mul_exp hc y a
  have huvNeg_int : IntegrableOn (u * dv) (Ioi (0 : ℝ)) := by
    rw [show u * dv =
      fun e => -(transferPsi c (y + a * e) * exp (-e)) by
        funext e
        simp [u, dv]]
    exact hu_int.neg
  have hduv_int : IntegrableOn (du * v) (Ioi (0 : ℝ)) := by
    rw [show du * v =
      fun e => a * transferPsiDeriv c (y + a * e) * exp (-e) by
        funext e
        rfl]
    exact hdu_int
  have htop : Tendsto (u * v) atTop (𝓝 (0 : ℝ)) := by
    rw [show u * v =
      fun e => transferPsi c (y + a * e) * exp (-e) by
        funext e
        rfl]
    exact tendsto_transferPsi_affine_mul_exp_atTop c y a
  by_cases hk : 0 < -y / a
  · have huk : ∀ e, 0 < e → e ≠ -y / a → HasDerivAt u (du e) e := by
      intro e he hne
      apply hu_deriv e he
      intro hzero
      apply hne
      apply (eq_div_iff ha).2
      linarith
    have huFin : IntervalIntegrable du volume 0 (-y / a) :=
      intervalIntegrable_transferPsiDeriv_affine hc y a 0 (-y / a) hk.le
    have hvFin : IntervalIntegrable dv volume 0 (-y / a) := by
      have hdv : Continuous dv := by
        simp only [dv]
        fun_prop
      exact hdv.intervalIntegrable 0 (-y / a)
    have hip := Feige.ExponentialStein.integral_Ioi_mul_deriv_one_kink
      (u := u) (v := v) (u' := du) (v' := dv)
      (k := -y / a) (a' := transferPsi c y) (b' := 0)
      hk hucont hvcont huk hvderiv huFin hvFin
      huvNeg_int hduv_int (by simp [u, v]) htop
    dsimp [u, du, v, dv] at hip
    simp_rw [mul_neg] at hip
    rw [integral_neg] at hip
    linear_combination -hip
  · have huall : ∀ e ∈ Ioi (0 : ℝ), HasDerivAt u (du e) e := by
      intro e he
      apply hu_deriv e he
      intro hzero
      apply hk
      rw [show -y / a = e by
        apply (div_eq_iff ha).2
        linarith]
      exact he
    have hzero : Tendsto (u * v) (𝓝[>] (0 : ℝ))
        (𝓝 (transferPsi c y)) := by
      have hz : Tendsto (u * v) (𝓝 (0 : ℝ)) (𝓝 ((u * v) 0)) :=
        (hucont.mul hvcont).continuousAt
      have hz' : Tendsto (u * v) (𝓝[>] (0 : ℝ)) (𝓝 ((u * v) 0)) :=
        hz.mono_left inf_le_left
      rw [show (u * v) 0 = transferPsi c y by simp [u, v]] at hz'
      exact hz'
    have hip := integral_Ioi_mul_deriv_eq_deriv_mul
      (a := 0) (a' := transferPsi c y) (b' := 0)
      huall hvderiv huvNeg_int hduv_int hzero htop
    dsimp [u, du, v, dv] at hip
    simp_rw [mul_neg] at hip
    rw [integral_neg] at hip
    linear_combination -hip

/-- Negative-affine fixed-`y` Stein identity for `φ`. -/
theorem transferPhi_stein_fixed_sub
    {d y b : ℝ} (hd : 0 < d) (hb : 0 < b) :
    transferPhi d y -
        (∫ e : ℝ in Ioi 0, transferPhi d (y - b * e) * exp (-e)) =
      ∫ e : ℝ in Ioi 0,
        b * transferPhiDeriv d (y - b * e) * exp (-e) := by
  have h := transferPhi_stein_fixed (y := y) (a := -b) hd (neg_ne_zero.mpr hb.ne')
  have hn := congrArg Neg.neg h
  simpa [sub_eq_add_neg, neg_mul, ← integral_neg, mul_assoc] using hn

/-- Negative-affine fixed-`y` Stein identity for `ψ`. -/
theorem transferPsi_stein_fixed_sub
    {c y b : ℝ} (hc : 0 < c) (hb : 0 < b) :
    transferPsi c y -
        (∫ e : ℝ in Ioi 0, transferPsi c (y - b * e) * exp (-e)) =
      ∫ e : ℝ in Ioi 0,
        b * transferPsiDeriv c (y - b * e) * exp (-e) := by
  have h := transferPsi_stein_fixed (y := y) (a := -b) hc (neg_ne_zero.mpr hb.ne')
  have hn := congrArg Neg.neg h
  simpa [sub_eq_add_neg, neg_mul, ← integral_neg, mul_assoc] using hn

/-- Fixed-`y` two-sided exponential Stein identity for `φ`. -/
theorem transferPhi_stein_fixed_two_sided
    {d y a b : ℝ} (hd : 0 < d) (ha : 0 < a) (hb : 0 < b) :
    (∫ e : ℝ in Ioi 0, transferPhi d (y + a * e) * exp (-e)) -
        (∫ e : ℝ in Ioi 0, transferPhi d (y - b * e) * exp (-e)) =
      (∫ e : ℝ in Ioi 0,
        a * transferPhiDeriv d (y + a * e) * exp (-e)) +
      (∫ e : ℝ in Ioi 0,
        b * transferPhiDeriv d (y - b * e) * exp (-e)) := by
  have hp := transferPhi_stein_fixed (y := y) (a := a) hd ha.ne'
  have hm := transferPhi_stein_fixed_sub (y := y) hd hb
  linear_combination hp + hm

/-- Fixed-`y` two-sided exponential Stein identity for `ψ`. -/
theorem transferPsi_stein_fixed_two_sided
    {c y a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) :
    (∫ e : ℝ in Ioi 0, transferPsi c (y + a * e) * exp (-e)) -
        (∫ e : ℝ in Ioi 0, transferPsi c (y - b * e) * exp (-e)) =
      (∫ e : ℝ in Ioi 0,
        a * transferPsiDeriv c (y + a * e) * exp (-e)) +
      (∫ e : ℝ in Ioi 0,
        b * transferPsiDeriv c (y - b * e) * exp (-e)) := by
  have hp := transferPsi_stein_fixed (y := y) (a := a) hc ha.ne'
  have hm := transferPsi_stein_fixed_sub (y := y) hc hb
  linear_combination hp + hm

end TransferTestFunctions

end Feige

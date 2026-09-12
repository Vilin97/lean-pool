/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The radial heat continuation profile

The profile is defined by the actual gamma-normalized improper integral in
Lemma 4.4. Its derivative kernels have gamma-integrable bounds on the whole
closed half-line of nonnegative profile arguments.
-/

@[expose] public section


noncomputable section

open Filter Set MeasureTheory
open scoped Topology ContDiff

namespace NavierStokes.RadialHeatProfile

/-- The unsigned kernel for the `n`-th derivative. -/
def kernel (a : ℝ) (n : ℕ) (z v : ℝ) : ℝ :=
  Real.exp (-v) * v ^ (a + (n : ℝ) - 1) * (1 + z * v) ^ (1 - a - (n : ℝ))

/-- Moment, given by `∫ v in Ioi (0 : ℝ), kernel a n z v`. -/
def moment (a : ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  ∫ v in Ioi (0 : ℝ), kernel a n z v

/-- The manuscript's normalized radial heat profile, with `a = 1 + h`. -/
def profile (a z : ℝ) : ℝ := (Real.Gamma a)⁻¹ * moment a 0 z

theorem base_one_le {z v : ℝ} (hz : 0 ≤ z) (hv : 0 ≤ v) : 1 ≤ 1 + z * v :=
  le_add_of_nonneg_right (mul_nonneg hz hv)

theorem base_pos {z v : ℝ} (hz : 0 ≤ z) (hv : 0 ≤ v) : 0 < 1 + z * v :=
  lt_of_lt_of_le zero_lt_one (base_one_le hz hv)

theorem kernel_pos (a : ℝ) (n : ℕ) {z v : ℝ} (hz : 0 ≤ z) (hv : 0 < v) :
    0 < kernel a n z v :=
  mul_pos (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hv _))
    (Real.rpow_pos_of_pos (base_pos hz hv.le) _)

theorem kernel_le_gamma {a : ℝ} (ha : 1 < a) (n : ℕ) {z v : ℝ}
    (hz : 0 ≤ z) (hv : 0 < v) :
    kernel a n z v ≤ Real.exp (-v) * v ^ (a + (n : ℝ) - 1) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hp : (1 + z * v) ^ (1 - a - (n : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (base_one_le hz hv.le) (by linarith)
  exact (mul_le_mul_of_nonneg_left hp
    (mul_nonneg (Real.exp_pos _).le (Real.rpow_pos_of_pos hv _).le)).trans_eq (mul_one _)

theorem kernel_norm_le_gamma {a : ℝ} (ha : 1 < a) (n : ℕ) {z v : ℝ}
    (hz : 0 ≤ z) (hv : 0 < v) :
    ‖kernel a n z v‖ ≤ Real.exp (-v) * v ^ (a + (n : ℝ) - 1) := by
  rw [Real.norm_eq_abs, abs_of_pos (kernel_pos a n hz hv)]
  exact kernel_le_gamma ha n hz hv

theorem kernel_continuousOn_v (a : ℝ) (n : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    ContinuousOn (kernel a n z) (Ioi 0) := by
  intro v hv
  have hp : ContinuousAt (fun v : ℝ => v ^ (a + (n : ℝ) - 1)) v :=
    continuousAt_id.rpow_const (Or.inl (show 0 < v from hv).ne')
  have hb : ContinuousAt (fun v : ℝ => (1 + z * v) ^ (1 - a - (n : ℝ))) v :=
    (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).rpow_const
      (Or.inl (base_pos hz (show 0 < v from hv).le).ne')
  have he : ContinuousAt (fun v : ℝ => Real.exp (-v)) v :=
    (Real.continuous_exp.comp continuous_neg).continuousAt
  exact ((he.fun_mul hp).fun_mul hb).continuousWithinAt

theorem kernel_integrable {a : ℝ} (ha : 1 < a) (n : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    IntegrableOn (kernel a n z) (Ioi 0) := by
  have hga : 0 < a + (n : ℝ) := by positivity
  apply (Real.GammaIntegral_convergent hga).mono'
    ((kernel_continuousOn_v a n hz).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact kernel_norm_le_gamma ha n hz hv

theorem kernel_hasDerivAt_z (a : ℝ) (n : ℕ) {z v : ℝ} (hz : 0 ≤ z) (hv : 0 < v) :
    HasDerivAt (fun z => kernel a n z v)
      ((1 - a - (n : ℝ)) * kernel a (n + 1) z v) z := by
  have hd := (((hasDerivAt_id z).mul_const v).const_add 1).rpow_const
    (p := 1 - a - (n : ℝ)) (Or.inl (base_pos hz hv.le).ne')
  have hvpow : v ^ (a + ((n + 1 : ℕ) : ℝ) - 1) =
      v ^ (a + (n : ℝ) - 1) * v := by
    rw [show a + ((n + 1 : ℕ) : ℝ) - 1 = (a + (n : ℝ) - 1) + 1 by push_cast; ring,
      Real.rpow_add_one hv.ne']
  convert! hd.const_mul (Real.exp (-v) * v ^ (a + (n : ℝ) - 1)) using 1
  dsimp [kernel]
  rw [hvpow]
  have he : 1 - a - ((n + 1 : ℕ) : ℝ) = (1 - a - (n : ℝ)) - 1 := by push_cast; ring
  rw [he]
  ring

theorem moment_pos {a : ℝ} (ha : 1 < a) (n : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    0 < moment a n z := by
  have hs : Function.support (kernel a n z) ∩ Ioi 0 = Ioi 0 := by
    rw [inter_eq_right]
    intro v hv
    exact (kernel_pos a n hz hv).ne'
  unfold moment
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · rw [hs, Real.volume_Ioi, ← ENNReal.ofReal_zero]
    exact ENNReal.ofReal_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact (kernel_pos a n hz hv).le
  · exact kernel_integrable ha n hz

theorem moment_le_gamma {a : ℝ} (ha : 1 < a) (n : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    moment a n z ≤ Real.Gamma (a + (n : ℝ)) := by
  have hga : 0 < a + (n : ℝ) := by positivity
  rw [Real.Gamma_eq_integral hga]
  apply integral_mono_ae (kernel_integrable ha n hz) (Real.GammaIntegral_convergent hga)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact kernel_le_gamma ha n hz hv

theorem moment_zero {a : ℝ} (ha : 1 < a) (n : ℕ) :
    moment a n 0 = Real.Gamma (a + (n : ℝ)) := by
  have hga : 0 < a + (n : ℝ) := by positivity
  simp only [moment, kernel, zero_mul, add_zero, Real.one_rpow, mul_one]
  exact (Real.Gamma_eq_integral hga).symm

theorem profile_pos {a z : ℝ} (ha : 1 < a) (hz : 0 ≤ z) : 0 < profile a z :=
  mul_pos (inv_pos.mpr (Real.Gamma_pos_of_pos (zero_lt_one.trans ha))) (moment_pos ha 0 hz)

theorem profile_zero {a : ℝ} (ha : 1 < a) : profile a 0 = 1 := by
  rw [profile, moment_zero ha]
  simp [(Real.Gamma_pos_of_pos (zero_lt_one.trans ha)).ne']

theorem profile_le_one {a z : ℝ} (ha : 1 < a) (hz : 0 ≤ z) : profile a z ≤ 1 := by
  have h := mul_le_mul_of_nonneg_left (moment_le_gamma ha 0 hz)
    (inv_pos.mpr (Real.Gamma_pos_of_pos (zero_lt_one.trans ha))).le
  simpa [profile, (Real.Gamma_pos_of_pos (zero_lt_one.trans ha)).ne'] using h

/-- Continuity includes the endpoint, by a bound independent of `z ≥ 0`. -/
theorem moment_continuousOn {a : ℝ} (ha : 1 < a) (n : ℕ) :
    ContinuousOn (moment a n) (Ici 0) := by
  apply continuousOn_of_dominated
    (bound := fun v : ℝ => Real.exp (-v) * v ^ (a + (n : ℝ) - 1))
  · intro z hz
    exact (kernel_continuousOn_v a n hz).aestronglyMeasurable measurableSet_Ioi
  · intro z hz
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact kernel_norm_le_gamma ha n hz hv
  · exact Real.GammaIntegral_convergent (by positivity)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    intro z hz
    exact (kernel_hasDerivAt_z a n hz hv).continuousAt.continuousWithinAt

theorem moment_hasDerivAt {a z : ℝ} (ha : 1 < a) (n : ℕ) (hz : 0 < z) :
    HasDerivAt (moment a n) ((1 - a - (n : ℝ)) * moment a (n + 1) z) z := by
  have hball : ∀ y ∈ Metric.ball z (z / 2), 0 ≤ y := by
    intro y hy
    have hd : |y - z| < z / 2 := by simpa only [Metric.mem_ball, Real.dist_eq] using hy
    have hlow := (abs_lt.mp hd).1
    linarith
  have hga : 0 < a + ((n + 1 : ℕ) : ℝ) := by positivity
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z v => kernel a n z v)
    (F' := fun z v => (1 - a - (n : ℝ)) * kernel a (n + 1) z v)
    (bound := fun v : ℝ => ‖1 - a - (n : ℝ)‖ *
      (Real.exp (-v) * v ^ (a + ((n + 1 : ℕ) : ℝ) - 1)))
    (μ := volume.restrict (Ioi 0)) (Metric.ball_mem_nhds _ (show 0 < z / 2 by linarith))
    (by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      exact (kernel_continuousOn_v a n (show 0 < y from hy).le).aestronglyMeasurable
        measurableSet_Ioi)
    (kernel_integrable ha n hz.le)
    ((kernel_integrable ha (n + 1) hz.le).aestronglyMeasurable.const_mul _)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      intro y hy
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (kernel_norm_le_gamma ha (n + 1) (hball y hy) hv)
        (norm_nonneg _))
    ((Real.GammaIntegral_convergent hga).const_mul _)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      intro y hy
      exact kernel_hasDerivAt_z a n (hball y hy) hv)
  unfold moment
  simpa only [integral_const_mul] using hi.2

/-- The same derivative formula holds from the right at zero. -/
theorem moment_hasDerivWithinAt {a z : ℝ} (ha : 1 < a) (n : ℕ) (hz : 0 ≤ z) :
    HasDerivWithinAt (moment a n) ((1 - a - (n : ℝ)) * moment a (n + 1) z)
      (Ici 0) z := by
  rcases eq_or_lt_of_le hz with rfl | hzpos
  · apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0)
    · intro z hz
      exact (moment_hasDerivAt ha n hz).differentiableAt.differentiableWithinAt
    · exact ((moment_continuousOn ha n) 0 (by simp)).mono Ioi_subset_Ici_self
    · exact self_mem_nhdsWithin
    · have hc : ContinuousWithinAt
          (fun z => (1 - a - (n : ℝ)) * moment a (n + 1) z) (Ioi 0) 0 :=
        ((continuousOn_const.mul (moment_continuousOn ha (n + 1))) 0 (by simp)).mono
          Ioi_subset_Ici_self
      apply hc.congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (moment_hasDerivAt ha n hy).deriv.symm
  · exact (moment_hasDerivAt ha n hzpos).hasDerivWithinAt

/-- Falling coefficients of the genuine derivative kernels. -/
noncomputable def derivativeCoeff (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => derivativeCoeff a n * (1 - a - (n : ℝ))

/-- Profile jet, given by `(Real.Gamma a)⁻¹ * derivativeCoeff a n * moment a n z`. -/
def profileJet (a : ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  (Real.Gamma a)⁻¹ * derivativeCoeff a n * moment a n z

theorem profileJet_hasDerivWithinAt {a z : ℝ} (ha : 1 < a) (n : ℕ) (hz : 0 ≤ z) :
    HasDerivWithinAt (profileJet a n) (profileJet a (n + 1) z) (Ici 0) z := by
  convert! (moment_hasDerivWithinAt ha n hz).const_mul
    ((Real.Gamma a)⁻¹ * derivativeCoeff a n) using 1
  dsimp [profileJet, derivativeCoeff]
  ring

theorem iteratedDerivWithin_profile {a : ℝ} (ha : 1 < a) (n : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    iteratedDerivWithin n (profile a) (Ici 0) z = profileJet a n z := by
  induction n generalizing z with
  | zero => simp [profileJet, derivativeCoeff, profile]
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      exact ((profileJet_hasDerivWithinAt ha n hz).congr_of_mem
        (fun y hy => ih hy) hz).derivWithin ((uniqueDiffOn_Ici 0) z hz)

/-- Genuine `C∞` regularity on the closed half-line, including zero. -/
theorem profile_contDiffOn {a : ℝ} (ha : 1 < a) :
    ContDiffOn ℝ ∞ (profile a) (Ici 0) := by
  apply contDiffOn_of_differentiableOn_deriv
  intro n _ z hz
  exact ((profileJet_hasDerivWithinAt ha n hz).congr_of_mem
    (fun y hy => iteratedDerivWithin_profile ha n hy) hz).differentiableWithinAt

/-- Every fixed derivative has a finite bound uniform on the whole half-line. -/
theorem profile_derivative_bound {a : ℝ} (ha : 1 < a) (n : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |iteratedDerivWithin n (profile a) (Ici 0) z| ≤
      |(Real.Gamma a)⁻¹ * derivativeCoeff a n| * Real.Gamma (a + (n : ℝ)) := by
  rw [iteratedDerivWithin_profile ha n hz, profileJet, abs_mul,
    abs_of_pos (moment_pos ha n hz)]
  exact mul_le_mul_of_nonneg_left (moment_le_gamma ha n hz) (abs_nonneg _)

theorem iteratedDeriv_profile {a z : ℝ} (ha : 1 < a) (n : ℕ) (hz : 0 < z) :
    iteratedDeriv n (profile a) z = profileJet a n z := by
  have hc : ContDiffAt ℝ n (profile a) z :=
    ((profile_contDiffOn ha).contDiffAt (Ici_mem_nhds hz)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have he := iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Ici 0) hc hz.le
  simpa only [iteratedDerivWithin, iteratedDeriv, he] using
    iteratedDerivWithin_profile ha n hz.le

/-! ## The vanishing boundary term and the actual ODE -/

/-- Boundary term, given by `Real.exp (-v) * v ^ a * (1 + z * v) ^ (-a)`. -/
def boundaryTerm (a z v : ℝ) : ℝ :=
  Real.exp (-v) * v ^ a * (1 + z * v) ^ (-a)

theorem rpow_add_two {x : ℝ} (hx : 0 < x) (p : ℝ) :
    x ^ (p + 2) = x ^ p * x ^ (2 : ℕ) := by
  rw [Real.rpow_add hx, Real.rpow_two]

theorem boundaryTerm_hasDerivAt (a : ℝ) {z v : ℝ} (hz : 0 ≤ z) (hv : 0 < v) :
    HasDerivAt (boundaryTerm a z)
      (a * z ^ 2 * kernel a 2 z v - (1 + 2 * a * z) * kernel a 1 z v +
        a * kernel a 0 z v) v := by
  have he : HasDerivAt (fun v : ℝ => Real.exp (-v)) (-Real.exp (-v)) v := by
    simpa only [mul_neg_one] using (hasDerivAt_neg v).exp
  have hp := Real.hasDerivAt_rpow_const (p := a) (Or.inl hv.ne')
  have hb := (((hasDerivAt_id v).const_mul z).const_add 1).rpow_const
    (p := -a) (Or.inl (base_pos hz hv.le).ne')
  have hv1 : v ^ a = v ^ (a - 1) * v := by
    convert! Real.rpow_add_one hv.ne' (a - 1) using 1
    congr 1
    ring
  have hv2 : v ^ (a + 2 - 1) = v ^ (a - 1) * v ^ 2 := by
    convert! rpow_add_two hv (a - 1) using 1
    congr 1
    ring
  have hb1 : (1 + z * v) ^ (-a) = (1 + z * v) ^ (-a - 1) * (1 + z * v) := by
    convert! Real.rpow_add_one (base_pos hz hv.le).ne' (-a - 1) using 1
    congr 1
    ring
  have hb2 : (1 + z * v) ^ (1 - a) = (1 + z * v) ^ (-a - 1) * (1 + z * v) ^ 2 := by
    convert! rpow_add_two (base_pos hz hv.le) (-a - 1) using 1
    congr 1
    ring
  convert! (he.fun_mul hp).fun_mul hb using 1
  dsimp only [kernel, id]
  norm_num only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, add_zero, sub_zero]
  rw [show a + 1 - 1 = a by ring, show 1 - a - 1 = -a by ring,
    show 1 - a - 2 = -a - 1 by ring, hv2, hb2, hv1, hb1]
  ring

theorem boundaryTerm_zero {a : ℝ} (ha : 1 < a) (z : ℝ) : boundaryTerm a z 0 = 0 := by
  simp [boundaryTerm, Real.zero_rpow (ne_of_gt (zero_lt_one.trans ha))]

theorem boundaryTerm_continuous_zero {a : ℝ} (ha : 1 < a) (z : ℝ) :
    ContinuousWithinAt (boundaryTerm a z) (Ici 0) 0 := by
  have hp : ContinuousAt (fun v : ℝ => v ^ a) 0 :=
    continuousAt_id.rpow_const (Or.inr (zero_lt_one.trans ha).le)
  have hb : ContinuousAt (fun v : ℝ => (1 + z * v) ^ (-a)) 0 :=
    (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).rpow_const
      (Or.inl (by simp))
  have he : ContinuousAt (fun v : ℝ => Real.exp (-v)) 0 :=
    (Real.continuous_exp.comp continuous_neg).continuousAt
  exact ((he.fun_mul hp).fun_mul hb).continuousWithinAt

theorem boundaryTerm_tendsto_zero {a z : ℝ} (ha : 1 < a) (hz : 0 ≤ z) :
    Tendsto (boundaryTerm a z) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun v : ℝ => Real.exp (-v) * v ^ a)
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with v hv
    have hb : 0 < boundaryTerm a z v :=
      mul_pos (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hv _))
        (Real.rpow_pos_of_pos (base_pos hz hv.le) _)
    rw [Real.norm_eq_abs, abs_of_pos hb]
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos (base_one_le hz hv.le) (by linarith : -a ≤ 0))
      (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hv a)).le).trans_eq (mul_one _)
  · simpa only [neg_one_mul, mul_neg_one, mul_comm] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a 1 zero_lt_one

/-- The improper integration by parts identity, with both boundary terms proved zero. -/
theorem moment_ode {a z : ℝ} (ha : 1 < a) (hz : 0 ≤ z) :
    a * z ^ 2 * moment a 2 z - (1 + 2 * a * z) * moment a 1 z +
      a * moment a 0 z = 0 := by
  have h2 := (kernel_integrable ha 2 hz).const_mul (a * z ^ 2)
  have h1 := (kernel_integrable ha 1 hz).const_mul (1 + 2 * a * z)
  have h0 := (kernel_integrable ha 0 hz).const_mul a
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (boundaryTerm_continuous_zero ha z) (fun v hv => boundaryTerm_hasDerivAt a hz hv)
    ((h2.sub h1).add h0) (boundaryTerm_tendsto_zero ha hz)
  have hadd := integral_add (h2.sub h1) h0
  have hsub := integral_sub h2 h1
  simp only [Pi.sub_apply] at hadd hsub
  rw [boundaryTerm_zero ha, sub_zero, hadd, hsub,
    integral_const_mul, integral_const_mul, integral_const_mul] at h
  exact h

theorem profileJet_ode {a z : ℝ} (ha : 1 < a) (hz : 0 ≤ z) :
    z ^ 2 * profileJet a 2 z + (1 + 2 * a * z) * profileJet a 1 z +
      a * (a - 1) * profile a z = 0 := by
  calc
    _ = (Real.Gamma a)⁻¹ * (a - 1) *
        (a * z ^ 2 * moment a 2 z - (1 + 2 * a * z) * moment a 1 z +
          a * moment a 0 z) := by
      simp only [profileJet, derivativeCoeff, profile, Nat.cast_one, Nat.cast_zero, sub_zero]
      ring
    _ = 0 := by rw [moment_ode ha hz, mul_zero]

/-- The stated ODE holds at the endpoint with derivatives within the half-line. -/
theorem profile_ode_within {a z : ℝ} (ha : 1 < a) (hz : 0 ≤ z) :
    z ^ 2 * iteratedDerivWithin 2 (profile a) (Ici 0) z +
      (1 + 2 * a * z) * derivWithin (profile a) (Ici 0) z +
      a * (a - 1) * profile a z = 0 := by
  rw [← iteratedDerivWithin_one, iteratedDerivWithin_profile ha 1 hz,
    iteratedDerivWithin_profile ha 2 hz]
  exact profileJet_ode ha hz

/-- On the open half-line these are the ordinary first and second derivatives. -/
theorem profile_ode {a z : ℝ} (ha : 1 < a) (hz : 0 < z) :
    z ^ 2 * iteratedDeriv 2 (profile a) z + (1 + 2 * a * z) * deriv (profile a) z +
      a * (a - 1) * profile a z = 0 := by
  rw [← iteratedDeriv_one, iteratedDeriv_profile ha 1 hz, iteratedDeriv_profile ha 2 hz]
  exact profileJet_ode ha hz.le

/-! ## Strict slope control and a quantitative first-order estimate -/

theorem kernel_slope_gap_pos (a : ℝ) {z v : ℝ} (hz : 0 ≤ z) (hv : 0 < v) :
    0 < kernel a 0 z v - z * kernel a 1 z v := by
  have hv1 : v ^ a = v ^ (a - 1) * v := by
    convert! Real.rpow_add_one hv.ne' (a - 1) using 1
    congr 1
    ring
  have hb1 : (1 + z * v) ^ (1 - a) = (1 + z * v) ^ (-a) * (1 + z * v) := by
    convert! Real.rpow_add_one (base_pos hz hv.le).ne' (-a) using 1
    congr 1
    ring
  have he : kernel a 0 z v - z * kernel a 1 z v =
      Real.exp (-v) * v ^ (a - 1) * (1 + z * v) ^ (-a) := by
    simp only [kernel, Nat.cast_zero, Nat.cast_one, add_zero, sub_zero]
    rw [show a + 1 - 1 = a by ring, show 1 - a - 1 = -a by ring, hv1, hb1]
    ring
  rw [he]
  exact mul_pos (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hv _))
    (Real.rpow_pos_of_pos (base_pos hz hv.le) _)

theorem moment_slope_gap_pos {a z : ℝ} (ha : 1 < a) (hz : 0 ≤ z) :
    0 < moment a 0 z - z * moment a 1 z := by
  let f := fun v => kernel a 0 z v - z * kernel a 1 z v
  have hi : IntegrableOn f (Ioi 0) :=
    (kernel_integrable ha 0 hz).sub ((kernel_integrable ha 1 hz).const_mul z)
  have hs : Function.support f ∩ Ioi 0 = Ioi 0 := by
    rw [inter_eq_right]
    intro v hv
    exact (kernel_slope_gap_pos a hz hv).ne'
  have hp : 0 < ∫ v in Ioi 0, f v := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · rw [hs, Real.volume_Ioi, ← ENNReal.ofReal_zero]
      exact ENNReal.ofReal_lt_top
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact (kernel_slope_gap_pos a hz hv).le
    · exact hi
  have he := integral_sub (kernel_integrable ha 0 hz)
    ((kernel_integrable ha 1 hz).const_mul z)
  simp only [integral_const_mul] at he
  simpa only [f, he, moment] using hp

theorem profile_hasDerivWithinAt {a z : ℝ} (ha : 1 < a) (hz : 0 ≤ z) :
    HasDerivWithinAt (profile a) (profileJet a 1 z) (Ici 0) z := by
  have he : profileJet a 0 = profile a := by
    funext x
    simp [profileJet, derivativeCoeff, profile]
  simpa only [he, Nat.zero_add] using profileJet_hasDerivWithinAt ha 0 hz

theorem profile_derivWithin {a z : ℝ} (ha : 1 < a) (hz : 0 ≤ z) :
    derivWithin (profile a) (Ici 0) z =
      (Real.Gamma a)⁻¹ * (1 - a) * moment a 1 z := by
  simpa [profileJet, derivativeCoeff] using
    (profile_hasDerivWithinAt ha hz).derivWithin ((uniqueDiffOn_Ici 0) z hz)

theorem profile_deriv {a z : ℝ} (ha : 1 < a) (hz : 0 < z) :
    deriv (profile a) z = (Real.Gamma a)⁻¹ * (1 - a) * moment a 1 z := by
  simpa [profileJet, derivativeCoeff] using
    ((profile_hasDerivWithinAt ha hz.le).hasDerivAt (Ici_mem_nhds hz)).deriv

theorem profile_derivWithin_neg {a z : ℝ} (ha : 1 < a) (hz : 0 ≤ z) :
    derivWithin (profile a) (Ici 0) z < 0 := by
  rw [profile_derivWithin ha hz]
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (inv_pos.mpr (Real.Gamma_pos_of_pos (zero_lt_one.trans ha)))
      (sub_neg.mpr ha)) (moment_pos ha 1 hz)

/-- The logarithmic slope is strictly less than `a - 1 = h`, including the endpoint. -/
theorem profile_logSlopeWithin_lt {a z : ℝ} (ha : 1 < a) (hz : 0 ≤ z) :
    -z * derivWithin (profile a) (Ici 0) z / profile a z < a - 1 := by
  apply (div_lt_iff₀ (profile_pos ha hz)).2
  have hp := mul_pos
    (mul_pos (inv_pos.mpr (Real.Gamma_pos_of_pos (zero_lt_one.trans ha))) (sub_pos.mpr ha))
    (moment_slope_gap_pos ha hz)
  rw [profile_derivWithin ha hz]
  dsimp only [profile]
  nlinarith

theorem profile_logSlope_lt {a z : ℝ} (ha : 1 < a) (hz : 0 < z) :
    -z * deriv (profile a) z / profile a z < a - 1 := by
  rw [← derivWithin_of_mem_nhds (Ici_mem_nhds hz)]
  exact profile_logSlopeWithin_lt ha hz.le

theorem profile_first_derivative_bound {a z : ℝ} (ha : 1 < a) (hz : 0 ≤ z) :
    |derivWithin (profile a) (Ici 0) z| ≤ a * (a - 1) := by
  have h := profile_derivative_bound ha 1 hz
  simp only [iteratedDerivWithin_one, derivativeCoeff, Nat.cast_zero, sub_zero, one_mul,
    Nat.cast_one] at h
  have hg := Real.Gamma_pos_of_pos (zero_lt_one.trans ha)
  have he : |(Real.Gamma a)⁻¹ * (1 - a)| * Real.Gamma (a + 1) = a * (a - 1) := by
    rw [Real.Gamma_add_one (zero_lt_one.trans ha).ne', abs_mul,
      abs_of_pos (inv_pos.mpr hg), abs_of_neg (sub_neg.mpr ha)]
    field_simp; ring
  exact h.trans_eq he

/-- An explicit version of `H(z) - 1 = O_h(z)`, with `C_h = h(1+h)`. -/
theorem profile_sub_one_bound {a z : ℝ} (ha : 1 < a) (hz : 0 ≤ z) :
    |profile a z - 1| ≤ a * (a - 1) * z := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := profile a) (f' := fun x => profileJet a 1 x)
    (a := 0) (b := z) (C := a * (a - 1))
    (fun x hx => (profile_hasDerivWithinAt ha hx.1).mono Icc_subset_Ici_self)
    (by
      intro x hx
      have hd := (profile_hasDerivWithinAt ha hx.1).derivWithin ((uniqueDiffOn_Ici 0) x hx.1)
      change ‖profileJet a 1 x‖ ≤ a * (a - 1)
      rw [← hd, Real.norm_eq_abs]
      exact profile_first_derivative_bound ha hx.1)
  simpa only [Real.norm_eq_abs, profile_zero ha, sub_zero] using h z ⟨hz, le_rfl⟩

/-! ## The radial heat equation with the source exponent -/

/-- This is `-A`, since `A = 1/2 + h` and `a = 1 + h`. -/
def spatialExponent (a : ℝ) : ℝ := 1 / 2 - a

/-- The physical profile in the coordinate `s = r²/2`, at backward time `τ`. -/
def spatialProfile (a τ s : ℝ) : ℝ :=
  s ^ spatialExponent a * profile a (2 * τ / s)

/-- Spatial first, given by `s ^ (spatialExponent a - 1) * (spatialExponent a * profile a (2 * τ
/ s) - (2 * τ / s) * profileJet a 1 (2 * τ / s))`. -/
def spatialFirst (a τ s : ℝ) : ℝ :=
  s ^ (spatialExponent a - 1) *
    (spatialExponent a * profile a (2 * τ / s) -
      (2 * τ / s) * profileJet a 1 (2 * τ / s))

/-- Spatial second, constructed using `s`. -/
def spatialSecond (a τ s : ℝ) : ℝ :=
  s ^ (spatialExponent a - 2) *
    (spatialExponent a * (spatialExponent a - 1) * profile a (2 * τ / s) -
      2 * (spatialExponent a - 1) * (2 * τ / s) * profileJet a 1 (2 * τ / s) +
      (2 * τ / s) ^ 2 * profileJet a 2 (2 * τ / s))

theorem profile_hasDerivAt {a z : ℝ} (ha : 1 < a) (hz : 0 < z) :
    HasDerivAt (profile a) (profileJet a 1 z) z :=
  (profile_hasDerivWithinAt ha hz.le).hasDerivAt (Ici_mem_nhds hz)

theorem profileJet_hasDerivAt {a z : ℝ} (ha : 1 < a) (n : ℕ) (hz : 0 < z) :
    HasDerivAt (profileJet a n) (profileJet a (n + 1) z) z :=
  (profileJet_hasDerivWithinAt ha n hz.le).hasDerivAt (Ici_mem_nhds hz)

theorem ratio_hasDerivAt {τ s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s => 2 * τ / s) (-(2 * τ) / s ^ 2) s := by
  simpa only [id_eq, zero_mul, mul_one, zero_sub] using
    (hasDerivAt_const s (2 * τ)).fun_div (hasDerivAt_id s) hs.ne'

theorem spatialProfile_hasDerivAt_s {a τ s : ℝ} (ha : 1 < a) (hτ : 0 < τ) (hs : 0 < s) :
    HasDerivAt (spatialProfile a τ) (spatialFirst a τ s) s := by
  have hz : 0 < 2 * τ / s := by positivity
  have hd := (Real.hasDerivAt_rpow_const (p := spatialExponent a) (Or.inl hs.ne')).fun_mul
    ((profile_hasDerivAt ha hz).comp s (ratio_hasDerivAt hs))
  simp only [Function.comp_def] at hd
  convert! hd using 1
  dsimp only [spatialFirst]
  rw [Real.rpow_sub_one hs.ne']
  field_simp; ring

theorem spatialFirst_hasDerivAt_s {a τ s : ℝ} (ha : 1 < a) (hτ : 0 < τ) (hs : 0 < s) :
    HasDerivAt (spatialFirst a τ) (spatialSecond a τ s) s := by
  have hz : 0 < 2 * τ / s := by positivity
  have hH := (profile_hasDerivAt ha hz).comp s (ratio_hasDerivAt hs)
  have hH' := (profileJet_hasDerivAt ha 1 hz).comp s (ratio_hasDerivAt hs)
  have hd := (Real.hasDerivAt_rpow_const (p := spatialExponent a - 1) (Or.inl hs.ne')).fun_mul
    ((hH.const_mul (spatialExponent a)).fun_sub ((ratio_hasDerivAt (τ := τ) hs).fun_mul hH'))
  simp only [Function.comp_def] at hd
  convert! hd using 1
  dsimp only [spatialSecond]
  rw [show spatialExponent a - 2 = (spatialExponent a - 1) - 1 by ring,
    Real.rpow_sub_one hs.ne', Real.rpow_sub_one hs.ne']
  field_simp; ring

theorem spatialProfile_hasDerivAt_time {a τ s : ℝ} (ha : 1 < a) (hτ : 0 < τ) (hs : 0 < s) :
    HasDerivAt (fun τ => spatialProfile a τ s)
      (2 * s ^ (spatialExponent a - 1) * profileJet a 1 (2 * τ / s)) τ := by
  have hz : 0 < 2 * τ / s := by positivity
  have hd := ((profile_hasDerivAt ha hz).comp τ
    (((hasDerivAt_id τ).const_mul 2).div_const s)).const_mul (s ^ spatialExponent a)
  simp only [Function.comp_def, id_eq] at hd
  convert! hd using 1
  rw [Real.rpow_sub_one hs.ne']
  ring

/-- The angular radial Laplacian in the variable `s = r²/2`. -/
theorem spatial_heat_identity {a τ s : ℝ} (ha : 1 < a) (hτ : 0 < τ) (hs : 0 < s) :
    -(2 * s ^ (spatialExponent a - 1) * profileJet a 1 (2 * τ / s)) =
      2 * s * spatialSecond a τ s + 2 * spatialFirst a τ s - spatialProfile a τ s / (2 * s) := by
  have hz : 0 ≤ 2 * τ / s := by positivity
  have hode := profileJet_ode ha hz
  have hpow : s ^ (spatialExponent a - 2) = s ^ spatialExponent a / s ^ 2 := by
    rw [show spatialExponent a - 2 = (spatialExponent a - 1) - 1 by ring,
      Real.rpow_sub_one hs.ne', Real.rpow_sub_one hs.ne']
    ring
  dsimp only [spatialSecond, spatialFirst, spatialProfile]
  rw [hpow, Real.rpow_sub_one hs.ne']
  have hres :
      2 * s * (s ^ spatialExponent a / s ^ 2 *
        (spatialExponent a * (spatialExponent a - 1) * profile a (2 * τ / s) -
          2 * (spatialExponent a - 1) * (2 * τ / s) * profileJet a 1 (2 * τ / s) +
          (2 * τ / s) ^ 2 * profileJet a 2 (2 * τ / s))) +
        2 * (s ^ spatialExponent a / s *
          (spatialExponent a * profile a (2 * τ / s) -
            (2 * τ / s) * profileJet a 1 (2 * τ / s))) -
        s ^ spatialExponent a * profile a (2 * τ / s) / (2 * s) =
      2 * s ^ spatialExponent a / s *
        ((2 * τ / s) ^ 2 * profileJet a 2 (2 * τ / s) +
          (2 * a * (2 * τ / s)) * profileJet a 1 (2 * τ / s) +
          a * (a - 1) * profile a (2 * τ / s)) := by
    dsimp only [spatialExponent]
    field_simp; ring
  rw [hres]
  have hsum : (2 * τ / s) ^ 2 * profileJet a 2 (2 * τ / s) +
      (2 * a * (2 * τ / s)) * profileJet a 1 (2 * τ / s) +
      a * (a - 1) * profile a (2 * τ / s) = -profileJet a 1 (2 * τ / s) := by
    linarith
  rw [hsum]
  ring

/-- The radial velocity profile in physical radius and backward time. -/
def radialProfile (a τ r : ℝ) : ℝ := spatialProfile a τ (r ^ 2 / 2)

/-- Radial first, given by `spatialFirst a τ (r ^ 2 / 2) * r`. -/
def radialFirst (a τ r : ℝ) : ℝ := spatialFirst a τ (r ^ 2 / 2) * r

/-- Radial second, given by `spatialSecond a τ (r ^ 2 / 2) * r ^ 2 + spatialFirst a τ (r ^ 2 /
2)`. -/
def radialSecond (a τ r : ℝ) : ℝ :=
  spatialSecond a τ (r ^ 2 / 2) * r ^ 2 + spatialFirst a τ (r ^ 2 / 2)

theorem radiusSquared_hasDerivAt (r : ℝ) :
    HasDerivAt (fun r : ℝ => r ^ 2 / 2) r r := by
  convert! ((hasDerivAt_id r).pow 2).div_const 2 using 1
  simp

theorem radialProfile_hasDerivAt_radius {a τ r : ℝ} (ha : 1 < a) (hτ : 0 < τ) (hr : 0 < r) :
    HasDerivAt (radialProfile a τ) (radialFirst a τ r) r := by
  have hs : 0 < r ^ 2 / 2 := by positivity
  exact (spatialProfile_hasDerivAt_s ha hτ hs).comp r (radiusSquared_hasDerivAt r)

theorem radialFirst_hasDerivAt_radius {a τ r : ℝ} (ha : 1 < a) (hτ : 0 < τ) (hr : 0 < r) :
    HasDerivAt (radialFirst a τ) (radialSecond a τ r) r := by
  have hs : 0 < r ^ 2 / 2 := by positivity
  have hd := ((spatialFirst_hasDerivAt_s ha hτ hs).comp r (radiusSquared_hasDerivAt r)).mul
    (hasDerivAt_id r)
  convert! hd using 1
  dsimp only [radialSecond, Function.comp_apply, id]
  ring

theorem radialProfile_first_derivative {a τ r : ℝ} (ha : 1 < a) (hτ : 0 < τ) (hr : 0 < r) :
    deriv (radialProfile a τ) r = radialFirst a τ r :=
  (radialProfile_hasDerivAt_radius ha hτ hr).deriv

theorem radialProfile_second_derivative {a τ r : ℝ} (ha : 1 < a) (hτ : 0 < τ) (hr : 0 < r) :
    iteratedDeriv 2 (radialProfile a τ) r = radialSecond a τ r := by
  have he : deriv (radialProfile a τ) =ᶠ[𝓝 r] radialFirst a τ := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with y hy
    exact radialProfile_first_derivative ha hτ hy
  have hd := (radialFirst_hasDerivAt_radius ha hτ hr).congr_of_eventuallyEq he
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact hd.deriv

theorem radialProfile_hasDerivAt_time {a τ r : ℝ} (ha : 1 < a) (hτ : 0 < τ) (hr : 0 < r) :
    HasDerivAt (fun τ => radialProfile a τ r)
      (2 * (r ^ 2 / 2) ^ (spatialExponent a - 1) * profileJet a 1 (2 * τ / (r ^ 2 / 2))) τ :=
  spatialProfile_hasDerivAt_time ha hτ (by positivity)

/-- The actual angular radial heat equation in radius and backward time.
The second radial derivative and both first derivatives are genuine `deriv`s. -/
theorem radial_heat_equation {a τ r : ℝ} (ha : 1 < a) (hτ : 0 < τ) (hr : 0 < r) :
    -deriv (fun τ => radialProfile a τ r) τ =
      iteratedDeriv 2 (radialProfile a τ) r + deriv (radialProfile a τ) r / r -
        radialProfile a τ r / r ^ 2 := by
  rw [(radialProfile_hasDerivAt_time ha hτ hr).deriv,
    radialProfile_first_derivative ha hτ hr, radialProfile_second_derivative ha hτ hr]
  rw [spatial_heat_identity ha hτ (show 0 < r ^ 2 / 2 by positivity)]
  dsimp only [radialSecond, radialFirst, radialProfile]
  field_simp; ring

/-- With `τ = 1 - t`, the sign is the forward heat sign in the manuscript. -/
theorem forward_radial_heat_equation {a t r : ℝ} (ha : 1 < a) (ht : t < 1) (hr : 0 < r) :
    deriv (fun t => radialProfile a (1 - t) r) t =
      iteratedDeriv 2 (radialProfile a (1 - t)) r + deriv (radialProfile a (1 - t)) r / r -
        radialProfile a (1 - t) r / r ^ 2 := by
  have hτ : 0 < 1 - t := sub_pos.mpr ht
  have hd := ((radialProfile_hasDerivAt_time ha hτ hr).comp t
    ((hasDerivAt_id t).const_sub 1)).deriv
  have htau := (radialProfile_hasDerivAt_time ha hτ hr).deriv
  have hheat := radial_heat_equation ha hτ hr
  rw [htau] at hheat
  simp only [mul_neg_one] at hd
  exact hd.trans hheat

theorem spatialFirst_neg {a τ s : ℝ} (ha : 1 < a) (hτ : 0 < τ) (hs : 0 < s) :
    spatialFirst a τ s < 0 := by
  have hz : 0 < 2 * τ / s := by positivity
  have hpos := profile_pos ha hz.le
  have hlog := (div_lt_iff₀ hpos).mp (profile_logSlope_lt ha hz)
  rw [(profile_hasDerivAt ha hz).deriv] at hlog
  have hb : spatialExponent a * profile a (2 * τ / s) -
      (2 * τ / s) * profileJet a 1 (2 * τ / s) < 0 := by
    dsimp only [spatialExponent]
    nlinarith
  exact mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos hs _) hb

theorem radialProfile_derivative_neg {a τ r : ℝ} (ha : 1 < a) (hτ : 0 < τ) (hr : 0 < r) :
    deriv (radialProfile a τ) r < 0 := by
  rw [radialProfile_first_derivative ha hτ hr]
  exact mul_neg_of_neg_of_pos (spatialFirst_neg ha hτ (by positivity)) hr

/-- Joint smoothness in the physical coordinate and backward time, also at `τ = 0`. -/
theorem spatialProfile_joint_contDiffOn {a : ℝ} (ha : 1 < a) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => spatialProfile a p.2 p.1)
      {p | 0 < p.1 ∧ 0 ≤ p.2} := by
  have hp : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => p.1 ^ spatialExponent a)
      {p | 0 < p.1 ∧ 0 ≤ p.2} :=
    contDiffOn_fst.rpow_const_of_ne (fun p hp => hp.1.ne')
  have hz : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => 2 * p.2 / p.1)
      {p | 0 < p.1 ∧ 0 ≤ p.2} :=
    (contDiffOn_const.mul contDiffOn_snd).div contDiffOn_fst (fun p hp => hp.1.ne')
  exact hp.mul ((profile_contDiffOn ha).comp hz (by
    intro p hp
    change 0 ≤ 2 * p.2 / p.1
    exact div_nonneg (mul_nonneg (by norm_num) hp.2) hp.1.le))

theorem radialProfile_joint_contDiffOn {a : ℝ} (ha : 1 < a) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => radialProfile a p.2 p.1)
      {p | 0 < p.1 ∧ 0 ≤ p.2} := by
  apply (spatialProfile_joint_contDiffOn ha).comp
    (((contDiff_fst.pow 2).div_const 2).prodMk contDiff_snd).contDiffOn
  intro p hp
  exact ⟨div_pos (sq_pos_of_pos hp.1) (by norm_num), hp.2⟩

/-- This is exactly the displayed integral in Lemma 4.4. -/
theorem profile_eq_integral (a z : ℝ) :
    profile a z = (Real.Gamma a)⁻¹ *
      ∫ v in Ioi (0 : ℝ), Real.exp (-v) * v ^ (a - 1) * (1 + z * v) ^ (1 - a) := by
  simp only [profile, moment, kernel, Nat.cast_zero, add_zero, sub_zero]

/-- The physical power is exactly `s^(-A)`, where `A = 1/2 + h`. -/
theorem radialProfile_source_formula (h τ r : ℝ) :
    radialProfile (1 + h) τ r =
      (r ^ 2 / 2) ^ (-(1 / 2 + h)) * profile (1 + h) (2 * τ / (r ^ 2 / 2)) := by
  simp only [radialProfile, spatialProfile, spatialExponent]
  congr 2
  ring

theorem profile_h_sub_one_bound {h z : ℝ} (hh : 0 < h) (hz : 0 ≤ z) :
    |profile (1 + h) z - 1| ≤ h * (1 + h) * z := by
  have hb := profile_sub_one_bound (a := 1 + h) (by linarith) hz
  convert! hb using 1
  ring

theorem profile_h_logSlope_lt {h z : ℝ} (hh : 0 < h) (hz : 0 < z) :
    -z * deriv (profile (1 + h)) z / profile (1 + h) z < h := by
  simpa only [add_sub_cancel_left] using
    profile_logSlope_lt (a := 1 + h) (by linarith) hz

/-- Any fixed normalization constant preserves the actual forward heat equation. -/
theorem scaled_forward_radial_heat_equation (C : ℝ) {a t r : ℝ}
    (ha : 1 < a) (ht : t < 1) (hr : 0 < r) :
    deriv (fun t => C * radialProfile a (1 - t) r) t =
      iteratedDeriv 2 (fun r => C * radialProfile a (1 - t) r) r +
        deriv (fun r => C * radialProfile a (1 - t) r) r / r -
        C * radialProfile a (1 - t) r / r ^ 2 := by
  have hsecond : iteratedDeriv 2 (fun r => C * radialProfile a (1 - t) r) r =
      C * iteratedDeriv 2 (radialProfile a (1 - t)) r := by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, deriv_const_mul_field']
  rw [hsecond, deriv_const_mul_field, deriv_const_mul_field,
    forward_radial_heat_equation ha ht hr]
  ring

theorem scaled_radialProfile_derivative_neg {C a τ r : ℝ}
    (hC : 0 < C) (ha : 1 < a) (hτ : 0 < τ) (hr : 0 < r) :
    deriv (fun r => C * radialProfile a τ r) r < 0 := by
  rw [deriv_const_mul_field]
  exact mul_neg_of_pos_of_neg hC (radialProfile_derivative_neg ha hτ hr)

end NavierStokes.RadialHeatProfile

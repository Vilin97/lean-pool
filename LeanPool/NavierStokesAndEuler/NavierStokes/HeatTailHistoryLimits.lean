/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.RenormalizedHeatMoment
public import LeanPool.NavierStokesAndEuler.NavierStokes.ExtendedHeatDebts
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-!
# Actual history limits on the pure heat tail

All tail integrals below are actual improper integrals. Their differentiated
kernels have explicit integrable power majorants. The physical histories use
the same outgoing profile and the same compensation witness throughout.
-/

noncomputable section

open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators
open NavierStokes.OutgoingProfile (Profile)
open NavierStokes.HeatedOutgoing (CompensationWitness Coeff)

namespace NavierStokes.HeatTailHistoryLimits

/-! ## Differentiated heat corrections and their actual tail integrals -/

noncomputable def tailKernel (square : Bool) (h k : ℝ) (n : ℕ) (ν u : ℝ) : ℝ :=
  u ^ (-k) * ExtendedHeatDebts.editJet square h 1 n ν u

noncomputable def tailJet (square : Bool) (h k : ℝ) (n : ℕ) (X ν : ℝ) : ℝ :=
  ∫ u in Ioi X, tailKernel square h k n ν u

theorem integral_decay_power {k X : ℝ} (hk : 0 < k) (hX : 0 < X) :
    (∫ u : ℝ in Ioi X, u ^ (-k - 1)) = X ^ (-k) / k := by
  have ht := integral_Ioi_rpow_of_lt (by linarith : -k - 1 < -1) hX
  simpa only [show -k - 1 + 1 = -k by ring, neg_div_neg_eq] using ht

theorem tailKernel_bound {h k L ν u : ℝ} (hh : 0 < h) (hu : 1 ≤ u)
    (hν : |ν| ≤ L) (square : Bool) (n : ℕ) :
    ‖tailKernel square h k n ν u‖ ≤ ExtendedHeatDebts.editBound square h L n * u ^ (-k - 1) := by
  have hup : 0 < u := zero_lt_one.trans_le hu
  rw [tailKernel, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hup _)]
  calc
    _ ≤ u ^ (-k) * (ExtendedHeatDebts.editBound square h L n / u) :=
      mul_le_mul_of_nonneg_left (ExtendedHeatDebts.editJet_bound hh hu hν square n)
        (Real.rpow_pos_of_pos hup _).le
    _ = _ := by rw [Real.rpow_sub_one hup.ne']; ring

theorem tailKernel_continuousOn {h : ℝ} (hh : 0 < h) (square : Bool) (k : ℝ)
    (n : ℕ) (ν : ℝ) : ContinuousOn (tailKernel square h k n ν) (Ioi 0) :=
  (continuousOn_id.rpow_const (fun u hu => Or.inl (show 0 < u from hu).ne')).mul
    (ExtendedHeatDebts.editJet_continuousOn_X hh zero_lt_one square n ν)

theorem tailKernel_measurable {h X : ℝ} (hh : 0 < h) (hX : 1 ≤ X)
    (square : Bool) (k : ℝ) (n : ℕ) (ν : ℝ) :
    AEStronglyMeasurable (tailKernel square h k n ν) (volume.restrict (Ioi X)) :=
  ((tailKernel_continuousOn hh square k n ν).mono
    (Ioi_subset_Ioi (zero_le_one.trans hX))).aestronglyMeasurable measurableSet_Ioi

theorem tailKernel_dominated {h k X : ℝ} (hh : 0 < h) (hk : 0 < k) (hX : 1 ≤ X)
    (square : Bool) :
    ExtendedHeatDebts.ChainDominated (fun n ν u => tailKernel square h k n ν u)
      (volume.restrict (Ioi X)) := by
  intro n L hL
  refine ⟨fun u => ExtendedHeatDebts.editBound square h L n * u ^ (-k - 1),
    (integrableOn_Ioi_rpow_of_lt (by linarith : -k - 1 < -1)
      (zero_lt_one.trans_le hX)).const_mul _, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact fun ν hν => tailKernel_bound hh (hX.trans hu.le) hν square n

theorem tailKernel_integrable {h k X : ℝ} (hh : 0 < h) (hk : 0 < k) (hX : 1 ≤ X)
    (square : Bool) (n : ℕ) (ν : ℝ) : IntegrableOn (tailKernel square h k n ν) (Ioi X) :=
  ExtendedHeatDebts.chain_integrable (tailKernel_measurable hh hX square k)
    (tailKernel_dominated hh hk hX square) n ν

theorem tailJet_bound {h k X L ν : ℝ} (hh : 0 < h) (hk : 0 < k) (hX : 1 ≤ X)
    (hν : |ν| ≤ L) (square : Bool) (n : ℕ) :
    |tailJet square h k n X ν| ≤
      (ExtendedHeatDebts.editBound square h L n / k) * X ^ (-k) := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by linarith : -k - 1 < -1)
    (zero_lt_one.trans_le hX)).const_mul (ExtendedHeatDebts.editBound square h L n)
  have hb := norm_integral_le_of_norm_le hi (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact tailKernel_bound hh (hX.trans hu.le) hν square n)
  rw [integral_const_mul, integral_decay_power hk (zero_lt_one.trans_le hX)] at hb
  simpa only [tailJet, Real.norm_eq_abs, mul_div_assoc, div_mul_eq_mul_div] using hb

theorem tailKernel_hasDerivAt {h : ℝ} (hh : 0 < h) (square : Bool) (k : ℝ)
    (n : ℕ) (u ν : ℝ) :
    HasDerivAt (fun v => tailKernel square h k n v u) (tailKernel square h k (n + 1) ν u) ν :=
  (ExtendedHeatDebts.editJet_hasDerivAt hh 1 u square n ν).const_mul _

theorem tailJet_hasDerivAt {h k X : ℝ} (hh : 0 < h) (hk : 0 < k) (hX : 1 ≤ X)
    (square : Bool) (n : ℕ) (ν : ℝ) :
    HasDerivAt (tailJet square h k n X) (tailJet square h k (n + 1) X ν) ν :=
  ExtendedHeatDebts.integral_chain_hasDerivAt
    (Eventually.of_forall fun u n ν => tailKernel_hasDerivAt hh square k n u ν)
    (tailKernel_measurable hh hX square k) (tailKernel_dominated hh hk hX square) n ν

theorem tailJet_contDiff {h k X : ℝ} (hh : 0 < h) (hk : 0 < k) (hX : 1 ≤ X)
    (square : Bool) : ContDiff ℝ ∞ (tailJet square h k 0 X) :=
  ExtendedHeatDebts.contDiff_integral_chain
    (Eventually.of_forall fun u n ν => tailKernel_hasDerivAt hh square k n u ν)
    (tailKernel_measurable hh hX square k) (tailKernel_dominated hh hk hX square)

theorem tailJet_eq_iteratedDeriv {h k X : ℝ} (hh : 0 < h) (hk : 0 < k) (hX : 1 ≤ X)
    (square : Bool) (n : ℕ) (ν : ℝ) :
    iteratedDeriv n (tailJet square h k 0 X) ν = tailJet square h k n X ν :=
  ExtendedHeatDebts.iteratedDeriv_integral_chain
    (Eventually.of_forall fun u n ν => tailKernel_hasDerivAt hh square k n u ν)
    (tailKernel_measurable hh hX square k) (tailKernel_dominated hh hk hX square) n ν

theorem tailJet_tendsto_zero {h k : ℝ} (hh : 0 < h) (hk : 0 < k)
    (square : Bool) (n : ℕ) (ν : ℝ) :
    Tendsto (fun X => tailJet square h k n X ν) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun X =>
    (ExtendedHeatDebts.editBound square h |ν| n / k) * X ^ (-k))
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    exact tailJet_bound hh hk hX le_rfl square n
  · simpa only [mul_zero] using (tendsto_rpow_neg_atTop hk).const_mul
      (ExtendedHeatDebts.editBound square h |ν| n / k)

theorem mul_decay_power {k X : ℝ} (hX : 0 < X) :
    X * X ^ (-k) = X ^ (-(k - 1)) := by
  calc
    X * X ^ (-k) = X ^ (1 : ℝ) * X ^ (-k) := by rw [Real.rpow_one]
    _ = X ^ (1 + -k) := (Real.rpow_add hX _ _).symm
    _ = _ := by congr 1; ring

theorem mul_tailJet_tendsto_zero {h k : ℝ} (hh : 0 < h) (hk : 1 < k)
    (square : Bool) (n : ℕ) (ν : ℝ) :
    Tendsto (fun X => X * tailJet square h k n X ν) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun X =>
    (ExtendedHeatDebts.editBound square h |ν| n / k) * X ^ (-(k - 1)))
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    have hXp := zero_lt_one.trans_le hX
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos hXp, Real.norm_eq_abs]
    calc
      _ ≤ X * ((ExtendedHeatDebts.editBound square h |ν| n / k) * X ^ (-k)) :=
        mul_le_mul_of_nonneg_left (tailJet_bound hh (zero_lt_one.trans hk) hX le_rfl square n)
          hXp.le
      _ = _ := by rw [mul_left_comm, mul_decay_power hXp]
  · simpa only [mul_zero] using (tendsto_rpow_neg_atTop (sub_pos.mpr hk)).const_mul
      (ExtendedHeatDebts.editBound square h |ν| n / k)

noncomputable def etaTail (square : Bool) (h k X η : ℝ) : ℝ :=
  tailJet square h k 0 X (ParametricHeatTail.diffusion η)

theorem etaTail_contDiff {h k X : ℝ} (hh : 0 < h) (hk : 0 < k) (hX : 1 ≤ X)
    (square : Bool) : ContDiff ℝ ∞ (etaTail square h k X) :=
  (tailJet_contDiff hh hk hX square).comp ParametricHeatTail.diffusion_contDiff

theorem etaTail_hasDerivAt {h k X : ℝ} (hh : 0 < h) (hk : 0 < k) (hX : 1 ≤ X)
    (square : Bool) (η : ℝ) : HasDerivAt (etaTail square h k X)
      (tailJet square h k 1 X (ParametricHeatTail.diffusion η) * (-2 * η)) η :=
  (tailJet_hasDerivAt hh hk hX square 0 _).comp η (ParametricHeatTail.diffusion_hasDerivAt η)

theorem etaTail_bound {h k X η : ℝ} (hh : 0 < h) (hk : 0 < k) (hX : 1 ≤ X)
    (hη : η ∈ Icc (-1 : ℝ) 1) (square : Bool) :
    |etaTail square h k X η| ≤ (ExtendedHeatDebts.editBound square h 1 0 / k) * X ^ (-k) := by
  exact tailJet_bound hh hk hX
    (by rw [abs_of_nonneg (ParametricHeatTail.diffusion_mem hη).1]; exact
      (ParametricHeatTail.diffusion_mem hη).2)
    square 0

theorem etaTail_derivative_bound {h k X η : ℝ} (hh : 0 < h) (hk : 0 < k) (hX : 1 ≤ X)
    (hη : η ∈ Icc (-1 : ℝ) 1) (square : Bool) :
    |deriv (etaTail square h k X) η| ≤
      2 * (ExtendedHeatDebts.editBound square h 1 1 / k) * X ^ (-k) := by
  rw [(etaTail_hasDerivAt hh hk hX square η).deriv, abs_mul]
  have hη' : |-2 * η| ≤ 2 := by
    rw [abs_mul]
    norm_num
    exact (abs_le.mpr hη).trans_eq (by ring)
  have hb := tailJet_bound (L := 1) hh hk hX
    (by rw [abs_of_nonneg (ParametricHeatTail.diffusion_mem hη).1]; exact
      (ParametricHeatTail.diffusion_mem hη).2)
    square 1
  nlinarith [abs_nonneg (tailJet square h k 1 X (ParametricHeatTail.diffusion η))]

theorem etaTail_tendsto_zero {h k : ℝ} (hh : 0 < h) (hk : 0 < k) (square : Bool) (η : ℝ) :
    Tendsto (fun X => etaTail square h k X η) atTop (𝓝 0) :=
  tailJet_tendsto_zero hh hk square 0 _

theorem etaTail_derivative_tendsto_zero {h k : ℝ} (hh : 0 < h) (hk : 0 < k)
    (square : Bool) (η : ℝ) : Tendsto (fun X => deriv (etaTail square h k X) η) atTop (𝓝 0) := by
  have ht := (tailJet_tendsto_zero hh hk square 1 (ParametricHeatTail.diffusion η)).mul_const (-2 *
    η)
  apply (show Tendsto (fun X => tailJet square h k 1 X (ParametricHeatTail.diffusion η) * (-2 * η))
    atTop (𝓝 0) by simpa only [zero_mul] using ht).congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  exact (etaTail_hasDerivAt hh hk hX square η).deriv.symm

theorem mul_etaTail_tendsto_zero {h k : ℝ} (hh : 0 < h) (hk : 1 < k) (square : Bool) (η : ℝ) :
    Tendsto (fun X => X * etaTail square h k X η) atTop (𝓝 0) :=
  mul_tailJet_tendsto_zero hh hk square 0 _

theorem mul_etaTail_derivative_tendsto_zero {h k : ℝ} (hh : 0 < h) (hk : 1 < k)
    (square : Bool) (η : ℝ) : Tendsto (fun X => X * deriv (etaTail square h k X) η) atTop (𝓝 0) :=
      by
  have ht := (mul_tailJet_tendsto_zero hh hk square 1 (ParametricHeatTail.diffusion η)).mul_const
    (-2 * η)
  apply (show Tendsto (fun X => (X * tailJet square h k 1 X (ParametricHeatTail.diffusion η)) * (-2
    * η))
    atTop (𝓝 0) by simpa only [zero_mul] using ht).congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  rw [(etaTail_hasDerivAt hh (zero_lt_one.trans hk) hX square η).deriv]
  ring

/-! ## Exact exterior formulas for the supplied outgoing profile -/

noncomputable def amplitude (F : Profile) (XR : ℝ) : ℝ :=
  RenormalizedHeatMoment.outgoingPowerAmplitude F XR

noncomputable def angularAmplitude (F : Profile) (XR : ℝ) : ℝ :=
  Real.sqrt 2 * amplitude F XR

noncomputable def tailStart (F : Profile) (XR : ℝ) : ℝ :=
  max (RenormalizedHeatMoment.heatThreshold F XR) (Real.exp 1)

theorem tailStart_ge_one (F : Profile) (XR : ℝ) : 1 ≤ tailStart F XR :=
  (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans (le_max_right _ _)

theorem tailStart_ge_switch (F : Profile) {XR : ℝ} (hXR : 0 < XR) :
    OutgoingDilation.switchRadius F XR ≤ tailStart F XR := by
  have he : 1 ≤ Real.exp (3 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have hp := mul_le_mul_of_nonneg_left he (OutgoingDilation.switchRadius_pos F XR hXR).le
  have hg : OutgoingDilation.switchRadius F XR ≤ RenormalizedHeatMoment.heatThreshold F XR := by
    simpa only [mul_one, RenormalizedHeatMoment.heatThreshold] using hp
  exact hg.trans (le_max_left _ _)

theorem helper_switch_one {X : ℝ} (hX : Real.exp 1 ≤ X) : HeatTailEdit.switch 1 X = 1 := by
  apply HeatTailEdit.switch_one
  have h := Real.log_le_log (Real.exp_pos 1) hX
  simp only [Real.log_exp, div_one] at *
  linarith

noncomputable def heatFactor (h η X : ℝ) : ℝ :=
  HeatProfileExtension.physicalProfile (1 + h) X η

theorem heatFactor_eq_profile (h : ℝ) {η X : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1)
    (hX : 0 < X) :
    heatFactor h η X = RadialHeatProfile.profile (1 + h) (2 * (1 - η ^ 2) / X) :=
  HeatProfileExtension.physicalProfile_eq_profile _ hX hη

theorem correction_eq_factor (h : ℝ) (η : ℝ) {X : ℝ} (hX : Real.exp 1 ≤ X) :
    ExtendedHeatDebts.editJet false h 1 0 (ParametricHeatTail.diffusion η) X = heatFactor h η X - 1
      := by
  simp only [ExtendedHeatDebts.editJet, Bool.false_eq_true, ite_false,
    ExtendedHeatDebts.correctionJet_zero, ExtendedHeatDebts.correction,
    helper_switch_one hX, one_mul]
  rfl

theorem squareCorrection_eq_factor (h : ℝ) (η : ℝ) {X : ℝ} (hX : Real.exp 1 ≤ X) :
    ExtendedHeatDebts.editJet true h 1 0 (ParametricHeatTail.diffusion η) X = heatFactor h η X ^ 2
      - 1 := by
  simp only [ExtendedHeatDebts.editJet, ite_true,
    ExtendedHeatDebts.squareCorrectionJet_zero, ExtendedHeatDebts.multiplier,
    ExtendedHeatDebts.correction, helper_switch_one hX, one_mul, add_sub_cancel]
  rfl

theorem sqrt_power_identity (h D : ℝ) {X : ℝ} (hX : 0 < X) :
    Real.sqrt (2 * X) * (D * X ^ (-(1 / 2 + h))) = Real.sqrt 2 * D * X ^ (-h) := by
  have hp : Real.sqrt X * X ^ (-(1 / 2 + h)) = X ^ (-h) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hX]
    congr 1
    ring
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ = Real.sqrt 2 * D * (Real.sqrt X * X ^ (-(1 / 2 + h))) := by ring
    _ = _ := by rw [hp]

theorem powerH_eq (F : Profile) {XR X : ℝ} (hXR : 0 < XR) (hX : 0 < X) :
    OutgoingDilation.powerH F XR X = angularAmplitude F XR * X ^ (-F.data.h) := by
  rw [RenormalizedHeatMoment.outgoing_powerH F hXR hX]
  exact sqrt_power_identity F.data.h (amplitude F XR) hX

theorem heated_H_eq (F : Profile) {XR : ℝ} (hXR : 0 < XR) (c : ℝ → Coeff)
    {η X : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) (hX : tailStart F XR ≤ X) :
    HeatedOutgoing.H F XR c (X,η) =
      angularAmplitude F XR * X ^ (-F.data.h) * heatFactor F.data.h η X := by
  have hXp : 0 < X := zero_lt_one.trans_le ((tailStart_ge_one F XR).trans hX)
  rw [HeatedOutgoing.H, RenormalizedHeatMoment.heated_exterior F hXR c η
    ((le_max_left _ _).trans hX), ← heatFactor_eq_profile _ hη hXp, ← mul_assoc]
  rw [show RenormalizedHeatMoment.A F.data.h = 1 / 2 + F.data.h from rfl,
    sqrt_power_identity _ _ hXp]
  rfl

theorem heated_square_eq (F : Profile) {XR : ℝ} (hXR : 0 < XR) (c : ℝ → Coeff)
    {η X : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) (hX : tailStart F XR ≤ X) :
    HeatedOutgoing.E F XR c (X,η) ^ 2 = amplitude F XR ^ 2 *
      X ^ (-(1 + 2 * F.data.h)) * heatFactor F.data.h η X ^ 2 := by
  have hXp : 0 < X := zero_lt_one.trans_le ((tailStart_ge_one F XR).trans hX)
  rw [RenormalizedHeatMoment.heated_exterior F hXR c η ((le_max_left _ _).trans hX),
    ← heatFactor_eq_profile _ hη hXp, mul_pow, mul_pow]
  have hp : (X ^ (-RenormalizedHeatMoment.A F.data.h)) ^ 2 = X ^ (-(1 + 2 * F.data.h)) := by
    rw [pow_two, ← Real.rpow_add hXp]
    congr 1
    unfold RenormalizedHeatMoment.A
    ring
  rw [hp]
  rfl

theorem heated_difference_eq_kernel (F : Profile) {XR : ℝ} (hXR : 0 < XR) (c : ℝ → Coeff)
    {η X : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) (hX : tailStart F XR ≤ X) :
    HeatedOutgoing.H F XR c (X,η) - OutgoingDilation.powerH F XR X =
      angularAmplitude F XR * tailKernel false F.data.h F.data.h 0 (ParametricHeatTail.diffusion η)
        X := by
  rw [heated_H_eq F hXR c hη hX,
    powerH_eq F hXR (zero_lt_one.trans_le ((tailStart_ge_one F XR).trans hX)),
    tailKernel, correction_eq_factor _ _ ((le_max_right _ _).trans hX)]
  ring

theorem heated_square_eq_kernel (F : Profile) {XR : ℝ} (hXR : 0 < XR) (c : ℝ → Coeff)
    {η X : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) (hX : tailStart F XR ≤ X) :
    HeatedOutgoing.E F XR c (X,η) ^ 2 = amplitude F XR ^ 2 *
      (X ^ (-(1 + 2 * F.data.h)) +
        tailKernel true F.data.h (1 + 2 * F.data.h) 0 (ParametricHeatTail.diffusion η) X) := by
  rw [heated_square_eq F hXR c hη hX, tailKernel,
    squareCorrection_eq_factor _ _ ((le_max_right _ _).trans hX)]
  ring

theorem canonicalKernel_eq_kernel (F : Profile) {XR : ℝ} (hXR : 0 < XR) (c : ℝ → Coeff)
    {η X : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) (hX : tailStart F XR ≤ X) :
    HeatedOutgoing.canonicalKernel F XR c η X = amplitude F XR ^ 2 *
      (X ^ (-(2 + 2 * F.data.h)) +
        tailKernel true F.data.h (2 + 2 * F.data.h) 0 (ParametricHeatTail.diffusion η) X) := by
  have hXp : 0 < X := zero_lt_one.trans_le ((tailStart_ge_one F XR).trans hX)
  rw [HeatedOutgoing.canonicalKernel, heated_square_eq F hXR c hη hX,
    tailKernel, squareCorrection_eq_factor _ _ ((le_max_right _ _).trans hX)]
  have hp : X ^ (-(1 + 2 * F.data.h)) / X = X ^ (-(2 + 2 * F.data.h)) := by
    rw [← Real.rpow_sub_one hXp.ne']
    congr 1
    ring
  calc
    _ = amplitude F XR ^ 2 * (X ^ (-(1 + 2 * F.data.h)) / X) * heatFactor F.data.h η X ^ 2 := by
      ring
    _ = _ := by rw [hp]; ring

/-! ## The constants are fixed by the same compensation witness -/

noncomputable def angularHistory (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (η X : ℝ) : ℝ :=
  ∫ u in Ioc 0 X, HeatedOutgoing.H F XR c (u,η)

noncomputable def energyHistory (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (η X : ℝ) : ℝ :=
  ∫ u in Ioc 0 X, HeatedOutgoing.energyDensity F XR c η u

noncomputable def powerHistory (F : Profile) (XR X : ℝ) : ℝ :=
  ∫ u in Ioc 0 X, OutgoingDilation.powerH F XR u

theorem split_positive_integral {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) {X : ℝ} (hX : 0 ≤ X) :
    (∫ u in Ioc 0 X, f u) + (∫ u in Ioi X, f u) = ∫ u in Ioi 0, f u := by
  simpa only [Ioc_union_Ioi_eq_Ioi hX] using
    (setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hf.mono_set Ioc_subset_Ioi_self) (hf.mono_set (Ioi_subset_Ioi hX))).symm

theorem angularHistory_integrable {F : Profile} {XR C : ℝ} (w : CompensationWitness F XR C)
    {η X : ℝ} (hη : η ∈ HeatedOutgoing.parameterDomain) (hX : 0 < X) :
    IntegrableOn (fun u => HeatedOutgoing.H F XR w.coefficients (u,η)) (Ioc 0 X) := by
  have hi := (OutgoingDilation.I_integrable F XR η X w.radius_pos hX).add
    ((w.changeRow_integrable η 2 hη).mono_set Ioc_subset_Ioi_self)
  apply IntegrableOn.congr_fun hi _ measurableSet_Ioc
  intro u hu
  change Real.sqrt (2*u) * OutgoingDilation.E F XR (u,η) +
    Real.sqrt (2*u) * (HeatedOutgoing.E F XR w.coefficients (u,η) - OutgoingDilation.E F XR (u,η)) =
    Real.sqrt (2*u) * HeatedOutgoing.E F XR w.coefficients (u,η)
  ring

theorem angularHistory_eq_power_sub_future {F : Profile} {XR C : ℝ}
    (w : CompensationWitness F XR C) {η X : ℝ}
    (hη : η ∈ HeatedOutgoing.parameterDomain) (hX : 0 < X) :
    angularHistory F XR w.coefficients η X = powerHistory F XR X -
      ∫ u in Ioi X, HeatedOutgoing.H F XR w.coefficients (u,η) - OutgoingDilation.powerH F XR u :=
        by
  have hi := angularHistory_integrable w hη hX
  have hr := (w.renormalized_integrable η hη).mono_set (show Ioc (0 : ℝ) X ⊆ Ioi 0 from fun _ h =>
    h.1)
  have hp : IntegrableOn (OutgoingDilation.powerH F XR) (Ioc 0 X) := by
    apply IntegrableOn.congr_fun (hi.sub hr) _ measurableSet_Ioc
    intro u hu
    dsimp
    ring
  have hs := split_positive_integral (w.renormalized_integrable η hη) hX.le
  rw [w.renormalized_zero η hη, integral_sub hi hp] at hs
  unfold angularHistory powerHistory
  linarith

theorem energyHistory_eq_square_future {F : Profile} {XR C B : ℝ}
    (hF : OutgoingProfile.Specification F B) (w : CompensationWitness F XR C)
    {η X : ℝ} (hη : η ∈ HeatedOutgoing.parameterDomain)
    (hX : OutgoingDilation.switchRadius F XR ≤ X) :
    energyHistory F XR w.coefficients η X =
      (1/2 : ℝ) * ∫ u in Ioi X, HeatedOutgoing.E F XR w.coefficients (u,η)^2 := by
  have hXp := (OutgoingDilation.switchRadius_pos F XR w.radius_pos).trans_le hX
  have hs := split_positive_integral (w.energy_integrable η hη) hXp.le
  have hz := w.energy_zero hF η hη
  unfold HeatedOutgoing.totalS at hz
  rw [hz] at hs
  have he : (∫ u in Ioi X, HeatedOutgoing.energyDensity F XR w.coefficients η u) =
      ∫ u in Ioi X, -(HeatedOutgoing.E F XR w.coefficients (u,η)^2/2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    rw [HeatedOutgoing.energyDensity,
      HeatedOutgoing.U_after_switch F XR η u w.radius_pos (hX.trans hu.le)]
    ring
  rw [he, integral_neg, integral_div] at hs
  unfold energyHistory
  linarith

noncomputable def powerTail (k X : ℝ) : ℝ := X ^ (-(k - 1)) / (k - 1)

theorem powerTail_eq_integral {k X : ℝ} (hk : 1 < k) (hX : 0 < X) :
    powerTail k X = ∫ u : ℝ in Ioi X, u ^ (-k) := by
  rw [integral_Ioi_rpow_of_lt (by linarith : -k < -1) hX, powerTail]
  rw [show -k + 1 = -(k - 1) by ring, neg_div_neg_eq]

theorem angularHistory_formula {F : Profile} {XR C : ℝ} (w : CompensationWitness F XR C)
    {η X : ℝ} (hη : η ∈ HeatedOutgoing.parameterDomain) (hX : tailStart F XR ≤ X) :
    angularHistory F XR w.coefficients η X = powerHistory F XR X -
      angularAmplitude F XR * etaTail false F.data.h F.data.h X η := by
  rw [angularHistory_eq_power_sub_future w hη (zero_lt_one.trans_le ((tailStart_ge_one F XR).trans
    hX))]
  have he : (∫ u in Ioi X, HeatedOutgoing.H F XR w.coefficients (u,η) - OutgoingDilation.powerH F
    XR u) =
      angularAmplitude F XR * etaTail false F.data.h F.data.h X η := by
    rw [etaTail, tailJet, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact heated_difference_eq_kernel F w.radius_pos w.coefficients hη (hX.trans hu.le)
  rw [he]

theorem square_future_formula (F : Profile) {XR : ℝ} (hXR : 0 < XR) (c : ℝ → Coeff)
    {η X : ℝ} (hη : η ∈ HeatedOutgoing.parameterDomain) (hX : tailStart F XR ≤ X) :
    (∫ u in Ioi X, HeatedOutgoing.E F XR c (u,η)^2) = amplitude F XR ^ 2 *
      (powerTail (1 + 2 * F.data.h) X + etaTail true F.data.h (1 + 2 * F.data.h) X η) := by
  have hX1 := (tailStart_ge_one F XR).trans hX
  have hh := F.data.h_pos
  have hiP := integrableOn_Ioi_rpow_of_lt (by linarith : -(1 + 2 * F.data.h) < -1)
    (zero_lt_one.trans_le hX1)
  have hiT := tailKernel_integrable hh (by linarith : 0 < 1 + 2 * F.data.h) hX1 true 0
    (ParametricHeatTail.diffusion η)
  have he : (∫ u in Ioi X, HeatedOutgoing.E F XR c (u,η)^2) =
      ∫ u in Ioi X, amplitude F XR ^ 2 * (u ^ (-(1 + 2 * F.data.h)) +
        tailKernel true F.data.h (1 + 2 * F.data.h) 0 (ParametricHeatTail.diffusion η) u) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact heated_square_eq_kernel F hXR c hη (hX.trans hu.le)
  rw [he, integral_const_mul, integral_add hiP hiT,
    ← powerTail_eq_integral (by linarith : 1 < 1 + 2 * F.data.h) (zero_lt_one.trans_le hX1)]
  rfl

theorem energyHistory_formula {F : Profile} {XR C B : ℝ}
    (hF : OutgoingProfile.Specification F B) (w : CompensationWitness F XR C)
    {η X : ℝ} (hη : η ∈ HeatedOutgoing.parameterDomain) (hX : tailStart F XR ≤ X) :
    energyHistory F XR w.coefficients η X = (amplitude F XR ^ 2 / 2) *
      (powerTail (1 + 2 * F.data.h) X + etaTail true F.data.h (1 + 2 * F.data.h) X η) := by
  rw [energyHistory_eq_square_future hF w hη ((tailStart_ge_switch F w.radius_pos).trans hX),
    square_future_formula F w.radius_pos w.coefficients hη hX]
  ring

theorem pressure_formula (F : Profile) {XR : ℝ} (hXR : 0 < XR) (c : ℝ → Coeff)
    {η X : ℝ} (hη : η ∈ HeatedOutgoing.parameterDomain) (hX : tailStart F XR ≤ X) :
    HeatedOutgoing.Pi F XR c (X,η) = -(amplitude F XR ^ 2 / 2) *
      (powerTail (2 + 2 * F.data.h) X + etaTail true F.data.h (2 + 2 * F.data.h) X η) := by
  have hX1 := (tailStart_ge_one F XR).trans hX
  have hh := F.data.h_pos
  have hiP := integrableOn_Ioi_rpow_of_lt (by linarith : -(2 + 2 * F.data.h) < -1)
    (zero_lt_one.trans_le hX1)
  have hiT := tailKernel_integrable hh (by linarith : 0 < 2 + 2 * F.data.h) hX1 true 0
    (ParametricHeatTail.diffusion η)
  have he : (∫ u in Ioi X, HeatedOutgoing.canonicalKernel F XR c η u) =
      ∫ u in Ioi X, amplitude F XR ^ 2 * (u ^ (-(2 + 2 * F.data.h)) +
        tailKernel true F.data.h (2 + 2 * F.data.h) 0 (ParametricHeatTail.diffusion η) u) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact canonicalKernel_eq_kernel F hXR c hη (hX.trans hu.le)
  rw [HeatedOutgoing.Pi, he, integral_const_mul, integral_add hiP hiT,
    ← powerTail_eq_integral (by linarith : 1 < 2 + 2 * F.data.h) (zero_lt_one.trans_le hX1)]
  unfold etaTail tailJet
  ring

/-! ## Genuine parameter derivatives and the history limits -/

theorem parameter_germ {f g : ℝ → ℝ} {η : ℝ} (hη : η ∈ Ioo (-1 : ℝ) 1)
    (he : ∀ t ∈ Icc (-1 : ℝ) 1, f t = g t) : f =ᶠ[𝓝 η] g := by
  filter_upwards [Ioo_mem_nhds hη.1 hη.2] with t ht
  exact he t ⟨ht.1.le, ht.2.le⟩

theorem angularHistory_hasDerivAt {F : Profile} {XR C : ℝ} (w : CompensationWitness F XR C)
    {η X : ℝ} (hη : η ∈ Ioo (-1 : ℝ) 1) (hX : tailStart F XR ≤ X) :
    HasDerivAt (fun t => angularHistory F XR w.coefficients t X)
      (-angularAmplitude F XR * deriv (etaTail false F.data.h F.data.h X) η) η := by
  have ht := (etaTail_hasDerivAt F.data.h_pos F.data.h_pos
    ((tailStart_ge_one F XR).trans hX) false η).differentiableAt.hasDerivAt
  have hd := ((ht.const_mul (angularAmplitude F XR)).const_sub (powerHistory F XR
    X)).congr_of_eventuallyEq
    (parameter_germ hη (fun t ht => angularHistory_formula w ht hX))
  simpa only [neg_mul] using hd

theorem energyHistory_hasDerivAt {F : Profile} {XR C B : ℝ}
    (hF : OutgoingProfile.Specification F B) (w : CompensationWitness F XR C)
    {η X : ℝ} (hη : η ∈ Ioo (-1 : ℝ) 1) (hX : tailStart F XR ≤ X) :
    HasDerivAt (fun t => energyHistory F XR w.coefficients t X)
      ((amplitude F XR ^ 2 / 2) * deriv (etaTail true F.data.h (1 + 2 * F.data.h) X) η) η := by
  have hh := F.data.h_pos
  have ht := (etaTail_hasDerivAt hh (by linarith : 0 < 1 + 2 * F.data.h)
    ((tailStart_ge_one F XR).trans hX) true η).differentiableAt.hasDerivAt
  exact ((ht.const_add (powerTail (1 + 2 * F.data.h) X)).const_mul (amplitude F XR ^ 2 /
    2)).congr_of_eventuallyEq
    (parameter_germ hη (fun t ht => energyHistory_formula hF w ht hX))

theorem pressure_hasDerivAt (F : Profile) {XR : ℝ} (hXR : 0 < XR) (c : ℝ → Coeff)
    {η X : ℝ} (hη : η ∈ Ioo (-1 : ℝ) 1) (hX : tailStart F XR ≤ X) :
    HasDerivAt (fun t => HeatedOutgoing.Pi F XR c (X,t))
      (-(amplitude F XR ^ 2 / 2) * deriv (etaTail true F.data.h (2 + 2 * F.data.h) X) η) η := by
  have hh := F.data.h_pos
  have ht := (etaTail_hasDerivAt hh (by linarith : 0 < 2 + 2 * F.data.h)
    ((tailStart_ge_one F XR).trans hX) true η).differentiableAt.hasDerivAt
  exact ((ht.const_add (powerTail (2 + 2 * F.data.h) X)).const_mul (-(amplitude F XR ^ 2 /
    2))).congr_of_eventuallyEq
    (parameter_germ hη (fun t ht => pressure_formula F hXR c ht hX))

theorem powerTail_tendsto_zero {k : ℝ} (hk : 1 < k) :
    Tendsto (powerTail k) atTop (𝓝 0) := by
  unfold powerTail
  simpa only [zero_div] using (tendsto_rpow_neg_atTop (sub_pos.mpr hk)).div_const (k - 1)

theorem mul_powerTail_tendsto_zero {k : ℝ} (hk : 2 < k) :
    Tendsto (fun X => X * powerTail k X) atTop (𝓝 0) := by
  have ht : Tendsto (fun X : ℝ => X ^ (-(k - 2)) / (k - 1)) atTop (𝓝 0) := by
    simpa only [zero_div] using (tendsto_rpow_neg_atTop (sub_pos.mpr hk)).div_const (k - 1)
  apply ht.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with X hX
  rw [powerTail, ← mul_div_assoc, mul_decay_power hX]
  congr 2
  ring

theorem angularHistory_sub_power_tendsto_zero {F : Profile} {XR C : ℝ}
    (w : CompensationWitness F XR C) {η : ℝ} (hη : η ∈ HeatedOutgoing.parameterDomain) :
    Tendsto (fun X => angularHistory F XR w.coefficients η X - powerHistory F XR X) atTop (𝓝 0) :=
      by
  have ht := (etaTail_tendsto_zero F.data.h_pos F.data.h_pos false η).const_mul (-angularAmplitude
    F XR)
  apply (show Tendsto (fun X => -angularAmplitude F XR * etaTail false F.data.h F.data.h X η)
    atTop (𝓝 0) by simpa only [mul_zero] using ht).congr'
  filter_upwards [eventually_ge_atTop (tailStart F XR)] with X hX
  rw [angularHistory_formula w hη hX]
  ring

theorem angularHistory_eta_tendsto_zero {F : Profile} {XR C : ℝ}
    (w : CompensationWitness F XR C) {η : ℝ} (hη : η ∈ Ioo (-1 : ℝ) 1) :
    Tendsto (fun X => deriv (fun t => angularHistory F XR w.coefficients t X) η) atTop (𝓝 0) := by
  have ht := (etaTail_derivative_tendsto_zero F.data.h_pos F.data.h_pos false η).const_mul
    (-angularAmplitude F XR)
  apply (show Tendsto (fun X => -angularAmplitude F XR * deriv (etaTail false F.data.h F.data.h X)
    η)
    atTop (𝓝 0) by simpa only [mul_zero] using ht).congr'
  filter_upwards [eventually_ge_atTop (tailStart F XR)] with X hX
  exact (angularHistory_hasDerivAt w hη hX).deriv.symm

theorem energyHistory_tendsto_zero {F : Profile} {XR C B : ℝ}
    (hF : OutgoingProfile.Specification F B) (w : CompensationWitness F XR C)
    {η : ℝ} (hη : η ∈ HeatedOutgoing.parameterDomain) :
    Tendsto (fun X => energyHistory F XR w.coefficients η X) atTop (𝓝 0) := by
  have hh := F.data.h_pos
  have ht := ((powerTail_tendsto_zero (by linarith : 1 < 1 + 2 * F.data.h)).add
    (etaTail_tendsto_zero hh (by linarith : 0 < 1 + 2 * F.data.h) true η)).const_mul (amplitude F
      XR ^ 2 / 2)
  apply (show Tendsto (fun X => (amplitude F XR ^ 2 / 2) *
    (powerTail (1 + 2 * F.data.h) X + etaTail true F.data.h (1 + 2 * F.data.h) X η))
    atTop (𝓝 0) by simpa only [add_zero, mul_zero] using ht).congr'
  filter_upwards [eventually_ge_atTop (tailStart F XR)] with X hX
  exact (energyHistory_formula hF w hη hX).symm

theorem energyHistory_eta_tendsto_zero {F : Profile} {XR C B : ℝ}
    (hF : OutgoingProfile.Specification F B) (w : CompensationWitness F XR C)
    {η : ℝ} (hη : η ∈ Ioo (-1 : ℝ) 1) :
    Tendsto (fun X => deriv (fun t => energyHistory F XR w.coefficients t X) η) atTop (𝓝 0) := by
  have hh := F.data.h_pos
  have ht := (etaTail_derivative_tendsto_zero hh (by linarith : 0 < 1 + 2 * F.data.h) true
    η).const_mul (amplitude F XR ^ 2 / 2)
  apply (show Tendsto (fun X => (amplitude F XR ^ 2 / 2) *
    deriv (etaTail true F.data.h (1 + 2 * F.data.h) X) η) atTop (𝓝 0) by simpa only [mul_zero]
      using ht).congr'
  filter_upwards [eventually_ge_atTop (tailStart F XR)] with X hX
  exact (energyHistory_hasDerivAt hF w hη hX).deriv.symm

theorem mul_pressure_tendsto_zero (F : Profile) {XR : ℝ} (hXR : 0 < XR) (c : ℝ → Coeff)
    {η : ℝ} (hη : η ∈ HeatedOutgoing.parameterDomain) :
    Tendsto (fun X => X * HeatedOutgoing.Pi F XR c (X,η)) atTop (𝓝 0) := by
  have hh := F.data.h_pos
  have ht := ((mul_powerTail_tendsto_zero (by linarith : 2 < 2 + 2 * F.data.h)).add
    (mul_etaTail_tendsto_zero hh (by linarith : 1 < 2 + 2 * F.data.h) true η)).const_mul
      (-(amplitude F XR ^ 2 / 2))
  apply (show Tendsto (fun X => -(amplitude F XR ^ 2 / 2) *
    (X * powerTail (2 + 2 * F.data.h) X + X * etaTail true F.data.h (2 + 2 * F.data.h) X η))
    atTop (𝓝 0) by simpa only [add_zero, mul_zero] using ht).congr'
  filter_upwards [eventually_ge_atTop (tailStart F XR)] with X hX
  rw [pressure_formula F hXR c hη hX]
  ring

theorem mul_pressure_eta_tendsto_zero (F : Profile) {XR : ℝ} (hXR : 0 < XR) (c : ℝ → Coeff)
    {η : ℝ} (hη : η ∈ Ioo (-1 : ℝ) 1) :
    Tendsto (fun X => X * deriv (fun t => HeatedOutgoing.Pi F XR c (X,t)) η) atTop (𝓝 0) := by
  have hh := F.data.h_pos
  have ht := (mul_etaTail_derivative_tendsto_zero hh (by linarith : 1 < 2 + 2 * F.data.h) true
    η).const_mul (-(amplitude F XR ^ 2 / 2))
  apply (show Tendsto (fun X => -(amplitude F XR ^ 2 / 2) *
    (X * deriv (etaTail true F.data.h (2 + 2 * F.data.h) X) η))
    atTop (𝓝 0) by simpa only [mul_zero] using ht).congr'
  filter_upwards [eventually_ge_atTop (tailStart F XR)] with X hX
  rw [(pressure_hasDerivAt F hXR c hη hX).deriv]
  ring

/-! ## The actual angular field and its radial derivative at infinity -/

noncomputable def heatH (h D η X : ℝ) : ℝ := D * X ^ (-h) * heatFactor h η X

noncomputable def factorSlope (h η X : ℝ) : ℝ :=
  -h * heatFactor h η X - (2 * (1 - η ^ 2) / X) *
    deriv (HeatProfileExtension.extension (1 + h)) (2 * (1 - η ^ 2) / X)

theorem heatFactor_tendsto_one {h : ℝ} (hh : 0 < h) (η : ℝ) :
    Tendsto (heatFactor h η) atTop (𝓝 1) := by
  have ha : 1 < 1 + h := by linarith
  have hz : Tendsto (fun X : ℝ => 2 * (1 - η ^ 2) / X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have ht := ((HeatProfileExtension.extension_contDiff ha).continuous.continuousAt (x :=
    0)).tendsto.comp hz
  unfold heatFactor HeatProfileExtension.physicalProfile HeatProfileExtension.scaledProfile
  simpa only [Function.comp_def, HeatProfileExtension.extension_zero ha] using ht

theorem factorSlope_tendsto {h : ℝ} (hh : 0 < h) (η : ℝ) :
    Tendsto (factorSlope h η) atTop (𝓝 (-h)) := by
  have ha : 1 < 1 + h := by linarith
  have hext := HeatProfileExtension.extension_contDiff ha
  have hdc : Continuous (deriv (HeatProfileExtension.extension (1 + h))) := by
    simpa only [iteratedDeriv_one] using
      hext.continuous_iteratedDeriv 1 (WithTop.coe_le_coe.mpr le_top)
  have hz : Tendsto (fun X : ℝ => 2 * (1 - η ^ 2) / X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hd := (hdc.continuousAt (x := 0)).tendsto.comp hz
  have ht := ((heatFactor_tendsto_one hh η).const_mul (-h)).sub (hz.mul hd)
  unfold factorSlope
  simpa only [Function.comp_def, mul_one, zero_mul, sub_zero] using ht

theorem heatH_tendsto_zero {h : ℝ} (hh : 0 < h) (D η : ℝ) :
    Tendsto (heatH h D η) atTop (𝓝 0) := by
  have ht := ((tendsto_rpow_neg_atTop hh).const_mul D).mul (heatFactor_tendsto_one hh η)
  unfold heatH
  simpa only [mul_zero, zero_mul] using ht

theorem heatH_hasDerivAt {h X : ℝ} (hh : 0 < h) (D η : ℝ) (hX : 0 < X) :
    HasDerivAt (heatH h D η) (D * X ^ (-h - 1) * factorSlope h η X) X := by
  have ha : 1 < 1 + h := by linarith
  have hz : HasDerivAt (fun x : ℝ => 2 * (1 - η ^ 2) / x)
      (-(2 * (1 - η ^ 2)) / X ^ 2) X := by
    convert! (hasDerivAt_const X (2 * (1 - η ^ 2))).div (hasDerivAt_id X) hX.ne' using 1
    simp only [id_eq]
    ring
  have hf := (((HeatProfileExtension.extension_contDiff ha).differentiable (by simp))
    (2 * (1 - η ^ 2) / X)).hasDerivAt.comp X hz
  simp only [Function.comp_def] at hf
  have hp := Real.hasDerivAt_rpow_const (p := -h) (Or.inl hX.ne')
  change HasDerivAt (fun x : ℝ => D * x ^ (-h) *
    HeatProfileExtension.extension (1 + h) (2 * (1 - η ^ 2) / x)) _ X
  convert! (hp.const_mul D).fun_mul hf using 1
  dsimp only [factorSlope, heatFactor, HeatProfileExtension.physicalProfile,
    HeatProfileExtension.scaledProfile]
  rw [Real.rpow_sub_one hX.ne']
  field_simp [hX.ne'] ; ring

theorem heatH_weighted_deriv {h X : ℝ} (hh : 0 < h) (D η : ℝ) (hX : 0 < X) :
    X * deriv (heatH h D η) X = D * X ^ (-h) * factorSlope h η X := by
  rw [(heatH_hasDerivAt hh D η hX).deriv, Real.rpow_sub_one hX.ne']
  field_simp [hX.ne']

theorem heatH_weighted_deriv_tendsto_zero {h : ℝ} (hh : 0 < h) (D η : ℝ) :
    Tendsto (fun X => X * deriv (heatH h D η) X) atTop (𝓝 0) := by
  have ht := ((tendsto_rpow_neg_atTop hh).const_mul D).mul (factorSlope_tendsto hh η)
  apply (show Tendsto (fun X => D * X ^ (-h) * factorSlope h η X) atTop (𝓝 0)
    by simpa only [mul_zero, zero_mul] using ht).congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with X hX
  exact (heatH_weighted_deriv hh D η hX).symm

theorem H_tendsto_zero (F : Profile) {XR : ℝ} (hXR : 0 < XR) (c : ℝ → Coeff)
    {η : ℝ} (hη : η ∈ HeatedOutgoing.parameterDomain) :
    Tendsto (fun X => HeatedOutgoing.H F XR c (X,η)) atTop (𝓝 0) := by
  apply (heatH_tendsto_zero F.data.h_pos (angularAmplitude F XR) η).congr'
  filter_upwards [eventually_ge_atTop (tailStart F XR)] with X hX
  exact (heated_H_eq F hXR c hη hX).symm

theorem H_hasDerivAt (F : Profile) {XR : ℝ} (hXR : 0 < XR) (c : ℝ → Coeff)
    {η X : ℝ} (hη : η ∈ HeatedOutgoing.parameterDomain) (hX : tailStart F XR < X) :
    HasDerivAt (fun u => HeatedOutgoing.H F XR c (u,η))
      (angularAmplitude F XR * X ^ (-F.data.h - 1) * factorSlope F.data.h η X) X := by
  have he : (fun u => HeatedOutgoing.H F XR c (u,η)) =ᶠ[𝓝 X]
      heatH F.data.h (angularAmplitude F XR) η := by
    filter_upwards [Ioi_mem_nhds hX] with u hu
    exact heated_H_eq F hXR c hη hu.le
  exact (heatH_hasDerivAt F.data.h_pos (angularAmplitude F XR) η
    (zero_lt_one.trans_le ((tailStart_ge_one F XR).trans hX.le))).congr_of_eventuallyEq he

theorem mul_H_deriv_tendsto_zero (F : Profile) {XR : ℝ} (hXR : 0 < XR) (c : ℝ → Coeff)
    {η : ℝ} (hη : η ∈ HeatedOutgoing.parameterDomain) :
    Tendsto (fun X => X * deriv (fun u => HeatedOutgoing.H F XR c (u,η)) X) atTop (𝓝 0) := by
  apply (heatH_weighted_deriv_tendsto_zero F.data.h_pos (angularAmplitude F XR) η).congr'
  filter_upwards [Ioi_mem_atTop (tailStart F XR)] with X hX
  rw [(H_hasDerivAt F hXR c hη hX).deriv,
    (heatH_hasDerivAt F.data.h_pos (angularAmplitude F XR) η
      (zero_lt_one.trans_le ((tailStart_ge_one F XR).trans hX.le))).deriv]

theorem mul_tailKernel_tendsto_zero {h k : ℝ} (hh : 0 < h) (hk : 0 < k)
    (square : Bool) (n : ℕ) (ν : ℝ) :
    Tendsto (fun X => X * tailKernel square h k n ν X) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun X => ExtendedHeatDebts.editBound square h |ν| n * X ^ (-k))
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    have hXp := zero_lt_one.trans_le hX
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos hXp]
    calc
      _ ≤ X * (ExtendedHeatDebts.editBound square h |ν| n * X ^ (-k - 1)) :=
        mul_le_mul_of_nonneg_left (tailKernel_bound hh hX le_rfl square n) hXp.le
      _ = _ := by rw [Real.rpow_sub_one hXp.ne']; field_simp [hXp.ne']
  · simpa only [mul_zero] using (tendsto_rpow_neg_atTop hk).const_mul
      (ExtendedHeatDebts.editBound square h |ν| n)

theorem mul_H_sub_powerH_tendsto_zero (F : Profile) {XR : ℝ} (hXR : 0 < XR) (c : ℝ → Coeff)
    {η : ℝ} (hη : η ∈ HeatedOutgoing.parameterDomain) :
    Tendsto (fun X => X * (HeatedOutgoing.H F XR c (X,η) - OutgoingDilation.powerH F XR X))
      atTop (𝓝 0) := by
  have ht := (mul_tailKernel_tendsto_zero F.data.h_pos F.data.h_pos false 0
    (ParametricHeatTail.diffusion η)).const_mul (angularAmplitude F XR)
  apply (show Tendsto (fun X => angularAmplitude F XR *
    (X * tailKernel false F.data.h F.data.h 0 (ParametricHeatTail.diffusion η) X))
    atTop (𝓝 0) by simpa only [mul_zero] using ht).congr'
  filter_upwards [eventually_ge_atTop (tailStart F XR)] with X hX
  rw [heated_difference_eq_kernel F hXR c hη hX]
  ring

/-- All required history limits for one and the same actual heat completion. -/
theorem actual_history_limits {F : Profile} {XR C B : ℝ}
    (hF : OutgoingProfile.Specification F B) (w : CompensationWitness F XR C)
    {η : ℝ} (hη : η ∈ Ioo (-1 : ℝ) 1) :
    Tendsto (fun X => angularHistory F XR w.coefficients η X - powerHistory F XR X) atTop (𝓝 0) ∧
    Tendsto (fun X => deriv (fun t => angularHistory F XR w.coefficients t X) η) atTop (𝓝 0) ∧
    Tendsto (fun X => HeatedOutgoing.H F XR w.coefficients (X,η)) atTop (𝓝 0) ∧
    Tendsto (fun X => X * deriv (fun u => HeatedOutgoing.H F XR w.coefficients (u,η)) X) atTop (𝓝
      0) ∧
    Tendsto (fun X => energyHistory F XR w.coefficients η X) atTop (𝓝 0) ∧
    Tendsto (fun X => deriv (fun t => energyHistory F XR w.coefficients t X) η) atTop (𝓝 0) ∧
    Tendsto (fun X => X * HeatedOutgoing.Pi F XR w.coefficients (X,η)) atTop (𝓝 0) ∧
    Tendsto (fun X => X * deriv (fun t => HeatedOutgoing.Pi F XR w.coefficients (X,t)) η) atTop (𝓝
      0) ∧
    Tendsto (fun X => X * (HeatedOutgoing.H F XR w.coefficients (X,η) -
      OutgoingDilation.powerH F XR X)) atTop (𝓝 0) := by
  have hb : η ∈ HeatedOutgoing.parameterDomain := ⟨hη.1.le, hη.2.le⟩
  exact ⟨angularHistory_sub_power_tendsto_zero w hb, angularHistory_eta_tendsto_zero w hη,
    H_tendsto_zero F w.radius_pos w.coefficients hb,
    mul_H_deriv_tendsto_zero F w.radius_pos w.coefficients hb,
    energyHistory_tendsto_zero hF w hb, energyHistory_eta_tendsto_zero hF w hη,
    mul_pressure_tendsto_zero F w.radius_pos w.coefficients hb,
    mul_pressure_eta_tendsto_zero F w.radius_pos w.coefficients hη,
    mul_H_sub_powerH_tendsto_zero F w.radius_pos w.coefficients hb⟩

end NavierStokes.HeatTailHistoryLimits

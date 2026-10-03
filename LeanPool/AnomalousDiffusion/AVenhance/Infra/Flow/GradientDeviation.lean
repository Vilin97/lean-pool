/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SpatialC1
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.VariationalEquation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Composition
public import Mathlib.Analysis.ODE.Gronwall

/-! A quantitative first-order estimate for the spatial derivative of a flow. -/

@[expose] public section

open Homogenization
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

/-- Reverse-time vector field used in the gradient-deviation estimate. -/
def GradientDeviation.gradientReverseTimeField (b : ℝ → Vec 2 → Vec 2) :
    ℝ → Vec 2 → Vec 2 := fun t x => -b (-t) x

/-- Reverse-time flow used in the gradient-deviation estimate. -/
def GradientDeviation.gradientReverseTimeFlow (X : ℝ → Vec 2 → ℝ → Vec 2) :
    ℝ → Vec 2 → ℝ → Vec 2 := fun t x s => X (-t) x (-s)

theorem GradientDeviation.gradientReverseTimeField_smoothPeriodic
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) :
    SmoothPeriodicField (GradientDeviation.gradientReverseTimeField b) := by
  refine ⟨?_, ?_⟩
  · change ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => -Function.uncurry b (-p.1, p.2))
    have hmap : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => (-p.1, p.2)) := by fun_prop
    exact contDiff_neg.comp (hb.smooth.comp hmap)
  · intro m k t x
    have h := hb.periodic (-m) k (-t) x
    simpa [GradientDeviation.gradientReverseTimeField, neg_add, add_comm] using congrArg Neg.neg h

theorem GradientDeviation.gradientReverseTimeFlow_isFlow
    {b : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hX : AVenhance.IsFlow b X) :
    AVenhance.IsFlow (GradientDeviation.gradientReverseTimeField b)
        (GradientDeviation.gradientReverseTimeFlow X) := by
  constructor
  · intro x s
    exact hX.1 x (-s)
  · intro x s t
    have hbase : HasDerivAt (fun r => X r x (-s))
        (b (0 - t) (X (0 - t) x (-s))) (0 - t) := by
      simpa only [zero_sub] using hX.2 x (-s) (-t)
    simpa only [GradientDeviation.gradientReverseTimeField,
        GradientDeviation.gradientReverseTimeFlow, zero_sub] using
      hbase.comp_const_sub 0 t

/-- The spatial derivative bound is unchanged by time reversal. -/
theorem GradientDeviation.gradientReverseTimeField_derivBound
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) {L : ℝ}
    (hL : ∀ r y, ‖jointSpatialFDeriv b r y‖ ≤ L) (r : ℝ) (y : Vec 2) :
    ‖jointSpatialFDeriv (GradientDeviation.gradientReverseTimeField b) r y‖ ≤ L := by
  have hbr := GradientDeviation.gradientReverseTimeField_smoothPeriodic hb
  have hL' := hL (-r) y
  have heq : (fun z : Vec 2 => GradientDeviation.gradientReverseTimeField b r z) =
      fun z => -b (-r) z := rfl
  calc
    ‖jointSpatialFDeriv (GradientDeviation.gradientReverseTimeField b) r y‖ =
        ‖fderiv ℝ (fun z => GradientDeviation.gradientReverseTimeField b r z) y‖ := by
          rw [jointSpatialFDeriv_eq_slice hbr]
    _ = ‖-fderiv ℝ (fun z => b (-r) z) y‖ := by
          rw [heq]
          change ‖fderiv ℝ (-(fun z => b (-r) z)) y‖ = _
          rw [fderiv_neg]
    _ = ‖jointSpatialFDeriv b (-r) y‖ := by
          rw [← jointSpatialFDeriv_eq_slice hb]
          simp
    _ ≤ L := hL (-r) y

/-- If the spatial derivative of a smooth periodic field is bounded by `L`,
then the spatial derivative of its forward flow differs from the identity by
at most `exp (L (t-s)) - 1`. -/
theorem flow_fderiv_deviation_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {L : ℝ} (hL_nonneg : 0 ≤ L)
    (hL : ∀ r y, ‖jointSpatialFDeriv b r y‖ ≤ L)
    {s t : ℝ} (hst : s ≤ t) (x : Vec 2) :
    ‖fderiv ℝ (fun y => X t y s) x - 1‖ ≤ Real.exp (L * (t - s)) - 1 := by
  obtain ⟨V, J, hV, hJ, hderiv⟩ :=
    exists_flow_hasFDerivAt_spatial_of_le hb hX x s t hst
  let A : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => jointSpatialFDeriv b r (X r x s)
  let K : ℝ := Real.exp (L * (t - s)) - 1
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    have hz : 0 ≤ L * (t - s) := mul_nonneg hL_nonneg (sub_nonneg.mpr hst)
    exact sub_nonneg.mpr (Real.one_le_exp hz)
  have hdirection (v : Vec 2) :
      ‖(J - (1 : Vec 2 →L[ℝ] Vec 2)) v‖ ≤ K * ‖v‖ := by
    let W : ℝ → Vec 2 := fun r => V r v s - v
    have hW_start : W s = 0 := by
      simp [W, hV.1]
    have hW_cont : ContinuousOn W (Set.Icc s t) :=
      HasDerivAt.continuousOn (fun r _ => by
        simpa [W, linearizedFieldAlongFlow] using (hV.2 v s r).sub_const v)
    have hW_deriv : ∀ r ∈ Set.Ico s t,
        HasDerivWithinAt W (A r (V r v s)) (Set.Ici r) r := by
      intro r hr
      have h := (hV.2 v s r).sub_const v
      simpa [W, A, linearizedFieldAlongFlow] using
        h.hasDerivWithinAt
    have hW_bound : ∀ r ∈ Set.Ico s t,
        ‖A r (V r v s)‖ ≤ L * ‖W r‖ + L * ‖v‖ := by
      intro r hr
      have hdecomp : V r v s = W r + v := by
        simp [W]
      rw [hdecomp, map_add]
      calc
        ‖A r (W r) + A r v‖ ≤ ‖A r (W r)‖ + ‖A r v‖ := norm_add_le _ _
        _ ≤ L * ‖W r‖ + L * ‖v‖ := by
          apply add_le_add
          · exact (A r).le_opNorm (W r) |>.trans
              (mul_le_mul_of_nonneg_right (hL r (X r x s)) (norm_nonneg _))
          · exact (A r).le_opNorm v |>.trans
              (mul_le_mul_of_nonneg_right (hL r (X r x s)) (norm_nonneg _))
    have hgron := norm_le_gronwallBound_of_norm_deriv_right_le
      (δ := 0) (K := L) (ε := L * ‖v‖) (a := s) (b := t)
      hW_cont hW_deriv (by rw [hW_start]; simp) hW_bound
    have hW_at_t : ‖W t‖ ≤ gronwallBound 0 L (L * ‖v‖) (t - s) :=
      hgron t ⟨hst, le_rfl⟩
    have hW_to_K : gronwallBound 0 L (L * ‖v‖) (t - s) = K * ‖v‖ := by
      by_cases hLzero : L = 0
      · simp [hLzero, gronwallBound_K0, K]
      · rw [gronwallBound_of_K_ne_0 hLzero]
        dsimp [K]
        field_simp
        ring
    have hJv : J v = V t v s := hJ v
    calc
      ‖(J - (1 : Vec 2 →L[ℝ] Vec 2)) v‖ = ‖W t‖ := by
        rw [sub_apply, one_apply_eq_self, hJv]
      _ ≤ gronwallBound 0 L (L * ‖v‖) (t - s) := hW_at_t
      _ = K * ‖v‖ := hW_to_K
  have hJ_bound := ContinuousLinearMap.opNorm_le_bound
    (J - (1 : Vec 2 →L[ℝ] Vec 2)) hK_nonneg hdirection
  simpa [hderiv.fderiv, K] using hJ_bound

/-- The exponential first-derivative estimate holds on either side of the
initial time. -/
theorem flow_fderiv_deviation
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {L : ℝ} (hL_nonneg : 0 ≤ L)
    (hL : ∀ r y, ‖jointSpatialFDeriv b r y‖ ≤ L)
    (s t : ℝ) (x : Vec 2) :
    ‖fderiv ℝ (fun y => X t y s) x - 1‖ ≤ Real.exp (L * |t - s|) - 1 := by
  by_cases hst : s ≤ t
  · simpa [abs_of_nonneg (sub_nonneg.mpr hst)] using
      flow_fderiv_deviation_of_le hb hX hL_nonneg hL hst x
  · have hts : t ≤ s := le_of_not_ge hst
    let br := GradientDeviation.gradientReverseTimeField b
    let Xr := GradientDeviation.gradientReverseTimeFlow X
    have hbr : SmoothPeriodicField br := GradientDeviation.gradientReverseTimeField_smoothPeriodic
        hb
    have hXr : AVenhance.IsFlow br Xr := GradientDeviation.gradientReverseTimeFlow_isFlow hX
    have hLr : ∀ r y, ‖jointSpatialFDeriv br r y‖ ≤ L :=
      GradientDeviation.gradientReverseTimeField_derivBound hb hL
    have hforward := flow_fderiv_deviation_of_le hbr hXr hL_nonneg hLr
      (s := -s) (t := -t) (by linarith) x
    have htime : -t - -s = |t - s| := by
      rw [abs_of_nonpos (sub_nonpos.mpr hts)]
      ring
    simpa [br, Xr, GradientDeviation.gradientReverseTimeFlow, htime] using hforward

/-- On the unit exponential scale, `exp(z)-1 ≤ 2z`; this is the linear
small-time form used in (10814)-(10818). -/
theorem flow_fderiv_deviation_of_small_time
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {L : ℝ} (hL_nonneg : 0 ≤ L)
    (hL : ∀ r y, ‖jointSpatialFDeriv b r y‖ ≤ L)
    (s t : ℝ) (x : Vec 2) (ht : L * |t - s| ≤ 1) :
    ‖fderiv ℝ (fun y => X t y s) x - 1‖ ≤ 2 * L * |t - s| := by
  have hdev := flow_fderiv_deviation hb hX hL_nonneg hL s t x
  let z : ℝ := L * |t - s|
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hz_le : |z| ≤ 1 := by
    rw [abs_of_nonneg hz]
    simpa [z] using ht
  have hExp := Real.abs_exp_sub_one_le hz_le
  have hExpNonneg : 0 ≤ Real.exp (L * |t - s|) - 1 := by
    exact sub_nonneg.mpr (Real.one_le_exp (by dsimp [z] at hz ⊢; exact hz))
  calc
    ‖fderiv ℝ (fun y => X t y s) x - 1‖ ≤
        Real.exp (L * |t - s|) - 1 := hdev
    _ = |Real.exp (L * |t - s|) - 1| := (abs_of_nonneg hExpNonneg).symm
    _ ≤ 2 * |z| := by simpa [z] using hExp
    _ = 2 * L * |t - s| := by rw [abs_of_nonneg hz]; dsimp [z]; ring

/-- The gradient-deviation estimate in (10814)-(10818), once the seminorm
hypothesis has been converted to the pointwise derivative bound
`‖Dₓb‖ ≤ d C_f R_f / 4`. -/
theorem flow_fderiv_deviation_paper_bound
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {d : ℕ} {C_f R_f : ℝ} (hd : 1 ≤ d) (hCf : 0 < C_f) (hRf : 0 < R_f)
    (hDb : ∀ r y, ‖jointSpatialFDeriv b r y‖ ≤ (d : ℝ) * C_f * R_f / 4)
    {t : ℝ} (ht : |t| ≤ 1 / (4 * (d : ℝ) * C_f * R_f)) (x : Vec 2) :
    ‖fderiv ℝ (fun y => X t y 0) x - 1‖ ≤ (d : ℝ) * C_f * R_f * |t| ∧
      (d : ℝ) * C_f * R_f * |t| ≤ 1 / 4 := by
  let L : ℝ := (d : ℝ) * C_f * R_f / 4
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hd)
  have hLpos : 0 < L := by dsimp [L]; positivity
  have hLnonneg : 0 ≤ L := hLpos.le
  let A : ℝ := (d : ℝ) * C_f * R_f
  have hApos : 0 < A := by dsimp [A]; positivity
  have hdenEq : 4 * A = 4 * (d : ℝ) * C_f * R_f := by dsimp [A]; ring
  have htA : |t| ≤ 1 / (4 * A) := by rw [hdenEq]; exact ht
  have hprod : A * |t| ≤ 1 / 4 := by
    calc
      A * |t| ≤ A * (1 / (4 * A)) := mul_le_mul_of_nonneg_left htA hApos.le
      _ = 1 / 4 := by
        dsimp [A]
        field_simp
  have htL : L * |t| ≤ 1 := by
    dsimp [L]
    dsimp [A] at hprod
    nlinarith
  have hsmall := flow_fderiv_deviation_of_small_time hb hX hLnonneg
    (by simpa [L] using hDb) 0 t x (by simpa using htL)
  have htarget : 2 * L * |t| ≤ A * |t| := by
    dsimp [L]
    dsimp [A]
    have hnonneg : 0 ≤ (d : ℝ) * C_f * R_f * |t| := by positivity
    nlinarith
  constructor
  · have hsmall' : ‖fderiv ℝ (fun y => X t y 0) x - 1‖ ≤ 2 * L * |t| := by
      simpa using hsmall
    calc
      _ ≤ A * |t| := hsmall'.trans htarget
      _ = (d : ℝ) * C_f * R_f * |t| := by rfl
  · simpa [A] using hprod

/-- Convert the paper's order-one seminorm hypothesis for a smooth Vec 2
field into the pointwise spatial derivative bound used in (10814)-(10818). -/
theorem jointSpatialFDeriv_bound_of_snorm
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {C_f R_f : ℝ} (hCf : 0 < C_f) (hRf : 0 < R_f)
    (hs : ∀ r, AVenhance.FaaDiBruno.snorm (b r) 1 R_f ≤ ENNReal.ofReal C_f) :
    ∀ r y, ‖jointSpatialFDeriv b r y‖ ≤ (2 : ℝ) * C_f * R_f / 4 := by
  intro r y
  let f : Vec 2 → Vec 2 := b r
  have hf : ContDiff ℝ 1 f := by
    have hspace : ContDiff ℝ ∞ (fun x : Vec 2 => (r, x)) := by fun_prop
    exact (hb.smooth.comp hspace).of_le (by simp)
  rw [jointSpatialFDeriv_eq_slice hb]
  exact AVenhance.FaaDiBruno.fderiv_norm_le_of_snorm_one_le f hf hRf
    (le_of_lt hCf) (hs r) y

/-- The gradient estimate in Proposition `p.ODE.flow` (10811)-(10825), with the
paper's seminorm assumption supplying the derivative bound. -/
theorem flow_fderiv_deviation_of_snorm
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {C_f R_f : ℝ} (hCf : 0 < C_f) (hRf : 0 < R_f)
    (hs : ∀ r, AVenhance.FaaDiBruno.snorm (b r) 1 R_f ≤ ENNReal.ofReal C_f)
    {t : ℝ} (ht : |t| ≤ 1 / (4 * 2 * C_f * R_f)) (x : Vec 2) :
    ‖fderiv ℝ (fun y => X t y 0) x - 1‖ ≤ (2 : ℝ) * C_f * R_f * |t| ∧
      (2 : ℝ) * C_f * R_f * |t| ≤ 1 / 4 := by
  have hDb := jointSpatialFDeriv_bound_of_snorm hb hCf hRf hs
  exact flow_fderiv_deviation_paper_bound hb hX (d := 2) (by norm_num)
    hCf hRf hDb ht x

end AVenhance.Infra.Flow

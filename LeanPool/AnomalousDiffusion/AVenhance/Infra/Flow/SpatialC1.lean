/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FieldTaylor
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Estimates
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FlowIntegral
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.VariationalEquation
public import Mathlib.Analysis.ODE.Gronwall

/-! Spatial differentiability of a characterized smooth periodic flow. -/

@[expose] public section

open Homogenization
open Filter Set
open scoped ContDiff NNReal Topology

namespace AVenhance.Infra.Flow

theorem SpatialC1.gronwallBound_zero_scale (L a c d : ℝ) :
    gronwallBound 0 L (c * a) d = c * gronwallBound 0 L a d := by
  by_cases hL : L = 0
  · simp [gronwallBound, hL]
    ring
  · simp [gronwallBound, hL]
    ring

/-- The nonlinear trajectory differs from its variational approximation by a
quadratic amount in the initial displacement, for forward time. -/
theorem flow_variational_quadratic_remainder_all_times_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2}
    (x : Vec 2) (s t : ℝ) (hst : s ≤ t)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ r, r ∈ Icc s t → ∀ h,
        ‖X r (x + h) s - X r x s - V r h s‖ ≤ C * ‖h‖ * ‖h‖ := by
  obtain ⟨L, hL₀, hL⟩ := exists_global_spatial_lipschitz hb
  obtain ⟨M, hM₀, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  obtain ⟨T, hT₀, hT⟩ := exists_global_smoothPeriodicField_taylor_remainder hb
  let A : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => jointSpatialFDeriv b r (X r x s)
  have hAL : ∀ r u v, ‖A r u - A r v‖ ≤ M * ‖u - v‖ := by
    intro r u v
    calc
      ‖A r u - A r v‖ = ‖A r (u - v)‖ := by rw [map_sub]
      _ ≤ ‖A r‖ * ‖u - v‖ := (A r).le_opNorm _
      _ ≤ M * ‖u - v‖ := mul_le_mul_of_nonneg_right (hM r (X r x s)) (norm_nonneg _)
  let E : ℝ := Real.exp (M * (t - s))
  let B : ℝ := T * E * E
  let K : ℝ≥0 := ⟨L, hL₀⟩
  have hLip : ∀ r, LipschitzWith K (b r) := by
    intro r
    apply LipschitzWith.of_dist_le_mul
    intro u v
    change dist (b r u) (b r v) ≤ L * dist u v
    rw [dist_eq_norm, dist_eq_norm]
    exact hL r u v
  let Q : ℝ := gronwallBound 0 L 1 (t - s)
  have hQ₀ : 0 ≤ Q := by
    have hmono := gronwallBound_mono (show 0 ≤ (0 : ℝ) by norm_num)
      (show 0 ≤ (1 : ℝ) by norm_num) hL₀
    have hq := hmono (show 0 ≤ t - s by linarith)
    simpa [Q, gronwallBound_x0] using hq
  have hB₀ : 0 ≤ B := mul_nonneg (mul_nonneg hT₀ (Real.exp_pos _).le) (Real.exp_pos _).le
  have hD₀ : 0 ≤ Q * B := mul_nonneg hQ₀ hB₀
  refine ⟨Q * B, hD₀, ?_⟩
  intro r hr h
  let ε : ℝ := B * ‖h‖ * ‖h‖
  have hVzero (r : ℝ) : V r 0 s = 0 :=
    linearSystemFlow_zero A M hAL hV s r
  have hVbound (r : ℝ) (hr : r ∈ Ico s t) : ‖V r h s‖ ≤ E * ‖h‖ := by
    have hgr := flow_spatial_gronwall (fun q v => A q v) hAL hV h 0 s r
    have hexp : Real.exp (M * |r - s|) ≤ E := by
      apply Real.exp_le_exp.mpr
      calc
        M * |r - s| = M * (r - s) := by
          rw [abs_of_nonneg (sub_nonneg.mpr hr.1)]
        _ ≤ M * (t - s) := mul_le_mul_of_nonneg_left (by linarith [hr.2]) hM₀
    calc
      ‖V r h s‖ = ‖V r h s - V r 0 s‖ := by rw [hVzero r, sub_zero]
      _ ≤ Real.exp (M * |r - s|) * ‖h - 0‖ := hgr
      _ = Real.exp (M * |r - s|) * ‖h‖ := by simp
      _ ≤ E * ‖h‖ := mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  let f : ℝ → Vec 2 := fun r => X r (x + h) s
  let g : ℝ → Vec 2 := fun r => X r x s + V r h s
  have hfderiv (r : ℝ) : HasDerivAt f (b r (f r)) r := by
    simpa [f] using hX.2 (x + h) s r
  have hgderiv (r : ℝ) : HasDerivAt g
      (b r (X r x s) + A r (V r h s)) r := by
    have hsum := (hX.2 x s r).add (hV.2 h s r)
    convert hsum using 1
    ext q
    rfl
  have hfcont : ContinuousOn f (Icc s t) :=
    HasDerivAt.continuousOn (fun r _ => hfderiv r)
  have hgcont : ContinuousOn g (Icc s t) :=
    HasDerivAt.continuousOn (fun r _ => hgderiv r)
  have hfwithin : ∀ r ∈ Ico s t,
      HasDerivWithinAt f (b r (f r)) (Ici r) r :=
    fun r _ => (hfderiv r).hasDerivWithinAt
  have hgwithin : ∀ r ∈ Ico s t,
      HasDerivWithinAt g (b r (X r x s) + A r (V r h s)) (Ici r) r :=
    fun r _ => (hgderiv r).hasDerivWithinAt
  have hfapprox : ∀ r ∈ Ico s t, dist (b r (f r)) (b r (f r)) ≤ (0 : ℝ) := by
    intro r hr
    simp
  have hgapprox : ∀ r ∈ Ico s t,
      dist (b r (X r x s) + A r (V r h s)) (b r (g r)) ≤ ε := by
    intro r hr
    have hTaylor := hT r (X r x s) (X r x s + V r h s)
    have hSlice := jointSpatialFDeriv_eq_slice hb r (X r x s)
    have hTaylor' :
        ‖b r (X r x s + V r h s) - b r (X r x s) -
            fderiv ℝ (fun y => b r y) (X r x s) (V r h s)‖ ≤
          T * ‖V r h s‖ * ‖V r h s‖ := by
      simpa using hTaylor
    have hrem :
        dist (b r (X r x s) + A r (V r h s))
          (b r (X r x s + V r h s)) =
        ‖b r (X r x s + V r h s) - b r (X r x s) -
            fderiv ℝ (fun y => b r y) (X r x s) (V r h s)‖ := by
      rw [dist_eq_norm]
      have hA : A r (V r h s) =
          fderiv ℝ (fun y => b r y) (X r x s) (V r h s) := by
        dsimp [A]
        rw [hSlice]
      rw [hA]
      have hneg : b r (X r x s) +
          fderiv ℝ (fun y => b r y) (X r x s) (V r h s) -
          b r (X r x s + V r h s) =
          -(b r (X r x s + V r h s) - b r (X r x s) -
            fderiv ℝ (fun y => b r y) (X r x s) (V r h s)) := by
        abel_nf
      rw [hneg, norm_neg]
    rw [hrem]
    calc
      _ ≤ T * ‖V r h s‖ * ‖V r h s‖ := hTaylor'
      _ ≤ T * (E * ‖h‖) * ‖V r h s‖ := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left (hVbound r hr) hT₀
        · exact norm_nonneg _
      _ ≤ T * (E * ‖h‖) * (E * ‖h‖) := by
        apply mul_le_mul_of_nonneg_left (hVbound r hr)
        exact mul_nonneg hT₀ (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      _ = ε := by
        simp [ε, B, E]
        ring
  have hstart : dist (f s) (g s) ≤ 0 := by
    simp [f, g, hX.1, hV.1]
  have hcomp := dist_le_of_approx_trajectories_ODE (K := K) (v := b)
    (a := s) (b := t) hLip hfcont hfwithin hfapprox hgcont hgwithin hgapprox hstart
  have hdist := hcomp r hr
  rw [dist_eq_norm] at hdist
  have hfg : f r - g r = X r (x + h) s - X r x s - V r h s := by
    dsimp [f, g]
    abel
  rw [hfg] at hdist
  have hK : (K : ℝ) = L := rfl
  rw [hK] at hdist
  have hdist' : ‖X r (x + h) s - X r x s - V r h s‖ ≤
      gronwallBound 0 L ε (r - s) := by
    simpa only [zero_add] using hdist
  have hε₀ : 0 ≤ ε := mul_nonneg (mul_nonneg hB₀ (norm_nonneg h)) (norm_nonneg h)
  have htime : r - s ≤ t - s := by linarith [hr.2]
  have hmono := gronwallBound_mono (show 0 ≤ (0 : ℝ) by norm_num) hε₀ hL₀
  calc
    ‖X r (x + h) s - X r x s - V r h s‖ ≤
        gronwallBound 0 L ε (r - s) := hdist'
    _ ≤ gronwallBound 0 L ε (t - s) := hmono htime
    _ = ε * Q := by
      calc
        gronwallBound 0 L ε (t - s) =
            gronwallBound 0 L (ε * 1) (t - s) := by
          exact congrArg (fun e : ℝ => gronwallBound 0 L e (t - s)) (by ring)
        _ = ε * gronwallBound 0 L 1 (t - s) :=
          SpatialC1.gronwallBound_zero_scale L 1 ε (t - s)
        _ = ε * Q := by rfl
    _ = (Q * B) * ‖h‖ * ‖h‖ := by
      simp [ε, B]
      ring

/-- The nonlinear trajectory differs from its variational approximation by a
quadratic amount at a fixed target time, as a consequence of the uniform
forward-interval estimate. -/
theorem flow_variational_quadratic_remainder_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2}
    (x : Vec 2) (s t : ℝ) (hst : s ≤ t)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ h, ‖X t (x + h) s - X t x s - V t h s‖ ≤ C * ‖h‖ * ‖h‖ := by
  obtain ⟨C, hC₀, hC⟩ := flow_variational_quadratic_remainder_all_times_of_le
    hb hX x s t hst hV
  exact ⟨C, hC₀, fun h => hC t ⟨hst, le_rfl⟩ h⟩

/-- The spatial flow map is Fréchet differentiable at every point for forward
time, with derivative given by the variational flow. -/
theorem exists_flow_hasFDerivAt_spatial_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s t : ℝ) (hst : s ≤ t) :
    ∃ V : ℝ → Vec 2 → ℝ → Vec 2, ∃ J : Vec 2 →L[ℝ] Vec 2,
      AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V ∧
      (∀ v, J v = V t v s) ∧ HasFDerivAt (fun y => X t y s) J x := by
  obtain ⟨M, hM₀, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  obtain ⟨V, hV, _⟩ := existsUnique_flow_variationalEquation hb hX x s
  obtain ⟨J, hJ⟩ := exists_flow_variationalContinuousLinearMap
    (fun r => jointSpatialFDeriv b r (X r x s))
    M (fun r => hM r (X r x s)) hV t s
  obtain ⟨C, hC₀, hC⟩ := flow_variational_quadratic_remainder_of_le hb hX x
    (s := s) (t := t) hst hV
  have hderiv : HasFDerivAt (fun y => X t y s) J x := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro ε hε
    let δ : ℝ := ε / (C + 1)
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    have hδnorm : ‖(0 : Vec 2)‖ < δ := by simpa using hδ
    filter_upwards
      [(continuous_norm.continuousAt.tendsto).eventually (Iio_mem_nhds hδnorm)] with h hh
    have hcoef : C * ‖h‖ ≤ ε := by
      calc
        C * ‖h‖ ≤ C * δ := mul_le_mul_of_nonneg_left hh.le hC₀
        _ ≤ ε := by
          calc
            C * (ε / (C + 1)) = (C * ε) / (C + 1) := by ring
            _ ≤ ε := (div_le_iff₀ (by positivity)).2 <| by
              nlinarith [mul_nonneg hC₀ hε.le]
    calc
      ‖X t (x + h) s - X t x s - J h‖ ≤ C * ‖h‖ * ‖h‖ := by
        rw [hJ h]
        exact hC h
      _ ≤ ε * ‖h‖ := by
        exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
  exact ⟨V, J, hV, hJ, hderiv⟩

/-- Time reversal preserves smooth joint periodicity. -/
def SpatialC1.reverseTimeField (b : ℝ → Vec 2 → Vec 2) : ℝ → Vec 2 → Vec 2 :=
  fun t x => -b (-t) x

/-- Flow with observation and starting times both reversed. -/
def SpatialC1.reverseTimeFlow (X : ℝ → Vec 2 → ℝ → Vec 2) :
    ℝ → Vec 2 → ℝ → Vec 2 :=
  fun t x s => X (-t) x (-s)

theorem SpatialC1.smoothPeriodicField_reverseTime
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) :
    SmoothPeriodicField (SpatialC1.reverseTimeField b) := by
  refine ⟨?_, ?_⟩
  · change ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => -Function.uncurry b (-p.1, p.2))
    have hmap : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => (-p.1, p.2)) := by fun_prop
    exact contDiff_neg.comp (hb.smooth.comp hmap)
  · intro m k t x
    have h := hb.periodic (-m) k (-t) x
    simpa [SpatialC1.reverseTimeField, neg_add, add_comm] using congrArg Neg.neg h

theorem SpatialC1.isFlow_reverseTime
    {b : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hX : AVenhance.IsFlow b X) :
    AVenhance.IsFlow (SpatialC1.reverseTimeField b) (SpatialC1.reverseTimeFlow X) := by
  constructor
  · intro x s
    exact hX.1 x (-s)
  · intro x s t
    have hbase : HasDerivAt (fun r => X r x (-s))
        (b (0 - t) (X (0 - t) x (-s))) (0 - t) := by
      simpa only [zero_sub] using hX.2 x (-s) (-t)
    simpa only [SpatialC1.reverseTimeField, SpatialC1.reverseTimeFlow, zero_sub] using
      hbase.comp_const_sub 0 t

/-- Spatial differentiability holds at arbitrary target and initial times.
The derivative is the unique variational flow along the characterized
trajectory. -/
theorem exists_flow_hasFDerivAt_spatial
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s t : ℝ) :
    ∃ V : ℝ → Vec 2 → ℝ → Vec 2, ∃ J : Vec 2 →L[ℝ] Vec 2,
      AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V ∧
      (∀ v, J v = V t v s) ∧ HasFDerivAt (fun y => X t y s) J x := by
  by_cases hst : s ≤ t
  · exact exists_flow_hasFDerivAt_spatial_of_le hb hX x s t hst
  · have hts : t ≤ s := le_of_not_ge hst
    let br := SpatialC1.reverseTimeField b
    let Xr := SpatialC1.reverseTimeFlow X
    have hbr : SmoothPeriodicField br := SpatialC1.smoothPeriodicField_reverseTime hb
    have hXr : AVenhance.IsFlow br Xr := SpatialC1.isFlow_reverseTime hX
    obtain ⟨V, hV, hVunique⟩ := existsUnique_flow_variationalEquation hb hX x s
    obtain ⟨Vr, Jr, hVr, hJr, hderivR⟩ :=
      exists_flow_hasFDerivAt_spatial_of_le hbr hXr x (-s) (-t) (by linarith)
    have hcoeff : ∀ u v,
        linearizedFieldAlongFlow br Xr x (-s) u v =
          -jointSpatialFDeriv b (-u) (X (-u) x s) v := by
      intro u v
      have hbrslice := jointSpatialFDeriv_eq_slice hbr u (X (-u) x s)
      have hbslice := jointSpatialFDeriv_eq_slice hb (-u) (X (-u) x s)
      dsimp [linearizedFieldAlongFlow, Xr, SpatialC1.reverseTimeFlow]
      simp only [neg_neg]
      change jointSpatialFDeriv br u (X (-u) x s) v = _
      rw [hbrslice, hbslice]
      simp [br, SpatialC1.reverseTimeField]
    let W : ℝ → Vec 2 → ℝ → Vec 2 := fun u v r => V (-u) v (-r)
    have hW : AVenhance.IsFlow (linearizedFieldAlongFlow br Xr x (-s)) W := by
      constructor
      · intro v r
        have hv := hV.1 v (-r)
        simpa [W] using hv
      · intro v r u
        have hbase : HasDerivAt (fun q => V q v (-r))
            (jointSpatialFDeriv b (0 - u) (X (0 - u) x s)
              (V (0 - u) v (-r))) (0 - u) := by
          simpa [linearizedFieldAlongFlow, zero_sub] using hV.2 v (-r) (-u)
        have hrev := hbase.comp_const_sub 0 u
        simpa only [W, zero_sub, hcoeff] using hrev
    obtain ⟨Vrev, hVrev, hVrevUnique⟩ :=
      existsUnique_flow_variationalEquation hbr hXr x (-s)
    have hVrEq : Vr = Vrev := hVrevUnique Vr hVr
    have hWEq : W = Vrev := hVrevUnique W hW
    have hJ : ∀ v, Jr v = V t v s := by
      intro v
      calc
        Jr v = Vr (-t) v (-s) := hJr v
        _ = Vrev (-t) v (-s) := by rw [hVrEq]
        _ = W (-t) v (-s) := by rw [hWEq]
        _ = V t v s := by simp [W]
    have hderiv : HasFDerivAt (fun y => X t y s) Jr x := by
      simpa [Xr, SpatialC1.reverseTimeFlow] using hderivR
    exact ⟨V, Jr, hV, hJ, hderiv⟩

end AVenhance.Infra.Flow

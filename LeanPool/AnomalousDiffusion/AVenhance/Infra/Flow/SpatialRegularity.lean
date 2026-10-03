/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SpatialC1
public import Mathlib.Analysis.ODE.Gronwall

/-! Continuity of the spatial derivative of a smooth periodic flow. -/

@[expose] public section

open Homogenization
open Set
open scoped ContDiff NNReal Topology

namespace AVenhance.Infra.Flow

theorem SpatialRegularity.gronwallBound_zero_scale_regular (L a c d : ℝ) :
    gronwallBound 0 L (c * a) d = c * gronwallBound 0 L a d := by
  by_cases hL : L = 0
  · simp [gronwallBound, hL]
    ring
  · simp [gronwallBound, hL]
    ring

/-- The variational derivative depends Lipschitz continuously on the base
point over a forward time interval. -/
theorem exists_flow_spatialFDeriv_lipschitz_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s t : ℝ) (hst : s ≤ t) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y,
      ∃ Jx Jy : Vec 2 →L[ℝ] Vec 2,
        HasFDerivAt (fun z => X t z s) Jx x ∧
        HasFDerivAt (fun z => X t z s) Jy y ∧
        ‖Jx - Jy‖ ≤ K * ‖x - y‖ := by
  obtain ⟨L, hL₀, hL⟩ := exists_global_spatial_lipschitz hb
  obtain ⟨M, hM₀, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  obtain ⟨C, hC₀, hC⟩ := exists_global_spatialFDeriv_lipschitz hb
  let d : ℝ := t - s
  let F : ℝ := Real.exp (L * d)
  let E : ℝ := Real.exp (M * d)
  let D : ℝ := C * F * E
  let K : ℝ := gronwallBound 0 M D d
  have hd₀ : 0 ≤ d := by dsimp [d]; linarith
  have hF₀ : 0 ≤ F := (Real.exp_pos _).le
  have hE₀ : 0 ≤ E := (Real.exp_pos _).le
  have hD₀ : 0 ≤ D := mul_nonneg (mul_nonneg hC₀ hF₀) hE₀
  have hK₀ : 0 ≤ K := by
    have hmono := gronwallBound_mono
      (show 0 ≤ (0 : ℝ) by norm_num) hD₀ hM₀
    have h := hmono (show 0 ≤ d by exact hd₀)
    simpa [K, gronwallBound_x0] using h
  refine ⟨K, hK₀, ?_⟩
  intro x y
  obtain ⟨Vx, Jx, hVx, hJx, hDx⟩ :=
    exists_flow_hasFDerivAt_spatial_of_le hb hX x s t hst
  obtain ⟨Vy, Jy, hVy, hJy, hDy⟩ :=
    exists_flow_hasFDerivAt_spatial_of_le hb hX y s t hst
  have hAxLip : ∀ r u v,
      ‖jointSpatialFDeriv b r (X r x s) u -
        jointSpatialFDeriv b r (X r x s) v‖ ≤ M * ‖u - v‖ := by
    intro r u v
    rw [← map_sub]
    exact ((jointSpatialFDeriv b r (X r x s)).le_opNorm (u - v)).trans
      (mul_le_mul_of_nonneg_right (hM r (X r x s)) (norm_nonneg _))
  let A : ℝ → Vec 2 → Vec 2 :=
    fun r v => jointSpatialFDeriv b r (X r x s) v
  have hTraj : ∀ r ∈ Icc s t, ‖X r x s - X r y s‖ ≤ F * ‖x - y‖ := by
    intro r hr
    have hgr := flow_spatial_gronwall b hL hX x y s r
    have hexp : Real.exp (L * |r - s|) ≤ F := by
      apply Real.exp_le_exp.mpr
      dsimp [F, d]
      rw [abs_of_nonneg (sub_nonneg.mpr hr.1)]
      exact mul_le_mul_of_nonneg_left (by linarith [hr.2]) hL₀
    exact hgr.trans (mul_le_mul_of_nonneg_right hexp (norm_nonneg _))
  have hCoeff : ∀ r ∈ Icc s t, ‖jointSpatialFDeriv b r (X r y s) -
      jointSpatialFDeriv b r (X r x s)‖ ≤ C * F * ‖x - y‖ := by
    intro r hr
    calc
      ‖jointSpatialFDeriv b r (X r y s) -
          jointSpatialFDeriv b r (X r x s)‖ ≤
          C * ‖X r y s - X r x s‖ := by
            simpa only [norm_sub_rev] using hC r (X r x s) (X r y s)
      _ ≤ C * (F * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left
            (by simpa only [norm_sub_rev] using hTraj r hr) hC₀
      _ = C * F * ‖x - y‖ := by ring
  let Kₙ : ℝ≥0 := ⟨M, hM₀⟩
  have hALip : ∀ r, LipschitzWith Kₙ (A r) := by
    intro r
    apply LipschitzWith.of_dist_le_mul
    intro u v
    change dist (A r u) (A r v) ≤ M * dist u v
    rw [dist_eq_norm, dist_eq_norm]
    exact hAxLip r u v
  have hdir : ∀ v, ‖Jx v - Jy v‖ ≤ K * ‖x - y‖ * ‖v‖ := by
    intro v
    have hvY (r : ℝ) (hr : r ∈ Ico s t) : ‖Vy r v s‖ ≤ E * ‖v‖ := by
      have hzero := linearSystemFlow_zero
        (fun q => jointSpatialFDeriv b q (X q y s)) M
        (fun q u w => by
          rw [← map_sub]
          exact ((jointSpatialFDeriv b q (X q y s)).le_opNorm (u - w)).trans
            (mul_le_mul_of_nonneg_right (hM q (X q y s)) (norm_nonneg _))) hVy s r
      have hgr := flow_spatial_gronwall
        (fun q w => jointSpatialFDeriv b q (X q y s) w)
        (fun q u w => by
          rw [← map_sub]
          exact ((jointSpatialFDeriv b q (X q y s)).le_opNorm (u - w)).trans
            (mul_le_mul_of_nonneg_right (hM q (X q y s)) (norm_nonneg _)))
        hVy v 0 s r
      have hexp : Real.exp (M * |r - s|) ≤ E := by
        apply Real.exp_le_exp.mpr
        dsimp [E, d]
        rw [abs_of_nonneg (sub_nonneg.mpr hr.1)]
        exact mul_le_mul_of_nonneg_left (by linarith [hr.2]) hM₀
      calc
        ‖Vy r v s‖ = ‖Vy r v s - Vy r 0 s‖ := by rw [hzero, sub_zero]
        _ ≤ Real.exp (M * |r - s|) * ‖v - 0‖ := hgr
        _ ≤ E * ‖v‖ := by simpa using mul_le_mul_of_nonneg_right hexp (norm_nonneg v)
    let fx : ℝ → Vec 2 := fun r => Vx r v s
    let gy : ℝ → Vec 2 := fun r => Vy r v s
    have hfxd (r : ℝ) : HasDerivAt fx (A r (fx r)) r := by
      simpa [fx, A, linearizedFieldAlongFlow] using hVx.2 v s r
    have hgyd (r : ℝ) : HasDerivAt gy
        (jointSpatialFDeriv b r (X r y s) (gy r)) r := by
      simpa [gy, linearizedFieldAlongFlow] using hVy.2 v s r
    have hfxcont : ContinuousOn fx (Icc s t) :=
      HasDerivAt.continuousOn (fun r _ => hfxd r)
    have hgycont : ContinuousOn gy (Icc s t) :=
      HasDerivAt.continuousOn (fun r _ => hgyd r)
    have hfxwithin : ∀ r ∈ Ico s t,
        HasDerivWithinAt fx (A r (fx r)) (Ici r) r :=
      fun r _ => (hfxd r).hasDerivWithinAt
    have hgywithin : ∀ r ∈ Ico s t,
        HasDerivWithinAt gy
          (jointSpatialFDeriv b r (X r y s) (gy r)) (Ici r) r :=
      fun r _ => (hgyd r).hasDerivWithinAt
    have hfxapprox : ∀ r ∈ Ico s t, dist (A r (fx r)) (A r (fx r)) ≤ (0 : ℝ) := by
      intro r hr
      simp
    have hgyapprox : ∀ r ∈ Ico s t,
        dist (jointSpatialFDeriv b r (X r y s) (gy r)) (A r (gy r)) ≤
          D * ‖x - y‖ * ‖v‖ := by
      intro r hr
      rw [dist_eq_norm]
      calc
        ‖jointSpatialFDeriv b r (X r y s) (gy r) - A r (gy r)‖ ≤
            ‖jointSpatialFDeriv b r (X r y s) -
              jointSpatialFDeriv b r (X r x s)‖ * ‖gy r‖ := by
                calc
                  _ = ‖(jointSpatialFDeriv b r (X r y s) -
                      jointSpatialFDeriv b r (X r x s)) (gy r)‖ := by
                        simp [A]
                  _ ≤ _ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (C * F * ‖x - y‖) * (E * ‖v‖) :=
              mul_le_mul (hCoeff r ⟨hr.1, le_of_lt hr.2⟩) (hvY r hr)
                (norm_nonneg _) (by positivity)
        _ = D * ‖x - y‖ * ‖v‖ := by simp [D]; ring
    have hstartv : dist (fx s) (gy s) ≤ (0 : ℝ) := by
      simp [fx, gy, hVx.1, hVy.1]
    have hvcomp := dist_le_of_approx_trajectories_ODE (K := Kₙ) (v := A)
      (a := s) (b := t) hALip hfxcont hfxwithin hfxapprox hgycont hgywithin
      hgyapprox hstartv
    have hvdiff : ‖Vx t v s - Vy t v s‖ ≤
        gronwallBound 0 M (D * ‖x - y‖ * ‖v‖) (t - s) := by
      have h := hvcomp t ⟨hst, le_rfl⟩
      have hKcast : (Kₙ : ℝ) = M := rfl
      simpa only [fx, gy, dist_eq_norm, hKcast, zero_add] using h
    have hscale : gronwallBound 0 M (D * ‖x - y‖ * ‖v‖) d =
        (‖x - y‖ * ‖v‖) * K := by
      rw [show D * ‖x - y‖ * ‖v‖ = (‖x - y‖ * ‖v‖) * D by ring]
      rw [SpatialRegularity.gronwallBound_zero_scale_regular M D (‖x - y‖ * ‖v‖) d]
    calc
      ‖Jx v - Jy v‖ = ‖Vx t v s - Vy t v s‖ := by rw [hJx v, hJy v]
      _ ≤ (‖x - y‖ * ‖v‖) * K := by
        calc
          _ ≤ gronwallBound 0 M (D * ‖x - y‖ * ‖v‖) (t - s) := hvdiff
          _ = (‖x - y‖ * ‖v‖) * K := by simpa [d] using hscale
      _ = K * ‖x - y‖ * ‖v‖ := by ring
  have hnorm : ‖Jx - Jy‖ ≤ K * ‖x - y‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK₀ (norm_nonneg _))
    intro v
    simpa only [sub_apply] using hdir v
  exact ⟨Jx, Jy, hDx, hDy, hnorm⟩

/-- The spatial derivative of a forward flow map is continuous in the initial
position. -/
theorem flow_spatialFDeriv_continuous_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s t : ℝ) (hst : s ≤ t) :
    Continuous (fun x => fderiv ℝ (fun y => X t y s) x) := by
  obtain ⟨K, hK₀, hK⟩ := exists_flow_spatialFDeriv_lipschitz_of_le hb hX s t hst
  let F : Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun x => fderiv ℝ (fun y => X t y s) x
  have hLip : ∀ x y, dist (F x) (F y) ≤ K * dist x y := by
    intro x y
    obtain ⟨Jx, Jy, hDx, hDy, hbound⟩ := hK x y
    have hDx' : F x = Jx := hDx.fderiv
    have hDy' : F y = Jy := hDy.fderiv
    rw [hDx', hDy', dist_eq_norm, dist_eq_norm]
    exact hbound
  have hLF : LipschitzWith ⟨K, hK₀⟩ F :=
    LipschitzWith.of_dist_le_mul hLip
  exact hLF.continuous

/-- Reverse-time vector field used in the spatial regularity argument. -/
def regularityReverseTimeField (b : ℝ → Vec 2 → Vec 2) :
    ℝ → Vec 2 → Vec 2 := fun t x => -b (-t) x

/-- Reverse-time flow used in the spatial regularity argument. -/
def regularityReverseTimeFlow (X : ℝ → Vec 2 → ℝ → Vec 2) :
    ℝ → Vec 2 → ℝ → Vec 2 := fun t x s => X (-t) x (-s)

theorem smoothPeriodicField_regularityReverseTime
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) :
    SmoothPeriodicField (regularityReverseTimeField b) := by
  refine ⟨?_, ?_⟩
  · change ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => -Function.uncurry b (-p.1, p.2))
    have hmap : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => (-p.1, p.2)) := by fun_prop
    exact contDiff_neg.comp (hb.smooth.comp hmap)
  · intro m k t x
    have h := hb.periodic (-m) k (-t) x
    simpa [regularityReverseTimeField, neg_add, add_comm] using congrArg Neg.neg h

theorem isFlow_regularityReverseTime
    {b : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hX : AVenhance.IsFlow b X) :
    AVenhance.IsFlow (regularityReverseTimeField b) (regularityReverseTimeFlow X) := by
  constructor
  · intro x s
    exact hX.1 x (-s)
  · intro x s t
    have hbase : HasDerivAt (fun r => X r x (-s))
        (b (0 - t) (X (0 - t) x (-s))) (0 - t) := by
      simpa only [zero_sub] using hX.2 x (-s) (-t)
    simpa only [regularityReverseTimeField, regularityReverseTimeFlow, zero_sub] using
      hbase.comp_const_sub 0 t

/-- The spatial derivative of a characterized smooth flow is continuous in
the initial position for arbitrary target and initial times. -/
theorem flow_spatialFDeriv_continuous
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s t : ℝ) :
    Continuous (fun x => fderiv ℝ (fun y => X t y s) x) := by
  by_cases hst : s ≤ t
  · exact flow_spatialFDeriv_continuous_of_le hb hX s t hst
  · have hts : t ≤ s := le_of_not_ge hst
    let br := regularityReverseTimeField b
    let Xr := regularityReverseTimeFlow X
    have hbr : SmoothPeriodicField br := smoothPeriodicField_regularityReverseTime hb
    have hXr : AVenhance.IsFlow br Xr := isFlow_regularityReverseTime hX
    have hcont := flow_spatialFDeriv_continuous_of_le hbr hXr (-s) (-t) (by linarith)
    simpa [Xr, regularityReverseTimeFlow] using hcont

/-- For fixed times, the spatial flow map is continuously differentiable, and
its derivative is the variational flow. -/
theorem flow_spatial_contDiff_one
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s t : ℝ) : ContDiff ℝ 1 (fun x => X t x s) := by
  rw [contDiff_one_iff_fderiv]
  constructor
  · intro x
    obtain ⟨V, J, hV, hJ, hD⟩ := exists_flow_hasFDerivAt_spatial hb hX x s t
    exact hD.differentiableAt
  · exact flow_spatialFDeriv_continuous hb hX s t

end AVenhance.Infra.Flow

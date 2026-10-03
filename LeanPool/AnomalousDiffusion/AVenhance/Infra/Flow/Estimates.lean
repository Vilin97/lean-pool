/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Flow.IsFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.CurveUniqueness
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.Analysis.ODE.Gronwall

/-! Grönwall and displacement estimates for characterized global flows. -/

@[expose] public section

open Homogenization
open scoped NNReal

namespace AVenhance.Infra.Flow

/-- The real constant in a global Lipschitz estimate is nonnegative when the
estimate holds on the nontrivial space `Vec 2`. -/
theorem lipschitz_constant_nonneg
    (b : ℝ → Vec 2 → Vec 2) {L : ℝ}
    (hL : ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖) : 0 ≤ L := by
  by_contra h
  have hneg : L < 0 := lt_of_not_ge h
  let e : Vec 2 := fun _ => 1
  have he : e ≠ 0 := by
    intro he
    have h0 := congrFun he ⟨0, by decide⟩
    norm_num [e] at h0
  have hnorm : 0 < ‖(0 : Vec 2) - e‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (by
      intro hzero
      apply he
      exact hzero.symm))
  have hbound := hL 0 0 e
  have hnonneg : 0 ≤ L * ‖(0 : Vec 2) - e‖ :=
    (norm_nonneg _).trans hbound
  have hnegative : L * ‖(0 : Vec 2) - e‖ < 0 := mul_neg_of_neg_of_pos hneg hnorm
  exact (not_lt_of_ge hnonneg) hnegative

/-- Grönwall's spatial stability estimate when the target time is not before
the initial time. -/
theorem flow_spatial_gronwall_of_le
    (b : ℝ → Vec 2 → Vec 2)
    {L : ℝ} (hL : ∀ u x y, ‖b u x - b u y‖ ≤ L * ‖x - y‖)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x y : Vec 2) (s t : ℝ) (hst : s ≤ t) :
    ‖X t x s - X t y s‖ ≤ Real.exp (L * (t - s)) * ‖x - y‖ := by
  have hL0 := lipschitz_constant_nonneg b hL
  let K : ℝ≥0 := ⟨L, hL0⟩
  have hLip : ∀ u, LipschitzWith K (b u) := by
    intro u
    apply LipschitzWith.of_dist_le_mul
    intro a c
    change dist (b u a) (b u c) ≤ L * dist a c
    rw [dist_eq_norm, dist_eq_norm]
    exact hL u a c
  have hfx : ContinuousOn (fun u => X u x s) (Set.Icc s t) :=
    HasDerivAt.continuousOn (fun u _ => hX.2 x s u)
  have hfy : ContinuousOn (fun u => X u y s) (Set.Icc s t) :=
    HasDerivAt.continuousOn (fun u _ => hX.2 y s u)
  have hdx : ∀ u ∈ Set.Ico s t,
      HasDerivWithinAt (fun v => X v x s) (b u (X u x s)) (Set.Ici u) u :=
    fun u _ => (hX.2 x s u).hasDerivWithinAt
  have hdy : ∀ u ∈ Set.Ico s t,
      HasDerivWithinAt (fun v => X v y s) (b u (X u y s)) (Set.Ici u) u :=
    fun u _ => (hX.2 y s u).hasDerivWithinAt
  have hstart : dist (X s x s) (X s y s) ≤ dist x y := by
    rw [hX.1, hX.1]
  have hbound := dist_le_of_trajectories_ODE (K := K) (v := b)
    (a := s) (b := t) hLip hfx hdx hfy hdy hstart t ⟨hst, le_rfl⟩
  have hK : (K : ℝ) = L := rfl
  rw [dist_eq_norm, dist_eq_norm] at hbound
  calc
    ‖X t x s - X t y s‖ ≤ ‖x - y‖ * Real.exp (L * (t - s)) := by
      simpa only [hK] using hbound
    _ = Real.exp (L * (t - s)) * ‖x - y‖ := mul_comm _ _

/-- Grönwall's spatial stability estimate at arbitrary times. -/
theorem flow_spatial_gronwall
    (b : ℝ → Vec 2 → Vec 2)
    {L : ℝ} (hL : ∀ u x y, ‖b u x - b u y‖ ≤ L * ‖x - y‖)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x y : Vec 2) (s t : ℝ) :
    ‖X t x s - X t y s‖ ≤ Real.exp (L * |t - s|) * ‖x - y‖ := by
  by_cases hst : s ≤ t
  · simpa [abs_of_nonneg (sub_nonneg.mpr hst)] using
      flow_spatial_gronwall_of_le b hL hX x y s t hst
  · have hts : t ≤ s := le_of_not_ge hst
    let br : ℝ → Vec 2 → Vec 2 := fun u z => -b (-u) z
    let xr : ℝ → Vec 2 → ℝ → Vec 2 := fun u z v => X (-u) z (-v)
    have hLr : ∀ u a c, ‖br u a - br u c‖ ≤ L * ‖a - c‖ := by
      intro u a c
      simpa only [br, neg_sub_neg, norm_neg, norm_sub_rev] using hL (-u) a c
    have hXr : AVenhance.IsFlow br xr := by
      constructor
      · intro z v
        exact hX.1 z (-v)
      · intro z v u
        have hbase : HasDerivAt (fun r => X r z (-v))
            (b (0 - u) (X (0 - u) z (-v))) (0 - u) := by
          simpa only [zero_sub] using hX.2 z (-v) (-u)
        simpa only [br, xr, zero_sub] using hbase.comp_const_sub 0 u
    have hrev := flow_spatial_gronwall_of_le br hLr hXr x y (-s) (-t)
      (by linarith)
    have habs : |t - s| = s - t := by
      rw [abs_of_nonpos (sub_nonpos.mpr hts)]
      ring
    have hrev' : ‖X t x s - X t y s‖ ≤
        Real.exp (L * ((-t) - (-s))) * ‖x - y‖ := by
      simpa only [xr, neg_neg] using hrev
    calc
      ‖X t x s - X t y s‖ ≤ Real.exp (L * ((-t) - (-s))) * ‖x - y‖ := hrev'
      _ = Real.exp (L * (s - t)) * ‖x - y‖ := by congr 1; ring_nf
      _ = Real.exp (L * |t - s|) * ‖x - y‖ := by rw [habs]

end AVenhance.Infra.Flow

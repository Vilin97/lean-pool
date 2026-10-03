/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FiniteSpatialJetBounds
public import Mathlib.Analysis.ODE.Gronwall

/-! Joint continuity of finite recursive jet flows on compact windows. -/

@[expose] public section

open Homogenization
open Filter Set
open scoped NNReal Topology

namespace AVenhance.Infra.Flow

noncomputable section

/-- On a compact time window and a bounded set of initial jet states, the
finite jet flow is Lipschitz in its initial state, with a constant depending
on the window and the bounded trajectory tube. -/
theorem spatialJetFlow_dist_le_on_window
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlowOn b X)
    (n : ℕ) (a d s : ℝ) (hs : s ∈ Icc a d) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ≥0, ∀ (t : ℝ), t ∈ Icc a d → ∀ z w : SpatialJetState n,
      ‖z‖ ≤ R → ‖w‖ ≤ R →
        dist (spatialJetFlow hb X hX n t z s)
          (spatialJetFlow hb X hX n t w s) ≤
            dist z w * Real.exp ((K : ℝ) * |t - s|) := by
  obtain ⟨C, hC0, hC⟩ := spatialJetFlow_bounded_on_window hb hX n a d s R hR
  obtain ⟨K, hK⟩ := spatialJetField_lipschitzOnWith_on_window hb n a d 0 C
  refine ⟨K, ?_⟩
  intro t ht z w hz hw
  let Y := spatialJetFlow hb X hX n
  have hY : IsFlowOn (spatialJetField b n) Y := spatialJetFlow_isFlow hb hX n
  have hmem (r : ℝ) (hr : r ∈ Icc a d) (y : SpatialJetState n)
      (hy : ‖y‖ ≤ R) : Y r y s ∈ Metric.closedBall (0 : SpatialJetState n) C := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hC r hr y hy
  have hYcont (y : SpatialJetState n) : ContinuousOn (fun r => Y r y s) (Icc a d) := by
    exact HasDerivAt.continuousOn (fun r _ => hY.2 y s r)
  have hYwithin (y : SpatialJetState n) (r : ℝ) (hr : r ∈ Ico a d) :
      HasDerivWithinAt (fun q => Y q y s)
        (spatialJetField b n r (Y r y s)) (Ici r) r :=
    (hY.2 y s r).hasDerivWithinAt
  by_cases hst : s ≤ t
  · let f : ℝ → SpatialJetState n := fun r => Y r z s
    let g : ℝ → SpatialJetState n := fun r => Y r w s
    have hLip : ∀ r ∈ Ico s t,
        LipschitzOnWith K (spatialJetField b n r)
          (Metric.closedBall (0 : SpatialJetState n) C) := by
      intro r hr
      exact hK r ⟨le_trans hs.1 hr.1, (le_of_lt hr.2).trans ht.2⟩
    have hf : ContinuousOn f (Icc s t) :=
      (hYcont z).mono (Icc_subset_Icc hs.1 ht.2)
    have hg : ContinuousOn g (Icc s t) :=
      (hYcont w).mono (Icc_subset_Icc hs.1 ht.2)
    have hf' : ∀ r ∈ Ico s t,
        HasDerivWithinAt f (spatialJetField b n r (f r)) (Ici r) r := by
      intro r hr
      exact hYwithin z r ⟨le_trans hs.1 hr.1, hr.2.trans_le ht.2⟩
    have hg' : ∀ r ∈ Ico s t,
        HasDerivWithinAt g (spatialJetField b n r (g r)) (Ici r) r := by
      intro r hr
      exact hYwithin w r ⟨le_trans hs.1 hr.1, hr.2.trans_le ht.2⟩
    have hfs : ∀ r ∈ Ico s t, f r ∈ Metric.closedBall (0 : SpatialJetState n) C := by
      intro r hr
      exact hmem r ⟨le_trans hs.1 hr.1, (le_of_lt hr.2).trans ht.2⟩ z hz
    have hgs : ∀ r ∈ Ico s t, g r ∈ Metric.closedBall (0 : SpatialJetState n) C := by
      intro r hr
      exact hmem r ⟨le_trans hs.1 hr.1, (le_of_lt hr.2).trans ht.2⟩ w hw
    have hstart : dist (f s) (g s) ≤ dist z w := by
      simp [f, g, hY.1]
    have hdist := dist_le_of_trajectories_ODE_of_mem hLip hf hf' hfs hg hg' hgs
      hstart t ⟨hst, le_rfl⟩
    simpa [f, g, abs_of_nonneg (sub_nonneg.mpr hst)] using hdist
  · have hts : t ≤ s := le_of_not_ge hst
    let endTime : ℝ := 2 * s - t
    have hend : s ≤ endTime := by dsimp [endTime]; linarith
    let f : ℝ → SpatialJetState n := fun q => Y (2 * s - q) z s
    let g : ℝ → SpatialJetState n := fun q => Y (2 * s - q) w s
    let F : ℝ → SpatialJetState n → SpatialJetState n :=
      fun q y => -spatialJetField b n (2 * s - q) y
    have htimeMap (q : ℝ) (hq : q ∈ Icc s endTime) :
        2 * s - q ∈ Icc a d := by
      have hq' := hq
      simp only [mem_Icc] at hq'
      constructor
      · have hleft : t ≤ 2 * s - q := by linarith [hq'.2]
        exact le_trans ht.1 hleft
      · have hright : 2 * s - q ≤ s := by linarith [hq'.1]
        exact le_trans hright hs.2
    have hLip : ∀ q ∈ Ico s endTime,
        LipschitzOnWith K (F q) (Metric.closedBall (0 : SpatialJetState n) C) := by
      intro q hq
      have hu := htimeMap q ⟨hq.1, hq.2.le⟩
      have h := hK (2 * s - q) hu
      apply LipschitzOnWith.of_dist_le_mul
      intro u hu v hv
      change dist (-spatialJetField b n (2 * s - q) u)
        (-spatialJetField b n (2 * s - q) v) ≤ (K : ℝ) * dist u v
      calc
        dist (-spatialJetField b n (2 * s - q) u)
            (-spatialJetField b n (2 * s - q) v) =
          dist (spatialJetField b n (2 * s - q) u)
            (spatialJetField b n (2 * s - q) v) := dist_neg_neg _ _
        _ ≤ (K : ℝ) * dist u v := h.dist_le_mul u hu v hv
    have hderivF (q : ℝ) : HasDerivAt f (F q (f q)) q := by
      have hbase := hY.2 z s (2 * s - q)
      have hrev := hbase.comp_const_sub (2 * s) q
      simpa [f, F, mul_assoc, mul_comm, mul_left_comm] using hrev
    have hderivG (q : ℝ) : HasDerivAt g (F q (g q)) q := by
      have hbase := hY.2 w s (2 * s - q)
      have hrev := hbase.comp_const_sub (2 * s) q
      simpa [g, F, mul_assoc, mul_comm, mul_left_comm] using hrev
    have hf : ContinuousOn f (Icc s endTime) :=
      HasDerivAt.continuousOn (fun q _ => hderivF q)
    have hg : ContinuousOn g (Icc s endTime) :=
      HasDerivAt.continuousOn (fun q _ => hderivG q)
    have hf' : ∀ q ∈ Ico s endTime,
        HasDerivWithinAt f (F q (f q)) (Ici q) q :=
      fun q _ => (hderivF q).hasDerivWithinAt
    have hg' : ∀ q ∈ Ico s endTime,
        HasDerivWithinAt g (F q (g q)) (Ici q) q :=
      fun q _ => (hderivG q).hasDerivWithinAt
    have hfs : ∀ q ∈ Ico s endTime, f q ∈ Metric.closedBall (0 : SpatialJetState n) C := by
      intro q hq
      exact hmem (2 * s - q) (htimeMap q ⟨hq.1, hq.2.le⟩) z hz
    have hgs : ∀ q ∈ Ico s endTime, g q ∈ Metric.closedBall (0 : SpatialJetState n) C := by
      intro q hq
      exact hmem (2 * s - q) (htimeMap q ⟨hq.1, hq.2.le⟩) w hw
    have hfstart : f s = z := by
      calc
        f s = Y s z s := by
          change Y (2 * s - s) z s = Y s z s
          congr 1
          ring
        _ = z := hY.1 z s
    have hgstart : g s = w := by
      calc
        g s = Y s w s := by
          change Y (2 * s - s) w s = Y s w s
          congr 1
          ring
        _ = w := hY.1 w s
    have hstart : dist (f s) (g s) ≤ dist z w := by
      rw [hfstart, hgstart]
    have hdist := dist_le_of_trajectories_ODE_of_mem hLip hf hf' hfs hg hg' hgs
      hstart endTime ⟨hend, le_rfl⟩
    have htarget : f endTime = Y t z s := by simp [f, endTime]
    have htarget' : g endTime = Y t w s := by simp [g, endTime]
    have htime : endTime - s = |t - s| := by
      dsimp [endTime]
      rw [abs_of_nonpos (sub_nonpos.mpr hts)]
      ring
    simpa [htarget, htarget', htime] using hdist

/-- The target-time and initial-state map of each finite recursive jet flow
is continuous when the initial time is fixed. -/
theorem spatialJetFlow_continuous_fixed_start
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlowOn b X)
    (n : ℕ) (s : ℝ) :
    Continuous (fun p : ℝ × SpatialJetState n =>
      spatialJetFlow hb X hX n p.1 p.2 s) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  rcases p with ⟨t, z⟩
  change Tendsto (fun q : ℝ × SpatialJetState n =>
      spatialJetFlow hb X hX n q.1 q.2 s)
    (𝓝 (t, z)) (𝓝 (spatialJetFlow hb X hX n t z s))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  let a : ℝ := min s t - 1
  let d : ℝ := max s t + 1
  let R : ℝ := ‖z‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hs : s ∈ Icc a d := by
    constructor
    · dsimp [a]
      linarith [min_le_left s t]
    · dsimp [d]
      linarith [le_max_left s t]
  have ht : t ∈ Icc a d := by
    constructor
    · dsimp [a]
      linarith [min_le_right s t]
    · dsimp [d]
      linarith [le_max_right s t]
  obtain ⟨K, hK⟩ := spatialJetFlow_dist_le_on_window hb hX n a d s hs R hR
  let A : ℝ × SpatialJetState n → ℝ := fun q =>
    Real.exp ((K : ℝ) * |q.1 - s|)
  let B : ℝ × SpatialJetState n → ℝ := fun q => ‖q.2 - z‖
  let C : ℝ × SpatialJetState n → ℝ := fun q =>
    ‖spatialJetFlow hb X hX n q.1 z s - spatialJetFlow hb X hX n t z s‖
  have hAT : Tendsto A (𝓝 (t, z)) (𝓝 (Real.exp ((K : ℝ) * |t - s|))) := by
    exact (show ContinuousAt A (t, z) from by fun_prop).tendsto
  have hBT : Tendsto B (𝓝 (t, z)) (𝓝 0) := by
    have h := (show ContinuousAt B (t, z) from by fun_prop).tendsto
    simpa [B] using h
  have hCT : Tendsto C (𝓝 (t, z)) (𝓝 0) := by
    have htproj : Tendsto (fun q : ℝ × SpatialJetState n => q.1)
        (𝓝 (t, z)) (𝓝 t) := continuous_fst.continuousAt.tendsto
    have htime : Tendsto (fun q : ℝ × SpatialJetState n =>
        spatialJetFlow hb X hX n q.1 z s)
        (𝓝 (t, z)) (𝓝 (spatialJetFlow hb X hX n t z s)) := by
      exact ((HasDerivAt.continuousAt
        ((spatialJetFlow_isFlow hb hX n).2 z s t)).tendsto).comp htproj
    have hsub : Tendsto (fun q : ℝ × SpatialJetState n =>
        spatialJetFlow hb X hX n q.1 z s - spatialJetFlow hb X hX n t z s)
        (𝓝 (t, z)) (𝓝 0) := by
      have hsub' : Tendsto (fun q : ℝ × SpatialJetState n =>
          spatialJetFlow hb X hX n q.1 z s - spatialJetFlow hb X hX n t z s)
          (𝓝 (t, z))
          (𝓝 (spatialJetFlow hb X hX n t z s - spatialJetFlow hb X hX n t z s)) :=
        htime.sub tendsto_const_nhds
      simpa using hsub'
    have hnorm := continuous_norm.continuousAt.tendsto.comp hsub
    simpa [C, Function.comp_def] using hnorm
  have hsum : Tendsto (fun q => A q * B q + C q) (𝓝 (t, z)) (𝓝 0) := by
    simpa using (hAT.mul hBT).add hCT
  have hnear (q : ℝ × SpatialJetState n)
      (hqtime : q.1 ∈ Icc a d) (hqstate : ‖q.2‖ ≤ R) :
      ‖spatialJetFlow hb X hX n q.1 q.2 s -
        spatialJetFlow hb X hX n t z s‖ ≤ A q * B q + C q := by
    calc
      _ ≤ ‖spatialJetFlow hb X hX n q.1 q.2 s -
          spatialJetFlow hb X hX n q.1 z s‖ + C q := by
            calc
              _ = ‖(spatialJetFlow hb X hX n q.1 q.2 s -
                    spatialJetFlow hb X hX n q.1 z s) +
                    (spatialJetFlow hb X hX n q.1 z s -
                    spatialJetFlow hb X hX n t z s)‖ := by congr 1; abel
              _ ≤ _ := norm_add_le _ _
      _ ≤ dist (spatialJetFlow hb X hX n q.1 q.2 s)
          (spatialJetFlow hb X hX n q.1 z s) + C q := by rw [dist_eq_norm]
      _ ≤ ‖q.2 - z‖ * Real.exp ((K : ℝ) * |q.1 - s|) + C q := by
        have hsp := hK q.1 hqtime q.2 z hqstate (by
          dsimp [R]
          linarith [norm_nonneg z])
        calc
          dist (spatialJetFlow hb X hX n q.1 q.2 s)
              (spatialJetFlow hb X hX n q.1 z s) + C q ≤
              dist q.2 z * Real.exp ((K : ℝ) * |q.1 - s|) + C q :=
            calc
              _ = C q + dist (spatialJetFlow hb X hX n q.1 q.2 s)
                    (spatialJetFlow hb X hX n q.1 z s) := by ring
              _ ≤ C q + dist q.2 z * Real.exp ((K : ℝ) * |q.1 - s|) :=
                add_le_add_right hsp (C q)
              _ = _ := by ring
          _ = ‖q.2 - z‖ * Real.exp ((K : ℝ) * |q.1 - s|) + C q := by
            rw [dist_eq_norm]
      _ = A q * B q + C q := by simp [A, B, mul_comm]
  have hlocal : ∀ᶠ q : ℝ × SpatialJetState n in 𝓝 (t, z),
      ‖spatialJetFlow hb X hX n q.1 q.2 s -
        spatialJetFlow hb X hX n t z s‖ ≤ A q * B q + C q := by
    have htimeEvent : ∀ᶠ q : ℝ × SpatialJetState n in 𝓝 (t, z),
        q.1 ∈ Icc a d :=
      (continuous_fst.continuousAt.tendsto).eventually
        (Icc_mem_nhds (by dsimp [a]; linarith [min_le_right s t])
          (by dsimp [d]; linarith [le_max_right s t]))
    have hstateEvent : ∀ᶠ q : ℝ × SpatialJetState n in 𝓝 (t, z),
        q.2 ∈ Metric.closedBall z 1 :=
      (continuous_snd.continuousAt.tendsto).eventually
        (Metric.closedBall_mem_nhds z (by norm_num : (0 : ℝ) < 1))
    filter_upwards [htimeEvent, hstateEvent] with q hqt hqz
    exact hnear q hqt (by
      dsimp [R]
      have hzdist : ‖q.2 - z‖ ≤ 1 := by
        rw [← dist_eq_norm]
        exact Metric.mem_closedBall.mp hqz
      calc
        ‖q.2‖ ≤ ‖q.2 - z‖ + ‖z‖ := by
          calc ‖q.2‖ = ‖(q.2 - z) + z‖ := by congr 1; abel
            _ ≤ _ := norm_add_le _ _
        _ ≤ 1 + ‖z‖ := by gcongr
        _ = ‖z‖ + 1 := by ring)
  apply squeeze_zero' (Filter.Eventually.of_forall fun q => norm_nonneg _) hlocal hsum

end

end AVenhance.Infra.Flow

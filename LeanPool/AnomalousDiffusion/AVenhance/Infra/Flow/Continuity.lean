/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Flow.IsFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Estimates
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Laws

/-! Joint continuity follows from curve continuity, the flow law, and the
spatial Grönwall estimate. -/

@[expose] public section

open Homogenization
open Filter
open scoped Topology

namespace AVenhance.Infra.Flow

/-- For a fixed initial time, the flow is jointly continuous in target time
and initial position. -/
theorem flow_continuous_fixed_start
    (b : ℝ → Vec 2 → Vec 2)
    {L : ℝ} (hL : ∀ u x y, ‖b u x - b u y‖ ≤ L * ‖x - y‖)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s : ℝ) : Continuous (fun p : ℝ × Vec 2 => X p.1 p.2 s) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  rcases p with ⟨t, x⟩
  change Tendsto (fun q : ℝ × Vec 2 => X q.1 q.2 s)
    (𝓝 (t, x)) (𝓝 (X t x s))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  let A : ℝ × Vec 2 → ℝ := fun q => Real.exp (L * |q.1 - s|)
  let B : ℝ × Vec 2 → ℝ := fun q => ‖q.2 - x‖
  let C : ℝ × Vec 2 → ℝ := fun q => ‖X q.1 x s - X t x s‖
  have hAT : Tendsto A (𝓝 (t, x)) (𝓝 (Real.exp (L * |t - s|))) := by
    exact (show ContinuousAt A (t, x) from by fun_prop).tendsto
  have hBT : Tendsto B (𝓝 (t, x)) (𝓝 0) := by
    have h := (show ContinuousAt B (t, x) from by fun_prop).tendsto
    simpa [B] using h
  have hCT : Tendsto C (𝓝 (t, x)) (𝓝 0) := by
    have ht : Tendsto (fun q : ℝ × Vec 2 => q.1) (𝓝 (t, x)) (𝓝 t) :=
      continuous_fst.continuousAt.tendsto
    have htime : Tendsto (fun q : ℝ × Vec 2 => X q.1 x s)
        (𝓝 (t, x)) (𝓝 (X t x s)) :=
      ((flow_continuous_time b hX x s).continuousAt.tendsto).comp ht
    simpa [C] using (tendsto_iff_norm_sub_tendsto_zero).mp htime
  have hsum : Tendsto (fun q : ℝ × Vec 2 => A q * B q + C q)
      (𝓝 (t, x)) (𝓝 0) := by
    simpa using (hAT.mul hBT).add hCT
  apply squeeze_zero (fun q => norm_nonneg _)
  · intro q
    calc
      ‖X q.1 q.2 s - X t x s‖ ≤
          ‖X q.1 q.2 s - X q.1 x s‖ + ‖X q.1 x s - X t x s‖ := by
            simpa only [dist_eq_norm] using
              (dist_triangle (X q.1 q.2 s) (X q.1 x s) (X t x s))
      _ ≤ A q * B q + C q := by
        have hsp := flow_spatial_gronwall b hL hX q.2 x s q.1
        calc
          _ ≤ Real.exp (L * |q.1 - s|) * ‖q.2 - x‖ +
              ‖X q.1 x s - X t x s‖ := add_le_add hsp (le_of_eq rfl)
          _ = A q * B q + C q := by rfl
  · exact hsum

/-- A globally characterized flow is jointly continuous in target time,
initial position, and initial time. -/
theorem flow_continuous_joint
    (b : ℝ → Vec 2 → Vec 2)
    {L : ℝ} (hL : ∀ u x y, ‖b u x - b u y‖ ≤ L * ‖x - y‖)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    Continuous (fun p : ℝ × Vec 2 × ℝ => X p.1 p.2.1 p.2.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  rcases p with ⟨t, x, s⟩
  let q : ℝ × Vec 2 × ℝ → Vec 2 := fun w => X s w.2.1 w.2.2
  let r : ℝ × Vec 2 × ℝ → Vec 2 := fun w => X w.2.2 w.2.1 s
  let E : ℝ × Vec 2 × ℝ → ℝ := fun w => Real.exp (L * |s - w.2.2|)
  let D : ℝ × Vec 2 × ℝ → ℝ := fun w => ‖w.2.1 - r w‖
  let V : ℝ × Vec 2 × ℝ → Vec 2 := fun w => X w.1 (q w) s
  let P : ℝ × Vec 2 × ℝ → Vec 2 := fun w => X w.1 w.2.1 w.2.2
  have ht : Tendsto (fun w : ℝ × Vec 2 × ℝ => w.1)
      (𝓝 (t, x, s)) (𝓝 t) :=
    (show ContinuousAt (fun w : ℝ × Vec 2 × ℝ => w.1) (t, x, s) from by fun_prop).tendsto
  have hx : Tendsto (fun w : ℝ × Vec 2 × ℝ => w.2.1)
      (𝓝 (t, x, s)) (𝓝 x) :=
    (show ContinuousAt (fun w : ℝ × Vec 2 × ℝ => w.2.1) (t, x, s) from by fun_prop).tendsto
  have hs : Tendsto (fun w : ℝ × Vec 2 × ℝ => w.2.2)
      (𝓝 (t, x, s)) (𝓝 s) :=
    (show ContinuousAt (fun w : ℝ × Vec 2 × ℝ => w.2.2) (t, x, s) from by fun_prop).tendsto
  have hxs : Tendsto (fun w : ℝ × Vec 2 × ℝ => (w.2.2, w.2.1))
      (𝓝 (t, x, s)) (𝓝 (s, x)) := by
    simpa only [nhds_prod_eq] using hs.prodMk hx
  have hfixed := flow_continuous_fixed_start b hL hX s
  have hr : Tendsto r (𝓝 (t, x, s)) (𝓝 x) := by
    have hfixedAt := (continuous_iff_continuousAt.mp hfixed) (s, x)
    have hcomp := hfixedAt.tendsto.comp hxs
    simpa [r, Function.comp_def, hX.1] using hcomp
  have hE : Tendsto E (𝓝 (t, x, s)) (𝓝 1) := by
    have h := (show ContinuousAt E (t, x, s) from by fun_prop).tendsto
    simpa [E] using h
  have hD : Tendsto D (𝓝 (t, x, s)) (𝓝 0) := by
    have hvec : Tendsto (fun w : ℝ × Vec 2 × ℝ => w.2.1 - r w)
        (𝓝 (t, x, s)) (𝓝 (0 : Vec 2)) := by
      simpa using hx.sub hr
    have hnorm := continuous_norm.continuousAt.tendsto.comp hvec
    simpa [D, Function.comp_def] using hnorm
  have hED : Tendsto (fun w : ℝ × Vec 2 × ℝ => E w * D w)
      (𝓝 (t, x, s)) (𝓝 0) := by
    simpa using hE.mul hD
  have hQclose : Tendsto (fun w : ℝ × Vec 2 × ℝ => ‖q w - w.2.1‖)
      (𝓝 (t, x, s)) (𝓝 0) := by
    apply squeeze_zero (fun w => norm_nonneg _)
    · intro w
      have hgroup := flow_group_law b ⟨L, hL⟩ hX w.2.1 s w.2.2 s
      have hsp := flow_spatial_gronwall b hL hX w.2.1 (r w) w.2.2 s
      have hbase : X s (r w) w.2.2 = w.2.1 := by
        calc
          X s (r w) w.2.2 = X s (X w.2.2 w.2.1 s) w.2.2 := rfl
          _ = X s w.2.1 s := hgroup
          _ = w.2.1 := hX.1 w.2.1 s
      calc
        ‖q w - w.2.1‖ = ‖X s w.2.1 w.2.2 - X s (r w) w.2.2‖ := by
          rw [hbase]
        _ ≤ E w * D w := by simpa [E, D, q, r] using hsp
    · exact hED
  have hq : Tendsto q (𝓝 (t, x, s)) (𝓝 x) := by
    have hdiff : Tendsto (fun w : ℝ × Vec 2 × ℝ => q w - w.2.1)
        (𝓝 (t, x, s)) (𝓝 (0 : Vec 2)) := by
      exact (tendsto_iff_norm_sub_tendsto_zero).2 (by simpa using hQclose)
    simpa using hdiff.add hx
  have hVP : V = P := by
    funext w
    exact flow_group_law b ⟨L, hL⟩ hX w.2.1 w.2.2 s w.1
  have hPair : Tendsto (fun w : ℝ × Vec 2 × ℝ => (w.1, q w))
      (𝓝 (t, x, s)) (𝓝 (t, x)) := by
    simpa only [nhds_prod_eq] using ht.prodMk hq
  have hfixedAt := (continuous_iff_continuousAt.mp hfixed) (t, x)
  have hcomp := hfixedAt.tendsto.comp hPair
  change Tendsto P (𝓝 (t, x, s)) (𝓝 (X t x s))
  rw [← hVP]
  simpa [V, Function.comp_def] using hcomp

end AVenhance.Infra.Flow

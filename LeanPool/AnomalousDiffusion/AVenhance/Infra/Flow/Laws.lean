/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Flow.IsFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsZ2Periodic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.CurveUniqueness
public import Mathlib.Analysis.ODE.Transform

/-! Algebraic consequences of the global flow characterization. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Flow

/-- The global Lipschitz hypothesis makes an integral curve unique from one value. -/
theorem flow_eq_of_isFlow
    (b : ℝ → Vec 2 → Vec 2)
    (hL : ∃ L : ℝ, ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖)
    {X Y : ℝ → Vec 2 → ℝ → Vec 2}
    (hX : AVenhance.IsFlow b X) (hY : AVenhance.IsFlow b Y) : X = Y := by
  rcases hL with ⟨L, hL⟩
  funext t
  funext x
  funext s
  have hcurves := integralCurve_unique b hL (fun r => hX.2 x s r)
    (fun r => hY.2 x s r) (s := s) (by rw [hX.1, hY.1])
  exact congrFun hcurves t

/-- Flow maps compose according to their time parameters. -/
theorem flow_group_law
    (b : ℝ → Vec 2 → Vec 2)
    (hL : ∃ L : ℝ, ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s r t : ℝ) : X t (X r x s) r = X t x s := by
  rcases hL with ⟨L, hL⟩
  have h₀ : X r (X r x s) r = X r x s := hX.1 (X r x s) r
  have hcurves := integralCurve_unique b hL
    (fun u => hX.2 (X r x s) r u) (fun u => hX.2 x s u) (s := r) h₀
  exact congrFun hcurves t

/-- Spatial lattice equivariance of a flow for a lattice-periodic vector field. -/
theorem flow_lattice_equivariant
    (b : ℝ → Vec 2 → Vec 2)
    (hL : ∃ L : ℝ, ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖)
    (hPeriodic : ∀ t, AVenhance.IsZ2Periodic (b t))
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s t : ℝ) (k : Fin 2 → ℤ) :
    X t (x + AVenhance.latticeShift k) s = X t x s + AVenhance.latticeShift k := by
  rcases hL with ⟨L, hL⟩
  let z := AVenhance.latticeShift k
  have hshift (u : ℝ) :
      HasDerivAt (fun r => X r x s + z) (b u (X u x s + z)) u := by
    simpa only [Function.comp_def, z, hPeriodic u k (X u x s)] using
      (hX.2 x s u).add_const z
  have hstart : X s (x + z) s = (X s x s) + z := by rw [hX.1, hX.1]
  have hcurves := integralCurve_unique b hL
    (fun u => hX.2 (x + z) s u) hshift (s := s) hstart
  exact congrFun hcurves t

/-- Shifting both time arguments by one preserves a flow of a one-periodic field. -/
theorem flow_time_shift_one
    (b : ℝ → Vec 2 → Vec 2)
    (hL : ∃ L : ℝ, ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖)
    (hPeriodic : ∀ t x, b (t + 1) x = b t x)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s t : ℝ) : X (t + 1) x (s + 1) = X t x s := by
  rcases hL with ⟨L, hL⟩
  have hshift (u : ℝ) :
      HasDerivAt (fun r => X (r + 1) x (s + 1))
        (b u (X (u + 1) x (s + 1))) u := by
    simpa only [Function.comp_def, hPeriodic u (X (u + 1) x (s + 1))] using
      (hX.2 x (s + 1) (u + 1)).comp_add_const u 1
  have hstart : X (s + 1) x (s + 1) = X s x s := by rw [hX.1, hX.1]
  have hcurves := integralCurve_unique b hL hshift (fun u => hX.2 x s u)
    (s := s) hstart
  exact congrFun hcurves t

/-- Every time slice of a global flow is continuous in the target time. -/
theorem flow_continuous_time
    (b : ℝ → Vec 2 → Vec 2)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s : ℝ) : Continuous (fun t => X t x s) := by
  exact continuous_iff_continuousAt.mpr (fun t => (hX.2 x s t).continuousAt)

end AVenhance.Infra.Flow

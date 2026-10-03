/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportSolution.GradientMatrix

/-! # Characteristics

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ContDiff NNReal Topology

noncomputable section

namespace AVenhance.FaaDiBruno

/-- Along a characterized flow trajectory, a classical transport solution
has derivative equal to the source evaluated on that trajectory. -/
theorem transportSolution_hasDerivAt_alongFlow
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s t : ℝ) :
    HasDerivAt (fun r => Y r (X r x s)) (g t (X t x s)) t := by
  let γ : ℝ → ℝ × Vec 2 := fun r => (r, X r x s)
  have hγ : HasDerivAt γ (1, b t (X t x s)) t := by
    exact (hasDerivAt_id t).prodMk (hX.2 x s t)
  have hcomp := (hY.smooth.differentiable (by simp) (t, X t x s)).hasFDerivAt
    |>.comp t hγ
  have heq := hY.equation t (X t x s)
  simpa [γ, Function.comp_def, Function.uncurry, heq] using hcomp.hasDerivAt

/-- Along each flow characteristic, every finite ordered spatial derivative
of a classical transport solution evolves by the recursively differentiated
source above. -/
theorem transportIteratedSpatialJet_hasDerivAt_alongFlow
    {b g Y : ℝ → Vec 2 → Vec 2}
    (I : List (Vec 2))
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s t : ℝ) :
    HasDerivAt
      (fun r => transportSpatialJet I (Function.uncurry Y) (r, X r x s))
      (transportSourceJet I b g Y (t, X t x s)) t := by
  let hbase : IsSmoothClassicalTransportSolution b g Y := ⟨hY, hg⟩
  have hjet := transportSolution_iteratedDirectionalDerivative_isSmoothSolution
    I hbase hb
  have hchar := transportSolution_hasDerivAt_alongFlow hjet.toIsClassicalTransportSolution
    hX x s t
  simpa [Function.curry] using hchar

/-- The characteristic integral formula for a classical transport solution,
valid on every oriented finite time interval. -/
theorem transportSolution_intervalIntegral_alongFlow
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s t : ℝ) :
    Y t (X t x s) - Y s (X s x s) =
      ∫ r in s..t, g r (X r x s) := by
  let F : ℝ → Vec 2 := fun r => Y r (X r x s)
  let G : ℝ → Vec 2 := fun r => g r (X r x s)
  have hXcont : Continuous fun r => X r x s :=
    continuous_iff_continuousAt.mpr fun r => (hX.2 x s r).continuousAt
  have hGcont : Continuous G := by
    exact hg.continuous.comp (continuous_id.prodMk hXcont)
  have hGint : IntervalIntegrable G volume s t := hGcont.intervalIntegrable s t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := s) (b := t)
    (fun r _ => transportSolution_hasDerivAt_alongFlow hY hX x s r) hGint
  simpa [F, G] using hFTC.symm

end AVenhance.FaaDiBruno

end

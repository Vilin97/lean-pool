/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.FlowTransportTest
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointSmoothFromFixedStart

/-! # RelativeError: full smoothness of the inverse-flow transported test -/

@[expose] public section

noncomputable section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance

/-- A smooth initial scalar transported by the inverse flow remains jointly
smooth in time and space. This supplies the regularity needed by the integrated
parabolic/transport pairing identity. -/
theorem inverseFlowTransportTest_contDiff_infty
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    {h₀ : Vec 2 → ℝ} (hh₀ : ContDiff ℝ (⊤ : ℕ∞) h₀) :
    ContDiff ℝ (⊤ : ℕ∞)
      (Function.uncurry (inverseFlowTransportTest (h₀ := h₀) X)) := by
  let P : ℝ × Vec 2 → Vec 2 := fun p => X 0 p.2 p.1
  have hflow : ContDiff ℝ (⊤ : ℕ∞) P := by
    have hInv := Infra.Flow.flow_inverse_joint_contDiff_infty hb hX
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => (p.1, p.2, (0 : ℝ))) := by
      fun_prop
    change ContDiff ℝ (⊤ : ℕ∞)
      ((fun q : ℝ × Vec 2 × ℝ => X q.2.2 q.2.1 q.1) ∘
        fun p : ℝ × Vec 2 => (p.1, p.2, (0 : ℝ)))
    exact hInv.comp hmap
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ × Vec 2 => h₀ (X 0 p.2 p.1))
  exact hh₀.comp hflow

end AVenhance.Infra.Section5.RelativeError

end

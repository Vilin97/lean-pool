/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SecondSpatial

/-! Joint continuity of the second variation in target time and initial point. -/

@[expose] public section

open Homogenization
open Set
open scoped ContDiff NNReal Topology

namespace AVenhance.Infra.Flow

/-- On a forward compact target-time interval, a fixed second spatial
variation is jointly continuous in target time and initial point. -/
theorem flow_secondVariation_jointContinuous_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (h k : Vec 2) (s t : ℝ) (hst : s ≤ t) :
    ContinuousOn (fun p : ℝ × Vec 2 =>
      flowSecondVariation hb hX p.2 s
        (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX p.2 s) |>.1)
        h k p.1 0 s) (Icc s t ×ˢ univ) := by
  obtain ⟨L, hL₀, hL⟩ := exists_global_spatial_lipschitz hb
  obtain ⟨M, hM₀, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  obtain ⟨Cjac, hCjac₀, hCjac⟩ := exists_global_spatialFDeriv_lipschitz hb
  obtain ⟨C₂, hC₂₀, hC₂⟩ := exists_global_spatialSecondDerivativeEval_bound hb
  obtain ⟨C₃, hC₃₀, hC₃⟩ := exists_global_spatialSecondDerivativeEval_lipschitz hb
  let Csp := flowSecondVariationLipschitzConstant L M Cjac C₂ C₃ s t
  have hCsp₀ : 0 ≤ Csp := by
    obtain ⟨C, hC₀, hCeq, _⟩ :=
      exists_flow_secondVariation_lipschitz_all_times_of_le hb hX
        L M Cjac C₂ C₃ hL₀ hM₀ hCjac₀ hC₂₀ hC₃₀ hL hM hCjac hC₂ hC₃
        0 0 s t hst h k
    dsimp [Csp]
    rw [← hCeq]
    exact hC₀
  let Kdir : ℝ≥0 := ⟨Csp * ‖h‖ * ‖k‖,
    mul_nonneg (mul_nonneg hCsp₀ (norm_nonneg h)) (norm_nonneg k)⟩
  let f : Vec 2 × ℝ → Vec 2 := fun p =>
    flowSecondVariation hb hX p.1 s
      (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX p.1 s) |>.1)
      h k p.2 0 s
  have htime (x : Vec 2) : ContinuousOn (fun q => f (x, q)) (Icc s t) := by
    let V : ℝ → Vec 2 → ℝ → Vec 2 :=
      Classical.choose (existsUnique_flow_variationalEquation hb hX x s)
    have hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V :=
      (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).1
    have hident (q : ℝ) : f (x, q) = flowSecondVariation hb hX x s hV h k q 0 s := by
      rfl
    have hWcont : ContinuousOn
        (fun q => flowSecondVariation hb hX x s hV h k q 0 s) (Icc s t) :=
      HasDerivAt.continuousOn (fun q _ =>
        (flowSecondVariation_isFlow hb hX x s hV h k).2 0 s q)
    exact hWcont.congr (fun q _ => hident q)
  have hspace (q : ℝ) (hq : q ∈ Icc s t) :
      LipschitzOnWith Kdir (fun x => f (x, q)) univ := by
    have hLip : LipschitzWith Kdir (fun x => f (x, q)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [dist_eq_norm, dist_eq_norm]
      obtain ⟨Cxy, _, hCxyEq, hbound⟩ :=
        exists_flow_secondVariation_lipschitz_all_times_of_le hb hX
          L M Cjac C₂ C₃ hL₀ hM₀ hCjac₀ hC₂₀ hC₃₀ hL hM hCjac hC₂ hC₃
          x y s t hst h k
      have hdiff := hbound q hq
      rw [hCxyEq] at hdiff
      calc
        ‖f (x, q) - f (y, q)‖ =
            ‖flowSecondVariation hb hX x s
                (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s) |>.1)
                h k q 0 s -
              flowSecondVariation hb hX y s
                (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX y s) |>.1)
                h k q 0 s‖ := by rfl
        _ = ‖flowSecondVariation hb hX y s
                (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX y s) |>.1)
                h k q 0 s -
              flowSecondVariation hb hX x s
                (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s) |>.1)
                h k q 0 s‖ := norm_sub_rev _ _
        _ ≤ Csp * ‖x - y‖ * ‖h‖ * ‖k‖ := hdiff
        _ = (Csp * ‖h‖ * ‖k‖) * dist x y := by rw [dist_eq_norm]; ring
    exact hLip.lipschitzOnWith
  let g : ℝ × Vec 2 → Vec 2 := fun p => f (p.2, p.1)
  have hprod : ContinuousOn g (Icc s t ×ˢ univ) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith' g Kdir hspace
      (fun x _ => by simpa [g] using htime x)
  simpa [g, f] using hprod

end AVenhance.Infra.Flow

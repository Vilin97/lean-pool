/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.ZeroVelocityJets

/-! Exact scale differences of actual velocity material powers. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- The material scale difference retains one coarse fast-velocity jet plus
the explicit correction sum, with no factor on the pure coarse term. -/
theorem amnr_velocity_power_error_expansion {b c : AmnrSpace → Vec 2}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (n : ℕ) (i : Fin 2) :
    amnrWord b (List.replicate n none) (fun y => b y i) -
      amnrWord c (List.replicate n none) (fun y => c y i) =
        amnrWord c (List.replicate n none) (amnrAdvectionVelocity b c i) +
          amnrMaterialErrorValue b c (fun y => b y i) n := by
  have hbi := (contDiff_apply ℝ ℝ i).comp hb
  have hci := (contDiff_apply ℝ ℝ i).comp hc
  have hh := amnr_material_power_expansion hb hc hbi n
  have hs := amnrWord_sub_global hc hbi hci (List.replicate n none)
  funext z
  have hp := congrFun hh z
  have hq := congrFun hs z
  change amnrWord b (List.replicate n none) (fun y => b y i) z =
    amnrWord c (List.replicate n none) (fun y => b y i) z +
      amnrMaterialErrorValue b c (fun y => b y i) n z at hp
  change amnrWord c (List.replicate n none) (amnrAdvectionVelocity b c i) z =
    amnrWord c (List.replicate n none) (fun y => b y i) z -
      amnrWord c (List.replicate n none) (fun y => c y i) z at hq
  change amnrWord b (List.replicate n none) (fun y => b y i) z -
    amnrWord c (List.replicate n none) (fun y => c y i) z =
      amnrWord c (List.replicate n none) (amnrAdvectionVelocity b c i) z +
        amnrMaterialErrorValue b c (fun y => b y i) n z
  linarith only [hp, hq]

/-- Nonempty coarse canonical velocity jets split into actual coarse and
fast jets; the scalar drift is never used in the estimate. -/
theorem amnr_velocity_coarse_mixed_abs_le_of_bounds {b c : AmnrSpace → Vec 2}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (w : List (Option (Fin 2))) (i : Fin 2) (z : AmnrSpace) {A B : ℝ}
    (hcoarse : |amnrWord c w (fun y => c y i) z| ≤ A)
    (hfast : |amnrWord c w (amnrAdvectionVelocity b c i) z| ≤ B) :
    |amnrWord c w (fun y => b y i) z| ≤ A + B := by
  have hs := congrFun (amnrWord_sub_global hc ((contDiff_apply ℝ ℝ i).comp hb)
    ((contDiff_apply ℝ ℝ i).comp hc) w) z
  change amnrWord c w (amnrAdvectionVelocity b c i) z =
    amnrWord c w (fun y => b y i) z - amnrWord c w (fun y => c y i) z at hs
  have he : amnrWord c w (fun y => b y i) z =
      amnrWord c w (fun y => c y i) z + amnrWord c w (amnrAdvectionVelocity b c i) z := by
    linarith only [hs]
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hcoarse hfast)

end AVenhance.Infra.Section4

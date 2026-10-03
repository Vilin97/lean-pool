/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.VelocityPowerExpansion

/-! Higher material scale steps with strictly lower canonical inputs. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Conditional induction step for the actual velocity scale difference.
Only the transported fast term is at the current material level. Every
changed-advection correction uses the strictly lower canonical inputs. -/
theorem amnr_velocity_higher_step_abs_le_of_lower_bounds
    {b c : AmnrSpace → Vec 2} {S H V Cv Cc Cb Ct : ℝ} {N : ℕ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hS : 0 ≤ S) (hH : 0 ≤ H) (hV : 0 ≤ V) (hCv : 1 ≤ Cv)
    (hCc : 0 ≤ Cc) (hCb : 0 ≤ Cb) (hVS : V * S = H)
    (α : List (Fin 2)) (n : ℕ) (hn : 1 ≤ n) (hbudget : α.length + 2 * n ≤ N)
    (i : Fin 2) (z : AmnrSpace)
    (hfast : ∀ p η r, η.length + 2 * r + 1 ≤ N → r < n →
      |amnrWord c (amnrMixedWord η r) (amnrAdvectionVelocity b c p) z| ≤
        (Cv * V) * amnrWeight S H (amnrMixedWord η r))
    (hcoarse : ∀ p η r, amnrMixedWord η r ≠ [] → η.length + 2 * r + 1 ≤ N → r < n →
      |amnrWord c (amnrMixedWord η r) (fun y => c y p) z| ≤
        (Cc * V) * amnrWeight S H (amnrMixedWord η r))
    (hB : ∀ p j η r, r < n → η.length + 2 * r + 2 ≤ N →
      |amnrWord c (amnrMixedWord η r) (amnrVelocityGradient c p j) z| ≤
        (Cb * H) * amnrWeight S H (amnrMixedWord η r))
    (htop : |amnrWord c (amnrMixedWord α n) (amnrAdvectionVelocity b c i) z| ≤
      Ct * V * S ^ α.length * H ^ n) :
    |amnrWord c (α.map some)
      (amnrWord b (List.replicate n none) (fun y => b y i) -
        amnrWord c (List.replicate n none) (fun y => c y i)) z| ≤
      (Ct + ((amnrMaterialErrorCardinality n * (n + 1) ^ α.length : ℕ) : ℝ) *
        (amnrNormalOrderConstant (N - 1) Cb (N - 1) * Cv) ^ n *
          (amnrNormalOrderConstant (N - 1) Cb (N - 1) * (Cc + Cv))) *
            V * S ^ α.length * H ^ n := by
  have hbi : ContDiff ℝ (⊤ : ℕ∞) (fun y => b y i) := (contDiff_apply ℝ ℝ i).comp hb
  have hv := amnrAdvectionVelocity_contDiff hb hc i
  have hjet := contDiffOn_univ.mp (amnrWord_contDiffOn_infty isOpen_univ hc.contDiffOn
    hv.contDiffOn (List.replicate n none))
  have he := amnrMaterialErrorValue_contDiff hb hc hbi n
  have hh := amnrMaterialError_spatial_abs_le_of_canonical_lower_bounds hb hc hbi hS hH hV
    hCv (show 0 ≤ Cc + Cv by linarith) hCb hVS α n hn hbudget z hfast
    (fun η r hne hη hr => by
      have hs := amnr_velocity_coarse_mixed_abs_le_of_bounds hb hc (amnrMixedWord η r) i z
        (hcoarse i η r hne hη hr) (hfast i η r hη hr)
      exact hs.trans_eq (by ring)) hB
  rw [amnr_velocity_power_error_expansion hb hc, amnrWord_add_global hc hjet he]
  simp only [Pi.add_apply]
  rw [← amnrWord_append]
  change |amnrWord c (amnrMixedWord α n) (amnrAdvectionVelocity b c i) z +
    amnrWord c (α.map some) (amnrMaterialErrorValue b c (fun y => b y i) n) z| ≤ _
  exact (abs_add_le _ _).trans ((add_le_add htop hh).trans_eq (by ring))

end AVenhance.Infra.Section4

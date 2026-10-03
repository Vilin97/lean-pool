/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectTransport

/-! Initial-time L2 norm continuity from joint continuity on the closed
half-line. This includes time zero, unlike an interior-time FTC interface. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set Filter Topology
namespace AVenhance.Infra.Section5.RelativeError
open AVenhance

/-- A jointly continuous cell field has continuous L2 norm, including
its initial slice. There is no size or normalization hypothesis. -/
theorem relative_initial_norm_continuous {F : ℝ → Vec 2 → ℝ}
    (hF : ContinuousOn (fun p : ℝ × Vec 2 => F p.1 p.2)
      (Ici (0 : ℝ) ×ˢ (univ : Set (Vec 2)))) (b : ℝ) :
    ContinuousOn (fun t => Real.sqrt (l2NormSq (F t))) (Icc 0 b) := by
  let K := Icc (0 : ℝ) b
  let Q : Set (Vec 2) := pi univ fun _ : Fin 2 => Icc (0 : ℝ) 1
  have hKclosed : IsClosed K := isClosed_Icc
  let : LocallyCompactSpace K := hKclosed.locallyCompactSpace
  have hjoint : Continuous (fun p : K × Vec 2 => F p.1.1 p.2) := by
    have hmap : Continuous (fun p : K × Vec 2 => (p.1.1, p.2)) := by fun_prop
    exact hF.comp_continuous hmap (fun p => ⟨p.1.2.1, mem_univ _⟩)
  have hQcompact : IsCompact Q := isCompact_univ_pi fun _ => isCompact_Icc
  have hparam : Continuous (fun t : K => ∫ x in Q, F t.1 x ^ 2) :=
    continuous_parametric_integral_of_continuous
      (f := fun (t : K) (x : Vec 2) => F t.1 x ^ 2)
      (by
        change Continuous (fun p : K × Vec 2 => F p.1.1 p.2 ^ 2)
        exact hjoint.pow 2) hQcompact
  have hcube : unitCube =ᵐ[(volume : Measure (Vec 2))] Q := by
    simpa [volume_pi, unitCube, Q] using
      (Measure.univ_pi_Ioo_ae_eq_Icc
        (f := fun _ : Fin 2 => (0 : ℝ)) (g := fun _ : Fin 2 => (1 : ℝ)))
  have heq : (fun t : K => ∫ x in Q, F t.1 x ^ 2) =
      fun t => l2NormSq (F t.1) := by
    funext t
    exact setIntegral_congr_set hcube.symm
  rw [heq] at hparam
  have henergy : ContinuousOn (fun t => l2NormSq (F t)) K := by
    rwa [continuousOn_iff_continuous_domRestrict]
  exact Real.continuous_sqrt.comp_continuousOn henergy
end AVenhance.Infra.Section5.RelativeError

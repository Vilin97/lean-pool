/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Continuity in time of unit-cell integrals of jointly continuous integrands on `(0,∞)` -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Homogenization
open AVenhance.Infra.Torus
open scoped Topology

namespace AVenhance.Infra.Section5.Integration.Energy

/-- The unit cell is a null-set perturbation of the closed unit square. -/
theorem unitCell_ae_eq_closedCube :
    unitCell 2 =ᵐ[(volume : Measure (Vec 2))] Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1
        := by
  refine unitCell_ae_eq_unitCube.trans ?_
  simpa [AVenhance.unitCube, volume_pi] using
    (Measure.univ_pi_Ioo_ae_eq_Icc (f := fun _ : Fin 2 => (0 : ℝ))
      (g := fun _ : Fin 2 => (1 : ℝ)))

/-- Unit-cell integrals of integrands jointly continuous on `(0,∞) × ℝ²` are continuous in
time on `(0,∞)`. -/
theorem continuousOn_integral_unitCell_Ioi {H : ℝ → Vec 2 → ℝ}
    (hH : ContinuousOn (Function.uncurry H) (Set.Ioi (0 : ℝ) ×ˢ Set.univ)) :
    ContinuousOn (fun t => ∫ x in unitCell 2, H t x) (Set.Ioi (0 : ℝ)) := by
  have hKc : IsCompact (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hcont : Continuous (Function.uncurry fun (u : Set.Ioi (0 : ℝ)) (x : Vec 2) => H u x) := by
    have h1 : Continuous fun p : Set.Ioi (0 : ℝ) × Vec 2 => Function.uncurry H (p.1.1, p.2) :=
      hH.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
        fun p => ⟨p.1.2, Set.mem_univ _⟩
    exact h1
  have : LocallyCompactSpace (Set.Ioi (0 : ℝ)) := isOpen_Ioi.locallyCompactSpace
  have hc := continuous_parametric_integral_of_continuous (μ := volume) hcont hKc
  rw [continuousOn_iff_continuous_domRestrict]
  convert hc using 2 with u
  exact setIntegral_congr_set unitCell_ae_eq_closedCube

end AVenhance.Infra.Section5.Integration.Energy

end

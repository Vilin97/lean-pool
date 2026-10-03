/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.BaseEnergyFrozen
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.BaseEnergyScalar

/-! # dissipation lower bound for classical solutions

For an admissible stream `φ`, `κ > 0`, and a classical solution `θ` with zero forcing and
smooth periodic mean-zero datum `g`:
`min (1/4) (2π²κ) ‖g‖² ≤ κ ‖∇θ‖²_{L²_{t,x}}`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization
open AVenhance.Infra.Torus
open AVenhance.Infra.Classical

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance

variable {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {g : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}

/-- Mean-zero Poincaré along a classical solution, in multiplicative form. -/
theorem classical_poincare (hφ : IsAdmissibleStream φ)
    (hsol : IsClassicalSol (streamVel φ) κ (fun _ _ => 0) g θ) (hg : MeanZeroOn unitCube g)
    {t : ℝ} (ht : 0 ≤ t) :
    4 * Real.pi ^ 2 * l2NormSq (θ t) ≤ gradNormSq (spaceGrad (θ t)) := by
  have hg' : ∫ x in unitCell 2, g x = 0 := by
    rw [integral_unitCell_eq_unitCube]
    exact hg
  have hm := classical_meanZero hφ hsol hg' ht
  have hm' : ∫ x in unitCube, θ t x = 0 := by
    rw [← integral_unitCell_eq_unitCube]
    exact hm
  have hP := Infra.Torus.l2NormSq_le_fourierPoincare
    ((classicalSmooth_slice_nonneg hsol.1 ht).of_le (by norm_num))
    (hsol.2.1 t ht) hm'
  have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hP hpi.le
  rwa [mul_inv_cancel_left₀ hpi.ne'] at this

/-- The dissipation lower bound for classical solutions with mean-zero datum. -/
theorem classical_dissipation_lower (hφ : IsAdmissibleStream φ) (hκ : 0 < κ)
    (hsol : IsClassicalSol (streamVel φ) κ (fun _ _ => 0) g θ) (hg : MeanZeroOn unitCube g) :
    min (1 / 4) (2 * Real.pi ^ 2 * κ) * l2NormSq g ≤
      κ * spaceTimeGradNormSq (fun t x => spaceGrad (θ t) x) := by
  rw [spaceTimeGradNormSq_eq_intervalIntegral hsol]
  refine dissipation_lower_scalar (e := fun t => l2NormSq (θ t)) hκ
    (integral_nonneg fun x => sq_nonneg _)
    (fun s _ => gradNormSq_nonneg' _) (gradNormSq_continuousOn hsol zero_le_one)
    (fun t ht => classical_energy_identity_frozen hφ hsol ht.1)
    (fun s hs => classical_poincare hφ hsol hg hs.1)

end AVenhance.Infra.Section5.RelativeError

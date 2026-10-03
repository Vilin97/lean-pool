/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.ZeroDataEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.WeakAlgebra
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsWeakSolution

/-!
# Uniqueness in the weak-solution class

Subtracting two weak solutions gives a zero-data weak solution. Its energy vanishes, and the
cellwise `L²` norm identity implies equality almost everywhere on every time slice.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization

namespace AVenhance.Infra.Parabolic.WeakUniqueness

/-- Two weak solutions with the same datum agree cell-a.e. at every time. -/
theorem weak_solutionGrad_unique
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {θ₀ : Vec 2 → ℝ}
    {θ η : ℝ → Vec 2 → ℝ} {D E : ℝ → Vec 2 → Vec 2}
    (hθ₀ : MemL2On AVenhance.unitCube θ₀)
    (hη : AVenhance.IsWeakSolutionGrad b κ θ₀ η E)
    (hθ : AVenhance.IsWeakSolutionGrad b κ θ₀ θ D)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    (hκ : 0 < κ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      η t =ᵐ[volume.restrict AVenhance.unitCube] θ t := by
  let w : ℝ → Vec 2 → ℝ := fun t x => η t x - θ t x
  let Dw : ℝ → Vec 2 → Vec 2 := fun t x => E t x - D t x
  have hdiff := isWeakSolutionGrad_sub hθ₀ hθ₀ hη hθ
  have hzero : AVenhance.IsWeakSolutionGrad b κ
      (fun _ : Vec 2 => (0 : ℝ)) w Dw := by
    simpa [w, Dw] using hdiff
  have henergy := weak_solution_zero_data_eq_zero hzero hb_meas hb_bdd hκ
  intro t ht
  have hslice : MemL2On AVenhance.unitCube (w t) := (hzero.1 t ht).2
  have hsquareInt : Integrable (fun x => w t x ^ 2)
      (volume.restrict AVenhance.unitCube) :=
    (memLp_two_iff_integrable_sq hslice.aestronglyMeasurable).1 hslice
  have hsquareNonneg : 0 ≤ᵐ[volume.restrict AVenhance.unitCube]
      fun x => w t x ^ 2 := ae_of_all _ fun x => sq_nonneg _
  have hsquareZero : (fun x => w t x ^ 2) =ᵐ[volume.restrict AVenhance.unitCube]
      (0 : Vec 2 → ℝ) := by
    apply (integral_eq_zero_iff_of_nonneg_ae hsquareNonneg hsquareInt).mp
    exact henergy t ht
  have hzeroAE : w t =ᵐ[volume.restrict AVenhance.unitCube] 0 := by
    filter_upwards [hsquareZero] with x hx
    exact sq_eq_zero_iff.mp hx
  filter_upwards [hzeroAE] with x hx
  have hx' : η t x - θ t x = 0 := by simpa [w] using hx
  exact sub_eq_zero.mp hx'

end AVenhance.Infra.Parabolic.WeakUniqueness

end

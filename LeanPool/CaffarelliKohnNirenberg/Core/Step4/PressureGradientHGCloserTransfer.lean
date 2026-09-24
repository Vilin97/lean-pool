/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.RouteAGradientProducerUniform

/-!
# Pressure Gradient HGCloser Transfer

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open CKN.Core.HeatPotential MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open scoped ENNReal NNReal Topology


namespace CKN.Core.Step4

/-! # Pressure-gradient Morrey membership for an identified field

The cell estimate applies to the same integrable weak pressure gradient
produced on the inner parabolic ball. Its finite bound is uniform over
components, cell centres, and radii, but may depend on the solution.
-/

/-- Convert a glued integrable weak pressure gradient with bounds on every
Morrey cell into the uniform Route A gradient conclusion. -/
theorem routeA_gradient_of_glued_field_cell_bounds
    (hGlued :
      ∀ q τ : ℝ, 5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
        ∀ {Ω : Set Vec3} {I : Set ℝ}
          {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
          {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
          IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
          ∀ (z₀ : ParabolicPoint) (R : ℝ), 0 < R →
          Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I →
          morreyVecMem 3 τ (Metric.ball z₀ R) u →
          (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
            (Metric.ball z₀ R) (fun z => Du z i)) →
          ∃ Dp : ParabolicPoint → Vec3,
            (∀ i : Fin 3, AEMeasurable (fun z => Dp z i)
              (volume.restrict (Metric.ball z₀ (R / 2)))) ∧
            (∀ i : Fin 3, Integrable (fun z => Dp z i)
              (volume.restrict (Metric.ball z₀ (R / 2)))) ∧
            (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
              ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
              tsupport ψ ⊆ parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ (R / 2) →
              (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
                -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
            ∃ Ccell : ℝ, ∀ i : Fin 3, ∀ z : ParabolicPoint,
              ∀ r : {r : ℝ // 0 < r},
                morreyCell (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q)
                  ((Metric.ball z₀ (R / 2)).indicator (fun w => Dp w i)) z r.1 ≤
                  ENNReal.ofReal Ccell) : routeAGradientProducerUniform := by
  intro q τ hq hτ hτ' Ω I u Du p f hsol z₀ R hR hdom hu hDu
  obtain ⟨Dp, hAE, _hInt, hweak, Ccell, hbound⟩ :=
    hGlued q τ hq hτ hτ' hsol z₀ R hR hdom hu hDu
  refine ⟨Dp, hAE, hweak, ?_⟩
  exact pressure_gradient_morreyVecMem_of_cell_bounds_real
    (C := Ccell) (routeA_uniform_kappa_min_lower hq hτ)
    (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top) hbound

end CKN.Core.Step4

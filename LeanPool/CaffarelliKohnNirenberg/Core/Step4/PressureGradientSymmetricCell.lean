/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradient
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.RouteAAssembly
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOneSided
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradient
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.Localization
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays

/-!
# Pressure Gradient Symmetric Cell

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

section

/-!
# Pressure Gradient Morrey Bridge

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Step4

/-- The same bridge with the scalar exponent written as an explicit real
number; this is convenient when the exponent is
`min ((1 / τ + 8 / 25)⁻¹) q`. -/
theorem pressure_gradient_morreyVecMem_of_cell_bounds_real
    {S : Set ParabolicPoint} {κ C : ℝ}
    {Dp : ParabolicPoint → Vec3}
    (hκ : 6 / 5 ≤ κ) (hC : ENNReal.ofReal C < ⊤)
    (hcell : ∀ i : Fin 3, ∀ z : ParabolicPoint,
      ∀ r : {r : ℝ // 0 < r},
      morreyCell (6 / 5 : ℝ) κ
        (S.indicator (fun w => Dp w i)) z r.1 ≤ ENNReal.ofReal C) :
    morreyVecMem (6 / 5 : ℝ) κ S Dp := by
  rw [morreyVecMem_iff_cylinder_lt_top (by norm_num) hκ]
  intro i
  exact (pressure_gradient_morrey_bound (fun z r => hcell i z r)).trans_lt hC

end CKN.Core.Step4
end

end

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Core.Step4

/-! The symmetric carrier for `G`.  The slice producer is deliberately kept at
the exact inner-ball interface consumed by `exists_spacetime_weak_gradient_of_slices`.
This is the space-time form of the paper's display (3.5). -/

/-- Existence interface for pressure-gradient slices on symmetric interior parabolic balls. -/
@[expose] def symmetricPressureGradientSliceProducer : Prop :=
  ∀ q : ℝ, 5 / 2 < q →
    ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ (z₀ : ParabolicPoint) (R : ℝ), 0 < R →
      Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I →
      morreyVecMem 3 (25 / 3 : ℝ) (Metric.ball z₀ R) u →
      (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
        (Metric.ball z₀ R) (fun z => Du z i)) →
      ∃ K : Fin 3 → ℝ → ℝ≥0∞,
        ∀ᵐ t ∂(volume.restrict (Ioo (z₀.2 - R ^ 2) (z₀.2 + R ^ 2))),
          ∀ i : Fin 3, ∃ g : Vec3 → ℝ,
            LocallyIntegrableOn g (vec3Ball z₀.1 R) volume ∧
            HasWeakPartialDerivOn (vec3Ball z₀.1 R) i
              (fun x => p (x, t)) g ∧
            eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
              (volume.restrict (vec3Ball z₀.1 (R / 2))) ≤ K i t

end CKN.Core.Step4

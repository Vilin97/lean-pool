/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientSWS
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.ConcreteRieszConsumption
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.CZUnconditional

/-! # The slice pressure-gradient bound with the explicit endpoint constant

`pressure_slice_bound_of_riesz_weak_extension` takes the selected
weak-gradient family as a hypothesis.  That hypothesis is now available
without any analytic input: the completed `L^{6/5}` extension of the second
Riesz transforms provides the field, its pairing with the first potential,
and the numerical bound, with the explicit constant
`czGradientOperatorConstant`.  The two statements below record the selected
family at that constant and the resulting slice bound, so the pressure
gradient on a slice is controlled with no Calderón--Zygmund premise.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Step4

/-- The selected weak gradient of the first potential exists with the
explicit constant `czGradientOperatorConstant`, with no analytic premise. -/
theorem exists_weak_pressure_gradient_unconditional :
    ∀ (i : Fin 3) (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume → HasCompactSupport G →
      ∃ D : Vec3 → Vec3,
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ)) volume ∧
        (∀ (j : Fin 3) (ψ : Vec3 → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x) =
            -(∫ x, D x j * ψ x)) ∧
        eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
          ENNReal.ofReal czGradientOperatorConstant *
            eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
  CKN.Core.Endgame.exists_weak_pressure_gradient_of_concrete_riesz_extension
    czGradientOperatorConstant le_rfl

/-- The slice bound of the pressure gradient, with the Calderón--Zygmund
input discharged by the completed extension.  Only the local representation
`p = ∂ᵢN * G + H`, the harmonic slice bound for `H`, and the local
integrability data remain; the constant is any `C` at least
`czGradientOperatorConstant`. -/
theorem pressure_slice_bound_unconditional
    {B B' : Set Vec3} (hB : IsOpen B)
    {p H gh G : Vec3 → ℝ} {i k : Fin 3} {ρ C : ℝ}
    (hC : czGradientOperatorConstant ≤ C)
    (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hGc : HasCompactSupport G)
    (hrep : p =ᵐ[volume.restrict B]
      pressureNewtonianDerivativePotential i G + H)
    (hH : HasWeakPartialDerivOn B k H gh)
    (hPloc : LocallyIntegrableOn
      (pressureNewtonianDerivativePotential i G) B volume)
    (hHloc : LocallyIntegrableOn H B volume)
    (hghloc : LocallyIntegrableOn gh B volume)
    (hgh : eLpNorm gh (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B') ≤
      ENNReal.ofReal C * ENNReal.ofReal (ρ ^ (-1 / 2 : ℝ)) *
        eLpNorm p (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B)) :
    ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g B volume ∧
      HasWeakPartialDerivOn B k p g ∧
      eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B') ≤
        ENNReal.ofReal C * (eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume +
          ENNReal.ofReal (ρ ^ (-1 / 2 : ℝ)) *
            eLpNorm p (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B)) :=
  pressure_slice_bound_of_riesz_weak_extension (ρ := ρ) hB
    (CKN.Core.Endgame.exists_weak_pressure_gradient_of_concrete_riesz_extension C hC)
    hG hGc hrep hH hPloc hHloc hghloc hgh

end CKN.Core.Step4

/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.WeakCZConsumption
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.ExtensionNormTransport
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.CZInputs

/-! # Weak gradients selected from the actual indexed extension

The completed L^(6/5) operator supplies its own membership and numerical
bound. Its positive pairing with the first potential selects the negatively
signed weak gradient, without any classical representative identification.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Endgame

/-- The actual indexed extension produces the required weak-gradient
output once its distributional pairing is supplied. -/
theorem exists_weak_pressure_gradient_of_riesz_extension
    (C_CZ : ℝ)
    (hconst : 3 * czGradientComponentConstant rieszSecondWeakTypeConstant 1 ≤ C_CZ)
    (hL2 : ∀ i j : Fin 3, RieszSecondL2Input i j)
    (hWeak11 : ∀ i j f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator (hL2 i j) f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (hpair : ∀ i j (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume → HasCompactSupport G →
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x) =
        ∫ x, rieszSecondGradientExtensionOperator (hL2 i j) (hWeak11 i j) G x * ψ x) :
    ∀ (i : Fin 3) (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume → HasCompactSupport G →
      ∃ D : Vec3 → Vec3,
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ)) volume ∧
        (∀ (j : Fin 3) (ψ : Vec3 → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x) =
            -(∫ x, D x j * ψ x)) ∧
        eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
          ENNReal.ofReal C_CZ * eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
  have hC : 0 ≤ czGradientComponentConstant rieszSecondWeakTypeConstant 1 :=
    ENNReal.toReal_nonneg
  apply exists_weak_pressure_gradient_of_extension
    (czGradientComponentConstant rieszSecondWeakTypeConstant 1) C_CZ hC hconst
    (fun i j => rieszSecondGradientExtensionOperator (hL2 i j) (hWeak11 i j))
    (fun i j G hG hGc => rieszSecondGradientExtension_memLp (hL2 i j) (hWeak11 i j) hG hGc)
    ?_ hpair
  intro i j G hG hGc
  exact eLpNorm_le_of_toLp_norm_le hG
    (rieszSecondGradientExtension_memLp (hL2 i j) (hWeak11 i j) hG hGc) hC
    (rieszSecondGradientExtension_toLp_bound (hL2 i j) (hWeak11 i j) hG hGc)

end CKN.Core.Endgame

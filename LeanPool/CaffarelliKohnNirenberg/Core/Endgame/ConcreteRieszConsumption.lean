/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondWeakCertificate
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtensionPairingMain
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.RieszWeakGradient
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.TensorExtensionPairing

/-! # Consuming the constructed indexed L² endpoint

The smooth global Hessian estimate supplies the indexed L² input, and
the concrete restricted weak endpoint is instantiated. The first-potential
pairing supplies the weak-gradient identity without an analytic input.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Endgame

/-- The concrete L² construction discharges the endpoint input in the
global tensor-extension pressure pairing. -/
theorem concrete_riesz_tensor_distributional_identity
    {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, (∑ i, ∑ j, rieszSecondP1ExtensionOperator
      (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j) (G i j) x) * spatialLaplacian ψ x) =
        ∫ x, ∑ i, ∑ j, G i j x * mixedSecond ψ i j x := by
  exact rieszSecondP1ExtensionTensor_distributional_identity
    rieszSecondL2Input rieszSecondL2_weak_type hG hψ hψc

/-- The concrete endpoints and first-potential pairing supply the signed
weak-gradient bound without an additional analytic premise. -/
theorem exists_weak_pressure_gradient_of_concrete_riesz_extension
    (C_CZ : ℝ)
    (hconst : 3 * czGradientComponentConstant rieszSecondWeakTypeConstant 1 ≤ C_CZ) :
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
  exact exists_weak_pressure_gradient_of_riesz_extension C_CZ hconst
    rieszSecondL2Input rieszSecondL2_weak_type
    (rieszSecondGradientExtension_weak_gradient_pairing
      rieszSecondL2Input rieszSecondL2_weak_type)

end CKN.Core.Endgame

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanWeakCurl
public import LeanPool.NavierStokesAndEuler.Euler.CanonicalGraphPotential
public import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientMultipliers
public import Mathlib.LinearAlgebra.BilinearForm.Properties

@[expose] public section

/-! A canonically normalized actual scalar potential for ordinary mean pressure gradients. -/

noncomputable section

namespace EulerMeanPressure

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal
  EulerCanonicalGraphPotential EulerMeanCoefficients
open scoped ContDiff

theorem symmetry_of_coordinates (L : Space →L[ℝ] Space)
    (hL : ∀ i j, (L (EuclideanSpace.single i 1)) j = (L (EuclideanSpace.single j 1)) i)
    (a b : Space) : ⟪L a, b⟫_ℝ = ⟪L b, a⟫_ℝ := by
  let B : LinearMap.BilinForm ℝ Space := (innerₗ Space).comp L.toLinearMap
  have hB : LinearMap.BilinForm.IsSymm B :=
    (LinearMap.BilinForm.isSymm_iff_basis (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis).2 (fun i j
      => by
      change ⟪L ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i),
          (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis j⟫_ℝ =
        ⟪L ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis j),
          (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i⟫_ℝ
      simpa only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
        EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul] using hL i j)
  exact hB.eq a b

/-- Smooth representatives of the actual closed gradient space have a genuine scalar potential. -/
theorem gradientSpace_has_potential (p : L2) (hp : p ∈ gradientSpace)
    (g : Space → Space) (hrep : p =ᵐ[volume] g) (hg : ContDiff ℝ ∞ g) :
    ∃ q : Space → ℝ, ContDiff ℝ ∞ q ∧ ∀ x, gradient q x = g x := by
  apply EulerGraphPullback.smooth_gradient_potential g hg
  intro x a b
  exact symmetry_of_coordinates (fderiv ℝ g x)
    (gradientSpace_classical_curl_zero p hp g hrep hg x) a b

/-- The concrete radial integral gives a fixed additive normalization, not just an existential pressure. -/
theorem gradientSpace_radial_potential (p : L2) (hp : p ∈ gradientSpace)
    (g : Space → Space) (hrep : p =ᵐ[volume] g) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (radialPotential g) ∧ radialPotential g 0 = 0 ∧
      ∀ x, gradient (radialPotential g) x = g x := by
  obtain ⟨q, hq, hgrad⟩ := gradientSpace_has_potential p hp g hrep hg
  exact ⟨radialPotential_smooth g hg.continuous q hq hgrad,
    radialPotential_zero g, radialPotential_gradient g hg.continuous q hq hgrad⟩

/-- An F-adjoint pressure residual is the actual pullback of a scalar gradient. -/
theorem weighted_pressure_has_potential (F FT : Field) (hFT : ∀ x, FT x = (F x).adjoint)
    (r : L2) (hr : (multiplier F).adjoint r ∈ gradientSpace)
    (g : Space → Space) (hrep : r =ᵐ[volume] g)
    (hg : ContDiff ℝ ∞ (fun x => (F x).adjoint (g x))) :
    ContDiff ℝ ∞ (radialPotential (fun x => (F x).adjoint (g x))) ∧
      radialPotential (fun x => (F x).adjoint (g x)) 0 = 0 ∧
      ∀ x, gradient (radialPotential (fun x => (F x).adjoint (g x))) x =
        (F x).adjoint (g x) := by
  apply gradientSpace_radial_potential ((multiplier F).adjoint r) hr
    (fun x => (F x).adjoint (g x)) ?_ hg
  rw [← multiplier_adjoint F FT hFT]
  filter_upwards [multiplier_ae FT r, hrep] with x hx hrx
  rw [hx, hrx, hFT]

end EulerMeanPressure

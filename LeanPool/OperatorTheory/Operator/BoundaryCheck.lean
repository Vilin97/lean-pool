/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import LeanPool.OperatorTheory.Operator

/-!
Manifest-driven boundary for the landed operator-theory surface.

Every declaration below has an explicit type and delegates to the production
declaration. A changed source signature therefore breaks elaboration, while
the manifest separately audits the production declaration's axioms.
-/

open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real

namespace CrouzeixPalenciaBoundary

universe u

section NumericalRange

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

noncomputable def numericalRange_boundary (A : E →L[ℂ] E) : Set ℂ :=
  numericalRange A

theorem mem_numericalRange_boundary (A : E →L[ℂ] E) (z : ℂ) :
    z ∈ numericalRange A ↔ ∃ x : E, ‖x‖ = 1 ∧ ⟪x, A x⟫_ℂ = z :=
  mem_numericalRange A z

theorem norm_le_of_mem_numericalRange_boundary (A : E →L[ℂ] E)
    {z : ℂ} (hz : z ∈ numericalRange A) : ‖z‖ ≤ ‖A‖ :=
  norm_le_of_mem_numericalRange A hz

theorem convex_numericalRange_boundary (A : E →L[ℂ] E) :
    Convex ℝ (numericalRange A) :=
  convex_numericalRange A

end NumericalRange

section SpectralSet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

noncomputable def polynomialSupNorm_boundary
    (p : Polynomial ℂ) (X : Set ℂ) : ℝ :=
  polynomialSupNorm p X

def IsKPolynomialSpectralSet_boundary
    (A : E →L[ℂ] E) (K : ℝ) (X : Set ℂ) : Prop :=
  IsKPolynomialSpectralSet A K X

def IsPolynomialSpectralSet_boundary
    (A : E →L[ℂ] E) (X : Set ℂ) : Prop :=
  IsPolynomialSpectralSet A X

theorem spectrum_subset_closure_numericalRange_boundary (A : E →L[ℂ] E) :
    spectrum ℂ (A : E →L[ℂ] E) ⊆ closure (numericalRange A) :=
  spectrum_subset_closure_numericalRange A

theorem numericalRange_adjoint_boundary (A : E →L[ℂ] E) :
    numericalRange (ContinuousLinearMap.adjoint A) =
      (starRingEnd ℂ) '' numericalRange A :=
  numericalRange_adjoint A

/-- Exact unconditional project capstone. This declaration is deliberately
part of the manifest boundary so supporting lemmas cannot produce a vacuous
green board while the final theorem is absent. -/
theorem crouzeix_palencia_boundary (A : E →L[ℂ] E) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) :=
  crouzeix_palencia A

end SpectralSet

section Dilation

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem exists_halmos_unitary_dilation_boundary
    (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) :
    ∃ U : WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E),
      U ∈ unitary (WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E)) ∧
        ∀ x : E, (U (WithLp.toLp 2 (x, 0))).fst = T x :=
  exists_halmos_unitary_dilation T hT

theorem exists_unitary_power_dilation_boundary
    (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (V : E →L[ℂ] H) (U : H →L[ℂ] H),
      (∀ x y : E, ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
        U ∈ unitary (H →L[ℂ] H) ∧
          ∀ (n : ℕ) (x : E),
            ContinuousLinearMap.adjoint V ((U ^ n) (V x)) = (T ^ n) x :=
  exists_unitary_power_dilation T hT

theorem vonNeumann_inequality_boundary
    (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) (p : ℂ[X]) :
    ‖aeval T p‖ ≤ polynomialSupNorm p (Metric.closedBall (0 : ℂ) 1) :=
  vonNeumann_inequality T hT p

end Dilation

section Contours

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

def ContourIntegrable_boundary (f : ℂ → F) (γ : ℝ → ℂ) : Prop :=
  ContourIntegrable f γ

noncomputable def contourIntegral_boundary (f : ℂ → F) (γ : ℝ → ℂ) : F :=
  contourIntegral f γ

theorem contourIntegral_eq_zero_of_hasDerivAt_of_closed_boundary
    {f Fp : ℂ → F} {γ : ℝ → ℂ}
    (hγ : ∀ t ∈ Icc (0 : ℝ) (2 * π), DifferentiableAt ℝ γ t)
    (hF : ∀ t ∈ Icc (0 : ℝ) (2 * π), HasDerivAt Fp (f (γ t)) (γ t))
    (hint : ContourIntegrable f γ) (hclosed : γ (2 * π) = γ 0) :
    contourIntegral f γ = 0 :=
  contourIntegral_eq_zero_of_hasDerivAt_of_closed hγ hF hint hclosed

end Contours

section Approximation

theorem convexThickeningApprox_spec_boundary
    (K : Set ℂ) (hcompact : IsCompact K) (hconvex : Convex ℝ K) :
    (∀ n, K ⊆ convexThickeningApprox K n ∧
      IsOpen (convexThickeningApprox K n) ∧
      StrictConvex ℝ (convexThickeningApprox K n)) ∧
      (⋂ n, convexThickeningApprox K n) = K :=
  convexThickeningApprox_spec K hcompact hconvex

noncomputable def smoothClosedBallApproximation_boundary
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    SmoothConvexApproximation (Metric.closedBall c R) :=
  smoothClosedBallApproximation c R hR

end Approximation

section Auxiliary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

noncomputable def crouzeixAuxiliaryOperator_boundary
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (h : ℂ → ℂ) : E →L[ℂ] E :=
  crouzeixAuxiliaryOperator A Omega h

noncomputable def crouzeixPolynomialAuxiliaryOperator_boundary
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ) : E →L[ℂ] E :=
  crouzeixPolynomialAuxiliaryOperator A Omega p

theorem exists_smoothJordanDomain_norm_bound_crouzeixPolynomialAuxiliaryOperator_boundary
    [CompleteSpace E] (A : E →L[ℂ] E) (p : Polynomial ℂ) :
    ∃ (Omega : SmoothJordanDomain) (C : ℝ),
      closure (numericalRange A) ⊆ Omega.carrier ∧
        ‖crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
          ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (2 * Real.pi * C) :=
  exists_smoothJordanDomain_norm_bound_crouzeixPolynomialAuxiliaryOperator A p

end Auxiliary

end CrouzeixPalenciaBoundary

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/

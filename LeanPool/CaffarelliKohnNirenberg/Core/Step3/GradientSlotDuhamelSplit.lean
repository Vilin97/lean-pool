/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyGradient

/-!
# Gradient Slot Duhamel Split

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
open CKN.Foundation.Parabolic
open CKN.Core.Step4


noncomputable section

namespace CKN.Core.Step3

/-!
# Regrouped integrands for the local equation

The tested form of the localized equation (`lem:local-equation`) pairs the
divergence-form sources `localizedDivergenceG`, `localizedDivergenceH` with a
test field and its first spatial derivative.  The paper writes the same
expression after moving the derivative of the product `φ * ψ` onto the cutoff
factor, which is what the identities below record.

`gradientSlot_divergence_integrand` is the divergence-form regrouping: the
source integrand together with the derivative slot equals the time, force,
convection, derivative and pressure contributions collected on the right.
`gradientSlot_gradient_integrand` is the corresponding regrouping for the
pressure-gradient slot of `localizedGradientSourceG`, where the second spatial
derivatives of the cutoff appear explicitly; it needs no smoothness hypotheses
because the product rule is not used.
-/

/-- The divergence-form tested integrand of the local equation, regrouped onto
the cutoff product `φ * ψ` (`lem:local-equation`).  The only analytic input is
the product rule `spatialPartial_mul_full` for the smooth cutoff factors. -/
theorem gradientSlot_divergence_integrand
    {φ ψ : Vec3 × ℝ → ℝ}
    (hφd : ContDiff ℝ (⊤ : ℕ∞) φ) (hψd : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (i : Fin 3) (z : ParabolicPoint) :
    localizedDivergenceG φ u Du p f z i * ψ z +
        ∑ j, localizedDivergenceH φ u p j z i * spatialPartial ψ j z =
      (u z i * (timePartial φ z * ψ z) + f z i * (φ z * ψ z)) +
        (∑ j, u z i * u z j * spatialPartial (fun w => φ w * ψ w) j z) +
        (∑ j, (-(Du z i j * (spatialPartial φ j z * ψ z)) +
          u z i * (spatialPartial φ j z * spatialPartial ψ j z))) +
        p z * spatialPartial (fun w => φ w * ψ w) i z := by
  have hsp : ∀ j : Fin 3, spatialPartial (fun w => φ w * ψ w) j z =
      spatialPartial φ j z * ψ z + φ z * spatialPartial ψ j z :=
    fun j => spatialPartial_mul_full hφd hψd j z
  simp only [localizedDivergenceG, localizedDivergenceH, hsp]
  simp only [Fin.sum_univ_three]
  fin_cases i <;> simp <;> ring

/-- The pressure-gradient tested integrand of the local equation, regrouped
onto the cutoff product `φ * ψ` (`lem:local-equation`).  No derivative of the
test field is moved, so no smoothness hypothesis is needed. -/
theorem gradientSlot_gradient_integrand
    {φ ψ : Vec3 × ℝ → ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {f : ParabolicPoint → Vec3} {Dp : ParabolicPoint → Vec3}
    (i : Fin 3) (z : ParabolicPoint) :
    localizedGradientSourceG φ u Du f Dp z i * ψ z +
        ∑ j, (-localizedGradientSourceH φ u j z i) * spatialPartial ψ j z =
      (u z i * (timePartial φ z * ψ z) + f z i * (φ z * ψ z)) +
        (-((φ z * ψ z) * localizedConvection u Du z i)) +
        (∑ j, (u z i * (spatialSecondPartial φ j j z * ψ z) +
          2 * (u z i * (spatialPartial φ j z * spatialPartial ψ j z)))) +
        (-(Dp z i * (φ z * ψ z))) := by
  simp only [localizedGradientSourceG, localizedGradientSourceH,
    localizedEquationG, localizedEquationH]
  rw [show spatialLaplacian (fun x => φ (x, z.2)) z.1 =
      ∑ j : Fin 3, spatialSecondPartial φ j j z by rfl]
  simp only [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  fin_cases i <;> ring

end CKN.Core.Step3

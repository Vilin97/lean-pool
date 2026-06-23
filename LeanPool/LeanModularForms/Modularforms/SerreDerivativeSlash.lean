/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import LeanPool.LeanModularForms.Modularforms.Derivative

/-! # SerreDerivativeSlash -/


@[expose] public section

/-!
# Slash Invariance of Serre Derivative of E₂

This file proves that the Serre derivative `serreD 1 E₂` is weight-4 slash-invariant
under SL(2,ℤ), despite E₂ itself not being modular.

## Main results

* `D_D₂` : Derivative of the anomaly function D₂: `D(D₂ γ) z = -c²/denom²`
* `MDifferentiable_D₂` : D₂ γ is MDifferentiable
* `serre_DE₂_slash_invariant` : serreD 1 E₂ is weight-4 slash-invariant

## Strategy

The key insight is that under the slash action:
- `E₂ ∣[2] γ = E₂ - α * D₂ γ` where `α = 3/π²`
- `D(D₂ γ) = -c²/denom²` where `c = γ₁₀`
- The anomaly terms cancel because `α - α² * π²/3 = 0` when `α = 3/π²`
-/

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap
open ModularForm EisensteinSeries TopologicalSpace Set MeasureTheory
open Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

open scoped ModularForm MatrixGroups Manifold Interval Real NNReal ENNReal Topology BigOperators

noncomputable section

/-! ## Helper lemmas for derivative of anomaly function D₂ -/

/-- The D-derivative of the anomaly function D₂.
    D₂ γ z = 2πi · (γ₁₀ / denom γ z), so
    D(D₂ γ) = (2πi)⁻¹ · d/dz[2πi · c / denom] = -c² / denom² -/
lemma D_D₂ (γ : SL(2, ℤ)) (z : ℍ) :
    D (D₂ γ) z = - (γ 1 0 : ℂ)^2 / (denom γ z)^2 := by
  have hz_ne : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hderiv : deriv ((D₂ γ) ∘ ofComplex) z =
      deriv (fun w => (2 * π * I * (γ 1 0 : ℂ)) / denom γ w) z := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [comp_apply, ofComplex_apply_of_im_pos hw, D₂, EisensteinSeries.D2]
  simp only [D, hderiv, div_eq_mul_inv, ← zpow_neg_one]
  rw [deriv_const_mul _ (.zpow (differentiableAt_denom γ z) (.inl hz_ne)),
      deriv_denom_zpow γ 1 z]
  simp only [Int.reduceNeg, Int.reduceSub, zpow_neg_one]; field_simp; ring

/-! ## MDifferentiable infrastructure for D₂ -/

/-- D₂ γ is MDifferentiable: it's a constant divided by a linear polynomial. -/
lemma MDifferentiable_D₂ (γ : SL(2, ℤ)) : MDiff (D₂ γ) := fun z => by
  have heq : D₂ γ = (fun w => (2 * π * I * (γ 1 0 : ℂ)) / denom γ w) ∘ (↑) := by ext; rfl
  rw [heq]; exact DifferentiableAt_MDifferentiableAt <|
    .div (differentiableAt_const _) (differentiableAt_denom γ z) (denom_ne_zero γ z)

/-! ## Slash invariance of serreD 1 E₂

This is the hard part: E₂ is NOT modular, so we cannot use `serre_D_slash_invariant`.
We must prove directly that the non-modular terms cancel. -/

/-- The Serre derivative of E₂ is weight-4 slash-invariant.
This requires explicit computation since E₂ is not modular.

**Proof strategy:**
Write serreD 1 E₂ = serreD 2 E₂ + (1/12) E₂². Then:
- (serreD 2 E₂) ∣[4] γ = serreD 2 (E₂ ∣[2] γ) by serre_D_slash_equivariant
- E₂ ∣[2] γ = E₂ - α D₂ γ where α = 1/(2ζ(2)) = 3/π²
- (E₂²) ∣[4] γ = (E₂ ∣[2] γ)²

After expansion, the anomaly terms involving D₂ γ and D(D₂ γ) cancel using:
- D(D₂ γ) = -c²/denom² (from D_D₂)
- The identity α = α² π²/3 (from ζ(2) = π²/6)
-/
lemma serre_DE₂_slash_invariant (γ : SL(2, ℤ)) :
    (serreD 1 E₂) ∣[(4 : ℤ)] γ = serreD 1 E₂ := by
  have hserre12 : serreD 1 E₂ = serreD 2 E₂ + (1 / 12 : ℂ) • (E₂ * E₂) := by
    ext z; simp only [serreD, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]; ring
  have hE₂slash := E₂_slash_transform γ
  ext z
  rw [hserre12]
  simp only [SlashAction.add_slash, Pi.add_apply, ModularForm.SL_smul_slash, Pi.smul_apply,
    smul_eq_mul]
  rw [show (serreD 2 E₂ ∣[(4 : ℤ)] γ) z = serreD 2 (E₂ ∣[(2 : ℤ)] γ) z by
        simpa using congrFun (serre_D_slash_equivariant 2 E₂ E₂_holo' γ) z,
      show ((E₂ * E₂) ∣[(4 : ℤ)] γ) z = (E₂ ∣[(2 : ℤ)] γ) z * (E₂ ∣[(2 : ℤ)] γ) z by
        simpa using congrFun (ModularForm.mul_slash_SL2 (2 : ℤ) (2 : ℤ) γ E₂ E₂) z]
  set α := (1 : ℂ) / (2 * riemannZeta 2) with hα_def
  have hE₂slash_fun : (E₂ ∣[(2 : ℤ)] γ) = E₂ - α • D₂ γ := by
    ext w; simpa using congrFun hE₂slash w
  rw [hE₂slash_fun]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, serreD, Pi.mul_apply]
  rw [show D (E₂ - α • D₂ γ) z = D E₂ z - α * D (D₂ γ) z by
        simp only [D_sub E₂ _ E₂_holo' ((MDifferentiable_D₂ γ).const_smul α),
                   D_smul α _ (MDifferentiable_D₂ γ), Pi.sub_apply, Pi.smul_apply, smul_eq_mul],
      D_D₂ γ z, show D₂ γ z = (2 * π * I * (γ 1 0 : ℂ)) / denom γ z from rfl,
      show α = 3 / π ^ 2 by simp only [hα_def, riemannZeta_two]; field_simp; ring]
  field_simp [UpperHalfPlane.denom_ne_zero γ z, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring_nf
  simp only [Complex.I_sq]
  ring

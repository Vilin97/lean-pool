/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.PressureRecoveryHelpers
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.PressureFunctionals
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.LocalizedTransport

/-!
# From scalar pressure-gradient identification to the cutoff pressure flux

This module is an integration-by-parts bridge. Its input is an explicit
identification of every compact scalar pressure-gradient pairing. It does not
assume a pressure-flux formula or any bound on the pressure at infinity.
-/

@[expose] public section



noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff BigOperators

namespace NavierStokesR3.PressureFluxIdentity

open ProblemStatement Comparison PressureRecovery HarmonicTestFunctionals
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness

theorem fluxFunction_smooth {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fun x : Space => fderiv ℝ χ x (w x)) :=
  (hχ.fderiv_right (m := ∞) (by simp)).clm_apply hw

theorem fluxFunction_hasCompactSupport {χ : Space → ℝ}
    (hcχ : HasCompactSupport χ) (w : Space → Space) :
    HasCompactSupport (fun x : Space => fderiv ℝ χ x (w x)) := by
  apply (hcχ.fderiv ℝ).mono
  intro x hx
  change fderiv ℝ χ x ≠ 0
  intro hzero
  apply hx
  simp only [hzero, _root_.zero_apply]

theorem integrable_pressure_flux {χ π : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hπ : ContDiff ℝ ∞ π) (hw : ContDiff ℝ ∞ w)
    (hcχ : HasCompactSupport χ) :
    Integrable (fun x : Space => π x * fderiv ℝ χ x (w x)) :=
  ConservativeDifference.integrable_mul_test hπ.continuous
    (fluxFunction_smooth hχ hw).continuous (fluxFunction_hasCompactSupport hcχ w)

/-- The scalar compact test associated to one component of the weighted velocity. -/
def weightedComponent (χ : Space → ℝ) (w : Space → Space) (k : Fin 3) : Space → ℝ :=
  fun x => χ x * w x k

theorem weightedComponent_smooth {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) (k : Fin 3) :
    ContDiff ℝ ∞ (weightedComponent χ w k) :=
  hχ.mul (component_contDiff hw k)

theorem weightedComponent_hasCompactSupport {χ : Space → ℝ}
    (hcχ : HasCompactSupport χ) (w : Space → Space) (k : Fin 3) :
    HasCompactSupport (weightedComponent χ w k) := hcχ.mul_right

theorem sum_partial_weightedComponent {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w)
    (hdiv : ∀ x : Space, (∑ k : Fin 3, partialD k w x k) = 0) (x : Space) :
    (∑ k : Fin 3, partialD k (weightedComponent χ w k) x) = fderiv ℝ χ x (w x) := by
  calc
    (∑ k : Fin 3, partialD k (weightedComponent χ w k) x) =
        ∑ k : Fin 3, spatialPartial k (fun y => χ y • w y) x k := by
      apply Finset.sum_congr rfl
      intro k _
      change spatialPartial k (fun y => (χ y • w y) k) x = _
      exact ConservativeDifference.partial_component (hχ.smul hw) k k x
    _ = fderiv ℝ χ x (w x) := by
      simpa only [hdiv x, mul_zero, add_zero] using
        LocalizedDifferenceEnergy.divergence_weighted hχ hw x

/-- The compact flux test is the sum of the differentiated component tests. -/
theorem sum_partial_realTest_weightedComponent {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) (hcχ : HasCompactSupport χ)
    (hdiv : ∀ x : Space, (∑ k : Fin 3, partialD k w x k) = 0) :
    (∑ k : Fin 3, partialCLM k (realTest (weightedComponent χ w k)
      (weightedComponent_smooth hχ hw k) (weightedComponent_hasCompactSupport hcχ w k))) =
    realTest (fun x : Space => fderiv ℝ χ x (w x))
      (fluxFunction_smooth hχ hw) (fluxFunction_hasCompactSupport hcχ w) := by
  ext x
  simp only [sum_apply, partialCLM_realTest, realTest_apply]
  calc
    (∑ k : Fin 3, ((spatialPartial k (weightedComponent χ w k) x : ℝ) : ℂ)) =
        ((∑ k : Fin 3, partialD k (weightedComponent χ w k) x : ℝ) : ℂ) :=
      (map_sum Complex.ofRealCLM _ _).symm
    _ = (fderiv ℝ χ x (w x) : ℂ) :=
      congrArg Complex.ofReal (sum_partial_weightedComponent hχ hw hdiv x)

/-- The sum of all canonical pressure pairings is a complex-linear functional. -/
def canonicalPressureLinear (g : Fin 3 → Fin 3 → Space → ℝ)
    (hg : ∀ i j : Fin 3, Integrable (g i j)) : ComplexTest →ₗ[ℂ] ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3, PressureFunctionals.pressurePairLinear i j (g i j) (hg i j)

@[simp] theorem canonicalPressureLinear_apply (g : Fin 3 → Fin 3 → Space → ℝ)
    (hg : ∀ i j : Fin 3, Integrable (g i j)) (ψ : ComplexTest) :
    canonicalPressureLinear g hg ψ = ∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (g i j) ψ := by
  simp only [canonicalPressureLinear, LinearMap.sum_apply,
      PressureFunctionals.pressurePairLinear_apply]

theorem integrable_canonical_flux_terms {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) (hcχ : HasCompactSupport χ)
    {g : Fin 3 → Fin 3 → Space → ℝ} (hg : ∀ i j : Fin 3, Integrable (g i j))
    (i j : Fin 3) :
    Integrable (fun x : Space => (g i j x : ℂ) * rieszTest i j
      (realTest (fun y : Space => fderiv ℝ χ y (w y))
        (fluxFunction_smooth hχ hw) (fluxFunction_hasCompactSupport hcχ w)) x) :=
  PressureFunctionals.integrable_l1_riesz_pair (hg i j) i j _

/-- Compact integration by parts turns the given scalar pressure-gradient
identification into the actual cutoff pressure flux. -/
theorem pressure_flux_eq_of_gradient_identification
    {π χ : Space → ℝ} {w : Space → Space} {g : Fin 3 → Fin 3 → Space → ℝ}
    (hπ : ContDiff ℝ ∞ π) (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w)
    (hcχ : HasCompactSupport χ) (hg : ∀ i j : Fin 3, Integrable (g i j))
    (hdiv : ∀ x : Space, (∑ k : Fin 3, partialD k w x k) = 0)
    (hgrad : ∀ (k : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ)
      (hcψ : HasCompactSupport ψ),
      (∫ x : Space, partialD k π x * ψ x) =
        -(∑ i : Fin 3, ∑ j : Fin 3,
          pressurePair i j (g i j) (partialCLM k (realTest ψ hψ hcψ))).re) :
    (∫ x : Space, π x * fderiv ℝ χ x (w x)) =
      (∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (g i j)
        (realTest (fun x : Space => fderiv ℝ χ x (w x))
          (fluxFunction_smooth hχ hw) (fluxFunction_hasCompactSupport hcχ w))).re := by
  let η : Fin 3 → ComplexTest := fun k =>
    partialCLM k (realTest (weightedComponent χ w k)
      (weightedComponent_smooth hχ hw k) (weightedComponent_hasCompactSupport hcχ w k))
  let Q : ComplexTest →ₗ[ℂ] ℂ := canonicalPressureLinear g hg
  have hsum : (∑ k : Fin 3, η k) =
      realTest (fun x : Space => fderiv ℝ χ x (w x))
        (fluxFunction_smooth hχ hw) (fluxFunction_hasCompactSupport hcχ w) :=
    sum_partial_realTest_weightedComponent hχ hw hcχ hdiv
  have hint (k : Fin 3) :
      Integrable (fun x : Space => π x * partialD k (weightedComponent χ w k) x) :=
    ConservativeDifference.integrable_mul_test hπ.continuous
      (spatial_partial_contDiff (weightedComponent_smooth hχ hw k) k).continuous
      (CompactEnergy.compact_partial (weightedComponent_hasCompactSupport hcχ w k) k)
  have hscalar (k : Fin 3) :
      (∫ x : Space, π x * partialD k (weightedComponent χ w k) x) = (Q (η k)).re := by
    have hibp :
        (∫ x : Space, partialD k π x * weightedComponent χ w k x) =
          -(∫ x : Space, π x * partialD k (weightedComponent χ w k) x) := by
      simpa only [partialD, mul_comm] using
        CompactEnergy.integral_mul_partial (weightedComponent_smooth hχ hw k) hπ
          (weightedComponent_hasCompactSupport hcχ w k) k
    have h := neg_injective (hibp.symm.trans (hgrad k (weightedComponent χ w k)
      (weightedComponent_smooth hχ hw k) (weightedComponent_hasCompactSupport hcχ w k)))
    simpa only [Q, η, canonicalPressureLinear_apply] using h
  have hfluxsum :
      (∫ x : Space, π x * fderiv ℝ χ x (w x)) =
        ∑ k : Fin 3, ∫ x : Space, π x * partialD k (weightedComponent χ w k) x := by
    calc
      (∫ x : Space, π x * fderiv ℝ χ x (w x)) =
          ∫ x : Space, ∑ k : Fin 3, π x * partialD k (weightedComponent χ w k) x := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change π x * fderiv ℝ χ x (w x) =
            ∑ k : Fin 3, π x * partialD k (weightedComponent χ w k) x
          rw [← sum_partial_weightedComponent hχ hw hdiv x, Finset.mul_sum]
      _ = _ := integral_finsetSum _ (fun k _ => hint k)
  calc
    (∫ x : Space, π x * fderiv ℝ χ x (w x)) =
        ∑ k : Fin 3, ∫ x : Space, π x * partialD k (weightedComponent χ w k) x := hfluxsum
    _ = ∑ k : Fin 3, (Q (η k)).re := Finset.sum_congr rfl (fun k _ => hscalar k)
    _ = (∑ k : Fin 3, Q (η k)).re :=
      (map_sum Complex.reCLM (fun k => Q (η k)) Finset.univ).symm
    _ = (Q (∑ k : Fin 3, η k)).re :=
      congrArg Complex.re (map_sum Q η Finset.univ).symm
    _ = _ := by
      rw [hsum]
      exact congrArg Complex.re (canonicalPressureLinear_apply g hg _)

end NavierStokesR3.PressureFluxIdentity

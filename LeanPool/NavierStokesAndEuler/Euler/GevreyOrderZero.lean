/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevGevreyOperators
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCylinder

/-! Cutoff-independent bounds for the actual order-zero Euler correction source. -/

@[expose] public section


noncomputable section

namespace EulerGevreyOrderZero

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerSobolevL2Product EulerH6Nonlinear EulerH6Pressure
  EulerPacketWeights EulerSobolevGevreyOperators EulerSobolevCoefficientPressure EulerVectorCylinder
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Cache the standard `NormedAddCommGroup (SobolevSpace period q)` instance to shorten
typeclass synthesis. -/
local instance orderZeroGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
/-- Cache the standard `NormedSpace ℝ (SobolevSpace period q)` instance to shorten typeclass
synthesis. -/
local instance orderZeroSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The actual derivative-free algebraic nonlinearity at one complete Sobolev level. -/
def algebraicAt {s : ℕ} (hs : 6 ≤ s)
    (C : Fin 3 → SobolevSpace period s →L[ℝ] SobolevSpace period s)
    (u v : SobolevSpace period s) : SobolevSpace period s :=
  ∑ i : Fin 3, C i (productHq period hs (coordinate 3 i) (coordinate_norm_le 3 i) u v)

/-- The part e·D z_a transports the prescribed background and has no derivative on the error. -/
def backgroundDrift {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (background : SobolevSpace period (s + 1)) (e : SobolevSpace period s) : SobolevSpace period s
        :=
  ∑ i : Fin 4, productHq period hs (L i) (hL i) e (derivativeOperator period s i background)

/-- The actual coefficient-weighted quadratic field has a uniform truncated Gevrey bound. -/
theorem algebraicAt_bound {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N + 6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (C : Fin 3 → SmoothCoefficient period)
    (K : ∀ i, EulerSpatialSobolevInverse.CoefficientJet period standardDirection s (C i))
    (u v : SobolevSpace period s) :
    weightedNorm period 6 N ρ (algebraicAt period hs (fun i => coefficientSobolevOperator period (K
        i)) u v) ≤
      (∑ i : Fin 3, weightedCoefficient period (K i) 6 N ρ) *
        productConstant period 3 * weightedNorm period 6 N ρ u * weightedNorm period 6 N ρ v := by
  apply (weightedNorm_sum_le period 6 N hN ρ hρ Finset.univ _).trans
  calc
    _ ≤ ∑ i : Fin 3, weightedCoefficient period (K i) 6 N ρ *
        (productConstant period 3 * weightedNorm period 6 N ρ u * weightedNorm period 6 N ρ v) := by
      apply Finset.sum_le_sum
      intro i _
      exact (weightedNorm_coefficient period (K i) 6 N hN ρ hρ _).trans
        (mul_le_mul_of_nonneg_left
          (weightedNorm_product period hs N hN ρ hρ (coordinate 3 i) (coordinate_norm_le 3 i) u v)
          (weightedCoefficient_nonneg period (K i) 6 N ρ hρ))
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Background transport is order zero in the error in the actual finite Gevrey norm. -/
theorem backgroundDrift_bound {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N + 6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (background : SobolevSpace period (s + 1)) (e : SobolevSpace period s) :
    weightedNorm period 6 N ρ (backgroundDrift period hs L hL background e) ≤
      productConstant period 3 * weightedNorm period 6 N ρ e *
        ∑ i : Fin 4, weightedNorm period 6 N ρ (derivativeOperator period s i background) := by
  apply (weightedNorm_sum_le period 6 N hN ρ hρ Finset.univ _).trans
  calc
    _ ≤ ∑ i : Fin 4, productConstant period 3 * weightedNorm period 6 N ρ e *
        weightedNorm period 6 N ρ (derivativeOperator period s i background) :=
      Finset.sum_le_sum fun i _ => weightedNorm_product period hs N hN ρ hρ (L i) (hL i) e _
    _ = _ := (Finset.mul_sum ..).symm

/-- The actual order-zero source Z(e)+r_a in the transformed Euler correction equation. -/
def orderZeroSource {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : SobolevSpace period s →L[ℝ] SobolevSpace period s)
    (C : Fin 3 → SobolevSpace period s →L[ℝ] SobolevSpace period s)
    (background : SobolevSpace period (s + 1)) (r e : SobolevSpace period s) : SobolevSpace period s
        :=
  r + backgroundDrift period hs L hL background e + C0 e +
    algebraicAt period hs C (truncateOperator period s background) e +
    algebraicAt period hs C e (truncateOperator period s background) + algebraicAt period hs C e e

/-- The source's actual order-zero forcing is bounded by residual, linear, and quadratic error
energies, with no cutoff-dependent constant. -/
theorem orderZeroSource_bound {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N + 6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : SmoothCoefficient period) (K0 : EulerSpatialSobolevInverse.CoefficientJet period
        standardDirection s C0)
    (C : Fin 3 → SmoothCoefficient period)
    (K : ∀ i, EulerSpatialSobolevInverse.CoefficientJet period standardDirection s (C i))
    (background : SobolevSpace period (s + 1)) (r e : SobolevSpace period s) :
    weightedNorm period 6 N ρ (orderZeroSource period hs L hL (coefficientSobolevOperator period K0)
      (fun i => coefficientSobolevOperator period (K i)) background r e) ≤
      weightedNorm period 6 N ρ r +
      (productConstant period 3 * (∑ i : Fin 4, weightedNorm period 6 N ρ (derivativeOperator
          period s i background)) +
        weightedCoefficient period K0 6 N ρ +
        2 * (∑ i : Fin 3, weightedCoefficient period (K i) 6 N ρ) * productConstant period 3 *
          weightedNorm period 6 N ρ (truncateOperator period s background)) * weightedNorm period 6
              N ρ e +
      (∑ i : Fin 3, weightedCoefficient period (K i) 6 N ρ) * productConstant period 3 *
          (weightedNorm period 6 N ρ e)^2 := by
  let A := fun i => coefficientSobolevOperator period (K i)
  let z := truncateOperator period s background
  let d := backgroundDrift period hs L hL background e
  let l := coefficientSobolevOperator period K0 e
  let a := algebraicAt period hs A z e
  let b := algebraicAt period hs A e z
  let c := algebraicAt period hs A e e
  let W := weightedNorm period 6 N ρ (s := s)
  have hsum : W (r+d+l+a+b+c) ≤ W r+W d+W l+W a+W b+W c := by
    apply (weightedNorm_add_le period 6 N hN ρ hρ _ c).trans
    apply add_le_add _ le_rfl
    apply (weightedNorm_add_le period 6 N hN ρ hρ _ b).trans
    apply add_le_add _ le_rfl
    apply (weightedNorm_add_le period 6 N hN ρ hρ _ a).trans
    apply add_le_add _ le_rfl
    apply (weightedNorm_add_le period 6 N hN ρ hρ _ l).trans
    apply add_le_add _ le_rfl
    exact weightedNorm_add_le period 6 N hN ρ hρ r d
  have hd := backgroundDrift_bound period hs N hN ρ hρ L hL background e
  have hl := weightedNorm_coefficient period K0 6 N hN ρ hρ e
  have ha := algebraicAt_bound period hs N hN ρ hρ C K z e
  have hb := algebraicAt_bound period hs N hN ρ hρ C K e z
  have hc := algebraicAt_bound period hs N hN ρ hρ C K e e
  have hsum' := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (W r)) hd) hl)
      ha) hb) hc
  exact hsum.trans (hsum'.trans_eq (by dsimp [W,z]; ring))

end EulerGevreyOrderZero

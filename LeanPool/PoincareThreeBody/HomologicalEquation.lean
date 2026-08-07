/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.Perturbation
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

/-!
# The first homological equation

This file verifies the product-rule step in Poincaré's perturbative argument.  If two families
Poisson-commute for all nearby parameter values, differentiating at the Kepler limit gives the sum
of the two cross brackets.  The hypotheses expose precisely the mixed derivatives which must later
be obtained from joint analyticity.
-/

namespace LeanPool.PoincareThreeBody


/-- Differentiating the canonical Poisson bracket with respect to a parameter gives the two cross
brackets.  The derivative hypotheses are stated coordinatewise to isolate the required interchange
of the mass derivative and the phase derivative. -/
theorem hasDerivAt_poissonBracket_family
    {F H : ℝ → PhaseSpace → ℝ} {F₁ H₁ : PhaseSpace → ℝ} {s : PhaseSpace}
    (hF : ∀ i, HasDerivAt
      (fun mass ↦ fderiv ℝ (F mass) s (coordinateVector i))
      (fderiv ℝ F₁ s (coordinateVector i)) 0)
    (hH : ∀ i, HasDerivAt
      (fun mass ↦ fderiv ℝ (H mass) s (coordinateVector i))
      (fderiv ℝ H₁ s (coordinateVector i)) 0) :
    HasDerivAt (fun mass ↦ poissonBracket (F mass) (H mass) s)
      (poissonBracket F₁ (H 0) s + poissonBracket (F 0) H₁ s) 0 := by
  have h02 := (hF 0).mul (hH 2)
  have h20 := (hF 2).mul (hH 0)
  have h13 := (hF 1).mul (hH 3)
  have h31 := (hF 3).mul (hH 1)
  have hraw := (h02.sub h20).add (h13.sub h31)
  apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards [] with mass
    unfold poissonBracket
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
  · unfold poissonBracket
    ring

/-- The coefficient of the parameter in a vanishing Poisson bracket is the first homological
equation. -/
theorem firstHomologicalEquation_of_poissonBracket_zero
    {F H : ℝ → PhaseSpace → ℝ} {F₁ H₁ : PhaseSpace → ℝ} {s : PhaseSpace}
    (hF : ∀ i, HasDerivAt
      (fun mass ↦ fderiv ℝ (F mass) s (coordinateVector i))
      (fderiv ℝ F₁ s (coordinateVector i)) 0)
    (hH : ∀ i, HasDerivAt
      (fun mass ↦ fderiv ℝ (H mass) s (coordinateVector i))
      (fderiv ℝ H₁ s (coordinateVector i)) 0)
    (hcommutes : ∀ᶠ mass in nhds 0, poissonBracket (F mass) (H mass) s = 0) :
    poissonBracket F₁ (H 0) s + poissonBracket (F 0) H₁ s = 0 := by
  have hbracket := hasDerivAt_poissonBracket_family hF hH
  have heq : (fun mass ↦ poissonBracket (F mass) (H mass) s) =ᶠ[nhds 0]
      (fun _ : ℝ ↦ 0) := hcommutes.mono fun mass hmass ↦ hmass
  have hzero : HasDerivAt (fun _ : ℝ ↦ 0)
      (poissonBracket F₁ (H 0) s + poissonBracket (F 0) H₁ s) 0 :=
    hbracket.congr_of_eventuallyEq heq.symm
  exact hzero.unique (hasDerivAt_const 0 0)

/-- For the restricted three-body Hamiltonian, the Hamiltonian cross term in the first
homological equation is the explicit first mass perturbation. -/
theorem firstHomologicalEquation_cr3bp
    {F : ℝ → PhaseSpace → ℝ} {F₁ : PhaseSpace → ℝ} {s : PhaseSpace}
    (hF : ∀ i, HasDerivAt
      (fun mass ↦ fderiv ℝ (F mass) s (coordinateVector i))
      (fderiv ℝ F₁ s (coordinateVector i)) 0)
    (hH : ∀ i, HasDerivAt
      (fun mass ↦ fderiv ℝ (hamiltonian mass) s (coordinateVector i))
      (fderiv ℝ firstMassPerturbation s (coordinateVector i)) 0)
    (hcommutes : ∀ᶠ mass in nhds 0,
      poissonBracket (F mass) (hamiltonian mass) s = 0) :
    poissonBracket F₁ (hamiltonian 0) s +
      poissonBracket (F 0) firstMassPerturbation s = 0 := by
  exact firstHomologicalEquation_of_poissonBracket_zero hF hH hcommutes

end LeanPool.PoincareThreeBody

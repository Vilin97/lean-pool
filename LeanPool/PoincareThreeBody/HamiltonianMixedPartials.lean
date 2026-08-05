/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.HomologicalEquation
import LeanPool.PoincareThreeBody.MixedPartials

/-!
# Mixed derivatives of the restricted three-body Hamiltonian

Joint analyticity permits the mass and phase derivatives of the Hamiltonian to be interchanged.
Combining this fact with the explicit mass derivative identifies the Hamiltonian term in
Poincaré's first homological equation.
-/

namespace LeanPool.PoincareThreeBody

open Challenge.PoincareThreeBody

/-- Near a collision-free phase point, the joint parameter coefficient of the Hamiltonian is the
explicit first mass perturbation. -/
theorem parameterCoefficient_hamiltonian_eventuallyEq
    {s : PhaseSpace} (hs : (0, s) ∈ collisionFree) :
    parameterCoefficient (Function.uncurry hamiltonian) =ᶠ[nhds s]
      firstMassPerturbation := by
  rcases hs with ⟨hfirst, hsecond⟩
  have hfirstEventually : ∀ᶠ y in nhds s, firstPrimaryDistanceSq 0 y ≠ 0 := by
    have hcontinuous : Continuous (fun y ↦ firstPrimaryDistanceSq 0 y) := by
      unfold firstPrimaryDistanceSq
      fun_prop
    exact hcontinuous.continuousAt.eventually_ne hfirst
  have hsecondEventually : ∀ᶠ y in nhds s, secondPrimaryDistanceSq 0 y ≠ 0 := by
    have hcontinuous : Continuous (fun y ↦ secondPrimaryDistanceSq 0 y) := by
      unfold secondPrimaryDistanceSq
      fun_prop
    exact hcontinuous.continuousAt.eventually_ne hsecond
  filter_upwards [hfirstEventually, hsecondEventually] with y hyFirst hySecond
  have hy : (0, y) ∈ collisionFree := ⟨hyFirst, hySecond⟩
  have hjointDifferentiable : DifferentiableAt ℝ
      (Function.uncurry hamiltonian) (0, y) :=
    (hamiltonian_analyticAt hy).differentiableAt
  rw [← deriv_curry_left hjointDifferentiable]
  exact deriv_hamiltonian_mass_zero hy

/-- The mass derivative of every phase partial of the Hamiltonian is the corresponding phase
partial of the explicit perturbation. -/
theorem hasDerivAt_hamiltonian_phasePartial_mass_zero
    {s : PhaseSpace} (hs : (0, s) ∈ collisionFree) (i : Fin 4) :
    HasDerivAt
      (fun mass ↦ fderiv ℝ (hamiltonian mass) s (coordinateVector i))
      (fderiv ℝ firstMassPerturbation s (coordinateVector i)) 0 := by
  have hsmooth : ContDiffAt ℝ 2 (Function.uncurry hamiltonian) (0, s) :=
    (hamiltonian_analyticAt hs).contDiffAt
  have hmixed := hasDerivAt_fderiv_curry_right
    (G := Function.uncurry hamiltonian) (b := s) (v := coordinateVector i) hsmooth
  have hderivativeMaps :=
    (parameterCoefficient_hamiltonian_eventuallyEq hs).fderiv_eq (𝕜 := ℝ)
  have hderivative := congrArg (fun L ↦ L (coordinateVector i)) hderivativeMaps
  exact hmixed.congr_deriv hderivative

/-- A jointly `C²` candidate which commutes with the physical Hamiltonian satisfies the explicit
first homological equation at every collision-free phase point over `μ = 0`. -/
theorem firstHomologicalEquation_cr3bp_of_contDiffAt
    {F : ℝ → PhaseSpace → ℝ} {s : PhaseSpace}
    (hs : (0, s) ∈ collisionFree)
    (hF : ContDiffAt ℝ 2 (Function.uncurry F) (0, s))
    (hcommutes : ∀ᶠ mass in nhds 0,
      poissonBracket (F mass) (hamiltonian mass) s = 0) :
    poissonBracket (parameterCoefficient (Function.uncurry F)) (hamiltonian 0) s +
      poissonBracket (F 0) firstMassPerturbation s = 0 := by
  apply firstHomologicalEquation_cr3bp
  · intro i
    exact hasDerivAt_fderiv_curry_right
      (G := Function.uncurry F) (b := s) (v := coordinateVector i) hF
  · exact hasDerivAt_hamiltonian_phasePartial_mass_zero hs
  · exact hcommutes

/-- The hypotheses used in the challenge imply the explicit first homological equation at every
collision-free phase point over the Kepler limit. -/
theorem IsFirstIntegralFamily.firstHomologicalEquation_mass_zero
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F) (hfirstIntegral : IsFirstIntegralFamily δ F)
    {s : PhaseSpace} (hs : (0, s) ∈ collisionFree) :
    poissonBracket (parameterCoefficient (Function.uncurry F)) (hamiltonian 0) s +
      poissonBracket (F 0) firstMassPerturbation s = 0 := by
  have hzeroDomain : (0, s) ∈ parameterDomain δ := ⟨by simpa using hδ, hs⟩
  have hFsmooth : ContDiffAt ℝ 2 (Function.uncurry F) (0, s) :=
    (hanalytic (0, s) hzeroDomain).contDiffAt
  have hmassSmall : ∀ᶠ mass in nhds (0 : ℝ), |mass| < δ := by
    have habs : ContinuousAt (fun mass : ℝ ↦ |mass|) 0 := by fun_prop
    exact habs.eventually (Iio_mem_nhds (by simpa using hδ))
  rcases hs with ⟨hfirst, hsecond⟩
  have hfirstEventually : ∀ᶠ mass in nhds (0 : ℝ),
      firstPrimaryDistanceSq mass s ≠ 0 := by
    have hcontinuous : Continuous (fun mass ↦ firstPrimaryDistanceSq mass s) := by
      unfold firstPrimaryDistanceSq
      fun_prop
    exact hcontinuous.continuousAt.eventually_ne hfirst
  have hsecondEventually : ∀ᶠ mass in nhds (0 : ℝ),
      secondPrimaryDistanceSq mass s ≠ 0 := by
    have hcontinuous : Continuous (fun mass ↦ secondPrimaryDistanceSq mass s) := by
      unfold secondPrimaryDistanceSq
      fun_prop
    exact hcontinuous.continuousAt.eventually_ne hsecond
  have hcommutes : ∀ᶠ mass in nhds (0 : ℝ),
      poissonBracket (F mass) (hamiltonian mass) s = 0 := by
    filter_upwards [hmassSmall, hfirstEventually, hsecondEventually]
      with mass hmass hfirstMass hsecondMass
    exact hfirstIntegral (mass, s) ⟨hmass, hfirstMass, hsecondMass⟩
  exact firstHomologicalEquation_cr3bp_of_contDiffAt
    ⟨hfirst, hsecond⟩ hFsmooth hcommutes

end LeanPool.PoincareThreeBody

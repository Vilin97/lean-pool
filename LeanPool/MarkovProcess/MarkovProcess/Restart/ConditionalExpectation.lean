/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Conditional expectation from restricted restart laws

This file records a generic measure-theoretic bridge from an event-restricted future-law identity
to a conditional-expectation identity.  The restart hypothesis is required after restriction to
every event in the conditioning measurable space.  Its specialization to the whole space alone is
only an unconditional distributional identity and is not enough for this conclusion.

No stochastic process, Markov property, or path-space construction is asserted here.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess

noncomputable section

variable {Omega beta E : Type*} {m : MeasurableSpace Omega}
  {mOmega : MeasurableSpace Omega} {mBeta : MeasurableSpace beta}
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- If the law of `Y` after restriction to every conditioning event is obtained by mixing
`kappa`, then integrating any bounded strongly measurable observable against `kappa` gives the
corresponding conditional expectation. -/
theorem condExp_comp_ae_eq_integral_kernel_of_restrict_map
    (mu : @Measure Omega mOmega) [IsFiniteMeasure mu]
    (kappa : @Kernel Omega beta mOmega mBeta) [IsMarkovKernel kappa]
    (Y : Omega → beta) (hY : @Measurable Omega beta mOmega mBeta Y)
    (hm : m ≤ mOmega)
    (hJoint : ∀ A : Set Omega, MeasurableSet[m] A →
      (mu.restrict A).map Y = kappa ∘ₘ (mu.restrict A))
    (F : beta → E) (hF : StronglyMeasurable F)
    (hFm : StronglyMeasurable[m] (fun omega ↦ ∫ y, F y ∂kappa omega))
    (C : Real) (hFC : ∀ y, ‖F y‖ ≤ C) :
    mu[fun omega ↦ F (Y omega)|m] =ᵐ[mu]
      fun omega ↦ ∫ y, F y ∂kappa omega := by
  have hfMeas : AEStronglyMeasurable (fun omega ↦ F (Y omega)) mu :=
    (hF.comp_measurable hY).aestronglyMeasurable
  have hfInt : Integrable (fun omega ↦ F (Y omega)) mu :=
    Integrable.of_bound hfMeas C (ae_of_all _ fun omega ↦ hFC (Y omega))
  have hgMeas : AEStronglyMeasurable[m]
      (fun omega ↦ ∫ y, F y ∂kappa omega) mu :=
    hFm.aestronglyMeasurable
  refine (ae_eq_condExp_of_forall_setIntegral_eq
    (m := m) (m₀ := mOmega) (μ := mu) hm hfInt ?_ ?_ hgMeas).symm
  · intro A _hA _hmuA
    exact Integrable.of_bound
      (hF.integral_kernel.aestronglyMeasurable.restrict)
      C (ae_of_all _ fun omega ↦ by
        simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
          norm_integral_le_of_norm_le_const
            (μ := kappa omega) (ae_of_all _ hFC))
  · intro A hA _hmuA
    have hFA : Integrable F ((mu.restrict A).map Y) := by
      rw [integrable_map_measure hF.aestronglyMeasurable hY.aemeasurable]
      exact hfInt.restrict
    have hFAComp : Integrable F (kappa ∘ₘ (mu.restrict A)) := by
      rw [← hJoint A hA]
      exact hFA
    rw [Measure.comp_eq_comp_const_apply] at hFAComp
    have hIntegralComp := Kernel.integral_comp hFAComp
    calc
      ∫ omega in A, (∫ y, F y ∂kappa omega) ∂mu =
          ∫ omega, (∫ y, F y ∂kappa omega) ∂(mu.restrict A) := rfl
      _ = ∫ y, F y ∂(kappa ∘ₘ (mu.restrict A)) :=
        by simpa only [Kernel.const_apply] using! hIntegralComp.symm
      _ = ∫ y, F y ∂((mu.restrict A).map Y) := by rw [hJoint A hA]
      _ = ∫ omega, F (Y omega) ∂(mu.restrict A) := by
        rw [integral_map hY.aemeasurable hF.aestronglyMeasurable]
      _ = ∫ omega in A, F (Y omega) ∂mu := rfl

end
end MarkovProcess

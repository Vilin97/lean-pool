/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Restart.ConditionalExpectation
import LeanPool.MarkovProcess.MarkovProcess.Path.Shift

/-!
# Deterministic-time conditional restart on continuous paths

This file specializes the generic conditional-expectation bridge to canonical continuous-path
space.  The required input is the full future restart identity after restriction to every event in
the canonical filtration at the restart time.  An unconditional shifted-law identity is only the
special case of the input for the whole path space and does not imply the result below.

The theorem is a conditional API: it does not prove its restricted restart-law hypothesis and does
not by itself associate a Markov or Hunt process with a transition semigroup.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ContinuousPath

noncomputable section

variable {alpha E : Type*} [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- An event-restricted whole-future restart identity gives the deterministic-time conditional
Markov formula for every bounded strongly measurable functional of the shifted path. -/
theorem condExp_shift_ae_eq_integral_pathKernel_of_restrict_map
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (x : alpha) (S : NNReal)
    (hRestart : ∀ A : Set (ContinuousPath alpha),
      MeasurableSet[canonicalFiltration (alpha := alpha) S] A →
        ((Q x).restrict A).map (shift S) =
          Kernel.comap Q (coordinateProcess (alpha := alpha) S)
              (measurable_coordinateProcess S) ∘ₘ ((Q x).restrict A))
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : Real) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    (Q x)[fun omega ↦ F (shift S omega)|canonicalFiltration (alpha := alpha) S] =ᵐ[Q x]
      fun omega ↦ ∫ eta, F eta ∂Q (omega S) := by
  let kappa : Kernel (ContinuousPath alpha) (ContinuousPath alpha) :=
    Kernel.comap Q (coordinateProcess (alpha := alpha) S)
      (measurable_coordinateProcess S)
  let : IsMarkovKernel kappa := by
    dsimp only [kappa]
    infer_instance
  have hFm : StronglyMeasurable[canonicalFiltration (alpha := alpha) S]
      (fun omega ↦ ∫ eta, F eta ∂kappa omega) := by
    have hBase : StronglyMeasurable[canonicalFiltration (alpha := alpha) S]
        (fun omega ↦ ∫ eta, F eta ∂Q (omega S)) :=
      hF.integral_kernel.comp_measurable
        (measurable_coordinateProcess_canonicalFiltration S)
    simpa only [kappa, Kernel.comap_apply, coordinateProcess_apply] using hBase
  have h := condExp_comp_ae_eq_integral_kernel_of_restrict_map
    (Q x) kappa (shift S) (measurable_shift_fixed S)
    ((canonicalFiltration (alpha := alpha)).le S)
    (by simpa only [kappa] using hRestart) F hF hFm C hFC
  simpa only [kappa, Kernel.comap_apply, coordinateProcess_apply] using h

end
end ContinuousPath
end MarkovProcess

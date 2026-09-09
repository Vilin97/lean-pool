/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.HeatAllOrders

@[expose] public section

/-! Transfer of continuous real inequalities from actual smooth H∞ representatives to finite
  Sobolev fields. -/

noncomputable section

namespace EulerSmoothInequalityTransfer

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerMetricTransport EulerSobolevHeat
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Every continuous inequality proved for actual smooth H∞ representatives passes to the genuine finite Sobolev space. -/
theorem binary_le_of_smooth {q : ℕ}
    (F G : SobolevSpace period q × SobolevSpace period q → ℝ) (hF : Continuous F) (hG : Continuous
      G)
    (hbound : ∀ (u v : SobolevSpace period q) (f g : LiftDomain period → Vector3),
      (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f →
      (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g →
      (∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) →
      (∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) →
      (∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period))
        →
      (∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure period))
        →
      F (u,v) ≤ G (u,v)) (u v : SobolevSpace period q) : F (u,v) ≤ G (u,v) := by
  let U : ℕ → SobolevSpace period q := fun n => restrictOperator period (by omega : q ≤ q+3)
    (smoothApprox period q n u)
  let V : ℕ → SobolevSpace period q := fun n => restrictOperator period (by omega : q ≤ q+3)
    (smoothApprox period q n v)
  have hU : Filter.Tendsto U Filter.atTop (𝓝 u) := smoothApprox_tendsto period u
  have hV : Filter.Tendsto V Filter.atTop (𝓝 v) := smoothApprox_tendsto period v
  have hp : Filter.Tendsto (fun n => (U n,V n)) Filter.atTop (𝓝 (u,v)) := hU.prodMk_nhds hV
  have hleft : Filter.Tendsto (fun n => F (U n,V n)) Filter.atTop (𝓝 (F (u,v))) := (hF.tendsto
    (u,v)).comp hp
  have hright : Filter.Tendsto (fun n => G (U n,V n)) Filter.atTop (𝓝 (G (u,v))) := (hG.tendsto
    (u,v)).comp hp
  apply le_of_tendsto_of_tendsto hleft hright
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨f,hf,hfs,hfL⟩ := smoothApprox_representative_all period n u
  obtain ⟨g,hg,hgs,hgL⟩ := smoothApprox_representative_all period n v
  exact hbound (U n) (V n) f g hf hg hfs hgs hfL hgL

end EulerSmoothInequalityTransfer

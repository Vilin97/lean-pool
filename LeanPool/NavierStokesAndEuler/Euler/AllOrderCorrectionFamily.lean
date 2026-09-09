/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderCorrectionBudget
import LeanPool.NavierStokesAndEuler.Euler.AllOrderCorrectionStability
import LeanPool.NavierStokesAndEuler.Euler.InviscidCorrectionCompatibility

/-! Constructed compatible inviscid corrections at every finite Sobolev order. -/

@[expose] public section


noncomputable section

namespace EulerAllOrderCorrectionFamily

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerCorrectionOperators EulerCorrectionEnergyData EulerAllOrderCorrectionData
  EulerAllOrderCorrectionBudget EulerCorrectionStabilityBudget EulerCorrectionLowerData
  EulerInviscidCorrectionCompatibility EulerGevreyMetricEstimate EulerVolterraConvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual finite-order correction chosen from the proved global nonlinear construction. -/
def solution {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) : C(Icc (0 : ℝ) T,SobolevSpace period (q+1)) :=
  Classical.choose (finite_exists period hT A B q hq)

/-- The constructed finite-order correction has zero initial trace. -/
theorem solution_initial {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) : solution period hT A B q hq ⟨0,le_rfl,hT.le⟩=0 :=
  (Classical.choose_spec (finite_exists period hT A B q hq)).1

/-- The constructed finite-order correction satisfies the actual lifted divergence constraint. -/
theorem solution_divergence {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    value period (solution period hT A B q hq t) ∈ divergenceFreeSpace period A.κ A.direction :=
  (Classical.choose_spec (finite_exists period hT A B q hq)).2.1 t

/-- Every retained cutoff of the constructed correction has the proved common energy bound. -/
theorem solution_energy {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (P : ℕ) (hPN : P ≤ q - 4) (hP : P + 6 ≤ q + 1) (t : Icc (0 : ℝ) T) :
    energyNorm period P hP (B.radius t) (B.metric.operatorPath period t)
      (solution period hT A B q hq t) ≤ B.delta/2 :=
  (Classical.choose_spec (finite_exists period hT A B q hq)).2.2.1 P hPN hP t

/-- The constructed correction satisfies the actual nonlinear projected-pressure equation at every
interior time. -/
theorem solution_hasDerivAt {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => value period (extendPath T hT.le (solution period hT A B q hq) r))
      (value period (((A.atOrder period q).coefficients period hq).apply
        ⟨t,ht.1.le,ht.2.le⟩ (solution period hT A B q hq ⟨t,ht.1.le,ht.2.le⟩))) t :=
  (Classical.choose_spec (finite_exists period hT A B q hq)).2.2.2 t ht

/-- The separately constructed solutions are genuinely the same correction after restriction;
uniqueness is proved from their actual equations. -/
theorem solution_compatible {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) :
    (truncateOperator period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      (solution period hT A B (q+1) (hq.trans (Nat.le_succ q))) = solution period hT A B q hq := by
  have hs : StabilityBudget period hT.le
      (lowerData period (A.atOrder period (q+1)) (A.metric.jet q) (A.linear.jet q)
        (fun i => (A.quadratic i).jet q) (A.metric.continuous q) (A.linear.continuous q)
        (fun i => (A.quadratic i).continuous q)) := by
    rw [A.lower_atOrder period q]
    exact stabilityBudget period hT A B q
  apply inviscid_corrections_compatible period hq T hT.le (A.atOrder period (q+1))
    (A.metric.jet q) (A.linear.jet q) (fun i => (A.quadratic i).jet q)
    (A.metric.continuous q) (A.linear.continuous q) (fun i => (A.quadratic i).continuous q)
    (solution period hT A B (q+1) (hq.trans (Nat.le_succ q)))
    (solution_hasDerivAt period hT A B (q+1) (hq.trans (Nat.le_succ q))) hs
    (solution period hT A B q hq)
  · simpa only [A.lower_atOrder period q] using solution_hasDerivAt period hT A B q hq
  · rw [solution_initial,solution_initial,map_zero]
  · intro t
    change value period (A.approximation.realization ((q+1)+1) t) ∈ _
    rw [A.approximation.value_eq]
    exact B.divergence t
  · exact solution_divergence period hT A B (q+1) (hq.trans (Nat.le_succ q))
  · exact solution_divergence period hT A B q hq

/-- Adjacent finite-order solutions have exactly the same underlying L² field. -/
theorem solution_value_succ {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    value period (solution period hT A B (q+1) (hq.trans (Nat.le_succ q)) t) =
      value period (solution period hT A B q hq t) :=
  congrArg (fun f => value period (f t)) (solution_compatible period hT A B q hq)

end EulerAllOrderCorrectionFamily

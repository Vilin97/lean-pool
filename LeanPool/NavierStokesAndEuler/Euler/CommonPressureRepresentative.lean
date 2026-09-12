/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.GraphPressurePotential
public import LeanPool.NavierStokesAndEuler.Euler.SobolevPointEvaluation
import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothPressureRepresentative
import LeanPool.NavierStokesAndEuler.Euler.SobolevJointEvaluation
import LeanPool.NavierStokesAndEuler.Euler.ClassicalDivergence
import LeanPool.NavierStokesAndEuler.Euler.CorrectionSourceRestriction
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderCorrectionBudget
import LeanPool.NavierStokesAndEuler.Euler.AllOrderCorrectionStability
import LeanPool.NavierStokesAndEuler.Euler.InviscidCorrectionCompatibility

/-! A canonical, jointly continuous representative of the constructed common signed pressure. -/

section

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

end
end

end

section

/-! The actual nonlinear source and signed coercive pressure agree across the constructed Sobolev
solutions. -/

@[expose] public section

noncomputable section

namespace EulerAllOrderPressureCoherence

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCorrectionOperators EulerCorrectionLowerData EulerCorrectionSourceRestriction
  EulerAllOrderCorrectionData EulerAllOrderCorrectionBudget EulerAllOrderCorrectionFamily
   EulerSobolevCoefficientPressure
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual continuous nonlinear raw source at a finite Sobolev order. -/
def rawSourcePath {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) : C(Icc (0 : ℝ) T,SobolevSpace period q) :=
  rawPath period hq (A.atOrder period q) (solution period hT A B q hq)

/-- The actual continuous signed coercive pressure at a finite Sobolev order. -/
def signedPressurePath {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) : C(Icc (0 : ℝ) T,SobolevSpace period q) :=
  pressurePath period hq (A.atOrder period q) (solution period hT A B q hq)

/-- The genuine raw sources of the constructed solutions restrict exactly across adjacent orders. -/
theorem rawSourcePath_truncate {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    truncateOperator period q (rawSourcePath period hT A B (q+1) (hq.trans (Nat.le_succ q)) t) =
      rawSourcePath period hT A B q hq t := by
  have h := truncate_rawSource period hq (A.atOrder period (q+1))
    (A.metric.jet q) (A.linear.jet q) (fun i => (A.quadratic i).jet q)
    (A.metric.continuous q) (A.linear.continuous q) (fun i => (A.quadratic i).continuous q)
    t (solution period hT A B (q+1) (hq.trans (Nat.le_succ q)) t)
  rw [A.lower_atOrder period q] at h
  have he := congrArg (fun f => f t) (solution_compatible period hT A B q hq)
  change truncateOperator period (q+1) (solution period hT A B (q+1) (hq.trans (Nat.le_succ q)) t) =
    solution period hT A B q hq t at he
  rw [he] at h
  exact h

/-- Adjacent genuine raw sources represent the same actual L² field. -/
theorem rawSourcePath_value_succ {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    value period (rawSourcePath period hT A B (q+1) (hq.trans (Nat.le_succ q)) t) =
      value period (rawSourcePath period hT A B q hq t) :=
  congrArg (value period (q := q)) (rawSourcePath_truncate period hT A B q hq t)

/-- The actual signed coercive pressures represent the same L² field at adjacent Sobolev orders. -/
theorem signedPressurePath_value_succ {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period
    hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    value period (signedPressurePath period hT A B (q+1) (hq.trans (Nat.le_succ q)) t) =
      value period (signedPressurePath period hT A B q hq t) := by
  change -value period (pressureSobolevOperator period (A.metric.jet (q+1) t) A.κ A.direction
    A.coercivity A.coercivity_pos (A.metric_pos t)
    (rawSourcePath period hT A B (q+1) (hq.trans (Nat.le_succ q)) t)) =
      -value period (pressureSobolevOperator period (A.metric.jet q t) A.κ A.direction
        A.coercivity A.coercivity_pos (A.metric_pos t) (rawSourcePath period hT A B q hq t))
  rw [pressureSobolevOperator_value,pressureSobolevOperator_value,rawSourcePath_value_succ]

/-- Every finite-order signed pressure represents the same actual base pressure. -/
theorem signedPressurePath_value_base {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period
    hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    value period (signedPressurePath period hT A B q hq t) =
      value period (signedPressurePath period hT A B 6 le_rfl t) := by
  exact Nat.le_induction (P := fun n hn => value period (signedPressurePath period hT A B n hn t) =
      value period (signedPressurePath period hT A B 6 le_rfl t)) rfl
    (fun n hn ih => (signedPressurePath_value_succ period hT A B n hn t).trans ih) q hq

/-- The common actual signed pressure is a continuous L² path. -/
def commonPressure {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A) :
    C(Icc (0 : ℝ) T,LiftL2 period) :=
  (valueOperator period 6).compLeftContinuous ℝ (Icc (0 : ℝ) T) (signedPressurePath period hT A B 6
      le_rfl)

/-- Every finite-order pressure realizes the common pressure field. -/
theorem signedPressurePath_value_common {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period
    hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    value period (signedPressurePath period hT A B q hq t)=commonPressure period hT A B t :=
  signedPressurePath_value_base period hT A B q hq t

/-- The common actual correction pressure belongs to the closed lifted gradient subspace. -/
theorem commonPressure_gradient {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (t : Icc (0 : ℝ) T) : commonPressure period hT A B t ∈ gradientSpace period A.κ A.direction :=
  (A.atOrder period 6).pressure_mem_gradient period le_rfl t (solution period hT A B 6 le_rfl t)

end EulerAllOrderPressureCoherence

end
end

end

section

/-! Smooth actual pressure and graph potentials of the constructed common inviscid correction. -/

section

/-! A common actual lifted inviscid correction with genuine jets of every order and smooth spatial
representatives. -/

@[expose] public section

noncomputable section

namespace EulerAllOrderLiftedCorrection

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerAllOrderCorrectionData
  EulerAllOrderCorrectionBudget EulerAllOrderCorrectionFamily EulerVolterraConvolution
  EulerMetricTransport  EulerSmoothPressureRepresentative EulerClassicalDivergence
      EulerTransportDerivatives
  EulerGevreyMetricEstimate
open scoped Topology ContDiff

variable (period : ℝ) [Fact (0 < period)]

/-- The independently constructed finite-order corrections all represent the same actual L² field.
-/
theorem solution_value_base {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    value period (solution period hT A B q hq t) = value period (solution period hT A B 6 le_rfl t)
        := by
  exact Nat.le_induction (P := fun n hn => value period (solution period hT A B n hn t) =
      value period (solution period hT A B 6 le_rfl t)) rfl
    (fun n hn ih => (solution_value_succ period hT A B n hn t).trans ih) q hq

/-- The common continuous L² path constructed from the genuine finite-order nonlinear solves. -/
def commonPath {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A) :
    C(Icc (0 : ℝ) T,LiftL2 period) :=
  (valueOperator period 7).compLeftContinuous ℝ (Icc (0 : ℝ) T) (solution period hT A B 6 le_rfl)

/-- Every finite-order constructed path realizes the common actual L² path. -/
theorem solution_value_common {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    value period (solution period hT A B q hq t)=commonPath period hT A B t :=
  solution_value_base period hT A B q hq t

/-- The common constructed correction has zero initial trace. -/
theorem commonPath_initial {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A) :
    commonPath period hT A B ⟨0,le_rfl,hT.le⟩=0 := by
  change value period (solution period hT A B 6 le_rfl ⟨0,le_rfl,hT.le⟩)=0
  rw [solution_initial]
  rfl

/-- The common path belongs to the genuine closed lifted divergence-free subspace. -/
theorem commonPath_divergence {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (t : Icc (0 : ℝ) T) : commonPath period hT A B t ∈ divergenceFreeSpace period A.κ A.direction :=
  solution_divergence period hT A B 6 le_rfl t

/-- An actual strong derivative jet of any prescribed order for the common nonlinear solution. -/
def commonJet {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (n : ℕ) (t : Icc (0 : ℝ) T) : SpatialJet period standardDirection n (commonPath period hT A B
        t) := by
  rw [← solution_value_common period hT A B (n+6) (by omega) t]
  exact EulerH6Pressure.SpatialJet.restrict
    (toJet period (solution period hT A B (n+6) (by omega) t)) n (by omega)

/-- Every external cutoff of the common solution retains the actual uniform Gevrey metric bound. -/
theorem commonPath_energy {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (P : ℕ) (t : Icc (0 : ℝ) T) :
    energyNorm period P (by omega : P+6 ≤ (P+6)+1) (B.radius t) (B.metric.operatorPath period t)
      (solution period hT A B (P+6) (by omega) t) ≤ B.delta/2 :=
  solution_energy period hT A B (P+6) (by omega) P (by omega) (by omega) t

/-- The common L² path satisfies the actual nonlinear inviscid correction equation. -/
theorem commonPath_hasDerivAt {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (EulerVolterraConvolution.extendPath T hT.le (commonPath period hT A B))
      (value period (((A.atOrder period 6).coefficients period le_rfl).apply
        ⟨t,ht.1.le,ht.2.le⟩ (solution period hT A B 6 le_rfl ⟨t,ht.1.le,ht.2.le⟩))) t :=
  solution_hasDerivAt period hT A B 6 le_rfl t ht

/-- Actual coherent all-order data and their concrete budgets construct a common inviscid correction
with genuine jets at every order and spatially smooth, pointwise divergence-free representatives.
No correction solution, energy estimate, convergence, or all-order compatibility is assumed. -/
theorem exists_smooth_lifted_correction {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period
    hT A) :
    ∃ (U : C(Icc (0 : ℝ) T,LiftL2 period)) (g : Icc (0 : ℝ) T → LiftDomain period → Vector3),
      U ⟨0,le_rfl,hT.le⟩=0 ∧
      (∀ n t, Nonempty (SpatialJet period standardDirection n (U t))) ∧
      (∀ q hq t, value period (solution period hT A B q hq t)=U t) ∧
      (∀ t x, ContDiff ℝ ∞ (localFieldLift period (g t) x)) ∧
      (∀ t, (U t : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g t) ∧
      (∀ t x, (∑ i : Fin 3, (fieldDerivative period (coordinateDirection A.κ A.direction i) (g t)
          x) i)=0) ∧
      ∀ t (ht : t ∈ Ioo 0 T), HasDerivAt (extendPath T hT.le U)
        (value period (((A.atOrder period 6).coefficients period le_rfl).apply
          ⟨t,ht.1.le,ht.2.le⟩ (solution period hT A B 6 le_rfl ⟨t,ht.1.le,ht.2.le⟩))) t := by
  have hs (t : Icc (0 : ℝ) T) := exists_smooth_representative period (commonPath period hT A B t)
    (fun n => commonJet period hT A B n t)
  choose g hg ha using hs
  refine ⟨commonPath period hT A B,g,commonPath_initial period hT A B,
    (fun n t => ⟨commonJet period hT A B n t⟩),solution_value_common period hT A B,hg,ha,?_,
    commonPath_hasDerivAt period hT A B⟩
  intro t
  exact divergenceFree_classical_divergence_zero period A.κ A.direction (commonPath period hT A B t)
    (commonPath_divergence period hT A B t) (g t) (ha t) (hg t)

end EulerAllOrderLiftedCorrection

end
end

end

@[expose] public section

noncomputable section

namespace EulerAllOrderSmoothPressure

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerAllOrderCorrectionData
  EulerAllOrderCorrectionBudget EulerAllOrderCorrectionFamily EulerAllOrderLiftedCorrection
  EulerAllOrderPressureCoherence EulerVolterraConvolution EulerMetricTransport
  EulerSmoothPressureRepresentative EulerGraphPressurePotential
open scoped Topology ContDiff

variable (period : ℝ) [Fact (0 < period)]

/-- Every strong derivative order of the common actual signed pressure is supplied by a constructed
finite Sobolev realization. -/
def pressureJet {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (n : ℕ) (t : Icc (0 : ℝ) T) : SpatialJet period standardDirection n (commonPressure period hT A
        B t) := by
  rw [← signedPressurePath_value_common period hT A B (n+6) (by omega) t]
  exact EulerH6Pressure.SpatialJet.restrict
    (toJet period (signedPressurePath period hT A B (n+6) (by omega) t)) n (by omega)

/-- The common nonlinear correction satisfies its actual signed-pressure equation in L². -/
theorem commonPath_pressure_equation {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT
    A)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT.le (commonPath period hT A B))
      (-value period (rawSourcePath period hT A B 6 le_rfl ⟨t,ht.1.le,ht.2.le⟩) -
        (A.metric.coefficient ⟨t,ht.1.le,ht.2.le⟩).operator
          (commonPressure period hT A B ⟨t,ht.1.le,ht.2.le⟩)) t := by
  have h := commonPath_hasDerivAt period hT A B t ht
  rw [(A.atOrder period 6).source_value period le_rfl] at h
  exact h

/-- The constructed signed pressure has a genuine smooth spatial representative at every time. -/
theorem exists_smooth_signed_pressure {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period
    hT A) :
    ∃ p : Icc (0 : ℝ) T → LiftDomain period → Vector3,
      (∀ t x, ContDiff ℝ ∞ (localFieldLift period (p t) x)) ∧
      ∀ t, (commonPressure period hT A B t : LiftDomain period → Vector3) =ᵐ[liftMeasure period] p
          t := by
  have h (t : Icc (0 : ℝ) T) := exists_smooth_representative period (commonPressure period hT A B t)
    (fun n => pressureJet period hT A B n t)
  choose p hp ha using h
  exact ⟨p,hp,ha⟩

/-- The actual signed correction pressure yields a smooth scalar potential on every
reciprocal-frequency graph.
The common pressure, all its strong jets, its smooth representative and its closed-gradient property
are constructed internally. -/
theorem exists_smooth_pressure_graph {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT
    A)
    (k : ℝ) (hk : k * A.κ = 1) :
    ∃ (p : Icc (0 : ℝ) T → LiftDomain period → Vector3) (Q : Icc (0 : ℝ) T → Vector3 → ℝ),
      (∀ t x, ContDiff ℝ ∞ (localFieldLift period (p t) x)) ∧
      (∀ t, (commonPressure period hT A B t : LiftDomain period → Vector3) =ᵐ[liftMeasure period] p
          t) ∧
      (∀ t, ContDiff ℝ ∞ (Q t)) ∧
      ∀ t x, gradient (Q t) x=A.κ • p t (cylinderGraph period k A.direction x) := by
  obtain ⟨p,hp,ha⟩ := exists_smooth_signed_pressure period hT A B
  have hQ (t : Icc (0 : ℝ) T) := gradientSpace_has_graph_potential period A.κ k hk A.direction
    (commonPressure period hT A B t) (commonPressure_gradient period hT A B t) (p t) (ha t) (hp t)
  choose Q hQs hQ using hQ
  exact ⟨p,Q,hp,ha,hQs,hQ⟩

end EulerAllOrderSmoothPressure

end
end

end

@[expose] public section

noncomputable section

namespace EulerCommonPressureRepresentative

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerAllOrderCorrectionData EulerAllOrderCorrectionBudget EulerAllOrderPressureCoherence
  EulerAllOrderSmoothPressure EulerSobolevPointEvaluation EulerSobolevJointEvaluation
  EulerSmoothPressureRepresentative EulerMetricTransport EulerGraphPressurePotential
open scoped ContDiff

variable (period : ℝ) [Fact (0 < period)]

/-- The canonical pointwise pressure, obtained by bounded evaluation of its actual continuous H3
realization. -/
def pointPressure {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) : Vector3 :=
  pointEvaluation period x (restrictOperator period (by omega : 3 ≤ 6)
    (signedPressurePath period hT A B 6 le_rfl t))

/-- The canonical pointwise pressure represents the constructed common L² pressure. -/
theorem pointPressure_ae {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (t : Icc (0 : ℝ) T) :
    (commonPressure period hT A B t : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      pointPressure period hT A B t :=
  representative_ae period (restrictOperator period (by omega : 3 ≤ 6)
    (signedPressurePath period hT A B 6 le_rfl t))

/-- The canonical pressure is jointly continuous in time and the actual cylinder point. -/
theorem pointPressure_joint_continuous {T : ℝ} (hT : 0 < T) (A : Data period T)
    (B : Budget period hT A) :
    Continuous (fun p : Icc (0 : ℝ) T × LiftDomain period => pointPressure period hT A B p.1 p.2) :=
  path_representative_joint_continuous period
    ((restrictOperator period (by omega : 3 ≤ 6)).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      (signedPressurePath period hT A B 6 le_rfl))

/-- The canonical pressure is continuous on each spatial slice. -/
theorem pointPressure_continuous {T : ℝ} (hT : 0 < T) (A : Data period T)
    (B : Budget period hT A) (t : Icc (0 : ℝ) T) :
    Continuous (pointPressure period hT A B t) :=
  representative_continuous period (restrictOperator period (by omega : 3 ≤ 6)
    (signedPressurePath period hT A B 6 le_rfl t))

/-- These same canonical representatives are smooth in every spatial coordinate. -/
theorem pointPressure_smooth {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (pointPressure period hT A B t) x) := by
  obtain ⟨g, hg, ha⟩ := exists_smooth_representative period (commonPressure period hT A B t)
    (fun n => pressureJet period hT A B n t)
  have he : pointPressure period hT A B t = g :=
    representative_eq period _ g (smoothField_continuous period g hg) ha
  rw [he]
  exact hg x

omit [Fact (0 < period)] in
/-- The physical phase graph is a continuous map into the periodic cylinder. -/
theorem cylinderGraph_continuous (k : ℝ) (m : Vector3) :
    Continuous (cylinderGraph period k m) := by
  unfold cylinderGraph
  exact continuous_id.prodMk ((AddCircle.continuous_mk' period).comp
    (continuous_const.mul (continuous_const.inner continuous_id)))

/-- The genuine signed graph pressure-gradient vector field. -/
def graphPressure {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (k : ℝ) (t : Icc (0 : ℝ) T) (x : Vector3) : Vector3 :=
  A.κ • pointPressure period hT A B t (cylinderGraph period k A.direction x)

/-- The actual graph pressure-gradient field is jointly continuous in time and space. -/
theorem graphPressure_joint_continuous {T : ℝ} (hT : 0 < T) (A : Data period T)
    (B : Budget period hT A) (k : ℝ) :
    Continuous (graphPressure period hT A B k).uncurry :=
  ((pointPressure_joint_continuous period hT A B).comp
    (continuous_fst.prodMk ((cylinderGraph_continuous period k A.direction).comp
        continuous_snd))).const_smul A.κ

/-- Each actual canonical graph field has a genuine smooth potential by the proved lifted
gradient-space reconstruction. -/
theorem graphPressure_has_potential {T : ℝ} (hT : 0 < T) (A : Data period T)
    (B : Budget period hT A) (k : ℝ) (hk : k * A.κ = 1) (t : Icc (0 : ℝ) T) :
    ∃ q : Vector3 → ℝ, ContDiff ℝ ∞ q ∧
      ∀ x, gradient q x = graphPressure period hT A B k t x :=
  gradientSpace_has_graph_potential period A.κ k hk A.direction
    (commonPressure period hT A B t) (commonPressure_gradient period hT A B t)
    (pointPressure period hT A B t) (pointPressure_ae period hT A B t)
    (pointPressure_smooth period hT A B t)

end EulerCommonPressureRepresentative

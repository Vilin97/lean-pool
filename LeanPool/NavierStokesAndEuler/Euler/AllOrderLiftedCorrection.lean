/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderCorrectionFamily
import LeanPool.NavierStokesAndEuler.Euler.ClassicalDivergence
import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothPressureRepresentative

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

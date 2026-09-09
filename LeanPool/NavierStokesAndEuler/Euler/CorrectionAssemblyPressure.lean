/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblyCommon
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionSourceRestriction

@[expose] public section

/-! Coherence and all-order regularity of the actual pressure associated with a finite correction
  family. -/

noncomputable section

namespace EulerCorrectionAssembly

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerCorrectionLowerData
  EulerCorrectionSourceRestriction EulerAllOrderCorrectionData EulerSobolevCoefficientPressure
  EulerVolterraConvolution

variable (period : ℝ) [Fact (0 < period)]
variable {T : ℝ} {hT : 0 < T} {A : Data period T}

/-- The actual continuous nonlinear raw source of each finite correction. -/
def FiniteFamily.rawSourcePath (F : FiniteFamily period hT A) (q : ℕ) (hq : 6 ≤ q) :
    C(Icc (0 : ℝ) T, SobolevSpace period q) :=
  rawPath period hq (A.atOrder period q) (F.solution q hq)

/-- The actual signed coercive pressure of each finite correction. -/
def FiniteFamily.signedPressurePath (F : FiniteFamily period hT A) (q : ℕ) (hq : 6 ≤ q) :
    C(Icc (0 : ℝ) T, SobolevSpace period q) :=
  pressurePath period hq (A.atOrder period q) (F.solution q hq)

/-- Proved correction compatibility gives exact restriction of the actual nonlinear sources. -/
theorem FiniteFamily.rawSourcePath_truncate (F : FiniteFamily period hT A) (C : ComparisonData
  period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    truncateOperator period q (F.rawSourcePath period (q+1) (hq.trans (Nat.le_succ q)) t) =
      F.rawSourcePath period q hq t := by
  have h := truncate_rawSource period hq (A.atOrder period (q+1))
    (A.metric.jet q) (A.linear.jet q) (fun i => (A.quadratic i).jet q)
    (A.metric.continuous q) (A.linear.continuous q) (fun i => (A.quadratic i).continuous q)
    t (F.solution (q+1) (hq.trans (Nat.le_succ q)) t)
  rw [A.lower_atOrder period q] at h
  have he := congrArg (fun f => f t) (F.compatible period C q hq)
  change truncateOperator period (q+1) (F.solution (q+1) (hq.trans (Nat.le_succ q)) t) =
    F.solution q hq t at he
  rw [he] at h
  exact h

/-- Adjacent nonlinear source realizations have the same actual L² value. -/
theorem FiniteFamily.rawSourcePath_value_succ (F : FiniteFamily period hT A) (C : ComparisonData
  period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    value period (F.rawSourcePath period (q+1) (hq.trans (Nat.le_succ q)) t) =
      value period (F.rawSourcePath period q hq t) :=
  congrArg (value period (q := q)) (F.rawSourcePath_truncate period C q hq t)

/-- The genuine signed coercive pressures agree at adjacent Sobolev orders. -/
theorem FiniteFamily.signedPressurePath_value_succ (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    value period (F.signedPressurePath period (q+1) (hq.trans (Nat.le_succ q)) t) =
      value period (F.signedPressurePath period q hq t) := by
  change -value period (pressureSobolevOperator period (A.metric.jet (q+1) t) A.κ A.direction
    A.coercivity A.coercivity_pos (A.metric_pos t)
    (F.rawSourcePath period (q+1) (hq.trans (Nat.le_succ q)) t)) =
      -value period (pressureSobolevOperator period (A.metric.jet q t) A.κ A.direction
        A.coercivity A.coercivity_pos (A.metric_pos t) (F.rawSourcePath period q hq t))
  rw [pressureSobolevOperator_value, pressureSobolevOperator_value, F.rawSourcePath_value_succ
    period C]

/-- Every finite signed pressure is a realization of the same actual base pressure. -/
theorem FiniteFamily.signedPressurePath_value_base (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    value period (F.signedPressurePath period q hq t) =
      value period (F.signedPressurePath period 6 le_rfl t) := by
  exact Nat.le_induction (P := fun n hn => value period (F.signedPressurePath period n hn t) =
      value period (F.signedPressurePath period 6 le_rfl t)) rfl
    (fun n hn ih => (F.signedPressurePath_value_succ period C n hn t).trans ih) q hq

/-- The actual common signed correction pressure is a continuous L² path. -/
def FiniteFamily.commonPressure (F : FiniteFamily period hT A) : C(Icc (0 : ℝ) T, LiftL2 period) :=
  (valueOperator period 6).compLeftContinuous ℝ (Icc (0 : ℝ) T) (F.signedPressurePath period 6
    le_rfl)

/-- Each finite pressure realizes the common actual signed pressure field. -/
theorem FiniteFamily.signedPressurePath_value_common (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    value period (F.signedPressurePath period q hq t) = F.commonPressure period t :=
  F.signedPressurePath_value_base period C q hq t

/-- The actual common pressure lies in the closed lifted gradient space. -/
theorem FiniteFamily.commonPressure_gradient (F : FiniteFamily period hT A) (t : Icc (0 : ℝ) T) :
    F.commonPressure period t ∈ gradientSpace period A.κ A.direction :=
  (A.atOrder period 6).pressure_mem_gradient period le_rfl t (F.solution 6 le_rfl t)

/-- The actual common pressure has genuine strong spatial jets of every order. -/
def FiniteFamily.pressureJet (F : FiniteFamily period hT A) (C : ComparisonData period hT A)
    (n : ℕ) (t : Icc (0 : ℝ) T) : SpatialJet period standardDirection n (F.commonPressure period t)
      := by
  rw [← F.signedPressurePath_value_common period C (n+6) (by omega) t]
  exact EulerH6Pressure.SpatialJet.restrict
    (toJet period (F.signedPressurePath period (n+6) (by omega) t)) n (by omega)

/-- The common correction satisfies the literal equation with its reconstructed actual signed pressure. -/
theorem FiniteFamily.commonPath_pressure_equation (F : FiniteFamily period hT A)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT.le (F.commonPath period))
      (-value period (F.rawSourcePath period 6 le_rfl ⟨t, ht.1.le, ht.2.le⟩) -
        (A.metric.coefficient ⟨t, ht.1.le, ht.2.le⟩).operator
          (F.commonPressure period ⟨t, ht.1.le, ht.2.le⟩)) t := by
  have h := F.commonPath_hasDerivAt period t ht
  rw [(A.atOrder period 6).source_value period le_rfl] at h
  exact h

end EulerCorrectionAssembly

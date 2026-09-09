/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblyPressure
public import LeanPool.NavierStokesAndEuler.Euler.CanonicalGraphPotential
public import LeanPool.NavierStokesAndEuler.Euler.CommonPressureRepresentative

@[expose] public section

/-! Canonical smooth pressure reconstruction for the generic finite-solution assembly. -/

noncomputable section

namespace EulerCorrectionAssembly

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerAllOrderCorrectionData
  EulerMetricTransport EulerSmoothPressureRepresentative EulerSobolevPointEvaluation
  EulerSobolevJointEvaluation EulerGraphPressurePotential EulerCanonicalGraphPotential

open scoped ContDiff

variable (period : ℝ) [Fact (0 < period)]
variable {T : ℝ} {hT : 0 < T} {A : Data period T}

/-- Bounded evaluation of the actual finite pressure fixes a canonical common pressure representative. -/
def FiniteFamily.pointPressure (F : FiniteFamily period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) : Vector3 :=
  pointEvaluation period x (restrictOperator period (by omega : 3 ≤ 6)
    (F.signedPressurePath period 6 le_rfl t))

/-- The canonical pressure represents the actual common signed L² pressure. -/
theorem FiniteFamily.pointPressure_ae (F : FiniteFamily period hT A) (t : Icc (0 : ℝ) T) :
    (F.commonPressure period t : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      F.pointPressure period t :=
  representative_ae period (restrictOperator period (by omega : 3 ≤ 6)
    (F.signedPressurePath period 6 le_rfl t))

/-- The canonical pressure is jointly continuous in time and the cylinder point. -/
theorem FiniteFamily.pointPressure_joint_continuous (F : FiniteFamily period hT A) :
    Continuous (F.pointPressure period).uncurry :=
  path_representative_joint_continuous period
    ((restrictOperator period (by omega : 3 ≤ 6)).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      (F.signedPressurePath period 6 le_rfl))

/-- Proved pressure coherence supplies spatial smoothness of the canonical pressure representative. -/
theorem FiniteFamily.pointPressure_smooth (F : FiniteFamily period hT A) (C : ComparisonData period
  hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (F.pointPressure period t) x) := by
  obtain ⟨g, hg, ha⟩ := exists_smooth_representative period (F.commonPressure period t)
    (fun n => F.pressureJet period C n t)
  have he : F.pointPressure period t = g :=
    representative_eq period _ g (smoothField_continuous period g hg) ha
  rw [he]
  exact hg x

/-- The genuine signed pressure-gradient vector field on the oscillatory physical graph. -/
def FiniteFamily.graphPressure (F : FiniteFamily period hT A) (k : ℝ)
    (t : Icc (0 : ℝ) T) (x : Vector3) : Vector3 :=
  A.κ • F.pointPressure period t (cylinderGraph period k A.direction x)

/-- The actual graph pressure-gradient field is jointly continuous. -/
theorem FiniteFamily.graphPressure_joint_continuous (F : FiniteFamily period hT A) (k : ℝ) :
    Continuous (F.graphPressure period k).uncurry :=
  ((F.pointPressure_joint_continuous period).comp
    (continuous_fst.prodMk
      ((EulerCommonPressureRepresentative.cylinderGraph_continuous period k A.direction).comp
        continuous_snd))).const_smul A.κ

/-- The actual common pressure has a genuine smooth scalar potential on each reciprocal-frequency graph. -/
theorem FiniteFamily.graphPressure_has_potential (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (k : ℝ) (hk : k * A.κ = 1) (t : Icc (0 : ℝ) T) :
    ∃ q : Vector3 → ℝ, ContDiff ℝ ∞ q ∧
      ∀ x, gradient q x = F.graphPressure period k t x :=
  gradientSpace_has_graph_potential period A.κ k hk A.direction
    (F.commonPressure period t) (F.commonPressure_gradient period t)
    (F.pointPressure period t) (F.pointPressure_ae period t) (F.pointPressure_smooth period C t)

/-- The actual graph pressure reconstructed by a canonical radial integral based at the origin. -/
def FiniteFamily.normalizedGraphPotential (F : FiniteFamily period hT A) (k : ℝ)
    (t : Icc (0 : ℝ) T) (x : Vector3) : ℝ :=
  radialPotential (F.graphPressure period k t) x

/-- The reconstructed scalar pressure has zero value at the origin at every time. -/
theorem FiniteFamily.normalizedGraphPotential_zero (F : FiniteFamily period hT A) (k : ℝ)
    (t : Icc (0 : ℝ) T) : F.normalizedGraphPotential period k t 0 = 0 :=
  radialPotential_zero _

/-- The normalized scalar pressure is jointly continuous, including both endpoint time slices. -/
theorem FiniteFamily.normalizedGraphPotential_joint_continuous (F : FiniteFamily period hT A) (k :
  ℝ) :
    Continuous (F.normalizedGraphPotential period k).uncurry :=
  radialPotential_joint_continuous _ (F.graphPressure_joint_continuous period k)

/-- The normalized scalar pressure is spatially smooth at every time. -/
theorem FiniteFamily.normalizedGraphPotential_smooth (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (k : ℝ) (hk : k * A.κ = 1) (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (F.normalizedGraphPotential period k t) := by
  obtain ⟨q, hq, hg⟩ := F.graphPressure_has_potential period C k hk t
  exact radialPotential_smooth _
    (Continuous.uncurry_left t (F.graphPressure_joint_continuous period k)) q hq hg

/-- The canonical scalar pressure has the actual signed graph pressure as its gradient. -/
theorem FiniteFamily.normalizedGraphPotential_gradient (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (k : ℝ) (hk : k * A.κ = 1)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    gradient (F.normalizedGraphPotential period k t) x =
      A.κ • F.pointPressure period t (cylinderGraph period k A.direction x) := by
  obtain ⟨q, hq, hg⟩ := F.graphPressure_has_potential period C k hk t
  exact radialPotential_gradient _
    (Continuous.uncurry_left t (F.graphPressure_joint_continuous period k)) q hq hg x

end EulerCorrectionAssembly

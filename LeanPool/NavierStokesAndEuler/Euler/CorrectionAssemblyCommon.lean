/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblyCompatibility
public import LeanPool.NavierStokesAndEuler.Euler.ClassicalDivergence
public import LeanPool.NavierStokesAndEuler.Euler.SobolevJointEvaluation

@[expose] public section

/-! A common actual smooth lifted correction assembled from finite solves and proved uniqueness. -/

noncomputable section

namespace EulerCorrectionAssembly

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerAllOrderCorrectionData
  EulerVolterraConvolution EulerMetricTransport EulerTransportDerivatives
  EulerSmoothPressureRepresentative EulerClassicalDivergence EulerSobolevPointEvaluation
  EulerSobolevJointEvaluation
open scoped ContDiff

variable (period : ℝ) [Fact (0 < period)]
variable {T : ℝ} {hT : 0 < T} {A : Data period T}

/-- The actual common continuous L² path, defined from the base finite correction. -/
def FiniteFamily.commonPath (F : FiniteFamily period hT A) : C(Icc (0 : ℝ) T, LiftL2 period) :=
  (valueOperator period 7).compLeftContinuous ℝ (Icc (0 : ℝ) T) (F.solution 6 le_rfl)

/-- Every supplied finite correction realizes the common actual L² path. -/
theorem FiniteFamily.value_common (F : FiniteFamily period hT A) (C : ComparisonData period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    value period (F.solution q hq t) = F.commonPath period t :=
  F.value_base period C q hq t

/-- The common correction has zero initial trace. -/
theorem FiniteFamily.commonPath_initial (F : FiniteFamily period hT A) :
    F.commonPath period ⟨0, le_rfl, hT.le⟩ = 0 := by
  change value period (F.solution 6 le_rfl ⟨0, le_rfl, hT.le⟩) = 0
  rw [F.initial]
  rfl

/-- The common correction satisfies the actual closed lifted divergence constraint. -/
theorem FiniteFamily.commonPath_divergence (F : FiniteFamily period hT A) (t : Icc (0 : ℝ) T) :
    F.commonPath period t ∈ divergenceFreeSpace period A.κ A.direction :=
  F.divergence 6 le_rfl t

/-- The common correction has an actual strong spatial jet at every derivative order. -/
def FiniteFamily.commonJet (F : FiniteFamily period hT A) (C : ComparisonData period hT A)
    (n : ℕ) (t : Icc (0 : ℝ) T) : SpatialJet period standardDirection n (F.commonPath period t) :=
      by
  rw [← F.value_common period C (n+6) (by omega) t]
  exact EulerH6Pressure.SpatialJet.restrict
    (toJet period (F.solution (n+6) (by omega) t)) n (by omega)

/-- The common L² path satisfies the actual nonlinear inviscid equation. -/
theorem FiniteFamily.commonPath_hasDerivAt (F : FiniteFamily period hT A)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT.le (F.commonPath period))
      (value period (((A.atOrder period 6).coefficients period le_rfl).apply
        ⟨t, ht.1.le, ht.2.le⟩ (F.solution 6 le_rfl ⟨t, ht.1.le, ht.2.le⟩))) t :=
  F.equation 6 le_rfl t ht

/-- Every other genuine finite-order correction realizes this same common field.
Consequently bounds proved for any particular finite solver may be transferred to the assembled
  solution. -/
theorem FiniteFamily.realizes_common (F : FiniteFamily period hT A) (C : ComparisonData period hT A)
    (q : ℕ) (hq : 6 ≤ q) (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)))
    (hi : u ⟨0, le_rfl, hT.le⟩ = 0)
    (hd : ∀ t, value period (u t) ∈ divergenceFreeSpace period A.κ A.direction)
    (hu : ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (fun r => value period (extendPath T hT.le u r))
        (value period (((A.atOrder period q).coefficients period hq).apply
          ⟨t, ht.1.le, ht.2.le⟩ (u ⟨t, ht.1.le, ht.2.le⟩))) t)
    (t : Icc (0 : ℝ) T) : value period (u t) = F.commonPath period t := by
  rw [F.unique_at_order period C q hq u hi hd hu]
  exact F.value_common period C q hq t

/-- Bounded H3 evaluation fixes a canonical actual pointwise representative of the common correction. -/
def FiniteFamily.pointField (F : FiniteFamily period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) : Vector3 :=
  pointEvaluation period x (restrictOperator period (by omega : 3 ≤ 7) (F.solution 6 le_rfl t))

/-- The canonical common field is an actual representative of its L² path. -/
theorem FiniteFamily.pointField_ae (F : FiniteFamily period hT A) (t : Icc (0 : ℝ) T) :
    (F.commonPath period t : LiftDomain period → Vector3) =ᵐ[liftMeasure period] F.pointField
      period t :=
  representative_ae period (restrictOperator period (by omega : 3 ≤ 7) (F.solution 6 le_rfl t))

/-- The canonical common field is jointly continuous in time and the cylinder point. -/
theorem FiniteFamily.pointField_joint_continuous (F : FiniteFamily period hT A) :
    Continuous (F.pointField period).uncurry :=
  path_representative_joint_continuous period
    ((restrictOperator period (by omega : 3 ≤ 7)).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      (F.solution 6 le_rfl))

/-- Proved compatibility and all finite genuine jets make the canonical common field spatially smooth. -/
theorem FiniteFamily.pointField_smooth (F : FiniteFamily period hT A) (C : ComparisonData period hT
  A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (F.pointField period t) x) := by
  obtain ⟨g, hg, ha⟩ := exists_smooth_representative period (F.commonPath period t)
    (fun n => F.commonJet period C n t)
  have he : F.pointField period t = g :=
    representative_eq period _ g (smoothField_continuous period g hg) ha
  rw [he]
  exact hg x

/-- The canonical smooth field has pointwise zero lifted divergence. -/
theorem FiniteFamily.pointField_divergence (F : FiniteFamily period hT A) (C : ComparisonData
  period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    (∑ i : Fin 3, (fieldDerivative period (coordinateDirection A.κ A.direction i)
      (F.pointField period t) x) i) = 0 :=
  divergenceFree_classical_divergence_zero period A.κ A.direction (F.commonPath period t)
    (F.commonPath_divergence period t) (F.pointField period t) (F.pointField_ae period t)
    (F.pointField_smooth period C t) x

end EulerCorrectionAssembly

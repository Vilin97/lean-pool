/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothCylinderFlow
public import LeanPool.NavierStokesAndEuler.Euler.CylinderDescentJets
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowJets

@[expose] public section

/-! Actual periodic displacement jets and their differentiated integral
equation. The real covering displacement is periodic, so its descent is
a vector-valued field, including its angular displacement component. -/

noncomputable section

namespace EulerSmoothCylinderFlow

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderCoverDescent
  EulerSmoothBanachFlow EulerFinitePathTensor EulerVolterraConvolution
open scoped ContDiff Interval

private local instance (n : ℕ) : MeasurableSpace (LiftTangent [×n]→L[ℝ] LiftTangent) := borel _
private local instance (n : ℕ) : BorelSpace (LiftTangent [×n]→L[ℝ] LiftTangent) := ⟨rfl⟩

variable (P T : ℝ) [Fact (0 < P)] (hT : 0 ≤ T)
  (A : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent)
  (hA : ∀ (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) z,
    A.field t (z.1,(c : ℝ)+z.2)=A.field t z)

def velocityCover (t : ℝ) : LiftTangent → LiftTangent := A.field (projIcc 0 T hT t)

def forwardCover (t : ℝ) : LiftTangent → LiftTangent :=
  (flowData T hT A).forward (projIcc 0 T hT t)

include hA in
omit [Fact (0 < P)] in
theorem forwardCover_deck (t : ℝ) (c : AddSubgroup.zmultiples P) (z : LiftTangent) :
    forwardCover T hT A t (z.1,(c : ℝ)+z.2) =
      ((forwardCover T hT A t z).1,(c : ℝ)+(forwardCover T hT A t z).2) :=
  EulerCylinderPeriodicFlow.flow_deck P (flowData T hT A) (velocity_deck P T hT A hA)
    0 (projIcc 0 T hT t) c z

include hA in
omit [Fact (0 < P)] in
theorem coverDisplacement_deck (t : ℝ) (c : AddSubgroup.zmultiples P) (z : LiftTangent) :
    EulerSmoothBanachFlow.displacement T hT A t (z.1,(c : ℝ)+z.2) =
      EulerSmoothBanachFlow.displacement T hT A t z := by
  change forwardCover T hT A t (z.1,(c : ℝ)+z.2)-(z.1,(c : ℝ)+z.2) =
    forwardCover T hT A t z-z
  rw [forwardCover_deck P T hT A hA]
  apply Prod.ext <;> simp

def displacement (t : ℝ) : LiftDomain P → LiftTangent :=
  descend P (EulerSmoothBanachFlow.displacement T hT A t)

def displacementJet (t : ℝ) (q : LiftDomain P) (n : ℕ) : LiftTangent [×n]→L[ℝ] LiftTangent :=
  jetSeries P (EulerSmoothBanachFlow.displacement T hT A t) q n

def compositionJet (t : ℝ) (q : LiftDomain P) (n : ℕ) : LiftTangent [×n]→L[ℝ] LiftTangent :=
  (jetSeries P (velocityCover T hT A t) (forward P T hT A (projIcc 0 T hT t) q)).taylorComp
    (jetSeries P (forwardCover T hT A t) q) n

include hA in
theorem displacement_cover (t : ℝ) (z : LiftTangent) :
    displacement P T hT A t (coveringMap P z)=EulerSmoothBanachFlow.displacement T hT A t z :=
  descend_cover P _ (fiber_constant_of_deck P _ (coverDisplacement_deck P T hT A hA t)) z

include hA in
theorem displacement_smooth (t : ℝ) (q : LiftDomain P) :
    ContDiff ℝ ∞ (EulerMetricTransport.localFieldLift P (displacement P T hT A t) q) :=
  descend_smooth P _ (coverDisplacement_deck P T hT A hA t)
    (EulerSmoothBanachFlow.displacement_contDiff T hT A t) q

include hA in
theorem displacementJet_local (t : ℝ) (q : LiftDomain P) (n : ℕ) :
    displacementJet P T hT A t q n =
      iteratedFDeriv ℝ n (EulerMetricTransport.localFieldLift P (displacement P T hT A t) q) 0 :=
  jetSeries_eq_local P _ (coverDisplacement_deck P T hT A hA t) q n

include hA in
theorem compositionJet_eq (t : ℝ) (q : LiftDomain P) (n : ℕ) :
    compositionJet P T hT A t q n =
      iteratedFDeriv ℝ n (velocityCover T hT A t ∘ forwardCover T hT A t) (sectionPoint P q) := by
  exact (jetSeries_comp P (velocityCover T hT A t)
    (fun c z => hA c (projIcc 0 T hT t) z) (forwardCover T hT A t)
    (A.smooth _) (forward_contDiff T hT A _) q n).symm

include hA in
theorem compositionJet_path (t : ℝ) (q : LiftDomain P) (n : ℕ) :
    compositionJet P T hT A t q n =
      extendPath T hT (velocityJetPath T hT A n (sectionPoint P q)) t := by
  rw [compositionJet_eq P T hT A hA]
  exact (velocityJetPath_apply T hT A n (sectionPoint P q) (projIcc 0 T hT t)).symm

theorem displacementJet_path (t : ℝ) (q : LiftDomain P) (n : ℕ) :
    displacementJet P T hT A t q n =
      extendPath T hT (displacementJetPath T hT A n (sectionPoint P q)) t :=
  (displacementJetPath_apply T hT A n (sectionPoint P q) t).symm

include hA in
theorem displacementJet_integral (t : Icc (0 : ℝ) T) (q : LiftDomain P) (n : ℕ) :
    displacementJet P T hT A t q n = ∫ s in (0 : ℝ)..(t : ℝ), compositionJet P T hT A s q n := by
  rw [displacementJet_path,displacementJetPath_integral]
  simp only [extendPath,projIcc_of_mem hT t.property,EulerContinuousTimeIntegral.integral_apply,
    EulerContinuousTimeIntegral.realIntegral]
  apply intervalIntegral.integral_congr
  intro s _
  exact (compositionJet_path P T hT A hA s q n).symm

omit [Fact (0 < P)] in
theorem velocityJetPath_label_continuous (n : ℕ) :
    Continuous (velocityJetPath T hT A n) :=
  (tensorPathMap n).continuous.comp
    (ContDiff.continuous_iteratedFDeriv (by simp) (velocityFamily_contDiff T hT A))

omit [Fact (0 < P)] in
theorem displacementJetPath_label_continuous (n : ℕ) :
    Continuous (displacementJetPath T hT A n) :=
  (tensorPathMap n).continuous.comp
    (ContDiff.continuous_iteratedFDeriv (by simp) (displacementFamily_contDiff T hT A))

include hA in
theorem compositionJet_joint_measurable (n : ℕ) :
    Measurable (fun z : ℝ × LiftDomain P => compositionJet P T hT A z.1 z.2 n) := by
  have hc : Continuous (fun z : ℝ × LiftTangent =>
      extendPath T hT (velocityJetPath T hT A n z.2) z.1) :=
    ((velocityJetPath_label_continuous T hT A n).comp continuous_snd).eval
      (continuous_projIcc.comp continuous_fst)
  have hm := hc.measurable.comp (measurable_fst.prodMk
    ((sectionPoint_measurable P).comp measurable_snd))
  simpa only [compositionJet_path P T hT A hA,Function.comp_def] using hm

theorem displacementJet_joint_measurable (n : ℕ) :
    Measurable (fun z : ℝ × LiftDomain P => displacementJet P T hT A z.1 z.2 n) := by
  have hc : Continuous (fun z : ℝ × LiftTangent =>
      extendPath T hT (displacementJetPath T hT A n z.2) z.1) :=
    ((displacementJetPath_label_continuous T hT A n).comp continuous_snd).eval
      (continuous_projIcc.comp continuous_fst)
  have hm := hc.measurable.comp (measurable_fst.prodMk
    ((sectionPoint_measurable P).comp measurable_snd))
  simpa only [displacementJet_path,Function.comp_def] using hm

end EulerSmoothCylinderFlow

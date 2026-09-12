/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderCoverDescent
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.MetricTransport
public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Descended cover tensors are the actual local spatial derivatives on
the cylinder. Their composition is the literal finite Taylor composition
used by the cylinder L² estimate. -/

@[expose] public section


noncomputable section

namespace EulerCylinderCoverDescent

open Set Function EulerLiftedGradientSpace EulerMetricTransport
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  (f : LiftTangent → W)
  (hperiod : ∀ (c : AddSubgroup.zmultiples P) z, f (z.1, (c : ℝ) + z.2) = f z)

include hperiod in
omit [Fact (0 < P)] in
theorem iteratedFDeriv_deck (n : ℕ) (c : AddSubgroup.zmultiples P) (z : LiftTangent) :
    iteratedFDeriv ℝ n f (z.1,(c : ℝ)+z.2)=iteratedFDeriv ℝ n f z := by
  let a : LiftTangent := (0,(c : ℝ))
  have shift (w : LiftTangent) : w+a=(w.1,(c : ℝ)+w.2) := by
    apply Prod.ext <;> simp [a,add_comm]
  have he : (fun w => f (w+a))=f := by
    funext w
    rw [shift,hperiod]
  rw [← shift,← iteratedFDeriv_comp_add_right n a z,he]

/-- Jet series, defined pointwise by `descend P (iteratedFDeriv ℝ n f) q`. -/
def jetSeries (q : LiftDomain P) : FormalMultilinearSeries ℝ LiftTangent W :=
  fun n => descend P (iteratedFDeriv ℝ n f) q

include hperiod in
theorem jetSeries_cover (n : ℕ) (z : LiftTangent) :
    jetSeries P f (coveringMap P z) n=iteratedFDeriv ℝ n f z :=
  descend_cover P _ (fiber_constant_of_deck P _ (iteratedFDeriv_deck P f hperiod n)) z

include hperiod in
omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
theorem localFieldLift_descend_cover (z : LiftTangent) :
    localFieldLift P (descend P f) (coveringMap P z)=fun h => f (z+h) := by
  have h0 : localFieldLift P (descend P f) 0=f := by
    funext h
    change descend P f ((0 : Vector3)+h.1,(0 : AddCircle P)+(h.2 : AddCircle P))=f h
    rw [zero_add,zero_add]
    exact descend_cover P f (fiber_constant_of_deck P f hperiod) h
  rw [localFieldLift_cover,h0]

include hperiod in
theorem descend_smooth (hf : ContDiff ℝ ∞ f) (q : LiftDomain P) :
    ContDiff ℝ ∞ (localFieldLift P (descend P f) q) := by
  obtain ⟨z,rfl⟩ := (coveringMap_isOpenQuotient P).surjective q
  rw [localFieldLift_descend_cover P f hperiod]
  exact hf.comp (contDiff_const.add contDiff_id)

include hperiod in
theorem jetSeries_eq_local (q : LiftDomain P) (n : ℕ) :
    jetSeries P f q n=iteratedFDeriv ℝ n (localFieldLift P (descend P f) q) 0 := by
  obtain ⟨z,rfl⟩ := (coveringMap_isOpenQuotient P).surjective q
  rw [jetSeries_cover P f hperiod,localFieldLift_descend_cover P f hperiod,
    iteratedFDeriv_comp_add_left,add_zero]

theorem jetSeries_joint_continuous {K : Type*} [TopologicalSpace K]
    (F : K → LiftTangent → W)
    (hF : ∀ t (c : AddSubgroup.zmultiples P) z, F t (z.1, (c : ℝ) + z.2) = F t z)
    (n : ℕ)
    (hJ : Continuous (fun z : K × LiftTangent => iteratedFDeriv ℝ n (F z.1) z.2)) :
    Continuous (fun z : K × LiftDomain P => jetSeries P (F z.1) z.2 n) :=
  descend_joint_continuous P (fun t => iteratedFDeriv ℝ n (F t)) hJ
    (fun t => fiber_constant_of_deck P _ (iteratedFDeriv_deck P (F t) (hF t) n))

include hperiod in
omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
theorem descend_comp_map (Φ : LiftTangent → LiftTangent) :
    descend P (f ∘ Φ) = descend P f ∘ descendMap P Φ := by
  funext q
  exact (descend_cover P f (fiber_constant_of_deck P f hperiod)
    (Φ (sectionPoint P q))).symm

include hperiod in
theorem jetSeries_comp (Φ : LiftTangent → LiftTangent)
    (hf : ContDiff ℝ ∞ f) (hΦ : ContDiff ℝ ∞ Φ) (q : LiftDomain P) (n : ℕ) :
    jetSeries P (f ∘ Φ) q n =
      (jetSeries P f (descendMap P Φ q)).taylorComp (jetSeries P Φ q) n := by
  have he : jetSeries P f (descendMap P Φ q) = ftaylorSeries ℝ f (Φ (sectionPoint P q)) := by
    funext j
    exact jetSeries_cover P f hperiod j (Φ (sectionPoint P q))
  rw [he]
  exact iteratedFDeriv_comp hf.contDiffAt hΦ.contDiffAt (by simp : (n : ℕ∞ω) ≤ ∞)

include hperiod in
omit [Fact (0 < P)] [NormedAddCommGroup W] [NormedSpace ℝ W] in
theorem comp_deck (Φ : LiftTangent → LiftTangent)
    (hΦ : ∀ (c : AddSubgroup.zmultiples P) z,
      Φ (z.1, (c : ℝ) + z.2) = ((Φ z).1, (c : ℝ) + (Φ z).2))
    (c : AddSubgroup.zmultiples P) (z : LiftTangent) :
    (f ∘ Φ) (z.1,(c : ℝ)+z.2)=(f ∘ Φ) z := by
  simp only [Function.comp_def,hΦ,hperiod]

include hperiod in
theorem local_jet_comp (Φ : LiftTangent → LiftTangent)
    (hdeck : ∀ (c : AddSubgroup.zmultiples P) z,
      Φ (z.1, (c : ℝ) + z.2) = ((Φ z).1, (c : ℝ) + (Φ z).2))
    (hf : ContDiff ℝ ∞ f) (hΦ : ContDiff ℝ ∞ Φ) (q : LiftDomain P) (n : ℕ) :
    iteratedFDeriv ℝ n (localFieldLift P (descend P f ∘ descendMap P Φ) q) 0 =
      (jetSeries P f (descendMap P Φ q)).taylorComp (jetSeries P Φ q) n := by
  rw [← descend_comp_map P f hperiod Φ,
    ← jetSeries_eq_local P (f ∘ Φ) (comp_deck P f hperiod Φ hdeck) q n]
  exact jetSeries_comp P f hperiod Φ hf hΦ q n

end EulerCylinderCoverDescent

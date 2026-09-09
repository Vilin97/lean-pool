/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderDescentJets
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.TransportDerivatives
import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderGraphTrace
import LeanPool.NavierStokesAndEuler.Euler.LpParameterIntegral
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! A phase-independent L² trace estimate for actual descended tensors.
One extra angular derivative suffices, and its norm is controlled by
the next actual cover tensor. -/

@[expose] public section


noncomputable section

namespace EulerCylinderJetGraphTrace

open Set MeasureTheory Filter EulerLiftedGradientSpace EulerCylinderCoverDescent
  EulerMetricTransport EulerTransportDerivatives EulerCylinderGraphTrace
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  (f : LiftTangent → W)
  (hperiod : ∀ (c : AddSubgroup.zmultiples P) z, f (z.1, (c : ℝ) + z.2) = f z)

include hperiod in
theorem fieldDerivative_descend (a : LiftTangent) (q : LiftDomain P) :
    fieldDerivative P a (descend P f) q = fderiv ℝ f (sectionPoint P q) a := by
  have he := localFieldLift_descend_cover P f hperiod (sectionPoint P q)
  rw [coveringMap_sectionPoint] at he
  change fderiv ℝ (localFieldLift P (descend P f) q) 0 a = _
  rw [he,fderiv_comp_add_left,add_zero]

include hperiod in
theorem jetSeries_smooth (hf : ContDiff ℝ ∞ f) (n : ℕ) (q : LiftDomain P) :
    ContDiff ℝ ∞ (localFieldLift P (fun x => jetSeries P f x n) q) :=
  descend_smooth P (iteratedFDeriv ℝ n f) (iteratedFDeriv_deck P f hperiod n)
    (hf.iteratedFDeriv_right (m := ∞) (by simp)) q

include hperiod in
theorem angularJet_bound (n : ℕ) (q : LiftDomain P) :
    ‖fieldDerivative P (0,1) (fun x => jetSeries P f x n) q‖ ≤ ‖jetSeries P f q (n+1)‖ := by
  change ‖fieldDerivative P (0,1) (descend P (iteratedFDeriv ℝ n f)) q‖ ≤ _
  rw [fieldDerivative_descend P (iteratedFDeriv ℝ n f) (iteratedFDeriv_deck P f hperiod n)]
  change ‖fderiv ℝ (iteratedFDeriv ℝ n f) (sectionPoint P q) (0,1)‖ ≤
    ‖iteratedFDeriv ℝ (n+1) f (sectionPoint P q)‖
  have h := (fderiv ℝ (iteratedFDeriv ℝ n f) (sectionPoint P q)).le_opNorm (0,1)
  simpa only [norm_fderiv_iteratedFDeriv,Prod.norm_def,norm_zero,norm_one,
    max_eq_right (by norm_num : (0 : ℝ) ≤ 1),mul_one] using h

include hperiod in
theorem angularJet_memLp_and_bound (hf : ContDiff ℝ ∞ f) (n : ℕ)
    (hLp : MemLp (fun q => jetSeries P f q (n + 1)) 2 (liftMeasure P)) :
    MemLp (fieldDerivative P (0,1) (fun q => jetSeries P f q n)) 2 (liftMeasure P) ∧
      (eLpNorm (fieldDerivative P (0,1) (fun q => jetSeries P f q n)) 2 (liftMeasure P)).toReal ≤
        (eLpNorm (fun q => jetSeries P f q (n+1)) 2 (liftMeasure P)).toReal := by
  have hc := smoothField_continuous P _ (fieldDerivative_smooth P (0,1) _
    (jetSeries_smooth P f hperiod hf n))
  have hb : ∀ᵐ q ∂liftMeasure P,
      ‖fieldDerivative P (0,1) (fun x => jetSeries P f x n) q‖ ≤ ‖jetSeries P f q (n+1)‖ :=
    Eventually.of_forall (angularJet_bound P f hperiod n)
  exact ⟨hLp.of_le hc.aestronglyMeasurable hb,
    ENNReal.toReal_mono hLp.eLpNorm_ne_top (eLpNorm_mono_ae hb)⟩

variable [CompleteSpace W]

theorem graph_norm_bound (g : LiftDomain P → W)
    (hg : ∀ q, ContDiff ℝ ∞ (localFieldLift P g q))
    (hLp : MemLp g 2 (liftMeasure P))
    (hDLp : MemLp (fieldDerivative P (0, 1) g) 2 (liftMeasure P))
    (θ : Vector3 → AddCircle P) (hθ : Continuous θ) (C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hn : (eLpNorm g 2 (liftMeasure P)).toReal ≤ C)
    (hd : (eLpNorm (fieldDerivative P (0, 1) g) 2 (liftMeasure P)).toReal ≤ D) :
    MemLp (fun x => g (x,θ x)) 2 volume ∧
      (eLpNorm (fun x => g (x,θ x)) 2 volume).toReal ≤ Real.sqrt (2/P+2*P)*(C+D) := by
  obtain ⟨hgraph,he⟩ := graph_memLp_and_energy_bound P g hg hLp hDLp θ hθ
  refine ⟨hgraph,?_⟩
  rw [EulerLpParameterIntegral.integral_norm_sq_eq volume _ hgraph,
    EulerLpParameterIntegral.integral_norm_sq_eq (liftMeasure P) _ hLp,
    EulerLpParameterIntegral.integral_norm_sq_eq (liftMeasure P) _ hDLp] at he
  have hP : 0 < P := Fact.out
  have hn' : (eLpNorm g 2 (liftMeasure P)).toReal^2 ≤ (C+D)^2 :=
    pow_le_pow_left₀ ENNReal.toReal_nonneg (hn.trans (le_add_of_nonneg_right hD)) 2
  have hd' : (eLpNorm (fieldDerivative P (0,1) g) 2 (liftMeasure P)).toReal^2 ≤ (C+D)^2 :=
    pow_le_pow_left₀ ENNReal.toReal_nonneg (hd.trans (le_add_of_nonneg_left hC)) 2
  apply (sq_le_sq₀ ENNReal.toReal_nonneg (mul_nonneg (Real.sqrt_nonneg _) (add_nonneg hC hD))).mp
  calc
    _ ≤ (2/P)*(eLpNorm g 2 (liftMeasure P)).toReal^2 +
        (2*P)*(eLpNorm (fieldDerivative P (0,1) g) 2 (liftMeasure P)).toReal^2 := he
    _ ≤ (2/P)*(C+D)^2+(2*P)*(C+D)^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hn' (by positivity))
        (mul_le_mul_of_nonneg_left hd' (by positivity))
    _ = (Real.sqrt (2/P+2*P)*(C+D))^2 := by
      rw [mul_pow,Real.sq_sqrt (by positivity)]
      ring

include hperiod in
theorem jet_graph_memLp_and_bound (hf : ContDiff ℝ ∞ f) (n : ℕ)
    (hLp : MemLp (fun q => jetSeries P f q n) 2 (liftMeasure P))
    (hLp₁ : MemLp (fun q => jetSeries P f q (n + 1)) 2 (liftMeasure P))
    (θ : Vector3 → AddCircle P) (hθ : Continuous θ) (C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hn : (eLpNorm (fun q => jetSeries P f q n) 2 (liftMeasure P)).toReal ≤ C)
    (hd : (eLpNorm (fun q => jetSeries P f q (n + 1)) 2 (liftMeasure P)).toReal ≤ D) :
    MemLp (fun x => jetSeries P f (x,θ x) n) 2 volume ∧
      (eLpNorm (fun x => jetSeries P f (x,θ x) n) 2 volume).toReal ≤
        Real.sqrt (2/P+2*P)*(C+D) := by
  obtain ⟨hDLp,hDn⟩ := angularJet_memLp_and_bound P f hperiod hf n hLp₁
  exact graph_norm_bound P _ (jetSeries_smooth P f hperiod hf n) hLp hDLp θ hθ C D hC hD hn
      (hDn.trans hd)

end EulerCylinderJetGraphTrace

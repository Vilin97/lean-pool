/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderHeatEquation

@[expose] public section

/-! Exact identification of the Gaussian cylinder generator with the actual strong-jet Laplacian. -/

noncomputable section

namespace EulerGaussianCylinderHeat

open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity
  EulerSpatialSobolevInverse
  EulerCylinderSobolev EulerMetricHeatEnergy
open scoped ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Every existing strong Sobolev jet is transported by the genuine heat operator. -/
def cylinderHeatJet {q : ℕ} {f : LiftL2 period} (J : SpatialJet period standardDirection q f) (v :
  ℝ≥0) :
    SpatialJet period standardDirection q (cylinderHeat period v f) :=
  EulerPressureJetIdentities.SpatialJet.map (cylinderHeat period v)
    (fun a f => (cylinderHeat_translation period v a f).symm) J

/-- Heat preserves every actual derivative coordinate. -/
theorem cylinderHeatJet_word {q n : ℕ} {f : LiftL2 period}
    (J : SpatialJet period standardDirection q f) (v : ℝ≥0) (w : Fin n → Fin 4) :
    (cylinderHeatJet period J v).word w = cylinderHeat period v (J.word w) :=
  EulerPressureJetIdentities.SpatialJet.map_word J (cylinderHeat period v) _ w

/-- The actual heat operator commutes with the true strong-jet Laplacian. -/
theorem cylinderHeatJet_laplacian {f : LiftL2 period} (J : SpatialJet period standardDirection 2 f)
  (v : ℝ≥0) :
    jetLaplacian period (cylinderHeatJet period J v) = cylinderHeat period v (jetLaplacian period
      J) := by
  simp only [jetLaplacian, cylinderHeatJet_word, map_sum]

/-- Real-time extension of the cylinder heat semigroup. -/
def realCylinderHeat (t : ℝ) : LiftL2 period →L[ℝ] LiftL2 period := cylinderHeat period t.toNNReal

theorem realCylinderHeat_apply (t : ℝ) (f : LiftL2 period) :
    realCylinderHeat period t f = realHeatList period cylinderDirections t f :=
  (realHeatList_eq_toNNReal period cylinderDirections t f).symm

/-- The actual cylinder heat generator at positive variance is one half of the Laplacian. -/
theorem realCylinderHeat_generator_pos {f : LiftL2 period} (J : SpatialJet period standardDirection
  2 f)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => realCylinderHeat period s f)
      ((1/2 : ℝ) • realCylinderHeat period t (jetLaplacian period J)) t := by
  let df : Fin 4 → LiftL2 period := fun i => J.word (fun _ : Fin 1 => i)
  let ddf : Fin 4 → LiftL2 period := fun i => J.word (fun _ : Fin 2 => i)
  have hD (i : Fin 4) : HasDerivAt (lineOrbit period (standardDirection i) f) (df i) 0 := by
    have h := J.word_hasDerivAt (show 0 < 2 by omega) Fin.elim0 i
    have he : Fin.cons i Fin.elim0 = (fun _ : Fin 1 => i) := by
      funext j
      fin_cases j
      rfl
    rw [he, SpatialJet.word_zero] at h
    exact h
  have hDD (i : Fin 4) : HasDerivAt (lineOrbit period (standardDirection i) (df i)) (ddf i) 0 := by
    have h := J.word_hasDerivAt (show 1 < 2 by omega) (fun _ : Fin 1 => i) i
    have he : Fin.cons i (fun _ : Fin 1 => i) = (fun _ : Fin 2 => i) := by
      funext j
      fin_cases j <;> rfl
    rw [he] at h
    exact h
  have h := realHeatList_generator_pos period (List.ofFn (fun i : Fin 4 => i)) standardDirection f
    df ddf
    (fun i _ => hD i) (fun i _ => hDD i) ht
  simpa only [List.map_ofFn, Function.comp_def, List.sum_ofFn, realCylinderHeat_apply,
    cylinderDirections, jetLaplacian, ddf] using h

/-- The actual cylinder heat generator at zero variance is a right Laplacian derivative. -/
theorem realCylinderHeat_generator_zero {f : LiftL2 period} (J : SpatialJet period
  standardDirection 2 f) :
    HasDerivWithinAt (fun s => realCylinderHeat period s f)
      ((1/2 : ℝ) • jetLaplacian period J) (Set.Ici 0) 0 := by
  have hc : Continuous (fun t : ℝ => realCylinderHeat period t (jetLaplacian period J)) :=
    (cylinderHeat_continuous period _).comp continuous_real_toNNReal
  have hlim : Filter.Tendsto (fun s => (1/2 : ℝ) • realCylinderHeat period s (jetLaplacian period
    J))
      (𝓝[>] (0 : ℝ)) (𝓝 ((1/2 : ℝ) • jetLaplacian period J)) := by
    have h := (hc.const_smul (1/2 : ℝ)).continuousAt (x := 0)
    simpa only [Pi.smul_def, realCylinderHeat, Real.toNNReal_zero, cylinderHeat_zero] using
      (h.continuousWithinAt (s := Set.Ioi 0)).tendsto
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioi 0)
    (fun t ht => (realCylinderHeat_generator_pos period J
      ht).differentiableAt.differentiableWithinAt)
    (((cylinderHeat_continuous period f).comp
      continuous_real_toNNReal).continuousAt.continuousWithinAt)
    self_mem_nhdsWithin
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (realCylinderHeat_generator_pos period J ht).deriv.symm

/-- Variance2νt is the genuine viscosity-ν heat evolution. -/
def viscousCylinderHeat (ν t : ℝ) : LiftL2 period →L[ℝ] LiftL2 period := realCylinderHeat period
  (2*ν*t)

/-- The constructed heat evolution solves u_t=νΔu, with the actual strong spatial Laplacian. -/
theorem viscousCylinderHeat_equation {f : LiftL2 period} (J : SpatialJet period standardDirection 2
  f)
    {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) :
    HasDerivAt (fun s => viscousCylinderHeat period ν s f)
      (ν • jetLaplacian period (cylinderHeatJet period J (2*ν*t).toNNReal)) t := by
  have hp : 0 < 2*ν*t := by positivity
  have h := (realCylinderHeat_generator_pos period J hp).scomp t
    ((hasDerivAt_id t).const_mul (2*ν))
  simp only [mul_one] at h
  change HasDerivAt (fun s => viscousCylinderHeat period ν s f)
    ((2*ν) • ((1/2 : ℝ) • realCylinderHeat period (2*ν*t) (jetLaplacian period J))) t at h
  rw [smul_smul, show (2*ν)*(1/2 : ℝ)=ν by ring] at h
  rw [cylinderHeatJet_laplacian]
  exact h

end EulerGaussianCylinderHeat

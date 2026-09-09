/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSpatialEmbedding
public import LeanPool.NavierStokesAndEuler.Euler.MeanSmoothRepresentative
import LeanPool.NavierStokesAndEuler.Euler.CylinderClassicalSolenoidal
import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalConstraints

/-! A genuine smooth ordinary solenoidal L² field remains solenoidal on the periodic cylinder. -/

@[expose] public section


noncomputable section

namespace EulerMeanCylinderSolenoidal

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerTransportDerivatives EulerMeanSolenoidal EulerVectorCalculus
  EulerCylinderSpatialEmbedding EulerCylinderClassicalSolenoidal EulerMeanSmoothRepresentative
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]

omit [Fact (0 < P)] in
theorem fieldDerivative_spatial (f : Space → Space) (hf : ContDiff ℝ ∞ f)
    (a : LiftTangent) (z : LiftDomain P) :
    fieldDerivative P a (fun x : LiftDomain P => f x.1) z = fderiv ℝ f z.1 a.1 := by
  have hi : HasFDerivAt (fun h : LiftTangent => z.1+h.1)
      (ContinuousLinearMap.fst ℝ Space ℝ) 0 :=
    (hasFDerivAt_fst : HasFDerivAt (Prod.fst : LiftTangent → Space)
      (ContinuousLinearMap.fst ℝ Space ℝ) 0).const_add z.1
  have hd := (hf.differentiable (by simp) (z.1+(0 : LiftTangent).1)).hasFDerivAt.comp
    (0 : LiftTangent) hi
  have he := congrArg (fun L : LiftTangent →L[ℝ] Space => L a) hd.fderiv
  change (fderiv ℝ (fun h : LiftTangent => f (z.1+h.1)) 0) a = _
  simpa only [Function.comp_def,Prod.fst_zero,add_zero,
    comp_apply,ContinuousLinearMap.coe_fst'] using he

omit [Fact (0 < P)] in
theorem lift_classical_divergence (κ : ℝ) (m : Space) (f : Space → Space)
    (hf : ContDiff ℝ ∞ f) (hd : ∀ x, divergence f x = 0) (z : LiftDomain P) :
    (∑ i : Fin 3, (fieldDerivative P (coordinateDirection κ m i)
      (fun x : LiftDomain P => f x.1) z) i) = 0 := by
  simp_rw [fieldDerivative_spatial P f hf]
  change (∑ i : Fin 3, (fderiv ℝ f z.1 (κ • EuclideanSpace.single i 1)) i) = 0
  simp only [map_smul,PiLp.smul_apply,smul_eq_mul,← Finset.mul_sum]
  rw [← divergence_eq_coordinate_sum,hd,mul_zero]

theorem embedding_representative (u : L2) (f : Space → Space)
    (hrep : (u : Space → Space) =ᵐ[volume] f) :
    (embedding P u : LiftDomain P → Space) =ᵐ[liftMeasure P] fun z => f z.1 := by
  filter_upwards [lift_ae P u,
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure Space))
      (ν := (volume : Measure (AddCircle P)))).ae hrep] with z hl hr
  exact hl.trans hr

/-- The conclusion is membership in the actual closed lifted-gradient orthogonal complement. -/
theorem embedding_mem (κ : ℝ) (m : Space) (u : L2) (hu : u ∈ solenoidalSpace)
    (f : Space → Space) (hf : ContDiff ℝ ∞ f) (hrep : (u : Space → Space) =ᵐ[volume] f) :
    embedding P u ∈ divergenceFreeSpace P κ m := by
  apply mem_of_classical P κ m (embedding P u) (fun z : LiftDomain P => f z.1)
    (embedding_representative P u f hrep)
  · intro z
    exact hf.comp (contDiff_const.add contDiff_fst)
  · exact lift_classical_divergence P κ m f hf
      (EulerMeanClassical.solenoidal_representative_divergence u hu f hf hrep)

theorem embedding_mem_of_smooth_orbit (κ : ℝ) (m : Space) (u : L2)
    (hu : u ∈ solenoidalSpace) (hs : SmoothOrbit u) :
    embedding P u ∈ divergenceFreeSpace P κ m :=
  embedding_mem P κ m u hu (representative u hs) (representative_smooth u hs) (representative_ae u
      hs)

end EulerMeanCylinderSolenoidal

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverageTime
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketOrbitForcing
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSpatialMeanPath
public import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeRegularity
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketNonlinearForcing
public import LeanPool.NavierStokesAndEuler.Euler.MeanSmoothRepresentative
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSpatialMean
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevSpace
import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverageRepresentative

/-! Literal angular averaging preserves actual raw cylinder-path admissibility. -/

section

/-!
# Literal angular averages are admissible mean forcing

The cylinder-to-space mean is the actual normalized angular integral. Its
proved ordinary translation regularity is converted into literal spatial L²
jets, so the mean packet provider receives an actual admissible input.
-/

section

/-! The bounded cylinder-to-space operator is the literal angular integral on smooth fields. -/

@[expose] public section

noncomputable section

namespace EulerCylinderSpatialMean

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerCylinderSpatialEmbedding EulerCylinderAngleAverage
  EulerCylinderSobolevSpace EulerSobolevPointEvaluation

variable (P : ℝ) [Fact (0 < P)]

/-- A continuous constant-angle field is spatially L² whenever its cylinder lift is L². -/
theorem continuous_memLp_of_lift {V : Type*} [NormedAddCommGroup V]
    (g : Space → V) (hg : Continuous g)
    (hgl : MemLp (fun z : LiftDomain P => g z.1) 2 (liftMeasure P)) :
    MemLp g 2 (volume : Measure Space) := by
  have hm : MemLp g 2 (Measure.map (Prod.fst : LiftDomain P → Space) (liftMeasure P)) :=
    (memLp_map_measure_iff hg.aestronglyMeasurable measurable_fst.aemeasurable).mpr hgl
  change MemLp g 2 (Measure.map Prod.fst
    ((volume : Measure Space).prod (volume : Measure (AddCircle P)))) at hm
  rw [Measure.map_fst_prod, AddCircle.measure_univ] at hm
  have hP : ENNReal.ofReal P ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Fact.out : 0 < P))
  have hu := hm.smul_measure (c := (ENNReal.ofReal P)⁻¹) (ENNReal.inv_ne_top.mpr hP)
  simpa only [smul_smul, ENNReal.inv_mul_cancel hP ENNReal.ofReal_ne_top, one_smul] using hu

/-- Raw mean, given by `P⁻¹ • (∫ s in (0 : ℝ)..P, f (y,(s : AddCircle P)))`. -/
def rawMean (f : LiftDomain P → Space) (y : Space) : Space :=
  P⁻¹ • (∫ s in (0 : ℝ)..P, f (y,(s : AddCircle P)))

variable (u : SobolevSpace P 3) (f : LiftDomain P → Space) (hf : Continuous f)
  (hrep : (value P u : LiftDomain P → Space) =ᵐ[liftMeasure P] f)

include hf hrep

theorem rawMean_continuous : Continuous (rawMean P f) := by
  have he : rawMean P f = fun y => representative P (sobolevAverage P 3 u) (y,0) := by
    funext y
    exact (pointEvaluation_average_mean P u f hf hrep y 0).symm
  rw [he]
  exact (representative_continuous P (sobolevAverage P 3 u)).comp
    (continuous_id.prodMk continuous_const)

theorem average_ae_rawMean :
    (average P (value P u) : LiftDomain P → Space) =ᵐ[liftMeasure P] fun z => rawMean P f z.1 := by
  have he (z : LiftDomain P) : representative P (sobolevAverage P 3 u) z = rawMean P f z.1 := by
    obtain ⟨θ,hθ⟩ := QuotientAddGroup.mk_surjective z.2
    have hz : z=(z.1,(θ : AddCircle P)) := by
      apply Prod.ext
      · rfl
      · exact hθ.symm
    rw [hz]
    exact pointEvaluation_average_mean P u f hf hrep z.1 θ
  filter_upwards [representative_ae P (sobolevAverage P 3 u)] with z hz
  exact hz.trans (he z)

theorem rawMean_memLp : MemLp (rawMean P f) 2 (volume : Measure Space) := by
  apply continuous_memLp_of_lift P (rawMean P f) (rawMean_continuous P u f hf hrep)
  exact (memLp_congr_ae (average_ae_rawMean P u f hf hrep)).mp (Lp.memLp (average P (value P u)))

/-- The actual ordinary-space L² mean has the normalized integral as its representative. -/
theorem mean_ae_rawMean :
    (mean P (value P u) : Space → Space) =ᵐ[volume] rawMean P f := by
  let v : SpatialL2 Space := (rawMean_memLp P u f hf hrep).toLp (rawMean P f)
  have hv : (v : Space → Space) =ᵐ[volume] rawMean P f :=
    (rawMean_memLp P u f hf hrep).coeFn_toLp
  have he : embedding P v = average P (value P u) := by
    apply Lp.ext
    filter_upwards [lift_ae P v,
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure Space))
        (ν := (volume : Measure (AddCircle P)))).ae hv,
      average_ae_rawMean P u f hf hrep] with z hl hm ha
    exact hl.trans (hm.trans ha.symm)
  have hm : mean P (value P u) = v := by
    rw [← mean_average P (value P u), ← he, mean_embedding]
  rw [hm]
  exact hv

end EulerCylinderSpatialMean

end
end

end

section

/-! The literal angular mean of a solved cylinder path is an actual smooth spatial L² path. -/

@[expose] public section

noncomputable section

namespace EulerCylinderSpatialMean

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSobolevSpace EulerCylinderSmoothOrbit EulerLpCylinderTranslation
  EulerCylinderSpatialEmbedding EulerMetricTransport
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (p : C(K, LiftL2 P)) (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))

include hp

/-- The ordinary L² time path represents the actual angular integral at every time. -/
theorem pathMean_pointField_ae (t : K) :
    (pathMean P p t : Space → Space) =ᵐ[volume] rawMean P (pointField P p hp t) := by
  have h := mean_ae_rawMean P (sobolevPath P 3 p hp t) (pointField P p hp t)
    (smoothField_continuous P _ (pointField_smooth P p hp t))
    (by simpa only [sobolevPath_value] using pointField_ae P p hp t)
  simpa only [pathMean_apply, sobolevPath_value] using h

theorem mean_slice_orbit (t : K) :
    EulerMeanSmoothRepresentative.SmoothOrbit (pathMean P p t) := by
  have h := (ContinuousMap.evalCLM ℝ t).contDiff.comp (pathMean_orbit_contDiff P p hp)
  exact h

/-- Uniqueness identifies the mean solver's ordinary representative with the literal integral. -/
theorem mean_pointField_eq (t : K) :
    EulerMeanSmoothRepresentative.representative (pathMean P p t) (mean_slice_orbit P p hp t) =
      rawMean P (pointField P p hp t) := by
  apply EulerMeanSmoothRepresentative.representative_unique
  · exact rawMean_continuous P (sobolevPath P 3 p hp t) (pointField P p hp t)
      (smoothField_continuous P _ (pointField_smooth P p hp t))
      (by simpa only [sobolevPath_value] using pointField_ae P p hp t)
  · exact pathMean_pointField_ae P p hp t

theorem rawMean_pointField_contDiff (t : K) :
    ContDiff ℝ ∞ (rawMean P (pointField P p hp t)) := by
  rw [← mean_pointField_eq P p hp t]
  exact EulerMeanSmoothRepresentative.representative_smooth _ _

end EulerCylinderSpatialMean

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanPacketProvider

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerCylinderSpatialMean
  EulerMeanSmoothRepresentative EulerMeanTimeContinuousTranslation
  EulerPacketPointJets EulerPacketProfileRecursion
open scoped ContDiff

variable (D : Data) (P : ℝ) [Fact (0 < P)]
  (p : C(Icc (0 : ℝ) D.T, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))

/-- The literal normalized integral of the actual cylinder representative. -/
def angularMeanRaw : VectorField := fun z =>
  rawMean P (pointField P p hp (D.clamp z.1)) z.2.1

include hp in
theorem angularMean_orbit :
    ContDiff ℝ ∞ (fun a : Space => pathTranslation D.T a (pathMean P p)) := by
  simpa only [pathTranslation, spatialPathTranslation, EulerLpTranslation.translation,
    EulerMeanSolenoidal.translation] using pathMean_orbit_contDiff P p hp

/-- A genuine forcing witness for the normalized angular mean. -/
def angularMeanForcing : Forcing D (angularMeanRaw D P p hp) :=
  Forcing.ofOrbitPath (pathMean P p) (angularMean_orbit D P p hp) (fun t x θ => by
    simp only [angularMeanRaw, Data.clamp_coe]
    exact congrFun (mean_pointField_eq P p hp t).symm x)

/-- A raw cylinder field identified with that representative has the same admissible mean. -/
def angularMeanForcingOfRaw (raw : VectorField)
    (hraw : ∀ (t : Icc (0 : ℝ) D.T) x θ,
      raw (t, (x, θ)) = pointField P p hp t (x, (θ : AddCircle P))) :
    Forcing D (fun z => P⁻¹ • (∫ θ in (0 : ℝ)..P, raw (z.1,(z.2.1,θ)))) := by
  apply (angularMeanForcing D P p hp).congr
  intro t x θ
  simp only [angularMeanRaw, Data.clamp_coe, rawMean]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  exact hraw t x s

end EulerMeanPacketProvider

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField.Field

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerMetricTransport
  EulerCylinderSobolevSpace EulerCylinderAngleAverage EulerCylinderSpatialMean
  EulerPacketProfileRecursion
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField}

/-- Its path is the genuine average operator, and its raw field is exactly the angular integral. -/
def angleMean (G : Field P T raw) : Field P T (EulerPacketProfileRecursion.angleMean P raw) :=
  ofLifted (pathAverage P G.path) (pathAverage_orbit_contDiff P G.path G.orbit)
    (fun t x => rawMean P (pointField P G.path G.orbit t) x.1)
    (fun t => (rawMean_continuous P (sobolevPath P 3 G.path G.orbit t)
      (pointField P G.path G.orbit t) (smoothField_continuous P _ (pointField_smooth P G.path
          G.orbit t))
      (by
          simpa only [sobolevPath_value] using pointField_ae P G.path G.orbit t)).comp
              continuous_fst)
    (fun t => by
      have h := average_ae_rawMean P (sobolevPath P 3 G.path G.orbit t)
        (pointField P G.path G.orbit t) (smoothField_continuous P _ (pointField_smooth P G.path
            G.orbit t))
        (by simpa only [sobolevPath_value] using pointField_ae P G.path G.orbit t)
      simpa only [sobolevPath_value,pathAverage_apply] using h)
    (fun t x θ => by
      change P⁻¹ • (∫ s in (0 : ℝ)..P, raw (t,(x,s))) =
        P⁻¹ • (∫ s in (0 : ℝ)..P, pointField P G.path G.orbit t (x,(s : AddCircle P)))
      congr 1
      apply intervalIntegral.integral_congr
      intro s _
      exact G.raw_eq t x s)

/-- Subtracting the literal mean is an operation on the actual cylinder L² path. -/
def highPart (G : Field P T raw) : Field P T (raw-EulerPacketProfileRecursion.angleMean P raw) :=
  G.sub G.angleMean

@[simp] theorem angleMean_path (G : Field P T raw) :
    G.angleMean.path = pathAverage P G.path := rfl

/-- The same actual angular integral is admissible for the constructed ordinary-space mean solver.
-/
def meanForcing (D : EulerMeanPacketProvider.Data) {raw : VectorField}
    (G : Field P D.T raw) :
    EulerMeanPacketProvider.Forcing D (EulerPacketProfileRecursion.angleMean P raw) :=
  EulerMeanPacketProvider.angularMeanForcingOfRaw D P G.path G.orbit raw G.raw_eq

end EulerPacketCylinderField.Field

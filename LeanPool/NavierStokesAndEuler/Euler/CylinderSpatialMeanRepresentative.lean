/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSpatialMean
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevSpace
import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverageRepresentative

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

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerC1Breakdown
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryMaximalVorticityIntegral
public import LeanPool.NavierStokesAndEuler.Euler.SolutionDefinitions
import LeanPool.NavierStokesAndEuler.Euler.ComparatorSingularityNorms
import LeanPool.NavierStokesAndEuler.Euler.EulerC1Limsup
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerBKM
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerKineticEnergy
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryL2Integration

/-! The canonical maximal fields in the challenge's position-first, real-time
convention. Extension by zero outside the lifespan has no role in the equation. -/

@[expose] public section


noncomputable section

open Set Filter MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSobolevBoundedField
open scoped ENNReal Topology ContDiff

namespace Euler.ComparatorBridge

variable {A : SmoothL2Field Space} (L : FiniteLifespan A)

/-- Maximal velocity extension, with branches according to `ht : t ∈ Ico (0 : ℝ) L.duration`. -/
def maximalVelocityExtension (x : Space) (t : ℝ) : Space :=
  if ht : t ∈ Ico (0 : ℝ) L.duration then L.maximalVelocity ⟨t, ht⟩ x else 0

/-- Maximal pressure extension, with branches according to `ht : t ∈ Ico (0 : ℝ) L.duration`. -/
def maximalPressureExtension (x : Space) (t : ℝ) : ℝ :=
  if ht : t ∈ Ico (0 : ℝ) L.duration then L.maximalPressure ⟨t, ht⟩ x else 0

theorem maximalVelocityExtension_eq (t : L.Time) :
    (maximalVelocityExtension L · (t : ℝ)) = L.maximalVelocity t := by
  funext x
  simp only [maximalVelocityExtension, dite_eq_left t.property]

theorem maximalPressureExtension_eq (t : L.Time) :
    (maximalPressureExtension L · (t : ℝ)) = L.maximalPressure t := by
  funext x
  simp only [maximalPressureExtension, dite_eq_left t.property]

theorem maximalVelocityExtension_initial : (maximalVelocityExtension L · 0) = A.field :=
  (maximalVelocityExtension_eq L L.initialTime).trans L.maximalVelocity_initial

theorem maximalVelocityExtension_memLp (t : ℝ) (ht : t ∈ Ico 0 L.duration) :
    MemLp (maximalVelocityExtension L · t) 2 volume := by
  rw [maximalVelocityExtension_eq L ⟨t, ht⟩]
  exact (L.maximalField ⟨t, ht⟩).memLp

theorem maximalVelocityExtension_divergence (t : ℝ) (ht : t ∈ Ico 0 L.duration)
    (x : Space) : Euler.divergence (maximalVelocityExtension L · t) x = 0 := by
  rw [maximalVelocityExtension_eq L ⟨t, ht⟩]
  exact L.maximalVelocity_divergence ⟨t, ht⟩ x

theorem velocityC1Norm_maximal (t : L.Time) :
    Euler.velocityC1Norm (maximalVelocityExtension L · (t : ℝ)) =
      ENNReal.ofReal (L.maximalC1Norm t) := by
  rw [maximalVelocityExtension_eq]
  exact velocityC1Norm_eq (L.maximalField t)

theorem vorticityNorm_maximal (t : L.Time) :
    Euler.vorticityNorm (maximalVelocityExtension L · (t : ℝ)) =
      ENNReal.ofReal (L.maximalVorticityNorm t) := by
  rw [maximalVelocityExtension_eq]
  exact vorticityNorm_eq (L.maximalField t)

theorem vorticityNorm_maximal_density (t : ℝ) (ht : t ∈ Ico 0 L.duration) :
    Euler.vorticityNorm (maximalVelocityExtension L · t) =
      ENNReal.ofReal (L.maximalVorticityDensity t) := by
  exact (vorticityNorm_maximal L ⟨t, ht⟩).trans
    (congrArg ENNReal.ofReal (L.maximalVorticityDensity_eq ⟨t, ht⟩)).symm

theorem maximalField_kineticEnergy (t : L.Time) :
    ‖(L.maximalField t).toLp‖ ^ 2 = ‖A.toLp‖ ^ 2 := by
  change ‖((L.evolution (L.intermediateHorizon t) (L.intermediateHorizon_pos t)
    (L.intermediateHorizon_lt t)).velocity (L.intermediateTime t)).toLp‖ ^ 2 = _
  rw [Evolution.kineticEnergy_conserved, L.evolution_initial]

theorem maximalVelocityExtension_energy (t : ℝ) (ht : t ∈ Ico 0 L.duration) :
    (∫ x, ‖maximalVelocityExtension L x t‖ ^ 2) = ‖A.toLp‖ ^ 2 := by
  have he := field_inner (L.maximalField ⟨t, ht⟩) (L.maximalField ⟨t, ht⟩)
  have hf : (∫ x, ‖(L.maximalField ⟨t, ht⟩).field x‖ ^ 2) =
      ‖(L.maximalField ⟨t, ht⟩).toLp‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using he.symm
  have hx := congrFun (maximalVelocityExtension_eq L ⟨t, ht⟩)
  calc
    _ = ∫ x, ‖(L.maximalField ⟨t, ht⟩).field x‖ ^ 2 :=
      integral_congr_ae (Eventually.of_forall (fun x => congrArg (fun a : Space => ‖a‖ ^ 2) (hx x)))
    _ = ‖A.toLp‖ ^ 2 := hf.trans (maximalField_kineticEnergy L ⟨t, ht⟩)

theorem maximalVelocityExtension_bounded_energy :
    ∃ E : ℝ, ∀ t ∈ Ico (0 : ℝ) L.duration,
      (∫ x, ‖maximalVelocityExtension L x t‖ ^ 2) < E := by
  refine ⟨‖A.toLp‖ ^ 2 + 1, ?_⟩
  intro t ht
  rw [maximalVelocityExtension_energy L t ht]
  exact lt_add_one _

theorem maximalVelocityExtension_c1_locally_bounded
    (S : ℝ) (_hS : 0 < S) (hSL : S < L.duration) :
    (⨆ t ∈ Icc (0 : ℝ) S, Euler.velocityC1Norm (maximalVelocityExtension L · t)) < ⊤ := by
  have hc : Continuous (fun t : Icc (0 : ℝ) S =>
      L.maximalC1Norm (L.shorterTime S hSL t)) :=
    L.maximalC1Norm_continuous.comp
      (continuous_subtype_val.subtype_mk (fun t => ⟨t.property.1, t.property.2.trans_lt hSL⟩))
  obtain ⟨M, hM⟩ := (isCompact_range hc).bddAbove
  apply lt_of_le_of_lt (b := ENNReal.ofReal M) _ ENNReal.ofReal_lt_top
  refine iSup_le (fun t => iSup_le (fun ht => ?_))
  exact (velocityC1Norm_maximal L (L.shorterTime S hSL ⟨t, ht⟩)).le.trans
    (ENNReal.ofReal_le_ofReal (hM ⟨⟨t, ht⟩, rfl⟩))

theorem maximalVelocityExtension_vorticity_locally_integrable
    (S : ℝ) (hS : 0 < S) (hSL : S < L.duration) :
    (∫⁻ t in Ico (0 : ℝ) S, Euler.vorticityNorm (maximalVelocityExtension L · t)) < ⊤ := by
  have he : (∫⁻ t in Ico (0 : ℝ) S, Euler.vorticityNorm (maximalVelocityExtension L · t)) =
      ∫⁻ t in Ico (0 : ℝ) S, ENNReal.ofReal (L.maximalVorticityDensity t) := by
    apply setLIntegral_congr_fun measurableSet_Ico
    intro t ht
    exact vorticityNorm_maximal_density L t ⟨ht.1, ht.2.trans hSL⟩
  rw [he, ← ofReal_integral_eq_lintegral_ofReal
    ((L.maximalVorticityDensity_continuousOn S hS hSL).integrableOn_Icc.mono_set
      Ico_subset_Icc_self)
    (Eventually.of_forall L.maximalVorticityDensity_nonneg)]
  exact ENNReal.ofReal_lt_top

theorem maximalVelocityExtension_c1_limsup :
    Filter.limsup (fun t : ℝ => Euler.velocityC1Norm (maximalVelocityExtension L · t))
      (𝓝[<] L.duration) = ⊤ := by
  rw [← L.map_time_atTop, ← Filter.limsup_comp]
  simpa only [Function.comp_def, velocityC1Norm_maximal] using L.maximalC1Norm_limsup_atTop

theorem maximalVelocityExtension_vorticity_integral :
    (∫⁻ t in Ico (0 : ℝ) L.duration, Euler.vorticityNorm (maximalVelocityExtension L · t)) = ⊤ := by
  rw [setLIntegral_congr_fun measurableSet_Ico (vorticityNorm_maximal_density L)]
  exact L.vorticity_lintegral_eq_top

end Euler.ComparatorBridge

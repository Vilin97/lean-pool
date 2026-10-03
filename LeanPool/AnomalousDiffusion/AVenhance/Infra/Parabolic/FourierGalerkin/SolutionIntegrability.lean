/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ScalarRepresentative
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.FrozenDriftProduct

/-!
# Integrability of the drift pairing at the synchronized limit
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization
open scoped ENNReal RealInnerProductSpace

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance solutionIntegrabilityMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance solutionIntegrabilityProbabilityCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance solutionIntegrabilityProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

/-- Periodic drift represented as a Euclidean-normed spatial vector on time times the torus. -/
def SolutionIntegrability.torusFrozenDriftVector (P : FrozenDriftProblem) : ℝ × Torus →
    SpatialVector :=
  fun p => WithLp.toLp 2 (AVenhance.Infra.Torus.periodicToTorus (P.b p.1) p.2)

/-- Pointwise pairing of the frozen drift with a product-space L² gradient. -/
def SolutionIntegrability.torusFrozenDriftGradientPairing (P : FrozenDriftProblem)
    (G : GradientProductTimeL2) : ℝ × Torus → ℝ := fun p =>
  inner ℝ (SolutionIntegrability.torusFrozenDriftVector P p) (G p)

/-- The drift paired with an arbitrary product-space `L²` gradient is integrable on
time times the torus. -/
theorem FrozenDriftProblem.torusFrozenDriftGradientPairing_integrable
    (P : FrozenDriftProblem) (G : GradientProductTimeL2) :
    Integrable (SolutionIntegrability.torusFrozenDriftGradientPairing P G)
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
  have hBtop : MemLp (SolutionIntegrability.torusFrozenDriftVector P) ⊤
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
    change MemLp (fun p : ℝ × Torus =>
      WithLp.toLp 2 (AVenhance.Infra.Torus.periodicToTorus (P.b p.1) p.2))
      ⊤ (GalerkinTimeMeasure.prod (volume : Measure Torus))
    exact P.torusDrift_memLp_top
  have hBtwo : MemLp (SolutionIntegrability.torusFrozenDriftVector P) 2
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) :=
    hBtop.mono_exponent (by norm_num)
  let B : GradientProductTimeL2 := hBtwo.toLp (SolutionIntegrability.torusFrozenDriftVector P)
  have hpair : (fun p => inner ℝ (B p) (G p)) =ᵐ[
      GalerkinTimeMeasure.prod (volume : Measure Torus)]
      SolutionIntegrability.torusFrozenDriftGradientPairing P G := by
    filter_upwards [hBtwo.coeFn_toLp] with p hp
    change inner ℝ (B p) (G p) =
      inner ℝ (SolutionIntegrability.torusFrozenDriftVector P p) (G p)
    rw [hp]
  have hLpInt := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) B G
  exact hLpInt.congr hpair

/-- Pulling the drift pairing back to the Euclidean cell preserves its integrability. -/
theorem FrozenDriftProblem.synchronizedGradient_driftPairing_integrable
    (P : FrozenDriftProblem) (G : GradientProductTimeL2) :
    Integrable (fun p : ℝ × Vec 2 =>
      Homogenization.vecDot (P.b p.1 p.2)
        (synchronizedGradientRepresentative G p.1 p.2))
      (volume.restrict AVenhance.timeCube) := by
  have htorus := P.torusFrozenDriftGradientPairing_integrable G
  have hphysical : Integrable
      (SolutionIntegrability.torusFrozenDriftGradientPairing P G ∘ physicalTimeTorusMap)
      (volume.restrict AVenhance.timeCube) :=
      (measurePreserving_physicalTimeTorusMap.integrable_comp
      htorus.aestronglyMeasurable).2 htorus
  have htimecube : MeasurableSet AVenhance.timeCube := by
    rw [AVenhance.timeCube]
    refine measurableSet_Ioo.prod ?_
    unfold AVenhance.unitCube
    exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)
  have heq : (fun p : ℝ × Vec 2 =>
      Homogenization.vecDot (P.b p.1 p.2)
        (synchronizedGradientRepresentative G p.1 p.2)) =ᵐ[
          volume.restrict AVenhance.timeCube]
      (SolutionIntegrability.torusFrozenDriftGradientPairing P G) ∘ physicalTimeTorusMap := by
    filter_upwards [ae_restrict_mem htimecube] with p hp
    rcases hp with ⟨ht, hx⟩
    have hcell : p.2 ∈ AVenhance.Infra.Torus.unitCell 2 := by
      simp only [AVenhance.unitCube, Set.mem_pi, Set.mem_univ,
        forall_true_left] at hx
      simp only [AVenhance.Infra.Torus.unitCell,
        AVenhance.Infra.Torus.unitCellAt, Set.mem_ofPred_eq, zero_add]
      intro i
      exact ⟨(hx i).1, le_of_lt (hx i).2⟩
    have hrepr := AVenhance.Infra.Torus.unitTorusRepresentative_eq_of_mem_unitCell hcell
    have hdrift : AVenhance.Infra.Torus.periodicToTorus (P.b p.1)
        (AVenhance.Infra.Torus.toUnitTorus 2 p.2) = P.b p.1 p.2 := by
      simp [AVenhance.Infra.Torus.periodicToTorus, hrepr]
    simp [SolutionIntegrability.torusFrozenDriftGradientPairing,
        SolutionIntegrability.torusFrozenDriftVector,
      physicalTimeTorusMap, synchronizedGradientRepresentative, hdrift,
      PiLp.inner_apply, Homogenization.vecDot]
    ring
  exact hphysical.congr heq.symm

end AVenhance.Infra.Parabolic.FourierGalerkin

end

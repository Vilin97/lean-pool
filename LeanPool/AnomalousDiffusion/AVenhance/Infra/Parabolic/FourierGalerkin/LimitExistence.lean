/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.LimitArbitraryTest
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.WeakGradientAssembly

/-!
# weak-solution existence from the synchronized Galerkin limit

The synchronized scalar path and product-space limits assemble into the exact `IsWeakSolutionGrad`
    predicate. The slice derivative identities are upgraded to global Euclidean
weak gradients by the periodization bridge, and the Fourier-cutoff weak equation is passed to all
smooth spacetime tests.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance limitExistenceMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance limitExistenceMeasureIsAddHaar : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance limitExistenceProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance limitExistenceProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

/-- Every bounded measurable periodic drift and every `L²` datum have a weak
solution in the exact author-`IsWeakSolutionGrad` class. -/
theorem FrozenDriftProblem.exists_isWeakSolutionGrad (P : FrozenDriftProblem) :
    ∃ θ : ℝ → Vec 2 → ℝ, ∃ Dθ : ℝ → Vec 2 → Vec 2,
      AVenhance.IsWeakSolutionGrad P.b P.κ P.θ₀ θ Dθ := by
  obtain ⟨σ, hσ, u, U, G, Uprod, Gprod, hUcont, hPathWeak, hUweak, hGweak,
      hScalarProductWeak, hGradientProductWeak, hbound, _htrace, _hUbound, _hGbound,
      _hUprodBound, _hGprodBound⟩ := P.exists_synchronized_weak_product_limit
  obtain ⟨S, hSmeas, hSae, hS⟩ := exists_measurable_synchronizedScalarSliceGood
    P σ u Uprod hPathWeak hScalarProductWeak hUcont
  let θ : ℝ → Vec 2 → ℝ := synchronizedScalarRepresentative Uprod u S
  let Dθ : ℝ → Vec 2 → Vec 2 := synchronizedGradientRepresentative Gprod
  have hpoint := synchronizedScalarRepresentative_pointwise_clauses
    Uprod u S P.scalarBound P.scalarBound_nonneg hS hbound
  have hthetaMem : MemLp (fun p : ℝ × Vec 2 => θ p.1 p.2) 2
      (volume.restrict AVenhance.timeCube) := by
    simpa [θ] using synchronizedScalarRepresentative_memLp_timeCube
      Uprod u S hSmeas hSae
  have hgradientMem (i : Fin 2) : MemLp
      (fun p : ℝ × Vec 2 => Dθ p.1 p.2 i) 2
      (volume.restrict AVenhance.timeCube) := by
    simpa [Dθ] using synchronizedGradientRepresentative_memLp_timeCube Gprod i
  have hmode := P.synchronized_limit_cell_realFourier_derivative_ae σ u Uprod Gprod
    S hS hSae hPathWeak hScalarProductWeak hGradientProductWeak hUcont hbound
  have hperiodicH1 : ∀ᵐ t ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
      AVenhance.IsPeriodicH1With (θ t) (Dθ t) := by
    simpa [θ, Dθ] using synchronized_limit_isPeriodicH1With_ae
      Uprod Gprod u S P.scalarBound P.scalarBound_nonneg hbound hS hmode
  have hdrift : Integrable
      (fun p : ℝ × Vec 2 =>
        Homogenization.vecDot (P.b p.1 p.2) (Dθ p.1 p.2))
      (volume.restrict AVenhance.timeCube) := by
    simpa [Dθ] using P.synchronizedGradient_driftPairing_integrable Gprod
  have hweakContinuous : ∀ v : ScalarTorusL2,
      Continuous (fun t => inner ℝ (u t) v) := hUcont
  have htestPairing : ∀ ψ : Vec 2 → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ →
        ContinuousOn (fun t => ∫ x in AVenhance.unitCube, θ t x * ψ x)
          (Set.Icc (0 : ℝ) 1) := by
    intro ψ hψ hψperiodic
    simpa [θ] using synchronizedScalarRepresentative_testPairing_continuous
      Uprod u S hS hweakContinuous hψ hψperiodic
  refine ⟨θ, Dθ, ?_⟩
  unfold AVenhance.IsWeakSolutionGrad
  refine ⟨hpoint.1, hpoint.2, hthetaMem, hgradientMem, hperiodicH1,
    hdrift, htestPairing, ?_⟩
  intro φ htest
  exact P.synchronized_limit_arbitrary_test_cell_identity σ hσ u Uprod Gprod
    hScalarProductWeak hGradientProductWeak S hSmeas hSae hS
    htest.1 htest.2.1 htest.2.2

end AVenhance.Infra.Parabolic.FourierGalerkin

end

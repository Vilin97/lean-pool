/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.Topology.ContinuousMap.CompactlySupported
import LeanPool.MarkovProcess.MarkovProcess.Killed.GluingPotential

/-!
# From vanishing observables to measurable ones

An identity between a measure `nu` on a target space and a measure `mu` on a source space,
tested on observables which are supported in the range of a measurable embedding `i` and
extended by zero off it, propagates from continuous observables vanishing at infinity to all
nonnegative measurable observables
(`lintegral_extend_eq_of_forall_zeroAtInfty`).  The reason is that both sides are integrals
against finite Borel measures on the source space, and continuous observables with compact
support already separate finite Borel measures on a locally compact second-countable metric
space.

This is the bridge which upgrades an analytically supplied identity of resolvents, stated for
continuous observables vanishing at infinity, to the identity of the corresponding potential
measures.

No topology on the target space is used, and no relation between the two measures other than the
tested identity is assumed.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty CompactlySupported

noncomputable section

namespace MarkovProcess

section Topological

variable {X : Type*} [TopologicalSpace X]

/-- A continuous observable with compact support, read as an observable vanishing at infinity. -/
noncomputable def compactlySupportedToZeroAtInfty (f : C_c(X, ℝ)) : C₀(X, ℝ) where
  toContinuousMap := f.toContinuousMap
  zero_at_infty' := HasCompactSupport.is_zero_at_infty f.hasCompactSupport'

/-- A compactly supported function, read as an observable vanishing at infinity, keeps its
values. -/
@[simp] theorem compactlySupportedToZeroAtInfty_apply (f : C_c(X, ℝ)) (x : X) :
    compactlySupportedToZeroAtInfty f x = f x := rfl

end Topological

section Measurable

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Integration of an observable extended by zero off the range of a measurable embedding is
integration of the observable against the pullback measure. -/
theorem lintegral_extend_eq_lintegral_comap {i : X → Y} (hi : MeasurableEmbedding i)
    (nu : Measure Y) {h : X → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ z, Function.extend i h 0 z ∂nu = ∫⁻ y, h y ∂nu.comap i := by
  have hext : Measurable (Function.extend i h 0) := hi.measurable_extend hh measurable_const
  have hzero : Function.extend i h 0 = (Set.range i).indicator (Function.extend i h 0) := by
    funext z
    by_cases hz : z ∈ Set.range i
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, Function.extend_apply' _ _ _ fun hmem ↦ hz hmem]
      rfl
  calc ∫⁻ z, Function.extend i h 0 z ∂nu
      = ∫⁻ z, (Set.range i).indicator (Function.extend i h 0) z ∂nu := by rw [← hzero]
    _ = ∫⁻ z in Set.range i, Function.extend i h 0 z ∂nu :=
        lintegral_indicator hi.measurableSet_range _
    _ = ∫⁻ z, Function.extend i h 0 z ∂(nu.comap i).map i := by rw [hi.map_comap]
    _ = ∫⁻ y, Function.extend i h 0 (i y) ∂nu.comap i := lintegral_map hext hi.measurable
    _ = ∫⁻ y, h y ∂nu.comap i := by simp only [hi.injective.extend_apply]

/-- The pullback of a finite measure along a measurable embedding is finite. -/
theorem isFiniteMeasure_comap {i : X → Y} (hi : MeasurableEmbedding i) (nu : Measure Y)
    [IsFiniteMeasure nu] : IsFiniteMeasure (nu.comap i) := by
  refine ⟨?_⟩
  have hmass : (nu.comap i).map i Set.univ = nu.comap i Set.univ := by
    rw [Measure.map_apply hi.measurable MeasurableSet.univ, Set.preimage_univ]
  rw [← hmass, hi.map_comap]
  exact lt_of_le_of_lt (Measure.restrict_le_self Set.univ) (measure_lt_top nu Set.univ)

end Measurable

section Transfer

variable {X Y : Type*} [MetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]

/-- **Testing an identity of measures on vanishing observables is enough.**  If a measure on the
target and a measure on the source assign the same integral to every nonnegative continuous
observable vanishing at infinity, extended by zero off the range of a measurable embedding, then
they assign the same integral to every nonnegative measurable observable. -/
theorem lintegral_extend_eq_of_forall_zeroAtInfty {i : X → Y} (hi : MeasurableEmbedding i)
    (nu : Measure Y) (mu : Measure X) [IsFiniteMeasure nu] [IsFiniteMeasure mu]
    (hc0 : ∀ f : C₀(X, ℝ), (∀ y, 0 ≤ f y) →
      ∫⁻ z, Function.extend i (fun y ↦ ENNReal.ofReal (f y)) 0 z ∂nu =
        ∫⁻ y, ENNReal.ofReal (f y) ∂mu)
    {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, Function.extend i g 0 z ∂nu = ∫⁻ y, g y ∂mu := by
  have : IsFiniteMeasure (nu.comap i) := isFiniteMeasure_comap hi nu
  have hpull : nu.comap i = mu := by
    refine Measure.ext_of_integral_eq_on_compactlySupported_nnreal fun f ↦ ?_
    set F : C₀(X, ℝ) := compactlySupportedToZeroAtInfty f.toReal with hF
    have hFapp : ∀ y, F y = (f y : ℝ) := by
      intro y
      rw [hF, compactlySupportedToZeroAtInfty_apply,
        CompactlySupportedContinuousMap.toReal_apply]
    have hF0 : ∀ y, 0 ≤ F y := fun y ↦ by rw [hFapp y]; exact (f y).coe_nonneg
    have hFmeas : Measurable fun y ↦ ENNReal.ofReal (F y) :=
      ENNReal.measurable_ofReal.comp F.continuous.measurable
    have hkey : ∫⁻ y, ENNReal.ofReal (F y) ∂nu.comap i = ∫⁻ y, ENNReal.ofReal (F y) ∂mu := by
      rw [← lintegral_extend_eq_lintegral_comap hi nu hFmeas]
      exact hc0 F hF0
    have h1 : ENNReal.ofReal (∫ y, F y ∂nu.comap i) =
        ∫⁻ y, ENNReal.ofReal (F y) ∂nu.comap i :=
      ofReal_integral_eq_lintegral_ofReal (F.toBCF.integrable (nu.comap i))
        (Eventually.of_forall hF0)
    have h2 : ENNReal.ofReal (∫ y, F y ∂mu) = ∫⁻ y, ENNReal.ofReal (F y) ∂mu :=
      ofReal_integral_eq_lintegral_ofReal (F.toBCF.integrable mu) (Eventually.of_forall hF0)
    have hreal : ENNReal.ofReal (∫ y, F y ∂nu.comap i) = ENNReal.ofReal (∫ y, F y ∂mu) := by
      rw [h1, hkey, ← h2]
    have hbochner : ∫ y, F y ∂nu.comap i = ∫ y, F y ∂mu :=
      (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hF0) (integral_nonneg hF0)).mp hreal
    simpa only [hFapp] using hbochner
  rw [lintegral_extend_eq_lintegral_comap hi nu hg, hpull]

end Transfer

end MarkovProcess

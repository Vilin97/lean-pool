/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Continuity.PathTightness
public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.PathModulus


/-!
# Tightness of the path laws of a continuous-path Markov process

The modulus estimate of `Trajectory/PathModulus.lean` is uniform in the starting point, and the
process starts where it is told, so the laws `continuousProcess P hP x` for `x` in a compact set
of starting points satisfy both hypotheses of the Arzelà--Ascoli tightness criterion of
`Continuity/PathTightness.lean`.  This file records the resulting tightness statement.

Tightness is asserted for the starting points ranging over a *compact* set.  Over all starting
points at once it is false in general already at time zero: the time-zero laws are the Dirac
measures `delta_x`, and `{delta_x : x ∈ alpha}` is tight exactly when `alpha` is compact.  A
    compact set of starting points is also all that weak continuity in the
starting point needs, since continuity at a point only sees a neighbourhood of it.

The state space is assumed *proper* (closed balls are compact).  This is what discharges the
compact containment condition: the modulus confines a path to a bounded neighbourhood of its
starting point, and over a proper space bounded closed sets are compact.  On a general complete
separable metric state space the compact containment condition has to be supplied separately;
`ContinuousPath.isCompact_moduliSet_of_forall_isCompact` is the interface for that.

Main results:

* `IsConservative.measure_eval_zero_notMem_eq_zero`, the process starts where it is told;
* `IsConservative.isTightMeasureSet_continuousProcess`, tightness of the path laws over a compact
  set of starting points;
* `IsConservative.exists_isCompact_measure_compl_le`, the same in epsilon form.

No compactness theorem for measures (Prokhorov's theorem) is proved or used, and no weak
convergence statement is made here.
-/

@[expose] public section

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- The process starts where it is told: from a starting point of a measurable set `A`, almost
every path has its time-zero value in `A`. -/
theorem IsConservative.measure_eval_zero_notMem_eq_zero (hK : P.KolmogorovRegular hP)
    {A : Set alpha} (hA : MeasurableSet A) {x : alpha} (hx : x ∈ A) :
    continuousProcess P hP x {omega : ContinuousPath alpha | omega 0 ∉ A} = 0 := by
  have hmeas : Measurable fun omega : ContinuousPath alpha ↦ omega (0 : ℝ≥0) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) 0
  have hval : (((continuousProcess P hP) x).map fun omega ↦ omega (0 : ℝ≥0)) Aᶜ = 0 := by
    rw [← Kernel.map_apply _ hmeas, IsConservative.continuousProcess_map_eval_zero P hP hK,
      Kernel.id_apply]
    rw [Measure.dirac_apply' _ hA.compl, Set.indicator_of_notMem (by simpa using hx)]
  rwa [Measure.map_apply hmeas hA.compl, Set.preimage_compl] at hval

variable [ProperSpace alpha]

/-- **Tightness of the path laws over a compact set of starting points.**  For a conservative
semigroup on a proper metric state space satisfying the intrinsic Kolmogorov moment criterion, the
family `{continuousProcess P hP x : x ∈ K0}` of laws on continuous-path space is tight whenever
`K0` is compact.

The two inputs are the modulus estimate `exists_measure_compl_modulusSet_le`, whose scale does not
depend on the starting point, and the fact that the process starts in `K0`. -/
theorem IsConservative.isTightMeasureSet_continuousProcess {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) {K0 : Set alpha} (hK0 : IsCompact K0) :
    IsTightMeasureSet ((fun x ↦ continuousProcess P hP x) '' K0) := by
  refine ContinuousPath.isTightMeasureSet_of_measure_compl_modulusSet_le hK0 ?_ ?_
  · rintro mu ⟨x, hx, rfl⟩
    exact IsConservative.measure_eval_zero_notMem_eq_zero P hP
      (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) hK0.isClosed.measurableSet hx
  · intro T r hr eps heps
    obtain ⟨delta, hdelta, hbound⟩ :=
      IsConservative.exists_measure_compl_modulusSet_le P hP hmom T hr heps
    refine ⟨delta, hdelta, ?_⟩
    rintro mu ⟨x, hx, rfl⟩
    exact hbound x

/-- Epsilon form of tightness: one compact set of paths carries all but `eps` of the mass from
every starting point of a compact set. -/
theorem IsConservative.exists_isCompact_measure_compl_le {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) {K0 : Set alpha} (hK0 : IsCompact K0) {eps : ℝ≥0∞}
    (heps : 0 < eps) :
    ∃ K : Set (ContinuousPath alpha), IsCompact K ∧
      ∀ x ∈ K0, continuousProcess P hP x Kᶜ ≤ eps := by
  obtain ⟨K, hKcompact, hKmass⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      (IsConservative.isTightMeasureSet_continuousProcess P hP hmom hK0) eps heps
  exact ⟨K, hKcompact, fun x hx ↦ hKmass _ ⟨x, hx, rfl⟩⟩

end

end SubMarkovKernelSemigroup

end MarkovProcess

end PortComputability

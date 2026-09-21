/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.CylinderAlgebra
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.PathTightness
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.StartingPointContinuity
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Weak continuity of the path law in the starting point

`Trajectory/StartingPointContinuity.lean` proves that cylinder expectations of the
continuous-path process depend continuously on the starting point.  This file upgrades that to
*every* bounded continuous functional of the path, which is weak continuity of the path law
itself.

The route needs no compactness theorem for measures.  Fix a starting point `x0` and a compact
neighbourhood `K0` of it.  Tightness (`Trajectory/PathTightness.lean`) produces one compact set of
paths carrying all but `eta` of the mass from every starting point of `K0`.  On that compact set
Stone--Weierstrass replaces the given functional by a bounded cylinder functional, with a norm
bound that makes the discarded mass cheap (`Trajectory/CylinderAlgebra.lean`), and the cylinder
functional is already known to have continuous expectations.  Three epsilons and a triangle
inequality finish the argument.

Main results:

* `IsFellerKernelSemigroup.continuous_integral_boundedCylinder`, continuity for cylinder
  functionals;
* `IsFellerKernelSemigroup.continuous_integral_continuousProcess`, continuity for every bounded
  continuous functional of the path;
* `IsConservative.pathLaw` and `IsFellerKernelSemigroup.continuous_pathLaw`, the same statement
  read as continuity into the space of probability measures on path space with its topology of
  convergence in distribution.

Nothing here asserts relative compactness of a family of laws, and no convergence of a sequence
of semigroups is treated.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BoundedContinuousFunction ENNReal NNReal

namespace MarkovProcess

section TruncationError

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Two bounded continuous functionals that agree to within `eps` on a measurable set have
integrals that agree to within `eps` plus the mass off that set times the sum of the norms. -/
theorem abs_integral_sub_le_of_approx_on (mu : Measure X) [IsProbabilityMeasure mu]
    (F G : X →ᵇ ℝ) {K : Set X} (hK : MeasurableSet K) {eps : ℝ} (heps : 0 ≤ eps)
    (happrox : ∀ x ∈ K, |G x - F x| ≤ eps) :
    |(∫ x, F x ∂mu) - ∫ x, G x ∂mu| ≤ eps + (‖F‖ + ‖G‖) * mu.real Kᶜ := by
  have hF : Integrable (fun x ↦ F x) mu := F.integrable mu
  have hG : Integrable (fun x ↦ G x) mu := G.integrable mu
  have hKc : MeasurableSet Kᶜ := hK.compl
  have hind : Integrable (Set.indicator Kᶜ (1 : X → ℝ)) mu :=
    (integrable_const (1 : ℝ)).indicator hKc
  have hbound : ∀ x, ‖F x - G x‖ ≤
      eps + (‖F‖ + ‖G‖) * Set.indicator Kᶜ (1 : X → ℝ) x := by
    intro x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_notMem (by simpa using hx), mul_zero, add_zero, Real.norm_eq_abs,
        abs_sub_comm]
      exact happrox x hx
    · rw [Set.indicator_of_mem (by simpa using hx), Pi.one_apply, mul_one]
      have h1 : ‖F x - G x‖ ≤ ‖F x‖ + ‖G x‖ := norm_sub_le _ _
      have h2 : ‖F x‖ ≤ ‖F‖ := F.norm_coe_le_norm x
      have h3 : ‖G x‖ ≤ ‖G‖ := G.norm_coe_le_norm x
      linarith
  have hmaj : Integrable
      (fun x ↦ eps + (‖F‖ + ‖G‖) * Set.indicator Kᶜ (1 : X → ℝ) x) mu :=
    (integrable_const eps).add (hind.const_mul _)
  rw [← integral_sub hF hG, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hmaj (Eventually.of_forall hbound)).trans_eq ?_
  rw [integral_add (integrable_const eps) (hind.const_mul _), integral_const, integral_const_mul,
    integral_indicator_one hKc, probReal_univ, smul_eq_mul, one_mul]

end TruncationError

namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [ProperSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- Expectations of a bounded cylinder functional depend continuously on the starting point. -/
theorem IsFellerKernelSemigroup.continuous_integral_boundedCylinder
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {G : ContinuousPath alpha → ℝ} (hG : ContinuousPath.IsBoundedCylinder G) :
    Continuous fun x ↦ ∫ omega, G omega ∂(continuousProcess P hP x) := by
  obtain ⟨I, g, hg⟩ := hG
  simp only [hg]
  exact hFeller.continuous_integral_finsetEvaluation_continuousProcess P hP hK I g

/-- **Weak continuity of the path law in the starting point.**  For a conservative Feller
semigroup on a proper metric state space satisfying the intrinsic Kolmogorov moment criterion, the
expectation of *every* bounded continuous functional of the path is a continuous function of the
starting point.

This extends the cylinder-expectation continuity of
`continuous_integral_finsetEvaluation_continuousProcess` to all of path space.  The proof is the
direct one: tightness over a compact neighbourhood of the reference point produces a compact set
of paths carrying all but a prescribed mass, Stone--Weierstrass replaces the functional by a
bounded cylinder functional on that compact set, and the cylinder case is already known.  No
compactness theorem for measures is used. -/
theorem IsFellerKernelSemigroup.continuous_integral_continuousProcess
    (hFeller : P.IsFellerKernelSemigroup) {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) (F : ContinuousPath alpha →ᵇ ℝ) :
    Continuous fun x ↦ ∫ omega, F omega ∂(continuousProcess P hP x) := by
  have hKreg := KolmogorovRegular.of_hasKolmogorovMoments P hP hmom
  refine continuous_iff_continuousAt.mpr fun x0 ↦ Metric.tendsto_nhds.mpr fun eps heps ↦ ?_
  set eps5 : ℝ := eps / 5 with heps5def
  have heps5 : 0 < eps5 := by positivity
  set Ctot : ℝ := ‖F‖ + (‖F‖ + eps5) with hCtotdef
  have hCtotpos : 0 < Ctot := by
    rw [hCtotdef]
    have := norm_nonneg F
    linarith
  set eta : ℝ := eps5 / Ctot with hetadef
  have hetapos : 0 < eta := div_pos heps5 hCtotpos
  obtain ⟨K0, hK0compact, hK0nhds⟩ := exists_compact_mem_nhds x0
  obtain ⟨Kp, hKpcompact, hKpmass⟩ :=
    IsConservative.exists_isCompact_measure_compl_le P hP hmom hK0compact
      (eps := ENNReal.ofReal eta) (ENNReal.ofReal_pos.mpr hetapos)
  obtain ⟨G, hGcyl, hGnorm, hGapprox⟩ :=
    ContinuousPath.exists_boundedCylinder_approx F hKpcompact heps5
  have hKpmeas : MeasurableSet Kp := hKpcompact.isClosed.measurableSet
  have herror : ∀ x ∈ K0, |(∫ omega, F omega ∂(continuousProcess P hP x)) -
      ∫ omega, G omega ∂(continuousProcess P hP x)| ≤ 2 * eps5 := by
    intro x hx
    have hmass : (continuousProcess P hP x).real Kpᶜ ≤ eta := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal hetapos.le (hKpmass x hx)
    have hbase := abs_integral_sub_le_of_approx_on (continuousProcess P hP x) F G hKpmeas
      heps5.le hGapprox
    have hFG : ‖F‖ + ‖G‖ ≤ Ctot := by
      rw [hCtotdef]
      linarith [hGnorm]
    have hprod : (‖F‖ + ‖G‖) * (continuousProcess P hP x).real Kpᶜ ≤ eps5 := by
      calc (‖F‖ + ‖G‖) * (continuousProcess P hP x).real Kpᶜ ≤ Ctot * eta :=
            mul_le_mul hFG hmass measureReal_nonneg hCtotpos.le
        _ = eps5 := by
            rw [hetadef]
            field_simp
    linarith [hbase, hprod]
  have hcylinder :=
    IsFellerKernelSemigroup.continuous_integral_boundedCylinder P hP hFeller hKreg hGcyl
  have hnear : ∀ᶠ x in nhds x0, |(∫ omega, G omega ∂(continuousProcess P hP x)) -
      ∫ omega, G omega ∂(continuousProcess P hP x0)| < eps5 := by
    have h := Metric.tendsto_nhds.mp (hcylinder.continuousAt (x := x0)) eps5 heps5
    simpa only [Real.dist_eq] using h
  filter_upwards [hnear, hK0nhds] with x hxnear hxK0
  rw [Real.dist_eq]
  have h1 := herror x hxK0
  have h2 := herror x0 (mem_of_mem_nhds hK0nhds)
  have h2' : |(∫ omega, G omega ∂(continuousProcess P hP x0)) -
      ∫ omega, F omega ∂(continuousProcess P hP x0)| ≤ 2 * eps5 := by
    rw [abs_sub_comm]
    exact h2
  have htri1 := abs_sub_le (∫ omega, F omega ∂(continuousProcess P hP x))
    (∫ omega, G omega ∂(continuousProcess P hP x))
    (∫ omega, F omega ∂(continuousProcess P hP x0))
  have htri2 := abs_sub_le (∫ omega, G omega ∂(continuousProcess P hP x))
    (∫ omega, G omega ∂(continuousProcess P hP x0))
    (∫ omega, F omega ∂(continuousProcess P hP x0))
  rw [heps5def] at h1 h2' hxnear
  linarith [htri1, htri2, h1, h2', hxnear]

/-- The law of the continuous-path process, read as a probability measure on path space. -/
def IsConservative.pathLaw (x : alpha) : ProbabilityMeasure (ContinuousPath alpha) :=
  ⟨continuousProcess P hP x, inferInstance⟩

omit [ProperSpace alpha] in
@[simp]
theorem IsConservative.pathLaw_toMeasure (x : alpha) :
    ((IsConservative.pathLaw P hP x : ProbabilityMeasure (ContinuousPath alpha)) :
        Measure (ContinuousPath alpha)) = continuousProcess P hP x :=
  rfl

/-- **The path law is weakly continuous in the starting point.**  Read on the space of
probability measures on path space with its topology of convergence in distribution, the map
`x ↦ pathLaw P hP x` is continuous. -/
theorem IsFellerKernelSemigroup.continuous_pathLaw
    (hFeller : P.IsFellerKernelSemigroup) {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) :
    Continuous (IsConservative.pathLaw P hP) := by
  refine ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr fun F ↦ ?_
  exact IsFellerKernelSemigroup.continuous_integral_continuousProcess P hP hFeller hmom F

end

end SubMarkovKernelSemigroup

end MarkovProcess

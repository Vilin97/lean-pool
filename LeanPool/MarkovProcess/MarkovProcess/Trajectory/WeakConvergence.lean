/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Semigroup.TrotterKato
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.Convergence
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.WeakContinuity

/-!
# Weak convergence of Feller processes on path space

`Trajectory/Convergence.lean` proves that strong convergence of the `C₀` semigroups makes the
finite-dimensional distributions of the continuous-path processes converge.  This file upgrades
that to convergence of the whole path laws, provided the approximating semigroups and the limit
semigroup satisfy **one common** intrinsic Kolmogorov moment bound `HasKolmogorovMoments p q M`.

The common moment bound is what makes the family of path laws at a fixed starting point tight:
the scale in the modulus estimate of `Continuity/PathModulus.lean` depends only on the exponents,
the constant and the tolerances, never on the semigroup, so one compact set of paths carries all
but a prescribed mass of every law of the family at once.  On that compact set Stone--Weierstrass
replaces a bounded continuous functional of the path by a bounded cylinder functional
(`Trajectory/CylinderAlgebra.lean`), whose expectations converge by the finite-dimensional
theorem.  Three epsilons finish the argument; no compactness theorem for measures is used.

Main results:

* `isTightMeasureSet_insert_continuousProcess` and
  `exists_isCompact_measure_compl_le_insert`, tightness of the family of path laws at a fixed
  starting point;
* `tendsto_integral_continuousProcess`, convergence of the expectation of every bounded
  continuous functional of the path;
* `tendsto_pathLaw`, the same statement read in the space of probability measures on path space
  with its topology of convergence in distribution, and
  `tendsto_pathLaw_of_tendsto_resolvent`, its form starting from the resolvents.

The state space is assumed proper, as in `Trajectory/PathTightness.lean`, and the moment bound is
assumed with the same exponents and constant for every member of the family; nothing is asserted
when the constants are allowed to vary, nor for a family whose limit is not itself the process of
a Feller semigroup.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BoundedContinuousFunction ENNReal NNReal ZeroAtInfty

namespace MarkovProcess


namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [ProperSpace alpha]
variable {iota : Type*} {l : Filter iota}
variable {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}

/-- **Tightness of the path laws of a family of semigroups at a fixed starting point.**  One
common intrinsic Kolmogorov moment bound gives one modulus of continuity for the whole family, so
the family of path laws from a fixed starting point, together with the law of the limit
semigroup, is tight on path space. -/
theorem isTightMeasureSet_insert_continuousProcess
    (hPc : ∀ i, (P i).IsConservative) (hQc : Q.IsConservative) {p q : ℝ} {M : ℝ≥0}
    (hPmom : ∀ i, (P i).HasKolmogorovMoments p q M) (hQmom : Q.HasKolmogorovMoments p q M)
    (x : alpha) :
    IsTightMeasureSet (insert (continuousProcess Q hQc x)
      (Set.range fun i ↦ continuousProcess (P i) (hPc i) x)) := by
  refine ContinuousPath.isTightMeasureSet_of_measure_compl_modulusSet_le
    (isCompact_singleton (x := x)) ?_ ?_
  · rintro mu (rfl | ⟨i, rfl⟩)
    · exact IsConservative.measure_eval_zero_notMem_eq_zero Q hQc
        (KolmogorovRegular.of_hasKolmogorovMoments Q hQc hQmom)
        (measurableSet_singleton x) rfl
    · exact IsConservative.measure_eval_zero_notMem_eq_zero (P i) (hPc i)
        (KolmogorovRegular.of_hasKolmogorovMoments (P i) (hPc i) (hPmom i))
        (measurableSet_singleton x) rfl
  · intro T r hr eps heps
    obtain ⟨gamma, hgamma, hgammaq⟩ := hQmom.exists_holderExponent
    obtain ⟨delta, hdelta, hmu⟩ :=
      ContinuousPath.exists_measure_compl_modulusSet_le (alpha := alpha) (M := M)
        hQmom.p_pos hgamma hgammaq T hr heps
    refine ⟨delta, hdelta, ?_⟩
    rintro mu (rfl | ⟨i, rfl⟩)
    · exact hmu _ (IsConservative.isKolmogorovProcess_continuousProcess Q hQc hQmom
        (KolmogorovRegular.of_hasKolmogorovMoments Q hQc hQmom) x)
    · exact hmu _ (IsConservative.isKolmogorovProcess_continuousProcess (P i) (hPc i) (hPmom i)
        (KolmogorovRegular.of_hasKolmogorovMoments (P i) (hPc i) (hPmom i)) x)

/-- Epsilon form of tightness: one compact set of paths carries all but `eps` of every law of the
family and of the law of the limit semigroup. -/
theorem exists_isCompact_measure_compl_le_insert
    (hPc : ∀ i, (P i).IsConservative) (hQc : Q.IsConservative) {p q : ℝ} {M : ℝ≥0}
    (hPmom : ∀ i, (P i).HasKolmogorovMoments p q M) (hQmom : Q.HasKolmogorovMoments p q M)
    (x : alpha) {eps : ℝ≥0∞} (heps : 0 < eps) :
    ∃ K : Set (ContinuousPath alpha), IsCompact K ∧
      (∀ i, continuousProcess (P i) (hPc i) x Kᶜ ≤ eps) ∧
        continuousProcess Q hQc x Kᶜ ≤ eps := by
  obtain ⟨K, hKcompact, hKmass⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      (isTightMeasureSet_insert_continuousProcess hPc hQc hPmom hQmom x) eps heps
  exact ⟨K, hKcompact, fun i ↦ hKmass _ (Set.mem_insert_of_mem _ ⟨i, rfl⟩),
    hKmass _ (Set.mem_insert _ _)⟩

/-- **Weak convergence of Feller processes on path space.**  Let `P i` be conservative Feller
kernel semigroups with one common intrinsic Kolmogorov moment bound, and let `Q` be one more such
semigroup.  If the `C₀` semigroups converge strongly, then from every starting point the
expectation of every bounded continuous functional of the path converges.

The proof combines the tightness of the family at that starting point with the cylinder
approximation on a compact set of paths and the convergence of the finite-dimensional
distributions; no compactness theorem for measures is used. -/
theorem tendsto_integral_continuousProcess
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hPc : ∀ i, (P i).IsConservative)
    (hQ : Q.IsFellerKernelSemigroup) (hQc : Q.IsConservative) {p q : ℝ} {M : ℝ≥0}
    (hPmom : ∀ i, (P i).HasKolmogorovMoments p q M) (hQmom : Q.HasKolmogorovMoments p q M)
    (hconv : ∀ (t : NNReal) (f : C₀(alpha, ℝ)),
      Tendsto (fun i ↦ (hP i).c0Semigroup t f) l (nhds (hQ.c0Semigroup t f)))
    (F : ContinuousPath alpha →ᵇ ℝ) (x : alpha) :
    Tendsto (fun i ↦ ∫ omega, F omega ∂(continuousProcess (P i) (hPc i) x)) l
      (nhds (∫ omega, F omega ∂(continuousProcess Q hQc x))) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  set eps5 : ℝ := eps / 5 with heps5def
  have heps5 : 0 < eps5 := by positivity
  set Ctot : ℝ := ‖F‖ + (‖F‖ + eps5) with hCtotdef
  have hCtotpos : 0 < Ctot := by
    rw [hCtotdef]
    have := norm_nonneg F
    linarith
  set eta : ℝ := eps5 / Ctot with hetadef
  have hetapos : 0 < eta := div_pos heps5 hCtotpos
  obtain ⟨Kp, hKpcompact, hKmassP, hKmassQ⟩ :=
    exists_isCompact_measure_compl_le_insert hPc hQc hPmom hQmom x
      (eps := ENNReal.ofReal eta) (ENNReal.ofReal_pos.mpr hetapos)
  obtain ⟨G, hGcyl, hGnorm, hGapprox⟩ :=
    ContinuousPath.exists_boundedCylinder_approx F hKpcompact heps5
  have hKpmeas : MeasurableSet Kp := hKpcompact.isClosed.measurableSet
  have herror : ∀ mu : Measure (ContinuousPath alpha), ∀ _ : IsProbabilityMeasure mu,
      mu Kpᶜ ≤ ENNReal.ofReal eta →
      |(∫ omega, F omega ∂mu) - ∫ omega, G omega ∂mu| ≤ 2 * eps5 := by
    intro mu hmuprob hmass
    have hmassreal : mu.real Kpᶜ ≤ eta := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal hetapos.le hmass
    have hbase := abs_integral_sub_le_of_approx_on mu F G hKpmeas heps5.le hGapprox
    have hFG : ‖F‖ + ‖G‖ ≤ Ctot := by
      rw [hCtotdef]
      linarith [hGnorm]
    have hprod : (‖F‖ + ‖G‖) * mu.real Kpᶜ ≤ eps5 := by
      calc (‖F‖ + ‖G‖) * mu.real Kpᶜ ≤ Ctot * eta :=
            mul_le_mul hFG hmassreal measureReal_nonneg hCtotpos.le
        _ = eps5 := by
            rw [hetadef]
            field_simp
    linarith [hbase, hprod]
  obtain ⟨I, g, hg⟩ := hGcyl
  have hcyl : Tendsto (fun i ↦ ∫ omega, G omega ∂(continuousProcess (P i) (hPc i) x)) l
      (nhds (∫ omega, G omega ∂(continuousProcess Q hQc x))) := by
    simp only [hg]
    exact tendsto_integral_finsetEvaluation_continuousProcess hP hPc
      (fun i ↦ KolmogorovRegular.of_hasKolmogorovMoments (P i) (hPc i) (hPmom i)) hQ hQc
      (KolmogorovRegular.of_hasKolmogorovMoments Q hQc hQmom) hconv I g x
  have hnear : ∀ᶠ i in l, |(∫ omega, G omega ∂(continuousProcess (P i) (hPc i) x)) -
      ∫ omega, G omega ∂(continuousProcess Q hQc x)| < eps5 := by
    have h := Metric.tendsto_nhds.mp hcyl eps5 heps5
    simpa only [Real.dist_eq] using h
  filter_upwards [hnear] with i hinear
  rw [Real.dist_eq]
  have h1 := herror (continuousProcess (P i) (hPc i) x) inferInstance (hKmassP i)
  have h2 := herror (continuousProcess Q hQc x) inferInstance hKmassQ
  have h2' : |(∫ omega, G omega ∂(continuousProcess Q hQc x)) -
      ∫ omega, F omega ∂(continuousProcess Q hQc x)| ≤ 2 * eps5 := by
    rw [abs_sub_comm]
    exact h2
  have htri1 := abs_sub_le (∫ omega, F omega ∂(continuousProcess (P i) (hPc i) x))
    (∫ omega, G omega ∂(continuousProcess (P i) (hPc i) x))
    (∫ omega, F omega ∂(continuousProcess Q hQc x))
  have htri2 := abs_sub_le (∫ omega, G omega ∂(continuousProcess (P i) (hPc i) x))
    (∫ omega, G omega ∂(continuousProcess Q hQc x))
    (∫ omega, F omega ∂(continuousProcess Q hQc x))
  rw [heps5def] at h1 h2' hinear
  linarith [htri1, htri2, h1, h2', hinear]

/-- **The path laws converge in distribution.**  Read in the space of probability measures on path
space with its topology of convergence in distribution, the laws of the approximating processes
converge to the law of the limit process, from every starting point. -/
theorem tendsto_pathLaw
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hPc : ∀ i, (P i).IsConservative)
    (hQ : Q.IsFellerKernelSemigroup) (hQc : Q.IsConservative) {p q : ℝ} {M : ℝ≥0}
    (hPmom : ∀ i, (P i).HasKolmogorovMoments p q M) (hQmom : Q.HasKolmogorovMoments p q M)
    (hconv : ∀ (t : NNReal) (f : C₀(alpha, ℝ)),
      Tendsto (fun i ↦ (hP i).c0Semigroup t f) l (nhds (hQ.c0Semigroup t f)))
    (x : alpha) :
    Tendsto (fun i ↦ IsConservative.pathLaw (P i) (hPc i) x) l
      (nhds (IsConservative.pathLaw Q hQc x)) := by
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr fun F ↦ ?_
  simpa only [IsConservative.pathLaw_toMeasure] using
    tendsto_integral_continuousProcess hP hPc hQ hQc hPmom hQmom hconv F x

/-- **Weak convergence on path space from convergence of the resolvents.**  Combining the
Trotter--Kato theorem with the previous statement: strong convergence of the `C₀` resolvents at
one positive shift already forces the path laws to converge in distribution. -/
theorem tendsto_pathLaw_of_tendsto_resolvent
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hPc : ∀ i, (P i).IsConservative)
    (hQ : Q.IsFellerKernelSemigroup) (hQc : Q.IsConservative) {p q : ℝ} {M : ℝ≥0}
    (hPmom : ∀ i, (P i).HasKolmogorovMoments p q M) (hQmom : Q.HasKolmogorovMoments p q M)
    {mu : Semigroup.PositiveShift}
    (hres : ∀ f : C₀(alpha, ℝ), Tendsto (fun i ↦ (hP i).c0Semigroup.resolvent mu f) l
      (nhds (hQ.c0Semigroup.resolvent mu f))) (x : alpha) :
    Tendsto (fun i ↦ IsConservative.pathLaw (P i) (hPc i) x) l
      (nhds (IsConservative.pathLaw Q hQc x)) := by
  refine tendsto_pathLaw hP hPc hQ hQc hPmom hQmom (fun t f ↦ ?_) x
  exact Semigroup.StronglyContinuousContractionSemigroup.tendsto_operator_of_tendsto_resolvent
    hres f t

end

end SubMarkovKernelSemigroup

end MarkovProcess

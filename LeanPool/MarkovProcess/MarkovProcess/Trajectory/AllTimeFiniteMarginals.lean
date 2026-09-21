/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.AllTimeMarginals
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.FiniteMarginals

/-!
# Arbitrary-time finite marginals of continuous-path trajectories

This file develops the simultaneous rational approximation needed to pass from the already
identified rational finite-dimensional distributions to finite families of arbitrary
nonnegative real times.  It proves the path-side dominated-convergence argument, identifies every
rational approximating law with the existing finite-set kernel, and reduces the desired equality
to compactly-supported-test convergence of those finite-set kernels.

The remaining Feller analytic statement is not claimed here: one must still prove that the
recursively composed finite-time kernels have that convergence under simultaneous convergence of
their strictly ordered time coordinates.  No continuous-time Markov or Hunt property is assumed
or asserted.
-/

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal

namespace MarkovProcess

section

/-- Every finite linearly ordered family embedded in nonnegative real time admits strictly
ordered rational approximations converging coordinatewise.  A common tail shift makes the
independently chosen approximations preserve all finitely many strict inequalities at every
level. -/
theorem exists_denseTime_finiteOrderEmbedding_seq_tendsto
    {ι : Type*} [Finite ι] [LinearOrder ι] (times : ι ↪o NNReal) :
    ∃ q : ℕ → ι ↪o DenseTime,
      ∀ i, Tendsto (fun k ↦ DenseTime.castOrderEmbedding (q k i))
        atTop (nhds (times i)) := by
  choose q hq using fun i : ι ↦ exists_denseTime_seq_tendsto (times i)
  have hordered : ∀ᶠ k in atTop,
      ∀ i j : ι, i < j →
        DenseTime.castOrderEmbedding (q i k) <
          DenseTime.castOrderEmbedding (q j k) := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    by_cases hij : i < j
    · exact ((hq i).eventually_lt (hq j) (times.strictMono hij)).mono
        fun k hk _ ↦ hk
    · exact Filter.Eventually.of_forall fun _ hij' ↦ (hij hij').elim
  rw [Filter.eventually_atTop] at hordered
  obtain ⟨N, hN⟩ := hordered
  let qOrdered : ℕ → ι ↪o DenseTime := fun k ↦
    OrderEmbedding.ofStrictMono (fun i ↦ q i (k + N)) fun i j hij ↦ by
      apply DenseTime.castOrderEmbedding.lt_iff_lt.mp
      exact hN (k + N) (Nat.le_add_left N k) i j hij
  refine ⟨qOrdered, fun i ↦ ?_⟩
  have hshift := (hq i).comp (Filter.tendsto_add_atTop_nat N)
  simpa only [qOrdered, Function.comp_apply] using! hshift

/-- Every finite strictly ordered family of nonnegative real times admits strictly ordered
rational approximations converging coordinatewise. -/
theorem exists_denseTime_finiteOrdered_seq_tendsto {n : ℕ}
    (times : FiniteOrderedTimes n) :
    ∃ q : ℕ → Fin n ↪o DenseTime,
      ∀ i, Tendsto (fun k ↦ DenseTime.castOrderEmbedding (q k i))
        atTop (nhds (times i)) :=
  exists_denseTime_finiteOrderEmbedding_seq_tendsto times

/-- Every finite set of nonnegative real times has a simultaneous strictly ordered rational
approximation on its fixed subtype of coordinates. -/
theorem exists_denseTime_finset_seq_tendsto (I : Finset NNReal) :
    ∃ q : ℕ → I ↪o DenseTime,
      ∀ t, Tendsto (fun k ↦ DenseTime.castOrderEmbedding (q k t))
        atTop (nhds (t : NNReal)) := by
  simpa only using! exists_denseTime_finiteOrderEmbedding_seq_tendsto
    (OrderEmbedding.subtype (fun t : NNReal ↦ t ∈ I))

namespace ContinuousPath

/-- Evaluate a continuous path at a finite family of times. -/
def finiteEvaluation {ι α : Type*} [TopologicalSpace α]
    (τ : ι → NNReal) : ContinuousPath α → (ι → α) :=
  fun path i ↦ path (τ i)

/-- Simultaneous evaluation at finitely many fixed times is continuous in the path. -/
theorem continuous_finiteEvaluation {ι α : Type*} [TopologicalSpace α] (τ : ι → NNReal) :
    Continuous (finiteEvaluation (α := α) τ) := by
  apply continuous_pi
  intro i
  exact continuous_eval (alpha := α) (τ i)

/-- If each time in a finite family converges, then simultaneous evaluation along any
continuous path converges in the finite product topology. -/
theorem tendsto_finiteEvaluation {ι α : Type*} [TopologicalSpace α]
    (τ : ι → NNReal) (q : ℕ → ι → NNReal)
    (hq : ∀ i, Tendsto (fun k ↦ q k i) atTop (nhds (τ i)))
    (path : ContinuousPath α) :
    Tendsto (fun k ↦ finiteEvaluation (α := α) (q k) path) atTop
      (nhds (finiteEvaluation (α := α) τ path)) := by
  apply tendsto_pi_nhds.2
  intro i
  exact Filter.Tendsto.comp path.continuous.continuousAt (hq i)

end ContinuousPath

section KernelLimits

variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] [LocallyCompactSpace α]

omit [SecondCountableTopology α] [LocallyCompactSpace α] in
/-- Simultaneous evaluation at finitely many fixed times is Borel measurable. -/
theorem ContinuousPath.measurable_finiteEvaluation {ι : Type*} (τ : ι → NNReal) :
    Measurable (finiteEvaluation (α := α) τ) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_coordinateProcess (alpha := α) (τ i)

omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α]
  [LocallyCompactSpace α] in
/-- Dominated convergence for a compactly supported test function evaluated at a convergent
finite family of times along a continuous-path probability kernel.  This is the path-side limit
needed in every finite-dimensional rational approximation argument. -/
theorem tendsto_integral_continuousPath_finiteEvaluation
    {β ι : Type*} [MeasurableSpace β] (K : Kernel β (ContinuousPath α)) (hK : IsMarkovKernel K)
    (x : β) (f : CompactlySupportedContinuousMap (ι → α) ℝ)
    (τ : ι → NNReal)
    (q : ℕ → ι → NNReal)
    (hq : ∀ i, Tendsto (fun k ↦ q k i) atTop (nhds (τ i))) :
    Tendsto
      (fun k ↦ ∫ path, f (ContinuousPath.finiteEvaluation (α := α) (q k) path) ∂K x)
      atTop
      (nhds (∫ path, f (ContinuousPath.finiteEvaluation (α := α) τ path) ∂K x)) := by
  let : IsMarkovKernel K := hK
  let f0 : ZeroAtInftyContinuousMap (ι → α) ℝ :=
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards [] with k
    exact (f.continuous.comp
      (ContinuousPath.continuous_finiteEvaluation (q k))).aestronglyMeasurable
  · refine ⟨‖f0‖, Filter.Eventually.of_forall fun k ↦ ?_⟩
    filter_upwards [] with path
    simpa only [f0, PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply,
      Real.norm_eq_abs] using! f0.toBCF.norm_coe_le_norm
      (ContinuousPath.finiteEvaluation (α := α) (q k) path)
  · filter_upwards [] with path
    exact Filter.Tendsto.comp f.continuous.continuousAt
      (ContinuousPath.tendsto_finiteEvaluation τ q hq path)

/-- Equality of finite-dimensional laws passes from approximating time families to their limit
once the comparison kernels have the corresponding compactly-supported-test convergence.

The convergence premise is deliberately stated at precisely the analytic seam: it says nothing
about a Markov property and is exactly the weak/vague continuity of the candidate finite-time
laws needed by the proof. -/
theorem Kernel.map_finiteEvaluation_eq_of_integral_tendsto
    {β ι : Type*} [MeasurableSpace β] [Finite ι]
    (K : Kernel β (ContinuousPath α)) (hK : IsMarkovKernel K)
    (Lseq : ℕ → Kernel β (ι → α)) (L : Kernel β (ι → α))
    (hL : IsMarkovKernel L) (τ : ι → NNReal) (q : ℕ → ι → NNReal)
    (hq : ∀ i, Tendsto (fun k ↦ q k i) atTop (nhds (τ i)))
    (hlaw : ∀ k, K.map (ContinuousPath.finiteEvaluation (q k)) = Lseq k)
    (hfinite : ∀ (x : β) (f : CompactlySupportedContinuousMap (ι → α) ℝ),
      Tendsto (fun k ↦ ∫ y, f y ∂Lseq k x) atTop (nhds (∫ y, f y ∂L x))) :
    K.map (ContinuousPath.finiteEvaluation τ) = L := by
  classical
  let := Fintype.ofFinite ι
  let : IsMarkovKernel K := hK
  let : IsMarkovKernel L := hL
  apply Kernel.ext
  intro x
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hpath := tendsto_integral_continuousPath_finiteEvaluation
    K hK x f τ q hq
  have heq : ∀ k,
      (∫ path, f (ContinuousPath.finiteEvaluation (q k) path) ∂K x) =
        ∫ y, f y ∂Lseq k x := by
    intro k
    have hm := congrArg (fun κ : Kernel β (ι → α) ↦ κ x) (hlaw k)
    have hi := congrArg (fun μ : Measure (ι → α) ↦ ∫ y, f y ∂μ) hm
    change (∫ y, f y ∂(K.map (ContinuousPath.finiteEvaluation (q k))) x) =
      ∫ y, f y ∂Lseq k x at hi
    have heval : Measurable (ContinuousPath.finiteEvaluation (α := α) (q k)) :=
      ContinuousPath.measurable_finiteEvaluation (q k)
    have hmap :
        (K.map (ContinuousPath.finiteEvaluation (q k))) x =
          (K x).map (ContinuousPath.finiteEvaluation (q k)) :=
      Kernel.map_apply K heval x
    rw [hmap, integral_map] at hi
    · exact hi
    · exact heval.aemeasurable
    · exact f.continuous.aestronglyMeasurable
  have hsame :
      (fun k ↦ ∫ path, f (ContinuousPath.finiteEvaluation (q k) path) ∂K x) =
        fun k ↦ ∫ y, f y ∂Lseq k x :=
    funext heq
  rw [hsame] at hpath
  have hlimit := tendsto_nhds_unique hpath (hfinite x f)
  have heval : Measurable (ContinuousPath.finiteEvaluation (α := α) τ) :=
    ContinuousPath.measurable_finiteEvaluation τ
  have hmap :
      (K.map (ContinuousPath.finiteEvaluation τ)) x =
        (K x).map (ContinuousPath.finiteEvaluation τ) :=
    Kernel.map_apply K heval x
  rw [hmap, integral_map]
  · exact hlimit
  · exact heval.aemeasurable
  · exact f.continuous.aestronglyMeasurable

namespace SubMarkovKernelSemigroup

/-- The rational index set used by one finite ordered rational approximation. -/
def finiteDenseApproximationIndexSet {I : Finset NNReal} (q : I ↪o DenseTime) :
    Finset DenseTime :=
  Finset.univ.map q.toEmbedding

/-- The corresponding finite set of physical nonnegative-real times. -/
def finiteDenseApproximationPhysicalSet {I : Finset NNReal} (q : I ↪o DenseTime) :
    Finset NNReal :=
  denseTimePhysicalSet (finiteDenseApproximationIndexSet q)

private theorem finiteDenseApproximation_mem {I : Finset NNReal} (q : I ↪o DenseTime)
    (t : I) :
    DenseTime.castOrderEmbedding (q t) ∈ finiteDenseApproximationPhysicalSet q := by
  rw [finiteDenseApproximationPhysicalSet, denseTimePhysicalSet, Finset.mem_map]
  refine ⟨q t, ?_, rfl⟩
  rw [finiteDenseApproximationIndexSet, Finset.mem_map]
  exact ⟨t, Finset.mem_univ t, rfl⟩

/-- Reindex a path on an approximating physical-time set by the original finite set. -/
def finiteDenseApproximationReindex {γ : Type*} {I : Finset NNReal}
    (q : I ↪o DenseTime) :
    (finiteDenseApproximationPhysicalSet q → γ) → I → γ :=
  fun path t ↦ path ⟨DenseTime.castOrderEmbedding (q t),
    finiteDenseApproximation_mem q t⟩

/-- The approximating-set reindexing map is measurable. -/
theorem measurable_finiteDenseApproximationReindex
    {γ : Type*} [MeasurableSpace γ] {I : Finset NNReal} (q : I ↪o DenseTime) :
    Measurable (finiteDenseApproximationReindex (γ := γ) q) := by
  rw [measurable_pi_iff]
  intro t
  let s : finiteDenseApproximationPhysicalSet q :=
    ⟨DenseTime.castOrderEmbedding (q t), finiteDenseApproximation_mem q t⟩
  exact measurable_pi_apply s

/-- The candidate finite law at one rational approximation, transported back to the fixed
coordinate type indexed by the original time set. -/
noncomputable def finiteDenseApproximationKernel
    (P : SubMarkovKernelSemigroup α) {I : Finset NNReal} (q : I ↪o DenseTime) :
    Kernel α (I → α) :=
  (finiteSetKernel P (finiteDenseApproximationPhysicalSet q)).map
    (finiteDenseApproximationReindex q)

namespace IsConservative

variable [CompleteSpace α] [StandardBorelSpace α] [Nonempty α]

omit [LocallyCompactSpace α] in
/-- At every finite ordered rational approximation, the continuous-path trajectory has exactly
the transported finite-set kernel law on the fixed original coordinate type. -/
theorem continuousPathTrajectory_map_finiteDenseApproximation
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (default : ContinuousPath α)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    {I : Finset NNReal} (q : I ↪o DenseTime) :
    (continuousPathTrajectory P hP default).map
        (ContinuousPath.finiteEvaluation
          (fun t : I ↦ DenseTime.castOrderEmbedding (q t))) =
      finiteDenseApproximationKernel P q := by
  let evalPhysical : ContinuousPath α →
      (finiteDenseApproximationPhysicalSet q → α) :=
    fun path t ↦ path t
  have hevalPhysical : Measurable evalPhysical := by
    rw [measurable_pi_iff]
    intro t
    exact ContinuousPath.measurable_coordinateProcess (alpha := α) t
  have hcomp :
      finiteDenseApproximationReindex (γ := α) q ∘ evalPhysical =
        ContinuousPath.finiteEvaluation
          (fun t : I ↦ DenseTime.castOrderEmbedding (q t)) := by
    rfl
  rw [← hcomp, Kernel.map_comp_right]
  · have hrational := continuousPathTrajectory_map_finiteDenseTimeSet
      P hP default hK (finiteDenseApproximationIndexSet q)
    change (continuousPathTrajectory P hP default).map evalPhysical =
      finiteSetKernel P (finiteDenseApproximationPhysicalSet q) at hrational
    rw [hrational]
    rfl
  · exact hevalPhysical
  · exact measurable_finiteDenseApproximationReindex q

/-- The arbitrary-time finite-marginal theorem reduced to convergence of the already constructed
finite-set kernels along one simultaneous rational approximation.  The remaining premise is an
analytic continuity statement about the Feller finite-time kernels, not a pathwise or Markov
assumption. -/
theorem continuousPathTrajectory_map_finiteTimeSet_of_integral_tendsto
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (default : ContinuousPath α)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (I : Finset NNReal) (q : ℕ → I ↪o DenseTime)
    (hq : ∀ t, Tendsto
      (fun k ↦ DenseTime.castOrderEmbedding (q k t)) atTop (nhds (t : NNReal)))
    (hfinite : ∀ (x : α) (f : CompactlySupportedContinuousMap (I → α) ℝ),
      Tendsto
        (fun k ↦ ∫ y, f y ∂finiteDenseApproximationKernel P (q k) x)
        atTop (nhds (∫ y, f y ∂finiteSetKernel P I x))) :
    (continuousPathTrajectory P hP default).map
        (ContinuousPath.finiteEvaluation (fun t : I ↦ (t : NNReal))) =
      finiteSetKernel P I := by
  let K := continuousPathTrajectory P hP default
  have hmarkovK : IsMarkovKernel K := by infer_instance
  have hmarkovFinite : IsMarkovKernel (finiteSetKernel P I) :=
    hP.isMarkovKernel_finiteSetKernel P I
  apply Kernel.map_finiteEvaluation_eq_of_integral_tendsto
    K hmarkovK (fun k ↦ finiteDenseApproximationKernel P (q k))
      (finiteSetKernel P I) hmarkovFinite
      (fun t : I ↦ (t : NNReal))
      (fun k t ↦ DenseTime.castOrderEmbedding (q k t)) hq
  · intro k
    exact continuousPathTrajectory_map_finiteDenseApproximation P hP default hK (q k)
  · exact hfinite

end IsConservative
end SubMarkovKernelSemigroup

end KernelLimits

end
end MarkovProcess

end PortComputability

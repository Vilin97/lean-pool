/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Kernel.FiniteRestrictionIdentification
import LeanPool.MarkovProcess.MarkovProcess.Path.KernelIdentification
import LeanPool.MarkovProcess.MarkovProcess.Path.Polish
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.DenseRestrictionMarginals
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.FellerConditional
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.FellerCountableStoppingRestart
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.FellerFiniteMarginals
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.FellerRestrictedRestart
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.FellerShift
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.FellerStoppingConditional
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.FellerStoppingRestart
import LeanPool.MarkovProcess.MarkovProcess.DenseTime.TwoPointMarginals

/-!
# The continuous-path Markov process of a Feller semigroup

This is the entry point of the library: for a conservative sub-Markov kernel semigroup `P` on a
nonempty, locally compact Polish state space it names the continuous-path process
`continuousProcess P hP`, restates under quotable names the properties proved for that process
elsewhere in the library, and proves that it is the unique Markov kernel into continuous paths
with the finite-dimensional distributions of `P`.

Every statement carries the Kolmogorov regularity hypothesis `P.KolmogorovRegular hP`, which is
what gives the dense-time trajectory of `P` a continuous modification.  The shift and restart
statements carry in addition the Feller hypothesis `P.IsFellerKernelSemigroup`; the uniqueness
statements carry neither Feller continuity nor local compactness.

Nothing here asserts a Hunt-process property, and no statement covers a stopping time that can be
infinite.
-/

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess

section FinsetEvaluation

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- Evaluate a continuous path simultaneously at every time of a finite set of nonnegative
times, indexing the result by that set. -/
abbrev finsetEvaluation (I : Finset NNReal) : ContinuousPath alpha → (I → alpha) :=
  finiteEvaluation (fun t : I ↦ (t : NNReal))

end ContinuousPath

end FinsetEvaluation

namespace Kernel

section DenseFiniteEvaluation

variable {alpha beta : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [MeasurableSpace beta]

/-- The finite rational-time marginals of a continuous-path kernel are its evaluations at the
corresponding physical times, reindexed by the rational labels. -/
theorem map_denseRestriction_map_restrict
    (kappa : Kernel beta (ContinuousPath alpha)) (I : Finset DenseTime) :
    (kappa.map ContinuousPath.denseRestriction).map I.restrict =
      (kappa.map (ContinuousPath.finsetEvaluation
        (SubMarkovKernelSemigroup.denseTimePhysicalSet I))).map
          (DenseTimePath.pullbackPhysicalSet I) := by
  have hEvaluate : Measurable (ContinuousPath.finsetEvaluation (alpha := alpha)
      (SubMarkovKernelSemigroup.denseTimePhysicalSet I)) := by
    rw [measurable_pi_iff]
    intro t
    exact ContinuousPath.measurable_coordinateProcess (alpha := alpha) (t : NNReal)
  have hfun : I.restrict ∘ ContinuousPath.denseRestriction (alpha := alpha) =
      DenseTimePath.pullbackPhysicalSet I ∘ ContinuousPath.finsetEvaluation
        (SubMarkovKernelSemigroup.denseTimePhysicalSet I) := by
    funext path
    exact (DenseTimePath.pullbackPhysicalSet_evaluation I path).symm
  rw [← Kernel.map_comp_right kappa ContinuousPath.measurable_denseRestriction
      (Finset.measurable_restrict I), hfun,
    Kernel.map_comp_right kappa hEvaluate (DenseTimePath.measurable_pullbackPhysicalSet I)]

section Identification

variable [T2Space alpha] [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

/-- A finite kernel into continuous-path space is determined by its evaluations at the finite
sets of physical times carried by rational labels. -/
theorem eq_of_map_denseFiniteEvaluation_eq
    (kappa eta : Kernel beta (ContinuousPath alpha)) [IsFiniteKernel kappa]
    (h : ∀ I : Finset DenseTime,
      kappa.map (ContinuousPath.finsetEvaluation
          (SubMarkovKernelSemigroup.denseTimePhysicalSet I)) =
        eta.map (ContinuousPath.finsetEvaluation
          (SubMarkovKernelSemigroup.denseTimePhysicalSet I))) :
    kappa = eta := by
  rw [← map_denseRestriction_eq_iff (alpha := alpha) (beta := beta)]
  apply eq_of_map_finiteRestriction_eq
  intro I
  rw [map_denseRestriction_map_restrict kappa I, map_denseRestriction_map_restrict eta I, h I]

end Identification

end DenseFiniteEvaluation

end Kernel

namespace SubMarkovKernelSemigroup

section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- Kolmogorov regularity of a conservative sub-Markov kernel semigroup: at every starting point
the canonical dense-time coordinate process of `P` satisfies a Kolmogorov--Chentsov moment bound
with an admissible Hölder exponent.

This is the hypothesis under which the dense-time trajectory of `P` admits a continuous
modification, and every statement about `continuousProcess P hP` carries it. -/
def KolmogorovRegular : Prop :=
  ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
    IsKolmogorovProcess (fun r omega ↦ omega r)
        (denseTimeTrajectory P hP DenseTime.enumeration
          DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
      0 < gamma ∧ gamma < (q - 1) / p

/-- The continuous-path process of a conservative sub-Markov kernel semigroup: the canonical
continuous trajectory kernel, with the fallback path of the underlying measurable extension fixed
once and for all.  Under `P.KolmogorovRegular hP` the choice of fallback is immaterial, by
`continuousProcess_eq_continuousPathTrajectory`. -/
def IsConservative.continuousProcess : Kernel alpha (ContinuousPath alpha) :=
  continuousPathTrajectory P hP (ContinuousMap.const NNReal (Classical.arbitrary alpha))

/-- The continuous-path process of a conservative semigroup is a Markov kernel: it assigns total
mass one to path space from every starting point. -/
instance isMarkovKernel_continuousProcess : IsMarkovKernel (continuousProcess P hP) := by
  unfold IsConservative.continuousProcess
  infer_instance

/-- The continuous-path process is the canonical continuous trajectory kernel built from any
fallback path whatsoever. -/
theorem IsConservative.continuousProcess_eq_continuousPathTrajectory
    (hK : P.KolmogorovRegular hP) (default : ContinuousPath alpha) :
    continuousProcess P hP = continuousPathTrajectory P hP default :=
  continuousPathTrajectory_eq P hP _ default hK

/-- Evaluating the continuous-path process at a nonnegative rational time gives the transition
kernel of `P` at that time. -/
theorem IsConservative.continuousProcess_map_eval
    (hK : P.KolmogorovRegular hP) (r : DenseTime) :
    (continuousProcess P hP).map (fun omega ↦ omega (DenseTime.castOrderEmbedding r)) =
      P (DenseTime.castOrderEmbedding r) :=
  continuousPathTrajectory_map_eval P hP _ hK r

/-- The continuous-path process starts where it is told: its time-zero coordinate has the law of
the identity kernel, that is, the Dirac measure at the starting point. -/
theorem IsConservative.continuousProcess_map_eval_zero (hK : P.KolmogorovRegular hP) :
    (continuousProcess P hP).map (fun omega ↦ omega 0) = Kernel.id := by
  have hzero : DenseTime.castOrderEmbedding (0 : DenseTime) = (0 : NNReal) := by
    rw [DenseTime.castOrderEmbedding, NNRat.castOrderEmbedding_apply, NNRat.cast_zero]
  have heval := IsConservative.continuousProcess_map_eval P hP hK 0
  rw [hzero] at heval
  rw [heval]
  exact P.zero

/-- Every finite rational-time marginal of the continuous-path process is the finite-set kernel of
`P` at the corresponding physical times. -/
theorem IsConservative.continuousProcess_map_finiteEvaluation_denseTime
    (hK : P.KolmogorovRegular hP) (I : Finset DenseTime) :
    (continuousProcess P hP).map
        (ContinuousPath.finsetEvaluation (denseTimePhysicalSet I)) =
      finiteSetKernel P (denseTimePhysicalSet I) :=
  continuousPathTrajectory_map_finiteDenseTimeSet P hP _ hK I

/-- Every finite restriction of the dense-time projection of the continuous-path process is the
finite-set kernel of `P`, reindexed from physical times back to rational labels. -/
theorem IsConservative.continuousProcess_map_denseRestriction_map_restrict
    (hK : P.KolmogorovRegular hP) (I : Finset DenseTime) :
    ((continuousProcess P hP).map ContinuousPath.denseRestriction).map I.restrict =
      (finiteSetKernel P (denseTimePhysicalSet I)).map (DenseTimePath.pullbackPhysicalSet I) :=
  continuousPathTrajectory_map_denseRestriction_map_restrict P hP _ hK I

omit [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha] in
include hP in
/-- A kernel into continuous paths whose empty finite-dimensional distribution is that of a
conservative `P` is automatically a Markov kernel: reading no coordinate at all already forces
total mass one.  This is why requiring `IsMarkovKernel Q` alongside the finite-dimensional
distributions of `P` costs nothing. -/
theorem IsConservative.isMarkovKernel_of_map_finiteEvaluation_empty
    (Q : Kernel alpha (ContinuousPath alpha))
    (hQ : Q.map (ContinuousPath.finsetEvaluation (alpha := alpha) (∅ : Finset NNReal)) =
      finiteSetKernel P ∅) :
    IsMarkovKernel Q := by
  let : IsMarkovKernel (finiteSetKernel P (∅ : Finset NNReal)) :=
    hP.isMarkovKernel_finiteSetKernel P ∅
  have hmeas : Measurable
      (ContinuousPath.finsetEvaluation (alpha := alpha) (∅ : Finset NNReal)) := by
    rw [measurable_pi_iff]
    intro t
    exact ContinuousPath.measurable_coordinateProcess (alpha := alpha) (t : NNReal)
  refine ⟨fun x ↦ ⟨?_⟩⟩
  have hx := congrArg (fun k : Kernel alpha ((∅ : Finset NNReal) → alpha) ↦ k x Set.univ) hQ
  rw [Kernel.map_apply' Q hmeas x MeasurableSet.univ, Set.preimage_univ] at hx
  rw [hx]
  exact measure_univ

variable [LocallyCompactSpace alpha]

/-- Every finite-dimensional distribution of the continuous-path process of a conservative Feller
semigroup is the finite-set kernel of `P` at the same times. -/
theorem IsFellerKernelSemigroup.continuousProcess_map_finiteEvaluation
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) (I : Finset NNReal) :
    (continuousProcess P hP).map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I :=
  hFeller.continuousPathTrajectory_map_finiteTimeSet P hP _ hK I

/-- Simple Markov property of the continuous-path process of a conservative Feller semigroup:
shifting by a deterministic nonnegative time gives the process started from the state at that
time, averaged over the transition kernel. -/
theorem IsFellerKernelSemigroup.continuousProcess_map_shift
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) (s : NNReal) :
    (continuousProcess P hP).map (ContinuousPath.shift s) = (continuousProcess P hP).comp (P s) :=
  hFeller.continuousPathTrajectory_map_shift P hP _ hK s

/-- Restart at a deterministic time: after restriction to an event of the canonical filtration at
time `s`, the law of the shifted path is the process started from the time-`s` state. -/
theorem IsFellerKernelSemigroup.continuousProcess_restrict_map_shift
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (x : alpha) (s : NNReal) (A : Set (ContinuousPath alpha))
    (hA : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := alpha) s] A) :
    (((continuousProcess P hP) x).restrict A).map (ContinuousPath.shift s) =
      Kernel.comap (continuousProcess P hP)
          (ContinuousPath.coordinateProcess (alpha := alpha) s)
          (ContinuousPath.measurable_coordinateProcess s) ∘ₘ
        (((continuousProcess P hP) x).restrict A) :=
  hFeller.continuousPathTrajectory_restrict_map_shift P hP _ hK x s A hA

/-- Strong Markov property at a finite stopping time, in restart form: after restriction to an
event of the stopped sigma-algebra, the law of the path shifted at the stopping time is the
process started from the state at that time. -/
theorem IsFellerKernelSemigroup.continuousProcess_restrict_map_shift_stoppingTime
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (x : alpha) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    (A : Set (ContinuousPath alpha)) (hA : MeasurableSet[hT.measurableSpace] A) :
    (((continuousProcess P hP) x).restrict A).map
        (fun omega ↦ ContinuousPath.shift (T omega) omega) =
      Kernel.comap (continuousProcess P hP) (fun omega ↦ omega (T omega))
          (ContinuousPath.measurable_eval_stoppingTime_borel T hT) ∘ₘ
        (((continuousProcess P hP) x).restrict A) :=
  hFeller.continuousPathTrajectory_restrict_map_shift_stoppingTime P hP _ hK x T hT A hA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- Simple Markov property in conditional-expectation form: given the canonical filtration at a
deterministic time, the conditional expectation of a bounded functional of the shifted path is
that functional's expectation under the process started from the current state. -/
theorem IsFellerKernelSemigroup.continuousProcess_condExp_shift
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (x : alpha) (s : NNReal) (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : ℝ) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((continuousProcess P hP) x)[fun omega ↦ F (ContinuousPath.shift s omega)|
        ContinuousPath.canonicalFiltration (alpha := alpha) s] =ᵐ[
      (continuousProcess P hP) x]
      fun omega ↦ ∫ eta, F eta ∂(continuousProcess P hP) (omega s) :=
  hFeller.continuousPathTrajectory_condExp_shift P hP _ hK x s F hF C hFC

/-- Strong Markov property in conditional-expectation form at a finite stopping time: given the
stopped sigma-algebra, the conditional expectation of a bounded functional of the path shifted at
the stopping time is that functional's expectation under the process started from the state at the
stopping time. -/
theorem IsFellerKernelSemigroup.continuousProcess_condExp_shift_stoppingTime
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (x : alpha) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : ℝ) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((continuousProcess P hP) x)[fun omega ↦
        F (ContinuousPath.shift (T omega) omega)|hT.measurableSpace] =ᵐ[
      (continuousProcess P hP) x]
      fun omega ↦ ∫ eta, F eta ∂(continuousProcess P hP) (omega (T omega)) :=
  hFeller.continuousPathTrajectory_condExp_shift_stoppingTime P hP _ hK x T hT F hF C hFC

/-- Strong Markov property at a finite stopping time with countable range, in
conditional-expectation form.  This is the countable-range case from which the general finite
stopping time is obtained by dyadic approximation from above. -/
theorem IsFellerKernelSemigroup.continuousProcess_condExp_shift_countableStoppingTime
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (x : alpha) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    (hTrange : (Set.range T).Countable)
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : ℝ) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((continuousProcess P hP) x)[fun omega ↦
        F (ContinuousPath.shift (T omega) omega)|hT.measurableSpace] =ᵐ[
      (continuousProcess P hP) x]
      fun omega ↦ ∫ eta, F eta ∂(continuousProcess P hP) (omega (T omega)) :=
  hFeller.continuousPathTrajectory_condExp_shift_countableStoppingTime P hP _ hK x T hT hTrange
    F hF C hFC

omit [LocallyCompactSpace alpha] in
/-- Uniqueness from rational times: a finite kernel into continuous paths whose evaluations at
the finite sets of physical times carried by rational labels are the finite-set kernels of `P` is
the continuous-path process of `P`.  Neither Feller continuity nor local compactness is used. -/
theorem IsConservative.eq_continuousProcess_of_map_finiteEvaluation_denseTime
    (hK : P.KolmogorovRegular hP) (Q : Kernel alpha (ContinuousPath alpha)) [IsFiniteKernel Q]
    (hQ : ∀ I : Finset DenseTime,
      Q.map (ContinuousPath.finsetEvaluation (denseTimePhysicalSet I)) =
        finiteSetKernel P (denseTimePhysicalSet I)) :
    Q = continuousProcess P hP :=
  Kernel.eq_of_map_denseFiniteEvaluation_eq Q _ fun I ↦
    (hQ I).trans (continuousProcess_map_finiteEvaluation_denseTime P hP hK I).symm

omit [LocallyCompactSpace alpha] in
/-- Uniqueness: a finite kernel into continuous paths with the finite-dimensional distributions of
`P` is the continuous-path process of `P`.  Only rational times are read off the hypothesis, so
neither Feller continuity nor local compactness is used. -/
theorem IsConservative.eq_continuousProcess_of_map_finiteEvaluation
    (hK : P.KolmogorovRegular hP) (Q : Kernel alpha (ContinuousPath alpha)) [IsFiniteKernel Q]
    (hQ : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I) :
    Q = continuousProcess P hP :=
  IsConservative.eq_continuousProcess_of_map_finiteEvaluation_denseTime P hP hK Q fun I ↦
    hQ (denseTimePhysicalSet I)

omit [LocallyCompactSpace alpha] in
/-- Existence and uniqueness at rational times, for a conservative Kolmogorov-regular semigroup:
there is exactly one Markov kernel into continuous paths whose evaluations at the finite sets of
physical times carried by rational labels are the finite-set kernels of `P`, namely
`continuousProcess P hP`.  No Feller hypothesis is used. -/
theorem IsConservative.existsUnique_continuousProcess_denseTime (hK : P.KolmogorovRegular hP) :
    ∃! Q : Kernel alpha (ContinuousPath alpha), IsMarkovKernel Q ∧
      ∀ I : Finset DenseTime,
        Q.map (ContinuousPath.finsetEvaluation (denseTimePhysicalSet I)) =
          finiteSetKernel P (denseTimePhysicalSet I) := by
  refine ⟨continuousProcess P hP,
    ⟨inferInstance, continuousProcess_map_finiteEvaluation_denseTime P hP hK⟩, ?_⟩
  rintro Q ⟨hQ, hmarg⟩
  let : IsMarkovKernel Q := hQ
  exact IsConservative.eq_continuousProcess_of_map_finiteEvaluation_denseTime P hP hK Q hmarg

/-- **Existence and uniqueness of the continuous-path Markov process.**  Let `P` be a sub-Markov
kernel semigroup on a nonempty, locally compact Polish state space that is conservative (`hP`),
Feller (`hFeller`), and Kolmogorov regular (`hK`).  Then there is exactly one Markov kernel `Q`
from the state space to continuous paths whose finite-dimensional distributions are those of `P`,
and it is `continuousProcess P hP`.

Here "finite-dimensional distributions" means, for each finite set `I` of nonnegative times, the
kernel `finiteSetKernel P I` obtained by composing the transition kernels of `P` along `I` in
increasing order; `ContinuousPath.finsetEvaluation I` reads the coordinates of a path at `I`.

The hypothesis `IsMarkovKernel Q` is not an extra requirement in disguise: it already follows from
the marginal condition at `I = ∅`, by `isMarkovKernel_of_map_finiteEvaluation_empty`. -/
theorem IsFellerKernelSemigroup.existsUnique_continuousProcess
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) :
    ∃! Q : Kernel alpha (ContinuousPath alpha), IsMarkovKernel Q ∧
      ∀ I : Finset NNReal,
        Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I := by
  refine ⟨continuousProcess P hP,
    ⟨inferInstance, hFeller.continuousProcess_map_finiteEvaluation P hP hK⟩, ?_⟩
  rintro Q ⟨hQ, hmarg⟩
  let : IsMarkovKernel Q := hQ
  exact IsConservative.eq_continuousProcess_of_map_finiteEvaluation P hP hK Q hmarg


omit [LocallyCompactSpace alpha] in
/-- Kolmogorov regularity follows from the intrinsic moment criterion on the semigroup. -/
theorem KolmogorovRegular.of_hasKolmogorovMoments {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) : P.KolmogorovRegular hP :=
  IsConservative.kolmogorovRegular_of_hasKolmogorovMoments P hP hmom

include hP in
/-- **Existence and uniqueness of the continuous Markov process, intrinsic form.**  For a
conservative Feller sub-Markov kernel semigroup on a locally compact Polish state space
satisfying the Kolmogorov moment criterion `HasKolmogorovMoments`, there is exactly one Markov
kernel into continuous paths whose finite-dimensional distributions are the increasing-order
iterated transition laws `finiteSetKernel P I`.  This is the form whose hypotheses mention only
the semigroup; `existsUnique_continuousProcess` is the same statement under the
construction-level regularity hypothesis `KolmogorovRegular`. -/
theorem IsFellerKernelSemigroup.existsUnique_continuousProcess_of_hasKolmogorovMoments
    (hFeller : P.IsFellerKernelSemigroup) {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) :
    ∃! Q : Kernel alpha (ContinuousPath alpha), IsMarkovKernel Q ∧
      ∀ I : Finset NNReal,
        Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I :=
  hFeller.existsUnique_continuousProcess P hP (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom)

include hP in
/-- A conservative Feller semigroup satisfying the Kolmogorov moment criterion has a unique
continuous-path Markov kernel realizing all of its finite-dimensional distributions. -/
theorem _root_.MarkovProcess.existsUnique_continuousProcess
    (hFeller : P.IsFellerKernelSemigroup) {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) :
    ∃! Q : Kernel alpha (ContinuousPath alpha), IsMarkovKernel Q ∧
      ∀ I : Finset NNReal,
        Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I :=
  hFeller.existsUnique_continuousProcess_of_hasKolmogorovMoments P hP hmom

end


end SubMarkovKernelSemigroup

end MarkovProcess

end PortComputability

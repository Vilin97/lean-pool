/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.MeasureFiniteRestrictionIdentification
public import LeanPool.MarkovProcess.MarkovProcess.Main
public import LeanPool.MarkovProcess.MarkovProcess.Parameterized.DenseTimeTrajectory


/-!
# The continuous-path process of a measurably parameterized semigroup

For a jointly measurable family of sub-Markov kernel semigroups indexed by a measurable parameter
space `Theta`, this file constructs the quenched continuous-path process as a single kernel
`Kernel (Theta × alpha) (ContinuousPath alpha)`: joint measurability in the parameter and the
starting state is carried by the kernel structure, not proved parameter by parameter afterwards.

The construction transports the jointly measurable dense-time trajectory
`parameterizedDenseTimeTrajectory` through the same measurable continuous-extension map that the
unparameterized `continuousProcess` uses, with the same fallback path.  The central result is the
fibre identity: at every parameter and every starting point the parameterized process is
*literally* the unparameterized process of that parameter's semigroup, with no null set and no
regularity hypothesis.  It rests on the corresponding dense-time fibre identity, which is proved
here from the finite enumeration-prefix marginals of the two trajectory kernels.

Fibrewise conservativity, Kolmogorov regularity and Kolmogorov moment bounds are named as
predicates on the parameterized family, so that consumers state hypotheses once.

No Markov, strong Markov, Feller, equivariance, annealed or killed statement is proved here; each
of those is a separate transport through the fibre identity.
-/

@[expose] public section

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

section

section Conservativity

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]

/-- Fibrewise conservativity of a measurably parameterized sub-Markov kernel semigroup: every
parameter slice is a conservative sub-Markov kernel semigroup, so that no mass is lost at any
time from any state for any parameter. -/
def IsConservative (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) : Prop :=
  ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative

end Conservativity

section Moments

variable {Theta alpha : Type*} [MeasurableSpace Theta] [PseudoEMetricSpace alpha]
  [MeasurableSpace alpha]

/-- Fibrewise Kolmogorov moment bounds with parameter-independent constants: every parameter slice
satisfies the intrinsic displacement estimate `∫ edist z y ^ p ∂(P theta h y) ≤ M * h ^ q`, with
the same exponents `p`, `q` and the same constant `M` for every parameter. -/
def HasKolmogorovMoments (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (p q : ℝ) (M : ℝ≥0) : Prop :=
  ∀ theta, (P.toSubMarkovKernelSemigroup theta).HasKolmogorovMoments p q M

end Moments

section DenseTimeFibre

variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

omit [StandardBorelSpace alpha] [Nonempty alpha] in
/-- Two finite measures on a countable product path space that agree on every finite
enumeration prefix agree.  Every finite coordinate set is contained in a long enough prefix,
so the prefix marginals already determine all finite-coordinate marginals. -/
private theorem measure_eq_of_map_denseTimeTrajectoryPrefix_eq (e : ℕ ≃ D)
    (mu nu : Measure (D → alpha)) [IsFiniteMeasure mu]
    (h : ∀ n : ℕ,
      mu.map (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectoryPrefix e n) =
        nu.map (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectoryPrefix e n)) :
    mu = nu := by
  refine MarkovProcess.Measure.eq_of_map_finiteRestriction_eq mu nu fun I ↦ ?_
  obtain ⟨n, hlt⟩ : ∃ n : ℕ, ∀ d ∈ I, e.symm d < n :=
    ⟨I.sup fun d ↦ e.symm d + 1,
      fun d hd ↦ Nat.lt_of_succ_le (Finset.le_sup (f := fun d ↦ e.symm d + 1) hd)⟩
  have hprefix : Measurable
      (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectoryPrefix (α := alpha) e n) :=
    SubMarkovKernelSemigroup.IsConservative.measurable_denseTimeTrajectoryPrefix e n
  have hg : Measurable
      (fun z : Fin n → alpha ↦ fun d : I ↦ z ⟨e.symm (d : D), hlt (d : D) d.2⟩) := by
    rw [measurable_pi_iff]
    intro d
    exact measurable_pi_apply _
  have hfun :
      (fun z : Fin n → alpha ↦ fun d : I ↦ z ⟨e.symm (d : D), hlt (d : D) d.2⟩) ∘
          SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectoryPrefix (α := alpha) e n =
        I.restrict := by
    funext path d
    change path (e (e.symm (d : D))) = path (d : D)
    rw [e.apply_symm_apply]
  rw [← hfun, ← Measure.map_map hg hprefix, ← Measure.map_map hg hprefix, h n]

/-- **Dense-time fibre identity.**  At every parameter and every starting state, the jointly
measurable parameterized dense-time trajectory is the dense-time trajectory of that parameter's
semigroup.  Both kernels are Markov with the same finite enumeration-prefix marginals. -/
theorem parameterizedDenseTimeTrajectory_apply
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (theta : Theta) (x : alpha) :
    P.parameterizedDenseTimeTrajectory hP e iota (theta, x) =
      SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectory
        (P.toSubMarkovKernelSemigroup theta) (hP theta) e iota x := by
  let : IsMarkovKernel (P.parameterizedDenseTimeTrajectory hP e iota) :=
    P.isMarkovKernel_parameterizedDenseTimeTrajectory hP e iota
  refine measure_eq_of_map_denseTimeTrajectoryPrefix_eq e _ _ fun n ↦ ?_
  have hprefix : Measurable
      (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectoryPrefix (α := alpha) e n) :=
    SubMarkovKernelSemigroup.IsConservative.measurable_denseTimeTrajectoryPrefix e n
  rw [← Kernel.map_apply _ hprefix, ← Kernel.map_apply _ hprefix,
    P.parameterizedDenseTimeTrajectory_map_prefix hP e iota n,
    SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectory_map_prefix
      (P.toSubMarkovKernelSemigroup theta) (hP theta) e iota n,
    P.parameterizedDenseTimePrefixKernel_apply e iota n theta x]

end DenseTimeFibre

section ContinuousProcess

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)

/-- Fibrewise Kolmogorov regularity: for every parameter, the dense-time coordinate process of
that parameter's semigroup satisfies a Kolmogorov--Chentsov moment bound with an admissible
Hölder exponent at every starting point.  The exponents and constants may depend on the parameter
and on the starting point. -/
def KolmogorovRegular : Prop :=
  ∀ theta, (P.toSubMarkovKernelSemigroup theta).KolmogorovRegular (hP theta)

/-- Fibrewise Kolmogorov moment bounds imply fibrewise Kolmogorov regularity. -/
theorem KolmogorovRegular.of_hasKolmogorovMoments {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) : P.KolmogorovRegular hP :=
  fun theta ↦ SubMarkovKernelSemigroup.IsConservative.kolmogorovRegular_of_hasKolmogorovMoments
    (P.toSubMarkovKernelSemigroup theta) (hP theta) (hmom theta)

/-- The parameterized continuous-path process: the jointly measurable dense-time trajectory of
`P`, transported to continuous paths by the canonical measurable extension, with the fallback path
of that extension fixed to the constant path at `Classical.arbitrary alpha` — exactly the fallback
used by the unparameterized `continuousProcess`.

Joint measurability in the parameter and the starting state is carried by the kernel structure.
Under `P.KolmogorovRegular hP` the choice of fallback is immaterial, by `continuousProcess_eq`. -/
def IsConservative.continuousProcess : Kernel (Theta × alpha) (ContinuousPath alpha) :=
  Kernel.toContinuousPathKernel
    (P.parameterizedDenseTimeTrajectory hP DenseTime.enumeration
      DenseTime.castOrderEmbedding.toEmbedding)
    (ContinuousMap.const NNReal (Classical.arbitrary alpha))

/-- The parameterized continuous-path process is a Markov kernel: from every parameter and every
starting state it assigns total mass one to continuous-path space. -/
instance isMarkovKernel_continuousProcess :
    IsMarkovKernel (IsConservative.continuousProcess P hP) := by
  let : IsMarkovKernel (P.parameterizedDenseTimeTrajectory hP DenseTime.enumeration
      DenseTime.castOrderEmbedding.toEmbedding) :=
    P.isMarkovKernel_parameterizedDenseTimeTrajectory hP _ _
  unfold IsConservative.continuousProcess
  exact Kernel.isMarkovKernel_toContinuousPathKernel _ _

/-- **Fibre identity.**  At every parameter `theta` and every starting state `x`, the parameterized
continuous-path process is the continuous-path process of the semigroup at `theta`, started at `x`.

The identity is exact and unconditional: it holds for every parameter and every starting point,
with no exceptional set and without any regularity hypothesis, because both sides transport the
same dense-time law through the same measurable extension.  It is the theorem that lets every
property of the unparameterized process be restated on the parameterized kernel. -/
theorem IsConservative.continuousProcess_apply (theta : Theta) (x : alpha) :
    IsConservative.continuousProcess P hP (theta, x) =
      SubMarkovKernelSemigroup.IsConservative.continuousProcess
        (P.toSubMarkovKernelSemigroup theta) (hP theta) x := by
  have hext := ContinuousPath.measurable_continuousExtension
    (ContinuousMap.const NNReal (Classical.arbitrary alpha))
  unfold IsConservative.continuousProcess
    SubMarkovKernelSemigroup.IsConservative.continuousProcess
    SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory
  rw [Kernel.toContinuousPathKernel_eq_map, Kernel.map_apply _ hext,
    Kernel.toContinuousPathKernel_eq_map, Kernel.map_apply _ hext,
    parameterizedDenseTimeTrajectory_apply]

/-- The fibre identity in kernel form: freezing the parameter of the parameterized
continuous-path process gives the continuous-path process of that parameter's semigroup, as
kernels from the starting state. -/
theorem IsConservative.continuousProcess_apply' (theta : Theta) :
    (IsConservative.continuousProcess P hP).comap (fun x ↦ (theta, x))
        (measurable_const.prodMk measurable_id) =
      SubMarkovKernelSemigroup.IsConservative.continuousProcess
        (P.toSubMarkovKernelSemigroup theta) (hP theta) := by
  refine Kernel.ext fun x ↦ ?_
  rw [Kernel.comap_apply, IsConservative.continuousProcess_apply]

/-- Under fibrewise Kolmogorov regularity, the jointly measurable dense-time trajectory of `P` is
almost surely supported on the dense-time restrictions of continuous paths, simultaneously for
every parameter and every starting state. -/
theorem IsConservative.isSupportedOnContinuousPaths_parameterizedDenseTimeTrajectory
    (hK : P.KolmogorovRegular hP) :
    Kernel.IsSupportedOnContinuousPaths
      (P.parameterizedDenseTimeTrajectory hP DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding) := by
  let : IsMarkovKernel (P.parameterizedDenseTimeTrajectory hP DenseTime.enumeration
      DenseTime.castOrderEmbedding.toEmbedding) :=
    P.isMarkovKernel_parameterizedDenseTimeTrajectory hP _ _
  refine Kernel.IsSupportedOnContinuousPaths.of_isKolmogorovCoordinate _ ?_
  rintro ⟨theta, x⟩
  rw [parameterizedDenseTimeTrajectory_apply]
  exact hK theta x

/-- Under fibrewise Kolmogorov regularity the parameterized continuous-path process is the
transport of the dense-time trajectory through the measurable extension built from *any* fallback
path: the arbitrary choice made in the definition is immaterial. -/
theorem IsConservative.continuousProcess_eq (hK : P.KolmogorovRegular hP)
    (default : ContinuousPath alpha) :
    IsConservative.continuousProcess P hP =
      Kernel.toContinuousPathKernel
        (P.parameterizedDenseTimeTrajectory hP DenseTime.enumeration
          DenseTime.castOrderEmbedding.toEmbedding) default :=
  Kernel.IsSupportedOnContinuousPaths.toContinuousPathKernel_eq _
    (IsConservative.isSupportedOnContinuousPaths_parameterizedDenseTimeTrajectory P hP hK) _ default

section QuenchedExpectations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Quenched expectations are jointly measurable.**  For a strongly measurable functional `F` on
continuous paths, the quenched expectation of `F` is a strongly measurable function of the
parameter and the starting state.  This is what allows a quenched expectation to be integrated
against a law on the parameter space. -/
theorem stronglyMeasurable_integral_continuousProcess (F : ContinuousPath alpha → E)
    (hF : StronglyMeasurable F) :
    StronglyMeasurable fun p : Theta × alpha ↦
      ∫ eta, F eta ∂IsConservative.continuousProcess P hP p :=
  hF.integral_kernel (κ := IsConservative.continuousProcess P hP)

variable [MeasurableSpace E] [BorelSpace E]

/-- **Measurable quenched expectations.**  For a strongly measurable functional `F` on continuous
paths, `(theta, x) ↦ ∫ F d(law of the process for parameter `theta` started at `x`)` is
measurable. -/
theorem measurable_integral_continuousProcess (F : ContinuousPath alpha → E)
    (hF : StronglyMeasurable F) :
    Measurable fun p : Theta × alpha ↦
      ∫ eta, F eta ∂IsConservative.continuousProcess P hP p :=
  (stronglyMeasurable_integral_continuousProcess P hP F hF).measurable

/-- Measurable quenched expectations of a finite-dimensional cylinder functional: for a finite set
`I` of times and a strongly measurable `f` on the coordinates at `I`, the quenched expectation of
`f` composed with the evaluation at `I` is measurable in the parameter and the starting state. -/
theorem measurable_integral_finsetEvaluation_continuousProcess (I : Finset NNReal)
    (f : (I → alpha) → E) (hf : StronglyMeasurable f) :
    Measurable fun p : Theta × alpha ↦
      ∫ eta, f (ContinuousPath.finsetEvaluation I eta)
        ∂IsConservative.continuousProcess P hP p := by
  have hI : Measurable (ContinuousPath.finsetEvaluation (alpha := alpha) I) := by
    rw [measurable_pi_iff]
    intro t
    exact ContinuousPath.measurable_coordinateProcess (alpha := alpha) (t : NNReal)
  exact measurable_integral_continuousProcess P hP _ (hf.comp_measurable hI)

end QuenchedExpectations

end ContinuousProcess

end
end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess

end PortComputability

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Main

/-!
# The identity semigroup and its continuous-path process

The transition semigroup that never moves: `idSemigroup t = Kernel.id` at every time.  It is
conservative, Feller, and satisfies the Kolmogorov moment criterion with exponents `p = 1`,
`q = 2` and constant `M = 0`, so the existence-and-uniqueness theorem of `MarkovProcess.Main`
applies to it verbatim.  The resulting process is identified: from every starting point `x` its
law is the Dirac mass at the constant path at `x`.

This file witnesses that the hypotheses of the main theorem are jointly satisfiable; it proves
nothing about any other semigroup, and it makes no claim about a semigroup that actually moves
(see `MarkovProcess.Examples.Drift` for that).
-/

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

section

section Definition

variable {alpha : Type*} [MeasurableSpace alpha]

/-- The identity kernel semigroup: the transition kernel at every time is the identity kernel,
so the associated process never moves. -/
def idSemigroup : SubMarkovKernelSemigroup alpha where
  kernel := fun _ ↦ Kernel.id
  measurable_kernel := (Kernel.id : Kernel alpha alpha).measurable.comp measurable_snd
  kernel_zero := rfl
  kernel_add := fun _ _ ↦ (Kernel.id_comp Kernel.id).symm
  isSubMarkovKernel := fun _ ↦ IsSubMarkovKernel.id

/-- Every transition measure of the identity semigroup is the Dirac mass at the starting
point. -/
theorem idSemigroup_apply (t : NNReal) (x : alpha) :
    (idSemigroup (alpha := alpha)) t x = Measure.dirac x := rfl

/-- The identity semigroup is conservative: every transition measure has total mass one. -/
theorem isConservative_idSemigroup :
    (idSemigroup (alpha := alpha)).IsConservative := by
  intro t x
  rw [idSemigroup_apply t x]
  exact measure_univ

end Definition

section Feller

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]

/-- Integrating a `C₀` function against the identity semigroup returns the function itself. -/
theorem kernelIntegral_idSemigroup (t : NNReal) (f : C₀(alpha, ℝ)) :
    kernelIntegral ((idSemigroup (alpha := alpha)) t) f = f := by
  funext x
  rw [kernelIntegral, idSemigroup_apply t x]
  exact integral_dirac' (f : alpha → ℝ) x f.continuous.stronglyMeasurable

/-- The identity semigroup maps `C₀` into itself. -/
theorem mapsC0_idSemigroup : (idSemigroup (alpha := alpha)).MapsC0 := by
  intro t f
  rw [kernelIntegral_idSemigroup t f]
  exact ⟨f.continuous, f.zero_at_infty'⟩

variable [LocallyCompactSpace alpha]

omit [LocallyCompactSpace alpha] in
/-- The identity semigroup is a Feller semigroup: its `C₀` operators are all the identity, so
they map `C₀` into itself and have constant, hence continuous, time orbits. -/
theorem isFellerKernelSemigroup_idSemigroup :
    (idSemigroup (alpha := alpha)).IsFellerKernelSemigroup := by
  refine ⟨mapsC0_idSemigroup, fun f ↦ ?_⟩
  have hconst : (fun _ : NNReal ↦ (idSemigroup (alpha := alpha)).c0Operator
      mapsC0_idSemigroup 0 f) =
      fun t : NNReal ↦ (idSemigroup (alpha := alpha)).c0Operator mapsC0_idSemigroup t f := by
    funext t
    apply ZeroAtInftyContinuousMap.ext
    intro x
    rw [SubMarkovKernelSemigroup.c0Operator_apply,
      SubMarkovKernelSemigroup.c0Operator_apply,
      kernelIntegral_idSemigroup t f, kernelIntegral_idSemigroup 0 f]
  rw [← hconst]
  exact continuous_const

end Feller

section Moments

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]

/-- The identity semigroup satisfies the Kolmogorov moment criterion with `p = 1`, `q = 2` and
vanishing constant: the displacement over any time is identically zero. -/
theorem hasKolmogorovMoments_idSemigroup :
    (idSemigroup (alpha := alpha)).HasKolmogorovMoments 1 2 0 := by
  refine ⟨one_pos, one_lt_two, fun h y ↦ ?_⟩
  have hmeas : Measurable (fun z : alpha ↦ edist z y ^ (1 : ℝ)) :=
    (measurable_edist_left (x := y)).pow_const 1
  rw [idSemigroup_apply h y, lintegral_dirac' y hmeas, edist_self,
    ENNReal.zero_rpow_of_pos one_pos, ENNReal.coe_zero, zero_mul]

end Moments

section Process

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [Nonempty alpha]

omit [LocallyCompactSpace alpha] in
/-- The identity semigroup is Kolmogorov regular, by its moment bound. -/
theorem kolmogorovRegular_idSemigroup :
    (idSemigroup (alpha := alpha)).KolmogorovRegular isConservative_idSemigroup :=
  SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments _
    isConservative_idSemigroup hasKolmogorovMoments_idSemigroup

/-- **The main theorem, applied to the identity semigroup.**  There is exactly one Markov kernel
from the state space to continuous paths whose finite-dimensional distributions are those of the
identity semigroup. This supplies a model of the main existence theorem’s hypotheses. -/
theorem existsUnique_continuousProcess_idSemigroup :
    ∃! Q : Kernel alpha (ContinuousPath alpha), IsMarkovKernel Q ∧
      ∀ I : Finset NNReal,
        Q.map (ContinuousPath.finsetEvaluation I) =
          SubMarkovKernelSemigroup.finiteSetKernel (idSemigroup (alpha := alpha)) I :=
  isFellerKernelSemigroup_idSemigroup.existsUnique_continuousProcess_of_hasKolmogorovMoments
    (idSemigroup (alpha := alpha)) isConservative_idSemigroup hasKolmogorovMoments_idSemigroup

omit [LocallyCompactSpace alpha] in
private theorem ae_eq_const_of_continuousProcess_idSemigroup (x : alpha) :
    (fun omega : ContinuousPath alpha ↦ omega) =ᵐ[
      SubMarkovKernelSemigroup.IsConservative.continuousProcess (idSemigroup (alpha := alpha))
        isConservative_idSemigroup x]
      fun _ ↦ ContinuousMap.const NNReal x := by
  set mu := SubMarkovKernelSemigroup.IsConservative.continuousProcess
    (idSemigroup (alpha := alpha)) isConservative_idSemigroup x with hmu
  have hcoord : ∀ q : DenseTime, ∀ᵐ omega ∂mu,
      omega (DenseTime.castOrderEmbedding q) = x := by
    intro q
    have hmeas : Measurable
        (fun omega : ContinuousPath alpha ↦ omega (DenseTime.castOrderEmbedding q)) :=
      ContinuousPath.measurable_coordinateProcess (alpha := alpha) _
    have hmap := SubMarkovKernelSemigroup.IsConservative.continuousProcess_map_eval
      (idSemigroup (alpha := alpha)) isConservative_idSemigroup kolmogorovRegular_idSemigroup q
    have hmapx : Measure.map (fun omega : ContinuousPath alpha ↦
        omega (DenseTime.castOrderEmbedding q)) mu = Measure.dirac x := by
      rw [hmu, ← Kernel.map_apply _ hmeas, hmap, idSemigroup_apply]
    have hsingleton : MeasurableSet ({x}ᶜ : Set alpha) :=
      (isClosed_singleton (x := x)).measurableSet.compl
    have hzero : mu ((fun omega : ContinuousPath alpha ↦
        omega (DenseTime.castOrderEmbedding q)) ⁻¹' ({x}ᶜ : Set alpha)) = 0 := by
      rw [← Measure.map_apply hmeas hsingleton, hmapx, Measure.dirac_apply' x hsingleton,
        Set.indicator_of_notMem (by simp only [Set.mem_compl_iff, Set.mem_singleton_iff,
          not_true_eq_false, not_false_eq_true])]
    exact hzero
  have hall : ∀ᵐ omega ∂mu, ∀ q : DenseTime,
      omega (DenseTime.castOrderEmbedding q) = x := ae_all_iff.mpr hcoord
  filter_upwards [hall] with omega homega
  apply ContinuousPath.denseRestriction_injective
  funext q
  rw [ContinuousPath.denseRestriction_apply, ContinuousPath.denseRestriction_apply, homega q]
  rfl

omit [LocallyCompactSpace alpha] in
/-- **The continuous-path process of the identity semigroup is the constant path.**  From every
starting point, the law of the process is the Dirac mass at the constant path at that point. -/
theorem continuousProcess_idSemigroup_eq (x : alpha) :
    SubMarkovKernelSemigroup.IsConservative.continuousProcess (idSemigroup (alpha := alpha))
        isConservative_idSemigroup x =
      Measure.dirac (ContinuousMap.const NNReal x) := by
  set mu := SubMarkovKernelSemigroup.IsConservative.continuousProcess
    (idSemigroup (alpha := alpha)) isConservative_idSemigroup x with hmu
  have hprob : IsProbabilityMeasure mu := by
    rw [hmu]
    infer_instance
  calc mu = mu.map id := (Measure.map_id).symm
    _ = mu.map (fun _ ↦ ContinuousMap.const NNReal x) :=
        Measure.map_congr (ae_eq_const_of_continuousProcess_idSemigroup x)
    _ = mu Set.univ • Measure.dirac (ContinuousMap.const NNReal x) := Measure.map_const _ _
    _ = Measure.dirac (ContinuousMap.const NNReal x) := by
        rw [measure_univ, one_smul]

end Process

end

end MarkovProcess

end PortComputability

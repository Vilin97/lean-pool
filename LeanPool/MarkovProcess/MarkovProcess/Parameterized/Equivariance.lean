/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Parameterized.ContinuousProcess
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.Equivariance

/-!
# Equivariance of the parameterized continuous-path process

The equivariance theorem of `MarkovProcess/Trajectory/Equivariance.lean`, restated for a measurably
parameterized family of sub-Markov kernel semigroups.  Here the state map `e` and the time factor
`c` are accompanied by a measurable reparameterization `g` of the parameter space, and the
intertwining hypothesis is fibrewise:
`P' theta t x = ((P (g theta) (c * t)) (e.symm x)).map e`.

The conclusion is a single identity of kernels on `Theta × alpha`: the quenched continuous-path
process of `P'` is the quenched process of `P` pulled back along `(theta, x) ↦ (g theta, e.symm x)`
and pushed forward by `ContinuousPath.rescale e c`.  The proof is fibrewise, through the exact
fibre identity `IsConservative.continuousProcess_apply`.

Main results: `ParameterizedSubMarkovKernelSemigroup.IsRescaledConjugate` with its fibre form and
its transfers of conservativity and of the Kolmogorov moment criterion;
`IsConservative.continuousProcess_eq_map_rescale`, its pointwise form and its intrinsic form
`continuousProcess_eq_map_rescale_of_hasKolmogorovMoments`; the covariance corollary
`IsConservative.continuousProcess_covariant` for a family that is its own rescaled conjugate, of
which stationarity and re-gauging covariance of a random environment (`g` the environment shift,
`e` the spatial translation, `c = 1`) are instances.

No scaling limit and no ergodic statement is asserted: the environment map `g`, the factor `c`
and both families are given in advance, and nothing is claimed about the law of the environment.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

noncomputable section

section Measurability

variable {Theta alpha beta : Type*} [MeasurableSpace Theta] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [TopologicalSpace beta] [MeasurableSpace beta]
  [BorelSpace beta]

/-- The reparameterization of the parameter-and-state space used by the equivariance statement:
relabel the parameter by `g` and pull the starting state back along `e`. -/
theorem measurable_reparameterize {g : Theta → Theta} (hg : Measurable g) (e : alpha ≃ₜ beta) :
    Measurable (fun p : Theta × beta ↦ (g p.1, e.symm p.2)) :=
  (hg.comp measurable_fst).prodMk (e.symm.measurable.comp measurable_snd)

/-- `P'` is the *rescaled conjugate* of `P` along the reparameterization `g`, the homeomorphism `e`
and the time factor `c`: the fibre of `P'` at `theta` is the rescaled conjugate of the fibre of `P`
at `g theta`. -/
def IsRescaledConjugate (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (P' : ParameterizedSubMarkovKernelSemigroup Theta beta)
    (g : Theta → Theta) (e : alpha ≃ₜ beta) (c : NNReal) : Prop :=
  ∀ theta t x, P' theta t x = ((P (g theta) (c * t)) (e.symm x)).map e

namespace IsRescaledConjugate

variable {P : ParameterizedSubMarkovKernelSemigroup Theta alpha}
  {P' : ParameterizedSubMarkovKernelSemigroup Theta beta} {g : Theta → Theta}
  {e : alpha ≃ₜ beta} {c : NNReal}

omit [BorelSpace alpha] [BorelSpace beta] in
/-- The fibre form of the relation: at every parameter the corresponding slices of `P` and `P'`
are rescaled conjugates in the sense of `SubMarkovKernelSemigroup.IsRescaledConjugate`. -/
theorem fibre (h : IsRescaledConjugate P P' g e c) (theta : Theta) :
    SubMarkovKernelSemigroup.IsRescaledConjugate (P.toSubMarkovKernelSemigroup (g theta))
      (P'.toSubMarkovKernelSemigroup theta) e c :=
  fun t x ↦ h theta t x

/-- Fibrewise conservativity transfers across rescaled conjugacy. -/
theorem isConservative (h : IsRescaledConjugate P P' g e c) (hP : P.IsConservative) :
    P'.IsConservative :=
  fun theta ↦ (h.fibre theta).isConservative (hP (g theta))

end IsRescaledConjugate

end Measurability

section Moments

variable {Theta alpha beta : Type*} [MeasurableSpace Theta] [PseudoEMetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [PseudoEMetricSpace beta] [MeasurableSpace beta]
  [BorelSpace beta]
variable {P : ParameterizedSubMarkovKernelSemigroup Theta alpha}
  {P' : ParameterizedSubMarkovKernelSemigroup Theta beta} {g : Theta → Theta}
  {e : alpha ≃ₜ beta} {c : NNReal}

/-- **Fibrewise transfer of the Kolmogorov moment criterion.**  If the state map is an isometry,
the parameter-uniform displacement bound of `P` passes to its rescaled conjugate `P'` with the
constant multiplied by `c ^ q`, uniformly in the parameter. -/
theorem IsRescaledConjugate.hasKolmogorovMoments
    (h : IsRescaledConjugate P P' g e c) (he : Isometry (e : alpha → beta)) {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) : P'.HasKolmogorovMoments p q (M * c ^ q) :=
  fun theta ↦ (h.fibre theta).hasKolmogorovMoments he (hmom (g theta))

end Moments

section ContinuousProcess

variable {Theta alpha beta : Type*} [MeasurableSpace Theta] [MetricSpace alpha]
  [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha] [MetricSpace beta] [CompleteSpace beta]
  [MeasurableSpace beta] [BorelSpace beta] [SecondCountableTopology beta] [Nonempty beta]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
  (P' : ParameterizedSubMarkovKernelSemigroup Theta beta)
  (hP : P.IsConservative) (hP' : P'.IsConservative)

/-- **Equivariance of the parameterized continuous-path process.**  If the fibre of `P'` at every
parameter `theta` is the fibre of `P` at `g theta` conjugated by `e` and sped up by `c`, then the
quenched continuous-path process of `P'` is the quenched process of `P`, pulled back along
`(theta, x) ↦ (g theta, e.symm x)` and pushed forward by `ContinuousPath.rescale e c`.

Joint measurability in the parameter and the starting state is carried by the kernel structure on
both sides; the Feller hypothesis is needed only for `P`. -/
theorem IsConservative.continuousProcess_eq_map_rescale
    (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) (hK' : P'.KolmogorovRegular hP')
    {g : Theta → Theta} (hg : Measurable g) {e : alpha ≃ₜ beta} {c : NNReal} (hc : 0 < c)
    (h : IsRescaledConjugate P P' g e c) :
    IsConservative.continuousProcess P' hP' =
      (Kernel.comap (IsConservative.continuousProcess P hP)
          (fun p : Theta × beta ↦ (g p.1, e.symm p.2))
          (measurable_reparameterize hg e)).map (ContinuousPath.rescale e c) := by
  refine Kernel.ext fun p ↦ ?_
  obtain ⟨theta, x⟩ := p
  rw [IsConservative.continuousProcess_apply,
    Kernel.map_apply _ (ContinuousPath.measurable_rescale e c), Kernel.comap_apply,
    IsConservative.continuousProcess_apply]
  exact SubMarkovKernelSemigroup.IsConservative.continuousProcess_apply_rescale
    (P.toSubMarkovKernelSemigroup (g theta)) (hP (g theta))
    (P'.toSubMarkovKernelSemigroup theta) (hP' theta) (hFeller (g theta)) (hK (g theta))
    (hK' theta) hc (h.fibre theta) x

/-- The parameterized equivariance identity at a fixed parameter and starting state. -/
theorem IsConservative.continuousProcess_apply_rescale
    (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) (hK' : P'.KolmogorovRegular hP')
    {g : Theta → Theta} {e : alpha ≃ₜ beta} {c : NNReal} (hc : 0 < c)
    (h : IsRescaledConjugate P P' g e c) (theta : Theta) (x : beta) :
    IsConservative.continuousProcess P' hP' (theta, x) =
      (IsConservative.continuousProcess P hP (g theta, e.symm x)).map
        (ContinuousPath.rescale e c) := by
  rw [IsConservative.continuousProcess_apply, IsConservative.continuousProcess_apply]
  exact SubMarkovKernelSemigroup.IsConservative.continuousProcess_apply_rescale
    (P.toSubMarkovKernelSemigroup (g theta)) (hP (g theta))
    (P'.toSubMarkovKernelSemigroup theta) (hP' theta) (hFeller (g theta)) (hK (g theta))
    (hK' theta) hc (h.fibre theta) x

/-- **Intrinsic form of the parameterized equivariance theorem.**  When the state map is an
isometry, a parameter-uniform Kolmogorov moment bound on `P` alone supplies the fibrewise
regularity of both families. -/
theorem IsConservative.continuousProcess_eq_map_rescale_of_hasKolmogorovMoments
    (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)
    {p q : ℝ} {M : ℝ≥0} (hmom : P.HasKolmogorovMoments p q M)
    {g : Theta → Theta} (hg : Measurable g) {e : alpha ≃ₜ beta}
    (he : Isometry (e : alpha → beta)) {c : NNReal} (hc : 0 < c)
    (h : IsRescaledConjugate P P' g e c) :
    IsConservative.continuousProcess P' hP' =
      (Kernel.comap (IsConservative.continuousProcess P hP)
          (fun p : Theta × beta ↦ (g p.1, e.symm p.2))
          (measurable_reparameterize hg e)).map (ContinuousPath.rescale e c) :=
  IsConservative.continuousProcess_eq_map_rescale P P' hP hP' hFeller
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom)
    (KolmogorovRegular.of_hasKolmogorovMoments P' hP' (h.hasKolmogorovMoments he hmom)) hg hc h

/-- **Covariance.**  A parameterized family that is its own rescaled conjugate along `(g, e, c)`
has a quenched continuous-path process invariant under the corresponding transformation of the
parameter, the starting state and the path.  Stationarity and re-gauging covariance of a random
environment are the case `c = 1`, with `g` the environment shift and `e` the matching spatial
translation. -/
theorem IsConservative.continuousProcess_covariant
    (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP)
    {g : Theta → Theta} (hg : Measurable g) {e : alpha ≃ₜ alpha} {c : NNReal} (hc : 0 < c)
    (h : IsRescaledConjugate P P g e c) :
    IsConservative.continuousProcess P hP =
      (Kernel.comap (IsConservative.continuousProcess P hP)
          (fun p : Theta × alpha ↦ (g p.1, e.symm p.2))
          (measurable_reparameterize hg e)).map (ContinuousPath.rescale e c) :=
  IsConservative.continuousProcess_eq_map_rescale P P hP hP hFeller hK hK hg hc h

end ContinuousProcess

end

end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess

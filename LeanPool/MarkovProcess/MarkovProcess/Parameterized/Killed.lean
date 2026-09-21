/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Killed.Semigroup
import LeanPool.MarkovProcess.MarkovProcess.Parameterized.ContinuousProcessProperties

/-!
# The killed parameterized family

For a measurably parameterized family of conservative Feller semigroups and an open set `U`, the
processes of the fibres killed when they leave `U` again form a measurably parameterized family
of sub-Markov kernel semigroups on the carrier `U`: `killedFamily P hP U hU hFeller hK :
ParameterizedSubMarkovKernelSemigroup Theta U`, whose fibre at `theta` is the killed semigroup
`killedSemigroup` of `Killed/Semigroup.lean` for the semigroup at `theta`
(`killedFamily_toSubMarkovKernelSemigroup`, definitionally).  The only new content is the joint
measurability of the killed transition probabilities in the parameter, the time and the starting
point, `measurable_killedKernelOn_family`, which comes from the joint measurability of the
parameterized continuous-path process through the fibre identity.

The killed process on lifetime paths (with a cemetery state) is not constructed here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess.ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)

/-- The killed transition probabilities of the fibres are jointly measurable in the parameter, the
time and the starting point in `U`. -/
theorem IsConservative.measurable_killedKernelOn_family :
    Measurable fun q : Theta × (NNReal × U) ↦
      SubMarkovKernelSemigroup.IsConservative.killedKernelOn (P.toSubMarkovKernelSemigroup q.1)
        (hP q.1) U hU q.2.1 q.2.2 := by
  refine Measure.measurable_of_measurable_coe _ fun B hB ↦ ?_
  have hB' : MeasurableSet (Subtype.val '' B) :=
    (MeasurableEmbedding.subtype_coe hU.measurableSet).measurableSet_image.mpr hB
  have hfun : (fun q : Theta × (NNReal × U) ↦
      SubMarkovKernelSemigroup.IsConservative.killedKernelOn (P.toSubMarkovKernelSemigroup q.1)
        (hP q.1) U hU q.2.1 q.2.2 B) =
      fun q ↦ IsConservative.continuousProcess P hP (q.1, (q.2.2 : alpha))
        (ContinuousPath.killedEvent U q.2.1 (Subtype.val '' B)) := by
    funext q
    rw [SubMarkovKernelSemigroup.IsConservative.killedKernelOn_apply_eq_continuousProcess _ _ U hU
      _ _ hB, IsConservative.continuousProcess_apply]
  rw [hfun]
  have hg : Measurable fun q : Theta × (NNReal × U) ↦ (q.1, (q.2.2 : alpha)) :=
    measurable_fst.prodMk (measurable_subtype_coe.comp (measurable_snd.comp measurable_snd))
  have heval : Measurable fun p : NNReal × ContinuousPath alpha ↦ p.2 p.1 :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable
  have hS : MeasurableSet {p : (Theta × (NNReal × U)) × ContinuousPath alpha |
      (p.1.2.1 : ℝ≥0∞) < ContinuousPath.exitTime U p.2 ∧ p.2 p.1.2.1 ∈ Subtype.val '' B} := by
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_lt
        (measurable_coe_nnreal_ennreal.comp (measurable_fst.comp (measurable_snd.comp
            measurable_fst)))
        ((ContinuousPath.measurable_exitTime U hU).comp measurable_snd)
    · exact (heval.comp ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
        measurable_snd)) hB'
  exact Kernel.measurable_kernel_prodMk_left
    (κ := (IsConservative.continuousProcess P hP).comap _ hg) hS

variable [LocallyCompactSpace alpha]

/-- **The killed parameterized family**: the processes of the fibres killed when they leave the
open set `U`, as a measurably parameterized family of sub-Markov kernel semigroups on the carrier
`U`. -/
noncomputable def IsConservative.killedFamily
    (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) : ParameterizedSubMarkovKernelSemigroup Theta U where
  kernel theta t :=
    SubMarkovKernelSemigroup.IsConservative.killedKernelOn (P.toSubMarkovKernelSemigroup theta)
      (hP theta) U hU t
  measurable_kernel := IsConservative.measurable_killedKernelOn_family P hP U hU
  kernel_zero theta :=
    SubMarkovKernelSemigroup.IsConservative.killedKernelOn_zero _ _ U hU (hK theta)
  kernel_add theta :=
    SubMarkovKernelSemigroup.IsConservative.killedKernelOn_add _ _ U hU (hFeller theta) (hK theta)
  isSubMarkovKernel theta t :=
    SubMarkovKernelSemigroup.IsConservative.isSubMarkovKernel_killedKernelOn
      (P.toSubMarkovKernelSemigroup theta) (hP theta) U hU t

/-- The fibre at `theta` is the killed semigroup of the semigroup at that parameter. -/
theorem IsConservative.killedFamily_toSubMarkovKernelSemigroup
    (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) (theta : Theta) :
    (IsConservative.killedFamily P hP U hU hFeller hK).toSubMarkovKernelSemigroup theta =
      SubMarkovKernelSemigroup.IsConservative.killedSemigroup (P.toSubMarkovKernelSemigroup theta)
        (hP theta) U hU (hFeller theta) (hK theta) := rfl

/-- The transition probabilities of the killed family, as probabilities of path events of the
parameterized process. -/
theorem IsConservative.killedFamily_apply
    (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) (theta : Theta) (t : NNReal) (x : U) {B : Set U}
    (hB : MeasurableSet B) :
    IsConservative.killedFamily P hP U hU hFeller hK theta t x B =
      IsConservative.continuousProcess P hP (theta, x)
        (ContinuousPath.killedEvent U t (Subtype.val '' B)) := by
  change SubMarkovKernelSemigroup.IsConservative.killedKernelOn (P.toSubMarkovKernelSemigroup theta)
    (hP theta) U hU t x B = _
  rw [SubMarkovKernelSemigroup.IsConservative.killedKernelOn_apply_eq_continuousProcess _ _ U hU
    t x hB, IsConservative.continuousProcess_apply]

end MarkovProcess.ParameterizedSubMarkovKernelSemigroup

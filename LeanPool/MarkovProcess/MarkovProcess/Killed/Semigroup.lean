/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Killed.Kernel

/-!
# The killed semigroup on the domain

The killed kernels `killedKernel P hP U hU t` of `Killed/Kernel.lean` live on the whole state
space and are the identity only on `U` at time zero.  Restricting them to the carrier `U` (the
subtype, with its Borel sigma-algebra) gives kernels `killedKernelOn P hP U hU t : Kernel U U`
which do form a sub-Markov kernel semigroup, the **killed semigroup**
`killedSemigroup P hP U hU hFeller hK : SubMarkovKernelSemigroup U`:

  `killedSemigroup t x B = Q x {ω | t < τ_U(ω) ∧ ω t ∈ B}`  for `x ∈ U`, `B ⊆ U`.

The passage to the subtype uses that the killed kernels put no mass outside `U`
(`killedKernel_apply_compl`), so nothing is lost: `(killedKernelOn t x).map Subtype.val =
killedKernel t x` (`map_val_killedKernelOn`).  The Chapman--Kolmogorov law, joint measurability
and the sub-Markov bound transfer from the carrier `alpha`.

No Feller property, strong continuity, or regularity of the killed semigroup is claimed, and its
process is not identified with the cemetery-extended process on lifetime paths.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)

/-- The killed kernels put no mass outside `U`: a path still inside `U` at time `t` is at a point
of `U` at time `t`. -/
theorem IsConservative.killedKernel_apply_compl (t : NNReal) (x : alpha) :
    IsConservative.killedKernel P hP U hU t x Uᶜ = 0 := by
  rw [IsConservative.killedKernel_apply P hP U hU t x hU.measurableSet.compl]
  have hempty : ContinuousPath.killedEvent U t Uᶜ = ∅ := by
    ext omega
    simp only [ContinuousPath.mem_killedEvent_iff, Set.mem_compl_iff, Set.mem_empty_iff_false,
      iff_false, not_and, not_not]
    exact fun h ↦ ContinuousPath.mem_of_lt_exitTime U omega t h
  rw [hempty, measure_empty]

/-- Almost every point under a killed kernel lies in `U`. -/
theorem IsConservative.ae_mem_killedKernel (t : NNReal) (x : alpha) :
    ∀ᵐ y ∂(IsConservative.killedKernel P hP U hU t x), y ∈ U :=
  (ae_iff).mpr (IsConservative.killedKernel_apply_compl P hP U hU t x)

/-- The killed transition kernel at time `t`, on the carrier `U`. -/
noncomputable def IsConservative.killedKernelOn (t : NNReal) : Kernel U U :=
  Kernel.comapRight
    (Kernel.comap (IsConservative.killedKernel P hP U hU t) Subtype.val measurable_subtype_coe)
    (MeasurableEmbedding.subtype_coe hU.measurableSet)

/-- The killed kernel on `U` is the pullback of the killed kernel on `alpha` along the inclusion. -/
theorem IsConservative.killedKernelOn_apply_eq (t : NNReal) (x : U) :
    IsConservative.killedKernelOn P hP U hU t x =
      (IsConservative.killedKernel P hP U hU t x).comap Subtype.val := by
  rw [IsConservative.killedKernelOn, Kernel.comapRight_apply, Kernel.comap_apply]

/-- The killed kernel on `U` evaluated on a measurable set of `U`. -/
theorem IsConservative.killedKernelOn_apply (t : NNReal) (x : U) {B : Set U}
    (hB : MeasurableSet B) :
    IsConservative.killedKernelOn P hP U hU t x B =
      IsConservative.killedKernel P hP U hU t x (Subtype.val '' B) := by
  rw [IsConservative.killedKernelOn, Kernel.comapRight_apply' _ _ _ hB, Kernel.comap_apply]

/-- The killed kernel on `U`, evaluated on a set, as a probability of the path event. -/
theorem IsConservative.killedKernelOn_apply_eq_continuousProcess (t : NNReal) (x : U)
    {B : Set U} (hB : MeasurableSet B) :
    IsConservative.killedKernelOn P hP U hU t x B =
      IsConservative.continuousProcess P hP x
        (ContinuousPath.killedEvent U t (Subtype.val '' B)) := by
  rw [IsConservative.killedKernelOn_apply P hP U hU t x hB,
    IsConservative.killedKernel_apply P hP U hU t x
      ((MeasurableEmbedding.subtype_coe hU.measurableSet).measurableSet_image.mpr hB)]

/-- Pushing the killed kernel on `U` forward along the inclusion recovers the killed kernel on
`alpha`. -/
theorem IsConservative.map_val_killedKernelOn (t : NNReal) (x : U) :
    (IsConservative.killedKernelOn P hP U hU t x).map Subtype.val =
      IsConservative.killedKernel P hP U hU t x := by
  rw [IsConservative.killedKernelOn_apply_eq,
    (MeasurableEmbedding.subtype_coe hU.measurableSet).map_comap, Subtype.range_val]
  exact Measure.restrict_eq_self_of_ae_mem (IsConservative.ae_mem_killedKernel P hP U hU t x)

/-- The total mass of the killed kernel on `U` is the survival probability. -/
theorem IsConservative.killedKernelOn_apply_univ (t : NNReal) (x : U) :
    IsConservative.killedKernelOn P hP U hU t x Set.univ =
      IsConservative.killedKernel P hP U hU t x U := by
  rw [IsConservative.killedKernelOn_apply P hP U hU t x MeasurableSet.univ, Set.image_univ,
    Subtype.range_val]

/-- The killed kernels on `U` are sub-Markov. -/
theorem IsConservative.isSubMarkovKernel_killedKernelOn (t : NNReal) :
    IsSubMarkovKernel (IsConservative.killedKernelOn P hP U hU t) := by
  intro x
  rw [IsConservative.killedKernelOn_apply_univ]
  exact (IsConservative.isSubMarkovKernel_killedKernel P hP U hU t).measure_le_one x U

/-- The killed kernels on `U` are jointly measurable in time and starting point. -/
theorem IsConservative.measurable_killedKernelOn :
    Measurable fun q : NNReal × U ↦ IsConservative.killedKernelOn P hP U hU q.1 q.2 := by
  refine Measure.measurable_of_measurable_coe _ fun B hB ↦ ?_
  have hfun : (fun q : NNReal × U ↦ IsConservative.killedKernelOn P hP U hU q.1 q.2 B) =
      fun q ↦ IsConservative.killedKernel P hP U hU q.1 q.2 (Subtype.val '' B) :=
    funext fun q ↦ IsConservative.killedKernelOn_apply P hP U hU q.1 q.2 hB
  rw [hfun]
  have hB' : MeasurableSet (Subtype.val '' B) :=
    (MeasurableEmbedding.subtype_coe hU.measurableSet).measurableSet_image.mpr hB
  exact (Measure.measurable_coe hB').comp ((IsConservative.measurable_killedKernel P hP U hU).comp
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)))

/-- At time zero the killed kernel on `U` is the identity kernel of `U`. -/
theorem IsConservative.killedKernelOn_zero (hK : P.KolmogorovRegular hP) :
    IsConservative.killedKernelOn P hP U hU 0 = Kernel.id := by
  refine Kernel.ext fun x ↦ Measure.ext fun B hB ↦ ?_
  have hB' : MeasurableSet (Subtype.val '' B) :=
    (MeasurableEmbedding.subtype_coe hU.measurableSet).measurableSet_image.mpr hB
  rw [IsConservative.killedKernelOn_apply P hP U hU 0 x hB, IsConservative.killedKernel_zero P
      hP U hU hK,
    Kernel.restrict_apply' _ _ _ hB', Kernel.id_apply, Kernel.id_apply,
    Measure.dirac_apply' _ (hB'.inter hU.measurableSet), Measure.dirac_apply' _ hB]
  rw [Set.inter_eq_left.mpr (Subtype.coe_image_subset U B),
    Set.indicator_image Subtype.val_injective]
  rfl

variable [LocallyCompactSpace alpha]

/-- **Chapman--Kolmogorov law for the killed kernels on `U`.** -/
theorem IsConservative.killedKernelOn_add (hFeller : P.IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) (s t : NNReal) :
    IsConservative.killedKernelOn P hP U hU (s + t) =
      (IsConservative.killedKernelOn P hP U hU t).comp
        (IsConservative.killedKernelOn P hP U hU s) := by
  refine Kernel.ext fun x ↦ Measure.ext fun B hB ↦ ?_
  have hB' : MeasurableSet (Subtype.val '' B) :=
    (MeasurableEmbedding.subtype_coe hU.measurableSet).measurableSet_image.mpr hB
  have hfun : (fun y : U ↦ IsConservative.killedKernelOn P hP U hU t y B) =
      fun y : U ↦ IsConservative.killedKernel P hP U hU t (y : alpha) (Subtype.val '' B) :=
    funext fun y ↦ IsConservative.killedKernelOn_apply P hP U hU t y hB
  rw [IsConservative.killedKernelOn_apply P hP U hU (s + t) x hB,
    IsConservative.killedKernel_add P hP U hU hFeller hK s t, Kernel.comp_apply' _ _ _ hB',
    Kernel.comp_apply' _ _ _ hB, hfun, ← IsConservative.map_val_killedKernelOn P hP U hU s x,
    (MeasurableEmbedding.subtype_coe hU.measurableSet).lintegral_map]

/-- **The killed semigroup on the domain `U`**: the process of `P` killed when it leaves `U`, as a
sub-Markov kernel semigroup on the carrier `U`. -/
noncomputable def IsConservative.killedSemigroup (hFeller : P.IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) : SubMarkovKernelSemigroup U where
  kernel := IsConservative.killedKernelOn P hP U hU
  measurable_kernel := IsConservative.measurable_killedKernelOn P hP U hU
  kernel_zero := IsConservative.killedKernelOn_zero P hP U hU hK
  kernel_add := IsConservative.killedKernelOn_add P hP U hU hFeller hK
  isSubMarkovKernel := IsConservative.isSubMarkovKernel_killedKernelOn P hP U hU

/-- The transition kernels of the killed semigroup are the killed kernels on `U`. -/
theorem IsConservative.killedSemigroup_apply (hFeller : P.IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) (t : NNReal) :
    IsConservative.killedSemigroup P hP U hU hFeller hK t =
      IsConservative.killedKernelOn P hP U hU t := rfl

/-- The killed semigroup evaluated on a set: the probability that the process started at `x ∈ U`
is still in `U` at time `t` and sits in `B` at time `t`. -/
theorem IsConservative.killedSemigroup_apply_apply (hFeller : P.IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) (t : NNReal) (x : U) {B : Set U} (hB : MeasurableSet B) :
    IsConservative.killedSemigroup P hP U hU hFeller hK t x B =
      IsConservative.continuousProcess P hP x
        (ContinuousPath.killedEvent U t (Subtype.val '' B)) :=
  IsConservative.killedKernelOn_apply_eq_continuousProcess P hP U hU t x hB

end MarkovProcess.SubMarkovKernelSemigroup

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Main
import LeanPool.MarkovProcess.MarkovProcess.Path.ExitTimeShift

/-!
# The process killed at the exit time of an open set: transition kernels

For the continuous-path process `Q = continuousProcess P hP` of a conservative Feller semigroup
and an open set `U`, the transition kernel at time `t` of the process **killed when it leaves
`U`** is

  `killedKernel P hP U hU t x B = Q x {ω | t < exitTime U ω ∧ ω t ∈ B}`,

the law of the position at time `t` restricted to the survival event `{t < τ_U}`.  This file
proves that these kernels are sub-Markov (`isSubMarkovKernel_killedKernel`), jointly measurable
in time and starting point (`measurable_killedKernel`), vanish off `U`
(`killedKernel_apply_of_notMem`), reduce at time zero to the identity restricted to `U`
(`killedKernel_zero`), and satisfy the Chapman--Kolmogorov law `killedKernel_add`,

  `killedKernel (s + t) = killedKernel t ∘ₖ killedKernel s`,

which follows from the Markov property of `Q` at the deterministic time `s` on the
`𝓕_s`-event `{s < τ_U}` together with the path identity `{s + t < τ} = {s < τ} ∩ {t < τ ∘ θ_s}`.

On the carrier `alpha` the family is not a `SubMarkovKernelSemigroup`, because at time zero it is
the identity only on `U` (it is `0` off `U`); the semigroup structure on the carrier `U` is a
separate packaging.  No Feller property of the killed family is claimed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- The event that a path is still inside `U` at time `t` and sits in `B` at time `t`. -/
def killedEvent (U : Set alpha) (t : NNReal) (B : Set alpha) : Set (ContinuousPath alpha) :=
  {omega | (t : ℝ≥0∞) < exitTime U omega ∧ omega t ∈ B}

/-- Membership in the killed event, unfolded. -/
theorem mem_killedEvent_iff (U : Set alpha) (t : NNReal) (B : Set alpha)
    (omega : ContinuousPath alpha) :
    omega ∈ killedEvent U t B ↔ (t : ℝ≥0∞) < exitTime U omega ∧ omega t ∈ B :=
  Iff.rfl

/-- The killed event of the whole space is the survival event. -/
theorem killedEvent_univ (U : Set alpha) (t : NNReal) :
    killedEvent U t Set.univ = {omega | (t : ℝ≥0∞) < exitTime U omega} := by
  ext omega
  simp only [mem_killedEvent_iff, Set.mem_univ, and_true, Set.mem_ofPred_eq]

/-- The killed event at time `s + t` is the survival event at time `s` intersected with the
killed event at time `t` of the path shifted by `s`. -/
theorem killedEvent_add (U : Set alpha) (s t : NNReal) (B : Set alpha) :
    killedEvent U (s + t) B =
      shift s ⁻¹' killedEvent U t B ∩ {omega | (s : ℝ≥0∞) < exitTime U omega} := by
  ext omega
  simp only [mem_killedEvent_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
    shift_apply]
  constructor
  · rintro ⟨hlt, hmem⟩
    obtain ⟨hs, ht⟩ := (coe_add_lt_exitTime_iff U omega s t).mp hlt
    exact ⟨⟨ht, hmem⟩, hs⟩
  · rintro ⟨⟨ht, hmem⟩, hs⟩
    exact ⟨(coe_add_lt_exitTime_iff U omega s t).mpr ⟨hs, ht⟩, hmem⟩

variable [MeasurableSpace alpha] [BorelSpace alpha]

/-- The killed event of a measurable set is measurable. -/
theorem measurableSet_killedEvent (U : Set alpha) (hU : IsOpen U) (t : NNReal) {B : Set alpha}
    (hB : MeasurableSet B) : MeasurableSet (killedEvent U t B) :=
  (measurableSet_lt_exitTime U hU t).inter
    ((measurable_coordinateProcess (alpha := alpha) t) hB)

omit [MeasurableSpace alpha] [BorelSpace alpha] in
/-- A path is inside an open set `U` at time zero exactly when its exit time from `U` is
positive. -/
theorem exitTime_pos_iff (U : Set alpha) (hU : IsOpen U) (omega : ContinuousPath alpha) :
    0 < exitTime U omega ↔ omega 0 ∈ U := by
  constructor
  · intro h
    exact mem_of_lt_exitTime U omega 0 (by rwa [ENNReal.coe_zero])
  · intro h
    by_contra hle
    rw [not_lt, ← ENNReal.coe_zero, exitTime_le_iff_mem_hitsSetBy U hU 0 omega] at hle
    obtain ⟨s, hs⟩ := hle
    have hs0 : (s : NNReal) = 0 := le_antisymm (Set.mem_Iic.mp s.2) zero_le
    rw [hs0] at hs
    exact hs h

end ContinuousPath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)

/-- The transition kernel at time `t` of the continuous-path process of `P` killed when it leaves
the open set `U`: the law of the position at time `t`, restricted to the event that the path has
not yet left `U`. -/
noncomputable def IsConservative.killedKernel (t : NNReal) : Kernel alpha alpha :=
  Kernel.map ((IsConservative.continuousProcess P hP).restrict
    (ContinuousPath.measurableSet_lt_exitTime U hU t)) (fun omega ↦ omega t)

/-- The killed kernel at time `t` started at `x` is the image of the law of the process, restricted
to the survival event `{t < τ_U}`, under evaluation at time `t`. -/
theorem IsConservative.killedKernel_eq_map (t : NNReal) (x : alpha) :
    IsConservative.killedKernel P hP U hU t x =
      ((IsConservative.continuousProcess P hP x).restrict
        {omega | (t : ℝ≥0∞) < ContinuousPath.exitTime U omega}).map (fun omega ↦ omega t) := by
  have hmeas : Measurable (fun omega : ContinuousPath alpha ↦ omega t) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) t
  rw [IsConservative.killedKernel, Kernel.map_apply _ hmeas, Kernel.restrict_apply]

/-- The killed kernel evaluated on a measurable set: the probability that the process is still in
`U` at time `t` and sits in `B` at time `t`. -/
theorem IsConservative.killedKernel_apply (t : NNReal) (x : alpha) {B : Set alpha}
    (hB : MeasurableSet B) :
    IsConservative.killedKernel P hP U hU t x B =
      IsConservative.continuousProcess P hP x (ContinuousPath.killedEvent U t B) := by
  have hmeas : Measurable (fun omega : ContinuousPath alpha ↦ omega t) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) t
  rw [IsConservative.killedKernel_eq_map, Measure.map_apply hmeas hB,
    Measure.restrict_apply (hmeas hB)]
  congr 1
  ext omega
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
    ContinuousPath.mem_killedEvent_iff]
  exact and_comm

/-- The total mass of the killed kernel is the survival probability `Q x {t < τ_U}`. -/
theorem IsConservative.killedKernel_apply_univ (t : NNReal) (x : alpha) :
    IsConservative.killedKernel P hP U hU t x Set.univ =
      IsConservative.continuousProcess P hP x
        {omega | (t : ℝ≥0∞) < ContinuousPath.exitTime U omega} := by
  rw [IsConservative.killedKernel_apply P hP U hU t x MeasurableSet.univ,
    ContinuousPath.killedEvent_univ]

/-- The killed kernels are sub-Markov. -/
theorem IsConservative.isSubMarkovKernel_killedKernel (t : NNReal) :
    IsSubMarkovKernel (IsConservative.killedKernel P hP U hU t) := by
  intro x
  rw [IsConservative.killedKernel_apply_univ]
  exact prob_le_one

/-- The killed kernels are jointly measurable in the time and the starting point. -/
theorem IsConservative.measurable_killedKernel :
    Measurable fun q : NNReal × alpha ↦ IsConservative.killedKernel P hP U hU q.1 q.2 := by
  refine Measure.measurable_of_measurable_coe _ fun B hB ↦ ?_
  have hfun : (fun q : NNReal × alpha ↦ IsConservative.killedKernel P hP U hU q.1 q.2 B) =
      fun q ↦ IsConservative.continuousProcess P hP q.2 (ContinuousPath.killedEvent U q.1 B) :=
    funext fun q ↦ IsConservative.killedKernel_apply P hP U hU q.1 q.2 hB
  rw [hfun]
  have heval : Measurable fun p : NNReal × ContinuousPath alpha ↦ p.2 p.1 :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable
  have hS : MeasurableSet {p : (NNReal × alpha) × ContinuousPath alpha |
      (p.1.1 : ℝ≥0∞) < ContinuousPath.exitTime U p.2 ∧ p.2 p.1.1 ∈ B} := by
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_lt (measurable_coe_nnreal_ennreal.comp measurable_fst.fst)
        ((ContinuousPath.measurable_exitTime U hU).comp measurable_snd)
    · exact (heval.comp (measurable_fst.fst.prodMk measurable_snd)) hB
  exact Kernel.measurable_kernel_prodMk_left
    (κ := Kernel.prodMkLeft NNReal (IsConservative.continuousProcess P hP)) hS

/-- Off `U` the killed kernels vanish: a path started outside `U` has exit time zero. -/
theorem IsConservative.killedKernel_apply_of_notMem (hK : P.KolmogorovRegular hP) (t : NNReal)
    {x : alpha} (hx : x ∉ U) : IsConservative.killedKernel P hP U hU t x = 0 := by
  have hmeas0 : Measurable (fun omega : ContinuousPath alpha ↦ omega 0) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) 0
  have hzero : IsConservative.continuousProcess P hP x {omega | omega 0 ∈ U} = 0 := by
    have h := congrArg (fun mu : Measure alpha ↦ mu U)
      (IsConservative.continuousProcess_map_eval_zero P hP hK ▸ rfl :
        (IsConservative.continuousProcess P hP).map (fun omega ↦ omega 0) x = Kernel.id x)
    rw [Kernel.map_apply _ hmeas0, Measure.map_apply hmeas0 hU.measurableSet, Kernel.id_apply,
      Measure.dirac_apply' x hU.measurableSet, Set.indicator_of_notMem hx] at h
    exact h
  refine Measure.ext fun B hB ↦ ?_
  rw [IsConservative.killedKernel_apply P hP U hU t x hB, Measure.coe_zero, Pi.zero_apply]
  refine measure_mono_null (fun omega homega ↦ ?_) hzero
  obtain ⟨hlt, -⟩ := (ContinuousPath.mem_killedEvent_iff U t B omega).mp homega
  exact (ContinuousPath.exitTime_pos_iff U hU omega).mp (lt_of_le_of_lt zero_le hlt)

/-- At time zero the killed kernel is the identity kernel restricted to `U`: the Dirac mass at the
starting point if it lies in `U`, and zero otherwise. -/
theorem IsConservative.killedKernel_zero (hK : P.KolmogorovRegular hP) :
    IsConservative.killedKernel P hP U hU 0 = Kernel.id.restrict hU.measurableSet := by
  have hmeas0 : Measurable (fun omega : ContinuousPath alpha ↦ omega 0) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) 0
  refine Kernel.ext fun x ↦ Measure.ext fun B hB ↦ ?_
  have hevent : ContinuousPath.killedEvent U 0 B = (fun omega : ContinuousPath alpha ↦ omega 0) ⁻¹'
      (B ∩ U) := by
    ext omega
    simp only [ContinuousPath.mem_killedEvent_iff, ENNReal.coe_zero, Set.mem_preimage,
      Set.mem_inter_iff, ContinuousPath.exitTime_pos_iff U hU]
    exact and_comm
  rw [IsConservative.killedKernel_apply P hP U hU 0 x hB, hevent,
    ← Measure.map_apply hmeas0 (hB.inter hU.measurableSet), ← Kernel.map_apply _ hmeas0,
    IsConservative.continuousProcess_map_eval_zero P hP hK, Kernel.restrict_apply' _ _ _ hB]

variable [LocallyCompactSpace alpha]

/-- **Chapman--Kolmogorov law for the killed kernels**: `killedKernel (s + t) = killedKernel t ∘ₖ
killedKernel s`.  It follows from the Markov property of the process at the deterministic time `s`
on the `𝓕_s`-event `{s < τ_U}`, and the path identity `{s + t < τ_U} = {s < τ_U} ∩ {t < τ_U ∘
    θ_s}`. -/
theorem IsConservative.killedKernel_add (hFeller : P.IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) (s t : NNReal) :
    IsConservative.killedKernel P hP U hU (s + t) =
      (IsConservative.killedKernel P hP U hU t).comp (IsConservative.killedKernel P hP U hU s) := by
  refine Kernel.ext fun x ↦ Measure.ext fun B hB ↦ ?_
  have hmeas_s : Measurable (fun omega : ContinuousPath alpha ↦ omega s) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) s
  have hE : MeasurableSet (ContinuousPath.killedEvent U t B) :=
    ContinuousPath.measurableSet_killedEvent U hU t hB
  have hA := ContinuousPath.measurableSet_lt_exitTime_canonicalFiltration U hU s
  have hrestart := congrArg (fun mu : Measure (ContinuousPath alpha) ↦
      mu (ContinuousPath.killedEvent U t B))
    (hFeller.continuousProcess_restrict_map_shift P hP hK x s _ hA)
  rw [Measure.map_apply (ContinuousPath.measurable_shift_fixed s) hE,
    Measure.restrict_apply ((ContinuousPath.measurable_shift_fixed s) hE),
    Measure.bind_apply hE (Kernel.aemeasurable _)] at hrestart
  have hfun : (fun y ↦ IsConservative.killedKernel P hP U hU t y B) =
      fun y ↦ IsConservative.continuousProcess P hP y (ContinuousPath.killedEvent U t B) :=
    funext fun y ↦ IsConservative.killedKernel_apply P hP U hU t y hB
  rw [Kernel.comp_apply' _ _ _ hB, hfun, IsConservative.killedKernel_apply P hP U hU (s + t) x hB,
    IsConservative.killedKernel_eq_map P hP U hU s x,
    lintegral_map ((IsConservative.continuousProcess P hP).measurable_coe hE) hmeas_s,
    ContinuousPath.killedEvent_add]
  exact hrestart

end SubMarkovKernelSemigroup

end MarkovProcess

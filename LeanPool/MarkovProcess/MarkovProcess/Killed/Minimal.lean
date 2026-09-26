/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Killed.Kernel
public import LeanPool.MarkovProcess.MarkovProcess.Path.Exhaustion
public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.Dynkin


/-!
# The semigroup as the limit of its killed parts

Along an open exhaustion `U n ↑ α` of the state space, the killed kernels increase to the
transition kernels of the semigroup: for every time `t`, starting point `x` and measurable set
`B`,

  `⨆ n, killedKernel P hP (U n) _ t x B = P t x B`   (`iSup_killedKernel_apply`),

and the survival probabilities `Q x {t < τ_{U n}}` increase to one. This is the statement that the
whole-space semigroup is the minimal semigroup of its killed parts; it rests on the path-space
fact that exit times along an exhaustion tend to infinity (`Path/Exhaustion.lean`), so the
killed events increase to the whole event `{ω t ∈ B}`.

The killed kernels are monotone in the open set (`killedKernel_mono`); no other structure is
used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- Killed events are monotone in the set. -/
theorem killedEvent_mono {U V : Set alpha} (hUV : U ⊆ V) (t : NNReal) (B : Set alpha) :
    killedEvent U t B ⊆ killedEvent V t B := by
  rintro omega ⟨hlt, hmem⟩
  exact ⟨lt_of_lt_of_le hlt (exitTime_mono hUV omega), hmem⟩

/-- Along an open exhaustion, the killed events increase to the event that the path is in `B` at
time `t`. -/
theorem IsOpenExhaustion.iUnion_killedEvent {U : ℕ → Set alpha} (hU : IsOpenExhaustion U)
    (t : NNReal) (B : Set alpha) :
    ⋃ n, killedEvent (U n) t B = {omega : ContinuousPath alpha | omega t ∈ B} := by
  ext omega
  simp only [Set.mem_iUnion, mem_killedEvent_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n, -, hmem⟩
    exact hmem
  · intro hmem
    obtain ⟨N, hN⟩ := hU.exists_lt_exitTime omega t
    exact ⟨N, hN N le_rfl, hmem⟩

/-- Along an open exhaustion, the survival events increase to the whole space. -/
theorem IsOpenExhaustion.iUnion_lt_exitTime {U : ℕ → Set alpha} (hU : IsOpenExhaustion U)
    (t : NNReal) :
    ⋃ n, {omega : ContinuousPath alpha | (t : ℝ≥0∞) < exitTime (U n) omega} = Set.univ := by
  ext omega
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  obtain ⟨N, hN⟩ := hU.exists_lt_exitTime omega t
  exact ⟨N, hN N le_rfl⟩

end ContinuousPath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- The killed kernels are monotone in the open set. -/
theorem IsConservative.killedKernel_mono {U V : Set alpha} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ⊆ V) (t : NNReal) (x : alpha) {B : Set alpha} (hB : MeasurableSet B) :
    IsConservative.killedKernel P hP U hU t x B ≤ IsConservative.killedKernel P hP V hV t x B := by
  rw [IsConservative.killedKernel_apply P hP U hU t x hB,
    IsConservative.killedKernel_apply P hP V hV t x hB]
  exact measure_mono (ContinuousPath.killedEvent_mono hUV t B)

/-- Along an open exhaustion, the survival probabilities increase to one. -/
theorem IsConservative.iSup_measure_lt_exitTime {U : ℕ → Set alpha}
    (hU : ContinuousPath.IsOpenExhaustion U) (t : NNReal) (x : alpha) :
    ⨆ n, IsConservative.continuousProcess P hP x
      {omega | (t : ℝ≥0∞) < ContinuousPath.exitTime (U n) omega} = 1 := by
  have hmono : Monotone fun n ↦
      {omega : ContinuousPath alpha | (t : ℝ≥0∞) < ContinuousPath.exitTime (U n) omega} :=
    fun m n hmn omega h ↦
      lt_of_lt_of_le h (ContinuousPath.exitTime_mono (hU.monotone hmn) omega)
  rw [← Monotone.measure_iUnion hmono, hU.iUnion_lt_exitTime t, measure_univ]

variable [LocallyCompactSpace alpha]

/-- **The semigroup is the limit of its killed parts.**  Along an open exhaustion, the killed
kernels increase to the transition kernels of the semigroup. -/
theorem IsFellerKernelSemigroup.iSup_killedKernel_apply (hFeller : P.IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) {U : ℕ → Set alpha} (hU : ContinuousPath.IsOpenExhaustion U)
    (t : NNReal) (x : alpha) {B : Set alpha} (hB : MeasurableSet B) :
    ⨆ n, IsConservative.killedKernel P hP (U n) (hU.isOpen n) t x B = P t x B := by
  have hmeas : Measurable (fun omega : ContinuousPath alpha ↦ omega t) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) t
  have hmono : Monotone fun n ↦ ContinuousPath.killedEvent (U n) t B :=
    fun m n hmn ↦ ContinuousPath.killedEvent_mono (hU.monotone hmn) t B
  simp_rw [IsConservative.killedKernel_apply P hP _ _ t x hB]
  rw [← Monotone.measure_iUnion hmono, hU.iUnion_killedEvent t B]
  change IsConservative.continuousProcess P hP x
    ((fun omega : ContinuousPath alpha ↦ omega t) ⁻¹' B) = _
  rw [← Measure.map_apply hmeas hB, ← Kernel.map_apply _ hmeas,
    hFeller.continuousProcess_map_eval_nnreal P hP hK t]

end SubMarkovKernelSemigroup

end MarkovProcess

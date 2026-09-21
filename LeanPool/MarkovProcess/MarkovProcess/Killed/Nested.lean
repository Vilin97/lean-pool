/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Killed.Marginals
import LeanPool.MarkovProcess.MarkovProcess.Lifetime.ExitTimeStopping
import LeanPool.MarkovProcess.MarkovProcess.Path.Exhaustion

/-!
# Nested domains: killing at the exit of a smaller set

For two sets `U ⊆ V` the path killed at the exit of `U` is the path killed at the exit of `V`,
killed once more at the exit of `U`.  This file proves that relation on path space and transports
it to the killed processes.

* `ContinuousPath.exitTime_mono`: a path leaves a smaller set no later;
* `LifetimePath.killedCoordinate W t`: the coordinate at time `t` of a lifetime path killed once
  more at the exit of `W`, together with its two coordinate formulas and its measurability for an
  open `W` (`LifetimePath.measurable_killedCoordinate`), which rests on the measurability of the
  lifetime-path exit time `LifetimePath.measurable_exitTime` proved here;
* `ContinuousPath.lifetimePath_exitTime_killAtExit`: the first time the `V`-killed path is not a
  live point of `U` is the exit time of `U`, that is, the lifetime of the `U`-killed path;
* `ContinuousPath.killedCoordinate_killAtExit`: killing the `V`-killed path once more at the exit
  of `U` reads, at every time, the coordinate of the `U`-killed path through the inclusion of `U`
  in `V`;
* `killedProcess_map_exitTime` and `killedProcess_map_killedCoordinates`: the same two statements
  for the laws, and finally `killedProcess_map_killedFinsetCoordinates`, the part-process property
  at the level of the finite-dimensional distributions: the process of `V` killed again at the
  exit of `U` has the finite-dimensional distributions of the cemetery extension of the killed
  semigroup on `U`.

The carriers of the two killed processes are the subtypes `U` and `V`, which are different types;
the statements here compare them through the inclusion of `U` in `V` rather than identifying the
two killed processes as laws on a common carrier.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess

namespace LifetimePath

section Killing

variable {beta : Type*} [PseudoMetricSpace beta]

/-- The coordinate at time `t` of a lifetime path killed once more at the exit of `W`: the
coordinate of the path strictly before the first time it is not a live point of `W`, and the
cemetery state from that time on. -/
noncomputable def killedCoordinate (W : Set beta) (t : NNReal) (eta : LifetimePath beta) :
    Cemetery beta :=
  if (t : ℝ≥0∞) < exitTime W eta then coordinate t eta else Cemetery.delta

/-- Before the exit time of `W`, killing again at the exit of `W` changes no coordinate. -/
theorem killedCoordinate_of_lt (W : Set beta) (t : NNReal) (eta : LifetimePath beta)
    (ht : (t : ℝ≥0∞) < exitTime W eta) :
    killedCoordinate W t eta = coordinate t eta :=
  ite_eq_left ht

/-- From the exit time of `W` on, the path killed again at the exit of `W` is at the cemetery. -/
theorem killedCoordinate_of_le (W : Set beta) (t : NNReal) (eta : LifetimePath beta)
    (ht : exitTime W eta ≤ (t : ℝ≥0∞)) :
    killedCoordinate W t eta = Cemetery.delta :=
  ite_eq_right (not_lt.mpr ht)

end Killing

section MeasurableExitTime

variable {beta : Type*} [PseudoMetricSpace beta] [MeasurableSpace beta] [BorelSpace beta]

/-- The exit time from an open set is a Borel function on lifetime-path space: it is a stopping
time for the canonical filtration, and the filtration is contained in the measurable structure. -/
theorem measurable_exitTime (W : Set beta) (hW : IsOpen W) :
    Measurable (exitTime W : LifetimePath beta → ℝ≥0∞) := by
  refine measurable_of_Iic fun a ↦ ?_
  induction a with
  | top =>
      have h : (exitTime W : LifetimePath beta → ℝ≥0∞) ⁻¹' Set.Iic ⊤ = Set.univ := by
        ext eta
        simp only [Set.mem_preimage, Set.mem_Iic, le_top, Set.mem_univ]
      rw [h]
      exact MeasurableSet.univ
  | coe t =>
      exact (canonicalFiltration (alpha := beta)).le t _ (isStoppingTime_exitTime W hW t)

/-- Every coordinate of a lifetime path killed again at the exit of an open set is measurable. -/
theorem measurable_killedCoordinate (W : Set beta) (hW : IsOpen W) (t : NNReal) :
    Measurable (killedCoordinate W t) := by
  intro S hS
  have hA : MeasurableSet {eta : LifetimePath beta | (t : ℝ≥0∞) < exitTime W eta} :=
    measurable_exitTime W hW measurableSet_Ioi
  by_cases hdelta : (Cemetery.delta : Cemetery beta) ∈ S
  · have hpre : killedCoordinate W t ⁻¹' S =
        ({eta : LifetimePath beta | (t : ℝ≥0∞) < exitTime W eta} ∩ coordinate t ⁻¹' S) ∪
          {eta : LifetimePath beta | (t : ℝ≥0∞) < exitTime W eta}ᶜ := by
      ext eta
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq,
        Set.mem_compl_iff, killedCoordinate]
      by_cases hlt : (t : ℝ≥0∞) < exitTime W eta
      · rw [ite_eq_left hlt]
        exact ⟨fun h ↦ Or.inl ⟨hlt, h⟩, fun h ↦ h.elim (fun h ↦ h.2) fun h ↦ absurd hlt h⟩
      · rw [ite_eq_right hlt]
        exact ⟨fun _ ↦ Or.inr hlt, fun _ ↦ hdelta⟩
    rw [hpre]
    exact (hA.inter (measurable_coordinate t hS)).union hA.compl
  · have hpre : killedCoordinate W t ⁻¹' S =
        {eta : LifetimePath beta | (t : ℝ≥0∞) < exitTime W eta} ∩ coordinate t ⁻¹' S := by
      ext eta
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, killedCoordinate]
      by_cases hlt : (t : ℝ≥0∞) < exitTime W eta
      · rw [ite_eq_left hlt]
        exact ⟨fun h ↦ ⟨hlt, h⟩, fun h ↦ h.2⟩
      · rw [ite_eq_right hlt]
        exact ⟨fun h ↦ absurd h hdelta, fun h ↦ absurd h.1 hlt⟩
    rw [hpre]
    exact hA.inter (measurable_coordinate t hS)

end MeasurableExitTime

end LifetimePath

namespace ContinuousPath

section Nested

variable {alpha : Type*} [PseudoMetricSpace alpha] {U V : Set alpha}

/-- **The `V`-killed path, killed once more at the exit of `U`, dies at the exit time of `U`.**
The first time at which the `V`-killed lifetime path is not a live point of `U` is the exit time
of `U`, that is, the lifetime of the `U`-killed path. -/
theorem lifetimePath_exitTime_killAtExit (hUV : U ⊆ V) (omega : ContinuousPath alpha) :
    LifetimePath.exitTime (Subtype.val ⁻¹' U : Set V) (killAtExit V omega) =
      exitTime U omega := by
  refine le_antisymm ?_ ?_
  · refine sInf_le_sInf ?_
    rintro s ⟨t, hst, ht⟩
    refine ⟨t, hst, ?_⟩
    rintro ⟨v, hv, hveq⟩
    by_cases hlt : (t : ℝ≥0∞) < exitTime V omega
    · rw [coordinate_killAtExit_of_lt V omega t hlt] at hveq
      have hvalue : (v : alpha) = omega t := congrArg Subtype.val (Sum.inl.inj hveq)
      exact ht (hvalue ▸ hv)
    · rw [coordinate_killAtExit_of_le V omega t (not_lt.mp hlt)] at hveq
      exact Sum.inl_ne_inr hveq
  · refine le_sInf ?_
    rintro s ⟨t, hst, ht⟩
    rw [hst]
    by_cases hlt : (t : ℝ≥0∞) < exitTime V omega
    · refine exitTime_le_of_notMem U omega t fun hmem ↦ ht ?_
      exact ⟨⟨omega t, mem_of_lt_exitTime V omega t hlt⟩, hmem,
        (coordinate_killAtExit_of_lt V omega t hlt).symm⟩
    · exact (exitTime_mono hUV omega).trans (not_lt.mp hlt)

/-- Strictly before the exit time of `U`, the `V`-killed path is alive at the point where the
`U`-killed path is alive, matched by the inclusion of `U` in `V`. -/
theorem coordinate_killAtExit_inclusion (hUV : U ⊆ V) (omega : ContinuousPath alpha) (t : NNReal)
    (ht : (t : ℝ≥0∞) < exitTime U omega) :
    LifetimePath.coordinate t (killAtExit V omega) =
      Cemetery.alive (Set.inclusion hUV ⟨omega t, mem_of_lt_exitTime U omega t ht⟩) :=
  coordinate_killAtExit_of_lt V omega t (ht.trans_le (exitTime_mono hUV omega))

/-- Killing the `V`-killed path once more at the exit of `U` reads, at every time, the coordinate
of the `U`-killed path through the inclusion of `U` in `V`. -/
theorem killedCoordinate_killAtExit (hUV : U ⊆ V) (omega : ContinuousPath alpha) (t : NNReal) :
    LifetimePath.killedCoordinate (Subtype.val ⁻¹' U : Set V) t (killAtExit V omega) =
      Sum.map (Set.inclusion hUV) id (LifetimePath.coordinate t (killAtExit U omega)) := by
  rw [LifetimePath.killedCoordinate, lifetimePath_exitTime_killAtExit hUV omega]
  by_cases hlt : (t : ℝ≥0∞) < exitTime U omega
  · rw [ite_eq_left hlt, coordinate_killAtExit_inclusion hUV omega t hlt,
      coordinate_killAtExit_of_lt U omega t hlt]
    rfl
  · rw [ite_eq_right hlt, coordinate_killAtExit_of_le U omega t (not_lt.mp hlt)]
    rfl

end Nested

end ContinuousPath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U V : Set alpha)

/-- **Nested domains, at the level of lifetimes.**  For open sets `U ⊆ V`, the first time at which
the process killed at the exit of `V` is not a live point of `U` has the law of the lifetime of
the process killed at the exit of `U`, started at the same point of `U`. -/
theorem IsConservative.killedProcess_map_exitTime (hUV : U ⊆ V) (hU : IsOpen U) (hV : IsOpen V)
    (x : U) :
    (IsConservative.killedProcess P hP V hV (Set.inclusion hUV x)).map
        (LifetimePath.exitTime (Subtype.val ⁻¹' U : Set V)) =
      (IsConservative.killedProcess P hP U hU x).map LifetimePath.lifetime := by
  have hW : IsOpen (Subtype.val ⁻¹' U : Set V) := hU.preimage continuous_subtype_val
  have hfun : LifetimePath.exitTime (Subtype.val ⁻¹' U : Set V) ∘
      ContinuousPath.killAtExit V = ContinuousPath.exitTime U :=
    funext fun omega ↦ ContinuousPath.lifetimePath_exitTime_killAtExit hUV omega
  rw [IsConservative.killedProcess_map_lifetime P hP U hU x,
    IsConservative.killedProcess_apply P hP V hV (Set.inclusion hUV x),
    Measure.map_map (LifetimePath.measurable_exitTime _ hW)
      (ContinuousPath.measurable_killAtExit V hV), hfun]

/-- **Nested domains, at the level of the coordinate laws.**  For open sets `U ⊆ V`, killing the
process of `V` once more at the exit of `U` gives, at every family of fixed times, the coordinate
law of the process killed at the exit of `U`, read through the inclusion of `U` in `V`. -/
theorem IsConservative.killedProcess_map_killedCoordinates (hUV : U ⊆ V) (hU : IsOpen U)
    (hV : IsOpen V) (x : U) {iota : Type*} (tau : iota → NNReal) :
    (IsConservative.killedProcess P hP V hV (Set.inclusion hUV x)).map
        (fun eta ↦ fun i ↦
          LifetimePath.killedCoordinate (Subtype.val ⁻¹' U : Set V) (tau i) eta) =
      (IsConservative.killedProcess P hP U hU x).map
        (fun omega ↦ fun i ↦
          Sum.map (Set.inclusion hUV) id (LifetimePath.coordinate (tau i) omega)) := by
  have hW : IsOpen (Subtype.val ⁻¹' U : Set V) := hU.preimage continuous_subtype_val
  have hm1 : Measurable fun eta : LifetimePath V ↦ fun i ↦
      LifetimePath.killedCoordinate (Subtype.val ⁻¹' U : Set V) (tau i) eta :=
    Measurable.of_eval fun i ↦
      LifetimePath.measurable_killedCoordinate _ hW (tau i)
  have hm2 : Measurable fun omega : LifetimePath U ↦ fun i ↦
      Sum.map (Set.inclusion hUV) id (LifetimePath.coordinate (tau i) omega) :=
    Measurable.of_eval fun i ↦
      ((measurable_inclusion hUV).sumMap measurable_id).comp
        (LifetimePath.measurable_coordinate (tau i))
  have hfun : (fun eta : LifetimePath V ↦ fun i ↦
        LifetimePath.killedCoordinate (Subtype.val ⁻¹' U : Set V) (tau i) eta) ∘
      ContinuousPath.killAtExit V =
      (fun omega : LifetimePath U ↦ fun i ↦
        Sum.map (Set.inclusion hUV) id (LifetimePath.coordinate (tau i) omega)) ∘
      ContinuousPath.killAtExit U := by
    funext omega i
    exact ContinuousPath.killedCoordinate_killAtExit hUV omega (tau i)
  rw [IsConservative.killedProcess_apply P hP V hV (Set.inclusion hUV x),
    IsConservative.killedProcess_apply P hP U hU x,
    Measure.map_map hm1 (ContinuousPath.measurable_killAtExit V hV),
    Measure.map_map hm2 (ContinuousPath.measurable_killAtExit U hU), hfun]

variable [LocallyCompactSpace alpha]

/-- **The part-process property, at the level of the finite-dimensional distributions.**  For open
sets `U ⊆ V`, the process killed at the exit of `V` and then killed once more at the exit of `U`
has, at every finite set of times, the finite-dimensional distribution of the cemetery extension
of the killed semigroup on `U`, read through the inclusion of `U` in `V`. -/
theorem IsConservative.killedProcess_map_killedFinsetCoordinates
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (hUV : U ⊆ V) (hU : IsOpen U) (hV : IsOpen V) (x : U) (I : Finset NNReal) :
    (IsConservative.killedProcess P hP V hV (Set.inclusion hUV x)).map
        (fun eta ↦ fun i : I ↦
          LifetimePath.killedCoordinate (Subtype.val ⁻¹' U : Set V) (i : NNReal) eta) =
      (finiteSetKernel (cemeterySemigroup (IsConservative.killedSemigroup P hP U hU hFeller hK))
          I (Cemetery.alive x)).map
        (fun p ↦ fun i : I ↦ Sum.map (Set.inclusion hUV) id (p i)) := by
  have hmap : Measurable fun p : I → Cemetery U ↦
      fun i : I ↦ Sum.map (Set.inclusion hUV) id (p i) :=
    Measurable.of_eval fun i ↦
      ((measurable_inclusion hUV).sumMap measurable_id).comp (measurable_pi_apply i)
  rw [IsConservative.killedProcess_map_killedCoordinates P hP U V hUV hU hV x
      (fun i : I ↦ (i : NNReal)),
    ← IsConservative.killedProcess_map_finiteEvaluation P hP U hU hFeller hK I x,
    Measure.map_map hmap (LifetimePath.measurable_coordinateFamily _)]
  rfl

end SubMarkovKernelSemigroup

end MarkovProcess

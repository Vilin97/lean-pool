/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Restart.CountableStoppingRestart
public import LeanPool.MarkovProcess.MarkovProcess.Path.RandomShiftMeasurability


/-!
# Measure-level restart at countable-range stopping times

Deterministic-time restricted restart identities at the attained times of a countable-range
finite stopping time patch to the measure-level identity at that stopping time: restricting the
path law to an event in the stopped sigma-algebra and shifting by the stopping time gives the
path kernel restarted from the state at the stopping time.  The proof decomposes the event over
the countable level sets of the stopping time.

This is ordinary conditional infrastructure.  The restart hypothesis is an assumption here; it
is proved for the continuous-path process in `Trajectory/FellerRestrictedRestart.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]

/-- Restricted restart at every attained deterministic time gives restricted restart at a
countable-range finite stopping time, as an identity of measures. -/
theorem restrict_map_shift_stoppingTime_eq_pathKernel_comp_of_restart_on_range
    (Q : Kernel alpha (ContinuousPath alpha))
    (x : alpha) (tau : ContinuousPath alpha → NNReal)
    (htau : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ (tau omega : WithTop NNReal)))
    (htauRange : (Set.range tau).Countable)
    (hRestart : ∀ S ∈ Set.range tau, ∀ A : Set (ContinuousPath alpha),
      MeasurableSet[canonicalFiltration (alpha := alpha) S] A →
        ((Q x).restrict A).map (shift S) =
          Kernel.comap Q (coordinateProcess (alpha := alpha) S)
              (measurable_coordinateProcess S) ∘ₘ ((Q x).restrict A)) :
    ∀ A : Set (ContinuousPath alpha), MeasurableSet[htau.measurableSpace] A →
      ((Q x).restrict A).map (fun omega ↦ shift (tau omega) omega) =
        Kernel.comap Q (fun omega ↦ omega (tau omega))
            (measurable_eval_stoppingTime_borel tau htau) ∘ₘ ((Q x).restrict A) := by
  classical
  intro A hA
  have : Countable (Set.range tau) := htauRange.to_subtype
  have hcoercedRange : (Set.range fun omega ↦ (tau omega : WithTop NNReal)).Countable := by
    refine (htauRange.image (fun t : NNReal ↦ (t : WithTop NNReal))).mono ?_
    rintro i ⟨omega, rfl⟩
    exact ⟨tau omega, ⟨omega, rfl⟩, rfl⟩
  have hYmeas : Measurable (fun omega : ContinuousPath alpha ↦ shift (tau omega) omega) :=
    measurable_shift_stoppingTime tau htau
  set lev : (Set.range tau) → Set (ContinuousPath alpha) :=
    fun S ↦ A ∩ {omega | tau omega = (S : NNReal)} with hlev
  have hlevF : ∀ S : Set.range tau,
      MeasurableSet[canonicalFiltration (alpha := alpha) (S : NNReal)] (lev S) := by
    intro S
    have h1 := hA.2 ((S : NNReal))
    have h2 : MeasurableSet[canonicalFiltration (alpha := alpha) (S : NNReal)]
        {omega | (tau omega : WithTop NNReal) = ((S : NNReal) : WithTop NNReal)} :=
      htau.measurableSet_eq_of_countable_range hcoercedRange (S : NNReal)
    have hset : lev S =
        (A ∩ {omega | (tau omega : WithTop NNReal) ≤ ((S : NNReal) : WithTop NNReal)}) ∩
          {omega | (tau omega : WithTop NNReal) = ((S : NNReal) : WithTop NNReal)} := by
      ext omega
      simp only [hlev, Set.mem_inter_iff, Set.mem_ofPred_eq, WithTop.coe_eq_coe,
        WithTop.coe_le_coe]
      exact ⟨fun h ↦ ⟨⟨h.1, h.2.le⟩, h.2⟩, fun h ↦ ⟨h.1.1, h.2⟩⟩
    rw [hset]
    exact h1.inter h2
  have hlevAmb : ∀ S : Set.range tau, MeasurableSet (lev S) := fun S ↦
    (canonicalFiltration (alpha := alpha)).le (S : NNReal) _ (hlevF S)
  have hdisj : Pairwise (Function.onFun Disjoint lev) := by
    intro S S' hSS'
    refine Set.disjoint_left.mpr fun omega homega homega' ↦ hSS' ?_
    simp only [hlev, Set.mem_inter_iff, Set.mem_ofPred_eq] at homega homega'
    exact Subtype.ext (by rw [← homega.2, ← homega'.2])
  have hunion : ⋃ S : Set.range tau, lev S = A := by
    ext omega
    simp only [hlev, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun ⟨_, h, _⟩ ↦ h, fun h ↦ ⟨⟨tau omega, ⟨omega, rfl⟩⟩, h, rfl⟩⟩
  ext B hB
  rw [Measure.map_apply hYmeas hB,
    Measure.bind_apply hB (Kernel.aemeasurable _),
    Measure.restrict_apply (hYmeas hB)]
  have hLHS : ((fun omega : ContinuousPath alpha ↦ shift (tau omega) omega) ⁻¹' B) ∩ A =
      ⋃ S : Set.range tau, (((shift (S : NNReal)) ⁻¹' B) ∩ lev S) := by
    rw [← hunion]
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage, hlev, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hB', S, hA', hS⟩
      exact ⟨S, by rw [← hS]; exact hB', hA', hS⟩
    · rintro ⟨S, hB', hA', hS⟩
      exact ⟨by rw [hS]; exact hB', S, hA', hS⟩
  rw [hLHS, measure_iUnion (fun S S' hSS' ↦ ((hdisj hSS').mono
      Set.inter_subset_right Set.inter_subset_right))
    (fun S ↦ (measurable_shift_fixed (S : NNReal) hB).inter (hlevAmb S))]
  have hRHS : ∫⁻ omega, (Kernel.comap Q (fun omega ↦ omega (tau omega))
        (measurable_eval_stoppingTime_borel tau htau)) omega B ∂((Q x).restrict A) =
      ∑' S : Set.range tau, ∫⁻ omega in lev S, Q (omega (tau omega)) B ∂(Q x) := by
    simp only [Kernel.comap_apply]
    show ∫⁻ omega in A, Q (omega (tau omega)) B ∂(Q x) = _
    rw [← hunion, lintegral_iUnion hlevAmb hdisj]
  rw [hRHS]
  refine tsum_congr fun S ↦ ?_
  have hres := congrArg (fun rho : Measure (ContinuousPath alpha) ↦ rho B)
    (hRestart (S : NNReal) S.2 (lev S) (hlevF S))
  simp only [Measure.map_apply (measurable_shift_fixed (S : NNReal)) hB,
    Measure.restrict_apply (measurable_shift_fixed (S : NNReal) hB),
    Measure.bind_apply hB (Kernel.aemeasurable _), Kernel.comap_apply,
    coordinateProcess_apply] at hres
  rw [hres]
  refine setLIntegral_congr_fun (hlevAmb S) fun omega homega ↦ ?_
  simp only [hlev, Set.mem_inter_iff, Set.mem_ofPred_eq] at homega
  rw [homega.2]

end ContinuousPath
end MarkovProcess

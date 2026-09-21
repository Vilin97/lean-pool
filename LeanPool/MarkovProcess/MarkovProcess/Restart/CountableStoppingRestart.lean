/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Restart.ConditionalMarkov
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Process.Stopping

/-!
# Conditional restart at countable-valued stopping times

This file upgrades deterministic-time conditional restart identities to a finite-valued or,
more generally, countable-valued finite stopping time.  It is ordinary conditional probability
infrastructure: the deterministic-time restart identity is a hypothesis here, proved for the
continuous-path process in `Trajectory/FellerRestrictedRestart.lean`.
-/

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ContinuousPath

section

variable {alpha E : Type*} [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

private theorem condExp_congr_ae_restrict
    {Omega : Type*} {m mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {f g : Omega → E} {s : Set Omega} (hm : m ≤ mOmega)
    (hs : MeasurableSet[m] s) (hf : Integrable f mu) (hg : Integrable g mu)
    (hfg : f =ᵐ[mu.restrict s] g) :
    mu[f|m] =ᵐ[mu.restrict s] mu[g|m] := by
  have hind : s.indicator f =ᵐ[mu] s.indicator g := by
    rw [Filter.EventuallyEq, ae_restrict_iff' (hm _ hs)] at hfg
    filter_upwards [hfg] with omega homega
    by_cases hts : omega ∈ s
    · simpa only [Set.indicator_of_mem hts] using homega hts
    · simp only [Set.indicator_of_notMem hts]
  have hce := condExp_congr_ae (m := m) hind
  have hfInd := condExp_indicator (m := m) hf hs
  have hgInd := condExp_indicator (m := m) hg hs
  rw [Filter.EventuallyEq, ae_restrict_iff' (hm _ hs)]
  filter_upwards [hfInd, hce, hgInd] with omega hfomega hceomega hgomega homega
  simpa only [Set.indicator_of_mem homega] using hfomega.symm.trans (hceomega.trans hgomega)

private theorem measurable_shift_stoppingTime
    (tau : ContinuousPath alpha → NNReal)
    (htau : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ (tau omega : WithTop NNReal)))
    (htauRange : (Set.range tau).Countable) :
    Measurable (fun omega ↦ shift (tau omega) omega) := by
  intro B hB
  have hpre : (fun omega ↦ shift (tau omega) omega) ⁻¹' B =
      ⋃ S ∈ Set.range tau, {omega | tau omega = S} ∩ shift S ⁻¹' B := by
    ext omega
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_range, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    exact ⟨fun homega ↦ ⟨tau omega, ⟨omega, rfl⟩, rfl, homega⟩,
      fun ⟨S, _, htauS, homega⟩ ↦ by simpa only [htauS] using homega⟩
  rw [hpre]
  refine MeasurableSet.biUnion htauRange fun S _ ↦ ?_
  refine ((canonicalFiltration (alpha := alpha)).le S _ ?_).inter
    ((measurable_shift_fixed S) hB)
  have hcoercedRange : (Set.range fun omega ↦ (tau omega : WithTop NNReal)).Countable := by
    rw [show Set.range (fun omega ↦ (tau omega : WithTop NNReal)) =
      (fun t : NNReal ↦ (t : WithTop NNReal)) '' Set.range tau by
        ext i
        simp only [Set.mem_range, Set.mem_image]
        constructor
        · rintro ⟨omega, rfl⟩
          exact ⟨tau omega, ⟨omega, rfl⟩, rfl⟩
        · rintro ⟨S, ⟨omega, rfl⟩, rfl⟩
          exact ⟨omega, rfl⟩]
    exact htauRange.image fun t : NNReal ↦ (t : WithTop NNReal)
  simpa only [WithTop.coe_eq_coe] using
    htau.measurableSet_eq_of_countable_range hcoercedRange S

/-- Deterministic-time conditional Markov formulas on the range of a countable-valued finite
stopping time patch to a conditional restart identity.  Countability and the stopping-time
property make the random shift measurable by gluing its deterministic restrictions along the
measurable level sets of `tau`. -/
theorem condExp_shift_stoppingTime_ae_eq_integral_pathKernel_of_restart_on_range
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (x : alpha) (tau : ContinuousPath alpha → NNReal)
    (htau : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ (tau omega : WithTop NNReal)))
    (htauRange : (Set.range tau).Countable)
    (hRestart : ∀ S ∈ Set.range tau, ∀ A : Set (ContinuousPath alpha),
      MeasurableSet[canonicalFiltration (alpha := alpha) S] A →
        ((Q x).restrict A).map (shift S) =
          Kernel.comap Q (coordinateProcess (alpha := alpha) S)
              (measurable_coordinateProcess S) ∘ₘ ((Q x).restrict A))
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : Real) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    (Q x)[fun omega ↦ F (shift (tau omega) omega)|htau.measurableSpace] =ᵐ[Q x]
      fun omega ↦ ∫ eta, F eta ∂Q (omega (tau omega)) := by
  let tauTop : ContinuousPath alpha → WithTop NNReal :=
    fun omega ↦ (tau omega : WithTop NNReal)
  have htauTopRange : (Set.range tauTop).Countable :=
    by
      rw [show Set.range tauTop =
        (fun t : NNReal ↦ (t : WithTop NNReal)) '' Set.range tau by
          ext i
          simp only [Set.mem_range, tauTop, Set.mem_image]
          constructor
          · rintro ⟨omega, rfl⟩
            exact ⟨tau omega, ⟨omega, rfl⟩, rfl⟩
          · rintro ⟨S, ⟨omega, rfl⟩, rfl⟩
            exact ⟨omega, rfl⟩]
      exact htauRange.image fun t : NNReal ↦ (t : WithTop NNReal)
  have huniv : Set.univ = ⋃ i ∈ Set.range tauTop, {omega | tauTop omega = i} := by
    ext omega
    simp only [Set.mem_univ, Set.mem_range, Set.iUnion_exists, Set.iUnion_iUnion_eq',
      Set.mem_iUnion, Set.mem_ofPred_eq, exists_apply_eq_apply']
  have hRandomShiftMeas : Measurable (fun omega ↦ shift (tau omega) omega) :=
    measurable_shift_stoppingTime tau htau htauRange
  have hRandomInt : Integrable (fun omega ↦ F (shift (tau omega) omega)) (Q x) :=
    Integrable.of_bound
      (hF.comp_measurable hRandomShiftMeas).aestronglyMeasurable C
      (ae_of_all _ fun omega ↦ hFC (shift (tau omega) omega))
  nth_rw 1 [← @Measure.restrict_univ (ContinuousPath alpha) _ (Q x)]
  rw [huniv, ae_eq_restrict_biUnion_iff _ htauTopRange]
  intro i hi
  have hiTop : i ≠ ⊤ := by
    rintro rfl
    obtain ⟨omega, homega⟩ := hi
    simp only [tauTop, WithTop.coe_ne_top] at homega
  lift i to NNReal using hiTop with S
  have hLevel : MeasurableSet[canonicalFiltration (alpha := alpha) S]
      {omega | tauTop omega = S} :=
    htau.measurableSet_eq_of_countable_range htauTopRange S
  have hSRange : S ∈ Set.range tau := by
    obtain ⟨omega, homega⟩ := hi
    exact ⟨omega, WithTop.coe_eq_coe.mp homega⟩
  have hDet := condExp_shift_ae_eq_integral_pathKernel_of_restrict_map
    Q x S (hRestart S hSRange) F hF C hFC
  have hDetInt : Integrable (fun omega ↦ F (shift S omega)) (Q x) :=
    Integrable.of_bound
      (hF.comp_measurable (measurable_shift_fixed S)).aestronglyMeasurable C
      (ae_of_all _ fun omega ↦ hFC (shift S omega))
  have hLocalInput :
      (fun omega ↦ F (shift (tau omega) omega)) =ᵐ[(Q x).restrict {omega | tauTop omega = S}]
        fun omega ↦ F (shift S omega) := by
    rw [Filter.EventuallyEq, ae_restrict_iff'
      ((canonicalFiltration (alpha := alpha)).le S _ hLevel)]
    exact Filter.Eventually.of_forall fun omega homega ↦ by
      simp only [Set.mem_ofPred_eq, tauTop, WithTop.coe_eq_coe] at homega
      rw [homega]
  have hLocalOutput :
      (fun omega ↦ ∫ eta, F eta ∂Q (omega S)) =ᵐ[(Q x).restrict {omega | tauTop omega = S}]
        fun omega ↦ ∫ eta, F eta ∂Q (omega (tau omega)) := by
    rw [Filter.EventuallyEq, ae_restrict_iff'
      ((canonicalFiltration (alpha := alpha)).le S _ hLevel)]
    exact Filter.Eventually.of_forall fun omega homega ↦ by
      simp only [Set.mem_ofPred_eq, tauTop, WithTop.coe_eq_coe] at homega
      rw [homega]
  exact
    (condExp_stopping_time_ae_eq_restrict_eq_of_countable_range
      (μ := Q x) (f := fun omega ↦ F (shift (tau omega) omega)) htau htauTopRange S).trans
      ((condExp_congr_ae_restrict (E := E)
        ((canonicalFiltration (alpha := alpha)).le S) hLevel hRandomInt hDetInt hLocalInput).trans
        (hDet.restrict.trans hLocalOutput))

/-- Deterministic-time conditional Markov formulas patch to a countable-valued finite stopping
time.  This backward-compatible form asks for the deterministic formula at every finite time. -/
theorem condExp_shift_stoppingTime_ae_eq_integral_pathKernel
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (x : alpha) (tau : ContinuousPath alpha → NNReal)
    (htau : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ (tau omega : WithTop NNReal)))
    (htauRange : (Set.range tau).Countable)
    (hRestart : ∀ (S : NNReal) (A : Set (ContinuousPath alpha)),
      MeasurableSet[canonicalFiltration (alpha := alpha) S] A →
        ((Q x).restrict A).map (shift S) =
          Kernel.comap Q (coordinateProcess (alpha := alpha) S)
              (measurable_coordinateProcess S) ∘ₘ ((Q x).restrict A))
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : Real) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    (Q x)[fun omega ↦ F (shift (tau omega) omega)|htau.measurableSpace] =ᵐ[Q x]
      fun omega ↦ ∫ eta, F eta ∂Q (omega (tau omega)) := by
  exact condExp_shift_stoppingTime_ae_eq_integral_pathKernel_of_restart_on_range
    Q x tau htau htauRange (fun S _ ↦ hRestart S) F hF C hFC

end
end ContinuousPath
end MarkovProcess

end PortComputability

/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.GradientSlotDuhamelTested
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationDuhamelKernels

/-!
# Gradient Slot Duhamel

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Core.HeatPotential CKN.Core.Step4


noncomputable section

namespace CKN.Core.Step3

/-!
# The gradient-slot Duhamel representation of the localized velocity

Paper label `lem:local-equation`, displayed equation `eq:local-equation`.  With
`φ` a space-time cutoff supported in a compactly contained box `Ω' × J`, the
localized velocity `φu` solves the whole-space heat equation with the heat-slot
source `localizedGradientSourceG` and the divergence-form source
`∂ⱼ localizedGradientSourceH`.  Testing the weak formulation of `def:sws`
against the backward heat kernel, and using that a compactly supported
localized field is determined by its heat potential, gives the representation
`φu = heatPotential G H` almost everywhere.

The tested identity is supplied by `gradientSlot_tested_transfer_of_sws`; the
passage from the tested identity to the potential is the established
`duhamel_of_localized_velocity`, whose derivative slot carries the opposite
sign convention and is converted by
`localized_gradient_slot_heat_representation`.
-/

/-- Measurability of the causal heat kernel on the space-time carrier. -/
private lemma heatKernelPlus_measurable_slot :
    Measurable (fun w : ParabolicPoint => heatKernelPlus w) := by
  unfold heatKernelPlus
  apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
  · unfold heatKernel
    apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
    · fun_prop
    · exact measurable_const
  · exact measurable_const

/-- Measurability of the spatial derivatives of the causal heat kernel. -/
private lemma heatKernelSpaceDerivative_measurable_slot (j : Fin 3) :
    Measurable (fun w : ParabolicPoint =>
      heatKernelSpaceDerivative w.1 w.2 j) := by
  have hk : Measurable (fun w : ParabolicPoint => heatKernel w.1 w.2) := by
    unfold heatKernel
    apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
    · fun_prop
    · exact measurable_const
  unfold heatKernelSpaceDerivative
  apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
  · have hcoord : Measurable (fun w : ParabolicPoint => w.1 j) :=
      (measurable_pi_apply j).comp measurable_fst
    exact (hcoord.neg.div (measurable_const.mul measurable_snd)).mul hk
  · exact measurable_const

/-- Local integrability of the spatial derivatives of the causal heat kernel. -/
private lemma heatKernelSpaceDerivative_locallyIntegrable_slot (j : Fin 3) :
    LocallyIntegrable
      (fun w : ParabolicPoint =>
        heatKernelSpaceDerivative w.1 w.2 j) volume := by
  apply heatKernelGradientNorm_locallyIntegrable.mono
    (heatKernelSpaceDerivative_measurable_slot j).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs]
  by_cases ht : 0 < z.2
  · unfold heatKernelGradientNorm
    have hnonneg : 0 ≤ ∑ k, |heatKernelSpaceDerivative z.1 z.2 k| :=
      Finset.sum_nonneg (fun k _hk => abs_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact Finset.single_le_sum
      (fun k _hk => abs_nonneg (heatKernelSpaceDerivative z.1 z.2 k))
      (Finset.mem_univ j)
  · rw [heatKernelGradientNorm_eq_zero_of_nonpos (le_of_not_gt ht)]
    unfold heatKernelSpaceDerivative
    simp [not_lt.mpr (le_of_not_gt ht)]

/-- Local integrability transported to the explicit space-time product carrier. -/
private lemma locallyIntegrable_prod_of_parabolic_slot
    {F : ParabolicPoint → ℝ} (hF : LocallyIntegrable F volume) :
    LocallyIntegrable (fun z : Vec3 × ℝ => F z) volume := by
  intro x
  rcases hF (show ParabolicPoint from x) with ⟨U, hU, hInt⟩
  refine ⟨parabolicHomeomorph '' U, ?_, ?_⟩
  · have h := parabolicHomeomorph.isOpenMap.image_mem_nhds hU
    change parabolicHomeomorph '' U ∈
      𝓝 (parabolicHomeomorph (show ParabolicPoint from x))
    exact h
  · have hset : parabolicHomeomorph '' U = U := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hz
        exact ⟨z, hz, rfl⟩
    rw [hset]
    exact hInt

/-- The gradient-slot Duhamel representation of the localized velocity, paper
label `lem:local-equation`.  For a suitable weak solution, a cutoff `φ`
supported in a compactly contained box `Ω' × J`, and a weak pressure gradient
`Dp` on that box, the localized velocity `φu` agrees almost everywhere with the
heat potential of `localizedGradientSourceG` in the heat slot and
`localizedGradientSourceH` in the divergence slot. -/
theorem localized_gradient_slot_duhamel_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J)
    {Dp : ParabolicPoint → Vec3}
    (hDpInt : ∀ i, Integrable (fun z => Dp z i)
      (volume.restrict (spaceTimeSet Ω' J)))
    (hDpweak : ∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
      tsupport ψ ⊆ Ω' ×ˢ J →
      (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
        -(∫ z : ParabolicPoint, Dp z i * ψ z)) :
    localizedVelocity φ u =ᵐ[volume]
      (fun z i => heatPotential
        (fun w => localizedGradientSourceG φ u Du f Dp w i)
        (fun j w => localizedGradientSourceH φ u j w i) z) := by
  obtain ⟨hVInt, -, -, hVSupport, -, -⟩ :=
    localized_divergence_source_data_of_sws hsol hφ hbox hφbox
  obtain ⟨hGradInt, hGradHInt, hGradSupport, hGradHSupport⟩ :=
    localized_gradient_source_data_of_sws hsol hφ hbox hφbox hDpInt
  have hv : ∀ i : Fin 3,
      LocallyIntegrable
        (fun z : Vec3 × ℝ => localizedVelocity φ u z i) volume := by
    intro i
    have hlocal := (hVInt i).locallyIntegrable
    exact locallyIntegrable_prod_of_parabolic_slot hlocal
  have hFg : ∀ (ζ : Vec3 × ℝ → ℝ)
      (_hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (_hζc : HasCompactSupport ζ)
      (i : Fin 3),
      Integrable
        (fun w : ParabolicPoint × ParabolicPoint =>
          backwardHeatKernel w.1 w.2 * ζ w.1 *
            localizedGradientSourceG φ u Du f Dp w.2 i)
        ((volume : Measure ParabolicPoint).prod volume) := by
    intro ζ hζ hζc i
    simpa [backwardHeatKernel, pointSub] using
      (duhamel_kernel_test_integrable_of_compact_support
        (k := fun w : ParabolicPoint => heatKernelPlus w)
        (F := fun w : ParabolicPoint =>
          localizedGradientSourceG φ u Du f Dp w i)
        (ζ := ζ) heatKernelPlus_locallyIntegrable
        heatKernelPlus_measurable_slot hζ hζc
        (hGradInt i) (hGradSupport i))
  have hFh : ∀ (ζ : Vec3 × ℝ → ℝ)
      (_hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (_hζc : HasCompactSupport ζ)
      (j i : Fin 3),
      Integrable
        (fun w : ParabolicPoint × ParabolicPoint =>
          backwardHeatSpatialKernel j w.1 w.2 * ζ w.1 *
            (-localizedGradientSourceH φ u j w.2 i))
        ((volume : Measure ParabolicPoint).prod volume) := by
    intro ζ hζ hζc j i
    simpa [backwardHeatSpatialKernel, pointSub] using
      (duhamel_kernel_test_integrable_of_compact_support
        (k := fun w : ParabolicPoint => heatKernelSpaceDerivative w.1 w.2 j)
        (F := fun w : ParabolicPoint => -localizedGradientSourceH φ u j w i)
        (ζ := ζ) (heatKernelSpaceDerivative_locallyIntegrable_slot j)
        (heatKernelSpaceDerivative_measurable_slot j) hζ hζc
        (hGradHInt j i) (hGradHSupport j i))
  have hpotential : ∀ i : Fin 3,
      LocallyIntegrable
        (fun z : Vec3 × ℝ =>
          duhamelPotential (localizedGradientSourceG φ u Du f Dp)
            (fun j w => -localizedGradientSourceH φ u j w) z i) volume := by
    intro i
    have hGpot : LocallyIntegrable
        (fun z : ParabolicPoint =>
          ∫ v, heatPotentialKernel z v *
            localizedGradientSourceG φ u Du f Dp v i) volume := by
      simpa [heatPotentialKernel, pointSub] using
        (parabolic_potential_locallyIntegrable_of_compact_integrable
          (k := fun w : ParabolicPoint => heatKernelPlus w)
          (g := fun w : ParabolicPoint =>
            localizedGradientSourceG φ u Du f Dp w i)
          heatKernelPlus_locallyIntegrable
          heatKernelPlus_measurable_slot (hGradInt i) (hGradSupport i))
    have hHpot : ∀ j : Fin 3, LocallyIntegrable
        (fun z : ParabolicPoint =>
          ∫ v, heatPotentialSpatialKernel j z v *
            (-localizedGradientSourceH φ u j v i)) volume := by
      intro j
      simpa [heatPotentialSpatialKernel, pointSub] using
        (parabolic_potential_locallyIntegrable_of_compact_integrable
          (k := fun w : ParabolicPoint => heatKernelSpaceDerivative w.1 w.2 j)
          (g := fun w : ParabolicPoint =>
            -localizedGradientSourceH φ u j w i)
          (heatKernelSpaceDerivative_locallyIntegrable_slot j)
          (heatKernelSpaceDerivative_measurable_slot j)
          (hGradHInt j i) (hGradHSupport j i))
    have hsum : LocallyIntegrable
        (fun z : ParabolicPoint =>
          ∑ j, ∫ v, heatPotentialSpatialKernel j z v *
            (-localizedGradientSourceH φ u j v i)) volume := by
      have hs : ∀ s : Finset (Fin 3), LocallyIntegrable
          (fun z : ParabolicPoint => ∑ j ∈ s, (∫ v : ParabolicPoint,
            heatPotentialSpatialKernel j z v *
              (-localizedGradientSourceH φ u j v i))) volume := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
            simpa using (locallyIntegrable_zero :
              LocallyIntegrable (fun _ : ParabolicPoint => (0 : ℝ)) volume)
        | @insert j s hj ih =>
            convert (hHpot j).add ih using 1
            funext z
            simp [Finset.sum_insert hj]
      simpa using hs (Finset.univ : Finset (Fin 3))
    have hpot : LocallyIntegrable
        (fun z : ParabolicPoint =>
          duhamelPotential (localizedGradientSourceG φ u Du f Dp)
            (fun j w => -localizedGradientSourceH φ u j w) z i) volume := by
      change LocallyIntegrable
        (fun z : ParabolicPoint =>
          (∫ v, heatPotentialKernel z v *
            localizedGradientSourceG φ u Du f Dp v i) -
          ∑ j, ∫ v, heatPotentialSpatialKernel j z v *
            (-localizedGradientSourceH φ u j v i)) volume
      exact hGpot.sub hsum
    exact locallyIntegrable_prod_of_parabolic_slot hpot
  have hweak : ∀ i : Fin 3, ∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
      (∫ z, localizedVelocity φ u z i *
          (-(timePartial ψ z) - ∑ j, spatialSecondPartial ψ j j z)) =
        (∫ z, localizedGradientSourceG φ u Du f Dp z i * ψ z) +
          ∑ j, ∫ z, (-localizedGradientSourceH φ u j z i) *
            spatialPartial ψ j z := by
    intro i ψ hψ
    refine Eq.trans (localized_divergence_scalar_tested_of_sws
      hsol hφ hbox hφbox i hψ) ?_
    exact gradientSlot_tested_transfer_of_sws hsol hφ hbox hφbox hDpInt
      hDpweak hψ i
  have hrep := duhamel_of_localized_velocity hv hpotential hFg hFh hweak
    (duhamelSupportDataOfCompactSupport
      hVSupport (fun i => hGradSupport i) (fun j i => hGradHSupport j i))
  have hheat := localized_gradient_slot_heat_representation hrep
  filter_upwards [hheat] with z hz
  change localizedVelocity φ u z =
    vectorHeatPotential (localizedGradientSourceG φ u Du f Dp)
      (localizedGradientSourceH φ u) z
  exact hz

end CKN.Core.Step3

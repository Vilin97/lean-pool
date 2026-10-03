/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationDuhamel

/-!
# Localized Equation Duhamel Finish

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
noncomputable section

namespace CKN.Core.Step3

open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Core.HeatPotential

private lemma heatKernelPlus_measurable_local :
    Measurable (fun p : ParabolicPoint => heatKernelPlus p) := by
  unfold heatKernelPlus
  apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
  · unfold heatKernel
    apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
    · fun_prop
    · exact measurable_const
  · exact measurable_const

private lemma locallyIntegrable_prod_of_parabolic
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

private lemma heatKernelSpaceDerivative_measurable (i : Fin 3) :
    Measurable (fun p : ParabolicPoint =>
      heatKernelSpaceDerivative p.1 p.2 i) := by
  have hk : Measurable (fun p : ParabolicPoint => heatKernel p.1 p.2) := by
    unfold heatKernel
    apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
    · fun_prop
    · exact measurable_const
  unfold heatKernelSpaceDerivative
  apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
  · have hcoord : Measurable (fun p : ParabolicPoint => p.1 i) :=
      (measurable_pi_apply i).comp measurable_fst
    exact (hcoord.neg.div (measurable_const.mul measurable_snd)).mul hk
  · exact measurable_const

private lemma heatKernelSpaceDerivative_locallyIntegrable (i : Fin 3) :
    LocallyIntegrable
      (fun p : ParabolicPoint => heatKernelSpaceDerivative p.1 p.2 i) volume := by
  apply heatKernelGradientNorm_locallyIntegrable.mono
    (heatKernelSpaceDerivative_measurable i).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs]
  by_cases ht : 0 < z.2
  · unfold heatKernelGradientNorm
    have hnonneg : 0 ≤ ∑ j, |heatKernelSpaceDerivative z.1 z.2 j| :=
      Finset.sum_nonneg (fun j _hj => abs_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact Finset.single_le_sum
      (fun j _hj => abs_nonneg (heatKernelSpaceDerivative z.1 z.2 j))
      (Finset.mem_univ i)
  · rw [heatKernelGradientNorm_eq_zero_of_nonpos (le_of_not_gt ht)]
    unfold heatKernelSpaceDerivative
    simp [not_lt.mpr (le_of_not_gt ht)]

theorem duhamel_of_suitableWeakSolution_localized
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox Ω I Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J) :
    ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      localizedVelocity (show ParabolicPoint → ℝ from φ) u z =
        duhamelPotential
          (localizedDivergenceG φ u Du p f)
          (localizedDivergenceH φ u p) z := by
  obtain ⟨hVInt, hGInt, hHInt, hVSupport, hGSupport, hHSupport⟩ :=
    localized_divergence_source_data_of_sws hsol hφ hbox hφbox
  have hv : ∀ i : Fin 3,
      LocallyIntegrable
        (fun z : Vec3 × ℝ => localizedVelocity φ u z i) volume :=
    fun i => by
      have hi : Integrable
          (fun z : Vec3 × ℝ => localizedVelocity
            (show ParabolicPoint → ℝ from φ) u z i) volume := hVInt i
      exact hi.locallyIntegrable
  have hFg : ∀ (ζ : Vec3 × ℝ → ℝ)
      (_hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (_hζc : HasCompactSupport ζ)
      (i : Fin 3),
      Integrable
        (fun q : ParabolicPoint × ParabolicPoint =>
          backwardHeatKernel q.1 q.2 * ζ q.1 * localizedDivergenceG φ u Du p f q.2 i)
        ((volume : Measure ParabolicPoint).prod volume) := by
    intro ζ hζ hζc i
    simpa [backwardHeatKernel, pointSub] using
      (duhamel_kernel_test_integrable_of_compact_support
        (k := fun z : ParabolicPoint => heatKernelPlus z)
        (F := fun z : ParabolicPoint => localizedDivergenceG φ u Du p f z i)
        (ζ := ζ) heatKernelPlus_locallyIntegrable heatKernelPlus_measurable_local
        hζ hζc (hGInt i) (hGSupport i))
  have hFh : ∀ (ζ : Vec3 × ℝ → ℝ)
      (_hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (_hζc : HasCompactSupport ζ)
      (j i : Fin 3),
      Integrable
        (fun q : ParabolicPoint × ParabolicPoint =>
          backwardHeatSpatialKernel j q.1 q.2 *
            ζ q.1 * localizedDivergenceH φ u p j q.2 i)
        ((volume : Measure ParabolicPoint).prod volume) := by
    intro ζ hζ hζc j i
    simpa [backwardHeatSpatialKernel, pointSub] using
      (duhamel_kernel_test_integrable_of_compact_support
        (k := fun z : ParabolicPoint =>
          heatKernelSpaceDerivative z.1 z.2 j)
        (F := fun z : ParabolicPoint => localizedDivergenceH φ u p j z i)
        (ζ := ζ) (heatKernelSpaceDerivative_locallyIntegrable j)
        (heatKernelSpaceDerivative_measurable j) hζ hζc
        (hHInt j i) (hHSupport j i))
  have hpotential : ∀ i : Fin 3,
      LocallyIntegrable
        (fun z : Vec3 × ℝ =>
          duhamelPotential (localizedDivergenceG φ u Du p f)
            (localizedDivergenceH φ u p) z i) volume := by
    intro i
    have hGpot : LocallyIntegrable
        (fun z : ParabolicPoint =>
          ∫ v, heatPotentialKernel z v *
            localizedDivergenceG φ u Du p f v i) volume := by
      simpa [heatPotentialKernel, pointSub] using
        (parabolic_potential_locallyIntegrable_of_compact_integrable
          (k := fun z : ParabolicPoint => heatKernelPlus z)
          (g := fun z : ParabolicPoint =>
            localizedDivergenceG φ u Du p f z i)
          heatKernelPlus_locallyIntegrable heatKernelPlus_measurable_local
          (hGInt i) (hGSupport i))
    have hHpot : ∀ j : Fin 3, LocallyIntegrable
        (fun z : ParabolicPoint =>
          ∫ v, heatPotentialSpatialKernel j z v *
            localizedDivergenceH φ u p j v i) volume := by
      intro j
      simpa [heatPotentialSpatialKernel, pointSub] using
        (parabolic_potential_locallyIntegrable_of_compact_integrable
          (k := fun z : ParabolicPoint =>
            heatKernelSpaceDerivative z.1 z.2 j)
          (g := fun z : ParabolicPoint =>
            localizedDivergenceH φ u p j z i)
          (heatKernelSpaceDerivative_locallyIntegrable j)
          (heatKernelSpaceDerivative_measurable j)
          (hHInt j i) (hHSupport j i))
    have hsum : LocallyIntegrable
        (fun z : ParabolicPoint =>
          ∑ j, ∫ v, heatPotentialSpatialKernel j z v *
            localizedDivergenceH φ u p j v i) volume := by
      have hs : ∀ s : Finset (Fin 3), LocallyIntegrable
          (fun z : ParabolicPoint =>
            Finset.sum s (fun j => ∫ v : ParabolicPoint,
              heatPotentialSpatialKernel j z v *
                localizedDivergenceH φ u p j v i)) volume := by
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
    have hpotP : LocallyIntegrable
        (fun z : ParabolicPoint =>
          duhamelPotential (localizedDivergenceG φ u Du p f)
            (localizedDivergenceH φ u p) z i) volume := by
      convert hGpot.sub hsum using 1
      funext z
      simp [duhamelPotential]
    exact locallyIntegrable_prod_of_parabolic hpotP
  have hweak : ∀ i : Fin 3, ∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
      (∫ z, localizedVelocity φ u z i *
          (-(timePartial ψ z) - ∑ j, spatialSecondPartial ψ j j z)) =
        (∫ z, localizedDivergenceG φ u Du p f z i * ψ z) +
          ∑ j, ∫ z, localizedDivergenceH φ u p j z i * spatialPartial ψ j z := by
    intro i ψ hψ
    exact localized_divergence_scalar_tested_of_sws
      hsol hφ hbox hφbox i hψ
  exact duhamel_of_localized_velocity hv hpotential hFg hFh hweak
    (duhamelSupportDataOfCompactSupport
      hVSupport (fun i => hGSupport i) (fun j i => hHSupport j i))

end CKN.Core.Step3

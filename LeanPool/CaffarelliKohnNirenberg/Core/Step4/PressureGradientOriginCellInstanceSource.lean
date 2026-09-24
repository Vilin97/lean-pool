/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientTensorSource
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientTensorSourcePairing
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SliceVelocityCube
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceDistribution

/-!
# The local tensor source of the pressure gradient

The source and its tested pairing in `eq:pressure-gradient-morrey` follow
from the velocity's spatial weak gradient and divergence constraint.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- The force-free centred tensor source has the integrability, support,
and pairing properties required by `eq:pressure-gradient-morrey`. -/
theorem origin_tensor_source_data_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (c : ℝ → Vec3) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∀ i : Fin 3, MemLp (fun x =>
        pressureDivergenceCutoffSourceCentredTensor
          (mollifiedBallCutoff z.1 hρ) (spatialDeriv (mollifiedBallCutoff z.1 hρ))
          (fun y => u (y, s)) (fun y => Du (y, s)) (c s) x i)
        (ENNReal.ofReal (6 / 5 : ℝ)) volume) ∧
      (∀ i : Fin 3, HasCompactSupport (fun x =>
        pressureDivergenceCutoffSourceCentredTensor
          (mollifiedBallCutoff z.1 hρ) (spatialDeriv (mollifiedBallCutoff z.1 hρ))
          (fun y => u (y, s)) (fun y => Du (y, s)) (c s) x i)) ∧
      (∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        (∑ i, ∫ x, pressureDivergenceCutoffSourceCentredTensor
          (mollifiedBallCutoff z.1 hρ) (spatialDeriv (mollifiedBallCutoff z.1 hρ))
          (fun y => u (y, s)) (fun y => Du (y, s)) (c s) x i * spatialDeriv ψ i x) =
        pressureSecondPairing
          (fun i j x => mollifiedBallCutoff z.1 hρ x * pressureUTensor u c (x, s) i j) ψ) := by
  obtain ⟨U, J, hbox, hball, htime⟩ := pressure_box_geometry hsol hρ hsub
  have hUΩ : U ⊆ Ω := subset_closure.trans hbox.2.2.1
  have hJI : J ⊆ I := subset_closure.trans hbox.2.2.2.2.2
  have hmem := slice_memLp_ae_of_sws hsol hbox
  have hgrad := (hsol.2.2.2.2.2.1 U J hbox).2.2.2.2.2.2.2.2
  have hgradAll : ∀ᵐ s ∂volume.restrict J, ∀ i : Fin 3,
      HasWeakGradientOn U (fun x => u (x, s) i) (fun x => Du (x, s) i) :=
    ae_all_iff.mpr hgrad
  have hloc : ∀ᵐ s ∂volume.restrict J, ∀ i : Fin 3,
      LocallyIntegrableOn (fun x => u (x, s) i) U volume := by
    filter_upwards [hmem] with s hs i
    exact locallyIntegrableOn_of_locallyIntegrable_restrict
      ((hs.1.eval i).locallyIntegrable (by norm_num))
  have hdiv := ae_slice_divergence_zero_of_forall_test hbox.1 hloc (by
    intro ψ hψ hψc hψU
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hJI
      (divfree_slice_weak_of_suitable hsol ψ hψ hψc (hψU.trans hUΩ))] with s hs
    have hz : ∀ x, x ∉ tsupport ψ →
        (∑ i, u (x, s) i * (fderiv ℝ ψ x) (basisVec i)) = 0 := by
      intro x hx
      rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]
      simp
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => hz x (fun h => hx (hψU h))),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => hz x (fun h => hx (hUΩ (hψU h))))]
    exact hs)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset htime hmem,
    ae_restrict_of_ae_restrict_of_subset htime hgradAll,
    ae_restrict_of_ae_restrict_of_subset htime hdiv] with s hs hw hd
  have hη := mollifiedBallCutoff_smooth z.1 hρ
  have hηc := mollifiedBallCutoff_hasCompactSupport z.1 hρ
  have hηB := pressure_cutoff_support_subset_ball z.1 hρ
  have hu3 := velocity_norm_memLp_three_on_ball_of_slices hρ hball hs.1 hs.2 hw
  have huComp (i : Fin 3) : MemLp (fun x => u (x, s) i) 3
      (volume.restrict (tsupport (mollifiedBallCutoff z.1 hρ))) := by
    have huB := (hs.1.eval i).mono_measure (Measure.restrict_mono_set volume hball)
    have hu3i : MemLp (fun x => u (x, s) i) (ENNReal.ofReal (3 : ℝ))
        (volume.restrict (vec3Ball z.1 ρ)) := by
      apply hu3.of_le huB.aestronglyMeasurable
      exact Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, Real.norm_of_nonneg (vec3EuclideanNorm_nonneg _)]
        exact abs_apply_le_vec3EuclideanNorm _ _
    simpa only [ENNReal.ofReal_ofNat] using
      hu3i.mono_measure (Measure.restrict_mono_set volume hηB)
  have hDuComp (i j : Fin 3) : MemLp (fun x => Du (x, s) i j) 2
      (volume.restrict (tsupport (mollifiedBallCutoff z.1 hρ))) :=
    ((hs.2.eval i).eval j).mono_measure
      (Measure.restrict_mono_set volume (hηB.trans hball))
  obtain ⟨hV, hVc⟩ := pressureDivergenceCutoffSourceCentredTensor_memLp_hasCompactSupport
    (c := c s) hηc.isCompact hη subset_rfl huComp hDuComp
  refine ⟨hV, hVc, ?_⟩
  intro ψ hψ hψc
  exact pressureDivergenceCutoffSourceCentredTensor_pairing_of_divfree hbox.1 hη hηc
    (hηB.trans hball) (fun i => hs.1.eval i) (fun i j => (hs.2.eval i).eval j)
    hw hd hψ hψc

end CKN.Core.Step4

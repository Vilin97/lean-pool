/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceDistribution
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34CentredPairing
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsCylinder
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalCore

/-!
# Lin34 Centred Pairing SWS

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-!
# The centred identification data at solution level

The slice identity of `Lin34CentredPairing.lean` is fed the slice data of a
suitable weak solution: the integrability of the two nonlinearities on the
support of the cut-off, the local integrability of the velocity, and the
divergence-free slice condition tested against every compactly supported smooth
function at once.  The result is the pair of hypotheses that the
Calderón--Zygmund estimate for the centred potential of `prop:lin34` consumes.
-/

/-- **The identification data for the centred first potential at solution
level.**  For a suitable weak solution and almost every time of the cylinder
`Q_ρ(z₀)`, the whole-space distributional identity of
`prop:pressure-decomposition` holds for the centred potential against the
centred source `eq:Uhat`, simultaneously for every compactly supported smooth
spatial test function, together with the integrability of that pairing. -/
theorem lin34_centredP1_cz_data_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          Integrable (fun x => lin34CentredP1 u p f z.1 ρ hρ s x *
            spatialLaplacian ψ x) volume →
          ∫ x, lin34CentredP1 u p f z.1 ρ hρ s x * spatialLaplacian ψ x =
            pressureSecondPairing (lin34CentredSource u z.1 hρ s) ψ) ∧
        ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          Integrable (fun x => lin34CentredP1 u p f z.1 ρ hρ s x *
            spatialLaplacian ψ x) volume := by
  classical
  have hη : ContDiff ℝ (⊤ : ℕ∞) (mollifiedBallCutoff z.1 hρ) :=
    mollifiedBallCutoff_smooth z.1 hρ
  have hηc : HasCompactSupport (mollifiedBallCutoff z.1 hρ) :=
    mollifiedBallCutoff_hasCompactSupport z.1 hρ
  obtain ⟨Ω₀, J, hbox, hballsub, htime⟩ := pressure_box_geometry hsol hρ hsub
  have hηΩ : tsupport (mollifiedBallCutoff z.1 hρ) ⊆ Ω :=
    (pressure_cutoff_support_subset_ball z.1 hρ).trans
      (fun x hx => hbox.2.2.1 (subset_closure (hballsub hx)))
  obtain ⟨Ω', hΩ'open, hηΩ', -, hΩ'compact, hΩ'Ω, hLp⟩ :=
    decomposition_slice_integrability hsol hηc hηΩ hηc hηΩ
  have : IsFiniteMeasure (volume.restrict Ω') := by
    refine isFiniteMeasure_restrict.mpr ?_
    exact (lt_of_le_of_lt (measure_mono (μ := volume) subset_closure)
      hΩ'compact.measure_lt_top).ne
  have hTsubI : Ioc (z.2 - ρ ^ 2) z.2 ⊆ I :=
    htime.trans (subset_closure.trans hbox.2.2.2.2.2)
  have hloc : ∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
      LocallyIntegrableOn (fun x : Vec3 => u (x, s) i) Ω' volume := by
    filter_upwards [hLp] with s hs i
    have hcomp : MemLp (fun x : Vec3 => u (x, s) i) 2 (volume.restrict Ω') :=
      hs.1.continuousLinearMap_comp (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
    have hint : IntegrableOn (fun x : Vec3 => u (x, s) i) Ω' volume :=
      hcomp.integrable (by norm_num)
    exact hint.locallyIntegrableOn
  have hsliceDiv : ∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ω' →
      ∀ᵐ s ∂volume.restrict I,
        ∫ x in Ω', ∑ i : Fin 3, u (x, s) i * (fderiv ℝ φ x) (basisVec i) = 0 := by
    intro φ hφ hφc hφΩ'
    have hφΩ : tsupport φ ⊆ Ω := hφΩ'.trans (subset_closure.trans hΩ'Ω)
    filter_upwards [divfree_slice_weak_of_suitable hsol φ hφ hφc hφΩ] with s hs
    have hzeroOut : ∀ x : Vec3, x ∉ tsupport φ →
        (∑ i : Fin 3, u (x, s) i * (fderiv ℝ φ x) (basisVec i)) = 0 := by
      intro x hx
      rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]
      simp
    have h1 : (∫ x in Ω, ∑ i : Fin 3, u (x, s) i * (fderiv ℝ φ x) (basisVec i)) =
        ∫ x, ∑ i : Fin 3, u (x, s) i * (fderiv ℝ φ x) (basisVec i) :=
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => hzeroOut x (fun hmem => hx (hφΩ hmem)))
    have h2 : (∫ x in Ω', ∑ i : Fin 3, u (x, s) i * (fderiv ℝ φ x) (basisVec i)) =
        ∫ x, ∑ i : Fin 3, u (x, s) i * (fderiv ℝ φ x) (basisVec i) :=
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => hzeroOut x (fun hmem => hx (hφΩ' hmem)))
    rw [h2, ← h1]
    exact hs
  have hdivAll := ae_slice_divergence_zero_of_forall_test hΩ'open hloc hsliceDiv
  have hP1all := pressureP1_cz_hP1_ae_of_sws hsol hη hηc hηΩ
    (lin34MeanVelocity u z.1 ρ)
  have hP1Intall := pressureP1_cz_hP1Int_ae_of_sws hsol hη hηc hηΩ
    (lin34MeanVelocity u z.1 ρ)
  have hsliceall := pressureCutoff_slice_data_ae_of_sws hsol hηc hηΩ
    (lin34MeanVelocity u z.1 ρ)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hTsubI hLp,
    ae_restrict_of_ae_restrict_of_subset hTsubI hdivAll,
    ae_restrict_of_ae_restrict_of_subset hTsubI hP1all,
    ae_restrict_of_ae_restrict_of_subset hTsubI hP1Intall,
    ae_restrict_of_ae_restrict_of_subset hTsubI hsliceall] with s hLps hdivs
    hP1s hP1Ints hslices
  have hmem : ∀ i : Fin 3, MemLp
      (fun y : Vec3 => u (y, s) i - lin34MeanVelocity u z.1 ρ s i) 2
      (volume.restrict Ω') := by
    intro i
    have hcomp : MemLp (fun y : Vec3 => u (y, s) i) 2 (volume.restrict Ω') :=
      hLps.1.continuousLinearMap_comp (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
    exact hcomp.sub (memLp_const (lin34MeanVelocity u z.1 ρ s i))
  have hum : ∀ j : Fin 3, IntegrableOn (fun y : Vec3 => u (y, s) j) Ω' volume := by
    intro j
    have hcomp : MemLp (fun y : Vec3 => u (y, s) j) 2 (volume.restrict Ω') :=
      hLps.1.continuousLinearMap_comp (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ)
    exact hcomp.integrable (by norm_num)
  have hUhat : ∀ i j : Fin 3, IntegrableOn
      (fun y : Vec3 => pressureUTensor (lin34CentredVelocity u z.1 ρ) 0
        ((y, s) : ParabolicPoint) i j)
      (tsupport (mollifiedBallCutoff z.1 hρ)) volume := by
    intro i j
    have hprod : Integrable (fun y : Vec3 =>
        (u (y, s) i - lin34MeanVelocity u z.1 ρ s i) *
          (u (y, s) j - lin34MeanVelocity u z.1 ρ s j)) (volume.restrict Ω') :=
      (hmem i).integrable_mul (hmem j)
    have hneg : Integrable (fun y : Vec3 =>
        -((u (y, s) i - lin34MeanVelocity u z.1 ρ s i) *
          (u (y, s) j - lin34MeanVelocity u z.1 ρ s j)))
        (volume.restrict Ω') := hprod.neg
    have hOn : IntegrableOn
        (fun y : Vec3 => pressureUTensor (lin34CentredVelocity u z.1 ρ) 0
          ((y, s) : ParabolicPoint) i j) Ω' volume := by
      refine hneg.congr (Filter.Eventually.of_forall ?_)
      intro y
      dsimp only
      simp only [pressureUTensor, lin34_centredVelocity_apply, Pi.zero_apply,
        sub_zero]
      ring
    exact hOn.mono_set hηΩ'
  refine ⟨fun ψ hψ hψc _ => ?_, fun ψ hψ hψc => ?_⟩
  · exact (lin34_centredP1_pairing_of_slice_data hρ hηΩ' hslices.1 hUhat hum
      hdivs hP1s hP1Ints hψ hψc).2
  · exact (lin34_centredP1_pairing_of_slice_data hρ hηΩ' hslices.1 hUhat hum
      hdivs hP1s hP1Ints hψ hψc).1

end CKN

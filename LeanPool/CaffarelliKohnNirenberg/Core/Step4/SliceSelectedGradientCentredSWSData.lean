/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientTensorSource
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCentredSourceTensor
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientInputsCentred
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientForceHolder
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SliceVelocityCube
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34CentredPairingSWS
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics

/-!
# Spatial slice data for the centred source

The regularity and incompressibility clauses of `def:sws` supply the local
norms, weak gradients, and zero trace used in `eq:pressure-gradient-decomposition`.
The exceptional set is chosen before quantifying over spatial test functions.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Core.Step4

/-- The spatial regularity data of `def:sws` on almost every cylinder slice. -/
theorem centredSWS_slice_data
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (fun x => u (x, s)) 3 (volume.restrict (vec3Ball z.1 ρ)) ∧
      MemLp (fun x => Du (x, s)) 2 (volume.restrict (vec3Ball z.1 ρ)) ∧
      MemLp (fun x => f (x, s)) (ENNReal.ofReal q)
        (volume.restrict (vec3Ball z.1 ρ)) ∧
      (∀ i, HasWeakGradientOn (vec3Ball z.1 ρ)
        (fun x => u (x, s) i) (fun x => Du (x, s) i)) := by
  obtain ⟨U, J, hbox, hB, hJ⟩ := pressure_box_geometry hsol hρ hsub
  have hLp := ae_restrict_of_ae_restrict_of_subset hJ (slice_memLp_ae_of_sws hsol hbox)
  have hwJ : ∀ᵐ s ∂volume.restrict J, ∀ i,
      HasWeakGradientOn U (fun x => u (x, s) i) (fun x => Du (x, s) i) := by
    rw [ae_all_iff]
    exact (hsol.2.2.2.2.2.1 U J hbox).2.2.2.2.2.2.2.2
  filter_upwards [hLp, ae_restrict_of_ae_restrict_of_subset hJ hwJ,
    velocity_norm_memLp_three_ae_on_ball_of_sws hsol hρ hsub,
    sws_force_memLp_slice_ae hsol hρ hsub] with s hs hw h₃ hf
  simp only [ENNReal.ofReal_ofNat] at h₃
  have hu₂ := hs.1.mono_measure (Measure.restrict_mono hB le_rfl)
  have hu₃ : MemLp (fun x => u (x, s)) 3 (volume.restrict (vec3Ball z.1 ρ)) := by
    apply h₃.of_le hu₂.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
      exact norm_le_vec3EuclideanNorm (u (x, s))
  exact ⟨hu₃, hs.2.mono_measure (Measure.restrict_mono hB le_rfl), hf,
    fun i => (hw i).restrict (isOpen_vec3Ball z.1 ρ) hB⟩

/-- Incompressibility in `def:sws` gives a zero spatial gradient trace on one
common almost-everywhere time set. -/
theorem centredSWS_trace_zero_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (fun x => ∑ i, Du (x, s) i i) =ᵐ[volume.restrict (vec3Ball z.1 ρ)] 0 := by
  let B := vec3Ball z.1 ρ
  let T := Ioc (z.2 - ρ ^ 2) z.2
  obtain ⟨U, J, hbox, hB, hT⟩ := pressure_box_geometry hsol hρ hsub
  have hBΩ : B ⊆ Ω := hB.trans (subset_closure.trans hbox.2.2.1)
  have hTI : T ⊆ I := hT.trans (subset_closure.trans hbox.2.2.2.2.2)
  have hdata := centredSWS_slice_data hsol hρ hsub
  have hloc : ∀ᵐ s ∂volume.restrict T, ∀ i,
      LocallyIntegrableOn (fun x => u (x, s) i) B volume := by
    filter_upwards [hdata] with s hs i
    exact locallyIntegrableOn_of_locallyIntegrable_restrict
      ((hs.1.eval i).locallyIntegrable (by norm_num))
  have htest : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ B → ∀ᵐ s ∂volume.restrict T,
        ∫ x in B, ∑ i, u (x, s) i * (fderiv ℝ ψ x) (basisVec i) = 0 := by
    intro ψ hψ hψc hψB
    have hψΩ := hψB.trans hBΩ
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hTI
      (divfree_slice_weak_of_suitable hsol ψ hψ hψc hψΩ)] with s hs
    have hout {A : Set Vec3} (hA : tsupport ψ ⊆ A) :
        (∫ x in A, ∑ i, u (x, s) i * (fderiv ℝ ψ x) (basisVec i)) =
          ∫ x, ∑ i, u (x, s) i * (fderiv ℝ ψ x) (basisVec i) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hx (hA h))]
      simp only [zero_apply, mul_zero, Finset.sum_const_zero]
    rw [hout hψB, ← hout hψΩ]
    exact hs
  have hdiv := ae_slice_divergence_zero_of_forall_test (isOpen_vec3Ball z.1 ρ) hloc htest
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr
    ((measure_mono (μ := volume) subset_closure).trans_lt
      (measure_closure_vec3Ball_lt_top hρ)).ne
  filter_upwards [hdata, hdiv] with s hs hd
  exact weak_gradient_trace_eq_zero_ae (isOpen_vec3Ball z.1 ρ)
    (fun i => (hs.1.eval i).mono_exponent (by norm_num))
    (fun i j => (hs.2.1.eval i).eval j) hs.2.2.2 hd

/-- The centred force-free source supplies the pairing in
`eq:pressure-gradient-decomposition` on almost every suitable-solution slice. -/
theorem centredSWS_pairing_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (c : ℝ → Vec3) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
        (∑ i, ∫ x, sourceMorreyCutoffVCentredTensorSpacetime
          (mollifiedBallCutoff z.1 hρ) (spatialDeriv (mollifiedBallCutoff z.1 hρ))
          u Du c (x, s) i * spatialDeriv ψ i x) =
        pressureSecondPairing (fun i j x => mollifiedBallCutoff z.1 hρ x *
          pressureUTensor u c (x, s) i j) ψ := by
  have hfinite : (volume.restrict (vec3Ball z.1 ρ)) univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono (μ := volume) subset_closure).trans_lt
      (measure_closure_vec3Ball_lt_top hρ)
  have : IsFiniteMeasure (volume.restrict (vec3Ball z.1 ρ)) := ⟨hfinite⟩
  filter_upwards [centredSWS_slice_data hsol hρ hsub,
    centredSWS_trace_zero_ae hsol hρ hsub] with s hs ht
  intro ψ hψ
  exact pressureDivergenceCutoffSourceCentredTensor_pairing_of_weak_data
    (c := c s) (isOpen_vec3Ball z.1 ρ) (mollifiedBallCutoff_smooth z.1 hρ)
    (mollifiedBallCutoff_hasCompactSupport z.1 hρ)
    (pressure_cutoff_support_subset_ball z.1 hρ) (fun _ => rfl) hfinite
    (fun i => (hs.1.eval i).mono_exponent (by norm_num))
    (fun i j => (hs.2.1.eval i).eval j) hs.2.2.2 ht hψ

end CKN.Core.Step4

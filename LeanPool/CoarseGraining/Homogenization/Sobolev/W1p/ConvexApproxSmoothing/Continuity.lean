/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.WeakDerivSmoothing

/-! # Continuity -/

namespace Homogenization

open scoped Pointwise Convolution

/-!
# Continuity, pointwise fderiv, and ae-equality for the smoothing

Concludes the weak-derivative chain with `ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec`,
then pivots to the pointwise-classical world: continuity of `convexApproxSample`,
`convexApproxIntegrand`, and the derived oscillation / weighted / kernel-times-
const integrands; continuity of `convexApproxSmoothing`; the parametric
`convexApproxFDerivIntegrand` and the explicit `hasFDerivAt_convexApproxSmoothing_of_contDiff`
computation (including its `apply_basisVec` form).
-/

theorem ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {i : Fin d} {u gi ρ : Vec d → ℝ} {p : ENNReal}
    (hρ : IsConvexApproxKernel ρ) (hp1 : 1 ≤ p)
    (huMem : MemLpOn U p u) (hgiMem : MemLpOn U p gi)
    (huWeak : HasWeakPartialDerivOn U i u gi)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    (fun x => (fderiv ℝ (Homogenization.convexApproxSmoothRepresentative U ρ u x0 r ε) x)
        (basisVec i)) =ᵐ[MeasureTheory.volume.restrict U]
      fun x => (1 - ε) *
        Homogenization.convexApproxSmoothRepresentative U ρ gi x0 r ε x := by
  have huLoc : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume :=
    MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      (huMem.locallyIntegrable hp1)
  have hgiLoc : MeasureTheory.LocallyIntegrableOn gi U MeasureTheory.volume :=
    MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      (hgiMem.locallyIntegrable hp1)
  have hsmooth :
      ContDiff ℝ (⊤ : ℕ∞)
        (Homogenization.convexApproxSmoothRepresentative U ρ u x0 r ε) :=
    contDiff_convexApproxSmoothRepresentative hU.1.measurableSet hρ hp1 huMem hr hε0
  have hgi_smooth :
      ContDiff ℝ (⊤ : ℕ∞)
        (Homogenization.convexApproxSmoothRepresentative U ρ gi x0 r ε) :=
    contDiff_convexApproxSmoothRepresentative hU.1.measurableSet hρ hp1 hgiMem hr hε0
  have hclassWeak :
      HasWeakPartialDerivOn U i
        (Homogenization.convexApproxSmoothRepresentative U ρ u x0 r ε)
        (fun x => (fderiv ℝ
            (Homogenization.convexApproxSmoothRepresentative U ρ u x0 r ε) x)
          (basisVec i)) :=
    HasWeakPartialDerivOn.of_contDiff (U := U) (i := i)
      (f := Homogenization.convexApproxSmoothRepresentative U ρ u x0 r ε)
      (hsmooth.of_le (by simp))
  have hroughWeak :
      HasWeakPartialDerivOn U i
        (Homogenization.convexApproxSmoothRepresentative U ρ u x0 r ε)
        (fun x => (1 - ε) *
          Homogenization.convexApproxSmoothRepresentative U ρ gi x0 r ε x) :=
    HasWeakPartialDerivOn.convexApproxSmoothRepresentative (i := i) hU huLoc hgiLoc huWeak
      hρ hball hr hε0 hε1
  have hclass_cont :
      Continuous
        (fun x => (fderiv ℝ
            (Homogenization.convexApproxSmoothRepresentative U ρ u x0 r ε) x)
          (basisVec i)) := by
    simpa using (hsmooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hrough_cont :
      Continuous
        (fun x => (1 - ε) *
          Homogenization.convexApproxSmoothRepresentative U ρ gi x0 r ε x) := by
    simpa using! continuous_const.mul hgi_smooth.continuous
  have hclassLoc :
      MeasureTheory.LocallyIntegrableOn
        (fun x => (fderiv ℝ
            (Homogenization.convexApproxSmoothRepresentative U ρ u x0 r ε) x)
          (basisVec i)) U MeasureTheory.volume :=
    hclass_cont.continuousOn.locallyIntegrableOn hU.1.measurableSet
  have hroughLoc :
      MeasureTheory.LocallyIntegrableOn
        (fun x => (1 - ε) *
          Homogenization.convexApproxSmoothRepresentative U ρ gi x0 r ε x) U
          MeasureTheory.volume :=
    hrough_cont.continuousOn.locallyIntegrableOn hU.1.measurableSet
  exact HasWeakPartialDerivOn.ae_eq hU.1 hclassLoc hroughLoc hclassWeak hroughWeak

theorem continuous_convexApproxSample_right {d : ℕ} (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    Continuous (fun z : Vec d => convexApproxSample x0 z r ε x) := by
  simpa [convexApproxSample] using!
    (continuous_const : Continuous (fun _ : Vec d => (1 - ε) • x)).add
      ((continuous_const : Continuous (fun _ : Vec d => ε)).smul
        ((continuous_const : Continuous (fun _ : Vec d => x0)).sub
          ((continuous_const : Continuous (fun _ : Vec d => r)).smul
            (continuous_id : Continuous (fun z : Vec d => z)))))

theorem continuous_convexApproxSample_prod {d : ℕ} (x0 : Vec d) (r ε : ℝ) :
    Continuous (fun p : Vec d × Vec d => convexApproxSample x0 p.2 r ε p.1) := by
  simpa [convexApproxSample] using!
    ((continuous_const : Continuous (fun _ : Vec d × Vec d => 1 - ε)).smul
        (continuous_fst : Continuous (fun p : Vec d × Vec d => p.1))).add
      ((continuous_const : Continuous (fun _ : Vec d × Vec d => ε)).smul
        ((continuous_const : Continuous (fun _ : Vec d × Vec d => x0)).sub
          ((continuous_const : Continuous (fun _ : Vec d × Vec d => r)).smul
            (continuous_snd : Continuous (fun p : Vec d × Vec d => p.2)))))

theorem continuous_convexApproxIntegrand_right {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    Continuous (fun z => convexApproxIntegrand ρ u x0 r ε x z) := by
  simpa [convexApproxIntegrand] using!
    hρ.mul (hu.comp (continuous_convexApproxSample_right x0 r ε x))

theorem continuous_convexApproxIntegrand_left {d : ℕ} {ρ u : Vec d → ℝ}
    (hu : Continuous u) (x0 z : Vec d) (r ε : ℝ) :
    Continuous (fun x => convexApproxIntegrand ρ u x0 r ε x z) := by
  simpa [convexApproxIntegrand] using!
    continuous_const.mul (hu.comp (continuous_convexApproxSample x0 z r ε))

theorem continuous_convexApproxIntegrand_prod {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) :
    Continuous (fun p : Vec d × Vec d => convexApproxIntegrand ρ u x0 r ε p.1 p.2) := by
  have hρ' : Continuous (fun p : Vec d × Vec d => ρ p.2) := hρ.comp continuous_snd
  have hu' : Continuous (fun p : Vec d × Vec d => u (convexApproxSample x0 p.2 r ε p.1)) :=
    hu.comp (continuous_convexApproxSample_prod x0 r ε)
  simpa [convexApproxIntegrand] using! hρ'.mul hu'

theorem tsupport_convexApproxIntegrand_subset {d : ℕ} {ρ u : Vec d → ℝ}
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    tsupport (fun z => convexApproxIntegrand ρ u x0 r ε x z) ⊆ tsupport ρ := by
  simpa [convexApproxIntegrand] using
    (tsupport_mul_subset_left (f := ρ)
      (g := fun z => u (convexApproxSample x0 z r ε x)))

theorem hasCompactSupport_convexApproxIntegrand {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : HasCompactSupport ρ) (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    HasCompactSupport (fun z => convexApproxIntegrand ρ u x0 r ε x z) := by
  simpa [convexApproxIntegrand] using!
    (hρ.mul_right : HasCompactSupport
      (fun z => ρ z * u (convexApproxSample x0 z r ε x)))

theorem integrable_convexApproxIntegrand {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ) (hρ_compact : HasCompactSupport ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    MeasureTheory.Integrable (fun z => convexApproxIntegrand ρ u x0 r ε x z) := by
  exact
    (continuous_convexApproxIntegrand_right hρ hu x0 r ε x).integrable_of_hasCompactSupport
      (hasCompactSupport_convexApproxIntegrand hρ_compact x0 r ε x)

theorem continuous_convexApproxDifferenceIntegrand {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    Continuous (fun z => ρ z * (u (convexApproxSample x0 z r ε x) - u x)) := by
  exact hρ.mul ((hu.comp (continuous_convexApproxSample_right x0 r ε x)).sub continuous_const)

theorem hasCompactSupport_convexApproxDifferenceIntegrand {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ_compact : HasCompactSupport ρ) (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    HasCompactSupport (fun z => ρ z * (u (convexApproxSample x0 z r ε x) - u x)) := by
  simpa using!
    (hρ_compact.mul_right : HasCompactSupport
      (fun z => ρ z * (u (convexApproxSample x0 z r ε x) - u x)))

theorem integrable_convexApproxDifferenceIntegrand {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ) (hρ_compact : HasCompactSupport ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    MeasureTheory.Integrable (fun z => ρ z * (u (convexApproxSample x0 z r ε x) - u x)) := by
  exact
    (continuous_convexApproxDifferenceIntegrand hρ hu x0 r ε x).integrable_of_hasCompactSupport
      (hasCompactSupport_convexApproxDifferenceIntegrand hρ_compact x0 r ε x)

theorem continuous_convexApproxWeightedOscillation {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    Continuous (fun z => ρ z * |u (convexApproxSample x0 z r ε x) - u x|) := by
  exact
    hρ.mul (((hu.comp (continuous_convexApproxSample_right x0 r ε x)).sub
      continuous_const).abs)

theorem hasCompactSupport_convexApproxWeightedOscillation {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ_compact : HasCompactSupport ρ) (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    HasCompactSupport (fun z => ρ z * |u (convexApproxSample x0 z r ε x) - u x|) := by
  simpa using!
    (hρ_compact.mul_right : HasCompactSupport
      (fun z => ρ z * |u (convexApproxSample x0 z r ε x) - u x|))

theorem integrable_convexApproxWeightedOscillation {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ) (hρ_compact : HasCompactSupport ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    MeasureTheory.Integrable (fun z => ρ z * |u (convexApproxSample x0 z r ε x) - u x|) := by
  exact
    (continuous_convexApproxWeightedOscillation hρ hu x0 r ε x).integrable_of_hasCompactSupport
      (hasCompactSupport_convexApproxWeightedOscillation hρ_compact x0 r ε x)

theorem integrable_convexApproxKernelMulConst {d : ℕ} {ρ : Vec d → ℝ}
    (hρ : Continuous ρ) (hρ_compact : HasCompactSupport ρ) (c : ℝ) :
    MeasureTheory.Integrable (fun z => ρ z * c) := by
  have hcont : Continuous (fun z => ρ z * c) := hρ.mul continuous_const
  have hcomp : HasCompactSupport (fun z => ρ z * c) := by
    simpa using! (hρ_compact.mul_right : HasCompactSupport (fun z => ρ z * c))
  exact hcont.integrable_of_hasCompactSupport hcomp

theorem continuous_convexApproxSmoothing {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ) (hρ_compact : HasCompactSupport ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) :
    Continuous (convexApproxSmoothing ρ u x0 r ε) := by
  have hcont :
      Continuous (Function.uncurry (fun x z => convexApproxIntegrand ρ u x0 r ε x z)) := by
    simpa [Function.uncurry] using! continuous_convexApproxIntegrand_prod hρ hu x0 r ε
  simpa [convexApproxSmoothing] using!
    (continuous_parametric_integral_of_continuous
      (μ := MeasureTheory.volume)
      (f := fun x z => convexApproxIntegrand ρ u x0 r ε x z)
      hcont hρ_compact.isCompact)

/-- The pointwise Fréchet-derivative integrand of the convex smoothing operator. -/
noncomputable def convexApproxFDerivIntegrand {d : ℕ} (ρ u : Vec d → ℝ)
    (x0 : Vec d) (r ε : ℝ) (x z : Vec d) : Vec d →L[ℝ] ℝ :=
  ((ρ z) * (1 - ε)) • fderiv ℝ u (convexApproxSample x0 z r ε x)

@[simp] theorem convexApproxFDerivIntegrand_apply {d : ℕ} (ρ u : Vec d → ℝ)
    (x0 : Vec d) (r ε : ℝ) (x z : Vec d) :
    convexApproxFDerivIntegrand ρ u x0 r ε x z =
      ((ρ z) * (1 - ε)) • fderiv ℝ u (convexApproxSample x0 z r ε x) :=
  rfl

theorem continuous_convexApproxFDerivIntegrand_right {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ) (hu : ContDiff ℝ 1 u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    Continuous (fun z => convexApproxFDerivIntegrand ρ u x0 r ε x z) := by
  have hscalar : Continuous (fun z => (ρ z) * (1 - ε)) := hρ.mul continuous_const
  have hfderiv :
      Continuous (fun z => fderiv ℝ u (convexApproxSample x0 z r ε x)) :=
    (hu.continuous_fderiv (by simp)).comp (continuous_convexApproxSample_right x0 r ε x)
  simpa [convexApproxFDerivIntegrand] using! hscalar.smul hfderiv

theorem hasCompactSupport_convexApproxFDerivIntegrand {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ_compact : HasCompactSupport ρ) (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    HasCompactSupport (fun z => convexApproxFDerivIntegrand ρ u x0 r ε x z) := by
  refine HasCompactSupport.of_support_subset_isCompact hρ_compact.isCompact ?_
  intro z hz
  by_contra hzρ
  apply hz
  have hρz : ρ z = 0 := image_eq_zero_of_notMem_tsupport (f := ρ) hzρ
  simp [convexApproxFDerivIntegrand, hρz]

theorem integrable_convexApproxFDerivIntegrand {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ) (hρ_compact : HasCompactSupport ρ) (hu : ContDiff ℝ 1 u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    MeasureTheory.Integrable (fun z => convexApproxFDerivIntegrand ρ u x0 r ε x z) := by
  exact
    (continuous_convexApproxFDerivIntegrand_right hρ hu x0 r ε x).integrable_of_hasCompactSupport
      (hasCompactSupport_convexApproxFDerivIntegrand hρ_compact x0 r ε x)

theorem hasFDerivAt_convexApproxSample {d : ℕ} (x0 z : Vec d) (r ε : ℝ) (x : Vec d) :
    HasFDerivAt (convexApproxSample x0 z r ε) ((1 - ε) • ContinuousLinearMap.id ℝ (Vec d)) x := by
  simpa [convexApproxSample] using
    ((((1 - ε) • ContinuousLinearMap.id ℝ (Vec d)).hasFDerivAt).add_const (ε • (x0 - r • z)))

theorem hasFDerivAt_convexApproxIntegrand_left_of_contDiff {d : ℕ} {ρ u : Vec d → ℝ}
    (_hρ : Continuous ρ) (hu : ContDiff ℝ 1 u)
    (x0 : Vec d) (r ε : ℝ) (x z : Vec d) :
    HasFDerivAt (fun y => convexApproxIntegrand ρ u x0 r ε y z)
      (convexApproxFDerivIntegrand ρ u x0 r ε x z) x := by
  have hu_deriv :
      HasFDerivAt u (fderiv ℝ u (convexApproxSample x0 z r ε x))
        (convexApproxSample x0 z r ε x) := by
    exact (hu.contDiffAt.differentiableAt (by simp)).hasFDerivAt
  have hsample :
      HasFDerivAt (convexApproxSample x0 z r ε) ((1 - ε) • ContinuousLinearMap.id ℝ (Vec d)) x :=
    hasFDerivAt_convexApproxSample x0 z r ε x
  have hcomp :
      HasFDerivAt
        (fun y => u (convexApproxSample x0 z r ε y))
        ((fderiv ℝ u (convexApproxSample x0 z r ε x)).comp
          (((1 - ε) • ContinuousLinearMap.id ℝ (Vec d)))) x :=
    hu_deriv.comp x hsample
  have hcomp' :
      HasFDerivAt
        (fun y => u (convexApproxSample x0 z r ε y))
        ((1 - ε) • fderiv ℝ u (convexApproxSample x0 z r ε x)) x := by
    convert hcomp using 1
    ext v
    simp
  simpa [convexApproxIntegrand, convexApproxFDerivIntegrand, smul_smul, mul_assoc,
    mul_left_comm, mul_comm] using hcomp'.const_mul (ρ z)

theorem hasFDerivAt_convexApproxSmoothing_of_contDiff {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) (hu : ContDiff ℝ 1 u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    HasFDerivAt (convexApproxSmoothing ρ u x0 r ε)
      (∫ z in tsupport ρ, convexApproxFDerivIntegrand ρ u x0 r ε x z) x := by
  let μ : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict (tsupport ρ)
  let F : Vec d → Vec d → ℝ := fun x' z => convexApproxIntegrand ρ u x0 r ε x' z
  let F' : Vec d → Vec d → Vec d →L[ℝ] ℝ :=
    fun x' z => convexApproxFDerivIntegrand ρ u x0 r ε x' z
  let S : Set (Vec d × Vec d) := Metric.closedBall x 1 ×ˢ tsupport ρ
  let K : Set (Vec d) := (fun p : Vec d × Vec d => convexApproxSample x0 p.2 r ε p.1) '' S
  have hF_meas : ∀ᶠ x' in nhds x, MeasureTheory.AEStronglyMeasurable (F x') μ := by
    refine Filter.Eventually.of_forall ?_
    intro x'
    exact Continuous.aestronglyMeasurable (μ := μ)
      (continuous_convexApproxIntegrand_right hρ.continuous hu.continuous x0 r ε x')
  have hF_int : MeasureTheory.Integrable (F x) μ := by
    have hF_int_volume :
        MeasureTheory.Integrable
          (fun z => convexApproxIntegrand ρ u x0 r ε x z) MeasureTheory.volume :=
      integrable_convexApproxIntegrand hρ.continuous hρ.compactSupport hu.continuous x0 r ε x
    simpa [F, μ] using
      (MeasureTheory.Integrable.restrict (s := tsupport ρ) hF_int_volume)
  have hF'_meas : MeasureTheory.AEStronglyMeasurable (F' x) μ := by
    exact Continuous.aestronglyMeasurable (μ := μ)
      (continuous_convexApproxFDerivIntegrand_right hρ.continuous hu x0 r ε x)
  have hS_compact : IsCompact S := (isCompact_closedBall x 1).prod hρ.compactSupport.isCompact
  have hK_compact : IsCompact K := by
    exact hS_compact.image (continuous_convexApproxSample_prod x0 r ε)
  let g : Vec d → ℝ := fun y => ‖fderiv ℝ u y‖
  have hg_cont : Continuous g := by
    simpa [g] using (hu.continuous_fderiv (by simp)).norm
  have hg_contOn : ContinuousOn g K := hg_cont.continuousOn
  obtain ⟨C, hC⟩ : ∃ C, ∀ t ∈ g '' K, ‖t‖ ≤ C := by
    exact (hK_compact.image_of_continuousOn hg_contOn).isBounded.exists_norm_le
  let B : ℝ := max C 0
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  let bound : Vec d → ℝ := fun z => ρ z * (|1 - ε| * B)
  have h_bound : ∀ᵐ z ∂μ, ∀ x' ∈ Metric.ball x 1, ‖F' x' z‖ ≤ bound z := by
    refine Filter.Eventually.of_forall ?_
    intro z
    by_cases hz : z ∈ tsupport ρ
    · intro x' hx'
      have hx'closed : x' ∈ Metric.closedBall x 1 := Metric.ball_subset_closedBall hx'
      have hsample_memK : convexApproxSample x0 z r ε x' ∈ K := by
        exact Set.mem_image_of_mem
          (fun p : Vec d × Vec d => convexApproxSample x0 p.2 r ε p.1)
          (show (x', z) ∈ S by
            exact ⟨hx'closed, hz⟩)
      have hg_mem : g (convexApproxSample x0 z r ε x') ∈ g '' K :=
        Set.mem_image_of_mem g hsample_memK
      have hnorm_fderiv : ‖fderiv ℝ u (convexApproxSample x0 z r ε x')‖ ≤ B := by
        calc
          ‖fderiv ℝ u (convexApproxSample x0 z r ε x')‖
              = g (convexApproxSample x0 z r ε x') := by rfl
          _ ≤ C := by
              simpa [g, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hC _ hg_mem
          _ ≤ B := le_max_left _ _
      have hF' : F' x' z = convexApproxFDerivIntegrand ρ u x0 r ε x' z := by
        rfl
      calc
        ‖F' x' z‖ = |ρ z| * |1 - ε| * ‖fderiv ℝ u (convexApproxSample x0 z r ε x')‖ := by
          rw [hF', convexApproxFDerivIntegrand, norm_smul, Real.norm_eq_abs, abs_mul, mul_assoc]
        _ = ρ z * (|1 - ε| * ‖fderiv ℝ u (convexApproxSample x0 z r ε x')‖) := by
          rw [abs_of_nonneg (hρ.nonneg z)]
          ring
        _ ≤ ρ z * (|1 - ε| * B) := by
          refine mul_le_mul_of_nonneg_left ?_ (hρ.nonneg z)
          exact mul_le_mul_of_nonneg_left hnorm_fderiv (abs_nonneg _)
        _ = bound z := by
          simp [bound]
    · intro x' hx'
      have hρz : ρ z = 0 := image_eq_zero_of_notMem_tsupport (f := ρ) hz
      simp [F', convexApproxFDerivIntegrand, bound, hρz]
  have hbound_integrable : MeasureTheory.Integrable bound μ := by
    have hbound_volume :
        MeasureTheory.Integrable (fun z => ρ z * (|1 - ε| * B)) MeasureTheory.volume :=
      integrable_convexApproxKernelMulConst hρ.continuous hρ.compactSupport (|1 - ε| * B)
    simpa [bound, μ, mul_assoc, mul_left_comm, mul_comm] using
      (MeasureTheory.Integrable.restrict (s := tsupport ρ) hbound_volume)
  have h_diff : ∀ᵐ z ∂μ, ∀ x' ∈ Metric.ball x 1, HasFDerivAt (F · z) (F' x' z) x' := by
    refine Filter.Eventually.of_forall ?_
    intro z x' hx'
    simpa [F, F'] using
      hasFDerivAt_convexApproxIntegrand_left_of_contDiff hρ.continuous hu x0 r ε x' z
  have hmain :
      HasFDerivAt (fun x' => ∫ z, F x' z ∂μ) (∫ z, F' x z ∂μ) x := by
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le
      (x₀ := x) (μ := μ) (s := Metric.ball x 1) (hs := Metric.ball_mem_nhds x zero_lt_one)
      (F := F) (F' := F') (bound := bound)
      hF_meas hF_int hF'_meas h_bound hbound_integrable h_diff
  simpa [convexApproxSmoothing, μ, F, F'] using! hmain

theorem fderiv_convexApproxSmoothing_of_contDiff {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) (hu : ContDiff ℝ 1 u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    fderiv ℝ (convexApproxSmoothing ρ u x0 r ε) x =
      ∫ z in tsupport ρ, convexApproxFDerivIntegrand ρ u x0 r ε x z := by
  exact (hasFDerivAt_convexApproxSmoothing_of_contDiff hρ hu x0 r ε x).fderiv

theorem fderiv_convexApproxSmoothing_apply_basisVec_of_contDiff {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) (hu : ContDiff ℝ 1 u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) (i : Fin d) :
    (fderiv ℝ (convexApproxSmoothing ρ u x0 r ε) x) (basisVec i) =
      (1 - ε) *
        convexApproxSmoothing ρ
          (fun y => (fderiv ℝ u y) (basisVec i)) x0 r ε x := by
  have hInt :
      MeasureTheory.Integrable
        (fun z => convexApproxFDerivIntegrand ρ u x0 r ε x z)
        (MeasureTheory.volume.restrict (tsupport ρ)) := by
    have hInt_volume :
        MeasureTheory.Integrable
          (fun z => convexApproxFDerivIntegrand ρ u x0 r ε x z) MeasureTheory.volume :=
      integrable_convexApproxFDerivIntegrand hρ.continuous hρ.compactSupport hu x0 r ε x
    simpa using
      (MeasureTheory.Integrable.restrict (s := tsupport ρ) hInt_volume)
  calc
    (fderiv ℝ (convexApproxSmoothing ρ u x0 r ε) x) (basisVec i)
        = (∫ z in tsupport ρ, convexApproxFDerivIntegrand ρ u x0 r ε x z) (basisVec i) := by
            rw [fderiv_convexApproxSmoothing_of_contDiff hρ hu x0 r ε x]
    _ = ∫ z in tsupport ρ, (convexApproxFDerivIntegrand ρ u x0 r ε x z) (basisVec i) := by
          simpa using ContinuousLinearMap.integral_apply hInt (basisVec i)
    _ = ∫ z in tsupport ρ,
          ((1 - ε) * (ρ z * (fderiv ℝ u (convexApproxSample x0 z r ε x) (basisVec i)))) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with z
            simp [convexApproxFDerivIntegrand]
            ring
    _ = (1 - ε) *
          ∫ z in tsupport ρ, ρ z * (fderiv ℝ u (convexApproxSample x0 z r ε x) (basisVec i)) := by
            rw [MeasureTheory.integral_const_mul]
    _ = (1 - ε) *
          convexApproxSmoothing ρ
            (fun y => (fderiv ℝ u y) (basisVec i)) x0 r ε x := by
            simp [convexApproxSmoothing, convexApproxIntegrand]

end Homogenization

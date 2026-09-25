/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.WeakDerivComp

/-! # Weak Deriv Smoothing -/

@[expose] public section

namespace Homogenization

open scoped Pointwise Convolution

/-!
# Weak derivatives of the convex smoothing operator

Lifts `HasWeakPartialDerivOn` (and the `HasWeakGradientOn` gradient variant)
through `convexApproxSmoothing` and the globally smooth representative
`convexApproxSmoothRepresentative`.
-/

theorem HasWeakPartialDerivOn.convexApproxSmoothing
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {i : Fin d} {u gi ρ : Vec d → ℝ}
    (huLoc : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume)
    (hgiLoc : MeasureTheory.LocallyIntegrableOn gi U MeasureTheory.volume)
    (hu : HasWeakPartialDerivOn U i u gi)
    (hρ : IsConvexApproxKernel ρ)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    HasWeakPartialDerivOn U i
      (Homogenization.convexApproxSmoothing ρ u x0 r ε)
      (fun x => (1 - ε) * Homogenization.convexApproxSmoothing ρ gi x0 r ε x) := by
  intro φ hφ_smooth hφ_compact hφ_sub
  let dφ : Vec d → ℝ := fun x => (fderiv ℝ φ x) (basisVec i)
  let φε : Vec d → ℝ := fun x => (1 - ε) * φ x
  let F : Vec d → Vec d → ℝ := fun x z =>
    ρ z * Set.indicator U u (convexApproxSample x0 z r ε x) * dφ x
  let G : Vec d → Vec d → ℝ := fun x z =>
    ρ z * Set.indicator U gi (convexApproxSample x0 z r ε x) * φε x
  have hdφ_cont : Continuous dφ := by
    simpa [dφ] using
      (hφ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφ_compact : HasCompactSupport dφ := by
    simpa [dφ] using hφ_compact.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hdφ_support_sub : Function.support dφ ⊆ tsupport φ := by
    intro x hx
    exact
      (support_fderiv_subset (𝕜 := ℝ) (f := φ)) <| by
        change fderiv ℝ φ x ≠ 0
        intro hzero
        apply hx
        simp [dφ, hzero]
  have hdφ_subφ : tsupport dφ ⊆ tsupport φ :=
    closure_minimal hdφ_support_sub (isClosed_tsupport (f := φ))
  have hdφ_sub : tsupport dφ ⊆ U := hdφ_subφ.trans hφ_sub
  have hφε_cont : Continuous φε := by
    simpa [φε] using! continuous_const.mul hφ_smooth.continuous
  have hφε_compact : HasCompactSupport φε := by
    simpa [φε] using! (HasCompactSupport.mul_left (f := fun _ : Vec d => 1 - ε) hφ_compact)
  have hφε_subφ : tsupport φε ⊆ tsupport φ := by
    let hsub :=
      tsupport_mul_subset_right (f := fun _ : Vec d => 1 - ε) (g := φ)
    intro x hx
    exact hsub (by simpa [φε] using hx)
  have hφε_sub : tsupport φε ⊆ U := hφε_subφ.trans hφ_sub
  have hprod_left :
      MeasureTheory.Integrable
        (fun p : Vec d × Vec d => F p.1 p.2)
        ((MeasureTheory.volume.restrict (tsupport dφ)).prod
          (MeasureTheory.volume.restrict (tsupport ρ))) := by
    simpa [F, dφ] using
      integrable_kernel_mul_indicator_comp_convexApproxSample_prod_mul_of_locallyIntegrableOn
        hU huLoc hρ hdφ_cont hdφ_compact hdφ_sub hball hr hε0 hε1
  have hprod_right :
      MeasureTheory.Integrable
        (fun p : Vec d × Vec d => G p.1 p.2)
        ((MeasureTheory.volume.restrict (tsupport φε)).prod
          (MeasureTheory.volume.restrict (tsupport ρ))) := by
    simpa [G, φε] using
      integrable_kernel_mul_indicator_comp_convexApproxSample_prod_mul_of_locallyIntegrableOn
        hU hgiLoc hρ hφε_cont hφε_compact hφε_sub hball hr hε0 hε1
  have hswap_left :
      ∫ x in tsupport dφ, ∫ z in tsupport ρ, F x z ∂MeasureTheory.volume ∂MeasureTheory.volume =
        ∫ z in tsupport ρ, ∫ x in tsupport dφ, F x z ∂MeasureTheory.volume ∂MeasureTheory.volume := by
    simpa using
      (MeasureTheory.integral_integral_swap
        (μ := MeasureTheory.volume.restrict (tsupport dφ))
        (ν := MeasureTheory.volume.restrict (tsupport ρ))
        (f := F) hprod_left)
  have hswap_right :
      ∫ x in tsupport φε, ∫ z in tsupport ρ, G x z ∂MeasureTheory.volume ∂MeasureTheory.volume =
        ∫ z in tsupport ρ, ∫ x in tsupport φε, G x z ∂MeasureTheory.volume ∂MeasureTheory.volume := by
    simpa using
      (MeasureTheory.integral_integral_swap
        (μ := MeasureTheory.volume.restrict (tsupport φε))
        (ν := MeasureTheory.volume.restrict (tsupport ρ))
        (f := G) hprod_right)
  have hleft_restrict :
      ∫ x in U, Homogenization.convexApproxSmoothing ρ u x0 r ε x * dφ x ∂MeasureTheory.volume =
        ∫ x in tsupport dφ, Homogenization.convexApproxSmoothing ρ u x0 r ε x * dφ x
          ∂MeasureTheory.volume := by
    exact
      MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        hU.1.measurableSet hdφ_sub (fun x hx => by
          simp [dφ, image_eq_zero_of_notMem_tsupport hx.2])
  have hright_restrict :
      ∫ x in U, Homogenization.convexApproxSmoothing ρ gi x0 r ε x * φε x
          ∂MeasureTheory.volume =
        ∫ x in tsupport φε, Homogenization.convexApproxSmoothing ρ gi x0 r ε x * φε x
          ∂MeasureTheory.volume := by
    exact
      MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        hU.1.measurableSet hφε_sub (fun x hx => by
          simp [φε, image_eq_zero_of_notMem_tsupport hx.2])
  have hinner_left_eq :
      ∫ x in tsupport dφ, Homogenization.convexApproxSmoothing ρ u x0 r ε x * dφ x
          ∂MeasureTheory.volume =
        ∫ x in tsupport dφ, ∫ z in tsupport ρ, F x z ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun hdφ_compact.isCompact.measurableSet ?_
    intro x hx
    have hxU : x ∈ U := hdφ_sub hx
    have hsample_mem : ∀ z ∈ tsupport ρ, convexApproxSample x0 z r ε x ∈ U := by
      intro z hz
      have hz_norm : ‖z‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hρ.support_subset_closedBall hz
      exact
        convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain hU hball hr hz_norm hε0
          (le_of_lt hε1) hxU
    calc
      Homogenization.convexApproxSmoothing ρ u x0 r ε x * dφ x
          = (∫ z in tsupport ρ, ρ z * u (convexApproxSample x0 z r ε x)
              ∂MeasureTheory.volume) * dφ x := by
                rfl
      _ = ∫ z in tsupport ρ, (ρ z * u (convexApproxSample x0 z r ε x)) * dφ x
            ∂MeasureTheory.volume := by
              rw [← MeasureTheory.integral_mul_const]
      _ = ∫ z in tsupport ρ, F x z ∂MeasureTheory.volume := by
            refine MeasureTheory.setIntegral_congr_fun hρ.compactSupport.isCompact.measurableSet ?_
            intro z hz
            let y : Vec d := convexApproxSample x0 z r ε x
            have hy_mem : y ∈ U := hsample_mem z hz
            change ρ z * u y * dφ x = ρ z * Set.indicator U u y * dφ x
            have hy_eq : Set.indicator U u y = u y := Set.indicator_of_mem (s := U) (f := u) hy_mem
            simpa [mul_assoc] using congrArg (fun t => ρ z * t * dφ x) hy_eq.symm
  have hinner_right_eq :
      ∫ x in tsupport φε, Homogenization.convexApproxSmoothing ρ gi x0 r ε x * φε x
          ∂MeasureTheory.volume =
        ∫ x in tsupport φε, ∫ z in tsupport ρ, G x z ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun hφε_compact.isCompact.measurableSet ?_
    intro x hx
    have hxU : x ∈ U := hφε_sub hx
    have hsample_mem : ∀ z ∈ tsupport ρ, convexApproxSample x0 z r ε x ∈ U := by
      intro z hz
      have hz_norm : ‖z‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hρ.support_subset_closedBall hz
      exact
        convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain hU hball hr hz_norm hε0
          (le_of_lt hε1) hxU
    calc
      Homogenization.convexApproxSmoothing ρ gi x0 r ε x * φε x
          = (∫ z in tsupport ρ, ρ z * gi (convexApproxSample x0 z r ε x)
              ∂MeasureTheory.volume) * φε x := by
                rfl
      _ = ∫ z in tsupport ρ, (ρ z * gi (convexApproxSample x0 z r ε x)) * φε x
            ∂MeasureTheory.volume := by
              rw [← MeasureTheory.integral_mul_const]
      _ = ∫ z in tsupport ρ, G x z ∂MeasureTheory.volume := by
            refine MeasureTheory.setIntegral_congr_fun hρ.compactSupport.isCompact.measurableSet ?_
            intro z hz
            let y : Vec d := convexApproxSample x0 z r ε x
            have hy_mem : y ∈ U := hsample_mem z hz
            change ρ z * gi y * φε x = ρ z * Set.indicator U gi y * φε x
            have hy_eq : Set.indicator U gi y = gi y := Set.indicator_of_mem (s := U) (f := gi) hy_mem
            simpa [mul_assoc] using congrArg (fun t => ρ z * t * φε x) hy_eq.symm
  have hfixed_z :
      ∀ z ∈ tsupport ρ,
        ∫ x in tsupport dφ, F x z ∂MeasureTheory.volume =
          -∫ x in tsupport φε, G x z ∂MeasureTheory.volume := by
    intro z hz
    have hz_norm : ‖z‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hρ.support_subset_closedBall hz
    have hmap :
        Set.MapsTo (convexApproxSample x0 z r ε) U U :=
      convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain hU hball hr hz_norm hε0
        (le_of_lt hε1)
    have hweak_z :
        ∫ x in U, u (convexApproxSample x0 z r ε x) * dφ x ∂MeasureTheory.volume =
          -∫ x in U, ((1 - ε) * gi (convexApproxSample x0 z r ε x)) * φ x
            ∂MeasureTheory.volume := by
      simpa [dφ] using
        ((hu.comp_convexApproxSample hU hball hr hz_norm hε0 hε1) φ hφ_smooth hφ_compact hφ_sub)
    have hleft_z :
        ∫ x in tsupport dφ, F x z ∂MeasureTheory.volume =
          ρ z * ∫ x in U, u (convexApproxSample x0 z r ε x) * dφ x ∂MeasureTheory.volume := by
      calc
        ∫ x in tsupport dφ, F x z ∂MeasureTheory.volume
            = ∫ x in U, F x z ∂MeasureTheory.volume := by
                symm
                exact
                  MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
                    hU.1.measurableSet hdφ_sub (fun x hx => by
                      simp [F, dφ, image_eq_zero_of_notMem_tsupport hx.2])
        _ = ∫ x in U, ρ z * (u (convexApproxSample x0 z r ε x) * dφ x)
              ∂MeasureTheory.volume := by
                refine MeasureTheory.setIntegral_congr_fun hU.1.measurableSet ?_
                intro x hx
                let y : Vec d := convexApproxSample x0 z r ε x
                have hy_mem : y ∈ U := hmap hx
                change ρ z * Set.indicator U u y * dφ x = ρ z * (u y * dφ x)
                have hy_eq : Set.indicator U u y = u y := Set.indicator_of_mem (s := U) (f := u) hy_mem
                simpa [mul_assoc] using congrArg (fun t => ρ z * t * dφ x) hy_eq
        _ = ρ z * ∫ x in U, u (convexApproxSample x0 z r ε x) * dφ x
              ∂MeasureTheory.volume := by
                rw [MeasureTheory.integral_const_mul]
    have hright_z :
        ∫ x in tsupport φε, G x z ∂MeasureTheory.volume =
          ρ z *
            ∫ x in U, ((1 - ε) * gi (convexApproxSample x0 z r ε x)) * φ x
              ∂MeasureTheory.volume := by
      calc
        ∫ x in tsupport φε, G x z ∂MeasureTheory.volume
            = ∫ x in U, G x z ∂MeasureTheory.volume := by
                symm
                exact
                  MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
                    hU.1.measurableSet hφε_sub (fun x hx => by
                      simp [G, φε, image_eq_zero_of_notMem_tsupport hx.2])
        _ = ∫ x in U,
              ρ z * (((1 - ε) * gi (convexApproxSample x0 z r ε x)) * φ x)
                ∂MeasureTheory.volume := by
                refine MeasureTheory.setIntegral_congr_fun hU.1.measurableSet ?_
                intro x hx
                let y : Vec d := convexApproxSample x0 z r ε x
                have hy_mem : y ∈ U := hmap hx
                change ρ z * Set.indicator U gi y * ((1 - ε) * φ x) =
                  ρ z * (((1 - ε) * gi y) * φ x)
                have hy_eq : Set.indicator U gi y = gi y := Set.indicator_of_mem (s := U) (f := gi) hy_mem
                calc
                  ρ z * Set.indicator U gi y * ((1 - ε) * φ x)
                      = ρ z * gi y * ((1 - ε) * φ x) := by
                          simpa [mul_assoc] using congrArg (fun t => ρ z * t * ((1 - ε) * φ x)) hy_eq
                  _ = ρ z * (((1 - ε) * gi y) * φ x) := by
                        ring
        _ = ρ z *
              ∫ x in U, ((1 - ε) * gi (convexApproxSample x0 z r ε x)) * φ x
                ∂MeasureTheory.volume := by
                rw [MeasureTheory.integral_const_mul]
    calc
      ∫ x in tsupport dφ, F x z ∂MeasureTheory.volume
          = ρ z * ∫ x in U, u (convexApproxSample x0 z r ε x) * dφ x
              ∂MeasureTheory.volume := hleft_z
      _ = ρ z *
            (-∫ x in U, ((1 - ε) * gi (convexApproxSample x0 z r ε x)) * φ x
              ∂MeasureTheory.volume) := by
                rw [hweak_z]
      _ = -(ρ z *
            ∫ x in U, ((1 - ε) * gi (convexApproxSample x0 z r ε x)) * φ x
              ∂MeasureTheory.volume) := by
                ring
      _ = -∫ x in tsupport φε, G x z ∂MeasureTheory.volume := by
            rw [← hright_z]
  have hz_integrated :
      ∫ z in tsupport ρ, ∫ x in tsupport dφ, F x z ∂MeasureTheory.volume
        ∂MeasureTheory.volume =
        ∫ z in tsupport ρ, -∫ x in tsupport φε, G x z ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun hρ.compactSupport.isCompact.measurableSet ?_
    intro z hz
    exact hfixed_z z hz
  calc
    ∫ x in U, Homogenization.convexApproxSmoothing ρ u x0 r ε x * (fderiv ℝ φ x) (basisVec i)
        ∂MeasureTheory.volume
      = ∫ x in U, Homogenization.convexApproxSmoothing ρ u x0 r ε x * dφ x
          ∂MeasureTheory.volume := by
          simp [dφ]
    _ = ∫ x in tsupport dφ, Homogenization.convexApproxSmoothing ρ u x0 r ε x * dφ x
          ∂MeasureTheory.volume := hleft_restrict
    _ = ∫ x in tsupport dφ, ∫ z in tsupport ρ, F x z ∂MeasureTheory.volume
          ∂MeasureTheory.volume := hinner_left_eq
    _ = ∫ z in tsupport ρ, ∫ x in tsupport dφ, F x z ∂MeasureTheory.volume
          ∂MeasureTheory.volume := hswap_left
    _ = ∫ z in tsupport ρ, -∫ x in tsupport φε, G x z ∂MeasureTheory.volume
          ∂MeasureTheory.volume := hz_integrated
    _ = -∫ z in tsupport ρ, ∫ x in tsupport φε, G x z ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_neg]
    _ = -∫ x in tsupport φε, ∫ z in tsupport ρ, G x z ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
            rw [← hswap_right]
    _ = -∫ x in tsupport φε, Homogenization.convexApproxSmoothing ρ gi x0 r ε x * φε x
          ∂MeasureTheory.volume := by
            rw [← hinner_right_eq]
    _ = -∫ x in U, Homogenization.convexApproxSmoothing ρ gi x0 r ε x * φε x
          ∂MeasureTheory.volume := by
          rw [← hright_restrict]
    _ = -∫ x in U, ((1 - ε) * Homogenization.convexApproxSmoothing ρ gi x0 r ε x) * φ x
          ∂MeasureTheory.volume := by
            congr 1
            refine MeasureTheory.setIntegral_congr_fun hU.1.measurableSet ?_
            intro x hx
            simp [φε, mul_assoc, mul_comm]

theorem HasWeakGradientOn.convexApproxSmoothing
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d} {ρ : Vec d → ℝ}
    (huLoc : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume)
    (hDuLoc : ∀ i : Fin d, MeasureTheory.LocallyIntegrableOn (fun x => Du x i) U MeasureTheory.volume)
    (hu : HasWeakGradientOn U u Du)
    (hρ : IsConvexApproxKernel ρ)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    HasWeakGradientOn U
      (Homogenization.convexApproxSmoothing ρ u x0 r ε)
      (fun x i => (1 - ε) * Homogenization.convexApproxSmoothing ρ (fun y => Du y i) x0 r ε x) := by
  intro i
  simpa using
    (HasWeakPartialDerivOn.convexApproxSmoothing (i := i) hU huLoc (hDuLoc i) (hu i) hρ
      hball hr hε0 hε1)

theorem HasWeakPartialDerivOn.convexApproxSmoothRepresentative
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {i : Fin d} {u gi ρ : Vec d → ℝ}
    (huLoc : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume)
    (hgiLoc : MeasureTheory.LocallyIntegrableOn gi U MeasureTheory.volume)
    (hu : HasWeakPartialDerivOn U i u gi)
    (hρ : IsConvexApproxKernel ρ)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    HasWeakPartialDerivOn U i
      (Homogenization.convexApproxSmoothRepresentative U ρ u x0 r ε)
      (fun x => (1 - ε) *
        Homogenization.convexApproxSmoothRepresentative U ρ gi x0 r ε x) := by
  intro φ hφ_smooth hφ_compact hφ_sub
  have hweak :
      HasWeakPartialDerivOn U i
        (Homogenization.convexApproxSmoothing ρ u x0 r ε)
        (fun x => (1 - ε) * Homogenization.convexApproxSmoothing ρ gi x0 r ε x) :=
    HasWeakPartialDerivOn.convexApproxSmoothing (i := i) hU huLoc hgiLoc hu hρ hball
      hr.le hε0.le hε1
  have hleft :
      ∫ x in U,
          Homogenization.convexApproxSmoothRepresentative U ρ u x0 r ε x *
            (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
        ∫ x in U,
          Homogenization.convexApproxSmoothing ρ u x0 r ε x *
            (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun hU.1.measurableSet ?_
    intro x hx
    have hrep :
        Homogenization.convexApproxSmoothRepresentative U ρ u x0 r ε x =
          Homogenization.convexApproxSmoothing ρ u x0 r ε x :=
      convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
        (u := u) hU hρ hx hball hr hε0 hε1
    change
      Homogenization.convexApproxSmoothRepresentative U ρ u x0 r ε x *
          (fderiv ℝ φ x) (basisVec i) =
        Homogenization.convexApproxSmoothing ρ u x0 r ε x *
          (fderiv ℝ φ x) (basisVec i)
    rw [hrep]
  have hright :
      ∫ x in U,
          ((1 - ε) * Homogenization.convexApproxSmoothing ρ gi x0 r ε x) * φ x
            ∂MeasureTheory.volume =
        ∫ x in U,
          ((1 - ε) * Homogenization.convexApproxSmoothRepresentative U ρ gi x0 r ε x) * φ x
            ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun hU.1.measurableSet ?_
    intro x hx
    have hrep :
        Homogenization.convexApproxSmoothRepresentative U ρ gi x0 r ε x =
          Homogenization.convexApproxSmoothing ρ gi x0 r ε x :=
      convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
        (u := gi) hU hρ hx hball hr hε0 hε1
    change
      ((1 - ε) * Homogenization.convexApproxSmoothing ρ gi x0 r ε x) * φ x =
        ((1 - ε) * Homogenization.convexApproxSmoothRepresentative U ρ gi x0 r ε x) *
          φ x
    rw [hrep]
  calc
    ∫ x in U,
        Homogenization.convexApproxSmoothRepresentative U ρ u x0 r ε x *
            (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume
        = ∫ x in U,
            Homogenization.convexApproxSmoothing ρ u x0 r ε x *
              (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume := hleft
    _ = -∫ x in U,
          ((1 - ε) * Homogenization.convexApproxSmoothing ρ gi x0 r ε x) * φ x
            ∂MeasureTheory.volume :=
        hweak φ hφ_smooth hφ_compact hφ_sub
    _ = -∫ x in U,
          ((1 - ε) * Homogenization.convexApproxSmoothRepresentative U ρ gi x0 r ε x) * φ x
            ∂MeasureTheory.volume := by
        rw [hright]

theorem HasWeakGradientOn.convexApproxSmoothRepresentative
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d} {ρ : Vec d → ℝ}
    (huLoc : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume)
    (hDuLoc : ∀ i : Fin d, MeasureTheory.LocallyIntegrableOn (fun x => Du x i) U
      MeasureTheory.volume)
    (hu : HasWeakGradientOn U u Du)
    (hρ : IsConvexApproxKernel ρ)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    HasWeakGradientOn U
      (Homogenization.convexApproxSmoothRepresentative U ρ u x0 r ε)
      (fun x i => (1 - ε) *
        Homogenization.convexApproxSmoothRepresentative U ρ (fun y => Du y i) x0 r ε x) := by
  intro i
  simpa using
    (HasWeakPartialDerivOn.convexApproxSmoothRepresentative (i := i) hU huLoc (hDuLoc i)
      (hu i) hρ hball hr hε0 hε1)

end Homogenization

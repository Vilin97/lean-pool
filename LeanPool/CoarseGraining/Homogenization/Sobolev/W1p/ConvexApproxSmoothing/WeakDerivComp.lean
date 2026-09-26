/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.SmoothRepresentative

/-! # Weak Deriv Comp -/

@[expose] public section

namespace Homogenization

open scoped Pointwise Convolution

/-!
# Weak partial derivatives of the `convexApproxSample` composition

Establishes `HasWeakPartialDerivOn.comp_convexApproxSample` (plus the gradient
variant) and the product-measure infrastructure that feeds it:
quasi-measure-preservation of `convexApproxSample`, strong measurability of
indicator products, and integrability of the kernel × indicator × comp tensor
against a locally integrable datum.
-/

theorem HasWeakPartialDerivOn.comp_convexApproxSample
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {i : Fin d} {u gi : Vec d → ℝ}
    (hu : HasWeakPartialDerivOn U i u gi)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    HasWeakPartialDerivOn U i
      (fun x => u (convexApproxSample x0 z r ε x))
      (fun x => (1 - ε) * gi (convexApproxSample x0 z r ε x)) := by
  intro φ hφ_smooth hφ_compact hφ_sub
  let a : ℝ := 1 - ε
  let b : Vec d := ε • (x0 - r • z)
  let V : Set (Vec d) := translateSet b (a • U)
  let c : ℝ := a * (a ^ d)⁻¹
  let ψ : Vec d → ℝ := fun y => c * φ (a⁻¹ • (y - b))
  let dφ : Vec d → ℝ := fun x => (fderiv ℝ φ x) (basisVec i)
  let dψ : Vec d → ℝ := fun y => (fderiv ℝ ψ y) (basisVec i)
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith
  have ha_ne : a ≠ 0 := ha_pos.ne'
  have ha_inv_ne : a⁻¹ ≠ 0 := inv_ne_zero ha_ne
  have hmap :
      Set.MapsTo (convexApproxSample x0 z r ε) U U :=
    convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain hU hball hr hz hε0 (le_of_lt hε1)
  have hV_sub : V ⊆ U :=
    translateSet_smul_subset_of_convexApproxSample_mapsTo (x0 := x0) (z := z) (r := r) (ε := ε)
      hmap
  have hψ_eq :
      ψ = fun y => c * φ (a⁻¹ • (y - b)) := rfl
  have h_affine_cancel : ∀ y : Vec d, a • (a⁻¹ • (y - b)) + b = y := by
    intro y
    rw [smul_smul, mul_inv_cancel₀ ha_ne, one_smul]
    abel
  have hdφ_zero :
      ∀ x, x ∉ U → dφ x = 0 := by
    intro x hx
    have hx_notin : x ∉ tsupport φ := fun hx' => hx (hφ_sub hx')
    have hφ_eq : φ =ᶠ[nhds x] 0 :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hx_notin |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    show (fderiv ℝ φ x) (basisVec i) = 0
    rw [Filter.EventuallyEq.fderiv_eq hφ_eq]
    simp
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    have hinner : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => a⁻¹ • (y - b)) := by
      have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec d => a⁻¹) := contDiff_const
      have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => y - b) :=
        contDiff_id.sub contDiff_const
      exact h1.smul h2
    simpa [ψ, hψ_eq] using contDiff_const.mul (hφ_smooth.comp hinner)
  have hψ_compact : HasCompactSupport ψ := by
    let e : Homeomorph (Vec d) (Vec d) :=
      (Homeomorph.subRight b).trans (Homeomorph.smulOfNeZero a⁻¹ ha_inv_ne)
    have hbase : HasCompactSupport (fun y : Vec d => φ (a⁻¹ • (y - b))) := by
      show HasCompactSupport (φ ∘ e)
      simpa [e, Function.comp] using hφ_compact.comp_homeomorph e
    have hmul :
        HasCompactSupport
          (fun y : Vec d => (fun _ : Vec d => c) y * (fun y : Vec d => φ (a⁻¹ • (y - b))) y) := by
      simpa using! (HasCompactSupport.mul_left (f := fun _ : Vec d => c) hbase)
    simpa [ψ, hψ_eq] using hmul
  have hψ_subV : tsupport ψ ⊆ V := by
    intro y hy
    have hy' :
        y ∈ tsupport (fun y : Vec d => φ (a⁻¹ • (y - b))) := by
      have hsub :
          tsupport (fun y : Vec d => c * φ (a⁻¹ • (y - b))) ⊆
            tsupport (fun y : Vec d => φ (a⁻¹ • (y - b))) :=
        tsupport_mul_subset_right
          (f := fun _ : Vec d => c)
          (g := fun y : Vec d => φ (a⁻¹ • (y - b)))
      exact hsub (by simpa [ψ, hψ_eq] using hy)
    let e : Homeomorph (Vec d) (Vec d) :=
      (Homeomorph.subRight b).trans (Homeomorph.smulOfNeZero a⁻¹ ha_inv_ne)
    have hx_tsupport : a⁻¹ • (y - b) ∈ tsupport φ := by
      rw [show (fun y : Vec d => φ (a⁻¹ • (y - b))) = φ ∘ e by
            funext t
            simp [e, Function.comp],
        tsupport_comp_eq_preimage φ e] at hy'
      exact hy'
    let x : Vec d := a⁻¹ • (y - b)
    have hxU : x ∈ U := hφ_sub hx_tsupport
    refine ⟨a • x, Set.smul_mem_smul_set hxU, ?_⟩
    calc
      y = a • x + b := by
            dsimp [x]
            rw [smul_smul, mul_inv_cancel₀ ha_ne, one_smul]
            abel
      _ = a • x + ε • (x0 - r • z) := by rfl
  have hψ_sub : tsupport ψ ⊆ U :=
    hψ_subV.trans hV_sub
  have hψ_value_zero :
      ∀ y ∈ U \ V, ψ y = 0 := by
    intro y hy
    have hy_notinV : y ∉ V := hy.2
    have hy_notin : y ∉ tsupport ψ := fun hy' => hy_notinV (hψ_subV hy')
    exact image_eq_zero_of_notMem_tsupport hy_notin
  have hdψ_formula :
      ∀ y : Vec d, dψ y = (a ^ d)⁻¹ * dφ (a⁻¹ • (y - b)) := by
    intro y
    have hbase_smooth :
        ContDiff ℝ 1 (fun t : Vec d => φ (a⁻¹ • (t - b))) := by
      have hinner : ContDiff ℝ 1 (fun t : Vec d => a⁻¹ • (t - b)) := by
        have h1 : ContDiff ℝ 1 (fun _ : Vec d => a⁻¹) := contDiff_const
        have h2 : ContDiff ℝ 1 (fun t : Vec d => t - b) :=
          contDiff_id.sub contDiff_const
        exact h1.smul h2
      exact (hφ_smooth.of_le (by simp)).comp hinner
    have hbase_diff : DifferentiableAt ℝ (fun t : Vec d => φ (a⁻¹ • (t - b))) y :=
      (hbase_smooth.contDiffAt).differentiableAt (by simp)
    have hderiv_base :
        fderiv ℝ (fun t : Vec d => φ (a⁻¹ • (t - b))) y =
          a⁻¹ • fderiv ℝ φ (a⁻¹ • (y - b)) := by
      calc
        fderiv ℝ (fun t : Vec d => φ (a⁻¹ • (t - b))) y
            = fderiv ℝ (fun s : Vec d => φ (a⁻¹ • s)) (y - b) := by
                simpa [sub_eq_add_neg] using
                  (fderiv_comp_sub (𝕜 := ℝ) (f := fun s : Vec d => φ (a⁻¹ • s)) (x := y) b)
        _ = a⁻¹ • fderiv ℝ φ (a⁻¹ • (y - b)) := by
              simpa using
                (fderiv_comp_smul (𝕜 := ℝ) (f := φ) (x := y - b) (c := a⁻¹))
    have hcoord :
        dψ y = c * ((a⁻¹) * dφ (a⁻¹ • (y - b))) := by
      have hderiv :
          fderiv ℝ ψ y =
            c • fderiv ℝ (fun t : Vec d => φ (a⁻¹ • (t - b))) y := by
        simpa [ψ, hψ_eq] using
          (fderiv_const_mul
            (𝕜 := ℝ)
            (a := fun t : Vec d => φ (a⁻¹ • (t - b)))
            (x := y)
            hbase_diff
            c)
      change (fderiv ℝ ψ y) (basisVec i) = c * (a⁻¹ * dφ (a⁻¹ • (y - b)))
      rw [hderiv]
      rw [hderiv_base]
      simp [dφ, mul_assoc, smul_smul]
    let g : ℝ := dφ (a⁻¹ • (y - b))
    calc
      dψ y = c * ((a⁻¹) * g) := hcoord
      _ = (c * a⁻¹) * g := by ring
      _ = (a ^ d)⁻¹ * g := by
            have hc : c * a⁻¹ = (a ^ d)⁻¹ := by
              dsimp [c]
              field_simp [ha_ne]
            rw [hc]
      _ = (a ^ d)⁻¹ * dφ (a⁻¹ • (y - b)) := by rfl
  have hdψ_zero :
      ∀ y ∈ U \ V, dψ y = 0 := by
    intro y hy
    have hy_notV : y ∉ V := hy.2
    have hx_notU : a⁻¹ • (y - b) ∉ U := by
      intro hxU
      have hy_memV : y ∈ V := by
        refine ⟨a • (a⁻¹ • (y - b)), ?_, ?_⟩
        · exact Set.smul_mem_smul_set hxU
        · rw [smul_smul, mul_inv_cancel₀ ha_ne, one_smul]
          abel
      exact hy_notV hy_memV
    rw [hdψ_formula]
    simp [hdφ_zero _ hx_notU]
  have hweak := hu ψ hψ_smooth hψ_compact hψ_sub
  have hleft_restrict :
      ∫ y in U, u y * dψ y ∂MeasureTheory.volume =
        ∫ y in V, u y * dψ y ∂MeasureTheory.volume := by
    exact
      MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        hU.1.measurableSet hV_sub (fun y hy => by simp [hdψ_zero y hy])
  have hright_restrict :
      ∫ y in U, gi y * ψ y ∂MeasureTheory.volume =
        ∫ y in V, gi y * ψ y ∂MeasureTheory.volume := by
    exact
      MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        hU.1.measurableSet hV_sub (fun y hy => by simp [hψ_value_zero y hy])
  have hleft_change :
      ∫ y in V, u y * dψ y ∂MeasureTheory.volume =
        ∫ x in U, u (convexApproxSample x0 z r ε x) * dφ x ∂MeasureTheory.volume := by
    have haux :
        (a ^ d)⁻¹ *
            ∫ y in V, u y * dφ (a⁻¹ • (y - b)) ∂MeasureTheory.volume =
          ∫ x in U, u (convexApproxSample x0 z r ε x) * dφ x ∂MeasureTheory.volume := by
      calc
        (a ^ d)⁻¹ *
            ∫ y in V, (fun y : Vec d => u y * dφ (a⁻¹ • (y - b))) y
              ∂MeasureTheory.volume
          = (a ^ d)⁻¹ *
              ∫ y in V, u (a • (a⁻¹ • (y - b)) + b) * dφ (a⁻¹ • (y - b))
                ∂MeasureTheory.volume := by
                  congr 1
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards with y
                  simp [h_affine_cancel y]
        _ = ∫ x in U, u (convexApproxSample x0 z r ε x) * dφ x
              ∂MeasureTheory.volume := by
                simpa [V, a, b, smul_eq_mul, convexApproxSample] using
                  (setIntegral_comp_inv_smul_sub_of_pos
                    (d := d)
                    (E := ℝ)
                    ha_pos
                    b
                    U
                    (fun x : Vec d => u (a • x + b) * dφ x))
    calc
      ∫ y in V, u y * dψ y ∂MeasureTheory.volume
          = ∫ y in V, u y * ((a ^ d)⁻¹ * dφ (a⁻¹ • (y - b))) ∂MeasureTheory.volume := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with y
              rw [hdψ_formula y]
      _ = ∫ y in V, (a ^ d)⁻¹ * (u y * dφ (a⁻¹ • (y - b))) ∂MeasureTheory.volume := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with y
            ring
      _ = (a ^ d)⁻¹ *
            ∫ y in V, (fun y : Vec d => u y * dφ (a⁻¹ • (y - b))) y ∂MeasureTheory.volume := by
              rw [MeasureTheory.integral_const_mul]
      _ = ∫ x in U, u (convexApproxSample x0 z r ε x) * dφ x ∂MeasureTheory.volume := by
            exact haux
  have hright_change :
      ∫ y in V, gi y * ψ y ∂MeasureTheory.volume =
        a * ∫ x in U, gi (convexApproxSample x0 z r ε x) * φ x ∂MeasureTheory.volume := by
    have haux :
        (a ^ d)⁻¹ *
            ∫ y in V, gi y * φ (a⁻¹ • (y - b)) ∂MeasureTheory.volume =
          ∫ x in U, gi (convexApproxSample x0 z r ε x) * φ x ∂MeasureTheory.volume := by
      calc
        (a ^ d)⁻¹ *
            ∫ y in V, (fun y : Vec d => gi y * φ (a⁻¹ • (y - b))) y
              ∂MeasureTheory.volume
          = (a ^ d)⁻¹ *
              ∫ y in V, gi (a • (a⁻¹ • (y - b)) + b) * φ (a⁻¹ • (y - b))
                ∂MeasureTheory.volume := by
                  congr 1
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards with y
                  simp [h_affine_cancel y]
        _ = ∫ x in U, gi (convexApproxSample x0 z r ε x) * φ x
              ∂MeasureTheory.volume := by
                simpa [V, a, b, smul_eq_mul, convexApproxSample] using
                  (setIntegral_comp_inv_smul_sub_of_pos
                    (d := d)
                    (E := ℝ)
                    ha_pos
                    b
                    U
                    (fun x : Vec d => gi (a • x + b) * φ x))
    calc
      ∫ y in V, gi y * ψ y ∂MeasureTheory.volume
          = ∫ y in V, gi y * (c * φ (a⁻¹ • (y - b))) ∂MeasureTheory.volume := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with y
              simp [ψ]
      _ = ∫ y in V, c * (gi y * φ (a⁻¹ • (y - b))) ∂MeasureTheory.volume := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with y
            ring
      _ = c * ∫ y in V, (fun y : Vec d => gi y * φ (a⁻¹ • (y - b))) y
            ∂MeasureTheory.volume := by
              rw [MeasureTheory.integral_const_mul]
      _ = a *
            ((a ^ d)⁻¹ * ∫ y in V, (fun y : Vec d => gi y * φ (a⁻¹ • (y - b))) y
              ∂MeasureTheory.volume) := by
                dsimp [c]
                ring
      _ = a * ∫ x in U, gi (convexApproxSample x0 z r ε x) * φ x
            ∂MeasureTheory.volume := by
              rw [haux]
  calc
    ∫ x in U, u (convexApproxSample x0 z r ε x) * (fderiv ℝ φ x) (basisVec i)
        ∂MeasureTheory.volume
      = ∫ y in U, u y * dψ y ∂MeasureTheory.volume := by
          rw [hleft_restrict, hleft_change]
    _ = -∫ y in U, gi y * ψ y ∂MeasureTheory.volume := by
          simpa [dψ] using hweak
    _ = -∫ y in V, gi y * ψ y ∂MeasureTheory.volume := by
          rw [hright_restrict]
    _ = -(a * ∫ x in U, gi (convexApproxSample x0 z r ε x) * φ x
            ∂MeasureTheory.volume) := by
          rw [hright_change]
    _ = -∫ x in U, (a * gi (convexApproxSample x0 z r ε x)) * φ x
            ∂MeasureTheory.volume := by
          congr 1
          calc
            a * ∫ x in U, gi (convexApproxSample x0 z r ε x) * φ x ∂MeasureTheory.volume
                = ∫ x in U, a * (gi (convexApproxSample x0 z r ε x) * φ x)
                    ∂MeasureTheory.volume := by
                      rw [← MeasureTheory.integral_const_mul]
            _ = ∫ x in U, (a * gi (convexApproxSample x0 z r ε x)) * φ x
                    ∂MeasureTheory.volume := by
                      apply MeasureTheory.integral_congr_ae
                      filter_upwards with x
                      ring
    _ = -∫ x in U, ((1 - ε) * gi (convexApproxSample x0 z r ε x)) * φ x
            ∂MeasureTheory.volume := by
          simp [a]

theorem HasWeakGradientOn.comp_convexApproxSample
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : HasWeakGradientOn U u Du)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    HasWeakGradientOn U
      (fun x => u (convexApproxSample x0 z r ε x))
      (fun x i => (1 - ε) * Du (convexApproxSample x0 z r ε x) i) := by
  intro i
  simpa using
    (hu i).comp_convexApproxSample hU hball hr hz hε0 hε1

theorem quasiMeasurePreserving_convexApproxSample
    {d : ℕ} (x0 z : Vec d) (r ε : ℝ) (hε1 : ε < 1) :
    MeasureTheory.Measure.QuasiMeasurePreserving (convexApproxSample x0 z r ε)
      MeasureTheory.volume MeasureTheory.volume := by
  let a : ℝ := 1 - ε
  let b : Vec d := ε • (x0 - r • z)
  have ha_ne : a ≠ 0 := by
    dsimp [a]
    linarith
  have hsmul :
      MeasureTheory.Measure.QuasiMeasurePreserving (fun x : Vec d => a • x)
        MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.Measure.quasiMeasurePreserving_smul (μ := MeasureTheory.volume) ha_ne
  have hadd :
      MeasureTheory.MeasurePreserving (fun x : Vec d => x + b)
        MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.measurePreserving_add_right MeasureTheory.volume b
  simpa [convexApproxSample, a, b, Function.comp] using!
    hadd.quasiMeasurePreserving.comp hsmul

theorem quasiMeasurePreserving_convexApproxSample_prod
    {d : ℕ} {U : Set (Vec d)} {ρ : Vec d → ℝ}
    (_hρ : IsConvexApproxKernel ρ)
    (x0 : Vec d) (r ε : ℝ) (hε1 : ε < 1) :
    MeasureTheory.Measure.QuasiMeasurePreserving
      (fun p : Vec d × Vec d => convexApproxSample x0 p.2 r ε p.1)
      ((MeasureTheory.volume.restrict U).prod (MeasureTheory.volume.restrict (tsupport ρ)))
      MeasureTheory.volume := by
  refine MeasureTheory.QuasiMeasurePreserving.prod_of_left ?_ ?_
  · have h1 : Measurable (fun p : Vec d × Vec d => (1 - ε) • p.1) :=
      (measurable_const : Measurable (fun _ : Vec d × Vec d => (1 - ε))).smul measurable_fst
    have h2 : Measurable (fun p : Vec d × Vec d => r • p.2) :=
      (measurable_const : Measurable (fun _ : Vec d × Vec d => r)).smul measurable_snd
    have h3 : Measurable (fun p : Vec d × Vec d => x0 - r • p.2) :=
      (measurable_const : Measurable (fun _ : Vec d × Vec d => x0)).sub h2
    have h4 : Measurable (fun p : Vec d × Vec d => ε • (x0 - r • p.2)) :=
      (measurable_const : Measurable (fun _ : Vec d × Vec d => ε)).smul h3
    show Measurable (fun p : Vec d × Vec d => convexApproxSample x0 p.2 r ε p.1)
    exact h1.add h4
  · refine Filter.Eventually.of_forall ?_
    intro z
    exact
      (quasiMeasurePreserving_convexApproxSample x0 z r ε hε1).mono_left
        MeasureTheory.Measure.absolutelyContinuous_restrict

theorem aestronglyMeasurable_indicator_comp_convexApproxSample_prod
    {d : ℕ} {U : Set (Vec d)} (hU_meas : MeasurableSet U)
    {u ρ : Vec d → ℝ}
    (hu : MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict U))
    (hρ : IsConvexApproxKernel ρ)
    {x0 : Vec d} {r ε : ℝ} (hε1 : ε < 1) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : Vec d × Vec d => Set.indicator U u (convexApproxSample x0 p.2 r ε p.1))
      ((MeasureTheory.volume.restrict U).prod
        (MeasureTheory.volume.restrict (tsupport ρ))) := by
  have hu_ind :
      MeasureTheory.AEStronglyMeasurable (Set.indicator U u) MeasureTheory.volume := by
    exact (aestronglyMeasurable_indicator_iff hU_meas).2 hu
  exact hu_ind.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_convexApproxSample_prod (U := U) (ρ := ρ) hρ x0 r ε hε1)

theorem aestronglyMeasurable_indicator_comp_convexApproxSample_prod_of_locallyIntegrableOn
    {d : ℕ} {U : Set (Vec d)} (hU_meas : MeasurableSet U)
    {u ρ : Vec d → ℝ}
    (hu : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume)
    (hρ : IsConvexApproxKernel ρ)
    {x0 : Vec d} {r ε : ℝ} (hε1 : ε < 1) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : Vec d × Vec d => Set.indicator U u (convexApproxSample x0 p.2 r ε p.1))
      ((MeasureTheory.volume.restrict U).prod
        (MeasureTheory.volume.restrict (tsupport ρ))) := by
  exact
    aestronglyMeasurable_indicator_comp_convexApproxSample_prod hU_meas
      hu.aestronglyMeasurable hρ hε1

theorem aestronglyMeasurable_kernel_mul_indicator_comp_convexApproxSample_prod_mul
    {d : ℕ} {U : Set (Vec d)} (hU_meas : MeasurableSet U)
    {u ρ ψ : Vec d → ℝ}
    (hu : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume)
    (hρ : IsConvexApproxKernel ρ) (hψ : Continuous ψ) (hψ_sub : tsupport ψ ⊆ U)
    {x0 : Vec d} {r ε : ℝ} (hε1 : ε < 1) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : Vec d × Vec d =>
        ρ p.2 * Set.indicator U u (convexApproxSample x0 p.2 r ε p.1) * ψ p.1)
      ((MeasureTheory.volume.restrict (tsupport ψ)).prod
        (MeasureTheory.volume.restrict (tsupport ρ))) := by
  set μψ : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict (tsupport ψ)
  set μρ : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict (tsupport ρ)
  have hbase :
      MeasureTheory.AEStronglyMeasurable
        (fun p : Vec d × Vec d => Set.indicator U u (convexApproxSample x0 p.2 r ε p.1))
        ((MeasureTheory.volume.restrict U).prod μρ) :=
    aestronglyMeasurable_indicator_comp_convexApproxSample_prod_of_locallyIntegrableOn hU_meas hu
      hρ hε1
  have hμψ_le : μψ ≤ MeasureTheory.volume.restrict U := by
    exact MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hψ_sub
  have hprod_le : μψ.prod μρ ≤ (MeasureTheory.volume.restrict U).prod μρ := by
    refine MeasureTheory.Measure.le_iff.2 ?_
    intro s hs
    rw [MeasureTheory.Measure.prod_apply hs, MeasureTheory.Measure.prod_apply hs]
    exact MeasureTheory.lintegral_mono' hμψ_le le_rfl
  have hcomp :
      MeasureTheory.AEStronglyMeasurable
        (fun p : Vec d × Vec d => Set.indicator U u (convexApproxSample x0 p.2 r ε p.1))
        (μψ.prod μρ) :=
    hbase.mono_measure hprod_le
  have hρ_meas :
      MeasureTheory.AEStronglyMeasurable (fun p : Vec d × Vec d => ρ p.2) (μψ.prod μρ) :=
    (hρ.continuous.comp continuous_snd).aestronglyMeasurable
  have hψ_meas :
      MeasureTheory.AEStronglyMeasurable (fun p : Vec d × Vec d => ψ p.1) (μψ.prod μρ) :=
    (hψ.comp continuous_fst).aestronglyMeasurable
  simpa [mul_assoc] using! hρ_meas.mul (hcomp.mul hψ_meas)

theorem integrable_kernel_mul_indicator_comp_convexApproxSample_prod_mul_of_integrableOn
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {u ρ ψ : Vec d → ℝ} (hu : MeasureTheory.IntegrableOn u U MeasureTheory.volume)
    (hρ : IsConvexApproxKernel ρ) (hψ : Continuous ψ) (hψ_compact : HasCompactSupport ψ)
    (hψ_sub : tsupport ψ ⊆ U)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    MeasureTheory.Integrable
      (fun p : Vec d × Vec d =>
        ρ p.2 * Set.indicator U u (convexApproxSample x0 p.2 r ε p.1) * ψ p.1)
      ((MeasureTheory.volume.restrict (tsupport ψ)).prod
        (MeasureTheory.volume.restrict (tsupport ρ))) := by
  set μψ : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict (tsupport ψ)
  set μρ : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict (tsupport ρ)
  let a : ℝ := 1 - ε
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith
  have huLoc : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume := hu.locallyIntegrableOn
  have hmeas :
      MeasureTheory.AEStronglyMeasurable
        (fun p : Vec d × Vec d =>
          ρ p.2 * Set.indicator U u (convexApproxSample x0 p.2 r ε p.1) * ψ p.1)
        (μψ.prod μρ) := by
    simpa [μψ, μρ] using
      aestronglyMeasurable_kernel_mul_indicator_comp_convexApproxSample_prod_mul
        hU.1.measurableSet huLoc hρ hψ hψ_sub hε1
  refine (MeasureTheory.integrable_prod_iff' hmeas).2 ?_
  constructor
  · filter_upwards [MeasureTheory.ae_restrict_mem hρ.compactSupport.isCompact.measurableSet] with z hz
    have hz_norm : ‖z‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hρ.support_subset_closedBall hz
    simpa [μψ, MeasureTheory.Integrable] using
      (integrableOn_kernel_mul_indicator_comp_convexApproxSample_mul_of_locallyIntegrableOn
        hU huLoc hψ hψ_sub hψ_compact.isCompact hball hr hz_norm hε0 hε1).integrable
  · obtain ⟨C0, hC0⟩ := hψ_compact.exists_bound_of_continuous hψ
    let Cψ : ℝ := max C0 0
    have hCψ_nonneg : 0 ≤ Cψ := by
      dsimp [Cψ]
      positivity
    have hψ_bound : ∀ x, ‖ψ x‖ ≤ Cψ := by
      intro x
      exact le_trans (hC0 x) (le_max_left _ _)
    let Cu : ℝ := ∫ y in U, |u y| ∂MeasureTheory.volume
    have hCu_nonneg : 0 ≤ Cu := by
      dsimp [Cu]
      exact MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun y => abs_nonneg _)
    let bound : Vec d → ℝ := fun z => ρ z * (Cψ * ((a ^ d)⁻¹ * Cu))
    have hbound_int :
        MeasureTheory.Integrable (fun z => bound z) μρ := by
      have hbound_volume :
          MeasureTheory.Integrable (fun z => bound z) MeasureTheory.volume := by
        have hcont : Continuous (fun z => bound z) := by
          simpa [bound] using! hρ.continuous.mul continuous_const
        have hcomp : HasCompactSupport (fun z => bound z) := by
          simpa [bound] using!
            (hρ.compactSupport.mul_right :
              HasCompactSupport (fun z => ρ z * (Cψ * ((a ^ d)⁻¹ * Cu)))
            )
        exact hcont.integrable_of_hasCompactSupport hcomp
      simpa [μρ] using (MeasureTheory.Integrable.restrict (s := tsupport ρ) hbound_volume)
    have hinner_meas :
        MeasureTheory.AEStronglyMeasurable
          (fun z =>
            ∫ x,
              ‖ρ z * Set.indicator U u (convexApproxSample x0 z r ε x) * ψ x‖
              ∂μψ)
          μρ := by
      simpa using hmeas.norm.prod_swap.integral_prod_right'
    refine MeasureTheory.Integrable.mono hbound_int hinner_meas ?_
    filter_upwards with z
    by_cases hzρ : z ∈ tsupport ρ
    · let V : Set (Vec d) := translateSet (ε • (x0 - r • z)) (a • U)
      have hz_norm : ‖z‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hρ.support_subset_closedBall hzρ
      have hmap :
          Set.MapsTo (convexApproxSample x0 z r ε) U U :=
        convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain hU hball hr hz_norm hε0
          (le_of_lt hε1)
      have hsample_int_ψ :
          MeasureTheory.IntegrableOn
            (fun x => |u (convexApproxSample x0 z r ε x)|)
            (tsupport ψ) MeasureTheory.volume := by
        have hu_norm :
            MeasureTheory.IntegrableOn (fun y => ‖u y‖) U MeasureTheory.volume := hu.norm
        simpa [Real.norm_eq_abs] using
          integrableOn_comp_convexApproxSample_of_locallyIntegrableOn hU hu_norm.locallyIntegrableOn
            hψ_sub hψ_compact.isCompact hball hr hz_norm hε0 hε1
      have hsample_int_U :
          MeasureTheory.IntegrableOn
            (fun x => |u (convexApproxSample x0 z r ε x)|)
            U MeasureTheory.volume := by
        simpa [Real.norm_eq_abs] using
          integrableOn_comp_convexApproxSample hU (show MeasureTheory.IntegrableOn (fun y => ‖u y‖) U MeasureTheory.volume from hu.norm)
            hball hr hz_norm hε0 hε1
      have hdom_int :
          MeasureTheory.Integrable
            (fun x => ρ z * (|u (convexApproxSample x0 z r ε x)| * Cψ)) μψ := by
        simpa [μψ, MeasureTheory.Integrable, mul_assoc, mul_left_comm, mul_comm] using
          ((hsample_int_ψ.integrable.mul_const Cψ).const_mul (ρ z))
      have hinner_int :
          MeasureTheory.Integrable
            (fun x => ρ z * Set.indicator U u (convexApproxSample x0 z r ε x) * ψ x) μψ := by
        simpa [μψ, MeasureTheory.Integrable] using
          (integrableOn_kernel_mul_indicator_comp_convexApproxSample_mul_of_locallyIntegrableOn
            hU huLoc hψ hψ_sub hψ_compact.isCompact hball hr hz_norm hε0 hε1).integrable
      have hpointwise :
          (fun x =>
            ‖ρ z * Set.indicator U u (convexApproxSample x0 z r ε x) * ψ x‖)
            ≤ᵐ[μψ]
              (fun x => ρ z * (|u (convexApproxSample x0 z r ε x)| * Cψ)) := by
        filter_upwards [MeasureTheory.ae_restrict_mem hψ_compact.isCompact.measurableSet] with x hx
        have hxU : x ∈ U := hψ_sub hx
        have hsample_mem : convexApproxSample x0 z r ε x ∈ U := hmap hxU
        calc
          ‖ρ z * Set.indicator U u (convexApproxSample x0 z r ε x) * ψ x‖
              = ρ z * (|u (convexApproxSample x0 z r ε x)| * ‖ψ x‖) := by
                  rw [Set.indicator_of_mem hsample_mem]
                  simp [Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg z), mul_left_comm, mul_comm]
          _ ≤ ρ z * (|u (convexApproxSample x0 z r ε x)| * Cψ) := by
                refine mul_le_mul_of_nonneg_left ?_ (hρ.nonneg z)
                exact mul_le_mul_of_nonneg_left (hψ_bound x) (abs_nonneg _)
      have hsample_bound :
          ∫ x, |u (convexApproxSample x0 z r ε x)| ∂μψ ≤ (a ^ d)⁻¹ * Cu := by
        have hmono :
            ∫ x in tsupport ψ, |u (convexApproxSample x0 z r ε x)| ∂MeasureTheory.volume ≤
              ∫ x in U, |u (convexApproxSample x0 z r ε x)| ∂MeasureTheory.volume := by
          exact MeasureTheory.setIntegral_mono_set hsample_int_U
            (Filter.Eventually.of_forall fun x => abs_nonneg _)
            (Filter.Eventually.of_forall hψ_sub)
        have hV_sub : V ⊆ U :=
          translateSet_smul_subset_of_convexApproxSample_mapsTo (x0 := x0) (z := z) (r := r)
            (ε := ε) hmap
        have hchange :
            ∫ x in U, |u (convexApproxSample x0 z r ε x)| ∂MeasureTheory.volume =
              (a ^ d)⁻¹ * ∫ y in V, |u y| ∂MeasureTheory.volume := by
          simpa [convexApproxSample, a, V, smul_eq_mul] using
            (setIntegral_comp_smul_add_of_pos (d := d) (E := ℝ) ha_pos
              (ε • (x0 - r • z)) U (fun y => |u y|))
        have hV_le :
            ∫ y in V, |u y| ∂MeasureTheory.volume ≤ Cu := by
          exact MeasureTheory.setIntegral_mono_set hu.norm
            (Filter.Eventually.of_forall fun y => abs_nonneg _)
            (Filter.Eventually.of_forall hV_sub)
        exact
          calc
          ∫ x, |u (convexApproxSample x0 z r ε x)| ∂μψ
              = ∫ x in tsupport ψ, |u (convexApproxSample x0 z r ε x)| ∂MeasureTheory.volume := by
                  simp [μψ]
          _ ≤ ∫ x in U, |u (convexApproxSample x0 z r ε x)| ∂MeasureTheory.volume := hmono
          _ = (a ^ d)⁻¹ * ∫ y in V, |u y| ∂MeasureTheory.volume := hchange
          _ ≤ (a ^ d)⁻¹ * Cu := by
                refine mul_le_mul_of_nonneg_left hV_le ?_
                positivity
      show ‖∫ x, ‖ρ z * Set.indicator U u (convexApproxSample x0 z r ε x) * ψ x‖ ∂μψ‖ ≤
          ‖bound z‖
      calc
        ‖∫ x, ‖ρ z * Set.indicator U u (convexApproxSample x0 z r ε x) * ψ x‖ ∂μψ‖
            = ∫ x, ‖ρ z * Set.indicator U u (convexApproxSample x0 z r ε x) * ψ x‖ ∂μψ := by
                have hinner_nonneg :
                    0 ≤ ∫ x, ‖ρ z * Set.indicator U u (convexApproxSample x0 z r ε x) * ψ x‖ ∂μψ := by
                  exact
                    MeasureTheory.integral_nonneg_of_ae
                      (Filter.Eventually.of_forall fun x => norm_nonneg _)
                rw [Real.norm_eq_abs, abs_of_nonneg hinner_nonneg]
        _ ≤ ∫ x, ρ z * (|u (convexApproxSample x0 z r ε x)| * Cψ) ∂μψ := by
              exact MeasureTheory.integral_mono_ae hinner_int.norm hdom_int hpointwise
        _ = ρ z * (Cψ * ∫ x, |u (convexApproxSample x0 z r ε x)| ∂μψ) := by
              rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]
              ring
        _ ≤ ρ z * (Cψ * ((a ^ d)⁻¹ * Cu)) := by
              refine mul_le_mul_of_nonneg_left ?_ (hρ.nonneg z)
              exact mul_le_mul_of_nonneg_left hsample_bound hCψ_nonneg
        _ = bound z := by
              rfl
        _ = ‖bound z‖ := by
              have hbound_nonneg : 0 ≤ bound z := by
                dsimp [bound]
                exact
                  mul_nonneg (hρ.nonneg z) <|
                    mul_nonneg hCψ_nonneg <| mul_nonneg (by positivity) hCu_nonneg
              rw [Real.norm_eq_abs, abs_of_nonneg hbound_nonneg]
    · have hρz : ρ z = 0 := image_eq_zero_of_notMem_tsupport (f := ρ) hzρ
      simp [bound, hρz]

theorem integrable_kernel_mul_indicator_comp_convexApproxSample_prod_mul_of_locallyIntegrableOn
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {u ρ ψ : Vec d → ℝ} (hu : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume)
    (hρ : IsConvexApproxKernel ρ) (hψ : Continuous ψ) (hψ_compact : HasCompactSupport ψ)
    (hψ_sub : tsupport ψ ⊆ U)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    MeasureTheory.Integrable
      (fun p : Vec d × Vec d =>
        ρ p.2 * Set.indicator U u (convexApproxSample x0 p.2 r ε p.1) * ψ p.1)
      ((MeasureTheory.volume.restrict (tsupport ψ)).prod
        (MeasureTheory.volume.restrict (tsupport ρ))) := by
  let K : Set (Vec d × Vec d) := tsupport ψ ×ˢ tsupport ρ
  let W : Set (Vec d) := (fun p : Vec d × Vec d => convexApproxSample x0 p.2 r ε p.1) '' K
  let uW : Vec d → ℝ := Set.indicator W u
  have hK_meas : MeasurableSet K := by
    exact hψ_compact.isCompact.measurableSet.prod hρ.compactSupport.isCompact.measurableSet
  have hK_compact : IsCompact K := by
    exact hψ_compact.isCompact.prod hρ.compactSupport.isCompact
  have hcont_sample_prod : Continuous (fun p : Vec d × Vec d => convexApproxSample x0 p.2 r ε p.1) := by
    have h1 : Continuous (fun p : Vec d × Vec d => (1 - ε) • p.1) :=
      (continuous_const : Continuous (fun _ : Vec d × Vec d => (1 - ε))).smul continuous_fst
    have h2 : Continuous (fun p : Vec d × Vec d => r • p.2) :=
      (continuous_const : Continuous (fun _ : Vec d × Vec d => r)).smul continuous_snd
    have h3 : Continuous (fun p : Vec d × Vec d => x0 - r • p.2) :=
      (continuous_const : Continuous (fun _ : Vec d × Vec d => x0)).sub h2
    have h4 : Continuous (fun p : Vec d × Vec d => ε • (x0 - r • p.2)) :=
      (continuous_const : Continuous (fun _ : Vec d × Vec d => ε)).smul h3
    show Continuous (fun p : Vec d × Vec d => convexApproxSample x0 p.2 r ε p.1)
    exact h1.add h4
  have hW_compact : IsCompact W := by
    exact hK_compact.image hcont_sample_prod
  have hW_sub : W ⊆ U := by
    intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    have hz_norm : ‖p.2‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hρ.support_subset_closedBall hp.2
    exact
      convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain hU hball hr hz_norm hε0
        (le_of_lt hε1) (hψ_sub hp.1)
  have huW_on_W : MeasureTheory.IntegrableOn u W MeasureTheory.volume := by
    exact hu.integrableOn_compact_subset hW_sub hW_compact
  have huW_volume : MeasureTheory.Integrable uW MeasureTheory.volume := by
    exact huW_on_W.integrable_indicator hW_compact.measurableSet
  have huW_on_U : MeasureTheory.IntegrableOn uW U MeasureTheory.volume := by
    exact huW_volume.integrableOn
  have htrunc :
      MeasureTheory.Integrable
        (fun p : Vec d × Vec d =>
          ρ p.2 * Set.indicator U uW (convexApproxSample x0 p.2 r ε p.1) * ψ p.1)
        ((MeasureTheory.volume.restrict (tsupport ψ)).prod
          (MeasureTheory.volume.restrict (tsupport ρ))) := by
    exact
      integrable_kernel_mul_indicator_comp_convexApproxSample_prod_mul_of_integrableOn
        hU huW_on_U hρ hψ hψ_compact hψ_sub hball hr hε0 hε1
  have hcongr :
      (fun p : Vec d × Vec d =>
        ρ p.2 * Set.indicator U uW (convexApproxSample x0 p.2 r ε p.1) * ψ p.1)
        =ᵐ[((MeasureTheory.volume.restrict (tsupport ψ)).prod
          (MeasureTheory.volume.restrict (tsupport ρ)))]
      (fun p : Vec d × Vec d =>
        ρ p.2 * Set.indicator U u (convexApproxSample x0 p.2 r ε p.1) * ψ p.1) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact
      (MeasureTheory.ae_restrict_iff' hK_meas).2 <|
        Filter.Eventually.of_forall fun p hp => by
          let y : Vec d := convexApproxSample x0 p.2 r ε p.1
          have hsample_mem_W : y ∈ W := by
            exact Set.mem_image_of_mem (fun q : Vec d × Vec d =>
              convexApproxSample x0 q.2 r ε q.1) hp
          have hsample_mem_U : y ∈ U := hW_sub hsample_mem_W
          have hleft : Set.indicator U uW y = u y := by
            rw [Set.indicator_of_mem hsample_mem_U]
            have hWu : Set.indicator W u y = u y := by
              simpa using (Set.indicator_of_mem (s := W) (f := u) hsample_mem_W)
            simpa [uW] using hWu
          have hright : Set.indicator U u y = u y := by
            rw [Set.indicator_of_mem hsample_mem_U]
          change ρ p.2 * Set.indicator U uW y * ψ p.1 = ρ p.2 * Set.indicator U u y * ψ p.1
          rw [hleft, hright]
  exact htrunc.congr hcongr

end Homogenization

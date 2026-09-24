/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.Identity
public import LeanPool.CaffarelliKohnNirenberg.Pressure.ParamExtension
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Slice Identity

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

private theorem identity_ts_support_spatialDeriv_subset {ψ : Vec3 → ℝ} (i : Fin 3) :
    tsupport (spatialDeriv ψ i) ⊆ tsupport ψ :=
  closure_minimal
    (by
      intro x hx
      by_contra hxt
      exact hx (by simp [spatialDeriv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxt]))
    (isClosed_tsupport ψ)

private theorem identity_support_mixedSecond_subset {ψ : Vec3 → ℝ} (i j : Fin 3) :
    Function.support (mixedSecond ψ i j) ⊆ tsupport ψ :=
  ((subset_tsupport (mixedSecond ψ i j)).trans
    (identity_ts_support_spatialDeriv_subset (ψ := spatialDeriv ψ j) i)).trans
      (identity_ts_support_spatialDeriv_subset j)

private theorem identity_ts_support_mixedSecond_subset {ψ : Vec3 → ℝ} (i j : Fin 3) :
    tsupport (mixedSecond ψ i j) ⊆ tsupport ψ :=
  closure_minimal
    (identity_support_mixedSecond_subset i j)
    (isClosed_tsupport ψ)

private theorem identity_ts_support_spatialLaplacian_subset {ψ : Vec3 → ℝ} :
    tsupport (spatialLaplacian ψ) ⊆ tsupport ψ := by
  exact closure_minimal
    (by
      intro x hx
      by_contra hxt
      apply hx
      simp only [spatialLaplacian]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have hxi : x ∉ tsupport (spatialDeriv ψ i) :=
        fun hi => hxt (identity_ts_support_spatialDeriv_subset i hi)
      simp [spatialDeriv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxi])
    (isClosed_tsupport ψ)

private theorem identity_pressure_slice_integral_eq_full
    {Ω : Set Vec3} {g : Vec3 → ℝ}
    (hzero : ∀ x ∉ Ω, g x = 0) :
    ∫ x in Ω, g x = ∫ x, g x := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]

private theorem identity_pressure_convection_pointwise
    {ψ : Vec3 → ℝ} {θ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {u : ParabolicPoint → Vec3} (z : ParabolicPoint) :
    (∑ i, ∑ j, u z i * u z j *
      spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z) =
      θ z.2 * ∑ i, ∑ j, u z i * u z j * mixedSecond ψ i j z.1 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pressureTest_spatialPartial hψ i j z, mixedSecond_swap hψ j i z.1]
  ring

private theorem identity_pressure_laplacian_pointwise
    {ψ : Vec3 → ℝ} {θ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (z : ParabolicPoint) :
    ∑ i, spatialPartial (fun w => pressureTestParabolic ψ θ w i) i z =
      θ z.2 * spatialLaplacian ψ z.1 := by
  unfold spatialLaplacian
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pressureTest_spatialPartial hψ i i z]
  rfl

private theorem identity_pressure_force_pointwise
    {ψ : Vec3 → ℝ} {θ : ℝ → ℝ}
    (z : ParabolicPoint) {f : ParabolicPoint → Vec3} :
    (∑ i, f z i * pressureTestParabolic ψ θ z i) =
      θ z.2 * ∑ i, f z i * spatialDeriv ψ i z.1 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change f z i * (θ z.2 * spatialDeriv ψ i z.1) = _
  ring

private theorem pressure_test_integral_zero
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) (hθI : tsupport θ ⊆ I) :
    ∫ s, θ s * pressureSliceResidual
      (Ω := Ω) (u := u) (p := p) (f := f) ψ s = 0 := by
  have hS2 := h.2.2.2.2.2.2.1
  have hS3 := h.2.2.2.2.2.2.2.1
  have htest := pressureTest_mem_spaceTimeTestFunction
    (Ω := Ω) (I := I) hψ hψc hψΩ hθ hθc hθI
  have hS3zero0 := (hS3 (fun z => pressureTestProduct ψ θ z) htest).2
  have hS3zero :
      ∫ z in spaceTimeSet Ω I,
        (-(∑ i, u z i * timePartial
            (fun w => pressureTestParabolic ψ θ w i) z))
          - ∑ i, ∑ j, u z i * u z j *
              spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z
          + ∑ i, ∑ j, Du z i j *
              spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z
          - p z * ∑ i, spatialPartial
              (fun w => pressureTestParabolic ψ θ w i) i z
          - ∑ i, f z i * pressureTestParabolic ψ θ z i = 0 := by
    convert hS3zero0 using 1; rfl
  obtain ⟨htimeInt, htimeZero⟩ :=
    pressure_time_integral_zero (ψ := ψ) (θ := θ) hS2 (hψ.of_le (by simp)) hψc hψΩ
      hθ hθc hθI
  obtain ⟨hconv, hvisc, hpress, hforce⟩ :=
    pressure_test_terms_integrable h hψ hψc hψΩ hθ hθc hθI
  have hviscZero := pressure_viscous_test_integral_zero
    h hψ hψc hψΩ hθ hθc hθI
  have hconv_zero_out : ∀ z ∉ spaceTimeSet Ω I,
      (∑ i, ∑ j, u z i * u z j *
        spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z) = 0 := by
    intro z hz
    by_cases hx : z.1 ∈ Ω
    · have ht : z.2 ∉ I := fun ht => hz ⟨hx, ht⟩
      have htθ : z.2 ∉ tsupport θ := fun htθ => ht (hθI htθ)
      refine Finset.sum_eq_zero (fun i _ => ?_)
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [pressureTest_spatialPartial hψ i j z]
      simp [image_eq_zero_of_notMem_tsupport htθ]
    · have hxψ : z.1 ∉ tsupport ψ := fun hxψ => hx (hψΩ hxψ)
      refine Finset.sum_eq_zero (fun i _ => ?_)
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [pressureTest_spatialPartial hψ i j z]
      simp [image_eq_zero_of_notMem_tsupport
        (fun hm => hxψ (identity_ts_support_mixedSecond_subset j i hm))]
  have hpress_zero_out : ∀ z ∉ spaceTimeSet Ω I,
      p z * ∑ i, spatialPartial
        (fun w => pressureTestParabolic ψ θ w i) i z = 0 := by
    intro z hz
    by_cases hx : z.1 ∈ Ω
    · have ht : z.2 ∉ I := fun ht => hz ⟨hx, ht⟩
      have htθ : z.2 ∉ tsupport θ := fun htθ => ht (hθI htθ)
      rw [Finset.sum_eq_zero (fun i _ => by
        rw [pressureTest_spatialPartial hψ i i z]
        simp [image_eq_zero_of_notMem_tsupport htθ]), mul_zero]
    · have hxψ : z.1 ∉ tsupport ψ := fun hxψ => hx (hψΩ hxψ)
      rw [Finset.sum_eq_zero (fun i _ => by
        rw [pressureTest_spatialPartial hψ i i z]
        simp [image_eq_zero_of_notMem_tsupport
          (fun hm => hxψ (identity_ts_support_mixedSecond_subset i i hm))]), mul_zero]
  have hforce_zero_out : ∀ z ∉ spaceTimeSet Ω I,
      (∑ i, f z i * pressureTestParabolic ψ θ z i) = 0 := by
    intro z hz
    by_cases hx : z.1 ∈ Ω
    · have ht : z.2 ∉ I := fun ht => hz ⟨hx, ht⟩
      have htθ : z.2 ∉ tsupport θ := fun htθ => ht (hθI htθ)
      refine Finset.sum_eq_zero (fun i _ => ?_)
      change f z i * (θ z.2 * spatialDeriv ψ i z.1) = _
      simp [image_eq_zero_of_notMem_tsupport htθ]
    · have hxψ : z.1 ∉ tsupport ψ := fun hxψ => hx (hψΩ hxψ)
      refine Finset.sum_eq_zero (fun i _ => ?_)
      change f z i * (θ z.2 * spatialDeriv ψ i z.1) = _
      simp [image_eq_zero_of_notMem_tsupport
        (fun hm => hxψ (identity_ts_support_spatialDeriv_subset i hm))]
  have htime_zero_out : ∀ z ∉ spaceTimeSet Ω I,
      ∑ i, u z i * timePartial
        (fun w => pressureTestParabolic ψ θ w i) z = 0 := by
    intro z hz
    by_cases hx : z.1 ∈ Ω
    · have ht : z.2 ∉ I := fun ht => hz ⟨hx, ht⟩
      have hdt : z.2 ∉ tsupport (fun t => (fderiv ℝ θ t) 1) := by
        intro hm
        exact ht (hθI (tsupport_fderiv_apply_subset ℝ 1 hm))
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [pressureTest_timePartial hθ i z]
      simp [image_eq_zero_of_notMem_tsupport hdt]
    · have hxψ : z.1 ∉ tsupport ψ := fun hxψ => hx (hψΩ hxψ)
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [pressureTest_timePartial hθ i z]
      simp [image_eq_zero_of_notMem_tsupport
        (fun hm => hxψ (identity_ts_support_spatialDeriv_subset i hm))]
  have hconv_set : ∫ z in spaceTimeSet Ω I,
      ∑ i, ∑ j, u z i * u z j *
        spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z =
      ∫ z, ∑ i, ∑ j, u z i * u z j *
        spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hconv_zero_out]
  have hpress_set : ∫ z in spaceTimeSet Ω I,
      p z * ∑ i, spatialPartial
        (fun w => pressureTestParabolic ψ θ w i) i z =
      ∫ z, p z * ∑ i, spatialPartial
        (fun w => pressureTestParabolic ψ θ w i) i z := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hpress_zero_out]
  have hforce_set : ∫ z in spaceTimeSet Ω I,
      ∑ i, f z i * pressureTestParabolic ψ θ z i =
      ∫ z, ∑ i, f z i * pressureTestParabolic ψ θ z i := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hforce_zero_out]
  have hconv_prod : Integrable
      (fun z => ∑ i, ∑ j, u z i * u z j *
        spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z)
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) := hconv
  have hpress_prod : Integrable
      (fun z => p z * ∑ i, spatialPartial
        (fun w => pressureTestParabolic ψ θ w i) i z)
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) := hpress
  have hforce_prod : Integrable
      (fun z => ∑ i, f z i * pressureTestParabolic ψ θ z i)
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) := hforce
  have hconv_outer : Integrable
      (fun s => θ s * (∫ x in Ω, ∑ i, ∑ j,
        u (x, s) i * u (x, s) j * mixedSecond ψ i j x)) volume := by
    have htime := hconv_prod.integral_prod_right
    refine htime.congr (Filter.Eventually.of_forall (fun s => ?_))
    have hz (x : Vec3) (hx : x ∉ Ω) :
        ∑ i, ∑ j, u (x, s) i * u (x, s) j * mixedSecond ψ i j x = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      refine Finset.sum_eq_zero (fun j _ => ?_)
      simp [image_eq_zero_of_notMem_tsupport
        (fun hm => hx (hψΩ (identity_ts_support_mixedSecond_subset i j hm)))]
    calc
      ∫ x, ∑ i, ∑ j, u (x, s) i * u (x, s) j *
          spatialPartial (fun w => pressureTestParabolic ψ θ w i) j (x, s) =
          ∫ x, θ s * ∑ i, ∑ j,
            u (x, s) i * u (x, s) j * mixedSecond ψ i j x := by
              apply integral_congr_ae
              filter_upwards [] with x
              exact identity_pressure_convection_pointwise hψ ((x, s) : ParabolicPoint)
      _ = θ s * ∫ x, ∑ i, ∑ j,
          u (x, s) i * u (x, s) j * mixedSecond ψ i j x := by
            rw [integral_const_mul]
      _ = θ s * (∫ x in Ω, ∑ i, ∑ j,
          u (x, s) i * u (x, s) j * mixedSecond ψ i j x) := by
            rw [(identity_pressure_slice_integral_eq_full hz).symm]
  have hpress_outer : Integrable
      (fun s => θ s * (∫ x in Ω, p (x, s) * spatialLaplacian ψ x)) volume := by
    have htime := hpress_prod.integral_prod_right
    refine htime.congr (Filter.Eventually.of_forall (fun s => ?_))
    have hz (x : Vec3) (hx : x ∉ Ω) :
        p (x, s) * spatialLaplacian ψ x = 0 := by
      rw [image_eq_zero_of_notMem_tsupport
        (fun hm => hx (hψΩ (identity_ts_support_spatialLaplacian_subset hm))), mul_zero]
    calc
      ∫ x, p (x, s) * ∑ i, spatialPartial
          (fun w => pressureTestParabolic ψ θ w i) i (x, s) =
          ∫ x, θ s * (p (x, s) * spatialLaplacian ψ x) := by
            apply integral_congr_ae
            filter_upwards [] with x
            have hp := identity_pressure_laplacian_pointwise (ψ := ψ) (θ := θ) hψ
              ((x, s) : ParabolicPoint)
            rw [hp]
            ring
      _ = θ s * ∫ x, p (x, s) * spatialLaplacian ψ x := by
            rw [integral_const_mul]
      _ = θ s * (∫ x in Ω, p (x, s) * spatialLaplacian ψ x) := by
            rw [(identity_pressure_slice_integral_eq_full hz).symm]
  have hforce_outer : Integrable
      (fun s => θ s * (∫ x in Ω, ∑ i,
        f (x, s) i * spatialDeriv ψ i x)) volume := by
    have htime := hforce_prod.integral_prod_right
    refine htime.congr (Filter.Eventually.of_forall (fun s => ?_))
    have hz (x : Vec3) (hx : x ∉ Ω) :
        ∑ i, f (x, s) i * spatialDeriv ψ i x = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      simp [image_eq_zero_of_notMem_tsupport
        (fun hm => hx (hψΩ (identity_ts_support_spatialDeriv_subset i hm)))]
    calc
      ∫ x, ∑ i, f (x, s) i * pressureTestParabolic ψ θ (x, s) i =
          ∫ x, θ s * ∑ i, f (x, s) i * spatialDeriv ψ i x := by
            apply integral_congr_ae
            filter_upwards [] with x
            simpa only [Prod.fst, Prod.snd] using
              (identity_pressure_force_pointwise (ψ := ψ) (θ := θ)
                (f := f) ((x, s) : ParabolicPoint))
      _ = θ s * ∫ x, ∑ i, f (x, s) i * spatialDeriv ψ i x := by
            rw [integral_const_mul]
      _ = θ s * (∫ x in Ω, ∑ i,
          f (x, s) i * spatialDeriv ψ i x) := by
            rw [(identity_pressure_slice_integral_eq_full hz).symm]
  have hconv_fubini : ∫ z, ∑ i, ∑ j, u z i * u z j *
        spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z =
      ∫ s, θ s * (∫ x in Ω, ∑ i, ∑ j,
        u (x, s) i * u (x, s) j * mixedSecond ψ i j x) := by
    have hf := integral_prod_symm _ hconv_prod
    calc
      ∫ z, ∑ i, ∑ j, u z i * u z j *
          spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z =
          ∫ s, ∫ x, ∑ i, ∑ j, u (x, s) i * u (x, s) j *
            spatialPartial (fun w => pressureTestParabolic ψ θ w i) j (x, s) := hf
      _ = ∫ s, θ s * (∫ x in Ω, ∑ i, ∑ j,
          u (x, s) i * u (x, s) j * mixedSecond ψ i j x) := by
            apply integral_congr_ae
            filter_upwards [] with s
            have hz (x : Vec3) (hx : x ∉ Ω) :
                ∑ i, ∑ j, u (x, s) i * u (x, s) j * mixedSecond ψ i j x = 0 := by
              refine Finset.sum_eq_zero (fun i _ => ?_)
              refine Finset.sum_eq_zero (fun j _ => ?_)
              simp [image_eq_zero_of_notMem_tsupport
                (fun hm => hx (hψΩ (identity_ts_support_mixedSecond_subset i j hm)))]
            calc
              ∫ x, ∑ i, ∑ j, u (x, s) i * u (x, s) j *
                  spatialPartial (fun w => pressureTestParabolic ψ θ w i) j (x, s) =
                  ∫ x, θ s * ∑ i, ∑ j, u (x, s) i * u (x, s) j *
                    mixedSecond ψ i j x := by
                      apply integral_congr_ae
                      filter_upwards [] with x
                      have hp (i j : Fin 3) :=
                        pressureTest_spatialPartial (ψ := ψ) (θ := θ) hψ i j
                          ((x, s) : ParabolicPoint)
                      simp_rw [hp]
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro i hi
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro j hj
                      rw [mixedSecond_swap hψ j i x]
                      ring
              _ = θ s * ∫ x, ∑ i, ∑ j, u (x, s) i * u (x, s) j *
                    mixedSecond ψ i j x := by
                      rw [integral_const_mul]
              _ = θ s * ∫ x in Ω, ∑ i, ∑ j,
                    u (x, s) i * u (x, s) j * mixedSecond ψ i j x := by
                      rw [(identity_pressure_slice_integral_eq_full hz).symm]
  have hpress_fubini : ∫ z, p z * ∑ i, spatialPartial
        (fun w => pressureTestParabolic ψ θ w i) i z =
      ∫ s, θ s * (∫ x in Ω, p (x, s) * spatialLaplacian ψ x) := by
    have hf := integral_prod_symm _ hpress_prod
    calc
      ∫ z, p z * ∑ i, spatialPartial
          (fun w => pressureTestParabolic ψ θ w i) i z =
          ∫ s, ∫ x, p (x, s) * ∑ i, spatialPartial
            (fun w => pressureTestParabolic ψ θ w i) i (x, s) := hf
      _ = ∫ s, θ s * (∫ x in Ω, p (x, s) * spatialLaplacian ψ x) := by
            apply integral_congr_ae
            filter_upwards [] with s
            have hz (x : Vec3) (hx : x ∉ Ω) :
                p (x, s) * spatialLaplacian ψ x = 0 := by
              rw [image_eq_zero_of_notMem_tsupport
                (fun hm => hx (hψΩ (identity_ts_support_spatialLaplacian_subset hm))),
                mul_zero]
            calc
              ∫ x, p (x, s) * ∑ i, spatialPartial
                  (fun w => pressureTestParabolic ψ θ w i) i (x, s) =
                  ∫ x, θ s * (p (x, s) * spatialLaplacian ψ x) := by
                    apply integral_congr_ae
                    filter_upwards [] with x
                    have hp := identity_pressure_laplacian_pointwise (ψ := ψ) (θ := θ) hψ
                      ((x, s) : ParabolicPoint)
                    rw [hp]
                    ring
              _ = θ s * ∫ x, p (x, s) * spatialLaplacian ψ x := by
                    rw [integral_const_mul]
              _ = θ s * ∫ x in Ω, p (x, s) * spatialLaplacian ψ x := by
                    rw [(identity_pressure_slice_integral_eq_full hz).symm]
  have hforce_fubini : ∫ z, ∑ i, f z i * pressureTestParabolic ψ θ z i =
      ∫ s, θ s * (∫ x in Ω, ∑ i, f (x, s) i * spatialDeriv ψ i x) := by
    have hf := integral_prod_symm _ hforce_prod
    calc
      ∫ z, ∑ i, f z i * pressureTestParabolic ψ θ z i =
          ∫ s, ∫ x, ∑ i, f (x, s) i * pressureTestParabolic ψ θ (x, s) i := hf
      _ = ∫ s, θ s * (∫ x in Ω, ∑ i, f (x, s) i * spatialDeriv ψ i x) := by
            apply integral_congr_ae
            filter_upwards [] with s
            have hz (x : Vec3) (hx : x ∉ Ω) :
                ∑ i, f (x, s) i * spatialDeriv ψ i x = 0 := by
              refine Finset.sum_eq_zero (fun i _ => ?_)
              simp [image_eq_zero_of_notMem_tsupport
                (fun hm => hx (hψΩ (identity_ts_support_spatialDeriv_subset i hm)))]
            calc
              ∫ x, ∑ i, f (x, s) i * pressureTestParabolic ψ θ (x, s) i =
                  ∫ x, θ s * ∑ i, f (x, s) i * spatialDeriv ψ i x := by
                    apply integral_congr_ae
                    filter_upwards [] with x
                    simpa only [Prod.fst, Prod.snd] using
                      (identity_pressure_force_pointwise (ψ := ψ) (θ := θ)
                        (f := f) ((x, s) : ParabolicPoint))
      _ = θ s * ∫ x, ∑ i, f (x, s) i * spatialDeriv ψ i x := by
                    rw [integral_const_mul]
              _ = θ s * ∫ x in Ω, ∑ i, f (x, s) i * spatialDeriv ψ i x := by
                    rw [(identity_pressure_slice_integral_eq_full hz).symm]
  let A : ParabolicPoint → ℝ := fun z => ∑ i, u z i * timePartial
    (fun w => pressureTestParabolic ψ θ w i) z
  let B : ParabolicPoint → ℝ := fun z => ∑ i, ∑ j, u z i * u z j *
    spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z
  let C : ParabolicPoint → ℝ := fun z => ∑ i, ∑ j, Du z i j *
    spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z
  let D : ParabolicPoint → ℝ := fun z => p z * ∑ i, spatialPartial
    (fun w => pressureTestParabolic ψ θ w i) i z
  let E : ParabolicPoint → ℝ := fun z => ∑ i, f z i * pressureTestParabolic ψ θ z i
  have htimeOn : IntegrableOn A (spaceTimeSet Ω I) volume := by
    change IntegrableOn (fun z => ∑ i, u z i * timePartial
      (fun w => pressureTestParabolic ψ θ w i) z) (spaceTimeSet Ω I) volume
    exact htimeInt
  have hconvOn : IntegrableOn B (spaceTimeSet Ω I) volume := by
    change IntegrableOn (fun z => ∑ i, ∑ j, u z i * u z j *
      spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z)
      (spaceTimeSet Ω I) volume
    exact hconv.integrableOn
  have hviscOn : IntegrableOn C (spaceTimeSet Ω I) volume := by
    change IntegrableOn (fun z => ∑ i, ∑ j, Du z i j *
      spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z)
      (spaceTimeSet Ω I) volume
    exact hvisc.integrableOn
  have hpressOn : IntegrableOn D (spaceTimeSet Ω I) volume := by
    change IntegrableOn (fun z => p z * ∑ i, spatialPartial
      (fun w => pressureTestParabolic ψ θ w i) i z) (spaceTimeSet Ω I) volume
    exact hpress.integrableOn
  have hforceOn : IntegrableOn E (spaceTimeSet Ω I) volume := by
    change IntegrableOn (fun z => ∑ i, f z i * pressureTestParabolic ψ θ z i)
      (spaceTimeSet Ω I) volume
    exact hforce.integrableOn
  have hsplit :
      ∫ z in spaceTimeSet Ω I, (-A z - B z + C z - D z - E z) =
        -(∫ z in spaceTimeSet Ω I, A z) -
          (∫ z in spaceTimeSet Ω I, B z) +
          (∫ z in spaceTimeSet Ω I, C z) -
          (∫ z in spaceTimeSet Ω I, D z) -
          (∫ z in spaceTimeSet Ω I, E z) := by
    have hab : IntegrableOn (fun z => -A z - B z)
        (spaceTimeSet Ω I) volume := htimeOn.neg.sub hconvOn
    have habc : IntegrableOn (fun z => -A z - B z + C z)
        (spaceTimeSet Ω I) volume := hab.add hviscOn
    have habcd : IntegrableOn (fun z => -A z - B z + C z - D z)
        (spaceTimeSet Ω I) volume := habc.sub hpressOn
    rw [integral_sub habcd hforceOn]
    rw [integral_sub habc hpressOn]
    rw [integral_add hab hviscOn]
    have hab_eq : (∫ z in spaceTimeSet Ω I, -A z - B z) =
        (∫ z in spaceTimeSet Ω I, -A z) -
          ∫ z in spaceTimeSet Ω I, B z := integral_sub htimeOn.neg hconvOn
    rw [hab_eq, integral_neg]
  have hmain : ∫ z in spaceTimeSet Ω I, (-A z - B z + C z - D z - E z) = 0 := by
    simpa only [A, B, C, D, E] using hS3zero
  rw [hsplit] at hmain
  simp only [A, B, C, D, E] at hmain
  have hsumzero :
      (∫ s, θ s * (∫ x in Ω, p (x, s) * spatialLaplacian ψ x)) +
          (∫ s, θ s * (∫ x in Ω, ∑ i, ∑ j,
            u (x, s) i * u (x, s) j * mixedSecond ψ i j x)) +
          ∫ s, θ s * (∫ x in Ω, ∑ i,
            f (x, s) i * spatialDeriv ψ i x) = 0 := by
    have hraw :
        (∫ z in spaceTimeSet Ω I, ∑ i, ∑ j, u z i * u z j *
          spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z) +
            (∫ z in spaceTimeSet Ω I, p z * ∑ i, spatialPartial
              (fun w => pressureTestParabolic ψ θ w i) i z) +
            ∫ z in spaceTimeSet Ω I, ∑ i, f z i * pressureTestParabolic ψ θ z i = 0 := by
      linarith only [hmain, htimeZero, hviscZero]
    rw [hconv_set, hpress_set, hforce_set, hconv_fubini, hpress_fubini,
      hforce_fubini] at hraw
    linarith only [hraw]
  have hres_outer : Integrable
      (fun s => θ s * pressureSliceResidual
        (Ω := Ω) (u := u) (p := p) (f := f) ψ s) volume := by
    have hsum := (hpress_outer.add hconv_outer).add hforce_outer
    refine hsum.congr (Filter.Eventually.of_forall (fun s => ?_))
    simp only [pressureSliceResidual]
    simp only [Pi.add_apply]
    ring
  have hres_split :
      ∫ s, θ s * pressureSliceResidual
        (Ω := Ω) (u := u) (p := p) (f := f) ψ s =
        (∫ s, θ s * (∫ x in Ω, p ((x, s) : ParabolicPoint) *
          spatialLaplacian ψ x)) +
          (∫ s, θ s * (∫ x in Ω, ∑ i, ∑ j,
            u ((x, s) : ParabolicPoint) i * u ((x, s) : ParabolicPoint) j *
              mixedSecond ψ i j x)) +
          ∫ s, θ s * (∫ x in Ω, ∑ i,
            f ((x, s) : ParabolicPoint) i * spatialDeriv ψ i x) := by
    have hpc :
        (∫ s, θ s * (∫ x in Ω, p ((x, s) : ParabolicPoint) *
          spatialLaplacian ψ x) +
          θ s * (∫ x in Ω, ∑ i, ∑ j,
            u ((x, s) : ParabolicPoint) i * u ((x, s) : ParabolicPoint) j *
              mixedSecond ψ i j x)) =
        (∫ s, θ s * (∫ x in Ω, p ((x, s) : ParabolicPoint) *
          spatialLaplacian ψ x)) +
          ∫ s, θ s * (∫ x in Ω, ∑ i, ∑ j,
            u ((x, s) : ParabolicPoint) i * u ((x, s) : ParabolicPoint) j *
              mixedSecond ψ i j x) := by
      simpa only [Pi.add_apply] using (integral_add hpress_outer hconv_outer)
    calc
      ∫ s, θ s * pressureSliceResidual
          (Ω := Ω) (u := u) (p := p) (f := f) ψ s =
          ∫ s, (θ s * (∫ x in Ω, p ((x, s) : ParabolicPoint) *
              spatialLaplacian ψ x) +
            θ s * (∫ x in Ω, ∑ i, ∑ j,
              u ((x, s) : ParabolicPoint) i * u ((x, s) : ParabolicPoint) j *
                mixedSecond ψ i j x)) +
            θ s * (∫ x in Ω, ∑ i,
              f ((x, s) : ParabolicPoint) i * spatialDeriv ψ i x) := by
                apply integral_congr_ae
                filter_upwards [] with s
                simp only [pressureSliceResidual]
                ring
      _ = (∫ s, θ s * (∫ x in Ω, p ((x, s) : ParabolicPoint) *
              spatialLaplacian ψ x) +
            θ s * (∫ x in Ω, ∑ i, ∑ j,
              u ((x, s) : ParabolicPoint) i * u ((x, s) : ParabolicPoint) j *
                mixedSecond ψ i j x)) +
            ∫ s, θ s * (∫ x in Ω, ∑ i,
              f ((x, s) : ParabolicPoint) i * spatialDeriv ψ i x) := by
                simpa only [Pi.add_apply] using
                  (integral_add (hpress_outer.add hconv_outer) hforce_outer)
      _ = (∫ s, θ s * (∫ x in Ω, p ((x, s) : ParabolicPoint) *
            spatialLaplacian ψ x)) +
            (∫ s, θ s * (∫ x in Ω, ∑ i, ∑ j,
              u ((x, s) : ParabolicPoint) i * u ((x, s) : ParabolicPoint) j *
                mixedSecond ψ i j x)) +
            ∫ s, θ s * (∫ x in Ω, ∑ i,
              f ((x, s) : ParabolicPoint) i * spatialDeriv ψ i x) := by
                rw [hpc]
  exact hres_split.trans hsumzero

/-! ### Per-test and parametrized forms -/

/-- The pressure slice identity, including the force term, holds for each fixed
compactly supported smooth spatial test function for almost every time. -/
theorem pressure_slice_identity_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ Ω) :
    ∀ᵐ s ∂volume.restrict I,
      ∫ x in Ω, p (x, s) * spatialLaplacian ψ x =
        -(∫ x in Ω, ∑ i, ∑ j, u (x, s) i * u (x, s) j * mixedSecond ψ i j x) -
          (∫ x in Ω, ∑ i, f (x, s) i * spatialDeriv ψ i x) := by
  have hI : IsOpen I := h.2.1
  have hloc := pressureSliceResidual_locallyIntegrable h hψ hψc hψΩ
  have hzero : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ I →
        ∫ t, η t • pressureSliceResidual
          (Ω := Ω) (u := u) (p := p) (f := f) ψ t = 0 := by
    intro η hη hηc hηI
    simpa only [smul_eq_mul] using
      (pressure_test_integral_zero h hψ hψc hψΩ hη hηc hηI)
  have hae := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hI hloc hzero
  have hae' := (ae_restrict_iff' hI.measurableSet).mpr hae
  filter_upwards [hae'] with s hs
  unfold pressureSliceResidual at hs
  ring_nf at hs ⊢
  linarith only [hs]

/-- The per-test pressure identity holds simultaneously for a countable family
of compactly supported smooth tests. -/
theorem pressure_slice_identity_ae_countable
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {C : Set (Vec3 → ℝ)} (hC : C.Countable)
    (hCtest : ∀ ψ ∈ C, ContDiff ℝ (⊤ : ℕ∞) ψ ∧
      HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω) :
    ∀ᵐ s ∂volume.restrict I, ∀ ψ ∈ C,
      ∫ x in Ω, p (x, s) * spatialLaplacian ψ x =
        -(∫ x in Ω, ∑ i, ∑ j, u (x, s) i * u (x, s) j * mixedSecond ψ i j x) -
          (∫ x in Ω, ∑ i, f (x, s) i * spatialDeriv ψ i x) := by
  classical
  haveI : Countable {ψ // ψ ∈ C} := hC.to_subtype
  have hsub : ∀ᵐ s ∂volume.restrict I, ∀ ψ : C,
      ∫ x in Ω, p (x, s) * spatialLaplacian ψ x =
        -(∫ x in Ω, ∑ i, ∑ j, u (x, s) i * u (x, s) j * mixedSecond ψ i j x) -
          (∫ x in Ω, ∑ i, f (x, s) i * spatialDeriv ψ i x) := by
    rw [ae_all_iff]
    intro ψ
    obtain ⟨hψ, hψc, hψΩ⟩ := hCtest ψ ψ.property
    exact pressure_slice_identity_ae h hψ hψc hψΩ
  filter_upwards [hsub] with s hs ψ hψ
  simpa only using hs ⟨ψ, hψ⟩

end CKN

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryL2Integration
public import LeanPool.NavierStokesAndEuler.Euler.MeanOrbitSmoothL2Field
public import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalConstraints

@[expose] public section

/-! A genuine smooth L² gradient belongs to the closed ordinary gradient
space, even when its scalar potential is not square-integrable. The
solenoidal remainder is both curl-free and harmonic, hence zero by the
actual L² integration-by-parts identity. -/

noncomputable section

namespace EulerOrdinarySobolev

open MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanVectorIdentities
  EulerMeanSolenoidal EulerMeanSmoothRepresentative EulerMeanPressure EulerMeanClassical
  EulerMeanCutoffCurl EulerVectorCalculus Laplacian
open scoped ContDiff ENNReal

theorem solenoidal_orbit (A : SmoothL2Field Space) :
    SmoothOrbit (solenoidalProjection A.toLp) := by
  have he : (fun a : Space => EulerMeanSolenoidal.translation a (solenoidalProjection A.toLp))=
      solenoidalProjection ∘ (fun a : Space => EulerMeanSolenoidal.translation a A.toLp) :=
    funext (fun a => solenoidalProjection_translation a A.toLp)
  change ContDiff ℝ ∞ _
  rw [he]
  exact solenoidalProjection.contDiff.comp A.translation_contDiff

theorem curl_zero_of_symmetric (A : SmoothL2Field Space)
    (hA : ∀ x i j, (fderiv ℝ A.field x (EuclideanSpace.single i 1)) j=
      (fderiv ℝ A.field x (EuclideanSpace.single j 1)) i) :
    vectorCurl A.field=0 := by
  funext x
  ext i
  change partialDerivative (fun y => A.field y (i+2)) (i+1) x-
    partialDerivative (fun y => A.field y (i+1)) (i+2) x=0
  simp only [partialDerivative,fderiv_coordinate A.field x
    (A.smooth.differentiable (by simp) x)]
  exact sub_eq_zero.mpr (hA x (i+1) (i+2))

theorem gradient_mem_of_symmetric (A : SmoothL2Field Space)
    (hA : ∀ x i j, (fderiv ℝ A.field x (EuclideanSpace.single i 1)) j=
      (fderiv ℝ A.field x (EuclideanSpace.single j 1)) i) :
    A.toLp ∈ gradientSpace := by
  let B := smoothL2Field (solenoidalProjection A.toLp) (solenoidal_orbit A)
  have hB : B.toLp=solenoidalProjection A.toLp := smoothL2Field_toLp _ _
  have hrep : (solenoidalProjection A.toLp : Space → Space)=ᵐ[volume] B.field := by
    rw [← hB]
    exact B.toLp_ae
  have hres : ((A.toLp-solenoidalProjection A.toLp : L2) : Space → Space)=ᵐ[volume] A.field-B.field
    := by
    filter_upwards [Lp.coeFn_sub A.toLp (solenoidalProjection A.toLp),A.toLp_ae,hrep]
      with x hs ha hb
    simp only [hs,ha,hb,Pi.sub_apply]
  have hsym := gradientSpace_classical_curl_zero _ (sub_solenoidalProjection_mem_gradient A.toLp)
    (A.field-B.field) hres (A.smooth.sub B.smooth)
  have hBc : ∀ x i j, (fderiv ℝ B.field x (EuclideanSpace.single i 1)) j=
      (fderiv ℝ B.field x (EuclideanSpace.single j 1)) i := by
    intro x i j
    have hd := hsym x i j
    rw [fderiv_sub (A.smooth.differentiable (by simp) x) (B.smooth.differentiable (by simp) x)] at
      hd
    simp only [sub_apply,PiLp.sub_apply] at hd
    linarith [hA x i j]
  have hcurl := curl_zero_of_symmetric B hBc
  have hdiv : divergence B.field=0 := funext
    (solenoidal_representative_divergence _ (solenoidalProjection_mem A.toLp) B.field B.smooth hrep)
  have hΔ : ∀ x, Δ B.field x=0 := by
    intro x
    have h := congrFun (vectorCurl_vectorCurl B.field B.smooth) x
    rw [hcurl,hdiv] at h
    have hc : vectorCurl (0 : Space → Space) x=0 := by
      ext i
      simp [vectorCurl,curl,partialDerivative]
    have hg : gradient (0 : Space → ℝ) x=0 := by simp [gradient]
    simp only [hc,hg,Pi.sub_apply,zero_sub] at h
    exact neg_eq_zero.mp h.symm
  have hz := field_zero_of_laplacian_zero B hΔ
  apply (solenoidalProjection_eq_zero_iff A.toLp).mp
  rw [← hB]
  apply Lp.ext
  filter_upwards [B.toLp_ae,Lp.coeFn_zero Space 2 (volume : Measure Space)] with x hb hzero
  rw [hb,hz,Pi.zero_apply,hzero]
  rfl

theorem gradient_mem (A : SmoothL2Field Space) (p : Space → ℝ)
    (hp : ContDiff ℝ ∞ p) (hgrad : ∀ x, A.field x=gradient p x) :
    A.toLp ∈ gradientSpace := by
  apply gradient_mem_of_symmetric A
  intro x i j
  have hi : (fun y => A.field y i)=partialDerivative p i :=
    funext (fun y => by rw [hgrad,gradient_coordinate])
  have hj : (fun y => A.field y j)=partialDerivative p j :=
    funext (fun y => by rw [hgrad,gradient_coordinate])
  have h := partialDerivative_comm p (hp.of_le (by simp)) j i x
  rw [← hi,← hj] at h
  simpa only [partialDerivative,fderiv_coordinate A.field x
    (A.smooth.differentiable (by simp) x)] using h

theorem gradient_pairing_zero (A U : SmoothL2Field Space) (p : Space → ℝ)
    (hp : ContDiff ℝ ∞ p) (hgrad : ∀ x, A.field x=gradient p x)
    (hdiv : ∀ x, divergence U.field x=0) : ⟪A.toLp,U.toLp⟫_ℝ=0 :=
  pressure_pairing_zero (gradient_mem A p hp hgrad)
    (smooth_mem_solenoidal U.field U.smooth U.memLp hdiv)

theorem potential_smooth (A : SmoothL2Field Space) (p : Space → ℝ)
    (hp : Differentiable ℝ p) (hgrad : ∀ x, A.field x=gradient p x) :
    ContDiff ℝ ∞ p := by
  apply contDiff_infty_iff_fderiv.mpr
  refine ⟨hp,?_⟩
  have he : fderiv ℝ p=(toDual ℝ Space) ∘ A.field := by
    funext x
    rw [Function.comp_apply,hgrad,toDual_gradient]
  rw [he]
  exact (toDual ℝ Space).contDiff.comp A.smooth

theorem gradient_pairing_zero_of_differentiable (A U : SmoothL2Field Space) (p : Space → ℝ)
    (hp : Differentiable ℝ p) (hgrad : ∀ x, A.field x=gradient p x)
    (hdiv : ∀ x, divergence U.field x=0) : ⟪A.toLp,U.toLp⟫_ℝ=0 :=
  gradient_pairing_zero A U p (potential_smooth A p hp hgrad) hgrad hdiv

end EulerOrdinarySobolev

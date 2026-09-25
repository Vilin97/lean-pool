/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceDistributionTransport
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Equation

/-!
# Second-order transport identities for translated mollifier kernels

This module records the mixed-second-order analogues of the first-order
mollifier transport identities of `CKN.Foundation.Measure.SliceDistributionTransport`.
In the elliptic-regularity analysis of Caffarelli--Kohn--Nirenberg (1982), the
pairing of a distribution with the countable family of translated mollifier
bumps is integrated by parts; the first-order identities handle the
divergence-form (first-derivative) slots, while the identities here handle the
second-derivative slots of `eq:leibniz-lap` and `eq:commute`.

Concretely, we differentiate under the reflected convolution: the integral of a
smooth `ψ` against the mixed second derivative `∂_i ∂_j` of the reflected kernel
`mollifier ε (x - ·)` equals the mollification of the corresponding mixed second
derivative of `ψ`.  The translation identities `spatialDeriv_sub_const` and
`mixedSecond_sub_const` reduce the reflected derivative to the translate of the
derivative, and the kernel vanishes outside its support ball.
-/

@[expose] public section

open MeasureTheory Metric
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-- Spatial derivative of a translate: `∂_i (z ↦ g (z - y)) (x) = ∂_i g (x - y)`.
This is the chain rule for the translation `z ↦ z - y`, used to move the
derivative of a reflected mollifier kernel back onto the kernel. -/
theorem spatialDeriv_sub_const {g : Vec3 → ℝ} (hg : Differentiable ℝ g) (y x : Vec3)
    (i : Fin 3) :
    spatialDeriv (fun z : Vec3 => g (z - y)) i x = spatialDeriv g i (x - y) := by
  have hinner : HasFDerivAt (fun z : Vec3 => z - y) (ContinuousLinearMap.id ℝ Vec3) x :=
    (hasFDerivAt_id x).sub_const y
  have houter : HasFDerivAt g (fderiv ℝ g (x - y)) (x - y) := (hg (x - y)).hasFDerivAt
  have hcomp := houter.comp x hinner
  simpa [spatialDeriv, Function.comp_def, ContinuousLinearMap.comp_apply] using
    congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) hcomp.fderiv

/-- Mixed second derivative of a translate:
`∂_i ∂_j (z ↦ g (z - y)) (x) = ∂_i ∂_j g (x - y)`.  This iterates the
translation chain rule `spatialDeriv_sub_const` on the smooth function `g`. -/
theorem mixedSecond_sub_const {g : Vec3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y x : Vec3)
    (i j : Fin 3) :
    mixedSecond (fun z : Vec3 => g (z - y)) i j x = mixedSecond g i j (x - y) := by
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hgd2 : Differentiable ℝ (spatialDeriv g j) :=
    (contDiff_spatialDeriv_smooth hg j).differentiable (by simp)
  have hstep : spatialDeriv (fun z : Vec3 => g (z - y)) j
      = fun w : Vec3 => spatialDeriv g j (w - y) := by
    funext w
    exact spatialDeriv_sub_const hgd y w j
  simp only [mixedSecond]
  rw [hstep]
  exact spatialDeriv_sub_const hgd2 y x i

/-- Integration by parts against a translated derivative: for smooth `ψ` and
smooth compactly supported `g`, the pairing of `ψ` with the reflected `i`th
partial derivative of `g` equals the pairing of the `i`th partial derivative of
`ψ` with the reflected `g`.  This is the weak partial-derivative identity for
`ψ` tested against the smooth compactly supported translate `w ↦ g (x - w)`. -/
theorem integral_mul_spatialDeriv_sub {ψ g : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (i : Fin 3) (x : Vec3) :
    ∫ y, ψ y * spatialDeriv g i (x - y) ∂MeasureTheory.volume =
      ∫ y, spatialDeriv ψ i y * g (x - y) ∂MeasureTheory.volume := by
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hφsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec3 => g (x - w)) :=
    hg.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport (fun w : Vec3 => g (x - w)) := by
    simpa [Function.comp_def] using hgc.comp_homeomorph (Homeomorph.subLeft x)
  have hchain : ∀ w : Vec3,
      (fderiv ℝ (fun w : Vec3 => g (x - w)) w) (basisVec i)
        = -(spatialDeriv g i) (x - w) := by
    intro w
    have hinner : HasFDerivAt (fun z : Vec3 => x - z)
        (0 - ContinuousLinearMap.id ℝ Vec3) w :=
      (hasFDerivAt_const x w).sub (hasFDerivAt_id w)
    have houter : HasFDerivAt g (fderiv ℝ g (x - w)) (x - w) :=
      (hgd (x - w)).hasFDerivAt
    have hcomp := houter.comp w hinner
    have h := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) hcomp.fderiv
    have hval : (0 - ContinuousLinearMap.id ℝ Vec3 : Vec3 →L[ℝ] Vec3) (basisVec i)
        = -(basisVec i) := by simp
    rw [ContinuousLinearMap.comp_apply, hval, map_neg] at h
    simpa [spatialDeriv, Function.comp_def] using h
  have hweak := HasWeakPartialDerivOn.of_contDiff (U := (Set.univ : Set Vec3)) (i := i)
    (hψ.of_le (by simp))
  have hw := hweak (fun w : Vec3 => g (x - w)) hφsmooth hφc (Set.subset_univ _)
  simp only [MeasureTheory.setIntegral_univ] at hw
  have hA : (∫ y, ψ y * spatialDeriv g i (x - y) ∂MeasureTheory.volume)
      = -∫ w, ψ w * (fderiv ℝ (fun w : Vec3 => g (x - w)) w) (basisVec i)
          ∂MeasureTheory.volume := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with w
    rw [hchain w]
    ring
  rw [hA, hw, neg_neg]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with w
  rfl

/-- The mixed second derivative of the radius-`ε` mollifier is continuous; it is
a second partial derivative of a smooth compactly supported kernel. -/
theorem continuous_mixedSecond_mollifier {ε : ℝ} (hε : 0 < ε) (i j : Fin 3) :
    Continuous (mixedSecond (mollifier (d := 3) ε hε) i j) :=
  (contDiff_mixedSecond_smooth (mollifier_contDiff (d := 3) (n := ⊤) hε) i j).continuous

/-- The mixed second derivative of the mollifier vanishes outside the support
ball: for `ε < ‖z‖`, `∂_i ∂_j mollifier ε z = 0`.  This is because the
topological support of a coordinate derivative is contained in that of the
kernel, which is the closed ball of radius `ε`. -/
theorem mixedSecond_mollifier_eq_zero {ε : ℝ} (hε : 0 < ε) (i j : Fin 3) {z : Vec3}
    (hz : ε < ‖z‖) : mixedSecond (mollifier (d := 3) ε hε) i j z = 0 := by
  have hts : tsupport (mollifier (d := 3) ε hε) = closedBall (0 : Vec3) ε :=
    (standardMollifier (d := 3) ε hε).tsupport_normed_eq
  have hsub : tsupport (spatialDeriv (mollifier (d := 3) ε hε) j)
      ⊆ closedBall (0 : Vec3) ε := by
    rw [← hts]
    exact tsupport_fderiv_apply_subset ℝ (basisVec j)
  have hz' : z ∉ tsupport (spatialDeriv (mollifier (d := 3) ε hε) j) := by
    intro hzmem
    have hball : z ∈ closedBall (0 : Vec3) ε := hsub hzmem
    rw [mem_closedBall, dist_zero_right] at hball
    exact not_le.2 hz hball
  change (fderiv ℝ (spatialDeriv (mollifier (d := 3) ε hε) j) z) (basisVec i) = 0
  rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hz']
  simp

/-- Integration by parts against the reflected mixed second derivative of the
mollifier: for smooth `ψ`, the pairing of `ψ` with `∂_i ∂_j mollifier ε (x - ·)`
equals the mollification of the mixed second derivative `∂_i ∂_j ψ`.  This is the
second-order analogue of the first-order identity
`integral_mul_fderiv_mollifier_sub`, obtained by applying
`integral_mul_spatialDeriv_sub` twice and using symmetry of the mixed partials. -/
theorem integral_mul_mixedSecond_mollifier_sub {ψ : Vec3 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i j : Fin 3) {ε : ℝ} (hε : 0 < ε) (x : Vec3) :
    ∫ y, ψ y * mixedSecond (mollifier (d := 3) ε hε) i j (x - y)
        ∂MeasureTheory.volume =
      mollify (mixedSecond ψ i j) ε hε x := by
  let m : Vec3 → ℝ := mollifier (d := 3) ε hε
  have hm : ContDiff ℝ (⊤ : ℕ∞) m := mollifier_contDiff (d := 3) hε
  have hmc : HasCompactSupport m := mollifier_hasCompactSupport (d := 3) hε
  have h1 := integral_mul_spatialDeriv_sub (ψ := ψ) hψ
    (contDiff_spatialDeriv_smooth hm j) (hmc.fderiv_apply (𝕜 := ℝ) (basisVec j)) i x
  have h2 := integral_mul_spatialDeriv_sub (ψ := spatialDeriv ψ i)
    (contDiff_spatialDeriv_smooth hψ i) hm hmc j x
  have h3 := integral_mul_mollifier_sub (d := 3) (mixedSecond ψ j i) hε x
  calc
    ∫ y, ψ y * mixedSecond m i j (x - y) ∂MeasureTheory.volume
        = ∫ y, spatialDeriv ψ i y * spatialDeriv m j (x - y) ∂MeasureTheory.volume := h1
    _ = ∫ y, mixedSecond ψ j i y * m (x - y) ∂MeasureTheory.volume := h2
    _ = mollify (mixedSecond ψ j i) ε hε x := h3
    _ = mollify (mixedSecond ψ i j) ε hε x := by
          have hswap : mixedSecond ψ j i = mixedSecond ψ i j :=
            funext fun w => (mixedSecond_swap hψ i j w).symm
          rw [hswap]

end CKN

end

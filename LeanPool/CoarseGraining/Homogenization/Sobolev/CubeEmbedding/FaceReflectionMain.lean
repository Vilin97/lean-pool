/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding.FaceReflection
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Face Reflection Main -/

@[expose] public section

namespace Homogenization

open Homogenization MeasureTheory
open scoped BigOperators

/-!
# Single-face even reflection: weak-gradient transport (main theorem)

The even reflection `faceReflect v a i` of a globally `C¹`, compactly supported
function `v` on `Vec (n+1)` has weak gradient the piecewise `faceGrad v a i` on
all of `Vec (n+1)` (hence, by restriction, on any open set).
-/

noncomputable section

variable {n : ℕ}

/-- The restriction of a compactly supported function to an insertion line is
compactly supported. -/
theorem hasCompactSupport_insertNth_line {φ : Vec (n + 1) → ℝ}
    (hφc : HasCompactSupport φ) (j : Fin (n + 1)) (z : Vec n) :
    HasCompactSupport (fun t => φ (j.insertNth t z)) := by
  have hK : IsCompact (tsupport φ) := hφc
  have himg : IsCompact ((fun x : Vec (n + 1) => x j) '' tsupport φ) :=
    hK.image (continuous_apply j)
  obtain ⟨R, hR⟩ := himg.isBounded.subset_closedBall (0 : ℝ)
  rw [Real.closedBall_eq_Icc] at hR
  simp only [zero_sub, zero_add] at hR
  apply HasCompactSupport.intro (K := Set.Icc (-R) R) isCompact_Icc
  intro t ht
  by_contra h0
  have hmem : (j.insertNth t z) ∈ tsupport φ :=
    subset_tsupport φ (by rw [Function.mem_support]; exact h0)
  have : t ∈ Set.Icc (-R) R := by
    have hmem2 : (j.insertNth t z : Vec (n + 1)) j
        ∈ (fun x : Vec (n + 1) => x j) '' tsupport φ :=
      ⟨j.insertNth t z, hmem, rfl⟩
    rw [Fin.insertNth_apply_same] at hmem2
    exact hR hmem2
  exact ht this

/-- Almost every real number differs from a fixed point. -/
private theorem ae_ne_point (a : ℝ) : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ a := by
  rw [MeasureTheory.ae_iff]
  simp

/-- **Diagonal per-line identity** (reflection direction = differentiation
direction).  The reflected line integrates by parts against `φ` with the
sign-flipped candidate derivative, with no boundary term. -/
private theorem faceReflect_line_integral_diag {v : Vec (n + 1) → ℝ}
    (hv : ContDiff ℝ 1 v) {φ : Vec (n + 1) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (a : ℝ) (j : Fin (n + 1)) (z : Vec n) :
    (∫ t, faceReflect v a j (j.insertNth t z)
          * (fderiv ℝ φ (j.insertNth t z)) (basisVec j))
      = -(∫ t, faceGrad v a j (j.insertNth t z) j * φ (j.insertNth t z)) := by
  have hvd : Differentiable ℝ v := hv.differentiable (by simp)
  have hvf : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by simp)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφf : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hlineDir : Continuous (fun t : ℝ => (j.insertNth t z : Vec (n + 1))) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_insertNth j z t).continuousAt
  have hlineRefl : Continuous (fun t : ℝ => (j.insertNth (2 * a - t) z : Vec (n + 1))) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_insertNth_reflect a j z t).continuousAt
  -- derivatives of the two branch functions and the line test
  have hd₁ : ∀ t, HasDerivAt (fun s => v (j.insertNth (2 * a - s) z))
      ((fderiv ℝ v (j.insertNth (2 * a - t) z)) (-basisVec j)) t :=
    fun t => hasDerivAt_comp_insertNth_reflect hvd a j z t
  have hd₂ : ∀ t, HasDerivAt (fun s => v (j.insertNth s z))
      ((fderiv ℝ v (j.insertNth t z)) (basisVec j)) t :=
    fun t => hasDerivAt_comp_insertNth hvd j z t
  have hφL_deriv : ∀ t, HasDerivAt (fun s => φ (j.insertNth s z))
      ((fderiv ℝ φ (j.insertNth t z)) (basisVec j)) t :=
    fun t => hasDerivAt_comp_insertNth hφd j z t
  have hc₁ : Continuous (fun t => (fderiv ℝ v (j.insertNth (2 * a - t) z)) (-basisVec j)) :=
    (hvf.comp hlineRefl).clm_apply continuous_const
  have hc₂ : Continuous (fun t => (fderiv ℝ v (j.insertNth t z)) (basisVec j)) :=
    (hvf.comp hlineDir).clm_apply continuous_const
  have hcφ : Continuous (fun t => (fderiv ℝ φ (j.insertNth t z)) (basisVec j)) :=
    (hφf.comp hlineDir).clm_apply continuous_const
  have hφL_cs : HasCompactSupport (fun t => φ (j.insertNth t z)) :=
    hasCompactSupport_insertNth_line hφc j z
  have hmatch : v (j.insertNth (2 * a - a) z) = v (j.insertNth a z) := by
    rw [show (2 * a - a : ℝ) = a by ring]
  -- integration by parts across the kink at `a`
  have hkey := integral_mul_deriv_piecewise_eq_neg a hd₁ hc₁ hd₂ hc₂ hmatch hφL_deriv hcφ hφL_cs
  -- rewrite the reflection to the piecewise form on the line
  have hA : ∀ t, faceReflect v a j (j.insertNth t z)
      = (if t ≤ a then v (j.insertNth (2 * a - t) z) else v (j.insertNth t z)) := by
    intro t
    simp only [faceReflect, Fin.insertNth_apply_same]
    rcases lt_trichotomy t a with h | h | h
    · rw [if_neg (not_le.mpr h), if_pos (le_of_lt h), coordFaceReflection_insertNth]
    · subst h
      rw [if_pos (le_refl t), if_pos (le_refl t), show (2 * t - t : ℝ) = t by ring]
    · rw [if_pos (le_of_lt h), if_neg (not_le.mpr h)]
  -- rewrite the candidate gradient to the piecewise derivative off the kink
  have hB : ∀ t, t ≠ a → faceGrad v a j (j.insertNth t z) j
      = (if t ≤ a then (fderiv ℝ v (j.insertNth (2 * a - t) z)) (-basisVec j)
          else (fderiv ℝ v (j.insertNth t z)) (basisVec j)) := by
    intro t ht
    unfold faceGrad
    rw [Fin.insertNth_apply_same]
    rcases lt_trichotomy t a with h | h | h
    · rw [if_neg (not_le.mpr h), if_pos (le_of_lt h), if_pos (rfl : j = j),
        coordFaceReflection_insertNth, map_neg, neg_one_mul]
    · exact absurd h ht
    · rw [if_pos (le_of_lt h), if_neg (not_le.mpr h)]
  -- assemble
  have e1 : (∫ t, faceReflect v a j (j.insertNth t z)
        * (fderiv ℝ φ (j.insertNth t z)) (basisVec j))
      = ∫ t, (if t ≤ a then v (j.insertNth (2 * a - t) z) else v (j.insertNth t z))
              * (fderiv ℝ φ (j.insertNth t z)) (basisVec j) :=
    integral_congr_ae (Filter.Eventually.of_forall fun t => by simp only [hA t])
  have e2 : (∫ t, (if t ≤ a then (fderiv ℝ v (j.insertNth (2 * a - t) z)) (-basisVec j)
              else (fderiv ℝ v (j.insertNth t z)) (basisVec j)) * φ (j.insertNth t z))
      = ∫ t, faceGrad v a j (j.insertNth t z) j * φ (j.insertNth t z) :=
    integral_congr_ae (by
      filter_upwards [ae_ne_point a] with t ht
      simp only [hB t ht])
  rw [e1, hkey, e2]

/-- **Off-diagonal per-line identity** (reflection direction ≠ differentiation
direction).  The line meets the reflection face at a single tangential value, so
each line is globally `C¹` and integrates by parts with no boundary term. -/
private theorem faceReflect_line_integral_offdiag {v : Vec (n + 1) → ℝ}
    (hv : ContDiff ℝ 1 v) {φ : Vec (n + 1) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (a : ℝ) {i j : Fin (n + 1)} (hji : j ≠ i) (z : Vec n) :
    (∫ t, faceReflect v a i (j.insertNth t z)
          * (fderiv ℝ φ (j.insertNth t z)) (basisVec j))
      = -(∫ t, faceGrad v a i (j.insertNth t z) j * φ (j.insertNth t z)) := by
  have hvd : Differentiable ℝ v := hv.differentiable (by simp)
  have hvf : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by simp)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφf : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hlineDir : Continuous (fun t : ℝ => (j.insertNth t z : Vec (n + 1))) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_insertNth j z t).continuousAt
  have hlineReflIdx :
      Continuous (fun t : ℝ => coordFaceReflection a i (j.insertNth t z)) :=
    (continuous_coordFaceReflection a i).comp hlineDir
  have hφL_deriv : ∀ t, HasDerivAt (fun s => φ (j.insertNth s z))
      ((fderiv ℝ φ (j.insertNth t z)) (basisVec j)) t :=
    fun t => hasDerivAt_comp_insertNth hφd j z t
  have hcφ : Continuous (fun t => (fderiv ℝ φ (j.insertNth t z)) (basisVec j)) :=
    (hφf.comp hlineDir).clm_apply continuous_const
  have hφL_cs : HasCompactSupport (fun t => φ (j.insertNth t z)) :=
    hasCompactSupport_insertNth_line hφc j z
  -- the `i`-th coordinate is constant along the `j`-line
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (show i ≠ j from fun h => hji h.symm)
  have hci : ∀ t, (j.insertNth t z : Vec (n + 1)) i = z k := by
    intro t; rw [← hk, Fin.insertNth_apply_succAbove]
  by_cases hac : a ≤ z k
  · -- direct branch on the whole line
    have hd : ∀ t, HasDerivAt (fun s => v (j.insertNth s z))
        ((fderiv ℝ v (j.insertNth t z)) (basisVec j)) t :=
      fun t => hasDerivAt_comp_insertNth hvd j z t
    have hc : Continuous (fun t => (fderiv ℝ v (j.insertNth t z)) (basisVec j)) :=
      (hvf.comp hlineDir).clm_apply continuous_const
    have hkey := integral_mul_deriv_eq_neg hd hc hφL_deriv hcφ hφL_cs
    have hEv : ∀ t, faceReflect v a i (j.insertNth t z) = v (j.insertNth t z) := by
      intro t; simp only [faceReflect]; rw [hci t, if_pos hac]
    have hGr : ∀ t, faceGrad v a i (j.insertNth t z) j
        = (fderiv ℝ v (j.insertNth t z)) (basisVec j) := by
      intro t; simp only [faceGrad]; rw [hci t, if_pos hac]
    have e1 : (∫ t, faceReflect v a i (j.insertNth t z)
          * (fderiv ℝ φ (j.insertNth t z)) (basisVec j))
        = ∫ t, v (j.insertNth t z) * (fderiv ℝ φ (j.insertNth t z)) (basisVec j) :=
      integral_congr_ae (Filter.Eventually.of_forall fun t => by simp only [hEv t])
    have e2 : (∫ t, (fderiv ℝ v (j.insertNth t z)) (basisVec j) * φ (j.insertNth t z))
        = ∫ t, faceGrad v a i (j.insertNth t z) j * φ (j.insertNth t z) :=
      integral_congr_ae (Filter.Eventually.of_forall fun t => by simp only [hGr t])
    rw [e1, hkey, e2]
  · -- reflected branch on the whole line
    have hd : ∀ t, HasDerivAt (fun s => v (coordFaceReflection a i (j.insertNth s z)))
        ((fderiv ℝ v (coordFaceReflection a i (j.insertNth t z))) (basisVec j)) t :=
      fun t => hasDerivAt_comp_coordFaceReflection_insertNth hvd a hji z t
    have hc : Continuous
        (fun t => (fderiv ℝ v (coordFaceReflection a i (j.insertNth t z))) (basisVec j)) :=
      (hvf.comp hlineReflIdx).clm_apply continuous_const
    have hkey := integral_mul_deriv_eq_neg hd hc hφL_deriv hcφ hφL_cs
    have hEv : ∀ t, faceReflect v a i (j.insertNth t z)
        = v (coordFaceReflection a i (j.insertNth t z)) := by
      intro t; simp only [faceReflect]; rw [hci t, if_neg hac]
    have hGr : ∀ t, faceGrad v a i (j.insertNth t z) j
        = (fderiv ℝ v (coordFaceReflection a i (j.insertNth t z))) (basisVec j) := by
      intro t; simp only [faceGrad]; rw [hci t, if_neg hac, if_neg hji, one_mul]
    have e1 : (∫ t, faceReflect v a i (j.insertNth t z)
          * (fderiv ℝ φ (j.insertNth t z)) (basisVec j))
        = ∫ t, v (coordFaceReflection a i (j.insertNth t z))
                * (fderiv ℝ φ (j.insertNth t z)) (basisVec j) :=
      integral_congr_ae (Filter.Eventually.of_forall fun t => by simp only [hEv t])
    have e2 : (∫ t, (fderiv ℝ v (coordFaceReflection a i (j.insertNth t z))) (basisVec j)
                * φ (j.insertNth t z))
        = ∫ t, faceGrad v a i (j.insertNth t z) j * φ (j.insertNth t z) :=
      integral_congr_ae (Filter.Eventually.of_forall fun t => by simp only [hGr t])
    rw [e1, hkey, e2]

/-- **Single-face weak-gradient transport.**
For `v : Vec (n+1) → ℝ` globally `C¹` with compact support, the even reflection
`faceReflect v a i` across `{x_i = a}` has weak `j`-th partial derivative
`faceGrad v a i · j` on all of `Vec (n+1)`, for every `j`. -/
theorem hasWeakPartialDerivOn_univ_faceReflect {v : Vec (n + 1) → ℝ}
    (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) (a : ℝ) (i j : Fin (n + 1)) :
    HasWeakPartialDerivOn Set.univ j (faceReflect v a i)
      (fun x => faceGrad v a i x j) := by
  intro φ hφ hφc _hφsub
  have hvd : Differentiable ℝ v := hv.differentiable (by simp)
  have hvf : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by simp)
  have hφf : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  -- integrand data
  have hEv_cont : Continuous (faceReflect v a i) := continuous_faceReflect hv.continuous a i
  have hEv_cs : HasCompactSupport (faceReflect v a i) := hasCompactSupport_faceReflect hvc a i
  have hDφ_cont : Continuous (fun x => (fderiv ℝ φ x) (basisVec j)) :=
    hφf.clm_apply continuous_const
  have hDφ_cs : HasCompactSupport (fun x => (fderiv ℝ φ x) (basisVec j)) :=
    hφc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  -- LHS integrand is integrable (continuous, compact support)
  have hF_int : Integrable
      (fun x => faceReflect v a i x * (fderiv ℝ φ x) (basisVec j))
      (volume : Measure (Vec (n + 1))) :=
    (hEv_cont.mul hDφ_cont).integrable_of_hasCompactSupport (hEv_cs.mul_right)
  -- `faceGrad · j` is measurable and bounded
  have hb1_cont : Continuous (fun x => (fderiv ℝ v x) (basisVec j)) :=
    hvf.clm_apply continuous_const
  have hb1_cs : HasCompactSupport (fun x => (fderiv ℝ v x) (basisVec j)) :=
    hvc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  obtain ⟨M, hM0, hMbound⟩ :=
    exists_norm_bound_of_continuous_hasCompactSupport hb1_cont hb1_cs
  have hb2_cont : Continuous
      (fun x => (if j = i then (-1 : ℝ) else 1)
        * (fderiv ℝ v (coordFaceReflection a i x)) (basisVec j)) :=
    continuous_const.mul ((hvf.comp (continuous_coordFaceReflection a i)).clm_apply
      continuous_const)
  have hset : MeasurableSet {x : Vec (n + 1) | a ≤ x i} :=
    measurableSet_le measurable_const (measurable_pi_apply i)
  have hGj_meas : Measurable (fun x => faceGrad v a i x j) :=
    Measurable.ite hset hb1_cont.measurable hb2_cont.measurable
  have hGj_bound : ∀ x, ‖faceGrad v a i x j‖ ≤ M := by
    intro x
    unfold faceGrad
    by_cases h : a ≤ x i
    · rw [if_pos h]; exact hMbound x
    · rw [if_neg h]
      rw [norm_mul]
      by_cases hji : j = i
      · rw [if_pos hji]; simp only [norm_neg, norm_one, one_mul]
        exact hMbound _
      · rw [if_neg hji]; simp only [norm_one, one_mul]
        exact hMbound _
  have hφ_int : Integrable φ (volume : Measure (Vec (n + 1))) :=
    hφ.continuous.integrable_of_hasCompactSupport hφc
  have hG_int : Integrable
      (fun x => faceGrad v a i x j * φ x) (volume : Measure (Vec (n + 1))) :=
    hφ_int.bdd_mul hGj_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall hGj_bound)
  -- peel coordinate `j`, reduce to per-line identities
  rw [MeasureTheory.setIntegral_univ, MeasureTheory.setIntegral_univ,
    integral_peel_coord j hF_int, integral_peel_coord j hG_int, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  by_cases hji : j = i
  · subst hji
    exact faceReflect_line_integral_diag hv hφ hφc a j z
  · exact faceReflect_line_integral_offdiag hv hφ hφc a hji z

end

end Homogenization

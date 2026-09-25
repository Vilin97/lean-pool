/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding.FaceReflectionMain
public import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding.Fold

/-! # Fold Transport -/

@[expose] public section

namespace Homogenization

open Homogenization MeasureTheory
open scoped BigOperators

/-!
# Weak gradient of the fold extension

The extension `x ↦ v (Fold lo hi x)` of a globally `C¹`, compactly supported `v`
has weak `j`-th partial derivative `(∂ⱼv)(Fold x) · foldSignⱼ(x)` on all of
`Vec (n+1)`.  Along a `j`-line only the `j`-th fold varies (two kinks), so the
`d`-dimensional statement reduces to the single-face reflection with two-kink
integration by parts.
-/

noncomputable section

variable {n : ℕ}

/-- **Per-line identity for the fold extension.**  Along the `j`-line the fold
extension integrates by parts across its two kinks with the signed candidate
derivative and no boundary term. -/
private theorem foldComp_line_integral {v : Vec (n + 1) → ℝ}
    (hv : ContDiff ℝ 1 v) {φ : Vec (n + 1) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (lo hi : Vec (n + 1)) (hlohi : ∀ k, lo k ≤ hi k) (j : Fin (n + 1)) (z : Vec n) :
    (∫ t, v (Fold lo hi (j.insertNth t z))
          * (fderiv ℝ φ (j.insertNth t z)) (basisVec j))
      = -(∫ t, ((fderiv ℝ v (Fold lo hi (j.insertNth t z))) (basisVec j)
              * foldSign (lo j) (hi j) ((j.insertNth t z : Vec (n + 1)) j)) * φ (j.insertNth t z)) := by
  have hvd : Differentiable ℝ v := hv.differentiable (by simp)
  have hvf : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by simp)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφf : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  set w : Vec n := fun m => foldR (lo (j.succAbove m)) (hi (j.succAbove m)) (z m) with hw
  -- line continuities
  have hlineDir : Continuous (fun t : ℝ => (j.insertNth t w : Vec (n + 1))) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_insertNth j w t).continuousAt
  have hlineLo : Continuous (fun t : ℝ => (j.insertNth (2 * lo j - t) w : Vec (n + 1))) :=
    continuous_iff_continuousAt.2 fun t =>
      (hasDerivAt_insertNth_reflect (lo j) j w t).continuousAt
  have hlineHi : Continuous (fun t : ℝ => (j.insertNth (2 * hi j - t) w : Vec (n + 1))) :=
    continuous_iff_continuousAt.2 fun t =>
      (hasDerivAt_insertNth_reflect (hi j) j w t).continuousAt
  have hlineφ : Continuous (fun t : ℝ => (j.insertNth t z : Vec (n + 1))) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_insertNth j z t).continuousAt
  -- branch derivatives
  have hd₂ : ∀ t, HasDerivAt (fun s => v (j.insertNth s w))
      ((fderiv ℝ v (j.insertNth t w)) (basisVec j)) t :=
    fun t => hasDerivAt_comp_insertNth hvd j w t
  have hd₁ : ∀ t, HasDerivAt (fun s => v (j.insertNth (2 * lo j - s) w))
      ((fderiv ℝ v (j.insertNth (2 * lo j - t) w)) (-basisVec j)) t :=
    fun t => hasDerivAt_comp_insertNth_reflect hvd (lo j) j w t
  have hd₃ : ∀ t, HasDerivAt (fun s => v (j.insertNth (2 * hi j - s) w))
      ((fderiv ℝ v (j.insertNth (2 * hi j - t) w)) (-basisVec j)) t :=
    fun t => hasDerivAt_comp_insertNth_reflect hvd (hi j) j w t
  have hc₂ : Continuous (fun t => (fderiv ℝ v (j.insertNth t w)) (basisVec j)) :=
    (hvf.comp hlineDir).clm_apply continuous_const
  have hc₁ : Continuous (fun t => (fderiv ℝ v (j.insertNth (2 * lo j - t) w)) (-basisVec j)) :=
    (hvf.comp hlineLo).clm_apply continuous_const
  have hc₃ : Continuous (fun t => (fderiv ℝ v (j.insertNth (2 * hi j - t) w)) (-basisVec j)) :=
    (hvf.comp hlineHi).clm_apply continuous_const
  have hφL_deriv : ∀ t, HasDerivAt (fun s => φ (j.insertNth s z))
      ((fderiv ℝ φ (j.insertNth t z)) (basisVec j)) t :=
    fun t => hasDerivAt_comp_insertNth hφd j z t
  have hcφ : Continuous (fun t => (fderiv ℝ φ (j.insertNth t z)) (basisVec j)) :=
    (hφf.comp hlineφ).clm_apply continuous_const
  have hφL_cs : HasCompactSupport (fun t => φ (j.insertNth t z)) :=
    hasCompactSupport_insertNth_line hφc j z
  -- matching at the two kinks
  have hm₁ : v (j.insertNth (2 * lo j - lo j) w) = v (j.insertNth (lo j) w) := by
    rw [show (2 * lo j - lo j : ℝ) = lo j by ring]
  have hm₂ : v (j.insertNth (hi j) w) = v (j.insertNth (2 * hi j - hi j) w) := by
    rw [show (2 * hi j - hi j : ℝ) = hi j by ring]
  -- two-kink integration by parts
  have hkey := integral_mul_deriv_two_kink_eq_neg (lo j) (hi j) (hlohi j)
    hd₁ hc₁ hd₂ hc₂ hd₃ hc₃ hm₁ hm₂ hφL_deriv hcφ hφL_cs
  -- rewrite the fold extension to the two-kink form on the line
  have hF : ∀ t, v (Fold lo hi (j.insertNth t z))
      = (if t < lo j then v (j.insertNth (2 * lo j - t) w)
          else if hi j < t then v (j.insertNth (2 * hi j - t) w) else v (j.insertNth t w)) := by
    intro t
    rw [Fold_insertNth, ← hw]
    unfold foldR
    by_cases h1 : t < lo j
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : hi j < t
      · rw [if_pos h2, if_pos h2]
      · rw [if_neg h2, if_neg h2]
  -- rewrite the piecewise derivative to the candidate gradient on the line
  have hG : ∀ t,
      (if t < lo j then (fderiv ℝ v (j.insertNth (2 * lo j - t) w)) (-basisVec j)
        else if hi j < t then (fderiv ℝ v (j.insertNth (2 * hi j - t) w)) (-basisVec j)
        else (fderiv ℝ v (j.insertNth t w)) (basisVec j))
      = (fderiv ℝ v (Fold lo hi (j.insertNth t z))) (basisVec j)
          * foldSign (lo j) (hi j) ((j.insertNth t z : Vec (n + 1)) j) := by
    intro t
    rw [Fin.insertNth_apply_same, Fold_insertNth, ← hw]
    unfold foldR foldSign
    by_cases h1 : t < lo j
    · rw [if_pos h1, if_pos h1, if_pos h1, map_neg]; ring
    · rw [if_neg h1, if_neg h1, if_neg h1]
      by_cases h2 : hi j < t
      · rw [if_pos h2, if_pos h2, if_pos h2, map_neg]; ring
      · rw [if_neg h2, if_neg h2, if_neg h2]; ring
  -- assemble
  have e1 : (∫ t, v (Fold lo hi (j.insertNth t z))
        * (fderiv ℝ φ (j.insertNth t z)) (basisVec j))
      = ∫ t, (if t < lo j then v (j.insertNth (2 * lo j - t) w)
                else if hi j < t then v (j.insertNth (2 * hi j - t) w) else v (j.insertNth t w))
              * (fderiv ℝ φ (j.insertNth t z)) (basisVec j) :=
    integral_congr_ae (Filter.Eventually.of_forall fun t => by simp only [hF t])
  have e2 : (∫ t, (if t < lo j then (fderiv ℝ v (j.insertNth (2 * lo j - t) w)) (-basisVec j)
              else if hi j < t then (fderiv ℝ v (j.insertNth (2 * hi j - t) w)) (-basisVec j)
              else (fderiv ℝ v (j.insertNth t w)) (basisVec j)) * φ (j.insertNth t z))
      = ∫ t, ((fderiv ℝ v (Fold lo hi (j.insertNth t z))) (basisVec j)
              * foldSign (lo j) (hi j) ((j.insertNth t z : Vec (n + 1)) j)) * φ (j.insertNth t z) :=
    integral_congr_ae (Filter.Eventually.of_forall fun t => by simp only [hG t])
  rw [e1, hkey, e2]

/-- **Weak-gradient transport for the fold extension.**
For `v : Vec (n+1) → ℝ` globally `C¹` with compact support and a box `[lo, hi]`,
the extension `x ↦ v (Fold lo hi x)` has weak `j`-th partial derivative
`(∂ⱼv)(Fold x) · foldSignⱼ(x)` on all of `Vec (n+1)`, for every `j`. -/
theorem hasWeakPartialDerivOn_univ_foldComp {v : Vec (n + 1) → ℝ}
    (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v)
    (lo hi : Vec (n + 1)) (hlohi : ∀ k, lo k ≤ hi k) (j : Fin (n + 1)) :
    HasWeakPartialDerivOn Set.univ j (fun x => v (Fold lo hi x))
      (fun x => (fderiv ℝ v (Fold lo hi x)) (basisVec j)
        * foldSign (lo j) (hi j) (x j)) := by
  intro φ hφ hφc _hφsub
  have hvf : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by simp)
  have hφf : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hFold_cont : Continuous (Fold lo hi) := continuous_Fold lo hi hlohi
  have hvFold_cont : Continuous (fun x => v (Fold lo hi x)) := hv.continuous.comp hFold_cont
  have hDφ_cont : Continuous (fun x => (fderiv ℝ φ x) (basisVec j)) :=
    hφf.clm_apply continuous_const
  have hDφ_cs : HasCompactSupport (fun x => (fderiv ℝ φ x) (basisVec j)) :=
    hφc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  -- LHS integrable (product with the compactly supported test derivative)
  have hF_int : Integrable
      (fun x => v (Fold lo hi x) * (fderiv ℝ φ x) (basisVec j))
      (volume : Measure (Vec (n + 1))) :=
    (hvFold_cont.mul hDφ_cont).integrable_of_hasCompactSupport hDφ_cs.mul_left
  -- candidate gradient: measurable and bounded
  have hb1_cont : Continuous (fun x => (fderiv ℝ v x) (basisVec j)) :=
    hvf.clm_apply continuous_const
  have hb1_cs : HasCompactSupport (fun x => (fderiv ℝ v x) (basisVec j)) :=
    hvc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  obtain ⟨M, hM0, hMbound⟩ :=
    exists_norm_bound_of_continuous_hasCompactSupport hb1_cont hb1_cs
  have hfst_cont : Continuous (fun x => (fderiv ℝ v (Fold lo hi x)) (basisVec j)) :=
    (hvf.comp hFold_cont).clm_apply continuous_const
  have hsign_meas : Measurable (foldSign (lo j) (hi j)) := by
    unfold foldSign
    refine Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const ?_
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
      measurable_const measurable_const
  have hGj_meas : Measurable (fun x => (fderiv ℝ v (Fold lo hi x)) (basisVec j)
      * foldSign (lo j) (hi j) (x j)) :=
    hfst_cont.measurable.mul (hsign_meas.comp (measurable_pi_apply j))
  have hGj_bound : ∀ x, ‖(fderiv ℝ v (Fold lo hi x)) (basisVec j)
      * foldSign (lo j) (hi j) (x j)‖ ≤ M := by
    intro x
    rw [norm_mul]
    have hsign : ‖foldSign (lo j) (hi j) (x j)‖ ≤ 1 := by
      unfold foldSign
      by_cases h1 : x j < lo j
      · rw [if_pos h1]; simp
      · rw [if_neg h1]; by_cases h2 : hi j < x j
        · rw [if_pos h2]; simp
        · rw [if_neg h2]; simp
    calc ‖(fderiv ℝ v (Fold lo hi x)) (basisVec j)‖ * ‖foldSign (lo j) (hi j) (x j)‖
        ≤ M * 1 := by
          apply mul_le_mul (hMbound _) hsign (norm_nonneg _) hM0
      _ = M := mul_one M
  have hφ_int : Integrable φ (volume : Measure (Vec (n + 1))) :=
    hφ.continuous.integrable_of_hasCompactSupport hφc
  have hG_int : Integrable
      (fun x => ((fderiv ℝ v (Fold lo hi x)) (basisVec j) * foldSign (lo j) (hi j) (x j))
        * φ x) (volume : Measure (Vec (n + 1))) :=
    hφ_int.bdd_mul hGj_meas.aestronglyMeasurable (Filter.Eventually.of_forall hGj_bound)
  -- peel coordinate `j`, reduce to per-line identities
  rw [MeasureTheory.setIntegral_univ, MeasureTheory.setIntegral_univ,
    integral_peel_coord j hF_int, integral_peel_coord j hG_int, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact foldComp_line_integral hv hφ hφc lo hi hlohi j z

end

end Homogenization

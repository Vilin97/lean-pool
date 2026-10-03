/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.Seeley

/-!
# The `C¹` Seeley extension

This file supplies the global differentiability and compact-support interface for the
two-reflection extension.  The derivative is glued across the unit sphere using the
matching identities from `Seeley`.
-/

public section

open Set
open scoped Topology

namespace CKN

noncomputable section

attribute [local instance] Classical.propDecidable

private theorem seeleyC1_annulus_open : IsOpen seeleyAnnulus := by
  rw [seeleyAnnulus]
  have hnorm : Continuous (vecEuclideanNorm (d := 3)) := by
    change Continuous (fun y : Vec 3 => Real.sqrt (vecNormSq y))
    exact (contDiff_vecNormSq (d := 3)).continuous.sqrt
  exact (isOpen_lt continuous_const hnorm).inter
    (isOpen_lt hnorm continuous_const)

/-- Derivative formula for the two-reflection Seeley extension outside the unit ball. -/
def seeleyC1Derivative (v : Vec 3 → ℝ) (x : Vec 3) :
    Vec 3 →L[ℝ] ℝ :=
  (3 : ℝ) • ((fderiv ℝ v (seeleyReflectionOne x)) ∘SL
    (fderiv ℝ seeleyReflectionOne x)) -
    (2 : ℝ) • ((fderiv ℝ v (seeleyReflectionTwo x)) ∘SL
      (fderiv ℝ seeleyReflectionTwo x))

private theorem seeley_norm_contDiffAt_of_ne_zero {x : Vec 3}
    (hx : x ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (vecEuclideanNorm (d := 3)) x := by
  have hq : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Vec 3 => vecNormSq y) x :=
    (contDiff_vecNormSq (d := 3)).contDiffAt
  have hq0 : vecNormSq x ≠ 0 := by
    intro hzero
    exact hx (vecNormSq_eq_zero hzero)
  change ContDiffAt ℝ (⊤ : ℕ∞)
    (fun y : Vec 3 => Real.sqrt (vecNormSq y)) x
  exact hq.sqrt hq0

private theorem seeleyReflectionOne_contDiffAt_of_norm_gt {x : Vec 3}
    (hx : 1 < vecEuclideanNorm x) :
    ContDiffAt ℝ (⊤ : ℕ∞) seeleyReflectionOne x := by
  have hq : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Vec 3 => vecNormSq y) x :=
    (contDiff_vecNormSq (d := 3)).contDiffAt
  have hqpos : 0 < vecNormSq x := by
    rw [← vecEuclideanNorm_sq]
    positivity
  change ContDiffAt ℝ (⊤ : ℕ∞)
    ((fun y : Vec 3 => (vecNormSq y)⁻¹) • fun y : Vec 3 => y) x
  exact hq.inv hqpos.ne' |>.smul contDiffAt_id

private theorem seeleyReflectionTwo_contDiffAt_of_norm_gt {x : Vec 3}
    (hx : 1 < vecEuclideanNorm x) :
    ContDiffAt ℝ (⊤ : ℕ∞) seeleyReflectionTwo x := by
  have hx0 : x ≠ 0 := by
    intro hzero
    have hzero' : vecEuclideanNorm x = 0 := vecEuclideanNorm_eq_zero_iff.mpr hzero
    linarith only [hx, hzero']
  have hnorm := seeley_norm_contDiffAt_of_ne_zero hx0
  have hden : (2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x ≠ 0 := by
    have ht : 0 < vecEuclideanNorm x := by linarith only [hx]
    have hf : 0 < 2 * vecEuclideanNorm x - 1 := by linarith only [hx]
    exact (mul_pos hf ht).ne'
  have hlin : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : Vec 3 => 2 * vecEuclideanNorm y - 1) x := by
    exact (contDiffAt_const.mul hnorm).sub contDiffAt_const
  have hscalar : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : Vec 3 => ((2 * vecEuclideanNorm y - 1) * vecEuclideanNorm y)⁻¹) x := by
    exact hlin.mul hnorm |>.inv hden
  change ContDiffAt ℝ (⊤ : ℕ∞)
    ((fun y : Vec 3 => ((2 * vecEuclideanNorm y - 1) * vecEuclideanNorm y)⁻¹) •
      fun y : Vec 3 => y) x
  exact hscalar.smul contDiffAt_id

private theorem seeley_closedBall_frontier_norm_eq_one {x : Vec 3}
    (hx : x ∈ frontier (euclideanClosedBall (0 : Vec 3) 1)) :
    vecEuclideanNorm x = 1 := by
  have hxC : x ∈ euclideanClosedBall (0 : Vec 3) 1 :=
    (isClosed_euclideanClosedBall (0 : Vec 3) 1).frontier_subset hx
  have hxle : vecEuclideanNorm x ≤ 1 := by
    simpa only [sub_zero] using
      (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)).mp hxC
  have hxnot : x ∉ interior (euclideanClosedBall (0 : Vec 3) 1) := by
    change x ∈ closure (euclideanClosedBall (0 : Vec 3) 1) ∧
      x ∉ interior (euclideanClosedBall (0 : Vec 3) 1) at hx
    exact hx.2
  by_contra hne
  have hlt : vecEuclideanNorm x < 1 := lt_of_le_of_ne hxle hne
  have hopen : IsOpen {y : Vec 3 | vecEuclideanNorm y < 1} := by
    exact isOpen_lt (by
        change Continuous (fun y : Vec 3 => Real.sqrt (vecNormSq y))
        exact (contDiff_vecNormSq (d := 3)).continuous.sqrt) continuous_const
  have hsub : {y : Vec 3 | vecEuclideanNorm y < 1} ⊆
      euclideanClosedBall (0 : Vec 3) 1 := by
    intro y hy
    change vecEuclideanNorm y < 1 at hy
    have hy' : vecEuclideanNorm (y - (0 : Vec 3)) ≤ 1 := by
      simpa only [sub_zero] using hy.le
    exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)).2 hy'
  exact hxnot ((interior_maximal hsub hopen) hlt)

private theorem seeleyExterior_fderiv_eq_c1Derivative
    (v : Vec 3 → ℝ) (hv : ContDiff ℝ 1 v) {x : Vec 3}
    (hx : x ∈ seeleyAnnulus) :
    fderiv ℝ (seeleyExterior v) x = seeleyC1Derivative v x := by
  have hρ1 : ContDiffAt ℝ (⊤ : ℕ∞) seeleyReflectionOne x :=
    seeleyReflectionOne_contDiffOn.contDiffAt (seeleyC1_annulus_open.mem_nhds hx)
  have hρ2 : ContDiffAt ℝ (⊤ : ℕ∞) seeleyReflectionTwo x :=
    seeleyReflectionTwo_contDiffOn.contDiffAt (seeleyC1_annulus_open.mem_nhds hx)
  have h1 := (hv.differentiable_one (seeleyReflectionOne x)).hasFDerivAt.comp x
    (hρ1.differentiableAt (by simp)).hasFDerivAt
  have h2 := (hv.differentiable_one (seeleyReflectionTwo x)).hasFDerivAt.comp x
    (hρ2.differentiableAt (by simp)).hasFDerivAt
  have h := (h1.const_mul 3).sub (h2.const_mul 2)
  have hf := h.fderiv
  have hseeley : seeleyExterior v =
      (fun y => 3 * (v ∘ seeleyReflectionOne) y) -
        (fun y => 2 * (v ∘ seeleyReflectionTwo) y) := by
    funext y
    rfl
  rw [hseeley]
  simpa [seeleyC1Derivative] using hf

private theorem seeleyExterior_hasFDerivAt_of_not_mem
    (v : Vec 3 → ℝ) (hv : ContDiff ℝ 1 v) {x : Vec 3}
    (hx : x ∉ euclideanClosedBall (0 : Vec 3) 1) :
    HasFDerivAt (seeleyExterior v) (seeleyC1Derivative v x) x := by
  have hnorm : 1 < vecEuclideanNorm x := by
    rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)] at hx
    simpa only [sub_zero] using (lt_of_not_ge hx)
  have hρ1 := seeleyReflectionOne_contDiffAt_of_norm_gt hnorm
  have hρ2 := seeleyReflectionTwo_contDiffAt_of_norm_gt hnorm
  have h1 := (hv.differentiable_one (seeleyReflectionOne x)).hasFDerivAt.comp x
    (hρ1.differentiableAt (by simp)).hasFDerivAt
  have h2 := (hv.differentiable_one (seeleyReflectionTwo x)).hasFDerivAt.comp x
    (hρ2.differentiableAt (by simp)).hasFDerivAt
  have h := (h1.const_mul 3).sub (h2.const_mul 2)
  have hseeley : seeleyExterior v =
      (fun y => 3 * (v ∘ seeleyReflectionOne) y) -
        (fun y => 2 * (v ∘ seeleyReflectionTwo) y) := by
    funext y
    rfl
  rw [hseeley]
  simpa [seeleyC1Derivative] using h

private theorem seeleyExterior_hasFDerivAt_on_sphere
    (v : Vec 3 → ℝ) (hv : ContDiff ℝ 1 v) {x : Vec 3}
    (hx : vecEuclideanNorm x = 1) :
    HasFDerivAt (seeleyExterior v) (fderiv ℝ v x) x := by
  have hAnn : x ∈ seeleyAnnulus := by
    exact ⟨by linarith only [hx], by linarith only [hx]⟩
  have hρ1 := seeleyReflectionOne_contDiffOn.contDiffAt
    (seeleyC1_annulus_open.mem_nhds hAnn)
  have hρ2 := seeleyReflectionTwo_contDiffOn.contDiffAt
    (seeleyC1_annulus_open.mem_nhds hAnn)
  have h1 := (hv.differentiable_one (seeleyReflectionOne x)).hasFDerivAt.comp x
    (hρ1.differentiableAt (by simp)).hasFDerivAt
  have h2 := (hv.differentiable_one (seeleyReflectionTwo x)).hasFDerivAt.comp x
    (hρ2.differentiableAt (by simp)).hasFDerivAt
  have he := (h1.const_mul 3).sub (h2.const_mul 2)
  have hseeley : seeleyExterior v =
      (fun y => 3 * (v ∘ seeleyReflectionOne) y) -
        (fun y => 2 * (v ∘ seeleyReflectionTwo) y) := by
    funext y
    rfl
  have hD : HasFDerivAt (seeleyExterior v) (seeleyC1Derivative v x) x := by
    rw [hseeley]
    simpa [seeleyC1Derivative] using he
  have hderivD : fderiv ℝ (seeleyExterior v) x = seeleyC1Derivative v x :=
    seeleyExterior_fderiv_eq_c1Derivative v hv hAnn
  have hderivV : fderiv ℝ (seeleyExterior v) x = fderiv ℝ v x := by
    ext z
    exact seeleyExterior_fderiv_on_sphere v hv hx z
  rw [← hderivV, hderivD]
  exact hD

private theorem seeleyReflectionOne_contDiffAt_of_norm_ge {x : Vec 3}
    (hx : 1 ≤ vecEuclideanNorm x) :
    ContDiffAt ℝ (⊤ : ℕ∞) seeleyReflectionOne x := by
  by_cases heq : vecEuclideanNorm x = 1
  · have hAnn : x ∈ seeleyAnnulus := by
      exact ⟨by linarith only [heq], by linarith only [heq]⟩
    exact seeleyReflectionOne_contDiffOn.contDiffAt
      (seeleyC1_annulus_open.mem_nhds hAnn)
  · exact seeleyReflectionOne_contDiffAt_of_norm_gt
      (lt_of_le_of_ne hx (Ne.symm heq))

private theorem seeleyReflectionTwo_contDiffAt_of_norm_ge {x : Vec 3}
    (hx : 1 ≤ vecEuclideanNorm x) :
    ContDiffAt ℝ (⊤ : ℕ∞) seeleyReflectionTwo x := by
  by_cases heq : vecEuclideanNorm x = 1
  · have hAnn : x ∈ seeleyAnnulus := by
      exact ⟨by linarith only [heq], by linarith only [heq]⟩
    exact seeleyReflectionTwo_contDiffOn.contDiffAt
      (seeleyC1_annulus_open.mem_nhds hAnn)
  · exact seeleyReflectionTwo_contDiffAt_of_norm_gt
      (lt_of_le_of_ne hx (Ne.symm heq))

private theorem seeleyC1Derivative_continuousAt_on_closure_compl
    (v : Vec 3 → ℝ) (hv : ContDiff ℝ 1 v) {x : Vec 3}
    (hx : x ∈ closure (euclideanClosedBall (0 : Vec 3) 1)ᶜ) :
    ContinuousAt (seeleyC1Derivative v) x := by
  have hnorm : 1 ≤ vecEuclideanNorm x := by
    by_cases hxC : x ∈ euclideanClosedBall (0 : Vec 3) 1
    · have hfront : x ∈ frontier (euclideanClosedBall (0 : Vec 3) 1) := by
        rw [frontier_eq_closure_inter_closure]
        exact ⟨subset_closure hxC, hx⟩
      exact (seeley_closedBall_frontier_norm_eq_one hfront).ge
    · rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)] at hxC
      exact (le_of_lt (by simpa only [sub_zero] using (lt_of_not_ge hxC)))
  have hρ1 := seeleyReflectionOne_contDiffAt_of_norm_ge hnorm
  have hρ2 := seeleyReflectionTwo_contDiffAt_of_norm_ge hnorm
  have hvf : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by simp)
  have h1 : ContinuousAt
      (fun y => fderiv ℝ v (seeleyReflectionOne y) ∘SL
        fderiv ℝ seeleyReflectionOne y) x :=
    (hvf.continuousAt.comp hρ1.continuousAt).clm_comp
      (hρ1.continuousAt_fderiv (by simp))
  have h2 : ContinuousAt
      (fun y => fderiv ℝ v (seeleyReflectionTwo y) ∘SL
        fderiv ℝ seeleyReflectionTwo y) x :=
    (hvf.continuousAt.comp hρ2.continuousAt).clm_comp
      (hρ2.continuousAt_fderiv (by simp))
  exact (h1.const_smul (3 : ℝ)).sub (h2.const_smul (2 : ℝ))

theorem seeleyExtension_contDiff (v : Vec 3 → ℝ) (hv : ContDiff ℝ 1 v) :
    ContDiff ℝ 1 (seeleyExtension v) := by
  let D : Vec 3 → Vec 3 →L[ℝ] ℝ := fun x =>
    if x ∈ euclideanClosedBall (0 : Vec 3) 1 then fderiv ℝ v x
    else seeleyC1Derivative v x
  have hDcont : Continuous D := by
    dsimp [D]
    apply continuous_if
    · intro x hx
      have hnorm := seeley_closedBall_frontier_norm_eq_one hx
      have hAnn : x ∈ seeleyAnnulus := by
        exact ⟨by linarith only [hnorm], by linarith only [hnorm]⟩
      have hleft : fderiv ℝ v x = fderiv ℝ (seeleyExterior v) x := by
        ext z
        exact (seeleyExterior_fderiv_on_sphere v hv hnorm z).symm
      exact hleft.trans (seeleyExterior_fderiv_eq_c1Derivative v hv hAnn)
    · exact (hv.continuous_fderiv (by simp)).continuousOn
    · exact fun x hx =>
        (seeleyC1Derivative_continuousAt_on_closure_compl v hv hx).continuousWithinAt
          (s := closure (euclideanClosedBall (0 : Vec 3) 1)ᶜ)
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨D, hDcont, ?_⟩
  intro x
  change HasFDerivAt
    (fun y : Vec 3 => if y ∈ euclideanClosedBall (0 : Vec 3) 1 then v y
      else seeleyExterior v y) (D x) x
  by_cases hxC : x ∈ euclideanClosedBall (0 : Vec 3) 1
  · by_cases hxI : x ∈ interior (euclideanClosedBall (0 : Vec 3) 1)
    · have h := seeley_glue_hasFDerivAt_of_mem_interior
        (C := euclideanClosedBall (0 : Vec 3) 1) (g := v) (h := seeleyExterior v) hxI
        (hv.differentiable_one x).hasFDerivAt
      simpa [D, hxC] using h
    · have hxF : x ∈ frontier (euclideanClosedBall (0 : Vec 3) 1) := by
        rw [frontier]
        exact ⟨subset_closure hxC, hxI⟩
      have hnorm := seeley_closedBall_frontier_norm_eq_one hxF
      have h := seeley_glue_hasFDerivAt
        (isClosed_euclideanClosedBall (0 : Vec 3) 1) hxF
        (by symm; exact seeleyExterior_eq_on_sphere v hnorm)
        (hv.differentiable_one x).hasFDerivAt
        (seeleyExterior_hasFDerivAt_on_sphere v hv hnorm)
      simpa [D, hxC] using h
  · have h := seeley_glue_hasFDerivAt_of_not_mem
      (C := euclideanClosedBall (0 : Vec 3) 1) (g := v) (h := seeleyExterior v)
      (isClosed_euclideanClosedBall (0 : Vec 3) 1) hxC
      (seeleyExterior_hasFDerivAt_of_not_mem v hv hxC)
    simpa [D, hxC] using h

theorem seeleyExtension_eq_on_closedBall {v : Vec 3 → ℝ} {x : Vec 3}
    (hx : x ∈ euclideanClosedBall (0 : Vec 3) 1) :
    seeleyExtension v x = v x := by
  simp [seeleyExtension, hx]

theorem seeleyExtension_fderiv_eq_of_mem_closedBall
    (v : Vec 3 → ℝ) (hv : ContDiff ℝ 1 v) {x : Vec 3}
    (hx : x ∈ euclideanClosedBall (0 : Vec 3) 1) :
    fderiv ℝ (seeleyExtension v) x = fderiv ℝ v x := by
  by_cases hxI : x ∈ interior (euclideanClosedBall (0 : Vec 3) 1)
  · unfold seeleyExtension
    have h := seeley_glue_hasFDerivAt_of_mem_interior
      (C := euclideanClosedBall (0 : Vec 3) 1) (g := v) (h := seeleyExterior v) hxI
      (hv.differentiable_one x).hasFDerivAt
    exact h.fderiv
  · have hxF : x ∈ frontier (euclideanClosedBall (0 : Vec 3) 1) := by
      rw [frontier]
      exact ⟨subset_closure hx, hxI⟩
    have hnorm := seeley_closedBall_frontier_norm_eq_one hxF
    have hvalue : v x = seeleyExterior v x := by
      symm
      exact seeleyExterior_eq_on_sphere v hnorm
    have hAnn : x ∈ seeleyAnnulus := by
      exact ⟨by linarith only [hnorm], by linarith only [hnorm]⟩
    have hρ1 : ContDiffAt ℝ (⊤ : ℕ∞) seeleyReflectionOne x :=
      seeleyReflectionOne_contDiffOn.contDiffAt (seeleyC1_annulus_open.mem_nhds hAnn)
    have hρ2 : ContDiffAt ℝ (⊤ : ℕ∞) seeleyReflectionTwo x :=
      seeleyReflectionTwo_contDiffOn.contDiffAt (seeleyC1_annulus_open.mem_nhds hAnn)
    have h1 := (hv.differentiable_one (seeleyReflectionOne x)).hasFDerivAt.comp x
      (hρ1.differentiableAt (by simp)).hasFDerivAt
    have h2 := (hv.differentiable_one (seeleyReflectionTwo x)).hasFDerivAt.comp x
      (hρ2.differentiableAt (by simp)).hasFDerivAt
    have he := (h1.const_mul 3).sub (h2.const_mul 2)
    have hseeley : seeleyExterior v =
        (fun y => 3 * (v ∘ seeleyReflectionOne) y) -
          (fun y => 2 * (v ∘ seeleyReflectionTwo) y) := by
      funext y
      rfl
    have he' : HasFDerivAt (seeleyExterior v) (fderiv ℝ v x) x := by
      have hD : HasFDerivAt (seeleyExterior v) (seeleyC1Derivative v x) x := by
        rw [hseeley]
        simpa [seeleyC1Derivative] using he
      have hderivD : fderiv ℝ (seeleyExterior v) x = seeleyC1Derivative v x :=
        seeleyExterior_fderiv_eq_c1Derivative v hv hAnn
      have hderivV : fderiv ℝ (seeleyExterior v) x = fderiv ℝ v x := by
        ext z
        exact seeleyExterior_fderiv_on_sphere v hv hnorm z
      rw [← hderivV, hderivD]
      exact hD
    unfold seeleyExtension
    exact (seeley_glue_hasFDerivAt
      (isClosed_euclideanClosedBall (0 : Vec 3) 1) hxF hvalue
      (hv.differentiable_one x).hasFDerivAt he').fderiv

theorem seeleyExtension_classicalGradient_eq_of_mem_closedBall
    (v : Vec 3 → ℝ) (hv : ContDiff ℝ 1 v) {x : Vec 3}
    (hx : x ∈ euclideanClosedBall (0 : Vec 3) 1) :
    classicalGradient (seeleyExtension v) x = classicalGradient v x := by
  funext i
  rw [classicalGradient_apply, classicalGradient_apply,
    seeleyExtension_fderiv_eq_of_mem_closedBall v hv hx]

theorem seeleyExtension_fderiv_eq_reflection_combo_of_mem_annulus
    (v : Vec 3 → ℝ) (hv : ContDiff ℝ 1 v) {x : Vec 3}
    (hx : 1 < vecEuclideanNorm x ∧ vecEuclideanNorm x < 2) :
    fderiv ℝ (seeleyExtension v) x =
      (3 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionOne) x -
        (2 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionTwo) x := by
  have hAnn : x ∈ seeleyAnnulus := by
    exact ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
  have hρ1 := seeleyReflectionOne_contDiffOn.contDiffAt
    (seeleyC1_annulus_open.mem_nhds hAnn)
  have hρ2 := seeleyReflectionTwo_contDiffOn.contDiffAt
    (seeleyC1_annulus_open.mem_nhds hAnn)
  have h1 := (hv.differentiable_one (seeleyReflectionOne x)).hasFDerivAt.comp x
    (hρ1.differentiableAt (by simp)).hasFDerivAt
  have h2 := (hv.differentiable_one (seeleyReflectionTwo x)).hasFDerivAt.comp x
    (hρ2.differentiableAt (by simp)).hasFDerivAt
  have h := (h1.const_mul 3).sub (h2.const_mul 2)
  have h1d : fderiv ℝ (v ∘ seeleyReflectionOne) x =
      fderiv ℝ v (seeleyReflectionOne x) ∘SL fderiv ℝ seeleyReflectionOne x :=
    h1.fderiv
  have h2d : fderiv ℝ (v ∘ seeleyReflectionTwo) x =
      fderiv ℝ v (seeleyReflectionTwo x) ∘SL fderiv ℝ seeleyReflectionTwo x :=
    h2.fderiv
  have hseeley : seeleyExterior v =
      (fun y => 3 * (v ∘ seeleyReflectionOne) y) -
        (fun y => 2 * (v ∘ seeleyReflectionTwo) y) := by
    funext y
    rfl
  have houtside : x ∉ euclideanClosedBall (0 : Vec 3) 1 := by
    intro hxC
    have hnorm := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
      (by norm_num)).mp hxC
    have hnorm' : vecEuclideanNorm x ≤ 1 := by
      simpa only [sub_zero] using hnorm
    linarith only [hx.1, hnorm']
  have hformula : HasFDerivAt (seeleyExterior v)
      ((3 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionOne) x -
        (2 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionTwo) x) x := by
    rw [hseeley]
    simpa only [h1d, h2d] using h
  have hext : HasFDerivAt (seeleyExtension v)
      ((3 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionOne) x -
        (2 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionTwo) x) x := by
    unfold seeleyExtension
    exact seeley_glue_hasFDerivAt_of_not_mem
      (isClosed_euclideanClosedBall (0 : Vec 3) 1) houtside hformula
  exact hext.fderiv

/-- Seeley extension multiplied by a compactly supported spatial cutoff. -/
@[expose] def seeleyCutoffExtension (v : Vec 3 → ℝ) : Vec 3 → ℝ :=
  canonicalBallCutoff (0 : Vec 3) 1 2 * seeleyExtension v

end
end CKN

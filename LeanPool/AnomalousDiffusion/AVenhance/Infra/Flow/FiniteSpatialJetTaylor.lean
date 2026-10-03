/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FiniteSpatialJet
public import Mathlib.Analysis.Calculus.MeanValue

/-! Compact-window Taylor control for the recursive augmented fields. -/

@[expose] public section

open Homogenization
open Set
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

noncomputable section

theorem spatialJetField_fderiv_eq_joint
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) (n : ℕ)
    (t : ℝ) (z : SpatialJetState n) :
    fderiv ℝ (spatialJetField b n t) z =
      (fderiv ℝ (Function.uncurry (spatialJetField b n)) (t, z)).comp
        (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n)) := by
  have hF : Differentiable ℝ (Function.uncurry (spatialJetField b n)) :=
    (spatialJetField_smooth hb n).differentiable (by norm_num)
  have htotal := (hF (t, z)).hasFDerivAt.comp z (hasFDerivAt_prodMk_right t z)
  have hslice : HasFDerivAt (spatialJetField b n t)
      ((fderiv ℝ (Function.uncurry (spatialJetField b n)) (t, z)).comp
        (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n))) z := by
    change HasFDerivAt (fun w => Function.uncurry (spatialJetField b n) (t, w)) _ _
    exact htotal
  exact hslice.fderiv

/-- The state derivative of an augmented field is uniformly bounded on a
compact time window and a bounded state ball. -/
theorem spatialJetField_fderiv_bound_on_window
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    (n : ℕ) (a d R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, t ∈ Icc a d →
      ∀ z : SpatialJetState n, ‖z‖ ≤ R →
        ‖fderiv ℝ (spatialJetField b n t) z‖ ≤ M := by
  let F : ℝ × SpatialJetState n → SpatialJetState n :=
    Function.uncurry (spatialJetField b n)
  have hF : ContDiff ℝ ∞ F := spatialJetField_smooth hb n
  let J : ℝ × SpatialJetState n →
      SpatialJetState n →L[ℝ] SpatialJetState n := fun p =>
    (fderiv ℝ F p).comp
      (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n))
  have hJ : ContDiff ℝ ∞ J := by
    exact (hF.fderiv_right (by norm_num)).clm_comp contDiff_const
  have hJcont : Continuous J := hJ.continuous
  have hnorm : Continuous (fun p : ℝ × SpatialJetState n => ‖J p‖) :=
    Continuous.norm (f := J) hJcont
  let region : Set (ℝ × SpatialJetState n) :=
    Icc a d ×ˢ Metric.closedBall (0 : SpatialJetState n) R
  have hcompact : IsCompact region := by
    exact isCompact_Icc.prod (isCompact_closedBall 0 R)
  have hbounded : BddAbove ((fun p => ‖J p‖) '' region) :=
    hcompact.bddAbove_image hnorm.continuousOn
  let M : ℝ := max (sSup ((fun p => ‖J p‖) '' region)) 0
  refine ⟨M, le_max_right _ _, ?_⟩
  intro t ht z hz
  have hmem : ‖J (t, z)‖ ∈ (fun p => ‖J p‖) '' region := by
    refine ⟨(t, z), ⟨ht, ?_⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hz
  have hsup := le_csSup hbounded hmem
  have hJ_eq : J (t, z) = fderiv ℝ (spatialJetField b n t) z := by
    dsimp [J, F]
    exact (spatialJetField_fderiv_eq_joint hb n t z).symm
  rw [← hJ_eq]
  exact le_trans hsup (le_max_left _ _)

/-- On a compact time window and a bounded state ball, the nonlinear part of
the first-order Taylor expansion of any recursive jet field is quadratically
bounded. -/
theorem spatialJetField_taylor_remainder_on_window
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    (n : ℕ) (a d R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, t ∈ Icc a d →
      ∀ x y : SpatialJetState n, ‖x‖ ≤ R → ‖y‖ ≤ R →
        ‖spatialJetField b n t y - spatialJetField b n t x -
          fderiv ℝ (spatialJetField b n t) x (y - x)‖ ≤
            C * ‖y - x‖ * ‖y - x‖ := by
  let F : ℝ × SpatialJetState n → SpatialJetState n :=
    Function.uncurry (spatialJetField b n)
  have hF : ContDiff ℝ ∞ F := spatialJetField_smooth hb n
  let J : ℝ × SpatialJetState n →
      SpatialJetState n →L[ℝ] SpatialJetState n := fun p =>
    (fderiv ℝ F p).comp
      (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n))
  have hJ : ContDiff ℝ ∞ J := by
    exact (hF.fderiv_right (by norm_num)).clm_comp contDiff_const
  have hDJ : Continuous (fun p : ℝ × SpatialJetState n => fderiv ℝ J p) :=
    hJ.continuous_fderiv (by norm_num)
  let region : Set (ℝ × SpatialJetState n) :=
    Icc a d ×ˢ Metric.closedBall (0 : SpatialJetState n) (3 * R)
  have hcompact : IsCompact region := by
    exact isCompact_Icc.prod (isCompact_closedBall 0 (3 * R))
  have hnorm : Continuous (fun p : ℝ × SpatialJetState n => ‖fderiv ℝ J p‖) :=
    Continuous.norm (f := fun p : ℝ × SpatialJetState n => fderiv ℝ J p) hDJ
  have hbounded : BddAbove ((fun p => ‖fderiv ℝ J p‖) '' region) :=
    hcompact.bddAbove_image hnorm.continuousOn
  let C : ℝ := max (sSup ((fun p => ‖fderiv ℝ J p‖) '' region)) 0
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC (t : ℝ) (ht : t ∈ Icc a d) (z : SpatialJetState n)
      (hz : ‖z‖ ≤ 3 * R) : ‖fderiv ℝ J (t, z)‖ ≤ C := by
    apply le_trans (le_csSup hbounded ?_)
    · exact le_max_left _ _
    · refine ⟨(t, z), ⟨ht, ?_⟩, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hz
  refine ⟨C, hC0, ?_⟩
  intro t ht x y hx hy
  let g : SpatialJetState n → SpatialJetState n := spatialJetField b n t
  let A : SpatialJetState n → SpatialJetState n →L[ℝ] SpatialJetState n :=
    fun z => fderiv ℝ g z
  have hg : ContDiff ℝ ∞ g := by
    have hmap : ContDiff ℝ ∞ (fun z : SpatialJetState n => (t, z)) := by
      exact contDiff_const.prodMk contDiff_id
    exact hF.comp hmap
  have hAeq (z : SpatialJetState n) : A z = J (t, z) := by
    dsimp [A, J, g, F]
    rw [spatialJetField_fderiv_eq_joint hb n t z]
  have hA : ContDiff ℝ ∞ A := by
    have hmap : ContDiff ℝ ∞ (fun z : SpatialJetState n => (t, z)) := by fun_prop
    have hA' : ContDiff ℝ ∞ (fun z : SpatialJetState n => J (t, z)) :=
      hJ.comp hmap
    have hEq : A = fun z => J (t, z) := by
      funext z
      exact hAeq z
    rw [hEq]
    exact hA'
  have hdf : Differentiable ℝ A := hA.differentiable (by norm_num)
  let big : Set (SpatialJetState n) := Metric.closedBall 0 (3 * R)
  have hbig : Convex ℝ big := convex_closedBall _ _
  have hxBig : x ∈ big := by
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖x‖ ≤ R := hx
      _ ≤ 3 * R := by
        calc
          R = 1 * R := by ring
          _ ≤ 3 * R := mul_le_mul_of_nonneg_right
            (by norm_num : (1 : ℝ) ≤ 3) hR
  have hyBig : y ∈ big := by
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖y‖ ≤ R := hy
      _ ≤ 3 * R := by
        calc
          R = 1 * R := by ring
          _ ≤ 3 * R := mul_le_mul_of_nonneg_right
            (by norm_num : (1 : ℝ) ≤ 3) hR
  have hDAbound (z : SpatialJetState n) (hz : z ∈ big) :
      ‖fderiv ℝ A z‖ ≤ C := by
    have hz' : ‖z‖ ≤ 3 * R := by
      simpa [big, Metric.mem_closedBall, dist_zero_right] using hz
    have hslice : HasFDerivAt A
        ((fderiv ℝ J (t, z)).comp
          (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n))) z := by
      have hparam : HasFDerivAt (fun w : SpatialJetState n => (t, w))
          (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n)) z :=
        hasFDerivAt_prodMk_right t z
      have hEq : (fun w => A w) = fun w => J (t, w) := by
        funext w
        exact hAeq w
      have hJtotal := (hJ.differentiable (by norm_num) (t, z)).hasFDerivAt
      have hJcomp := hJtotal.comp z hparam
      exact hJcomp.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun w => congrFun hEq w)
    rw [hslice.fderiv]
    calc
      ‖(fderiv ℝ J (t, z)).comp
          (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n))‖ ≤
          ‖fderiv ℝ J (t, z)‖ *
            ‖ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n)‖ :=
        (fderiv ℝ J (t, z)).opNorm_comp_le _
      _ = ‖fderiv ℝ J (t, z)‖ := by
        rw [ContinuousLinearMap.norm_inr, mul_one]
      _ ≤ C := hC t ht z hz'
  have hLip : ∀ z ∈ big, ‖A z - A x‖ ≤ C * ‖z - x‖ := by
    intro z hz
    exact hbig.norm_image_sub_le_of_norm_fderiv_le
      (fun w _ => hdf w) hDAbound hxBig hz
  let S : Set (SpatialJetState n) := Metric.closedBall x ‖y - x‖
  have hS : Convex ℝ S := convex_closedBall _ _
  have hxS : x ∈ S := by simp [S, Metric.mem_closedBall]
  have hyS : y ∈ S := by
    simp [S, Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
  have hdisp : ‖y - x‖ ≤ 2 * R := by
    calc
      ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add hy hx
      _ = 2 * R := by ring
  have hSsub : S ⊆ big := by
    intro z hz
    have hzdist : ‖z - x‖ ≤ ‖y - x‖ := by
      simpa [S, Metric.mem_closedBall, dist_eq_norm] using hz
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖z‖ ≤ ‖z - x‖ + ‖x‖ := norm_le_norm_sub_add _ _
      _ ≤ ‖y - x‖ + R := add_le_add hzdist hx
      _ ≤ 2 * R + R := by gcongr
      _ = 3 * R := by ring
  have hLipOn : ∀ z ∈ S, ‖A z - A x‖ ≤ (C * ‖y - x‖) := by
    intro z hz
    have hzdist : ‖z - x‖ ≤ ‖y - x‖ := by
      simpa [S, Metric.mem_closedBall, dist_eq_norm] using hz
    exact (hLip z (hSsub hz)).trans
      (mul_le_mul_of_nonneg_left hzdist hC0)
  have hTaylor := hS.norm_image_sub_le_of_norm_fderiv_le'
    (f := g) (φ := A x)
    (fun z _ => hg.differentiable (by norm_num) z) hLipOn hxS hyS
  simpa [g, A, mul_assoc, mul_comm, mul_left_comm] using hTaylor

end

end AVenhance.Infra.Flow

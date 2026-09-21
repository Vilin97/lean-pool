/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.SmoothLimit

/-! # Smooth Pointwise -/

namespace Homogenization

open scoped Interval Manifold

noncomputable section

/-!
# Pointwise smooth backward-quotient convergence

This shard isolates the classical smooth estimate used by the C.2 limit
handoff: if a coordinate derivative has a global Lipschitz bound, then the
backward difference quotient converges pointwise at rate `O(|h|)`.
-/

private theorem norm_basisVec {d : ℕ} (i : Fin d) : ‖basisVec i‖ = (1 : ℝ) := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).2 ?_
    intro j
    by_cases hji : j = i
    · subst hji
      simp [basisVec]
    · simp [basisVec, hji]
  · have hi : ‖basisVec i i‖ ≤ ‖basisVec i‖ := norm_le_pi_norm (basisVec i) i
    simpa [basisVec] using hi

private theorem norm_sub_euclideanCoordShift_neg {d : ℕ}
    (h : ℝ) (i : Fin d) (x : Vec d) :
    ‖x - euclideanCoordShift (-h) i x‖ = ‖h‖ := by
  have hx : x - euclideanCoordShift (-h) i x = h • basisVec i := by
    ext j
    by_cases hji : j = i
    · subst hji
      simp [euclideanCoordShift, basisVec]
    · simp [euclideanCoordShift, basisVec, hji]
  rw [hx, norm_smul, norm_basisVec i, mul_one]

private theorem norm_segmentBlend_sub_left_euclideanCoordShift_neg_le {d : ℕ}
    (h : ℝ) (i : Fin d) (x : Vec d) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖segmentBlend x t (euclideanCoordShift (-h) i x) - x‖ ≤ ‖h‖ := by
  have hseg :
      ‖x - segmentBlend x t (euclideanCoordShift (-h) i x)‖ =
        |1 - t| * ‖x - euclideanCoordShift (-h) i x‖ :=
    norm_left_sub_segmentBlend x (euclideanCoordShift (-h) i x) t
  have ht_abs : |1 - t| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  calc
    ‖segmentBlend x t (euclideanCoordShift (-h) i x) - x‖ =
        ‖x - segmentBlend x t (euclideanCoordShift (-h) i x)‖ := by
          rw [norm_sub_rev]
    _ = |1 - t| * ‖x - euclideanCoordShift (-h) i x‖ := hseg
    _ ≤ 1 * ‖x - euclideanCoordShift (-h) i x‖ := by
      exact mul_le_mul_of_nonneg_right ht_abs (norm_nonneg _)
    _ = ‖h‖ := by rw [one_mul, norm_sub_euclideanCoordShift_neg]

private theorem continuous_segmentBlend_left {d : ℕ} (x y : Vec d) :
    Continuous (fun t : ℝ => segmentBlend x t y) := by
  have hcont : Continuous (fun t : ℝ => y + t • (x - y)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  convert hcont using 1
  funext t
  rw [segmentBlend_eq_add_smul_sub]

/-- A global Lipschitz bound on the coordinate derivative gives a pointwise
`O(|h|)` estimate for the backward difference quotient. -/
theorem euclideanBackwardDifferenceQuotient_sub_coordDeriv_le_of_coordDeriv_lipschitz
    {d : ℕ} {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {h : ℝ} (hh : h ≠ 0) (i : Fin d) {C : ℝ} (hC : 0 ≤ C)
    (hLip : ∀ z x : Vec d,
      ‖euclideanCoordDeriv i u z - euclideanCoordDeriv i u x‖ ≤ C * ‖z - x‖)
    (x : Vec d) :
    ‖euclideanBackwardDifferenceQuotient h i u x - euclideanCoordDeriv i u x‖ ≤
      C * ‖h‖ := by
  let Dg : Vec d → ℝ := fun z => euclideanCoordDeriv i u z
  let y : Vec d := euclideanCoordShift (-h) i x
  have hDQ :
      euclideanBackwardDifferenceQuotient h i u x =
        ∫ t in (0 : ℝ)..1, Dg (segmentBlend x t y) := by
    simpa [Dg, y] using
      euclideanBackwardDifferenceQuotient_eq_integral_coordDeriv_along_segment hu hh i x
  have hD_cont : Continuous Dg := by
    simpa [Dg] using (contDiff_euclideanCoordDeriv hu i).continuous
  have hseg_cont : Continuous (fun t : ℝ => segmentBlend x t y) :=
    continuous_segmentBlend_left x y
  have hcomp_cont : Continuous (fun t : ℝ => Dg (segmentBlend x t y)) :=
    hD_cont.comp hseg_cont
  have hcomp_int :
      IntervalIntegrable (fun t : ℝ => Dg (segmentBlend x t y))
        MeasureTheory.volume (0 : ℝ) 1 :=
    hcomp_cont.intervalIntegrable 0 1
  have hconst_int :
      IntervalIntegrable (fun _ : ℝ => Dg x) MeasureTheory.volume (0 : ℝ) 1 :=
    continuous_const.intervalIntegrable 0 1
  have hdiff_eq :
      euclideanBackwardDifferenceQuotient h i u x - Dg x =
        ∫ t in (0 : ℝ)..1, (Dg (segmentBlend x t y) - Dg x) := by
    rw [hDQ, intervalIntegral.integral_sub hcomp_int hconst_int]
    simp
  have hnorm_cont :
      Continuous (fun t : ℝ => ‖Dg (segmentBlend x t y) - Dg x‖) :=
    (hcomp_cont.sub continuous_const).norm
  have hnorm_int :
      IntervalIntegrable (fun t : ℝ => ‖Dg (segmentBlend x t y) - Dg x‖)
        MeasureTheory.volume (0 : ℝ) 1 :=
    hnorm_cont.intervalIntegrable 0 1
  have hbound_int :
      IntervalIntegrable (fun _ : ℝ => C * ‖h‖) MeasureTheory.volume (0 : ℝ) 1 :=
    continuous_const.intervalIntegrable 0 1
  calc
    ‖euclideanBackwardDifferenceQuotient h i u x - Dg x‖ =
        ‖∫ t in (0 : ℝ)..1, (Dg (segmentBlend x t y) - Dg x)‖ := by
          rw [hdiff_eq]
    _ ≤ ∫ t in (0 : ℝ)..1, ‖Dg (segmentBlend x t y) - Dg x‖ :=
      intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ _t in (0 : ℝ)..1, C * ‖h‖ := by
      apply intervalIntegral.integral_mono_on zero_le_one hnorm_int hbound_int
      intro t ht
      have hseg : ‖segmentBlend x t y - x‖ ≤ ‖h‖ := by
        simpa [y] using norm_segmentBlend_sub_left_euclideanCoordShift_neg_le h i x ht
      exact (hLip (segmentBlend x t y) x).trans
        (mul_le_mul_of_nonneg_left hseg hC)
    _ = C * ‖h‖ := by simp

/-- A global Fréchet-derivative bound on a coordinate derivative gives the
corresponding global Lipschitz bound. -/
theorem euclideanCoordDeriv_lipschitz_of_fderiv_bound
    {d : ℕ} {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (i : Fin d) {C : ℝ}
    (hbound : ∀ x : Vec d, ‖fderiv ℝ (fun z => euclideanCoordDeriv i u z) x‖ ≤ C) :
    ∀ z x : Vec d,
      ‖euclideanCoordDeriv i u z - euclideanCoordDeriv i u x‖ ≤ C * ‖z - x‖ := by
  intro z x
  simpa using
    (Convex.norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ) (f := fun z => euclideanCoordDeriv i u z)
      (s := Set.univ) (C := C) (x := x) (y := z)
      (fun y _ => (contDiff_euclideanCoordDeriv hu i).differentiable (by simp) y)
      (fun y _ => hbound y) convex_univ trivial trivial)

/-- Smooth backward quotients converge pointwise at rate `O(|h|)` when the
Fréchet derivative of the coordinate derivative is globally bounded. -/
theorem euclideanBackwardDifferenceQuotient_sub_coordDeriv_le_of_fderiv_bound
    {d : ℕ} {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {h : ℝ} (hh : h ≠ 0) (i : Fin d) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x : Vec d, ‖fderiv ℝ (fun z => euclideanCoordDeriv i u z) x‖ ≤ C)
    (x : Vec d) :
    ‖euclideanBackwardDifferenceQuotient h i u x - euclideanCoordDeriv i u x‖ ≤
      C * ‖h‖ :=
  euclideanBackwardDifferenceQuotient_sub_coordDeriv_le_of_coordDeriv_lipschitz
    hu hh i hC (euclideanCoordDeriv_lipschitz_of_fderiv_bound hu i hbound) x

theorem exists_bound_fderiv_euclideanCoordDeriv_of_contDiff_hasCompactSupport
    {d : ℕ} {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hu_compact : HasCompactSupport u) (i : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : Vec d, ‖fderiv ℝ (fun z => euclideanCoordDeriv i u z) x‖ ≤ C := by
  exact exists_bound_fderiv_of_contDiff_hasCompactSupport
    (contDiff_euclideanCoordDeriv hu i)
    (hasCompactSupport_euclideanCoordDeriv hu_compact i)

private theorem contDiff_h1WeakTest_deriv
    {d : ℕ} {U : Set (Vec d)} (φ : H1WeakTestFunction U) (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => φ.deriv j x) := by
  simpa [H1WeakTestFunction.deriv, euclideanCoordDeriv] using!
    contDiff_euclideanCoordDeriv φ.smooth j

private theorem hasCompactSupport_h1WeakTest_deriv
    {d : ℕ} {U : Set (Vec d)} (φ : H1WeakTestFunction U) (j : Fin d) :
    HasCompactSupport (fun x => φ.deriv j x) := by
  simpa [H1WeakTestFunction.deriv] using
    φ.compactSupport.fderiv_apply (𝕜 := ℝ) (basisVec j)

/-- Smooth compactly supported weak tests have a global pointwise
`O(|h|)` backward-quotient estimate for each Hessian coordinate. -/
theorem exists_backwardDifferenceQuotient_h1WeakTest_deriv_pointwise_bound
    {d : ℕ} {U : Set (Vec d)} (φ : H1WeakTestFunction U) (i j : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ h : ℝ, h ≠ 0 →
        ∀ x : Vec d,
          ‖euclideanBackwardDifferenceQuotient h i (fun y => φ.deriv j y) x -
              (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i)‖ ≤ C * ‖h‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_bound_fderiv_euclideanCoordDeriv_of_contDiff_hasCompactSupport
      (contDiff_h1WeakTest_deriv φ j)
      (hasCompactSupport_h1WeakTest_deriv φ j) i
  refine ⟨C, hC, ?_⟩
  intro h hh x
  simpa [euclideanCoordDeriv] using
    euclideanBackwardDifferenceQuotient_sub_coordDeriv_le_of_fderiv_bound
      (contDiff_h1WeakTest_deriv φ j) hh i hC hbound x

namespace WeakPoissonEquationOn

variable {d : ℕ} {V : Set (Vec d)}

/-- The smooth pointwise estimate closes the `SmoothLimit` hypothesis whenever
the quotient step sequence is nonzero and tends to zero. -/
theorem openCubeInnerHessianPairingTendsto_of_smooth_pointwise_bound
    {Q : TriadicCube d} (uQ : H1Function (openCubeSet Q))
    (stepSeq : ℕ → ℝ) (i j : Fin d) {ρ₁ : ℝ}
    (hSV : scaledOpenCubeSet Q ρ₁ ⊆ V)
    (hVU : V ⊆ openCubeSet Q)
    (hVshift : ∀ n, ∀ x ∈ V,
      euclideanCoordShift (stepSeq n) i x ∈ openCubeSet Q)
    (hstep_tendsto : Filter.Tendsto stepSeq Filter.atTop (nhds 0))
    (hstep_ne : ∀ n, stepSeq n ≠ 0) :
    OpenCubeInnerHessianPairingTendsto (ρ₁ := ρ₁) uQ V stepSeq i j := by
  refine
    openCubeInnerHessianPairingTendsto_of_backwardDifferenceQuotient_deriv_pointwise_bound
      uQ stepSeq i j hSV hVU hVshift hstep_tendsto ?_
  intro φ
  obtain ⟨C, _hC, hCbound⟩ :=
    exists_backwardDifferenceQuotient_h1WeakTest_deriv_pointwise_bound φ i j
  refine ⟨C, fun n => ?_⟩
  exact Filter.Eventually.of_forall fun x => hCbound (stepSeq n) (hstep_ne n) x

/-- Standard closed-cube geometry supplies the domain-shift hypotheses needed
by `openCubeInnerHessianPairingTendsto_of_smooth_pointwise_bound`. -/
theorem openCubeInnerHessianPairingTendsto_of_smooth_pointwise_bound_of_step_abs
    {Q : TriadicCube d} (uQ : H1Function (openCubeSet Q))
    (V : Set (Vec d)) (stepSeq : ℕ → ℝ) (i j : Fin d)
    {ρ₁ σ₁ ν : ℝ}
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν ≤ σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hstep_abs : ∀ n, |stepSeq n| ≤ (σ₁ - ν) * cubeRadius Q)
    (hstep_tendsto : Filter.Tendsto stepSeq Filter.atTop (nhds 0))
    (hstep_ne : ∀ n, stepSeq n ≠ 0) :
    OpenCubeInnerHessianPairingTendsto (ρ₁ := ρ₁) uQ V stepSeq i j := by
  have hSV : scaledOpenCubeSet Q ρ₁ ⊆ V :=
    (scaledOpenCubeSet_subset_scaledClosedCubeSet Q ρ₁).trans hinnerV
  have hσ₁_nonneg : 0 ≤ σ₁ := hν_nonneg.trans hνσ
  have hVU : V ⊆ openCubeSet Q := by
    intro x hx
    exact
      scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one
        Q hν_nonneg (lt_of_le_of_lt hνσ hσ₁_lt_one) (hVν hx)
  have hVshift : ∀ n, ∀ x ∈ V,
      euclideanCoordShift (stepSeq n) i x ∈ openCubeSet Q := by
    intro n x hx
    have hxν : x ∈ scaledClosedCubeSet Q ν := hVν hx
    have hxσ₁ :
        euclideanCoordShift (stepSeq n) i x ∈ scaledClosedCubeSet Q σ₁ :=
      euclideanCoordShift_mem_scaledClosedCubeSet_of_mem_scaledClosedCubeSet
        Q hνσ (hstep_abs n) i hxν
    exact
      scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one
        Q hσ₁_nonneg hσ₁_lt_one hxσ₁
  exact
    openCubeInnerHessianPairingTendsto_of_smooth_pointwise_bound
      uQ stepSeq i j hSV hVU hVshift hstep_tendsto hstep_ne

end WeakPoissonEquationOn

end

end Homogenization

/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.QuadraticContinuation
public import LeanPool.CarlsonFunctions.Carlson.R.SlitJointAnalytic

/-!
# Quadratic transformations with slit-plane transformed nodes

Both regularized transformations hold for all complex parameters whenever the
unsquared variables `x,y` have positive real parts. Their squares, product, and
squared arithmetic mean need only lie in the slit plane; they need not have
positive real parts. Thus this extends the node domains of the earlier native
and parameter-continued formulas in Carlson 1977, §§6.9–6.10.

The proof uses joint node holomorphy and agreement near `(1,1)`. It does not
claim every component of the algebraic preimage of the slit plane: branches
on larger domains still require separate analysis. The finer equal-parameter
normalization and its L-function transformations are not extended by this file.
-/

open Complex ProbabilityTheory Set Filter
open scoped Classical Topology
@[expose] public noncomputable section
namespace DirichletTransform.TwoVariable

/-- A product of two right-half-plane numbers avoids the principal branch cut. -/
theorem mul_mem_slitPlane_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    x * y ∈ slitPlane := by
  apply mem_slitPlane_iff.mpr
  by_cases hi : (x * y).im = 0
  · left
    have hid : x.re * (x * y).re = y.re * (x.re ^ 2 + x.im ^ 2) - x.im * (x * y).im := by
      simp only [mul_re, mul_im]
      ring
    rw [hi, mul_zero, sub_zero] at hid
    have hp : 0 < y.re * (x.re ^ 2 + x.im ^ 2) :=
      mul_pos hy (add_pos_of_pos_of_nonneg (sq_pos_of_pos hx) (sq_nonneg _))
    exact (mul_pos_iff_of_pos_left hx).mp (hid.symm ▸ hp)
  · exact Or.inr hi

/-- Squaring a right-half-plane number can leave that half-plane but not the slit plane. -/
theorem sq_mem_slitPlane_of_re_pos {x : ℂ} (hx : 0 < x.re) : x ^ 2 ∈ slitPlane := by
  simpa only [pow_two] using mul_mem_slitPlane_of_re_pos hx hx

/-- The two transformed mean squares stay on the principal slit branch. -/
theorem meanSquares_mem_slitDomain {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    pair (arithmeticMeanSq x y) (geometricMeanSq x y) ∈ carlsonRSlitDomain := by
  intro i
  fin_cases i
  · apply sq_mem_slitPlane_of_re_pos
    simp only [div_ofNat_re, add_re]
    positivity
  · exact mul_mem_slitPlane_of_re_pos hx hy

private theorem convex_right_node_domain : Convex ℝ (carlsonRVariableDomain (ι := Fin 2)) := by
  intro z hz w hw a b ha hb hab i
  exact convex_carlsonRightHalfPlane (hz i) (hw i) ha hb hab

private theorem pair_eta (w : Fin 2 → ℂ) : pair (w 0) (w 1) = w := by
  ext i
  fin_cases i <;> rfl

private theorem eventually_quadraticDomains_one :
    ∀ᶠ w : Fin 2 → ℂ in 𝓝 (fun _ => 1),
      FirstQuadraticDomain (w 0) (w 1) ∧ SecondQuadraticDomain (w 0) (w 1) := by
  have hone : (fun _ : Fin 2 => (1 : ℂ)) ∈ carlsonRVariableDomain :=
    fun _ => by simp [carlsonRightHalfPlane]
  have hm : Continuous (fun w : Fin 2 → ℂ =>
      pair (arithmeticMeanSq (w 0) (w 1)) (geometricMeanSq (w 0) (w 1))) := by
    unfold arithmeticMeanSq geometricMeanSq pair
    fun_prop
  have hs : Continuous (fun w : Fin 2 → ℂ => pair ((w 0) ^ 2) ((w 1) ^ 2)) := by
    unfold pair
    fun_prop
  have hmone : pair (arithmeticMeanSq 1 1) (geometricMeanSq 1 1) ∈ carlsonRVariableDomain := by
    intro i
    fin_cases i <;> norm_num [pair, arithmeticMeanSq, geometricMeanSq, carlsonRightHalfPlane]
  have hsone : pair ((1 : ℂ) ^ 2) ((1 : ℂ) ^ 2) ∈ carlsonRVariableDomain := by
    intro i
    fin_cases i <;> norm_num [pair, carlsonRightHalfPlane]
  filter_upwards [isOpen_carlsonRVariableDomain.eventually_mem hone,
    hm.continuousAt.tendsto.eventually (isOpen_carlsonRVariableDomain.eventually_mem hmone),
    hs.continuousAt.tendsto.eventually (isOpen_carlsonRVariableDomain.eventually_mem hsone)]
    with w hw hm hs
  exact ⟨⟨by simpa only [pair_eta] using hw, hm⟩, ⟨hs, hm⟩⟩

private theorem analyticAt_meanSquares (w : Fin 2 → ℂ) :
    AnalyticAt ℂ (fun q : Fin 2 → ℂ =>
      pair (arithmeticMeanSq (q 0) (q 1)) (geometricMeanSq (q 0) (q 1))) w := by
  have h0 := (ContinuousLinearMap.proj 0 : (Fin 2 → ℂ) →L[ℂ] ℂ).analyticAt w
  have h1 := (ContinuousLinearMap.proj 1 : (Fin 2 → ℂ) →L[ℂ] ℂ).analyticAt w
  apply analyticAt_pi_iff.mpr
  intro i
  fin_cases i
  · exact ((h0.add h1).div_const (c := (2 : ℂ))).pow 2
  · exact h0.mul h1

/-- First quadratic transformation, with no restriction on the real parts of
the transformed mean squares and no Dirichlet-parameter exclusions. -/
theorem regRSlit_firstQuadratic (t β x y : ℂ) (hx : 0 < x.re) (hy : 0 < y.re) :
    regCarlsonRSlit (2 * t) (pair β β) (pair x y) =
      quadraticGammaRatio β * regCarlsonRSlit t (pair (β + t) (1 / 2 - t))
        (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) := by
  let F := fun w : Fin 2 → ℂ => regCarlsonRSlit (2 * t) (pair β β) w
  let G := fun w : Fin 2 → ℂ => quadraticGammaRatio β *
    regCarlsonRSlit t (pair (β + t) (1 / 2 - t))
      (pair (arithmeticMeanSq (w 0) (w 1)) (geometricMeanSq (w 0) (w 1)))
  have hF : AnalyticOnNhd ℂ F carlsonRVariableDomain :=
    (analyticOnNhd_regCarlsonRSlit _ _).mono carlsonRVariableDomain_subset_slitDomain
  have hG : AnalyticOnNhd ℂ G carlsonRVariableDomain := by
    intro w hw
    exact analyticAt_const.mul (analyticAt_regCarlsonRSlit_comp
      analyticAt_const analyticAt_const (analyticAt_meanSquares w)
      (meanSquares_mem_slitDomain (hw 0) (hw 1)))
  have heq := hF.eqOn_of_preconnected_of_eventuallyEq hG
    convex_right_node_domain.isPreconnected
    (show (fun _ : Fin 2 => (1 : ℂ)) ∈ carlsonRVariableDomain from fun _ => by
      simp [carlsonRightHalfPlane]) ?_
  · exact heq (show pair x y ∈ carlsonRVariableDomain by
      intro i; fin_cases i <;> assumption)
  · filter_upwards [eventually_quadraticDomains_one] with w hw
    change regCarlsonRSlit (2 * t) (pair β β) w = _
    conv_lhs => rw [← pair_eta w]
    rw [regCarlsonRSlit_eq_continued _ _ hw.1.1]
    change _ = quadraticGammaRatio β * regCarlsonRSlit t _ _
    rw [regCarlsonRSlit_eq_continued _ _ hw.1.2]
    exact regRContinued_firstQuadratic t β (w 0) (w 1) hw.1

/-- Second quadratic transformation on the whole positive-real-part square-root
domain. The squared input nodes and both transformed nodes may have negative real parts. -/
theorem regRSlit_secondQuadratic (t β x y : ℂ) (hx : 0 < x.re) (hy : 0 < y.re) :
    regCarlsonRSlit t (pair β β) (pair (x ^ 2) (y ^ 2)) =
      quadraticGammaRatio β * regCarlsonRSlit t (pair (2 * β + t) (1 / 2 - β - t))
        (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) := by
  let F := fun w : Fin 2 → ℂ => regCarlsonRSlit t (pair β β) (pair ((w 0) ^ 2) ((w 1) ^ 2))
  let G := fun w : Fin 2 → ℂ => quadraticGammaRatio β *
    regCarlsonRSlit t (pair (2 * β + t) (1 / 2 - β - t))
      (pair (arithmeticMeanSq (w 0) (w 1)) (geometricMeanSq (w 0) (w 1)))
  have hF : AnalyticOnNhd ℂ F carlsonRVariableDomain := by
    intro w hw
    apply analyticAt_regCarlsonRSlit_comp analyticAt_const analyticAt_const
    · apply analyticAt_pi_iff.mpr
      intro i
      fin_cases i
      · exact ((ContinuousLinearMap.proj 0 : (Fin 2 → ℂ) →L[ℂ] ℂ).analyticAt w).pow 2
      · exact ((ContinuousLinearMap.proj 1 : (Fin 2 → ℂ) →L[ℂ] ℂ).analyticAt w).pow 2
    · intro i
      fin_cases i
      · exact sq_mem_slitPlane_of_re_pos (hw 0)
      · exact sq_mem_slitPlane_of_re_pos (hw 1)
  have hG : AnalyticOnNhd ℂ G carlsonRVariableDomain := by
    intro w hw
    exact analyticAt_const.mul (analyticAt_regCarlsonRSlit_comp
      analyticAt_const analyticAt_const (analyticAt_meanSquares w)
      (meanSquares_mem_slitDomain (hw 0) (hw 1)))
  have heq := hF.eqOn_of_preconnected_of_eventuallyEq hG
    convex_right_node_domain.isPreconnected
    (show (fun _ : Fin 2 => (1 : ℂ)) ∈ carlsonRVariableDomain from fun _ => by
      simp [carlsonRightHalfPlane]) ?_
  · exact heq (show pair x y ∈ carlsonRVariableDomain by
      intro i; fin_cases i <;> assumption)
  · filter_upwards [eventually_quadraticDomains_one] with w hw
    change regCarlsonRSlit t (pair β β) (pair ((w 0) ^ 2) ((w 1) ^ 2)) =
      quadraticGammaRatio β * regCarlsonRSlit t _ _
    rw [regCarlsonRSlit_eq_continued _ _ hw.2.1, regCarlsonRSlit_eq_continued _ _ hw.2.2]
    exact regRContinued_secondQuadratic t β (w 0) (w 1) hw.2

end DirichletTransform.TwoVariable
end

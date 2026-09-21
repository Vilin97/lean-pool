/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.QuadraticContinuation
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Equal-parameter continuation and quadratic transformations

The equal-parameter family `R_t(β, β; x, y)` has a larger parameter domain than
one obtains by excluding all poles of `Γ(2β)`: the values at nonpositive integer
`β` are removable. Its natural regularization divides by `Γ(β + 1/2)`.

We construct that entire regularization uniquely by agreement with the native
integral on `re β > 0`. Square roots in the positive component allow the second
quadratic identity to supply existence for any right-half-plane nodes. Both
quadratic transformations then identify this canonical continuation, including
its removable values. The ordinary function is analytic wherever `β + 1/2` is
not a nonpositive integer. No extension of the node domains is asserted here.
-/

open Complex ProbabilityTheory Filter Set
open scoped Classical Topology
@[expose] public noncomputable section
namespace DirichletTransform.TwoVariable

/-- Characterization of the entire equal-parameter regularization. -/
def IsRegEqualRContinuation (t x y : ℂ) (G : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ G univ ∧ ∀ β, 0 < β.re →
    G β = rIntegral t β β x y / Gamma (β + 1 / 2)

/-- Native agreement uniquely determines the entire equal-parameter regularization. -/
theorem IsRegEqualRContinuation.unique {t x y : ℂ} {F G : ℂ → ℂ}
    (hF : IsRegEqualRContinuation t x y F) (hG : IsRegEqualRContinuation t x y G) : F = G := by
  apply hF.1.eq_of_eventuallyEq hG.1 (z₀ := (1 : ℂ))
  filter_upwards [Complex.continuous_re.continuousAt.eventually_const_lt
    (show (0 : ℝ) < (1 : ℂ).re by norm_num)] with β hβ
  rw [hF.2 β hβ, hG.2 β hβ]

private theorem isRegEqualRContinuation_of_quadratic
    (t s x y : ℂ) (Z : Fin 2 → ℂ) (hZ : Z ∈ carlsonRVariableDomain)
    (hz : pair x y ∈ carlsonRVariableDomain) (b : ℂ → Fin 2 → ℂ)
    (hb : AnalyticOnNhd ℂ b univ)
    (h : ∀ β, regCarlsonRContinued t (pair x y) hz (pair β β) =
      quadraticGammaRatio β * regCarlsonRContinued s Z hZ (b β)) :
    IsRegEqualRContinuation t x y (fun β => regCarlsonRContinued s Z hZ (b β)) := by
  refine ⟨fun β _ => analyticAt_regCarlsonRContinued_comp hZ analyticAt_const (hb β trivial), ?_⟩
  intro β hβ
  have hpos : pair β β ∈ mvBetaConvergent := by intro i; fin_cases i <;> exact hβ
  have hc : 0 < (β + 1 / 2).re := by simp only [add_re]; norm_num; linarith
  apply (eq_div_iff (Gamma_ne_zero_of_re_pos hc)).mpr
  have H := h β
  rw [regCarlsonRContinued_eq_integral _ hz hpos] at H
  change _ = Gamma (∑ i, pair β β i) * regCarlsonRIntegral t (pair β β) (pair x y)
  rw [sum_pair, H, ← mul_assoc, Gamma_mul_quadraticGammaRatio hβ, mul_comm]

/-- The first transformed regularized function gives the entire equal-parameter family. -/
theorem isRegEqualRContinuation_firstQuadratic (t x y : ℂ) (hz : FirstQuadraticDomain x y) :
    IsRegEqualRContinuation (2 * t) x y (fun β => regCarlsonRContinued t
      (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) hz.2
      (pair (β + t) (1 / 2 - t))) := by
  apply isRegEqualRContinuation_of_quadratic (2 * t) t x y _ hz.2 hz.1
  · intro β _
    apply analyticAt_pi_iff.mpr
    intro i; fin_cases i
    · exact analyticAt_id.add analyticAt_const
    · exact analyticAt_const
  · exact fun β => regRContinued_firstQuadratic t β x y hz

/-- The second transformed regularized function gives the entire equal-parameter family. -/
theorem isRegEqualRContinuation_secondQuadratic (t x y : ℂ) (hz : SecondQuadraticDomain x y) :
    IsRegEqualRContinuation t (x ^ 2) (y ^ 2) (fun β => regCarlsonRContinued t
      (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) hz.2
      (pair (2 * β + t) (1 / 2 - β - t))) := by
  apply isRegEqualRContinuation_of_quadratic t t (x ^ 2) (y ^ 2) _ hz.2 hz.1
  · intro β _
    apply analyticAt_pi_iff.mpr
    intro i; fin_cases i
    · exact (analyticAt_const.mul analyticAt_id).add analyticAt_const
    · exact (analyticAt_const.sub analyticAt_id).sub analyticAt_const
  · exact fun β => regRContinued_secondQuadratic t β x y hz

private lemma exists_right_root {z : ℂ} (hz : 0 < z.re) :
    ∃ x : ℂ, x ^ 2 = z ∧ 0 < x.re ∧ |x.im| < x.re := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq z (show 0 < (2 : ℕ) by omega)
  have hs : u.im ^ 2 < u.re ^ 2 := by
    have H := congrArg Complex.re hu
    simp only [pow_two, mul_re] at H
    nlinarith
  have hn : u.re ≠ 0 := by intro h; rw [h] at hs; nlinarith [sq_nonneg u.im]
  have hp : ∀ v : ℂ, v ^ 2 = z → 0 < v.re → |v.im| < v.re := by
    intro v hv hvp
    have H := congrArg Complex.re hv
    simp only [pow_two, mul_re] at H
    exact (sq_lt_sq₀ (abs_nonneg _) hvp.le).mp (by rw [sq_abs]; nlinarith)
  rcases lt_or_gt_of_ne hn with h | h
  · refine ⟨-u, by simpa using hu, by simpa using neg_pos.mpr h, ?_⟩
    exact hp (-u) (by simpa using hu) (by simpa using neg_pos.mpr h)
  · exact ⟨u, hu, h, hp u hu h⟩

private lemma secondQuadraticDomain_of_right_roots {x y : ℂ}
    (hx : |x.im| < x.re) (hy : |y.im| < y.re) : SecondQuadraticDomain x y := by
  have hxpos : 0 < x.re := (abs_nonneg _).trans_lt hx
  have hypos : 0 < y.re := (abs_nonneg _).trans_lt hy
  have hx₂ : x.im ^ 2 < x.re ^ 2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg _) hxpos.le).mpr hx
  have hy₂ : y.im ^ 2 < y.re ^ 2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg _) hypos.le).mpr hy
  have hprod : x.im * y.im < x.re * y.re :=
    (le_abs_self _).trans_lt (by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hx.le (abs_nonneg _)).trans_lt
        (mul_lt_mul_of_pos_left hy hxpos))
  have hsum : (x.im + y.im) ^ 2 < (x.re + y.re) ^ 2 := by
    have h : |x.im + y.im| < x.re + y.re := (abs_add_le _ _).trans_lt (add_lt_add hx hy)
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg _) (add_pos hxpos hypos).le).mpr h
  constructor
  · intro i; fin_cases i
    · change 0 < (x ^ 2).re
      simp only [pow_two, mul_re]; nlinarith
    · change 0 < (y ^ 2).re
      simp only [pow_two, mul_re]; nlinarith
  · intro i; fin_cases i
    · change 0 < (arithmeticMeanSq x y).re
      norm_num [arithmeticMeanSq, pow_two, mul_re, mul_im, div_re, div_im]
      nlinarith
    · change 0 < (x * y).re
      rw [mul_re]; linarith

/-- Existence on arbitrary right-half-plane nodes, without selecting a square-root branch
in the definition of the continuation. -/
theorem exists_isRegEqualRContinuation (t x y : ℂ) (hz : pair x y ∈ carlsonRVariableDomain) :
    ∃ G, IsRegEqualRContinuation t x y G := by
  obtain ⟨u, hu, _, hup⟩ := exists_right_root (show 0 < x.re from hz 0)
  obtain ⟨v, hv, _, hvp⟩ := exists_right_root (show 0 < y.re from hz 1)
  exact ⟨_, by simpa only [hu, hv] using
    isRegEqualRContinuation_secondQuadratic t u v (secondQuadraticDomain_of_right_roots hup hvp)⟩

/-- Canonical entire continuation of `R_t(β, β; x, y) / Γ(β + 1/2)`. -/
def regEqualRContinued (t x y : ℂ) (hz : pair x y ∈ carlsonRVariableDomain) : ℂ → ℂ :=
  (exists_isRegEqualRContinuation t x y hz).choose

/-- The chosen continuation satisfies the native characterization. -/
theorem isRegEqualRContinuation_regEqualRContinued (t x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) :
    IsRegEqualRContinuation t x y (regEqualRContinued t x y hz) :=
  (exists_isRegEqualRContinuation t x y hz).choose_spec

/-- The canonical equal-parameter regularization is entire in `β`. -/
theorem analyticOnNhd_regEqualRContinued (t x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) :
    AnalyticOnNhd ℂ (regEqualRContinued t x y hz) univ :=
  (isRegEqualRContinuation_regEqualRContinued t x y hz).1

/-- First quadratic transformation with the natural equal-parameter regularization.
Unlike the general `Γ(2β)` regularization, this loses no information at integral `β`. -/
theorem regEqualRContinued_firstQuadratic (t β x y : ℂ) (hz : FirstQuadraticDomain x y) :
    regEqualRContinued (2 * t) x y hz.1 β = regCarlsonRContinued t
      (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) hz.2
      (pair (β + t) (1 / 2 - t)) :=
  congrFun ((isRegEqualRContinuation_regEqualRContinued (2 * t) x y hz.1).unique
    (isRegEqualRContinuation_firstQuadratic t x y hz)) β

/-- Second quadratic transformation with the natural equal-parameter regularization. -/
theorem regEqualRContinued_secondQuadratic (t β x y : ℂ) (hz : SecondQuadraticDomain x y) :
    regEqualRContinued t (x ^ 2) (y ^ 2) hz.1 β = regCarlsonRContinued t
      (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) hz.2
      (pair (2 * β + t) (1 / 2 - β - t)) :=
  congrFun ((isRegEqualRContinuation_regEqualRContinued t (x ^ 2) (y ^ 2) hz.1).unique
    (isRegEqualRContinuation_secondQuadratic t x y hz)) β

/-- Compatibility with the general regularized R-function. The factor can vanish;
the equal-parameter regularization retains the removable values in that case. -/
theorem regCarlsonRContinued_pair_eq (t β x y : ℂ) (hz : pair x y ∈ carlsonRVariableDomain) :
    regCarlsonRContinued t (pair x y) hz (pair β β) =
      quadraticGammaRatio β * regEqualRContinued t x y hz β := by
  obtain ⟨u, hu, _, hup⟩ := exists_right_root (show 0 < x.re from hz 0)
  obtain ⟨v, hv, _, hvp⟩ := exists_right_root (show 0 < y.re from hz 1)
  subst x; subst y
  have hroot := secondQuadraticDomain_of_right_roots hup hvp
  rw [regEqualRContinued_secondQuadratic t β u v hroot]
  exact regRContinued_secondQuadratic t β u v hroot

/-- Joint analytic dependence on the exponent and the equal Dirichlet parameter. -/
theorem analyticAt_regEqualRContinued_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f b : E → ℂ} {p : E} {x y : ℂ} (hz : pair x y ∈ carlsonRVariableDomain)
    (hf : AnalyticAt ℂ f p) (hb : AnalyticAt ℂ b p) :
    AnalyticAt ℂ (fun w => regEqualRContinued (f w) x y hz (b w)) p := by
  obtain ⟨u, hu, _, hup⟩ := exists_right_root (show 0 < x.re from hz 0)
  obtain ⟨v, hv, _, hvp⟩ := exists_right_root (show 0 < y.re from hz 1)
  subst x; subst y
  have hroot := secondQuadraticDomain_of_right_roots hup hvp
  simp only [regEqualRContinued_secondQuadratic _ _ u v hroot]
  apply analyticAt_regCarlsonRContinued_comp hroot.2 hf
  apply analyticAt_pi_iff.mpr
  intro i; fin_cases i
  · exact (analyticAt_const.mul hb).add hf
  · exact (analyticAt_const.sub hb).sub hf

/-- Equal-parameter ordinary R. At genuine poles of `Γ(β + 1/2)` this definition is
totalized; analyticity and its interpretation as continuation are asserted on the
Gamma-regular domain, which includes every nonpositive integer `β`. -/
def equalRContinued (t x y : ℂ) (hz : pair x y ∈ carlsonRVariableDomain) (β : ℂ) : ℂ :=
  Gamma (β + 1 / 2) * regEqualRContinued t x y hz β

/-- Agreement with the original integral wherever that integral converges. -/
theorem equalRContinued_eq_integral (t β x y : ℂ) (hz : pair x y ∈ carlsonRVariableDomain)
    (hβ : 0 < β.re) : equalRContinued t x y hz β = rIntegral t β β x y := by
  have hc : 0 < (β + 1 / 2).re := by simp only [add_re]; norm_num; linarith
  rw [equalRContinued, (isRegEqualRContinuation_regEqualRContinued t x y hz).2 β hβ]
  exact mul_div_cancel₀ _ (Gamma_ne_zero_of_re_pos hc)

/-- Analyticity of the ordinary equal-parameter function on Carlson's parameter domain. -/
theorem analyticOnNhd_equalRContinued (t x y : ℂ) (hz : pair x y ∈ carlsonRVariableDomain) :
    AnalyticOnNhd ℂ (equalRContinued t x y hz) {β | IsCarlsonGammaRegular (β + 1 / 2)} := by
  intro β hβ
  have hG : AnalyticAt ℂ (fun w : ℂ => Gamma (w + 1 / 2)) β := by
    have hsum : AnalyticAt ℂ (fun w : ℂ => w + 1 / 2) β := analyticAt_id.add analyticAt_const
    have H := ((differentiable_one_div_Gamma.analyticAt (β + 1 / 2)).comp_of_eq hsum rfl).inv
      (inv_ne_zero (Gamma_ne_zero hβ))
    change AnalyticAt ℂ (fun w : ℂ => (Gamma (w + 1 / 2))⁻¹⁻¹) β at H
    simpa only [inv_inv] using H
  exact hG.mul (analyticOnNhd_regEqualRContinued t x y hz β trivial)

/-- The nonpositive integral parameters are in the ordinary continuation domain. -/
theorem isCarlsonGammaRegular_neg_nat_add_half (n : ℕ) :
    IsCarlsonGammaRegular (-(n : ℂ) + 1 / 2) := by
  intro m hm
  have H : (2 : ℂ) * m + 1 = 2 * n := by linear_combination 2 * hm
  have Hnat : 2 * m + 1 = 2 * n := by exact_mod_cast H
  omega

/-- At exponent zero the entire equal-parameter regularization is reciprocal Gamma. -/
@[simp] theorem regEqualRContinued_zero (β x y : ℂ) (hz : pair x y ∈ carlsonRVariableDomain) :
    regEqualRContinued 0 x y hz β = (Gamma (β + 1 / 2))⁻¹ := by
  obtain ⟨u, hu, _, hup⟩ := exists_right_root (show 0 < x.re from hz 0)
  obtain ⟨v, hv, _, hvp⟩ := exists_right_root (show 0 < y.re from hz 1)
  subst x; subst y
  have hroot := secondQuadraticDomain_of_right_roots hup hvp
  rw [regEqualRContinued_secondQuadratic 0 β u v hroot]
  rw [show (0 : ℂ) = (0 : ℕ) by norm_num, regCarlsonRContinued_natCast]
  simp only [regCarlsonR, regCarlsonRPolynomial_zero, sum_pair]
  congr 2
  ring

/-- Regression check for the removable values: the exponent-zero function is one,
including at `β = 0, -1, -2, ...`. -/
@[simp] theorem equalRContinued_zero (β x y : ℂ) (hz : pair x y ∈ carlsonRVariableDomain)
    (hβ : IsCarlsonGammaRegular (β + 1 / 2)) : equalRContinued 0 x y hz β = 1 := by
  rw [equalRContinued, regEqualRContinued_zero, mul_inv_cancel₀ (Gamma_ne_zero hβ)]

/-- Carlson 6.9-3 on the full common parameter domain of the ordinary functions. -/
theorem equalRContinued_firstQuadratic (t β x y : ℂ) (hz : FirstQuadraticDomain x y)
    (_hβ : IsCarlsonGammaRegular (β + 1 / 2)) :
    equalRContinued (2 * t) x y hz.1 β = Gamma (β + 1 / 2) * regCarlsonRContinued t
      (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) hz.2
      (pair (β + t) (1 / 2 - t)) := by
  rw [equalRContinued, regEqualRContinued_firstQuadratic t β x y hz]

/-- Carlson 6.10-1 on the full common parameter domain of the ordinary functions. -/
theorem equalRContinued_secondQuadratic (t β x y : ℂ) (hz : SecondQuadraticDomain x y)
    (_hβ : IsCarlsonGammaRegular (β + 1 / 2)) :
    equalRContinued t (x ^ 2) (y ^ 2) hz.1 β = Gamma (β + 1 / 2) * regCarlsonRContinued t
      (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) hz.2
      (pair (2 * β + t) (1 / 2 - β - t)) := by
  rw [equalRContinued, regEqualRContinued_secondQuadratic t β x y hz]

end DirichletTransform.TwoVariable
end

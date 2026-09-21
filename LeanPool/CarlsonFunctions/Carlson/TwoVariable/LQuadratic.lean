/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.EqualParameter
public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.ParameterSymmetry
public import LeanPool.CarlsonFunctions.Carlson.L.SlitContinuation

/-!
# Differentiating the quadratic transformations

The natural equal-parameter L-regularization is the exponent derivative of the
equal-parameter R-regularization. In particular, its definition does not divide
by the possibly vanishing `quadraticGammaRatio`.

Both quadratic identities are differentiated here, including the correction from
the moving Dirichlet parameters. The parameter-transfer identity (1987), (2.12),
identifies this correction with the transformed L-term, yielding (6.4) and (6.5).
All complex exponent and Dirichlet parameters are allowed. The input node domains
are those of the R-identities; transformed ratios use the slit-plane interface.
At exponent zero the correction vanishes, giving both identities (6.8).
-/

open Complex Filter Set
open scoped Classical Topology
@[expose] public noncomputable section
namespace DirichletTransform.TwoVariable

/-- The normalization by `Γ(β + 1/2)`, retaining removable equal-parameter values. -/
def regEqualLContinued (t x y : ℂ) (hz : pair x y ∈ carlsonRVariableDomain)
    (β : ℂ) : ℂ :=
  deriv (fun s => regEqualRContinued s x y hz β) t

theorem hasDerivAt_regEqualRContinued_L (t β x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) :
    HasDerivAt (fun s => regEqualRContinued s x y hz β)
      (regEqualLContinued t x y hz β) t :=
  (analyticAt_regEqualRContinued_comp hz analyticAt_id analyticAt_const).differentiableAt.hasDerivAt

/-- Entire dependence on both the exponent and the equal Dirichlet parameter. -/
theorem analyticOnNhd_regEqualLContinued_joint (x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) :
    AnalyticOnNhd ℂ (fun p : Fin 2 → ℂ => regEqualLContinued (p 0) x y hz (p 1)) univ := by
  have ha : AnalyticOnNhd ℂ
      (fun p : Fin 2 → ℂ => regEqualRContinued (p 0) x y hz (p 1)) univ :=
    fun p _ => analyticAt_regEqualRContinued_comp hz
      ((analyticAt_pi_iff.mp analyticAt_id) 0) ((analyticAt_pi_iff.mp analyticAt_id) 1)
  have h := ha.partialDeriv isOpen_univ 0
  have heq : SeveralComplexVariables.partialDeriv 0
      (fun p : Fin 2 → ℂ => regEqualRContinued (p 0) x y hz (p 1)) =
      (fun p => regEqualLContinued (p 0) x y hz (p 1)) := by
    funext p
    simp [SeveralComplexVariables.partialDeriv, regEqualLContinued]
  rwa [heq] at h

/-- Analytic substitutions in the exponent and equal parameter. -/
theorem analyticAt_regEqualLContinued_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f b : E → ℂ} {p : E} {x y : ℂ} (hz : pair x y ∈ carlsonRVariableDomain)
    (hf : AnalyticAt ℂ f p) (hb : AnalyticAt ℂ b p) :
    AnalyticAt ℂ (fun w => regEqualLContinued (f w) x y hz (b w)) p := by
  have hp : AnalyticAt ℂ (fun w => pair (f w) (b w)) p := by
    apply analyticAt_pi_iff.mpr
    intro i; fin_cases i
    · exact hf
    · exact hb
  exact (analyticOnNhd_regEqualLContinued_joint x y hz (pair (f p) (b p)) trivial).comp_of_eq hp rfl

/-- The ordinary equal-parameter L-function. At genuine poles of `Γ(β + 1/2)`
this is only a totalized expression; nonpositive integral `β` are removable values. -/
def equalLContinued (t x y : ℂ) (hz : pair x y ∈ carlsonRVariableDomain) (β : ℂ) : ℂ :=
  Gamma (β + 1 / 2) * regEqualLContinued t x y hz β

/-- The ordinary equal-parameter L-function is the exponent derivative of ordinary R. -/
theorem hasDerivAt_equalRContinued_L (t β x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) :
    HasDerivAt (fun s => equalRContinued s x y hz β) (equalLContinued t x y hz β) t :=
  (hasDerivAt_regEqualRContinued_L t β x y hz).const_mul _

/-- Holomorphy on Carlson's ordinary equal-parameter domain. -/
theorem analyticAt_equalLContinued_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f b : E → ℂ} {p : E} {x y : ℂ} (hz : pair x y ∈ carlsonRVariableDomain)
    (hf : AnalyticAt ℂ f p) (hb : AnalyticAt ℂ b p)
    (hβ : IsCarlsonGammaRegular (b p + 1 / 2)) :
    AnalyticAt ℂ (fun w => equalLContinued (f w) x y hz (b w)) p := by
  have hsum := hb.add (analyticAt_const (v := (1 / 2 : ℂ)))
  have hG := ((differentiable_one_div_Gamma.analyticAt (b p + 1 / 2)).comp_of_eq hsum rfl).inv
    (inv_ne_zero (Gamma_ne_zero hβ))
  change AnalyticAt ℂ (fun w => (Gamma (b w + 1 / 2))⁻¹⁻¹) p at hG
  simp only [inv_inv] at hG
  exact hG.mul (analyticAt_regEqualLContinued_comp hz hf hb)

/-- In particular, the nonpositive integral equal parameters are regular points,
not poles of the ordinary L-continuation. -/
theorem analyticAt_equalLContinued_neg_nat (t x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) (n : ℕ) :
    AnalyticAt ℂ (equalLContinued t x y hz) (-(n : ℂ)) :=
  analyticAt_equalLContinued_comp hz analyticAt_const analyticAt_id
    (isCarlsonGammaRegular_neg_nat_add_half n)

/-- Agreement with the Gamma-normalized native L-integral on convergent parameters. -/
theorem regEqualLContinued_eq_integral (t β x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) (hβ : 0 < β.re) :
    regEqualLContinued t x y hz β =
      carlsonLIntegral t (pair β β) (pair x y) / Gamma (β + 1 / 2) := by
  have hb : pair β β ∈ mvBetaConvergent := by
    intro i; fin_cases i <;> exact hβ
  have heq : (fun s => regEqualRContinued s x y hz β) =
      (fun s => rIntegral s β β x y / Gamma (β + 1 / 2)) :=
    funext fun s => (isRegEqualRContinuation_regEqualRContinued s x y hz).2 β hβ
  have h := hasDerivAt_regEqualRContinued_L t β x y hz
  rw [heq] at h
  exact h.unique ((hasDerivAt_carlsonRIntegral_L t hb hz).div_const _)

/-- Agreement of ordinary equal-parameter L with its convergent integral. -/
theorem equalLContinued_eq_integral (t β x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) (hβ : 0 < β.re) :
    equalLContinued t x y hz β = carlsonLIntegral t (pair β β) (pair x y) := by
  have hc : 0 < (β + 1 / 2).re := by simp only [add_re]; norm_num; linarith
  rw [equalLContinued, regEqualLContinued_eq_integral t β x y hz hβ]
  exact mul_div_cancel₀ _ (Gamma_ne_zero_of_re_pos hc)

/-- Compatibility does not require cancelling the Gamma ratio. -/
theorem regCarlsonLContinued_pair_eq (t β x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) :
    regCarlsonLContinued t (pair x y) hz (pair β β) =
      quadraticGammaRatio β * regEqualLContinued t x y hz β := by
  have heq : (fun s => regCarlsonRContinued s (pair x y) hz (pair β β)) =
      (fun s => quadraticGammaRatio β * regEqualRContinued s x y hz β) :=
    funext fun s => regCarlsonRContinued_pair_eq s β x y hz
  have h := (hasDerivAt_regCarlsonRContinued_L t (pair β β) hz)
  rw [heq] at h
  exact h.unique ((hasDerivAt_regEqualRContinued_L t β x y hz).const_mul _)

/-- Slit-interface compatibility on the node domain of the equal-parameter family. -/
theorem regCarlsonLSlit_pair_eq (t β x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) :
    regCarlsonLSlit t (pair β β) (pair x y) =
      quadraticGammaRatio β * regEqualLContinued t x y hz β := by
  rw [regCarlsonLSlit_eq_continued t (pair β β) hz,
    regCarlsonLContinued_pair_eq t β x y hz]

/-- The missing term when the exponent and the Dirichlet parameters both vary.
The parameter sum `u + v` stays fixed along this derivative. -/
def regRParameterTransfer (t u v x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) : ℂ :=
  deriv (fun s => regCarlsonRContinued t (pair x y) hz (pair (u + s) (v - s))) 0

/-- Carlson (1987), (2.12), normalized at the first node. The ratio may lie outside
the right half-plane, so the transformed L-function uses its slit continuation. -/
theorem regRParameterTransfer_eq_L (t u v x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) :
    regRParameterTransfer t u v x y hz =
      x ^ t * regCarlsonLSlit (-v) (pair (u + v + t) (-t)) (pair 1 (y / x)) := by
  have hs : pair 1 (y / x) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · simp [pair]
    · exact div_mem_slitPlane_of_re_pos (hz 1) (hz 0)
  have heq : (fun s => regCarlsonRContinued t (pair x y) hz (pair (u + s) (v - s))) =
      (fun s => x ^ t * regCarlsonRSlit (s - v) (pair (u + v + t) (-t)) (pair 1 (y / x))) := by
    funext s
    have h := regCarlsonRSlit_parameterInterchange t (u + s) (v - s) (hz 0) (hz 1)
    simp only [pair_zero, pair_one] at h
    rw [regCarlsonRSlit_eq_continued t _ hz,
      show u + s + (v - s) + t = u + v + t by ring,
      show -(v - s) = s - v by ring] at h
    exact h
  have h := ((hasDerivAt_regCarlsonRSlit_L (-v) (pair (u + v + t) (-t)) hs).comp_of_eq 0
    ((hasDerivAt_id 0).sub_const v) (by simp)).const_mul (x ^ t)
  rw [regRParameterTransfer, heq]
  simpa using h.deriv

/-- Carlson (1987), second form of (2.12), normalized at the last node. -/
theorem regRParameterTransfer_eq_neg_L (t u v x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) :
    regRParameterTransfer t u v x y hz =
      -(y ^ t * regCarlsonLSlit (-u) (pair (-t) (u + v + t)) (pair (x / y) 1)) := by
  have hs : pair (x / y) 1 ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact div_mem_slitPlane_of_re_pos (hz 0) (hz 1)
    · simp [pair]
  have heq : (fun s => regCarlsonRContinued t (pair x y) hz (pair (u + s) (v - s))) =
      (fun s => y ^ t * regCarlsonRSlit (-u - s) (pair (-t) (u + v + t)) (pair (x / y) 1)) := by
    funext s
    have h := regCarlsonRSlit_parameterInterchange_last t (u + s) (v - s) (hz 0) (hz 1)
    simp only [pair_zero, pair_one] at h
    rw [regCarlsonRSlit_eq_continued t _ hz,
      show u + s + (v - s) + t = u + v + t by ring,
      show -(u + s) = -u - s by ring] at h
    exact h
  have h := ((hasDerivAt_regCarlsonRSlit_L (-u) (pair (-t) (u + v + t)) hs).comp_of_eq 0
    ((hasDerivAt_const 0 (-u)).sub (hasDerivAt_id 0)) (by simp)).const_mul (y ^ t)
  rw [regRParameterTransfer, heq]
  simpa using h.deriv

private theorem deriv_diagonal {F : ℂ × ℂ → ℂ} {t : ℂ}
    (hF : DifferentiableAt ℂ F (t, t)) :
    deriv (fun s => F (s, s)) t =
      deriv (fun s => F (s, t)) t + deriv (fun s => F (t, s)) t := by
  have h₁ := hF.hasFDerivAt.comp_hasDerivAt_of_eq t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t t)) rfl
  have h₂ := hF.hasFDerivAt.comp_hasDerivAt_of_eq t
    ((hasDerivAt_const t t).prodMk (hasDerivAt_id t)) rfl
  have h := hF.hasFDerivAt.comp_hasDerivAt_of_eq t
    ((hasDerivAt_id t).prodMk (hasDerivAt_id t)) rfl
  simp only [Function.comp_def, id_eq] at h h₁ h₂
  rw [h.deriv, h₁.deriv, h₂.deriv, ← map_add]
  simp

/-- Chain rule for the exponent and a sum-preserving parameter transfer. -/
theorem deriv_regRContinued_exponent_transfer (t u v x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) :
    deriv (fun s => regCarlsonRContinued s (pair x y) hz (pair (u + s) (v - s))) t =
      regCarlsonLContinued t (pair x y) hz (pair (u + t) (v - t)) +
        regRParameterTransfer t (u + t) (v - t) x y hz := by
  have ha : AnalyticAt ℂ (fun p : ℂ × ℂ =>
      regCarlsonRContinued p.1 (pair x y) hz (pair (u + p.2) (v - p.2))) (t, t) := by
    apply analyticAt_regCarlsonRContinued_comp hz analyticAt_fst
    apply analyticAt_pi_iff.mpr
    intro i
    fin_cases i
    · exact analyticAt_const.add analyticAt_snd
    · exact analyticAt_const.sub analyticAt_snd
  rw [deriv_diagonal ha.differentiableAt]
  congr 1
  let g : ℂ → ℂ := fun s => regCarlsonRContinued t (pair x y) hz (pair (u + s) (v - s))
  have hg : DifferentiableAt ℂ g t := by
    apply AnalyticAt.differentiableAt
    apply analyticAt_regCarlsonRContinued_comp hz analyticAt_const
    apply analyticAt_pi_iff.mpr
    intro i
    fin_cases i
    · exact analyticAt_const.add analyticAt_id
    · exact analyticAt_const.sub analyticAt_id
  have h := hg.hasDerivAt.comp_of_eq 0
    ((hasDerivAt_const 0 t).add (hasDerivAt_id 0)) (by simp)
  simpa [regRParameterTransfer, g, Function.comp_def, add_assoc, sub_sub] using h.deriv.symm

/-- First quadratic identity with the full parameter-derivative correction. -/
theorem regEqualLContinued_firstQuadratic_deriv (t β x y : ℂ)
    (hz : FirstQuadraticDomain x y) :
    2 * regEqualLContinued (2 * t) x y hz.1 β =
      regCarlsonLContinued t (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) hz.2
        (pair (β + t) (1 / 2 - t)) +
      regRParameterTransfer t (β + t) (1 / 2 - t)
        (arithmeticMeanSq x y) (geometricMeanSq x y) hz.2 := by
  have h := (hasDerivAt_regEqualRContinued_L (2 * t) β x y hz.1).comp t
    ((hasDerivAt_id t).const_mul 2)
  have heq : (fun s => regEqualRContinued (2 * s) x y hz.1 β) =
      (fun s => regCarlsonRContinued s
        (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) hz.2
        (pair (β + s) (1 / 2 - s))) :=
    funext fun s => regEqualRContinued_firstQuadratic s β x y hz
  have hd := h.deriv
  change deriv (fun s => regEqualRContinued (2 * s) x y hz.1 β) t = _ at hd
  rw [heq, deriv_regRContinued_exponent_transfer] at hd
  simpa [mul_comm] using hd.symm

/-- Second quadratic identity with the full parameter-derivative correction. -/
theorem regEqualLContinued_secondQuadratic_deriv (t β x y : ℂ)
    (hz : SecondQuadraticDomain x y) :
    regEqualLContinued t (x ^ 2) (y ^ 2) hz.1 β =
      regCarlsonLContinued t (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) hz.2
        (pair (2 * β + t) (1 / 2 - β - t)) +
      regRParameterTransfer t (2 * β + t) (1 / 2 - β - t)
        (arithmeticMeanSq x y) (geometricMeanSq x y) hz.2 := by
  have heq : (fun s => regEqualRContinued s (x ^ 2) (y ^ 2) hz.1 β) =
      (fun s => regCarlsonRContinued s
        (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) hz.2
        (pair (2 * β + s) (1 / 2 - β - s))) :=
    funext fun s => regEqualRContinued_secondQuadratic s β x y hz
  change deriv (fun s => regEqualRContinued s (x ^ 2) (y ^ 2) hz.1 β) t = _
  rw [heq]
  exact deriv_regRContinued_exponent_transfer t (2 * β) (1 / 2 - β)
    (arithmeticMeanSq x y) (geometricMeanSq x y) hz.2

/-- Carlson (1987), (6.4), for all complex parameters, retaining removable values.
The second L-term is evaluated at the slit-plane ratio `A / G`. -/
theorem regEqualLContinued_firstQuadratic (t β x y : ℂ)
    (hz : FirstQuadraticDomain x y) :
    2 * regEqualLContinued (2 * t) x y hz.1 β =
      regCarlsonLSlit t (pair (β + t) (1 / 2 - t))
        (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) -
      geometricMeanSq x y ^ t * regCarlsonLSlit (-(β + t))
        (pair (-t) (β + 1 / 2 + t))
        (pair (arithmeticMeanSq x y / geometricMeanSq x y) 1) := by
  have h := regEqualLContinued_firstQuadratic_deriv t β x y hz
  rw [regRParameterTransfer_eq_neg_L,
    show β + t + (1 / 2 - t) + t = β + 1 / 2 + t by ring] at h
  rw [regCarlsonLSlit_eq_continued t _ hz.2]
  simpa only [sub_eq_add_neg] using h

/-- Carlson (1987), (6.5) with the first forms of (6.6) and (6.7), for all
complex parameters. No Gamma factor is cancelled in this normalization. -/
theorem regEqualLContinued_secondQuadratic (t β x y : ℂ)
    (hz : SecondQuadraticDomain x y) :
    regEqualLContinued t (x ^ 2) (y ^ 2) hz.1 β =
      regCarlsonLSlit t (pair (2 * β + t) (1 / 2 - β - t))
        (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) -
      geometricMeanSq x y ^ t * regCarlsonLSlit (-(2 * β + t))
        (pair (-t) (β + 1 / 2 + t))
        (pair (arithmeticMeanSq x y / geometricMeanSq x y) 1) := by
  have h := regEqualLContinued_secondQuadratic_deriv t β x y hz
  rw [regRParameterTransfer_eq_neg_L,
    show 2 * β + t + (1 / 2 - β - t) + t = β + 1 / 2 + t by ring] at h
  rw [regCarlsonLSlit_eq_continued t _ hz.2]
  simpa only [sub_eq_add_neg] using h

/-- The first quadratic transformation in ordinary normalization. Its finite-function
interpretation uses Carlson's domain `IsCarlsonGammaRegular (β + 1/2)`; the algebraic
identity also holds for the totalized values at genuine poles. -/
theorem equalLContinued_firstQuadratic (t β x y : ℂ)
    (hz : FirstQuadraticDomain x y) :
    2 * equalLContinued (2 * t) x y hz.1 β =
      carlsonLSlit t (pair (β + t) (1 / 2 - t))
        (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) -
      geometricMeanSq x y ^ t * carlsonLSlit (-(β + t))
        (pair (-t) (β + 1 / 2 + t))
        (pair (arithmeticMeanSq x y / geometricMeanSq x y) 1) := by
  have h := congrArg (fun w => Gamma (β + 1 / 2) * w)
    (regEqualLContinued_firstQuadratic t β x y hz)
  simp only [equalLContinued, carlsonLSlit, sum_pair]
  rw [show β + t + (1 / 2 - t) = β + 1 / 2 by ring,
    show -t + (β + 1 / 2 + t) = β + 1 / 2 by ring]
  linear_combination h

/-- The second quadratic transformation in ordinary normalization, with the same
genuine-pole convention as `equalLContinued_firstQuadratic`. -/
theorem equalLContinued_secondQuadratic (t β x y : ℂ)
    (hz : SecondQuadraticDomain x y) :
    equalLContinued t (x ^ 2) (y ^ 2) hz.1 β =
      carlsonLSlit t (pair (2 * β + t) (1 / 2 - β - t))
        (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) -
      geometricMeanSq x y ^ t * carlsonLSlit (-(2 * β + t))
        (pair (-t) (β + 1 / 2 + t))
        (pair (arithmeticMeanSq x y / geometricMeanSq x y) 1) := by
  have h := congrArg (fun w => Gamma (β + 1 / 2) * w)
    (regEqualLContinued_secondQuadratic t β x y hz)
  simp only [equalLContinued, carlsonLSlit, sum_pair]
  rw [show 2 * β + t + (1 / 2 - β - t) = β + 1 / 2 by ring,
    show -t + (β + 1 / 2 + t) = β + 1 / 2 by ring]
  linear_combination h

/-- At degree zero a sum-preserving parameter derivative vanishes. -/
@[simp] theorem regRParameterTransfer_zero (u v x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) :
    regRParameterTransfer 0 u v x y hz = 0 := by
  have heq : (fun s => regCarlsonRContinued 0 (pair x y) hz (pair (u + s) (v - s))) =
      (fun _ : ℂ => (Gamma (u + v))⁻¹) := by
    funext s
    rw [show (0 : ℂ) = (0 : ℕ) by norm_num, regCarlsonRContinued_natCast]
    simp only [regCarlsonR, regCarlsonRPolynomial_zero, sum_pair]
    congr 2
    ring
  unfold regRParameterTransfer
  rw [heq, deriv_const]

/-- Carlson (1987), first identity (6.8), with no Dirichlet parameter exclusions. -/
theorem regEqualLContinued_firstQuadratic_zero (β x y : ℂ)
    (hz : FirstQuadraticDomain x y) :
    2 * regEqualLContinued 0 x y hz.1 β =
      regCarlsonLContinued 0 (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) hz.2
        (pair β (1 / 2)) := by
  simpa using regEqualLContinued_firstQuadratic_deriv 0 β x y hz

/-- Carlson (1987), second identity (6.8), with no Dirichlet parameter exclusions. -/
theorem regEqualLContinued_secondQuadratic_zero (β x y : ℂ)
    (hz : SecondQuadraticDomain x y) :
    regEqualLContinued 0 (x ^ 2) (y ^ 2) hz.1 β =
      regCarlsonLContinued 0 (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) hz.2
        (pair (2 * β) (1 / 2 - β)) := by
  simpa using regEqualLContinued_secondQuadratic_deriv 0 β x y hz

end DirichletTransform.TwoVariable

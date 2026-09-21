/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.Quadratic
public import LeanPool.CarlsonFunctions.Carlson.R.JointParameter

/-!
# Quadratic transformations on the full Dirichlet parameter domain

The regularized transformations are entire identities in `(t, β)`. The entire Gamma ratio
below, rather than a quotient evaluated at Gamma poles, implements Legendre duplication.
Node domains are unchanged from the native transformation theorems.
`EqualParameter` supplies the canonical ordinary continuation, retaining the removable
values at nonpositive integral `β` where the entire ratio here vanishes.
-/

open Complex ProbabilityTheory Filter Set
open scoped Classical Topology
@[expose] public noncomputable section
namespace DirichletTransform.TwoVariable

/-- Entire extension of `Γ(β + 1/2) / Γ(2β)`. The formula remains meaningful at Gamma poles. -/
def quadraticGammaRatio (β : ℂ) : ℂ :=
  (2 : ℂ) ^ (1 - 2 * β) * (Real.sqrt Real.pi : ℂ) * (Gamma β)⁻¹

/-- Legendre's duplication ratio is entire. -/
theorem analyticOnNhd_quadraticGammaRatio : AnalyticOnNhd ℂ quadraticGammaRatio univ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  have he : Differentiable ℂ (fun β : ℂ => 1 - 2 * β) :=
    (differentiable_const (1 : ℂ)).sub ((differentiable_const (2 : ℂ)).mul differentiable_id)
  have hp : Differentiable ℂ (fun β : ℂ => (2 : ℂ) ^ (1 - 2 * β)) :=
    fun β => (he β).const_cpow (Or.inl two_ne_zero)
  exact ((hp.mul_const (Real.sqrt Real.pi : ℂ)).mul differentiable_one_div_Gamma).differentiableOn

/-- Duplication converts the native normalization into the equal-parameter normalization. -/
theorem Gamma_mul_quadraticGammaRatio {β : ℂ} (hβ : 0 < β.re) :
    Gamma (β + β) * quadraticGammaRatio β = Gamma (β + 1 / 2) := by
  have hG := Gamma_ne_zero_of_re_pos hβ
  apply (mul_right_cancel₀ hG)
  dsimp [quadraticGammaRatio]
  rw [show β + β = 2 * β by ring]
  have H := Gamma_mul_Gamma_add_half β
  calc
    _ = Gamma (2 * β) * (2 : ℂ) ^ (1 - 2 * β) * (Real.sqrt Real.pi : ℂ) := by
      field_simp
    _ = _ := by linear_combination -H

private lemma analyticAt_coordinate (p : Fin 2 → ℂ) (i : Fin 2) :
    AnalyticAt ℂ (fun q : Fin 2 → ℂ => q i) p :=
  (ContinuousLinearMap.proj i : (Fin 2 → ℂ) →L[ℂ] ℂ).analyticAt p

/-- Permanence of functional relations in the two complex parameters. -/
private theorem quadratic_parameter_identity
    (l : ℂ → ℂ) (r : ℂ → ℂ → Fin 2 → ℂ)
    (hl : AnalyticOnNhd ℂ l univ)
    (hr : AnalyticOnNhd ℂ (fun p : Fin 2 → ℂ => r (p 0) (p 1)) univ)
    (hseed : r 0 (1 / 4) ∈ mvBetaConvergent)
    (hsum : ∀ t β, ∑ i, r t β i = β + 1 / 2)
    (z Z : Fin 2 → ℂ) (hz : z ∈ carlsonRVariableDomain) (hZ : Z ∈ carlsonRVariableDomain)
    (hnative : ∀ t β, pair β β ∈ mvBetaConvergent → r t β ∈ mvBetaConvergent →
      carlsonRIntegral (l t) (pair β β) z = carlsonRIntegral t (r t β) Z)
    (t β : ℂ) :
    regCarlsonRContinued (l t) z hz (pair β β) =
      quadraticGammaRatio β * regCarlsonRContinued t Z hZ (r t β) := by
  let L : (Fin 2 → ℂ) → ℂ := fun p => regCarlsonRContinued (l (p 0)) z hz (pair (p 1) (p 1))
  let R : (Fin 2 → ℂ) → ℂ := fun p => quadraticGammaRatio (p 1) *
    regCarlsonRContinued (p 0) Z hZ (r (p 0) (p 1))
  have hleft : AnalyticOnNhd ℂ L univ := by
    intro p _
    apply analyticAt_regCarlsonRContinued_comp hz
    · exact (hl _ (mem_univ _)).comp (analyticAt_coordinate p 0)
    · apply analyticAt_pi_iff.mpr
      intro i; fin_cases i <;> exact (analyticAt_coordinate p 1)
  have hright : AnalyticOnNhd ℂ R univ := by
    intro p _
    apply AnalyticAt.mul
    · exact (analyticOnNhd_quadraticGammaRatio _ (mem_univ _)).comp
        (analyticAt_coordinate p 1)
    · exact analyticAt_regCarlsonRContinued_comp hZ
        (analyticAt_coordinate p 0) (hr p (mem_univ _))
  let o := pair (0 : ℂ) (1 / 4)
  have hbc : ContinuousAt (fun p : Fin 2 → ℂ => pair (p 1) (p 1)) o := by
    apply continuousAt_pi.mpr
    intro i; fin_cases i <;> exact (continuous_apply 1).continuousAt
  have hbl := hbc.tendsto.eventually (isOpen_mvBetaConvergent.mem_nhds (by
    intro i; fin_cases i <;> norm_num [o, pair]))
  have hbr := (hr o (mem_univ _)).continuousAt.tendsto.eventually
    (isOpen_mvBetaConvergent.mem_nhds hseed)
  have hevent : L =ᶠ[𝓝 o] R := by
    filter_upwards [hbl, hbr] with p hbp hrp
    dsimp [L, R]
    rw [regCarlsonRContinued_eq_integral _ hz hbp, regCarlsonRContinued_eq_integral _ hZ hrp]
    have hβ : 0 < (p 1).re := hbp 0
    have htotal : 0 < (p 1 + p 1).re := by simpa using add_pos hβ hβ
    apply mul_left_cancel₀ (Gamma_ne_zero_of_re_pos htotal)
    rw [← mul_assoc, Gamma_mul_quadraticGammaRatio hβ]
    have H := hnative (p 0) (p 1) hbp hrp
    simpa only [carlsonRIntegral, sum_pair, hsum] using H
  exact congrFun (hleft.eq_of_eventuallyEq hright hevent) (pair t β)

/-- First quadratic transformation, entire in both parameters, including exceptional
Gamma parameters. There are no convergence or non-pole hypotheses. -/
theorem regRContinued_firstQuadratic (t β x y : ℂ) (hz : FirstQuadraticDomain x y) :
    regCarlsonRContinued (2 * t) (pair x y) hz.1 (pair β β) =
      quadraticGammaRatio β * regCarlsonRContinued t
        (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) hz.2
        (pair (β + t) (1 / 2 - t)) := by
  apply quadratic_parameter_identity (fun t => 2 * t) (fun t β => pair (β + t) (1 / 2 - t))
  · exact analyticOnNhd_const.mul analyticOnNhd_id
  · intro p _
    apply analyticAt_pi_iff.mpr
    intro i; fin_cases i
    · exact (analyticAt_coordinate p 1).add (analyticAt_coordinate p 0)
    · exact analyticAt_const.sub (analyticAt_coordinate p 0)
  · intro i; fin_cases i <;> norm_num [pair]
  · intro t β; simp only [sum_pair]; ring
  · exact fun t β hb hr => rIntegral_firstQuadratic t β x y hb hr hz

/-- Second quadratic transformation, entire in both parameters. -/
theorem regRContinued_secondQuadratic (t β x y : ℂ) (hz : SecondQuadraticDomain x y) :
    regCarlsonRContinued t (pair (x ^ 2) (y ^ 2)) hz.1 (pair β β) =
      quadraticGammaRatio β * regCarlsonRContinued t
        (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) hz.2
        (pair (2 * β + t) (1 / 2 - β - t)) := by
  apply quadratic_parameter_identity id (fun t β => pair (2 * β + t) (1 / 2 - β - t))
  · exact analyticOnNhd_id
  · intro p _
    apply analyticAt_pi_iff.mpr
    intro i; fin_cases i
    · exact (analyticAt_const.mul (analyticAt_coordinate p 1)).add
        (analyticAt_coordinate p 0)
    · exact (analyticAt_const.sub (analyticAt_coordinate p 1)).sub
        (analyticAt_coordinate p 0)
  · intro i; fin_cases i <;> norm_num [pair]
  · intro t β; simp only [sum_pair]; ring
  · exact fun t β hb hr => rIntegral_secondQuadratic t β x y hb hr hz

end DirichletTransform.TwoVariable
end

/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.PicardFuchs
import LeanPool.Chudnovsky.Estimates
import LeanPool.Chudnovsky.Ramanujan
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Kummer's solution of the Picard–Fuchs equation

This file covers chapter 8 of Milla's proof of the Chudnovsky formula (arXiv:1809.00533v6,
`130_Kummer.tex`).

## Main definitions

* `Chudnovsky.kummerB` : Kummer's solution
  `b(J) = J^(-1/4) · (1-J)^(1/4) · ₂F₁(1/12, 5/12; 1; 1/J)` (paper Thm. `satzbj`), realized
  with principal-branch `cpow`. (The paper allows an arbitrary fixed branch of the fourth
  roots; since the Picard–Fuchs equation is homogeneous the choice is immaterial there.)

## Main statements (all proved)

* `Chudnovsky.kummerB_satisfiesPicardFuchs` : `b(J)` solves the Picard–Fuchs equation
  (paper Thm. `satzbj`). The paper states this for all `|J| > 1`; with the principal branch
  we must additionally stay off the branch cuts, i.e. off the real axis (for `J` real with
  `|J| > 1` either `J` or `1 - J` is a negative real).
* `Chudnovsky.norm_inv_J_lt_one` : `1/J(τ)` lies in the unit disc on `Region` (from
  `Estimates.lean`'s `one_lt_norm_J`), so that the hypergeometric series converges.
* `Chudnovsky.E₄_eq_hyp2F1_pow_four` : the chapter's output `omegastrich`, in the branch-free
  fourth-power form recommended by PLAN A7:
  `E₄(τ) = (₂F₁(1/12, 5/12; 1; 1/J(τ)))⁴` for `τ ∈ Region`, proved by the Wronskian
  comparison argument described in the section `OmegaStrich` below (using Ramanujan's
  derivative identities from `Ramanujan.lean` in place of the paper's period integrals).

## Faithfulness note on `omegastrich`

The paper's Thm. `omegastrich` reads
`Δ(τ)^(1/12) = (2π / 12^(1/4)) · J(τ)^(-1/12) · ₂F₁(1/12, 5/12; 1; 1/J(τ))`,
with all roots determined only up to roots of unity until the Main Theorem's connectedness
argument (paper Remark `bemwurzel`); here `Δ` is the *lattice* discriminant
`g₂³ - 27g₃² = (2π)¹² · Δ_Mathlib`. Raising to the 12th power and using
`1728·J = E₄³/Δ_Mathlib` (`Chudnovsky.mul_J_eq`) gives the branch-free equivalent
`E₄³ = F¹²`; the classical (and correct on `Region`) branch refinement is `E₄ = F⁴`, which is
what chapter 9 consumes after the PLAN A7 reformulation. TODO: if the final assembly of
`MainTheorem.lean` turns out to need the literal `Δ^(1/12)` statement (it uses `ωtilde₁ = Δ^(1/12)`
only through `F` and `dF/dJ`), add it here with an explicit principal-branch bookkeeping.
-/

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex ModularForm

/-- **Kummer's solution** `b(J) = J^(-1/4) · (1-J)^(1/4) · ₂F₁(1/12, 5/12; 1; 1/J)` of the
Picard–Fuchs equation (paper Thm. `satzbj`), taken with principal-branch complex powers. -/
def kummerB (z : ℂ) : ℂ :=
  z ^ (-(1 / 4) : ℂ) * (1 - z) ^ ((1 / 4) : ℂ) * hyp2F1 z⁻¹

/-- The hypergeometric function `hyp2F1 = ₂F₁(1/12, 5/12; 1; ·)` is analytic on the open unit
disc, being the sum of its power series (whose radius of convergence is `1`). -/
private theorem hyp2F1_analyticAt {w : ℂ} (hw : ‖w‖ < 1) : AnalyticAt ℂ hyp2F1 w := by
  have habc : ∀ kn : ℕ, (kn : ℂ) ≠ -(1 / 12 : ℂ) ∧ (kn : ℂ) ≠ -(5 / 12 : ℂ) ∧ (kn : ℂ) ≠ -1 := by
    intro kn
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have h0 : ((12 * kn + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination 12 * h
      rw [Nat.cast_eq_zero] at h0; omega
    · have h0 : ((12 * kn + 5 : ℕ) : ℂ) = 0 := by push_cast; linear_combination 12 * h
      rw [Nat.cast_eq_zero] at h0; omega
    · have h0 : ((kn + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination h
      rw [Nat.cast_eq_zero] at h0; omega
  have hrad : (ordinaryHypergeometricSeries ℂ (1 / 12 : ℂ) (5 / 12) 1).radius = 1 :=
    ordinaryHypergeometricSeries_radius_eq_one ℂ (a := 1 / 12) (b := 5 / 12) (c := 1) habc
  have hfps := (ordinaryHypergeometricSeries ℂ (1 / 12 : ℂ) (5 / 12) 1).hasFPowerSeriesOnBall
    (by rw [hrad]; exact one_pos)
  rw [hrad] at hfps
  have hmem : w ∈ Metric.eball (0 : ℂ) 1 := by
    rw [mem_eball_zero_iff, show ‖w‖ₑ = (‖w‖₊ : ENNReal) from rfl]; exact_mod_cast hw
  exact hfps.analyticAt_of_mem hmem

/-- Paper Thm. `satzbj`: Kummer's function `b(J)` solves the Picard–Fuchs differential
equation on `|J| > 1`.

TODO: the paper's statement holds for `|J| > 1` with *any* fixed branch of the fourth roots;
with the principal branch (`Complex.cpow`) we restrict to the complement of the real axis,
where both `z ↦ z^(-1/4)` and `z ↦ (1-z)^(1/4)` are holomorphic (`J` real with `|J| > 1`
makes `J` or `1 - J` a negative real, i.e. lie on the principal branch cut). -/
theorem kummerB_satisfiesPicardFuchs :
    SatisfiesPicardFuchs kummerB {z : ℂ | 1 < ‖z‖ ∧ z.im ≠ 0} := by
  intro z hz
  obtain ⟨hznorm, hzim⟩ := hz
  -- Basic numerical facts on the region `S = {1 < ‖z‖, im z ≠ 0}`.
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hznorm; exact absurd hznorm (by norm_num)
  have hz1 : z ≠ 1 := by
    intro h; rw [h, norm_one] at hznorm; exact absurd hznorm (lt_irrefl 1)
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz1)
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.2 hz1
  have hslitz : z ∈ Complex.slitPlane := Or.inr hzim
  have h1zim : (1 - z).im ≠ 0 := by
    rw [Complex.sub_im, Complex.one_im, zero_sub]; exact neg_ne_zero.2 hzim
  have hslit1z : (1 - z) ∈ Complex.slitPlane := Or.inr h1zim
  have huw : ‖z⁻¹‖ < 1 := by
    rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hznorm
  -- Differentiability of `hyp2F1` and of `deriv hyp2F1` on the open unit disc.
  have hHD1 : ∀ v : ℂ, ‖v‖ < 1 → HasDerivAt hyp2F1 (deriv hyp2F1 v) v :=
    fun v hv => (hyp2F1_analyticAt hv).differentiableAt.hasDerivAt
  have hHD2 : ∀ v : ℂ, ‖v‖ < 1 → HasDerivAt (deriv hyp2F1) (deriv (deriv hyp2F1) v) v :=
    fun v hv => (hyp2F1_analyticAt hv).deriv.differentiableAt.hasDerivAt
  -- The hypergeometric ODE for `hyp2F1` at `u = z⁻¹` (paper eq. `tmp1`).
  have hc : ∀ k : ℕ, (k : ℂ) ≠ -(1 : ℂ) := by
    intro k h
    have h0 : ((k + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination h
    rw [Nat.cast_eq_zero] at h0; omega
  have hODE := ordinaryHypergeometric_ode (1 / 12) (5 / 12) 1 hc huw
  rw [show (fun w : ℂ => ₂F₁ (1 / 12 : ℂ) (5 / 12) 1 w) = hyp2F1 from rfl,
    show ₂F₁ (1 / 12 : ℂ) (5 / 12) 1 z⁻¹ = hyp2F1 z⁻¹ from rfl] at hODE
  -- Solve the ODE for the second derivative `F''(u)`.
  have hinv1 : z⁻¹ - 1 ≠ 0 := by
    rw [sub_ne_zero]; intro h; exact hz1 (by rw [← inv_inv z, h, inv_one])
  have hden : z⁻¹ * (z⁻¹ - 1) ≠ 0 := mul_ne_zero (inv_ne_zero hz0) hinv1
  have hF2 : deriv (deriv hyp2F1) z⁻¹
      = -(((1 / 12 + 5 / 12 + 1) * z⁻¹ - 1) * deriv hyp2F1 z⁻¹ + 1 / 12 * (5 / 12) * hyp2F1 z⁻¹)
          / (z⁻¹ * (z⁻¹ - 1)) := by
    rw [eq_div_iff hden]; linear_combination hODE
  -- The first-derivative function `D1 = (deriv kummerB)` in reduced form.
  set D1 : ℂ → ℂ := fun w =>
      -(1 / 4 : ℂ) * (w ^ (-(1 / 4) : ℂ) * w⁻¹) * (1 - w) ^ (1 / 4 : ℂ) * hyp2F1 w⁻¹
    + w ^ (-(1 / 4) : ℂ) * (-(1 / 4 : ℂ) * ((1 - w) ^ (1 / 4 : ℂ) * (1 - w)⁻¹)) * hyp2F1 w⁻¹
    + w ^ (-(1 / 4) : ℂ) * (1 - w) ^ (1 / 4 : ℂ) * (deriv hyp2F1 w⁻¹ * (-(w ^ 2)⁻¹)) with hD1def
  -- `HasDerivAt kummerB (D1 w) w` at every point of the region.
  have hderivKummer : ∀ w : ℂ, w ∈ {z : ℂ | 1 < ‖z‖ ∧ z.im ≠ 0} →
      deriv kummerB w = D1 w := by
    intro w hw
    obtain ⟨hwn, hwim⟩ := hw
    have hw0 : w ≠ 0 := by
      intro h; rw [h, norm_zero] at hwn; exact absurd hwn (by norm_num)
    have hw1 : w ≠ 1 := by
      intro h; rw [h, norm_one] at hwn; exact lt_irrefl 1 hwn
    have hwslit : w ∈ Complex.slitPlane := Or.inr hwim
    have hw1im : (1 - w).im ≠ 0 := by
      rw [Complex.sub_im, Complex.one_im, zero_sub]; exact neg_ne_zero.2 hwim
    have hw1slit : (1 - w) ∈ Complex.slitPlane := Or.inr hw1im
    have hwuw : ‖w⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hwn
    have hP := (hasDerivAt_id w).cpow_const (c := (-(1 / 4) : ℂ)) hwslit
    have hQ := ((hasDerivAt_id w).const_sub (1 : ℂ)).cpow_const (c := (1 / 4 : ℂ)) hw1slit
    have hG := (hHD1 w⁻¹ hwuw).comp w (hasDerivAt_inv hw0)
    have eZ1 : w ^ (-(1 / 4) - 1 : ℂ) = w ^ (-(1 / 4) : ℂ) * w⁻¹ := by
      rw [Complex.cpow_sub _ _ hw0, Complex.cpow_one, div_eq_mul_inv]
    have eW1 : (1 - w) ^ (1 / 4 - 1 : ℂ) = (1 - w) ^ (1 / 4 : ℂ) * (1 - w)⁻¹ := by
      rw [Complex.cpow_sub _ _ (sub_ne_zero.2 (Ne.symm hw1)), Complex.cpow_one, div_eq_mul_inv]
    have h : HasDerivAt kummerB _ w := (hP.mul hQ).mul hG
    rw [h.deriv]
    simp only [hD1def, id_eq, Pi.mul_apply]
    rw [eZ1, eW1]; ring
  -- The region is open, hence a neighbourhood of `z`, so we may differentiate `D1` again.
  have hSopen : IsOpen {z : ℂ | 1 < ‖z‖ ∧ z.im ≠ 0} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_ne.preimage Complex.continuous_im)
  have hSnhds : {z : ℂ | 1 < ‖z‖ ∧ z.im ≠ 0} ∈ nhds z := hSopen.mem_nhds ⟨hznorm, hzim⟩
  have heqEv : deriv kummerB =ᶠ[nhds z] D1 :=
    Filter.eventuallyEq_of_mem hSnhds (fun w hw => hderivKummer w hw)
  -- Second-derivative building blocks at `z`.
  have hPz := (hasDerivAt_id z).cpow_const (c := (-(1 / 4) : ℂ)) hslitz
  have hIz := hasDerivAt_inv hz0
  have hQz := ((hasDerivAt_id z).const_sub (1 : ℂ)).cpow_const (c := (1 / 4 : ℂ)) hslit1z
  have hWz := (hasDerivAt_inv h1z).comp z ((hasDerivAt_id z).const_sub (1 : ℂ))
  have hGz := (hHD1 z⁻¹ huw).comp z (hasDerivAt_inv hz0)
  have hGdz := (hHD2 z⁻¹ huw).comp z (hasDerivAt_inv hz0)
  have hSz := ((hasDerivAt_inv (pow_ne_zero 2 hz0)).comp z (hasDerivAt_pow 2 z)).neg
  -- Assemble `HasDerivAt D1 _ z` term by term.
  have hPI := hPz.mul hIz
  have ht1 := ((hPI.const_mul (-(1 / 4) : ℂ)).mul hQz).mul hGz
  have hQW := hQz.mul hWz
  have ht2 := (hPz.mul (hQW.const_mul (-(1 / 4) : ℂ))).mul hGz
  have hPQ := hPz.mul hQz
  have hGdS := hGdz.mul hSz
  have ht3 := hPQ.mul hGdS
  have hHD_D1 : HasDerivAt D1 _ z := (ht1.add ht2).add ht3
  -- cpow reductions at `z`.
  have eZ1z : z ^ (-(1 / 4) - 1 : ℂ) = z ^ (-(1 / 4) : ℂ) * z⁻¹ := by
    rw [Complex.cpow_sub _ _ hz0, Complex.cpow_one, div_eq_mul_inv]
  have eW1z : (1 - z) ^ (1 / 4 - 1 : ℂ) = (1 - z) ^ (1 / 4 : ℂ) * (1 - z)⁻¹ := by
    rw [Complex.cpow_sub _ _ h1z, Complex.cpow_one, div_eq_mul_inv]
  -- Rewrite the Picard–Fuchs expression and finish by the ODE substitution.
  rw [heqEv.deriv_eq, hderivKummer z ⟨hznorm, hzim⟩, hHD_D1.deriv]
  simp only [hD1def, kummerB, id_eq, Pi.mul_apply, Pi.neg_apply, Function.comp_apply]
  rw [eZ1z, eW1z, hF2]
  field_simp
  ring

/-- On `Region`, the argument `1/J(τ)` of the hypergeometric function lies in the open unit
disc (via `Estimates.lean`'s `one_lt_norm_J`). -/
theorem norm_inv_J_lt_one {τ : ℍ} (hτ : τ ∈ Region) : ‖(J τ)⁻¹‖ < 1 := by
  rw [norm_inv]
  exact inv_lt_one_of_one_lt₀ (one_lt_norm_J hτ)

/-! ### The branch-free `omegastrich`: `E₄ = ₂F₁(1/12, 5/12; 1; 1/J)⁴` on `Region`

The proof follows the "differentiate and compare" strategy of PLAN A7, in a *Wronskian*
form that needs no quantitative estimates near `i∞`:

1. Near `i∞`, the hypergeometric pair `(X, Y) = (F(1/J), F′(1/J))` (with
   `F = ₂F₁(1/12, 5/12; 1; ·)`) and the modular pair
   `(Xtilde, Ytilde) = (E₄^{1/4}, E₄^{1/4}·E₄³·(E₂E₄-E₆)/(12·(E₄³-E₆²)·E₆))` both solve the same
   linear 2×2 system `D Z = M(τ)·Z`: the first by the hypergeometric ODE and the chain
   rule with `D (1/J) = (1/J)·E₆/E₄` (from Ramanujan's identities), the second again by
   Ramanujan's identities.  Here `M₁₂ = (1/J)E₆/E₄`, `M₂₁ = (5/144)E₄²/E₆`,
   `M₂₂ = ((3/2)(1/J) - 1)·E₄²/E₆`, and the principal branch `E₄^{1/4}` is harmless
   since `E₄ ≈ 1` near `i∞`.
2. The Wronskian `w = XYtilde - YXtilde` solves the scalar ODE `D w = M₂₂·w` where `M₂₂ → -1`
   at `i∞`.  Along each vertical line `t ↦ x₀ + it` the function `t ↦ ‖w‖²·e^{-2πt}` is
   monotone nondecreasing (as soon as `Re M₂₂ ≤ -1/2`), while `w → 0` at `i∞` (both
   pairs converge to `(1, 5/144)`); hence `w ≡ 0`.
3. `w ≡ 0` forces `(Xtilde/X)′ = 0`, so `Xtilde/X` is constant `= 1` (its limit at `i∞`) on
   `{Im τ > A}`, whence `E₄ = Xtilde⁴ = X⁴` there — no fourth-root ambiguity survives the
   fourth power.
4. The identity spreads to all of `Region` by the identity theorem
   (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` on the half-plane
   `{5/4 < Im z}`, on which both sides are holomorphic since `‖J‖ > 1` there).

The only limit that is not pure soft analysis is `Ytilde → 5/144`, and even it needs no new
estimates: by `D E₄ = q·Φ′(q)` (`normalizedDeriv_eq_q_mul_deriv_cuspFunction`) with
`Φ′(0) = 240` (`E₄_qExpansion_coeff_one`), and `Δ/q = kfun → 1` (from `lemk`),
`(E₂E₄-E₆)/(E₄³-E₆²) = 3qΦ′(q)/(1728·q·kfun) → 720/1728 = 5/12`. -/

section OmegaStrich

open Filter Function EisensteinSeries Derivative SlashInvariantForm

open scoped Real Topology MatrixGroups CongruenceSubgroup ModularForm Manifold
  InnerProductSpace

private instance : Fact (IsCusp OnePoint.infty 𝒮ℒ) :=
  ⟨(𝒮ℒ).isCusp_of_mem_strictPeriods one_pos one_mem_strictPeriods_SL⟩

/-! #### The two solution pairs, at the level of `ℂ` -/

/-- The hypergeometric solution `X = F(1/J)`. -/
private def XhC : ℂ → ℂ := fun z => hyp2F1 (J (ofComplex z))⁻¹

/-- Its companion `Y = F′(1/J)`. -/
private def YhC : ℂ → ℂ := fun z => deriv hyp2F1 (J (ofComplex z))⁻¹

/-- The modular solution `Xtilde = E₄^{1/4}` (principal branch). -/
private def XtC : ℂ → ℂ := fun z => E₄ (ofComplex z) ^ (1 / 4 : ℂ)

/-- Its companion `Ytilde = E₄^{1/4}·E₄³·(E₂E₄-E₆) / (12·(E₄³-E₆²)·E₆)`, the unique modular
expression with `D Xtilde = M₁₂·Ytilde`. -/
private def YtC : ℂ → ℂ := fun z =>
  E₄ (ofComplex z) ^ (1 / 4 : ℂ) * E₄ (ofComplex z) ^ 3
    * (E2 (ofComplex z) * E₄ (ofComplex z) - E₆ (ofComplex z))
    / (12 * (E₄ (ofComplex z) ^ 3 - E₆ (ofComplex z) ^ 2) * E₆ (ofComplex z))

/-- The Wronskian `w = X·Ytilde - Y·Xtilde` of the two pairs. -/
private def WrC : ℂ → ℂ := fun z => XhC z * YtC z - YhC z * XtC z

/-- The lower-right entry `M₂₂ = ((3/2)(1/J) - 1)·E₄²/E₆` of the coefficient matrix. -/
private def m22 (τ : ℍ) : ℂ := (3 / 2 * (J τ)⁻¹ - 1) * (E₄ τ ^ 2 / E₆ τ)

private lemma XhC_apply (τ : ℍ) : XhC ↑τ = hyp2F1 (J τ)⁻¹ := by
  simp only [XhC, ofComplex_apply]

private lemma YhC_apply (τ : ℍ) : YhC ↑τ = deriv hyp2F1 (J τ)⁻¹ := by
  simp only [YhC, ofComplex_apply]

private lemma XtC_apply (τ : ℍ) : XtC ↑τ = E₄ τ ^ (1 / 4 : ℂ) := by
  simp only [XtC, ofComplex_apply]

private lemma YtC_apply (τ : ℍ) :
    YtC ↑τ = E₄ τ ^ (1 / 4 : ℂ) * E₄ τ ^ 3 * (E2 τ * E₄ τ - E₆ τ)
      / (12 * (E₄ τ ^ 3 - E₆ τ ^ 2) * E₆ τ) := by
  simp only [YtC, ofComplex_apply]

private lemma WrC_apply (τ : ℍ) : WrC ↑τ = XhC ↑τ * YtC ↑τ - YhC ↑τ * XtC ↑τ := rfl

/-! #### Elementary algebra around `1/J` -/

/-- `1/J = (E₄³ - E₆²)/E₄³`, unconditionally (`inv_div`; both sides are `0` if `E₄ = 0`). -/
private lemma inv_J_eq (τ : ℍ) : (J τ)⁻¹ = (E₄ τ ^ 3 - E₆ τ ^ 2) / E₄ τ ^ 3 := by
  rw [J, inv_div]

private lemma J_ne_zero {τ : ℍ} (h4 : E₄ τ ≠ 0) : J τ ≠ 0 :=
  div_ne_zero (pow_ne_zero 3 h4) (E₄_cube_sub_E₆_sq_ne_zero τ)

private lemma inv_J_sub_one {τ : ℍ} (h4 : E₄ τ ≠ 0) :
    (J τ)⁻¹ - 1 = -(E₆ τ ^ 2) / E₄ τ ^ 3 := by
  rw [inv_J_eq, div_sub_one (pow_ne_zero 3 h4)]
  congr 1
  ring

/-! #### Derivatives of the Eisenstein series at the `ℂ`-level

These repackage the Ramanujan identities `deriv_comp_ofComplex_E2/E₄/E₆` as `HasDerivAt`
statements for the compositions with `ofComplex`, ready for the chain rule. -/

private lemma hasDerivAt_E₄C (τ : ℍ) :
    HasDerivAt (fun z => E₄ (ofComplex z))
      (2 * ↑π * Complex.I / 3 * (E2 τ * E₄ τ - E₆ τ)) ↑τ := by
  have h := (mdifferentiableAt_iff.mp (ModularFormClass.holo E₄ τ)).hasDerivAt
  rw [deriv_comp_ofComplex_E₄] at h
  exact h

private lemma hasDerivAt_E₆C (τ : ℍ) :
    HasDerivAt (fun z => E₆ (ofComplex z))
      (↑π * Complex.I * (E2 τ * E₆ τ - E₄ τ ^ 2)) ↑τ := by
  have h := (mdifferentiableAt_iff.mp (ModularFormClass.holo E₆ τ)).hasDerivAt
  rw [deriv_comp_ofComplex_E₆] at h
  exact h

private lemma hasDerivAt_E2C (τ : ℍ) :
    HasDerivAt (fun z => E2 (ofComplex z))
      (↑π * Complex.I / 6 * (E2 τ ^ 2 - E₄ τ)) ↑τ := by
  have h := (mdifferentiableAt_iff.mp (E2_mdifferentiable τ)).hasDerivAt
  rw [deriv_comp_ofComplex_E2] at h
  exact h

/-- `D (1/J) = (1/J)·E₆/E₄` (2πi-normalized), i.e. the raw derivative of `z ↦ 1/J`. -/
private lemma hasDerivAt_invJ (τ : ℍ) (h4 : E₄ τ ≠ 0) :
    HasDerivAt (fun z => (J (ofComplex z))⁻¹)
      (2 * ↑π * Complex.I * ((J τ)⁻¹ * (E₆ τ / E₄ τ))) ↑τ := by
  have hB : E₄ τ ^ 3 - E₆ τ ^ 2 ≠ 0 := E₄_cube_sub_E₆_sq_ne_zero τ
  have hfun : (fun z => (J (ofComplex z))⁻¹)
      = fun z => (E₄ (ofComplex z) ^ 3 - E₆ (ofComplex z) ^ 2) / E₄ (ofComplex z) ^ 3 := by
    funext z
    exact inv_J_eq (ofComplex z)
  rw [hfun]
  have hnum := ((hasDerivAt_E₄C τ).pow 3).sub ((hasDerivAt_E₆C τ).pow 2)
  have hden := (hasDerivAt_E₄C τ).pow 3
  have hden0 : E₄ (ofComplex ↑τ) ^ 3 ≠ 0 := by
    rw [ofComplex_apply]
    exact pow_ne_zero 3 h4
  have hq : HasDerivAt
      (fun z => (E₄ (ofComplex z) ^ 3 - E₆ (ofComplex z) ^ 2) / E₄ (ofComplex z) ^ 3) _ ↑τ :=
    hnum.div hden hden0
  convert hq using 1
  simp only [Pi.pow_apply, Pi.sub_apply, ofComplex_apply]
  rw [inv_J_eq]
  field_simp
  ring

/-! #### The linear 2×2 system satisfied by both pairs -/

/-- `D X = M₁₂·Y` for the hypergeometric pair (chain rule). -/
private lemma hasDerivAt_XhC (τ : ℍ) (h4 : E₄ τ ≠ 0) (hu : ‖(J τ)⁻¹‖ < 1) :
    HasDerivAt XhC (2 * ↑π * Complex.I * ((J τ)⁻¹ * (E₆ τ / E₄ τ)) * YhC ↑τ) ↑τ := by
  have hpt : (J (ofComplex ↑τ))⁻¹ = (J τ)⁻¹ := by rw [ofComplex_apply]
  have hF : HasDerivAt hyp2F1 (deriv hyp2F1 (J τ)⁻¹) ((J (ofComplex ↑τ))⁻¹) := by
    rw [hpt]
    exact (hyp2F1_analyticAt hu).differentiableAt.hasDerivAt
  have h : HasDerivAt XhC _ ↑τ := hF.comp (↑τ : ℂ) (hasDerivAt_invJ τ h4)
  convert h using 1
  rw [YhC_apply]
  ring

/-- `D Y = M₂₁·X + M₂₂·Y` for the hypergeometric pair (chain rule plus the
hypergeometric ODE `ordinaryHypergeometric_ode` at `u = 1/J`). -/
private lemma hasDerivAt_YhC (τ : ℍ) (h4 : E₄ τ ≠ 0) (h6 : E₆ τ ≠ 0)
    (hu : ‖(J τ)⁻¹‖ < 1) :
    HasDerivAt YhC (2 * ↑π * Complex.I *
      (5 / 144 * (E₄ τ ^ 2 / E₆ τ) * XhC ↑τ + m22 τ * YhC ↑τ)) ↑τ := by
  have hB : E₄ τ ^ 3 - E₆ τ ^ 2 ≠ 0 := E₄_cube_sub_E₆_sq_ne_zero τ
  have hJ : J τ ≠ 0 := J_ne_zero h4
  have hpt : (J (ofComplex ↑τ))⁻¹ = (J τ)⁻¹ := by rw [ofComplex_apply]
  have hF2at : HasDerivAt (deriv hyp2F1) (deriv (deriv hyp2F1) (J τ)⁻¹)
      ((J (ofComplex ↑τ))⁻¹) := by
    rw [hpt]
    exact (hyp2F1_analyticAt hu).deriv.differentiableAt.hasDerivAt
  have h : HasDerivAt YhC _ ↑τ := hF2at.comp (↑τ : ℂ) (hasDerivAt_invJ τ h4)
  -- the hypergeometric ODE at `u = 1/J`, solved for the second derivative
  have hc : ∀ k : ℕ, (k : ℂ) ≠ -(1 : ℂ) := by
    intro k hk
    have h0 : ((k + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination hk
    rw [Nat.cast_eq_zero] at h0
    omega
  have hODE := ordinaryHypergeometric_ode (1 / 12) (5 / 12) 1 hc hu
  rw [show (fun w : ℂ => ₂F₁ (1 / 12 : ℂ) (5 / 12) 1 w) = hyp2F1 from rfl,
    show ₂F₁ (1 / 12 : ℂ) (5 / 12) 1 (J τ)⁻¹ = hyp2F1 (J τ)⁻¹ from rfl] at hODE
  have hu0 : (J τ)⁻¹ ≠ 0 := inv_ne_zero hJ
  have hu1 : (J τ)⁻¹ - 1 ≠ 0 := by
    rw [inv_J_sub_one h4]
    exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 h6)) (pow_ne_zero 3 h4)
  have hden : (J τ)⁻¹ * ((J τ)⁻¹ - 1) ≠ 0 := mul_ne_zero hu0 hu1
  have hF2 : deriv (deriv hyp2F1) (J τ)⁻¹
      = -(((1 / 12 + 5 / 12 + 1) * (J τ)⁻¹ - 1) * deriv hyp2F1 (J τ)⁻¹
          + 1 / 12 * (5 / 12) * hyp2F1 (J τ)⁻¹) / ((J τ)⁻¹ * ((J τ)⁻¹ - 1)) := by
    rw [eq_div_iff hden]
    linear_combination hODE
  convert h using 1
  rw [XhC_apply, YhC_apply, hF2]
  simp only [m22]
  rw [inv_J_sub_one h4, inv_J_eq]
  field_simp
  ring

/-- `D Xtilde = M₁₂·Ytilde` for the modular pair (this is Ramanujan's `D E₄` identity, and the
definition of `Ytilde`). -/
private lemma hasDerivAt_XtC (τ : ℍ) (hs : E₄ τ ∈ Complex.slitPlane) (h6 : E₆ τ ≠ 0) :
    HasDerivAt XtC (2 * ↑π * Complex.I * ((J τ)⁻¹ * (E₆ τ / E₄ τ)) * YtC ↑τ) ↑τ := by
  have h4 : E₄ τ ≠ 0 := Complex.slitPlane_ne_zero hs
  have hB : E₄ τ ^ 3 - E₆ τ ^ 2 ≠ 0 := E₄_cube_sub_E₆_sq_ne_zero τ
  have hsC : E₄ (ofComplex ↑τ) ∈ Complex.slitPlane := by
    rw [ofComplex_apply]
    exact hs
  have h : HasDerivAt XtC _ ↑τ := (hasDerivAt_E₄C τ).cpow_const (c := (1 / 4 : ℂ)) hsC
  convert h using 1
  simp only [ofComplex_apply]
  rw [YtC_apply, Complex.cpow_sub _ _ h4, Complex.cpow_one, inv_J_eq]
  field_simp
  ring

/-- `D Ytilde = M₂₁·Xtilde + M₂₂·Ytilde` for the modular pair: the key computation, an identity of
rational expressions in `E₂, E₄, E₆` that follows from Ramanujan's three derivative
identities (verified here by `field_simp`/`ring` after the chain rule). -/
private lemma hasDerivAt_YtC (τ : ℍ) (hs : E₄ τ ∈ Complex.slitPlane) (h6 : E₆ τ ≠ 0) :
    HasDerivAt YtC (2 * ↑π * Complex.I *
      (5 / 144 * (E₄ τ ^ 2 / E₆ τ) * XtC ↑τ + m22 τ * YtC ↑τ)) ↑τ := by
  have h4 : E₄ τ ≠ 0 := Complex.slitPlane_ne_zero hs
  have hB : E₄ τ ^ 3 - E₆ τ ^ 2 ≠ 0 := E₄_cube_sub_E₆_sq_ne_zero τ
  have hsC : E₄ (ofComplex ↑τ) ∈ Complex.slitPlane := by
    rw [ofComplex_apply]
    exact hs
  have hT := (hasDerivAt_E₄C τ).cpow_const (c := (1 / 4 : ℂ)) hsC
  have hnum := (hT.mul ((hasDerivAt_E₄C τ).pow 3)).mul
    (((hasDerivAt_E2C τ).mul (hasDerivAt_E₄C τ)).sub (hasDerivAt_E₆C τ))
  have hden := ((((hasDerivAt_E₄C τ).pow 3).sub ((hasDerivAt_E₆C τ).pow 2)).const_mul
    (12 : ℂ)).mul (hasDerivAt_E₆C τ)
  have hden0 : 12 * (E₄ (ofComplex ↑τ) ^ 3 - E₆ (ofComplex ↑τ) ^ 2) * E₆ (ofComplex ↑τ) ≠ 0 := by
    rw [ofComplex_apply]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hB) h6
  have h : HasDerivAt YtC _ ↑τ := hnum.div hden hden0
  convert h using 1
  simp only [Pi.pow_apply, Pi.sub_apply, Pi.mul_apply, ofComplex_apply]
  rw [XtC_apply, YtC_apply]
  simp only [m22]
  rw [Complex.cpow_sub _ _ h4, Complex.cpow_one, inv_J_eq]
  field_simp
  ring

/-- The Wronskian equation `D w = M₂₂·w`: the trace of the system is `M₂₂` since
`M₁₁ = 0`. -/
private lemma hasDerivAt_WrC (τ : ℍ) (hs : E₄ τ ∈ Complex.slitPlane) (h6 : E₆ τ ≠ 0)
    (hu : ‖(J τ)⁻¹‖ < 1) :
    HasDerivAt WrC (2 * ↑π * Complex.I * (m22 τ * WrC ↑τ)) ↑τ := by
  have h4 : E₄ τ ≠ 0 := Complex.slitPlane_ne_zero hs
  have h : HasDerivAt WrC _ ↑τ :=
    ((hasDerivAt_XhC τ h4 hu).mul (hasDerivAt_YtC τ hs h6)).sub
      ((hasDerivAt_YhC τ h4 h6 hu).mul (hasDerivAt_XtC τ hs h6))
  convert h using 1
  rw [WrC_apply]
  ring

/-! #### Limits of the two pairs at `i∞`

All limits are soft consequences of `E₂, E₄, E₆ → 1` except `Ytilde → 5/144`, which uses the
cusp-function factorization of `D E₄` and `kfun → 1`. -/

private lemma tendsto_q_zero : Tendsto (fun τ : ℍ => q τ) atImInfty (𝓝 0) := by
  simpa [q] using qParam_tendsto_atImInfty one_pos

private lemma tendsto_invJ : Tendsto (fun τ : ℍ => (J τ)⁻¹) atImInfty (𝓝 0) := by
  have h := ((tendsto_E₄_atImInfty.pow 3).sub (tendsto_E₆_atImInfty.pow 2)).div
    (tendsto_E₄_atImInfty.pow 3) (by norm_num)
  norm_num at h
  exact h.congr fun τ => (inv_J_eq τ).symm

private lemma tendsto_XhC : Tendsto (fun τ : ℍ => XhC ↑τ) atImInfty (𝓝 1) := by
  have hF : ContinuousAt hyp2F1 0 := (hyp2F1_analyticAt (by norm_num)).continuousAt
  have h := hF.tendsto.comp tendsto_invJ
  rw [show hyp2F1 0 = 1 from ordinaryHypergeometric_zero (1 / 12 : ℂ) (5 / 12) 1] at h
  exact h.congr fun τ => by simp only [comp_apply, XhC, ofComplex_apply]

/-- `F′(0) = ab/c = 5/144`, from the power series of `₂F₁(1/12, 5/12; 1; ·)`. -/
private lemma deriv_hyp2F1_zero : deriv hyp2F1 0 = 5 / 144 := by
  have habc : ∀ kn : ℕ, (kn : ℂ) ≠ -(1 / 12 : ℂ) ∧ (kn : ℂ) ≠ -(5 / 12 : ℂ) ∧ (kn : ℂ) ≠ -1 := by
    intro kn
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have h0 : ((12 * kn + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination 12 * h
      rw [Nat.cast_eq_zero] at h0; omega
    · have h0 : ((12 * kn + 5 : ℕ) : ℂ) = 0 := by push_cast; linear_combination 12 * h
      rw [Nat.cast_eq_zero] at h0; omega
    · have h0 : ((kn + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination h
      rw [Nat.cast_eq_zero] at h0; omega
  have hrad : (ordinaryHypergeometricSeries ℂ (1 / 12 : ℂ) (5 / 12) 1).radius = 1 :=
    ordinaryHypergeometricSeries_radius_eq_one ℂ (a := 1 / 12) (b := 5 / 12) (c := 1) habc
  have hfps := (ordinaryHypergeometricSeries ℂ (1 / 12 : ℂ) (5 / 12) 1).hasFPowerSeriesOnBall
    (by rw [hrad]; exact one_pos)
  have hat : HasFPowerSeriesAt hyp2F1 (ordinaryHypergeometricSeries ℂ (1 / 12 : ℂ) (5 / 12) 1) 0 :=
    hfps.hasFPowerSeriesAt
  rw [hat.deriv, ordinaryHypergeometricSeries_apply_eq]
  simp only [ascPochhammer_one, Polynomial.eval_X, Nat.factorial_one, Nat.cast_one, inv_one,
    one_mul, one_pow, smul_eq_mul, mul_one]
  norm_num

private lemma tendsto_YhC : Tendsto (fun τ : ℍ => YhC ↑τ) atImInfty (𝓝 (5 / 144)) := by
  have hF : ContinuousAt (deriv hyp2F1) 0 :=
    ((hyp2F1_analyticAt (by norm_num)).deriv).continuousAt
  have h := hF.tendsto.comp tendsto_invJ
  rw [deriv_hyp2F1_zero] at h
  exact h.congr fun τ => by simp only [comp_apply, YhC, ofComplex_apply]

private lemma tendsto_XtC : Tendsto (fun τ : ℍ => XtC ↑τ) atImInfty (𝓝 1) := by
  have hc : ContinuousAt (fun z : ℂ => z ^ (1 / 4 : ℂ)) 1 :=
    continuousAt_cpow_const (Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num)))
  have h := hc.tendsto.comp tendsto_E₄_atImInfty
  rw [Complex.one_cpow] at h
  exact h.congr fun τ => by simp only [comp_apply, XtC, ofComplex_apply]

private lemma E₄_periodic : Function.Periodic (⇑E₄ ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex E₄ one_mem_strictPeriods_SL

/-- The cusp-function form of `Ytilde`: writing `E₂E₄ - E₆ = 3·D E₄ = 3q·Φ′(q)` and
`E₄³ - E₆² = 1728·q·kfun`, the factor `q` cancels exactly. -/
private lemma YtC_eq (τ : ℍ) :
    YtC ↑τ = XtC ↑τ * E₄ τ ^ 3 * deriv (cuspFunction 1 ⇑E₄) (q τ)
      / (6912 * kfun τ * E₆ τ) := by
  have hq : q τ ≠ 0 := q_ne_zero τ
  have hkey : E2 τ * E₄ τ - E₆ τ = 3 * (q τ * deriv (cuspFunction 1 ⇑E₄) (q τ)) := by
    have h2 := normalizedDeriv_eq_q_mul_deriv_cuspFunction E₄_periodic
      (ModularFormClass.holo E₄) (ModularFormClass.bdd_at_infty E₄) τ
    rw [deriv_E₄ τ] at h2
    linear_combination 3 * h2
  have hB : E₄ τ ^ 3 - E₆ τ ^ 2 = 1728 * q τ * kfun τ := by
    rw [kfun]
    field_simp
  rcases eq_or_ne (E₆ τ) 0 with h6 | h6
  · rw [YtC_apply, h6]
    simp
  · have hk : kfun τ ≠ 0 :=
      div_ne_zero (E₄_cube_sub_E₆_sq_ne_zero τ) (mul_ne_zero (by norm_num) hq)
    have hd1 : (12 : ℂ) * (1728 * q τ * kfun τ) * E₆ τ ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num)
        (mul_ne_zero (mul_ne_zero (by norm_num) hq) hk)) h6
    have hd2 : (6912 : ℂ) * kfun τ * E₆ τ ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hk) h6
    rw [YtC_apply, XtC_apply, hkey, hB, div_eq_div_iff hd1 hd2]
    ring

private lemma tendsto_kfun : Tendsto kfun atImInfty (𝓝 1) := by
  have hkt : Tendsto ktilde atImInfty (𝓝 1) := by
    have h1 : Tendsto (fun τ : ℍ => (1 : ℂ) - q τ - q τ ^ 2) atImInfty (𝓝 (1 - 0 - 0 ^ 2)) :=
      (tendsto_const_nhds.sub tendsto_q_zero).sub (tendsto_q_zero.pow 2)
    have h2 := h1.pow 24
    norm_num at h2
    exact h2.congr fun τ => by rw [ktilde]
  have hdiff : Tendsto (fun τ : ℍ => kfun τ - ktilde τ) atImInfty (𝓝 0) := by
    have hev : ∀ᶠ τ : ℍ in atImInfty, ‖kfun τ - ktilde τ‖ ≤ 365.6 * ‖q τ‖ ^ 2 := by
      rw [eventually_iff, atImInfty_mem]
      exact ⟨2, fun τ hτ => lemk (lt_of_lt_of_le (by norm_num) hτ)⟩
    have hg : Tendsto (fun τ : ℍ => 365.6 * ‖q τ‖ ^ 2) atImInfty (𝓝 0) := by
      have h := (tendsto_q_zero.norm.pow 2).const_mul (365.6 : ℝ)
      simpa using h
    exact squeeze_zero_norm' hev hg
  have h := hkt.add hdiff
  rw [add_zero] at h
  exact h.congr fun τ => by ring

private lemma tendsto_YtC : Tendsto (fun τ : ℍ => YtC ↑τ) atImInfty (𝓝 (5 / 144)) := by
  have hΦana : AnalyticAt ℂ (cuspFunction 1 ⇑E₄) 0 :=
    analyticAt_cuspFunction_zero one_pos E₄_periodic (ModularFormClass.holo E₄)
      (ModularFormClass.bdd_at_infty E₄)
  have hΦ0 : deriv (cuspFunction 1 ⇑E₄) 0 = 240 := by
    have h := ModularForm.E₄_qExpansion_coeff_one
    rw [qExpansion_coeff] at h
    simpa [iteratedDeriv_one] using h
  have hΦ : Tendsto (fun τ : ℍ => deriv (cuspFunction 1 ⇑E₄) (q τ)) atImInfty (𝓝 240) := by
    have h := (hΦana.deriv.continuousAt.tendsto).comp tendsto_q_zero
    rwa [hΦ0] at h
  have hnum := (tendsto_XtC.mul (tendsto_E₄_atImInfty.pow 3)).mul hΦ
  have hden : Tendsto (fun τ : ℍ => 6912 * kfun τ * E₆ τ) atImInfty (𝓝 (6912 * 1 * 1)) :=
    (tendsto_kfun.const_mul (6912 : ℂ)).mul tendsto_E₆_atImInfty
  have h := hnum.div hden (by norm_num)
  have hval : ((1 * 1 ^ 3 * 240 : ℂ)) / (6912 * 1 * 1) = 5 / 144 := by norm_num
  rw [hval] at h
  exact h.congr fun τ => (YtC_eq τ).symm

private lemma tendsto_WrC : Tendsto (fun τ : ℍ => WrC ↑τ) atImInfty (𝓝 0) := by
  have h := (tendsto_XhC.mul tendsto_YtC).sub (tendsto_YhC.mul tendsto_XtC)
  norm_num at h
  exact h.congr fun τ => by rw [WrC_apply]

private lemma tendsto_m22 : Tendsto (fun τ : ℍ => m22 τ) atImInfty (𝓝 (-1)) := by
  have h := ((tendsto_invJ.const_mul (3 / 2 : ℂ)).sub_const 1).mul
    ((tendsto_E₄_atImInfty.pow 2).div tendsto_E₆_atImInfty (by norm_num))
  norm_num at h
  exact h.congr fun τ => by rw [m22]

/-! #### Small helpers for the "eventually" bookkeeping -/

private lemma near_one_slitPlane {z : ℂ} (h : ‖z - 1‖ < 1 / 2) : z ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
  have h1 : |(z - 1).re| ≤ ‖z - 1‖ := Complex.abs_re_le_norm _
  rw [Complex.sub_re, Complex.one_re] at h1
  have h2 := abs_le.mp h1
  linarith [h2.1]

private lemma near_one_ne_zero {z : ℂ} (h : ‖z - 1‖ < 1 / 2) : z ≠ 0 := by
  intro h0
  rw [h0, zero_sub, norm_neg, norm_one] at h
  norm_num at h

private lemma re_le_neg_half {z : ℂ} (h : ‖z + 1‖ < 1 / 2) : z.re ≤ -(1 / 2) := by
  have h1 : |(z + 1).re| ≤ ‖z + 1‖ := Complex.abs_re_le_norm _
  rw [Complex.add_re, Complex.one_re] at h1
  have h2 := abs_le.mp h1
  linarith [h2.2]

/-- The real inner product `⟪z, c·z⟫_ℝ = Re c · ‖z‖²` on `ℂ`. -/
private lemma real_inner_mul_self (c z : ℂ) : ⟪z, c * z⟫_ℝ = c.re * ‖z‖ ^ 2 := by
  rw [Complex.inner, show c * z * (starRingEnd ℂ) z = c * (z * (starRingEnd ℂ) z) from by ring,
    Complex.mul_conj, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.normSq_eq_norm_sq]

/-- All pointwise conditions needed for the system hold eventually at `i∞`. -/
private lemma eventually_good : ∀ᶠ τ : ℍ in atImInfty,
    E₄ τ ∈ Complex.slitPlane ∧ E₆ τ ≠ 0 ∧ J τ ≠ 0 ∧ ‖(J τ)⁻¹‖ < 1 ∧ XhC ↑τ ≠ 0 ∧
      (m22 τ).re ≤ -(1 / 2) := by
  have h₁ : ∀ᶠ τ : ℍ in atImInfty, ‖E₄ τ - 1‖ < 1 / 2 := by
    have h := Metric.tendsto_nhds.mp tendsto_E₄_atImInfty (1 / 2) (by norm_num)
    simpa [dist_eq_norm] using h
  have h₂ : ∀ᶠ τ : ℍ in atImInfty, ‖E₆ τ - 1‖ < 1 / 2 := by
    have h := Metric.tendsto_nhds.mp tendsto_E₆_atImInfty (1 / 2) (by norm_num)
    simpa [dist_eq_norm] using h
  have h₃ : ∀ᶠ τ : ℍ in atImInfty, ‖(J τ)⁻¹‖ < 1 := by
    have h := Metric.tendsto_nhds.mp tendsto_invJ 1 one_pos
    simpa [dist_eq_norm] using h
  have h₄ : ∀ᶠ τ : ℍ in atImInfty, ‖XhC ↑τ - 1‖ < 1 / 2 := by
    have h := Metric.tendsto_nhds.mp tendsto_XhC (1 / 2) (by norm_num)
    simpa [dist_eq_norm] using h
  have h₅ : ∀ᶠ τ : ℍ in atImInfty, ‖m22 τ + 1‖ < 1 / 2 := by
    have h := Metric.tendsto_nhds.mp tendsto_m22 (1 / 2) (by norm_num)
    simpa [dist_eq_norm, sub_neg_eq_add] using h
  filter_upwards [h₁, h₂, h₃, h₄, h₅] with τ k₁ k₂ k₃ k₄ k₅
  exact ⟨near_one_slitPlane k₁, near_one_ne_zero k₂, J_ne_zero (near_one_ne_zero k₁), k₃,
    near_one_ne_zero k₄, re_le_neg_half k₅⟩

/-! #### The vertical-line Wronskian argument -/

private lemma coe_ofComplex {w : ℂ} (hw : 0 < w.im) : ((ofComplex w : ℍ) : ℂ) = w := by
  rw [ofComplex_apply_of_im_pos hw]

private lemma im_ofComplex {w : ℂ} (hw : 0 < w.im) : (ofComplex w).im = w.im := by
  rw [← UpperHalfPlane.coe_im, coe_ofComplex hw]

private lemma E₄_ne_zero_of_mem_Region {τ : ℍ} (hτ : τ ∈ Region) : E₄ τ ≠ 0 := by
  have h1 := norm_E₄trunc_ge hτ
  have h2 := norm_sub_E₄trunc_le hτ
  have hq : ‖q τ‖ < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  have hqpos : 0 < ‖q τ‖ := norm_q_pos τ
  have hq3 : ‖q τ‖ ^ 3 ≤ (0.000389 : ℝ) ^ 3 := pow_le_pow_left₀ hqpos.le hq.le 3
  intro h0
  rw [h0, zero_sub, norm_neg] at h2
  nlinarith [hq3]

private lemma im_add_vert (z₀ : ℂ) (t : ℝ) : (z₀ + ↑t * Complex.I).im = z₀.im + t := by
  simp [Complex.add_im, Complex.mul_im]

private lemma tendsto_vertical {z₀ : ℂ} (h : 0 < z₀.im) :
    Tendsto (fun t : ℝ => ofComplex (z₀ + ↑t * Complex.I)) atTop atImInfty := by
  have key : Tendsto (UpperHalfPlane.im ∘ fun t : ℝ => ofComplex (z₀ + ↑t * Complex.I))
      atTop atTop := by
    have hev : (UpperHalfPlane.im ∘ fun t : ℝ => ofComplex (z₀ + ↑t * Complex.I))
        =ᶠ[atTop] fun t : ℝ => z₀.im + t := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      have him : 0 < (z₀ + ↑t * Complex.I).im := by
        rw [im_add_vert]
        linarith
      simp only [comp_apply]
      rw [im_ofComplex him, im_add_vert]
    rw [tendsto_congr' hev]
    exact tendsto_atTop_add_const_left _ _ tendsto_id
  exact tendsto_comap_iff.mpr key

/-- **Vanishing of the Wronskian** on `{Im z > A}`: a solution of `D w = M₂₂ w` with
`Re M₂₂ ≤ -1/2` has `‖w‖²·e^{-2πt}` nondecreasing along vertical lines, so `w → 0` at
`i∞` forces `w = 0`. -/
private lemma WrC_eq_zero {A : ℝ} (hA : 2 ≤ A)
    (hgood : ∀ σ : ℍ, A ≤ σ.im →
      E₄ σ ∈ Complex.slitPlane ∧ E₆ σ ≠ 0 ∧ J σ ≠ 0 ∧ ‖(J σ)⁻¹‖ < 1 ∧ XhC ↑σ ≠ 0 ∧
        (m22 σ).re ≤ -(1 / 2))
    {z₀ : ℂ} (hz₀ : A < z₀.im) : WrC z₀ = 0 := by
  have hz₀im : 0 < z₀.im := by linarith
  have him : ∀ t : ℝ, 0 ≤ t → 0 < (z₀ + ↑t * Complex.I).im := by
    intro t ht
    rw [im_add_vert]
    linarith
  have himA : ∀ t : ℝ, 0 ≤ t → A ≤ (ofComplex (z₀ + ↑t * Complex.I)).im := by
    intro t ht
    rw [im_ofComplex (him t ht), im_add_vert]
    linarith
  -- the derivative of `ψ(t) = w(z₀ + it)` is `-2π·M₂₂·ψ`
  have hψd : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s : ℝ => WrC (z₀ + ↑s * Complex.I))
        (-(2 * ↑π) * (m22 (ofComplex (z₀ + ↑t * Complex.I))
          * WrC (z₀ + ↑t * Complex.I))) t := by
    intro t ht
    set σ : ℍ := ofComplex (z₀ + ↑t * Complex.I) with hσ
    obtain ⟨hs, h6, hJ, hu, hXh0, hre⟩ := hgood σ (himA t ht)
    have hW0 := hasDerivAt_WrC σ
    have hW := hW0 hs h6 hu
    have hcoe : (σ : ℂ) = z₀ + ↑t * Complex.I := by
      rw [hσ]
      exact coe_ofComplex (him t ht)
    rw [hcoe] at hW
    have hline : HasDerivAt (fun w : ℂ => z₀ + w * Complex.I) Complex.I ((t : ℝ) : ℂ) := by
      simpa using ((hasDerivAt_id ((t : ℝ) : ℂ)).mul_const Complex.I).const_add z₀
    have hcc := hW.comp ((t : ℝ) : ℂ) hline
    have hcomp : HasDerivAt (fun s : ℝ => WrC (z₀ + ↑s * Complex.I))
        (2 * ↑π * Complex.I * (m22 σ * WrC (z₀ + ↑t * Complex.I)) * Complex.I) t :=
      hcc.comp_ofReal
    have hval : 2 * ↑π * Complex.I * (m22 σ * WrC (z₀ + ↑t * Complex.I)) * Complex.I
        = -(2 * ↑π) * (m22 σ * WrC (z₀ + ↑t * Complex.I)) := by
      linear_combination (2 * ↑π * (m22 σ * WrC (z₀ + ↑t * Complex.I))) * Complex.I_mul_I
    exact hval ▸ hcomp
  -- the derivative of `r(t) = ‖ψ(t)‖²`
  have hrd : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s : ℝ => ‖WrC (z₀ + ↑s * Complex.I)‖ ^ 2)
        (2 * ((-(2 * ↑π) * m22 (ofComplex (z₀ + ↑t * Complex.I))).re
          * ‖WrC (z₀ + ↑t * Complex.I)‖ ^ 2)) t := by
    intro t ht
    have h := (hψd t ht).norm_sq
    rwa [show -(2 * ↑π) * (m22 (ofComplex (z₀ + ↑t * Complex.I)) * WrC (z₀ + ↑t * Complex.I))
        = (-(2 * ↑π) * m22 (ofComplex (z₀ + ↑t * Complex.I))) * WrC (z₀ + ↑t * Complex.I)
        from by ring, real_inner_mul_self] at h
  -- the weighted modulus `g(t) = r(t)·e^{-2πt}` and its monotonicity
  have hgd : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s : ℝ => ‖WrC (z₀ + ↑s * Complex.I)‖ ^ 2 * Real.exp (-(2 * π) * s))
        (2 * ((-(2 * ↑π) * m22 (ofComplex (z₀ + ↑t * Complex.I))).re
            * ‖WrC (z₀ + ↑t * Complex.I)‖ ^ 2) * Real.exp (-(2 * π) * t)
          + ‖WrC (z₀ + ↑t * Complex.I)‖ ^ 2 * (-(2 * π) * Real.exp (-(2 * π) * t))) t := by
    intro t ht
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(2 * π) * s))
        (-(2 * π) * Real.exp (-(2 * π) * t)) t := by
      have h1 : HasDerivAt (fun s : ℝ => -(2 * π) * s) (-(2 * π)) t := by
        simpa using (hasDerivAt_id t).const_mul (-(2 * π))
      have h2 := (Real.hasDerivAt_exp (-(2 * π) * t)).comp t h1
      rw [show Real.exp (-(2 * π) * t) * (-(2 * π))
        = -(2 * π) * Real.exp (-(2 * π) * t) from mul_comm _ _] at h2
      exact h2
    exact (hrd t ht).mul hexp
  have hmono : MonotoneOn (fun s : ℝ => ‖WrC (z₀ + ↑s * Complex.I)‖ ^ 2
      * Real.exp (-(2 * π) * s)) (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun s hs => ((hgd s hs).continuousAt).continuousWithinAt
    · rw [interior_Ici]
      exact fun s hs => (hgd s (le_of_lt hs)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro s hs
      rw [(hgd s (le_of_lt hs)).deriv]
      obtain ⟨_, _, _, _, _, hre⟩ :=
        hgood (ofComplex (z₀ + ↑s * Complex.I)) (himA s (le_of_lt hs))
      have h1 : (0 : ℝ) ≤ ‖WrC (z₀ + ↑s * Complex.I)‖ ^ 2 := by positivity
      have h2 : (0 : ℝ) < Real.exp (-(2 * π) * s) := Real.exp_pos _
      have h3 : (-(2 * ↑π) * m22 (ofComplex (z₀ + ↑s * Complex.I))).re
          = -(2 * π) * (m22 (ofComplex (z₀ + ↑s * Complex.I))).re := by
        rw [show (-(2 * ↑π) : ℂ) = ((-(2 * π) : ℝ) : ℂ) from by push_cast; ring,
          Complex.re_ofReal_mul]
      rw [h3]
      have key : (0 : ℝ) ≤ -(4 * π * (m22 (ofComplex (z₀ + ↑s * Complex.I))).re) - 2 * π := by
        nlinarith [Real.pi_pos]
      nlinarith [mul_nonneg (mul_nonneg h1 h2.le) key]
  -- `ψ → 0` along the ray, so `r → 0`
  have hψ0 : Tendsto (fun t : ℝ => WrC (z₀ + ↑t * Complex.I)) atTop (𝓝 0) := by
    have h := tendsto_WrC.comp (tendsto_vertical hz₀im)
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simp only [comp_apply]
    rw [coe_ofComplex (him t ht)]
  have hr0 : Tendsto (fun t : ℝ => ‖WrC (z₀ + ↑t * Complex.I)‖ ^ 2) atTop (𝓝 0) := by
    have h := (hψ0.norm).pow 2
    simpa using h
  -- squeeze: `g 0 ≤ g t ≤ r t → 0`
  have hg0 : ‖WrC (z₀ + ↑(0 : ℝ) * Complex.I)‖ ^ 2 * Real.exp (-(2 * π) * 0) ≤ 0 := by
    have hle : ∀ᶠ t : ℝ in atTop,
        ‖WrC (z₀ + ↑(0 : ℝ) * Complex.I)‖ ^ 2 * Real.exp (-(2 * π) * 0)
          ≤ ‖WrC (z₀ + ↑t * Complex.I)‖ ^ 2 := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      have hmt := hmono Set.self_mem_Ici (Set.mem_Ici.mpr ht) ht
      have hexp1 : Real.exp (-(2 * π) * t) ≤ 1 := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        nlinarith [Real.pi_pos]
      nlinarith [sq_nonneg ‖WrC (z₀ + ↑t * Complex.I)‖, Real.exp_pos (-(2 * π) * t), hmt]
    exact ge_of_tendsto hr0 hle
  have hz : WrC (z₀ + ↑(0 : ℝ) * Complex.I) = WrC z₀ := by norm_num
  rw [hz, mul_zero, Real.exp_zero, mul_one] at hg0
  have hnorm : ‖WrC z₀‖ = 0 := by nlinarith [sq_nonneg ‖WrC z₀‖, norm_nonneg (WrC z₀)]
  exact norm_eq_zero.mp hnorm

/-- On `{Im z > A}` the two solutions agree: the ratio `Xtilde/X` has vanishing derivative
(Wronskian zero), hence is constant, and its limit at `i∞` is `1`. -/
private lemma XtC_eq_XhC {A : ℝ} (hA : 2 ≤ A)
    (hgood : ∀ σ : ℍ, A ≤ σ.im →
      E₄ σ ∈ Complex.slitPlane ∧ E₆ σ ≠ 0 ∧ J σ ≠ 0 ∧ ‖(J σ)⁻¹‖ < 1 ∧ XhC ↑σ ≠ 0 ∧
        (m22 σ).re ≤ -(1 / 2))
    {z : ℂ} (hz : A < z.im) : XtC z = XhC z := by
  have hΩo : IsOpen {w : ℂ | A < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hΩc : IsPreconnected {w : ℂ | A < w.im} := (convex_halfSpace_im_gt A).isPreconnected
  -- pointwise: the ratio has vanishing derivative
  have hkey : ∀ w : ℂ, A < w.im → HasDerivAt (fun y => XtC y / XhC y) 0 w ∧ XhC w ≠ 0 := by
    intro w hw
    have hw0 : 0 < w.im := by linarith
    have hcoe : ((ofComplex w : ℍ) : ℂ) = w := coe_ofComplex hw0
    have hAw : A ≤ (ofComplex w).im := by
      rw [im_ofComplex hw0]
      linarith
    obtain ⟨hs, h6, hJ, hu, hXh0, hre⟩ := hgood (ofComplex w) hAw
    have h4 : E₄ (ofComplex w) ≠ 0 := Complex.slitPlane_ne_zero hs
    have hXt := hasDerivAt_XtC (ofComplex w) hs h6
    have hXh := hasDerivAt_XhC (ofComplex w) h4 hu
    rw [hcoe] at hXt hXh hXh0
    refine ⟨?_, hXh0⟩
    have hW0 : WrC w = 0 := WrC_eq_zero hA hgood hw
    have hWr : XhC w * YtC w - YhC w * XtC w = 0 := by rwa [WrC] at hW0
    have hdiv : HasDerivAt (fun y => XtC y / XhC y)
        ((2 * ↑π * Complex.I * ((J (ofComplex w))⁻¹ * (E₆ (ofComplex w) / E₄ (ofComplex w)))
            * YtC w * XhC w
          - XtC w * (2 * ↑π * Complex.I
            * ((J (ofComplex w))⁻¹ * (E₆ (ofComplex w) / E₄ (ofComplex w))) * YhC w))
          / XhC w ^ 2) w :=
      hXt.div hXh hXh0
    have hval : (2 * ↑π * Complex.I * ((J (ofComplex w))⁻¹
            * (E₆ (ofComplex w) / E₄ (ofComplex w))) * YtC w * XhC w
          - XtC w * (2 * ↑π * Complex.I
            * ((J (ofComplex w))⁻¹ * (E₆ (ofComplex w) / E₄ (ofComplex w))) * YhC w))
          / XhC w ^ 2 = 0 := by
      rw [div_eq_zero_iff]
      left
      linear_combination (2 * ↑π * Complex.I
        * ((J (ofComplex w))⁻¹ * (E₆ (ofComplex w) / E₄ (ofComplex w)))) * hWr
    exact hval ▸ hdiv
  have hdiff : DifferentiableOn ℂ (fun y => XtC y / XhC y) {w : ℂ | A < w.im} :=
    fun w hw => ((hkey w hw).1.differentiableAt).differentiableWithinAt
  have hderiv0 : Set.EqOn (deriv fun y => XtC y / XhC y) 0 {w : ℂ | A < w.im} :=
    fun w hw => (hkey w hw).1.deriv
  -- the limit of the (constant) ratio along the vertical ray from `z` is `1`
  have hz0 : 0 < z.im := by linarith
  have hray : Tendsto (fun t : ℝ => XtC (z + ↑t * Complex.I) / XhC (z + ↑t * Complex.I))
      atTop (𝓝 1) := by
    have h := (tendsto_XtC.div tendsto_XhC one_ne_zero).comp (tendsto_vertical hz0)
    norm_num at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have him : 0 < (z + ↑t * Complex.I).im := by
      rw [im_add_vert]
      linarith
    simp only [comp_apply, Pi.div_apply]
    rw [coe_ofComplex him]
  have hconst_ray : Tendsto (fun t : ℝ => XtC (z + ↑t * Complex.I) / XhC (z + ↑t * Complex.I))
      atTop (𝓝 (XtC z / XhC z)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have himt : (z + ↑t * Complex.I) ∈ {w : ℂ | A < w.im} := by
      have := im_add_vert z t
      change A < (z + ↑t * Complex.I).im
      rw [this]
      linarith
    exact (hΩo.is_const_of_deriv_eq_zero hΩc hdiff hderiv0 himt hz).symm
  have h1 : XtC z / XhC z = 1 := tendsto_nhds_unique hconst_ray hray
  have hXh0 : XhC z ≠ 0 := (hkey z hz).2
  field_simp at h1
  exact h1

/-- **Kummer's solution for the lattice `Ltilde = Δ^(1/12)·L_τ`** (paper Thm. `omegastrich`,
ch. 8), in the branch-free fourth-power form recommended by PLAN A7:
for all `τ` with `Im τ > 1.25`,
`E₄(τ) = (₂F₁(1/12, 5/12; 1; 1/J(τ)))⁴`.

This is equivalent to the paper's
`Δ(τ)^(1/12) = (2π/12^(1/4)) · J(τ)^(-1/12) · ₂F₁(1/12, 5/12; 1; 1/J(τ))`
raised to the 12th power (see the module docstring), with the branch fixed as the paper does
in its Main Theorem via continuity/connectedness on `Region`. -/
theorem E₄_eq_hyp2F1_pow_four {τ : ℍ} (hτ : τ ∈ Region) :
    E₄ τ = hyp2F1 (J τ)⁻¹ ^ 4 := by
  -- choose a height `A ≥ 2` above which all `eventually_good` conditions hold
  obtain ⟨A₀, hA₀⟩ := (atImInfty_mem _).mp eventually_good
  set A : ℝ := max A₀ 2 with hAdef
  have hA2 : (2 : ℝ) ≤ A := le_max_right _ _
  have hgood : ∀ σ : ℍ, A ≤ σ.im →
      E₄ σ ∈ Complex.slitPlane ∧ E₆ σ ≠ 0 ∧ J σ ≠ 0 ∧ ‖(J σ)⁻¹‖ < 1 ∧ XhC ↑σ ≠ 0 ∧
        (m22 σ).re ≤ -(1 / 2) :=
    fun σ hσ => hA₀ σ (le_trans (le_max_left _ _) hσ)
  -- the identity `E₄ = Xtilde⁴ = X⁴` on `{Im z > A}`
  have hΩeq : ∀ w : ℂ, A < w.im → E₄ (ofComplex w) = hyp2F1 (J (ofComplex w))⁻¹ ^ 4 := by
    intro w hw
    have h := XtC_eq_XhC hA2 hgood hw
    have h4 : E₄ (ofComplex w) = XtC w ^ 4 := by
      rw [show XtC w = E₄ (ofComplex w) ^ (1 / 4 : ℂ) from rfl, ← Complex.cpow_nat_mul,
        show ((4 : ℕ) : ℂ) * (1 / 4) = 1 by norm_num, Complex.cpow_one]
    rw [h4, h]
    rfl
  -- both sides are analytic on `S = {Im z > 5/4}`
  have hSo : IsOpen {w : ℂ | 5 / 4 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hSc : IsPreconnected {w : ℂ | 5 / 4 < w.im} :=
    (convex_halfSpace_im_gt (5 / 4)).isPreconnected
  have hsub : {w : ℂ | 5 / 4 < w.im} ⊆ upperHalfPlaneSet := fun w hw => by
    have hw' : (5 : ℝ) / 4 < w.im := hw
    change 0 < w.im
    linarith
  have hf : AnalyticOnNhd ℂ (⇑E₄ ∘ ofComplex) {w : ℂ | 5 / 4 < w.im} :=
    ((UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo E₄)).mono hsub).analyticOnNhd hSo
  have hg : AnalyticOnNhd ℂ (fun w => hyp2F1 (J (ofComplex w))⁻¹ ^ 4)
      {w : ℂ | 5 / 4 < w.im} := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hSo
    have hw0 : 0 < w.im := lt_trans (by norm_num) hw
    have hR : ofComplex w ∈ Region := by
      change 5 / 4 < (ofComplex w).im
      rw [im_ofComplex hw0]
      exact hw
    have h4 : E₄ (ofComplex w) ≠ 0 := E₄_ne_zero_of_mem_Region hR
    have hu : ‖(J (ofComplex w))⁻¹‖ < 1 := norm_inv_J_lt_one hR
    have hXh := hasDerivAt_XhC (ofComplex w) h4 hu
    rw [coe_ofComplex hw0] at hXh
    exact ((hXh.pow 4).differentiableAt).differentiableWithinAt
  -- eventual equality at the point `i·(A+1)`, and analytic continuation
  have him : (((A + 1 : ℝ) : ℂ) * Complex.I).im = A + 1 := by
    simp [Complex.mul_im]
  have hz₀S : (((A + 1 : ℝ) : ℂ) * Complex.I) ∈ {w : ℂ | 5 / 4 < w.im} := by
    change (5 : ℝ) / 4 < (((A + 1 : ℝ) : ℂ) * Complex.I).im
    rw [him]
    linarith
  have hev : (⇑E₄ ∘ ofComplex) =ᶠ[𝓝 (((A + 1 : ℝ) : ℂ) * Complex.I)]
      fun w => hyp2F1 (J (ofComplex w))⁻¹ ^ 4 := by
    have hmem : {w : ℂ | A < w.im} ∈ 𝓝 (((A + 1 : ℝ) : ℂ) * Complex.I) := by
      refine (isOpen_lt continuous_const Complex.continuous_im).mem_nhds ?_
      change A < (((A + 1 : ℝ) : ℂ) * Complex.I).im
      rw [him]
      linarith
    exact Filter.eventuallyEq_of_mem hmem fun w hw => hΩeq w hw
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hSc hz₀S hev
  have hτS : (↑τ : ℂ) ∈ {w : ℂ | 5 / 4 < w.im} := by
    change (5 : ℝ) / 4 < (↑τ : ℂ).im
    rw [UpperHalfPlane.coe_im]
    exact hτ
  have h := heq hτS
  simpa only [comp_apply, ofComplex_apply] using h

end OmegaStrich

end Chudnovsky

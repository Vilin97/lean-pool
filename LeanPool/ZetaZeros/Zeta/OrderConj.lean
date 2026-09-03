/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import LeanPool.ZetaZeros.Zeta.Defs

/-!
# Conjugation preserves the multiplicity of a zero

BOTH of the symmetries whose composition `ρ ↦ 1 - conj ρ` makes the rescaled zeros
conjugation-invariant. The conjugation half is the cheap one: it follows from `riemannZeta_conj`
together with the fact that pre- and post-composing with conjugation does not change an analytic
order. The reflection half needs the functional equation, and needs the order to be transported
across `ρ ↦ 1 - ρ`, for which Mathlib has nothing ready-made.

The three private lemmas below are adapted, with thanks, from
`AxiomMath/PrimeNumberTheoremAnd`, `PrimeNumberTheoremAnd/IEANTN/KadiriZeroCounting.lean`, where
they support the same statement for that project's own order function.
-/

@[expose] public section

namespace ZetaZeros

/-- If `f` has derivative `f'` at `conj z₀`, the double conjugate has derivative `conj f'` at
`z₀`. -/
private lemma hasDerivAt_conj_conj {f : ℂ → ℂ} {f' z₀ : ℂ}
    (hf : HasDerivAt f f' ((starRingEnd ℂ) z₀)) :
    HasDerivAt (fun w ↦ (starRingEnd ℂ) (f ((starRingEnd ℂ) w)))
      ((starRingEnd ℂ) f') z₀ := by
  rw [hasDerivAt_iff_tendsto_slope] at hf ⊢
  have hconj_tendsto : Filter.Tendsto (starRingEnd ℂ)
      (nhdsWithin z₀ {z₀}ᶜ)
      (nhdsWithin ((starRingEnd ℂ) z₀) {(starRingEnd ℂ) z₀}ᶜ) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (Complex.continuous_conj.tendsto z₀).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      intro h
      apply hw
      have := congrArg (starRingEnd ℂ) h
      simpa [Complex.conj_conj] using this
  have hcomp := (Complex.continuous_conj.tendsto f').comp (hf.comp hconj_tendsto)
  refine Filter.Tendsto.congr (fun u ↦ ?_) hcomp
  simp only [Function.comp_apply, slope_def_field, map_div₀, map_sub, Complex.conj_conj]

/-- Analyticity of the double conjugate. -/
private lemma analyticAt_conj_conj {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f ((starRingEnd ℂ) z₀)) :
    AnalyticAt ℂ (fun w ↦ (starRingEnd ℂ) (f ((starRingEnd ℂ) w))) z₀ := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt] at hf ⊢
  have hc : Filter.Tendsto (starRingEnd ℂ) (nhds z₀) (nhds ((starRingEnd ℂ) z₀)) :=
    Complex.continuous_conj.tendsto z₀
  filter_upwards [hc.eventually hf] with w hw
  exact (hasDerivAt_conj_conj hw.hasDerivAt).differentiableAt

/-- The analytic order of the double conjugate at `z₀` is the analytic order of `f` at
`conj z₀`. -/
private lemma analyticOrderAt_conj_conj {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f ((starRingEnd ℂ) z₀)) :
    analyticOrderAt (fun w ↦ (starRingEnd ℂ) (f ((starRingEnd ℂ) w))) z₀ =
      analyticOrderAt f ((starRingEnd ℂ) z₀) := by
  have hcfc := analyticAt_conj_conj hf
  have hc : Filter.Tendsto (starRingEnd ℂ) (nhds z₀) (nhds ((starRingEnd ℂ) z₀)) :=
    Complex.continuous_conj.tendsto z₀
  cases h : analyticOrderAt f ((starRingEnd ℂ) z₀) with
  | top =>
      rw [analyticOrderAt_eq_top] at h ⊢
      filter_upwards [hc.eventually h] with w hw
      rw [hw, map_zero]
  | coe n =>
      rw [hf.analyticOrderAt_eq_natCast] at h
      obtain ⟨g, hg, hg0, hfg⟩ := h
      rw [hcfc.analyticOrderAt_eq_natCast]
      refine ⟨fun w ↦ (starRingEnd ℂ) (g ((starRingEnd ℂ) w)),
        analyticAt_conj_conj hg, ?_, ?_⟩
      · intro h0
        apply hg0
        have := congrArg (starRingEnd ℂ) h0
        simpa [Complex.conj_conj] using this
      · filter_upwards [hc.eventually hfg] with w hw
        rw [hw]
        simp only [smul_eq_mul, map_mul, map_pow, map_sub, Complex.conj_conj]

/-- Zeta is analytic away from its pole. -/
private lemma analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_ne.mem_nhds hs] with w hw
  exact differentiableAt_riemannZeta hw

/-- **Conjugation preserves the multiplicity of a zero.** -/
@[zz_tag "lem_order_conj"]
theorem zeroMultiplicity_conj {ρ : ℂ} (hρ : ρ ≠ 1) :
    zeroMultiplicity ((starRingEnd ℂ) ρ) = zeroMultiplicity ρ := by
  have hρ' : (starRingEnd ℂ) ρ ≠ 1 := by
    intro h
    apply hρ
    have := congrArg (starRingEnd ℂ) h
    simpa [Complex.conj_conj] using this
  have key := analyticOrderAt_conj_conj (analyticAt_riemannZeta hρ')
  have hfun : (fun w ↦ (starRingEnd ℂ) (riemannZeta ((starRingEnd ℂ) w))) = riemannZeta := by
    funext w
    rw [riemannZeta_conj, Complex.conj_conj]
  rw [hfun] at key
  simp only [zeroMultiplicity, analyticOrderNatAt, key]

/-! ### The functional equation preserves multiplicity

Mathlib has no form of this statement; what it supplies is `riemannZeta_one_sub`, the functional
equation in the form
`zeta (1 - s) = functionalEqFactor s * zeta s`.

Two things then have to be shown, and the second is the real work:

* `functionalEqFactor` is analytic and NON-VANISHING on the strip. `Gamma` is non-zero where the
  real part is positive, the `cpow` factor is an `exp`, and `cos (pi s / 2)` vanishes only at odd
  integers -- none of which have real part strictly between `0` and `1`.
* The order has to move ACROSS the reflection, from `rho` to `1 - rho`. Mathlib has no lemma for
  that, so `analyticOrderAt_comp_const_sub` is proved here: the order of `w -> f (a - w)` at `z` is
  the order of `f` at `a - z`. It is stated for a general `f` and `a` because nothing in it is about
  zeta, and it is the piece worth reusing. -/

/-- One direction of the transport of the vanishing order along `w ↦ a - w`. -/
theorem le_analyticOrderAt_comp_const_sub {f : ℂ → ℂ} {a z : ℂ} {n : ℕ}
    (h : (n : ℕ∞) ≤ analyticOrderAt f (a - z)) :
    (n : ℕ∞) ≤ analyticOrderAt (fun w => f (a - w)) z := by
  by_cases hf : AnalyticAt ℂ f (a - z)
  · rw [natCast_le_analyticOrderAt hf] at h
    obtain ⟨g, hg, hfg⟩ := h
    have hinner : AnalyticAt ℂ (fun w : ℂ => a - w) z :=
      analyticAt_const.sub analyticAt_id
    have htend : Filter.Tendsto (fun w : ℂ => a - w) (nhds z) (nhds (a - z)) :=
      (continuous_const.sub continuous_id).tendsto z
    have hfc : AnalyticAt ℂ (fun w => f (a - w)) z := hf.comp hinner
    have hgc : AnalyticAt ℂ (fun w => g (a - w)) z := hg.comp hinner
    refine (natCast_le_analyticOrderAt hfc).2
      ⟨fun w => (-1 : ℂ) ^ n * g (a - w), analyticAt_const.mul hgc, ?_⟩
    · filter_upwards [htend.eventually hfg] with w hw
      simp only [smul_eq_mul] at hw ⊢
      rw [hw, show a - w - (a - z) = -(w - z) by ring, neg_pow]
      ring
  · rw [analyticOrderAt_of_not_analyticAt hf, nonpos_iff_eq_zero, Nat.cast_eq_zero] at h
    subst h
    simp

/-- **Transport of the vanishing order along an affine reflection.** -/
theorem analyticOrderAt_comp_const_sub (f : ℂ → ℂ) (a z : ℂ) :
    analyticOrderAt (fun w => f (a - w)) z = analyticOrderAt f (a - z) := by
  refine le_antisymm (ENat.forall_natCast_le_iff_le.mp ?_)
    (ENat.forall_natCast_le_iff_le.mp ?_)
  · intro n hn
    have h2 : (n : ℕ∞) ≤ analyticOrderAt (fun w => f (a - w)) (a - (a - z)) := by
      rwa [sub_sub_cancel]
    have h3 := le_analyticOrderAt_comp_const_sub h2
    have hfun : (fun w : ℂ => f (a - (a - w))) = f := by
      funext w; rw [sub_sub_cancel]
    rw [hfun] at h3
    exact h3
  · intro n hn
    exact le_analyticOrderAt_comp_const_sub hn

/-! ### The factor in the functional equation -/

/-- The factor in `ζ (1 - s) = functionalEqFactor s * ζ s`, written with `exp` rather than `cpow`
so that its analyticity is visible. -/
noncomputable def functionalEqFactor (s : ℂ) : ℂ :=
  2 * Complex.exp (Complex.log (2 * (Real.pi : ℂ)) * (-s)) * Complex.Gamma s *
    Complex.cos ((Real.pi : ℂ) * s / 2)

theorem two_mul_pi_ne_zero : (2 * (Real.pi : ℂ)) ≠ 0 :=
  mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

theorem zeta_one_sub_eq (s : ℂ) (hn : ∀ n : ℕ, s ≠ -(n : ℂ)) (h1 : s ≠ 1) :
    riemannZeta (1 - s) = functionalEqFactor s * riemannZeta s := by
  rw [riemannZeta_one_sub hn h1, functionalEqFactor, Complex.cpow_def_of_ne_zero two_mul_pi_ne_zero]

theorem differentiableOn_functionalEqFactor :
    DifferentiableOn ℂ functionalEqFactor {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs' : ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro m hm
    rw [hm] at hs
    simp only [Set.mem_ofPred_eq] at hs
    simp at hs
    linarith [hs]
  have hGamma : DifferentiableAt ℂ Complex.Gamma s := Complex.differentiableAt_Gamma s hs'
  have : DifferentiableAt ℂ functionalEqFactor s := by
    unfold functionalEqFactor
    exact (((differentiableAt_const _).mul
      ((Complex.differentiable_exp _).comp _
        (((differentiableAt_const _).mul (differentiableAt_id.neg))))).mul hGamma).mul
      ((Complex.differentiable_cos _).comp _
        (((differentiableAt_const _).mul differentiableAt_id).div_const _))
  exact this.differentiableWithinAt

theorem analyticAt_functionalEqFactor {ρ : ℂ} (h0 : 0 < ρ.re) :
    AnalyticAt ℂ functionalEqFactor ρ := by
  refine differentiableOn_functionalEqFactor.analyticAt ?_
  exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds h0

theorem functionalEqFactor_ne_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    functionalEqFactor ρ ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hGamma : Complex.Gamma ρ ≠ 0 := Complex.Gamma_ne_zero_of_re_pos h0
  have hcos : Complex.cos ((Real.pi : ℂ) * ρ / 2) ≠ 0 := by
    intro hc
    rw [Complex.cos_eq_zero_iff] at hc
    obtain ⟨k, hk⟩ := hc
    have h2 : (Real.pi : ℂ) * ρ = (Real.pi : ℂ) * (2 * (k : ℂ) + 1) := by
      linear_combination 2 * hk
    have hρ : ρ = 2 * (k : ℂ) + 1 := mul_left_cancel₀ hpi h2
    have hre : ρ.re = 2 * (k : ℝ) + 1 := by
      rw [hρ]; simp
    rw [hre] at h0 h1
    have hk0 : (0 : ℝ) < 2 * (k : ℝ) + 1 := h0
    have hk1 : 2 * (k : ℝ) + 1 < 1 := h1
    have : (0 : ℤ) < 2 * k + 1 := by
      have : (0 : ℝ) < ((2 * k + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have : (2 * k + 1 : ℤ) < 1 := by
      have : ((2 * k + 1 : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    omega
  unfold functionalEqFactor
  have hexp : Complex.exp (Complex.log (2 * (Real.pi : ℂ)) * (-ρ)) ≠ 0 := Complex.exp_ne_zero _
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hexp) hGamma) hcos

/-- **The functional equation preserves multiplicity.** For every `ρ` in the open critical strip,
the multiplicity of `1 - ρ` as a zero of `ζ` equals that of `ρ`. -/
@[zz_tag "lem_order_one_sub"]
theorem zeroMultiplicity_one_sub {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    zeroMultiplicity (1 - ρ) = zeroMultiplicity ρ := by
  have key : analyticOrderAt riemannZeta (1 - ρ) = analyticOrderAt riemannZeta ρ := by
    -- Step 1: reflect
    rw [← analyticOrderAt_comp_const_sub riemannZeta 1 ρ]
    -- Step 2: use the functional equation near `ρ`
    have hU : IsOpen {s : ℂ | 0 < s.re ∧ s.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hmem : {s : ℂ | 0 < s.re ∧ s.re < 1} ∈ nhds ρ := hU.mem_nhds ⟨h0, h1⟩
    have heq : (fun w => riemannZeta (1 - w)) =ᶠ[nhds ρ]
        fun w => functionalEqFactor w * riemannZeta w := by
      filter_upwards [hmem] with s hs
      obtain ⟨hs0, hs1⟩ := hs
      have hne1 : s ≠ 1 := by
        intro h; rw [h] at hs1; simp at hs1
      have hnen : ∀ n : ℕ, s ≠ -(n : ℂ) := by
        intro m hm
        rw [hm] at hs0
        simp at hs0
        linarith [hs0]
      exact zeta_one_sub_eq s hnen hne1
    rw [analyticOrderAt_congr heq]
    -- Step 3: multiplication by an analytic non-vanishing factor
    have hz : AnalyticAt ℂ riemannZeta ρ := by
      refine differentiableOn_riemannZeta.analyticAt ?_
      refine IsOpen.mem_nhds isOpen_compl_singleton ?_
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h; rw [h] at h1; simp at h1
    have hG := analyticAt_functionalEqFactor h0
    have : (fun w => functionalEqFactor w * riemannZeta w) = functionalEqFactor * riemannZeta := rfl
    rw [this, analyticOrderAt_mul hG hz]
    have : analyticOrderAt functionalEqFactor ρ = 0 :=
      analyticOrderAt_eq_zero.2 (Or.inr (functionalEqFactor_ne_zero h0 h1))
    rw [this, zero_add]
  unfold zeroMultiplicity analyticOrderNatAt
  rw [key]

end ZetaZeros

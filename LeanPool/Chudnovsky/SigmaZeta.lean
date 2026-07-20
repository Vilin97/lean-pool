/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.Basic
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# The Weierstrass σ- and ζ-functions

Statements from chapter 1 of Milla, *A detailed proof of the Chudnovsky formula with means
of a basic first year approach* (arXiv:1809.00533v6, file `060_ElliptFunct.tex`):

* `PeriodPair.weierstrassSigma` : the Weierstrass σ-function
  `σ(z; L) = z·∏_{ω ∈ L, ω ≠ 0} (1 - z/ω)·exp(z/ω + z²/(2ω²))` (paper Def. `defisigma`);
* `PeriodPair.weierstrassZeta` : the Weierstrass ζ-function
  `ζ(z; L) = 1/z + ∑_{ω ∈ L, ω ≠ 0} (1/(z-ω) + 1/ω + z/ω²)` (paper Def. `defizeta`);
* convergence statements (paper Rem. `bemsigma`), oddness of σ and ζ (paper `sigmaodd`),
  the location and simplicity of the zeros of σ (paper Rem. `bemsigma`),
  `ζ = σ'/σ` (paper Def. `defizeta`) and `ζ' = -℘` (paper Def. `defiwp`).

All nontrivial proofs are `sorry`-ed for now; this file pins the statements.
-/

noncomputable section

namespace PeriodPair

open Complex Filter Topology Module

/-- The factor of the Weierstrass σ-product associated to a nonzero lattice point `w`:
`(1 - z/w)·exp(z/w + z²/(2w²))`. -/
def weierstrassSigmaTerm (z w : ℂ) : ℂ :=
  (1 - z / w) * Complex.exp (z / w + z ^ 2 / (2 * w ^ 2))

/-- The summand of the Weierstrass ζ-series associated to a nonzero lattice point `w`:
`1/(z-w) + 1/w + z/w²`. -/
def weierstrassZetaTerm (z w : ℂ) : ℂ :=
  1 / (z - w) + 1 / w + z / w ^ 2

variable (L : PeriodPair)

/-- The Weierstrass σ-function of the lattice `L` (paper Def. `defisigma`):
`σ(z; L) = z·∏_{ω ∈ L, ω ≠ 0} (1 - z/ω)·exp(z/ω + z²/(2ω²))`. -/
def weierstrassSigma (z : ℂ) : ℂ :=
  z * ∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm z (l.1 : ℂ)

/-- The Weierstrass ζ-function of the lattice `L` (paper Def. `defizeta`):
`ζ(z; L) = 1/z + ∑_{ω ∈ L, ω ≠ 0} (1/(z-ω) + 1/ω + z/ω²)`. -/
def weierstrassZeta (z : ℂ) : ℂ :=
  1 / z + ∑' l : {l : L.lattice // l ≠ 0}, weierstrassZetaTerm z (l.1 : ℂ)

/-! ## Helper lemmas -/

/-- Negation as an equivalence of the nonzero lattice points. -/
private def negNonzero : {l : L.lattice // l ≠ 0} ≃ {l : L.lattice // l ≠ 0} :=
  (Equiv.neg L.lattice).subtypeEquiv fun a ↦ by simp

@[simp] private lemma negNonzero_coe (l : {l : L.lattice // l ≠ 0}) :
    ((L.negNonzero l).1 : ℂ) = -(l.1 : ℂ) := by
  simp [negNonzero, Equiv.subtypeEquiv]

private lemma weierstrassSigmaTerm_neg_neg (z w : ℂ) :
    weierstrassSigmaTerm (-z) (-w) = weierstrassSigmaTerm z w := by
  simp only [weierstrassSigmaTerm, neg_div_neg_eq, neg_sq]

private lemma weierstrassZetaTerm_neg_neg (z w : ℂ) :
    weierstrassZetaTerm (-z) (-w) = -weierstrassZetaTerm z w := by
  simp only [weierstrassZetaTerm, neg_sq, show (-z - -w : ℂ) = -(z - w) by ring,
    div_neg, neg_div, one_div]
  ring

private lemma weierstrassZetaTerm_eq (z w : ℂ) (hw : w ≠ 0) (hzw : z ≠ w) :
    weierstrassZetaTerm z w = z ^ 2 / (w ^ 2 * (z - w)) := by
  have h1 : z - w ≠ 0 := sub_ne_zero.mpr hzw
  rw [weierstrassZetaTerm]
  field_simp
  ring

/-- Summability of `‖ω‖⁻³` over the nonzero lattice points. -/
private lemma summable_norm_rpow_neg_three :
    Summable (fun l : {l : L.lattice // l ≠ 0} ↦ ‖(l.1 : ℂ)‖ ^ (-3 : ℝ)) := by
  have h : (-3 : ℝ) < -(Module.finrank ℤ L.lattice : ℝ) := by
    rw [L.finrank_lattice]; norm_num
  exact (ZLattice.summable_norm_rpow L.lattice (-3) h).comp_injective Subtype.val_injective

/-- All but finitely many nonzero lattice points have norm `≥ r`. -/
private lemma cofinite_norm_ge (r : ℝ) :
    ∀ᶠ l in (Filter.cofinite : Filter {l : L.lattice // l ≠ 0}), r ≤ ‖(l.1 : ℂ)‖ := by
  rw [Filter.eventually_cofinite]
  have hfin : (Metric.closedBall (0 : L.lattice) r).Finite :=
    isCompact_iff_finite.mp (isCompact_closedBall _ _)
  refine Set.Finite.subset (hfin.preimage (Subtype.val_injective.injOn)) ?_
  intro l hl
  simp only [Set.mem_setOf_eq, not_le] at hl
  rw [Set.mem_preimage, Metric.mem_closedBall, Subtype.dist_eq]
  simp only [ZeroMemClass.coe_zero, dist_zero_right]
  exact hl.le

/-- The pointwise bound `‖ζ-summand‖ ≤ 2‖z‖²‖ω‖⁻³` for `‖ω‖ ≥ 2‖z‖`. -/
private lemma norm_weierstrassZetaTerm_le (z w : ℂ) (hw : w ≠ 0) (h : 2 * ‖z‖ ≤ ‖w‖) :
    ‖weierstrassZetaTerm z w‖ ≤ 2 * ‖z‖ ^ 2 * ‖w‖ ^ (-3 : ℝ) := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hznw : z ≠ w := by
    rintro rfl
    have : ‖z‖ ≤ 0 := by linarith
    exact hw (by rw [← norm_eq_zero]; linarith [norm_nonneg z])
  have hzw : z - w ≠ 0 := sub_ne_zero.mpr hznw
  have h1 : ‖w‖ / 2 ≤ ‖z - w‖ := by
    rw [norm_sub_rev]
    have := norm_sub_norm_le w z
    linarith
  have hbound : ‖weierstrassZetaTerm z w‖ ≤ 2 * ‖z‖ ^ 2 / ‖w‖ ^ 3 := by
    rw [weierstrassZetaTerm_eq z w hw hznw, norm_div, norm_mul, norm_pow, norm_pow,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 2 * ‖z‖ ^ 2 * ‖w‖ ^ 2 by positivity),
      norm_nonneg z, hwpos, h1, sq_nonneg ‖z‖]
  refine hbound.trans_eq ?_
  rw [show (-3 : ℝ) = -(3 : ℕ) by norm_num, Real.rpow_neg hwpos.le, Real.rpow_natCast]
  ring

/-- The pointwise bound `‖σ-factor − 1‖ ≤ (4/3)‖z‖³‖ω‖⁻³` for `‖ω‖ ≥ 2‖z‖`. -/
private lemma norm_weierstrassSigmaTerm_sub_one_le (z w : ℂ) (hw : w ≠ 0) (h : 2 * ‖z‖ ≤ ‖w‖) :
    ‖weierstrassSigmaTerm z w - 1‖ ≤ 4 / 3 * ‖z‖ ^ 3 * ‖w‖ ^ (-3 : ℝ) := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hnorm : ‖z / w‖ ≤ 1 / 2 := by
    rw [norm_div, div_le_iff₀ hwpos]; linarith
  have hlt1 : ‖-(z / w)‖ < 1 := by rw [norm_neg]; linarith
  have h1a : (1 : ℂ) - z / w ≠ 0 := by
    intro H
    rw [sub_eq_zero] at H
    rw [← H, norm_one] at hnorm
    norm_num at hnorm
  have hexp : weierstrassSigmaTerm z w =
      Complex.exp (Complex.log (1 + -(z / w)) - logTaylor 3 (-(z / w))) := by
    have h1 : (1 : ℂ) + -(z / w) = 1 - z / w := by ring
    have htaylor : logTaylor 3 (-(z / w)) = -(z / w + z ^ 2 / (2 * w ^ 2)) := by
      simp only [logTaylor, Finset.sum_range_succ, Finset.sum_range_zero]
      push_cast
      ring
    rw [h1, htaylor, sub_neg_eq_add, Complex.exp_add, Complex.exp_log h1a, weierstrassSigmaTerm]
  rw [hexp]
  have hubound : ‖Complex.log (1 + -(z / w)) - logTaylor 3 (-(z / w))‖ ≤ 2 / 3 * ‖z / w‖ ^ 3 := by
    have hinv : (1 - ‖z / w‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      rw [inv_eq_one_div]; linarith
    calc ‖Complex.log (1 + -(z / w)) - logTaylor 3 (-(z / w))‖
        ≤ ‖-(z / w)‖ ^ (2 + 1) * (1 - ‖-(z / w)‖)⁻¹ / (2 + 1) :=
          norm_log_sub_logTaylor_le 2 hlt1
      _ = ‖z / w‖ ^ 3 * (1 - ‖z / w‖)⁻¹ / 3 := by rw [norm_neg]; norm_num
      _ ≤ ‖z / w‖ ^ 3 * 2 / 3 := by gcongr
      _ = 2 / 3 * ‖z / w‖ ^ 3 := by ring
  have hule1 : ‖Complex.log (1 + -(z / w)) - logTaylor 3 (-(z / w))‖ ≤ 1 := by
    refine hubound.trans ?_
    nlinarith [pow_le_pow_left₀ (norm_nonneg (z / w)) hnorm 3, norm_nonneg (z / w)]
  calc ‖Complex.exp (Complex.log (1 + -(z / w)) - logTaylor 3 (-(z / w))) - 1‖
      ≤ 2 * ‖Complex.log (1 + -(z / w)) - logTaylor 3 (-(z / w))‖ := norm_exp_sub_one_le hule1
    _ ≤ 2 * (2 / 3 * ‖z / w‖ ^ 3) := by gcongr
    _ = 4 / 3 * ‖z / w‖ ^ 3 := by ring
    _ = 4 / 3 * ‖z‖ ^ 3 * ‖w‖ ^ (-3 : ℝ) := by
        rw [norm_div, div_pow, show (-3 : ℝ) = -(3 : ℕ) by norm_num,
          Real.rpow_neg hwpos.le, Real.rpow_natCast]
        ring

/-- A σ-factor vanishes only at its own lattice point. -/
private lemma weierstrassSigmaTerm_ne_zero {z w : ℂ} (hw : w ≠ 0) (hzw : z ≠ w) :
    weierstrassSigmaTerm z w ≠ 0 := by
  rw [weierstrassSigmaTerm]
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  rw [sub_ne_zero]
  exact fun H ↦ hzw ((div_eq_one_iff_eq hw).mp H.symm)

/-- The logarithmic derivative of a σ-factor is the corresponding ζ-summand. -/
private lemma logDeriv_weierstrassSigmaTerm {z w : ℂ} (hw : w ≠ 0) (hzw : z ≠ w) :
    logDeriv (fun z ↦ weierstrassSigmaTerm z w) z = weierstrassZetaTerm z w := by
  have h1a : (1 : ℂ) - z / w ≠ 0 := by
    rw [sub_ne_zero]; exact fun H ↦ hzw ((div_eq_one_iff_eq hw).mp H.symm)
  have hzw' : z - w ≠ 0 := sub_ne_zero.mpr hzw
  have hg : HasDerivAt (fun z : ℂ ↦ z / w + z ^ 2 / (2 * w ^ 2)) (1 / w + z / w ^ 2) z := by
    have hA : HasDerivAt (fun z : ℂ ↦ z / w) (1 / w) z := (hasDerivAt_id z).div_const w
    have hB : HasDerivAt (fun z : ℂ ↦ z ^ 2 / (2 * w ^ 2)) (z / w ^ 2) z := by
      have h2 : HasDerivAt (fun z : ℂ ↦ z ^ 2 / (2 * w ^ 2)) ((2 * z) / (2 * w ^ 2)) z := by
        simpa using (hasDerivAt_pow 2 z).div_const (2 * w ^ 2)
      rwa [mul_div_mul_left _ _ (two_ne_zero)] at h2
    exact hA.add hB
  have d1 : deriv (fun z : ℂ ↦ 1 - z / w) z = -(1 / w) :=
    (((hasDerivAt_id z).div_const w).const_sub 1).deriv
  have hmul := logDeriv_mul (f := fun z : ℂ ↦ 1 - z / w)
    (g := fun z : ℂ ↦ Complex.exp (z / w + z ^ 2 / (2 * w ^ 2))) z h1a (Complex.exp_ne_zero _)
    (by fun_prop) (by fun_prop)
  rw [show (fun z ↦ weierstrassSigmaTerm z w)
      = fun z : ℂ ↦ (1 - z / w) * Complex.exp (z / w + z ^ 2 / (2 * w ^ 2)) from rfl, hmul,
    logDeriv_apply, logDeriv_apply, d1, hg.cexp.deriv, weierstrassZetaTerm]
  have hwz : w - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzw)
  field_simp
  ring

/-- The derivative of a ζ-summand. -/
private lemma deriv_weierstrassZetaTerm {z w : ℂ} (_hw : w ≠ 0) (hzw : z ≠ w) :
    deriv (fun z ↦ weierstrassZetaTerm z w) z = 1 / w ^ 2 - 1 / (z - w) ^ 2 := by
  have hzw' : z - w ≠ 0 := sub_ne_zero.mpr hzw
  have hd : HasDerivAt (fun z : ℂ ↦ weierstrassZetaTerm z w)
      (-1 / (z - w) ^ 2 + 0 + 1 / w ^ 2) z := by
    unfold weierstrassZetaTerm
    have h1 : HasDerivAt (fun z : ℂ ↦ 1 / (z - w)) (-1 / (z - w) ^ 2) z := by
      simp only [one_div]
      exact ((hasDerivAt_id z).sub_const w).inv hzw'
    have h2 : HasDerivAt (fun _ : ℂ ↦ 1 / w) (0 : ℂ) z := hasDerivAt_const z _
    have h3 : HasDerivAt (fun z : ℂ ↦ z / w ^ 2) (1 / w ^ 2) z := by
      simpa using (hasDerivAt_id z).div_const (w ^ 2)
    exact (h1.add h2).add h3
  rw [hd.deriv]; ring

/-- Summability of `‖σ-factor − 1‖` over the nonzero lattice points. -/
private lemma summable_norm_sigma_sub_one (z : ℂ) :
    Summable (fun l : {l : L.lattice // l ≠ 0} ↦ ‖weierstrassSigmaTerm z (l.1 : ℂ) - 1‖) := by
  refine Summable.of_norm_bounded_eventually
    ((L.summable_norm_rpow_neg_three).mul_left (4 / 3 * ‖z‖ ^ 3)) ?_
  filter_upwards [L.cofinite_norm_ge (2 * ‖z‖)] with l hl
  rw [norm_norm]
  have hw : (l.1 : ℂ) ≠ 0 := by simpa using l.2
  exact norm_weierstrassSigmaTerm_sub_one_le z (l.1 : ℂ) hw hl

/-- On a compact set the norm is bounded by a positive constant. -/
private lemma exists_norm_bound_on_compact {K : Set ℂ} (hK : IsCompact K) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ K, ‖x‖ ≤ r := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    refine ⟨max r 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x hx => ?_⟩
    have := hr hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)

/-! ## Convergence (paper Rem. `bemsigma`) -/

/-- The σ-product converges for every `z`. -/
theorem multipliable_weierstrassSigmaTerm (z : ℂ) :
    Multipliable fun l : {l : L.lattice // l ≠ 0} ↦ weierstrassSigmaTerm z (l.1 : ℂ) := by
  have hsummable :
      Summable (fun l : {l : L.lattice // l ≠ 0} ↦ weierstrassSigmaTerm z (l.1 : ℂ) - 1) := by
    refine Summable.of_norm_bounded_eventually
      ((L.summable_norm_rpow_neg_three).mul_left (4 / 3 * ‖z‖ ^ 3)) ?_
    filter_upwards [L.cofinite_norm_ge (2 * ‖z‖)] with l hl
    have hw : (l.1 : ℂ) ≠ 0 := by simpa using l.2
    exact norm_weierstrassSigmaTerm_sub_one_le z (l.1 : ℂ) hw hl
  exact (Complex.multipliable_one_add_of_summable hsummable).congr fun l ↦ by ring

/-- The σ-product converges locally uniformly on `ℂ`. -/
theorem hasProdLocallyUniformly_weierstrassSigmaTerm :
    HasProdLocallyUniformly
      (fun (l : {l : L.lattice // l ≠ 0}) (z : ℂ) ↦ weierstrassSigmaTerm z (l.1 : ℂ))
      (fun z ↦ ∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm z (l.1 : ℂ)) := by
  apply hasProdLocallyUniformly_of_forall_compact
  intro K hK
  obtain ⟨r, hr0, hKr⟩ := exists_norm_bound_on_compact hK
  have key := Summable.hasProdUniformlyOn_one_add
    (f := fun (l : {l : L.lattice // l ≠ 0}) (x : ℂ) ↦ weierstrassSigmaTerm x (l.1 : ℂ) - 1)
    (K := K) (u := fun l ↦ 4 / 3 * r ^ 3 * ‖(l.1 : ℂ)‖ ^ (-3 : ℝ)) hK
    ((L.summable_norm_rpow_neg_three).mul_left (4 / 3 * r ^ 3)) ?_ ?_
  · refine (key.congr ?_).congr_right ?_
    · exact Filter.Eventually.of_forall fun n x _ ↦ Finset.prod_congr rfl fun i _ ↦ by ring
    · exact fun x _ ↦ tprod_congr fun l ↦ by ring
  · filter_upwards [L.cofinite_norm_ge (2 * r)] with l hl x hx
    have hw : (l.1 : ℂ) ≠ 0 := by simpa using l.2
    have hx' : ‖x‖ ≤ r := hKr x hx
    have h2 : 2 * ‖x‖ ≤ ‖(l.1 : ℂ)‖ := le_trans (by linarith) hl
    calc ‖weierstrassSigmaTerm x (l.1 : ℂ) - 1‖
        ≤ 4 / 3 * ‖x‖ ^ 3 * ‖(l.1 : ℂ)‖ ^ (-3 : ℝ) :=
          norm_weierstrassSigmaTerm_sub_one_le x (l.1 : ℂ) hw h2
      _ ≤ 4 / 3 * r ^ 3 * ‖(l.1 : ℂ)‖ ^ (-3 : ℝ) := by gcongr
  · intro i
    apply Continuous.continuousOn
    unfold weierstrassSigmaTerm
    fun_prop

/-- The ζ-series converges away from the lattice. -/
theorem summable_weierstrassZetaTerm (z : ℂ) (_hz : z ∉ L.lattice) :
    Summable fun l : {l : L.lattice // l ≠ 0} ↦ weierstrassZetaTerm z (l.1 : ℂ) := by
  refine Summable.of_norm_bounded_eventually
    ((L.summable_norm_rpow_neg_three).mul_left (2 * ‖z‖ ^ 2)) ?_
  filter_upwards [L.cofinite_norm_ge (2 * ‖z‖)] with l hl
  have hw : (l.1 : ℂ) ≠ 0 := by simpa using l.2
  exact norm_weierstrassZetaTerm_le z (l.1 : ℂ) hw hl

/-- The ζ-series converges locally uniformly away from the lattice. -/
theorem hasSumLocallyUniformlyOn_weierstrassZetaTerm :
    HasSumLocallyUniformlyOn
      (fun (l : {l : L.lattice // l ≠ 0}) (z : ℂ) ↦ weierstrassZetaTerm z (l.1 : ℂ))
      (fun z ↦ ∑' l : {l : L.lattice // l ≠ 0}, weierstrassZetaTerm z (l.1 : ℂ))
      (↑L.lattice)ᶜ := by
  apply hasSumLocallyUniformlyOn_of_forall_compact L.isClosed_lattice.isOpen_compl
  intro K hKsub hK
  obtain ⟨r, hr0, hKr⟩ := exists_norm_bound_on_compact hK
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  apply tendstoUniformlyOn_tsum_of_cofinite_eventually
    ((L.summable_norm_rpow_neg_three).mul_left (2 * r ^ 2))
  filter_upwards [L.cofinite_norm_ge (2 * r)] with l hl x hx
  have hw : (l.1 : ℂ) ≠ 0 := by simpa using l.2
  have hx' : ‖x‖ ≤ r := hKr x hx
  have h2 : 2 * ‖x‖ ≤ ‖(l.1 : ℂ)‖ := le_trans (by linarith) hl
  calc ‖weierstrassZetaTerm x (l.1 : ℂ)‖
      ≤ 2 * ‖x‖ ^ 2 * ‖(l.1 : ℂ)‖ ^ (-3 : ℝ) := norm_weierstrassZetaTerm_le x (l.1 : ℂ) hw h2
    _ ≤ 2 * r ^ 2 * ‖(l.1 : ℂ)‖ ^ (-3 : ℝ) := by gcongr

/-! ## Basic properties -/

/-- Each σ-factor is entire (as a function of `z`). -/
private lemma differentiable_weierstrassSigmaTerm (w : ℂ) :
    Differentiable ℂ (fun z ↦ weierstrassSigmaTerm z w) := by
  unfold weierstrassSigmaTerm; fun_prop

/-- The σ-product is entire (as a function of `z`). -/
private lemma differentiable_tprod_weierstrassSigmaTerm :
    Differentiable ℂ
      (fun z ↦ ∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm z (l.1 : ℂ)) := by
  rw [← differentiableOn_univ]
  refine
    (L.hasProdLocallyUniformly_weierstrassSigmaTerm.hasProdLocallyUniformlyOn).differentiableOn
      (.of_forall fun _ ↦ ?_) isOpen_univ
  simpa [Finset.prod_fn] using
    DifferentiableOn.finsetProd fun i _ ↦
      (differentiable_weierstrassSigmaTerm (i.1 : ℂ)).differentiableOn

/-- `σ` is an entire function. -/
theorem differentiable_weierstrassSigma : Differentiable ℂ L.weierstrassSigma := by
  change Differentiable ℂ fun z ↦
    z * ∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm z (l.1 : ℂ)
  exact fun z ↦ differentiableAt_id.mul (L.differentiable_tprod_weierstrassSigmaTerm z)

/-- `ζ` is holomorphic away from the lattice. -/
theorem differentiableOn_weierstrassZeta :
    DifferentiableOn ℂ L.weierstrassZeta (↑L.lattice)ᶜ := by
  have hopen : IsOpen ((↑L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  have hsum : DifferentiableOn ℂ
      (fun z ↦ ∑' l : {l : L.lattice // l ≠ 0}, weierstrassZetaTerm z (l.1 : ℂ))
      (↑L.lattice)ᶜ := by
    refine
      (L.hasSumLocallyUniformlyOn_weierstrassZetaTerm.summableLocallyUniformlyOn).differentiableOn
        hopen ?_
    intro l r hr
    have hrne : r ≠ (l.1 : ℂ) := by rintro rfl; exact hr l.1.2
    have hw : (l.1 : ℂ) ≠ 0 := by simpa using l.2
    have hrw : r - (l.1 : ℂ) ≠ 0 := sub_ne_zero.mpr hrne
    unfold weierstrassZetaTerm
    fun_prop (disch := assumption)
  have hinv : DifferentiableOn ℂ (fun z : ℂ ↦ 1 / z) (↑L.lattice)ᶜ := by
    intro z hz
    have hz0 : z ≠ 0 := by rintro rfl; exact hz L.lattice.zero_mem
    exact ((differentiableAt_const (1 : ℂ)).div differentiableAt_id hz0).differentiableWithinAt
  change DifferentiableOn ℂ
    (fun z ↦ 1 / z + ∑' l : {l : L.lattice // l ≠ 0}, weierstrassZetaTerm z (l.1 : ℂ)) _
  exact hinv.add hsum

/-- `σ` is an odd function (paper Prop. `sigmaodd`). -/
theorem weierstrassSigma_neg (z : ℂ) :
    L.weierstrassSigma (-z) = -L.weierstrassSigma z := by
  have hprod : (∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm (-z) (l.1 : ℂ))
      = ∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm z (l.1 : ℂ) := by
    rw [← (L.negNonzero).tprod_eq (fun l ↦ weierstrassSigmaTerm z (l.1 : ℂ))]
    exact tprod_congr fun l ↦ by
      rw [L.negNonzero_coe, ← weierstrassSigmaTerm_neg_neg z (-(l.1 : ℂ)), neg_neg]
  simp only [weierstrassSigma, hprod]
  ring

/-- `ζ` is an odd function. -/
theorem weierstrassZeta_neg (z : ℂ) :
    L.weierstrassZeta (-z) = -L.weierstrassZeta z := by
  have hsum : (∑' l : {l : L.lattice // l ≠ 0}, weierstrassZetaTerm (-z) (l.1 : ℂ))
      = -∑' l : {l : L.lattice // l ≠ 0}, weierstrassZetaTerm z (l.1 : ℂ) := by
    rw [← (L.negNonzero).tsum_eq (fun l ↦ weierstrassZetaTerm (-z) (l.1 : ℂ)), ← tsum_neg]
    exact tsum_congr fun l ↦ by rw [L.negNonzero_coe, weierstrassZetaTerm_neg_neg]
  simp only [weierstrassZeta, hsum]
  rw [neg_add]
  congr 1
  rw [one_div, one_div, inv_neg]

/-! ## Zeros of σ (paper Rem. `bemsigma`) -/

/-- The zeros of `σ` are exactly the lattice points. -/
theorem weierstrassSigma_eq_zero_iff (z : ℂ) :
    L.weierstrassSigma z = 0 ↔ z ∈ L.lattice := by
  constructor
  · intro h
    by_contra hz
    have hz0 : z ≠ 0 := by rintro rfl; exact hz L.lattice.zero_mem
    rw [weierstrassSigma, mul_eq_zero] at h
    rcases h with h | h
    · exact hz0 h
    · have hfac : ∀ l : {l : L.lattice // l ≠ 0},
          (1 : ℂ) + (weierstrassSigmaTerm z (l.1 : ℂ) - 1) ≠ 0 := by
        intro l
        rw [show (1 : ℂ) + (weierstrassSigmaTerm z (l.1 : ℂ) - 1)
          = weierstrassSigmaTerm z (l.1 : ℂ) by ring]
        refine weierstrassSigmaTerm_ne_zero (by simpa using l.2) ?_
        rintro rfl
        exact hz l.1.2
      refine tprod_one_add_ne_zero_of_summable
        (f := fun l : {l : L.lattice // l ≠ 0} ↦ weierstrassSigmaTerm z (l.1 : ℂ) - 1)
        hfac (L.summable_norm_sigma_sub_one z) ?_
      rw [← h]
      exact tprod_congr fun l : {l : L.lattice // l ≠ 0} ↦ by ring
  · intro hz
    rw [weierstrassSigma]
    by_cases hz0 : z = 0
    · simp [hz0]
    · apply mul_eq_zero_of_right
      have hlmem : (⟨z, hz⟩ : L.lattice) ≠ 0 := fun H ↦ hz0 (by simpa using congrArg Subtype.val H)
      refine (hasProd_zero_of_exists_eq_zero ⟨⟨⟨z, hz⟩, hlmem⟩, ?_⟩).tprod_eq
      change weierstrassSigmaTerm z z = 0
      rw [weierstrassSigmaTerm, div_self hz0]
      simp

/-- Generic differentiability of an infinite product `∏' i, g i z` of entire functions that
converges locally uniformly, given for each compact-radius `r` a summable bound on `‖g i · − 1‖`
on the ball of radius `r`. -/
private lemma differentiable_tprod_family {ι : Type*} (g : ι → ℂ → ℂ)
    (hdiff : ∀ i, Differentiable ℂ (g i))
    (hbound : ∀ r : ℝ, 0 ≤ r → ∃ u : ι → ℝ, Summable u ∧
      ∀ᶠ i in (Filter.cofinite : Filter ι), ∀ x : ℂ, ‖x‖ ≤ r → ‖g i x - 1‖ ≤ u i) :
    Differentiable ℂ (fun z ↦ ∏' i, g i z) := by
  rw [← differentiableOn_univ]
  have hLU : HasProdLocallyUniformly g (fun z ↦ ∏' i, g i z) := by
    apply hasProdLocallyUniformly_of_forall_compact
    intro K hK
    obtain ⟨r, hr0, hKr⟩ := exists_norm_bound_on_compact hK
    obtain ⟨u, hu, hub⟩ := hbound r hr0.le
    have key := Summable.hasProdUniformlyOn_one_add
      (f := fun (i : ι) (x : ℂ) ↦ g i x - 1) (K := K) (u := u) hK hu ?_ ?_
    · refine (key.congr ?_).congr_right ?_
      · exact Filter.Eventually.of_forall fun n x _ ↦ Finset.prod_congr rfl fun i _ ↦ by ring
      · exact fun x _ ↦ tprod_congr fun i ↦ by ring
    · filter_upwards [hub] with i hi x hx
      exact hi x (hKr x hx)
    · exact fun i ↦ ((hdiff i).continuous.sub continuous_const).continuousOn
  refine hLU.hasProdLocallyUniformlyOn.differentiableOn (.of_forall fun _ ↦ ?_) isOpen_univ
  simpa [Finset.prod_fn] using DifferentiableOn.finsetProd fun i _ ↦ (hdiff i).differentiableOn

/-- At a nonzero lattice point `ω`, the derivative of `σ` is nonzero: split the factor at `ω`
out of the product, `σ z = (z · Q z) · (σ-factor at ω)`, where the factor vanishes simply and
`z · Q z` is nonzero at `ω`. -/
private lemma deriv_weierstrassSigma_ne_zero_at (i₀ : {l : L.lattice // l ≠ 0}) :
    deriv L.weierstrassSigma (i₀.1 : ℂ) ≠ 0 := by
  classical
  set w : ℂ := (i₀.1 : ℂ) with hw
  have hwne : w ≠ 0 := by rw [hw]; simpa using i₀.2
  -- the σ-product with the factor at `i₀` replaced by `1`
  set g : {l : L.lattice // l ≠ 0} → ℂ → ℂ :=
    fun n z ↦ if n = i₀ then 1 else weierstrassSigmaTerm z (n.1 : ℂ) with hg
  set Q : ℂ → ℂ := fun z ↦ ∏' n : {l : L.lattice // l ≠ 0}, g n z with hQ
  have hgdiff : ∀ n, Differentiable ℂ (g n) := by
    intro n
    simp only [hg]
    by_cases h : n = i₀
    · simp only [if_pos h]; exact differentiable_const 1
    · simp only [if_neg h]; exact differentiable_weierstrassSigmaTerm (n.1 : ℂ)
  have hQdiff : Differentiable ℂ Q := by
    rw [hQ]
    refine differentiable_tprod_family g hgdiff (fun r hr ↦ ?_)
    refine ⟨fun n ↦ 4 / 3 * r ^ 3 * ‖(n.1 : ℂ)‖ ^ (-3 : ℝ),
      (L.summable_norm_rpow_neg_three).mul_left _, ?_⟩
    filter_upwards [L.cofinite_norm_ge (2 * r)] with n hn x hx
    simp only [hg]
    by_cases h : n = i₀
    · simp only [if_pos h, sub_self, norm_zero]
      positivity
    · simp only [if_neg h]
      have hwn : (n.1 : ℂ) ≠ 0 := by simpa using n.2
      have h2 : 2 * ‖x‖ ≤ ‖(n.1 : ℂ)‖ := le_trans (by linarith) hn
      calc ‖weierstrassSigmaTerm x (n.1 : ℂ) - 1‖
          ≤ 4 / 3 * ‖x‖ ^ 3 * ‖(n.1 : ℂ)‖ ^ (-3 : ℝ) :=
            norm_weierstrassSigmaTerm_sub_one_le x (n.1 : ℂ) hwn h2
        _ ≤ 4 / 3 * r ^ 3 * ‖(n.1 : ℂ)‖ ^ (-3 : ℝ) := by gcongr
  have hsplit : ∀ z : ℂ,
      (∏' n : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm z (n.1 : ℂ))
        = weierstrassSigmaTerm z w * Q z := by
    intro z
    have hsummg : Summable (fun n : {l : L.lattice // l ≠ 0} ↦ g n z - 1) := by
      refine Summable.of_norm_bounded (L.summable_norm_sigma_sub_one z) (fun n ↦ ?_)
      simp only [hg]
      split_ifs with h
      · simp only [sub_self, norm_zero]; exact norm_nonneg _
      · exact le_refl _
    have hmultg : Multipliable (fun n : {l : L.lattice // l ≠ 0} ↦ g n z) :=
      (Complex.multipliable_one_add_of_summable hsummg).congr fun n ↦ by ring
    have hthis := eq_mul_of_hasProd_ite (L.multipliable_weierstrassSigmaTerm z).hasProd i₀ (Q z)
      (by rw [hQ]; exact hmultg.hasProd)
    rw [hthis, hw]; ring
  have hQw : Q w ≠ 0 := by
    change (∏' n : {l : L.lattice // l ≠ 0}, g n w) ≠ 0
    have hle : ∀ n, ‖g n w - 1‖ ≤ ‖weierstrassSigmaTerm w (n.1 : ℂ) - 1‖ := by
      intro n; simp only [hg]
      split_ifs with h
      · simp only [sub_self, norm_zero]; exact norm_nonneg _
      · exact le_refl _
    have hfac : ∀ n, (1 : ℂ) + (g n w - 1) ≠ 0 := by
      intro n
      rw [show (1 : ℂ) + (g n w - 1) = g n w by ring]
      simp only [hg]
      by_cases h : n = i₀
      · simp only [if_pos h]; exact one_ne_zero
      · simp only [if_neg h]
        refine weierstrassSigmaTerm_ne_zero (by simpa using n.2) (fun hcontra ↦ ?_)
        exact h (Subtype.ext (Subtype.ext hcontra.symm))
    have hsummable : Summable (fun n ↦ ‖g n w - 1‖) :=
      Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) hle (L.summable_norm_sigma_sub_one w)
    have hne := tprod_one_add_ne_zero_of_summable
      (f := fun n : {l : L.lattice // l ≠ 0} ↦ g n w - 1) hfac hsummable
    rwa [tprod_congr fun n ↦ (by ring : (1 : ℂ) + (g n w - 1) = g n w)] at hne
  -- derivative of the single factor at its own zero
  have hBderiv : HasDerivAt (fun z ↦ weierstrassSigmaTerm z w)
      (-(1 / w) * Complex.exp (w / w + w ^ 2 / (2 * w ^ 2))) w := by
    unfold weierstrassSigmaTerm
    have hg : HasDerivAt (fun z : ℂ ↦ z / w + z ^ 2 / (2 * w ^ 2)) (1 / w + w / w ^ 2) w := by
      have hA : HasDerivAt (fun z : ℂ ↦ z / w) (1 / w) w := (hasDerivAt_id w).div_const w
      have hB : HasDerivAt (fun z : ℂ ↦ z ^ 2 / (2 * w ^ 2)) (w / w ^ 2) w := by
        have h2 : HasDerivAt (fun z : ℂ ↦ z ^ 2 / (2 * w ^ 2)) ((2 * w) / (2 * w ^ 2)) w := by
          simpa using (hasDerivAt_pow 2 w).div_const (2 * w ^ 2)
        rwa [mul_div_mul_left _ _ (two_ne_zero)] at h2
      exact hA.add hB
    have hlin : HasDerivAt (fun z : ℂ ↦ 1 - z / w) (-(1 / w)) w :=
      ((hasDerivAt_id w).div_const w).const_sub 1
    have hmul := hlin.mul hg.cexp
    have hV : (-(1 / w) * Complex.exp (w / w + w ^ 2 / (2 * w ^ 2)))
        = -(1 / w) * Complex.exp (w / w + w ^ 2 / (2 * w ^ 2))
          + (1 - w / w) * (Complex.exp (w / w + w ^ 2 / (2 * w ^ 2)) * (1 / w + w / w ^ 2)) := by
      rw [div_self hwne]; ring
    rw [hV]
    exact hmul
  have hBw : weierstrassSigmaTerm w w = 0 := by
    rw [weierstrassSigmaTerm, div_self hwne]; simp
  have hdB_ne : (-(1 / w) * Complex.exp (w / w + w ^ 2 / (2 * w ^ 2))) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (one_div_ne_zero hwne)) (Complex.exp_ne_zero _)
  have hσeq : L.weierstrassSigma = fun z ↦ (z * Q z) * weierstrassSigmaTerm z w := by
    funext z
    change z * (∏' n : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm z (n.1 : ℂ))
      = (z * Q z) * weierstrassSigmaTerm z w
    rw [hsplit z]; ring
  rw [hσeq]
  have hzQ : HasDerivAt (fun z : ℂ ↦ z * Q z) (1 * Q w + w * deriv Q w) w :=
    (hasDerivAt_id w).mul (hQdiff w).hasDerivAt
  have hfull : HasDerivAt (fun z : ℂ ↦ (z * Q z) * weierstrassSigmaTerm z w)
      (w * Q w * (-(1 / w) * Complex.exp (w / w + w ^ 2 / (2 * w ^ 2)))) w := by
    have hm := hzQ.mul hBderiv
    have hV : (w * Q w * (-(1 / w) * Complex.exp (w / w + w ^ 2 / (2 * w ^ 2))))
        = (1 * Q w + w * deriv Q w) * weierstrassSigmaTerm w w
          + w * Q w * (-(1 / w) * Complex.exp (w / w + w ^ 2 / (2 * w ^ 2))) := by
      rw [hBw]; ring
    rw [hV]
    exact hm
  rw [hfull.deriv]
  exact mul_ne_zero (mul_ne_zero hwne hQw) hdB_ne

/-- The zeros of `σ` at the lattice points are simple (order `1`). -/
theorem meromorphicOrderAt_weierstrassSigma (l : ℂ) (hl : l ∈ L.lattice) :
    meromorphicOrderAt L.weierstrassSigma l = 1 := by
  have hAn : AnalyticAt ℂ L.weierstrassSigma l := L.differentiable_weierstrassSigma.analyticAt l
  have hzero : L.weierstrassSigma l = 0 := (L.weierstrassSigma_eq_zero_iff l).mpr hl
  have hderiv : deriv L.weierstrassSigma l ≠ 0 := by
    by_cases hl0 : l = 0
    · -- `l = 0`: `σ z = z · P z`, and `P 0 = 1`, so `σ' 0 = 1 ≠ 0`.
      subst hl0
      have hP : Differentiable ℂ
          (fun z ↦ ∏' n : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm z (n.1 : ℂ)) :=
        L.differentiable_tprod_weierstrassSigmaTerm
      have hP0 :
          (∏' n : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm (0 : ℂ) (n.1 : ℂ)) = 1 := by
        have : (fun n : {l : L.lattice // l ≠ 0} ↦ weierstrassSigmaTerm (0 : ℂ) (n.1 : ℂ))
            = fun _ ↦ (1 : ℂ) := by
          funext n; simp [weierstrassSigmaTerm]
        rw [this, tprod_one]
      have hd : HasDerivAt L.weierstrassSigma _ (0 : ℂ) :=
        (hasDerivAt_id (0 : ℂ)).mul (hP 0).hasDerivAt
      rw [hd.deriv]
      simp [hP0]
    · -- `l ≠ 0`: reduce to the split-factor lemma at the lattice point `l`.
      have hmem : (⟨l, hl⟩ : L.lattice) ≠ 0 :=
        fun H ↦ hl0 (by simpa using congrArg Subtype.val H)
      exact L.deriv_weierstrassSigma_ne_zero_at ⟨⟨l, hl⟩, hmem⟩
  have hord : analyticOrderAt L.weierstrassSigma l = 1 :=
    hAn.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero hderiv
  rw [hAn.meromorphicOrderAt_eq, hord]
  rfl

/-! ## The logarithmic derivative and `ζ' = -℘` -/

/-- `ζ` is the logarithmic derivative of `σ` (paper Def. `defizeta`). -/
theorem logDeriv_weierstrassSigma (z : ℂ) (hz : z ∉ L.lattice) :
    logDeriv L.weierstrassSigma z = L.weierstrassZeta z := by
  have hz0 : z ≠ 0 := by rintro rfl; exact hz L.lattice.zero_mem
  have hopen : IsOpen ((↑L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  have hzne : ∀ l : {l : L.lattice // l ≠ 0}, z ≠ (l.1 : ℂ) := by
    intro l; rintro rfl; exact hz l.1.2
  have hwne : ∀ l : {l : L.lattice // l ≠ 0}, (l.1 : ℂ) ≠ 0 := fun l ↦ by simpa using l.2
  have hfacne : ∀ l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm z (l.1 : ℂ) ≠ 0 :=
    fun l ↦ weierstrassSigmaTerm_ne_zero (hwne l) (hzne l)
  have hlogterm : ∀ l : {l : L.lattice // l ≠ 0},
      logDeriv (fun z ↦ weierstrassSigmaTerm z (l.1 : ℂ)) z = weierstrassZetaTerm z (l.1 : ℂ) :=
    fun l ↦ logDeriv_weierstrassSigmaTerm (hwne l) (hzne l)
  have hprodne : (∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm z (l.1 : ℂ)) ≠ 0 := by
    have h := tprod_one_add_ne_zero_of_summable
      (f := fun l : {l : L.lattice // l ≠ 0} ↦ weierstrassSigmaTerm z (l.1 : ℂ) - 1)
      (fun l ↦ by
        rw [show (1 : ℂ) + (weierstrassSigmaTerm z (l.1 : ℂ) - 1)
          = weierstrassSigmaTerm z (l.1 : ℂ) by ring]
        exact hfacne l)
      (L.summable_norm_sigma_sub_one z)
    rwa [tprod_congr fun l : {l : L.lattice // l ≠ 0} ↦ (by ring :
      (1 : ℂ) + (weierstrassSigmaTerm z (l.1 : ℂ) - 1) = weierstrassSigmaTerm z (l.1 : ℂ))] at h
  have hlogP :
      logDeriv (fun z ↦ ∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm z (l.1 : ℂ)) z
        = ∑' l : {l : L.lattice // l ≠ 0}, weierstrassZetaTerm z (l.1 : ℂ) := by
    have hkey := logDeriv_tprod_eq_tsum
      (f := fun (l : {l : L.lattice // l ≠ 0}) (z : ℂ) ↦ weierstrassSigmaTerm z (l.1 : ℂ))
      hopen (show z ∈ (↑L.lattice : Set ℂ)ᶜ from hz) hfacne
      (fun l ↦ (differentiable_weierstrassSigmaTerm (l.1 : ℂ)).differentiableOn)
      ((L.summable_weierstrassZetaTerm z hz).congr fun l ↦ (hlogterm l).symm)
      (L.hasProdLocallyUniformly_weierstrassSigmaTerm.hasProdLocallyUniformlyOn
        |>.multipliableLocallyUniformlyOn)
      hprodne
    rw [hkey]
    exact tsum_congr hlogterm
  have hmul : logDeriv L.weierstrassSigma z
      = logDeriv (fun z : ℂ ↦ z) z
        + logDeriv (fun z ↦ ∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm z (l.1 : ℂ)) z :=
    logDeriv_mul (f := fun z : ℂ ↦ z)
      (g := fun z ↦ ∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm z (l.1 : ℂ)) z hz0 hprodne
      differentiableAt_id (L.differentiable_tprod_weierstrassSigmaTerm z)
  rw [hmul, hlogP, logDeriv_id', weierstrassZeta]

/-- Each ζ-summand is holomorphic away from the lattice. -/
private lemma differentiableOn_weierstrassZetaTerm (l : {l : L.lattice // l ≠ 0}) :
    DifferentiableOn ℂ (fun z ↦ weierstrassZetaTerm z (l.1 : ℂ)) (↑L.lattice)ᶜ := by
  intro r hr
  have hrne : r ≠ (l.1 : ℂ) := by rintro rfl; exact hr l.1.2
  have hw : (l.1 : ℂ) ≠ 0 := by simpa using l.2
  have hrw : r - (l.1 : ℂ) ≠ 0 := sub_ne_zero.mpr hrne
  unfold weierstrassZetaTerm
  fun_prop (disch := assumption)

/-- The partial sums of the ζ-series converge locally uniformly away from the lattice. -/
private lemma tendstoLocallyUniformlyOn_zetaSum :
    TendstoLocallyUniformlyOn
      (fun (t : Finset {l : L.lattice // l ≠ 0}) (z : ℂ) ↦
        ∑ l ∈ t, weierstrassZetaTerm z (l.1 : ℂ))
      (fun z ↦ ∑' l : {l : L.lattice // l ≠ 0}, weierstrassZetaTerm z (l.1 : ℂ))
      atTop (↑L.lattice)ᶜ :=
  hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
    L.hasSumLocallyUniformlyOn_weierstrassZetaTerm

/-- The ζ-sum is holomorphic away from the lattice. -/
private lemma differentiableAt_tsum_weierstrassZetaTerm {z : ℂ} (hz : z ∉ L.lattice) :
    DifferentiableAt ℂ
      (fun z ↦ ∑' l : {l : L.lattice // l ≠ 0}, weierstrassZetaTerm z (l.1 : ℂ)) z := by
  have hopen : IsOpen ((↑L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  exact (L.tendstoLocallyUniformlyOn_zetaSum.differentiableOn
    (Eventually.of_forall fun t ↦ DifferentiableOn.fun_sum fun i _ ↦
      L.differentiableOn_weierstrassZetaTerm i) hopen).differentiableAt (hopen.mem_nhds hz)

/-- The term-by-term derivative of the ζ-sum has sum `ζ'`. -/
private lemma hasSum_deriv_zetaTerm {z : ℂ} (hz : z ∉ L.lattice) :
    HasSum (fun l : {l : L.lattice // l ≠ 0} ↦ 1 / (l.1 : ℂ) ^ 2 - 1 / (z - l.1) ^ 2)
      (deriv (fun z ↦ ∑' l : {l : L.lattice // l ≠ 0}, weierstrassZetaTerm z (l.1 : ℂ)) z) := by
  have hopen : IsOpen ((↑L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  have hzc : z ∈ (↑L.lattice : Set ℂ)ᶜ := hz
  have hzne : ∀ l : {l : L.lattice // l ≠ 0}, z ≠ (l.1 : ℂ) := by
    intro l; rintro rfl; exact hz l.1.2
  have hwne : ∀ l : {l : L.lattice // l ≠ 0}, (l.1 : ℂ) ≠ 0 := fun l ↦ by simpa using l.2
  have hderivS : HasSum
      (fun l : {l : L.lattice // l ≠ 0} ↦ deriv (fun z ↦ weierstrassZetaTerm z (l.1 : ℂ)) z)
      (deriv (fun z ↦ ∑' l : {l : L.lattice // l ≠ 0}, weierstrassZetaTerm z (l.1 : ℂ)) z) := by
    rw [HasSum]
    convert! (L.tendstoLocallyUniformlyOn_zetaSum.deriv
      (Eventually.of_forall fun t ↦ DifferentiableOn.fun_sum fun i _ ↦
        L.differentiableOn_weierstrassZetaTerm i) hopen).tendsto_at hzc using 1
    ext1 t
    exact (deriv_fun_sum fun i _ ↦
      (L.differentiableOn_weierstrassZetaTerm i).differentiableAt (hopen.mem_nhds hzc)).symm
  exact hderivS.congr_fun fun l ↦ (deriv_weierstrassZetaTerm (hwne l) (hzne l)).symm

/-- The value of the term-by-term derivative sum: `-℘ + 1/z²`. -/
private lemma hasSum_val_zetaTerm {z : ℂ} (hz : z ∉ L.lattice) :
    HasSum (fun l : {l : L.lattice // l ≠ 0} ↦ 1 / (l.1 : ℂ) ^ 2 - 1 / (z - l.1) ^ 2)
      (-L.weierstrassP z + 1 / z ^ 2) := by
  have hz0 : z ≠ 0 := by rintro rfl; exact hz L.lattice.zero_mem
  have hPg : HasSum (fun l : L.lattice ↦ 1 / (l : ℂ) ^ 2 - 1 / (z - l) ^ 2) (-L.weierstrassP z) :=
    (L.hasSum_weierstrassP z).neg.congr_fun fun l ↦ by ring
  have hsingle : HasSum
      (fun l : L.lattice ↦ if l = 0 then
        (1 / ((0 : L.lattice) : ℂ) ^ 2 - 1 / (z - ((0 : L.lattice) : ℂ)) ^ 2) else (0 : ℂ))
      (1 / ((0 : L.lattice) : ℂ) ^ 2 - 1 / (z - ((0 : L.lattice) : ℂ)) ^ 2) := hasSum_ite_eq 0 _
  have hmod : HasSum
      (fun l : L.lattice ↦ if l = 0 then (0 : ℂ) else 1 / (l : ℂ) ^ 2 - 1 / (z - l) ^ 2)
      (-L.weierstrassP z
        - (1 / ((0 : L.lattice) : ℂ) ^ 2 - 1 / (z - ((0 : L.lattice) : ℂ)) ^ 2)) := by
    refine (hPg.sub hsingle).congr_fun fun l ↦ ?_
    by_cases h : l = 0 <;> simp [h]
  have hrange : ∀ x ∉ Set.range (Subtype.val : {l : L.lattice // l ≠ 0} → L.lattice),
      (fun l : L.lattice ↦ if l = 0 then (0 : ℂ) else 1 / (l : ℂ) ^ 2 - 1 / (z - l) ^ 2) x = 0 := by
    intro x hx
    have hx0 : x = 0 := by by_contra h; exact hx ⟨⟨x, h⟩, rfl⟩
    simp [hx0]
  have hval :
      (-L.weierstrassP z - (1 / ((0 : L.lattice) : ℂ) ^ 2 - 1 / (z - ((0 : L.lattice) : ℂ)) ^ 2))
      = -L.weierstrassP z + 1 / z ^ 2 := by simp
  have hfun : (fun l : {l : L.lattice // l ≠ 0} ↦
        if (l.1 : L.lattice) = 0 then (0 : ℂ) else 1 / (l.1 : ℂ) ^ 2 - 1 / (z - l.1) ^ 2)
      = fun l : {l : L.lattice // l ≠ 0} ↦ 1 / (l.1 : ℂ) ^ 2 - 1 / (z - l.1) ^ 2 := by
    ext l; rw [if_neg l.2]
  rw [← hval, ← hfun]
  exact (Subtype.val_injective.hasSum_iff hrange).mpr hmod

/-- The derivative of the ζ-sum, computed term by term. -/
private lemma deriv_tsum_weierstrassZetaTerm {z : ℂ} (hz : z ∉ L.lattice) :
    deriv (fun z ↦ ∑' l : {l : L.lattice // l ≠ 0}, weierstrassZetaTerm z (l.1 : ℂ)) z
      = -L.weierstrassP z + 1 / z ^ 2 :=
  (L.hasSum_deriv_zetaTerm hz).unique (L.hasSum_val_zetaTerm hz)

/-- `℘` is the negative derivative of `ζ` (paper Def. `defiwp`). -/
theorem deriv_weierstrassZeta (z : ℂ) (hz : z ∉ L.lattice) :
    deriv L.weierstrassZeta z = -L.weierstrassP z := by
  have hz0 : z ≠ 0 := by rintro rfl; exact hz L.lattice.zero_mem
  have h : HasDerivAt (fun z : ℂ ↦ 1 / z) (-1 / z ^ 2) z := by
    simp only [one_div]; exact (hasDerivAt_id z).inv hz0
  change deriv (fun z ↦ 1 / z + ∑' l : {l : L.lattice // l ≠ 0}, weierstrassZetaTerm z (l.1 : ℂ)) z
    = -L.weierstrassP z
  rw [deriv_fun_add h.differentiableAt (L.differentiableAt_tsum_weierstrassZetaTerm hz), h.deriv,
    L.deriv_tsum_weierstrassZetaTerm hz]
  ring

end PeriodPair

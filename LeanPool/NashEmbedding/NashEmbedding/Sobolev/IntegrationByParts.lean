/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Tactic
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Convolution
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Periodization
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.RiemannSum

/-!
# Fourier-transform Integration By Parts (Bridge Lemma 1)

For `φ ∈ C^∞_c(ℝⁿ; ℂ)`, the space-side j-th partial derivative becomes
frequency-side multiplication by `i · ξ_j` under `ftRn`:

  `ftRn n (∂_j φ) ξ = i · ξ_j · ftRn n φ ξ`.

Iterating and specialising to the Laplacian gives the polynomial-decay
estimate used in `cinfty_rapidDecay` (Bridge Lemma 1 for the assembly).

## Main contents

* `partialDeriv_hasCompactSupport`, `laplacian_hasCompactSupport`,
  `laplacian_iterate_hasCompactSupport` — compact-support companions
  to the `_contDiff` lemmas in `Periodization.lean`.
* `ftRn_partialDeriv_single` — the IBP identity, via Mathlib's
  `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`.
* `ftRn_laplacian`, `ftRn_laplacian_iterate` — the Laplacian and its
  iterates on the frequency side, mirroring `stdFourierCoeff_laplacian`
  and `stdFourierCoeff_laplacian_iterate`.
* `cinfty_rapidDecay` — **Bridge Lemma 1**: for `φ ∈ C^∞_c(ℝⁿ; ℂ)`,
  `FTRapidDecay n φ` holds. Closed by iterated Laplacian on `ftRn`,
  the trivial sup bound `ftRn_norm_le` on `Δ^N φ`, and
  `memSobolev_of_rapid_decay`.
-/

open scoped BigOperators ContDiff
open Complex Real MeasureTheory


noncomputable section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-! ## Compact support of partial derivatives and iterated Laplacian -/

/-- Companion to `partialDeriv_contDiff`: partial derivative preserves
compact support (for smooth functions). -/
lemma partialDeriv_hasCompactSupport {g : (Fin n → ℝ) → ℂ}
    (hg_supp : HasCompactSupport g) (j : Fin n) :
    HasCompactSupport (partialDeriv j g) := by
  change HasCompactSupport (fun θ => fderiv ℝ g θ (Pi.single j 1))
  exact HasCompactSupport.fderiv_apply (𝕜 := ℝ) hg_supp (Pi.single j 1)

/-- Companion to `laplacian_contDiff`: the Laplacian preserves compact
support (for smooth functions). -/
lemma laplacian_hasCompactSupport {g : (Fin n → ℝ) → ℂ}
    (hg_supp : HasCompactSupport g) :
    HasCompactSupport (laplacian g) := by
  -- Rewrite the pointwise sum as a function-level Finset.sum, then use
  -- Finset.sum_induction with `HasCompactSupport.add` and the zero case.
  have h_eq : laplacian g = ∑ j : Fin n, partialDeriv j (partialDeriv j g) := by
    unfold laplacian
    funext θ
    exact (Finset.sum_apply θ Finset.univ _).symm
  rw [h_eq]
  -- `hasCompactSupport_zero` isn't a mathlib identifier at the pinned
  -- commit; prove inline via `tsupport 0 = ∅`.
  have h0 : HasCompactSupport (0 : (Fin n → ℝ) → ℂ) := by
    unfold HasCompactSupport tsupport
    simp [Function.support_zero]
  refine Finset.sum_induction
    (fun j : Fin n => partialDeriv j (partialDeriv j g))
    HasCompactSupport (fun _ _ h1 h2 => h1.add h2) h0 ?_
  intro j _
  exact partialDeriv_hasCompactSupport (partialDeriv_hasCompactSupport hg_supp j) j

/-- Companion to `laplacian_iterate_contDiff`: iterated Laplacian
preserves compact support. -/
lemma laplacian_iterate_hasCompactSupport {g : (Fin n → ℝ) → ℂ}
    (hg_supp : HasCompactSupport g) (N : ℕ) :
    HasCompactSupport (laplacian^[N] g) := by
  induction N with
  | zero => simpa
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    exact laplacian_hasCompactSupport ih

/-! ## IBP: partial derivative ↔ frequency multiplication -/

/-- The Fourier transform of a partial derivative equals multiplication
by `i · ξ_j` of the original Fourier transform, for smooth compactly
supported `φ : ℝⁿ → ℂ`. Proved via Mathlib's
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` applied to
`f := (Fourier kernel) y ↦ exp(-i·⟨ξ,y⟩)` and `g := φ`. -/
lemma ftRn_partialDeriv_single
    {φ : (Fin n → ℝ) → ℂ}
    (hsmooth : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ)
    (j : Fin n) (ξ : Fin n → ℝ) :
    ftRn n (partialDeriv j φ) ξ = (Complex.I * (ξ j : ℂ)) * ftRn n φ ξ := by
  -- The Fourier-transform kernel.
  set E : (Fin n → ℝ) → ℂ := fun y => Complex.exp (-(Complex.I * ↑(∑ k, ξ k * y k)))
    with hE_def
  -- E is smooth. Follow the earlier `fourierExp_contDiff` pattern: prove the
  -- real-valued sum smooth via `fun_prop`, then compose with `ofRealCLM` and `exp`.
  have hE_smooth : ContDiff ℝ ∞ E := by
    have h1 : ContDiff ℝ ∞ (fun y : (Fin n → ℝ) => ∑ k, ξ k * y k) := by fun_prop
    have h2 : ContDiff ℝ ∞ (fun y : (Fin n → ℝ) => ((∑ k, ξ k * y k : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp h1
    exact Complex.contDiff_exp.comp ((contDiff_const.mul h2).neg)
  have hE_diff : Differentiable ℝ E := hE_smooth.differentiable (by simp)
  have hφ_diff : Differentiable ℝ φ := hsmooth.differentiable (by simp)
  -- Compact-support and integrability facts.
  have hpartial_sm : ContDiff ℝ ∞ (partialDeriv j φ) := partialDeriv_contDiff hsmooth j
  have hpartial_supp : HasCompactSupport (partialDeriv j φ) :=
    partialDeriv_hasCompactSupport hsupp j
  -- E · φ and E · (∂ⱼφ) are integrable: continuous with compact support = supp(φ) / supp(∂ⱼφ).
  have hEφ_int : Integrable (fun y => E y * φ y) :=
    (hE_smooth.continuous.mul hsmooth.continuous).integrable_of_hasCompactSupport
      hsupp.mul_left
  have hE_dphi_int : Integrable (fun y => E y * partialDeriv j φ y) :=
    (hE_smooth.continuous.mul hpartial_sm.continuous).integrable_of_hasCompactSupport
      hpartial_supp.mul_left
  -- The j-th directional derivative of E: `-i·ξⱼ · E`.
  have hE_deriv : ∀ y, fderiv ℝ E y (Pi.single j 1) = -(Complex.I * (ξ j : ℂ)) * E y := by
    intro y
    have hd : HasFDerivAt E (fderiv ℝ E y) y := (hE_diff y).hasFDerivAt
    have h1d : HasDerivAt (fun t : ℝ => E (Function.update y j t))
                          (fderiv ℝ E y (Pi.single j 1)) (y j) :=
      hasDerivAt_update_of_hasFDerivAt hd j
    have hexp : HasDerivAt (fun t : ℝ => E (Function.update y j t))
                (-(Complex.I * (ξ j : ℂ)) * E y) (y j) := by
      change HasDerivAt (fun t : ℝ => Complex.exp
              (-(Complex.I * ↑(∑ k, ξ k * (Function.update y j t) k))))
              (-(Complex.I * (ξ j : ℂ)) *
                Complex.exp (-(Complex.I * ↑(∑ k, ξ k * y k)))) (y j)
      simp +decide [Function.update_apply, Finset.sum_ite,
                    Finset.filter_eq', Finset.filter_ne']
      -- Mirrors the earlier `hasDerivAt_fourierExp_update` (Periodization.lean),
      -- with an extra outer `.neg` for our sign convention and the coefficient
      -- cast from ℝ to ℂ.
      convert HasDerivAt.comp (y j) (Complex.hasDerivAt_exp _)
        (HasDerivAt.neg <| HasDerivAt.const_mul Complex.I <| HasDerivAt.add
          (HasDerivAt.const_mul ((ξ j : ℝ) : ℂ) <|
            hasDerivAt_id _ |> HasDerivAt.ofReal_comp)
          <| hasDerivAt_const _ _)
        using 1
      all_goals (first | rfl | (norm_num; ring))
    exact h1d.unique hexp
  -- (fderiv E · e_j) · φ integrable, via the fderiv computation.
  have hdE_phi_int : Integrable (fun y => fderiv ℝ E y (Pi.single j 1) * φ y) := by
    have h : (fun y => fderiv ℝ E y (Pi.single j 1) * φ y)
           = (fun y => -(Complex.I * (ξ j : ℂ)) * (E y * φ y)) := by
      funext y; rw [hE_deriv y]; ring
    rw [h]
    exact hEφ_int.const_mul _
  -- Mathlib IBP: ∫ E · (∂φ)(e_j) = - ∫ (∂E)(e_j) · φ.
  have hIBP : ∫ y, E y * fderiv ℝ φ y (Pi.single j 1)
              = - ∫ y, fderiv ℝ E y (Pi.single j 1) * φ y :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      hdE_phi_int hE_dphi_int hEφ_int (fun x _ => hE_diff.differentiableAt) (fun x _ =>
          hφ_diff.differentiableAt)
  -- LHS is ftRn (partialDeriv j φ) ξ up to mul_comm.
  have hLHS : (∫ y, E y * fderiv ℝ φ y (Pi.single j 1))
              = ftRn n (partialDeriv j φ) ξ := by
    unfold ftRn partialDeriv
    congr 1; funext y
    show E y * fderiv ℝ φ y (Pi.single j 1)
       = fderiv ℝ φ y (Pi.single j 1) * Complex.exp (-(Complex.I * ↑(∑ k, ξ k * y k)))
    ring
  -- RHS reduces to (I ξⱼ) · ftRn n φ ξ.
  have hRHS : (- ∫ y, fderiv ℝ E y (Pi.single j 1) * φ y)
              = (Complex.I * (ξ j : ℂ)) * ftRn n φ ξ := by
    have h : (fun y => fderiv ℝ E y (Pi.single j 1) * φ y)
           = (fun y => -(Complex.I * (ξ j : ℂ)) * (E y * φ y)) := by
      funext y; rw [hE_deriv y]; ring
    rw [h, integral_const_mul]
    unfold ftRn
    have heq : (∫ y, E y * φ y)
             = ∫ y, φ y * Complex.exp (-(Complex.I * ↑(∑ k, ξ k * y k))) := by
      congr 1; funext y
      show E y * φ y = φ y * Complex.exp (-(Complex.I * ↑(∑ k, ξ k * y k)))
      ring
    rw [heq]; ring
  rw [← hLHS, hIBP, hRHS]

/-! ## `ftRn` linearity over finite sums (helper) -/

/-- Linearity of `ftRn` over finite sums of continuous compactly supported
functions. Proved by induction on the finset (using ftRn's compatibility
with pointwise addition on integrable functions) — the `integral_finset_sum`
route hit unbounded heartbeat timeouts on the nested `∫ ∑` pattern. -/
lemma ftRn_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → (Fin n → ℝ) → ℂ)
    (hf_ct : ∀ i ∈ s, Continuous (f i))
    (hf_supp : ∀ i ∈ s, HasCompactSupport (f i))
    (ξ : Fin n → ℝ) :
    ftRn n (fun y => ∑ i ∈ s, f i y) ξ = ∑ i ∈ s, ftRn n (f i) ξ := by
  classical
  set E : (Fin n → ℝ) → ℂ :=
    fun y => Complex.exp (-(Complex.I * ↑(∑ k, ξ k * y k))) with hE_def
  have hE_ct : Continuous E := by
    change Continuous (fun y : (Fin n → ℝ) => Complex.exp _)
    refine Complex.continuous_exp.comp ?_
    refine ((continuous_const.mul ?_).neg)
    refine Complex.continuous_ofReal.comp ?_
    exact by fun_prop
  revert hf_ct hf_supp
  induction s using Finset.induction_on with
  | empty =>
    intro _ _
    change (∫ _, (0 : ℂ) * _) = 0
    simp
  | @insert i₀ s₀ hi_notin ih =>
    intro hf_ct hf_supp
    have hi_in : i₀ ∈ insert i₀ s₀ := Finset.mem_insert_self i₀ s₀
    have hs_sub : ∀ j ∈ s₀, j ∈ insert i₀ s₀ := fun j hj => Finset.mem_insert_of_mem hj
    have hf_ct_s : ∀ j ∈ s₀, Continuous (f j) :=
      fun j hj => hf_ct j (hs_sub j hj)
    have hf_supp_s : ∀ j ∈ s₀, HasCompactSupport (f j) :=
      fun j hj => hf_supp j (hs_sub j hj)
    have ih' := ih hf_ct_s hf_supp_s
    change (∫ y, (∑ j ∈ insert i₀ s₀, f j y) * E y)
       = ∑ j ∈ insert i₀ s₀, ftRn n (f j) ξ
    simp only [Finset.sum_insert hi_notin, add_mul]
    -- Compact support is on the LEFT factor (`f i₀`, then `∑ j ∈ s₀, f j`),
    -- with E on the RIGHT: use `.mul_right`, NOT `.mul_left`. Earlier attempts
    -- with `.mul_left` triggered isDefEq/whnf timeouts because Lean was trying
    -- to unify `f i₀` with `E` — silent type-directed misfire.
    have hf_i_int : Integrable (fun y => f i₀ y * E y) :=
      ((hf_ct i₀ hi_in).mul hE_ct).integrable_of_hasCompactSupport
        (hf_supp i₀ hi_in).mul_right
    have hf_s_ct : Continuous (fun y : (Fin n → ℝ) => ∑ j ∈ s₀, f j y) :=
      continuous_finsetSum s₀ (fun j hj => hf_ct_s j hj)
    have hf_s_supp : HasCompactSupport (fun y : (Fin n → ℝ) => ∑ j ∈ s₀, f j y) := by
      have h0 : HasCompactSupport (0 : (Fin n → ℝ) → ℂ) := by
        unfold HasCompactSupport tsupport; simp [Function.support_zero]
      -- Function-valued sum vs pointwise sum: bridge via funext + Finset.sum_apply.
      have h_eq : (fun y : (Fin n → ℝ) => ∑ j ∈ s₀, f j y)
                = ∑ j ∈ s₀, f j := by
        funext y; exact (Finset.sum_apply y s₀ _).symm
      rw [h_eq]
      exact Finset.sum_induction (fun j : ι => f j) HasCompactSupport
        (fun _ _ h1 h2 => h1.add h2) h0 hf_supp_s
    have hf_s_int : Integrable (fun y => (∑ j ∈ s₀, f j y) * E y) :=
      (hf_s_ct.mul hE_ct).integrable_of_hasCompactSupport hf_s_supp.mul_right
    rw [MeasureTheory.integral_add hf_i_int hf_s_int]
    -- LHS first term = ftRn n (f i₀) ξ by defeq; second term = ih'.
    -- `congr 1` handles both when both sides are wrapped identically.
    exact congrArg (· + _) rfl |>.trans (congrArg (_ + ·) ih')

/-! ## Laplacian on the frequency side -/

/-- The Fourier transform of the Laplacian:
`ftRn (Δφ) ξ = -|ξ|² · ftRn φ ξ`. Mirrors
`stdFourierCoeff_laplacian` in `Periodization.lean`. -/
lemma ftRn_laplacian
    {φ : (Fin n → ℝ) → ℂ}
    (hsmooth : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ)
    (ξ : Fin n → ℝ) :
    ftRn n (laplacian φ) ξ = -(∑ j, (ξ j : ℂ) ^ 2) * ftRn n φ ξ := by
  -- Rewrite `laplacian φ` as `fun y => ∑ j, ...`, split integral over sum,
  -- apply `ftRn_partialDeriv_single` twice per coord, then simplify with I² = -1.
  have h_lap : laplacian φ = fun y => ∑ j : Fin n,
      partialDeriv j (partialDeriv j φ) y := by
    unfold laplacian
    rfl
  rw [h_lap, ftRn_finset_sum Finset.univ _
    (fun j _ => (partialDeriv_contDiff (partialDeriv_contDiff hsmooth j) j).continuous)
    (fun j _ => partialDeriv_hasCompactSupport (partialDeriv_hasCompactSupport hsupp j) j) ξ]
  have h_j : ∀ j : Fin n, ftRn n (partialDeriv j (partialDeriv j φ)) ξ
                        = -((ξ j : ℂ) ^ 2) * ftRn n φ ξ := by
    intro j
    rw [ftRn_partialDeriv_single
          (partialDeriv_contDiff hsmooth j)
          (partialDeriv_hasCompactSupport hsupp j) j ξ,
        ftRn_partialDeriv_single hsmooth hsupp j ξ]
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    ring_nf
    linear_combination ((ξ j : ℂ) ^ 2 * ftRn n φ ξ) * hI2
  simp_rw [h_j]
  rw [← Finset.sum_mul, ← Finset.sum_neg_distrib]

/-- Iterated Laplacian on the frequency side. Mirrors
`stdFourierCoeff_laplacian_iterate`. -/
lemma ftRn_laplacian_iterate
    {φ : (Fin n → ℝ) → ℂ}
    (hsmooth : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ)
    (N : ℕ) (ξ : Fin n → ℝ) :
    ftRn n (laplacian^[N] φ) ξ = (-(∑ j, (ξ j : ℂ) ^ 2)) ^ N * ftRn n φ ξ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply',
        ftRn_laplacian (laplacian_iterate_contDiff hsmooth N)
          (laplacian_iterate_hasCompactSupport hsupp N) ξ,
        ih, pow_succ]
    ring

/-! ## Bridge Lemma 1 -/

/-- **Bridge Lemma 1.** For `φ ∈ C^∞_c(ℝⁿ; ℂ)` and `0 < n`,
`FTRapidDecay n φ` holds. Structure mirrors `stdFourierCoeff_rapid_decay`
in `Periodization.lean`: sup bounds on the integrand (via
`ftRn_norm_le`), iterated Laplacian on the frequency side, weight
arithmetic, `memSobolev_of_rapid_decay`. -/
theorem cinfty_rapidDecay (hn : 0 < n)
    {φ : (Fin n → ℝ) → ℂ}
    (hsmooth : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    FTRapidDecay n φ := by
  intro s
  -- FTRapidDecay unfolds to `∀ s, Summable (m ↦ weight n s m · ‖ftRn n φ ↑m‖²)`,
  -- which is `MemSobolev n s (fun m => ftRn n φ ↑m)`.
  apply memSobolev_of_rapid_decay hn (a := fun m => ftRn n φ (fun j => (m j : ℝ)))
  intro N
  -- L¹ bounds on φ and Δ^N φ (both smooth compactly supported ⇒ integrable ⇒ ftRn_norm_le).
  have hφ_int : Integrable φ :=
    hsmooth.continuous.integrable_of_hasCompactSupport hsupp
  have hΔN_sm : ContDiff ℝ ∞ (laplacian^[N] φ) := laplacian_iterate_contDiff hsmooth N
  have hΔN_supp : HasCompactSupport (laplacian^[N] φ) :=
    laplacian_iterate_hasCompactSupport hsupp N
  have hΔN_int : Integrable (laplacian^[N] φ) :=
    hΔN_sm.continuous.integrable_of_hasCompactSupport hΔN_supp
  set L0 : ℝ := ∫ y, ‖φ y‖ with hL0_def
  set LN : ℝ := ∫ y, ‖(laplacian^[N] φ) y‖ with hLN_def
  have hL0 : 0 ≤ L0 := integral_nonneg (fun _ => norm_nonneg _)
  have hLN : 0 ≤ LN := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨2 ^ N * (L0 + LN) + 1, by positivity, fun m => ?_⟩
  set S : ℝ := ∑ j, ((m j : ℝ)) ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h0 : ‖ftRn n φ (fun j => (m j : ℝ))‖ ≤ L0 :=
    ftRn_norm_le φ hφ_int (fun j => (m j : ℝ))
  have hN : S ^ N * ‖ftRn n φ (fun j => (m j : ℝ))‖ ≤ LN := by
    have h_it := ftRn_laplacian_iterate hsmooth hsupp N (fun j => (m j : ℝ))
    have h_ln := ftRn_norm_le _ hΔN_int (fun j => (m j : ℝ))
    rw [h_it, norm_mul, norm_pow, norm_neg] at h_ln
    have hcast : ‖∑ j, ((m j : ℝ) : ℂ) ^ 2‖ = S := by
      have h_eq : (∑ j, ((m j : ℝ) : ℂ) ^ 2) = ((S : ℝ) : ℂ) := by
        rw [hS]; push_cast; rfl
      rw [h_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0]
    rwa [hcast] at h_ln
  -- Weight bookkeeping (verbatim from stdFourierCoeff_rapid_decay).
  have hw : weight n (N / 2 : ℝ) m ≤ 2 ^ N * (1 + S ^ N) := by
    calc weight n (N / 2 : ℝ) m ≤ weight n (N : ℝ) m :=
          weight_mono (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]) m
      _ = (1 + S) ^ N := by unfold weight; rw [Real.rpow_natCast]
      _ ≤ (2 * max 1 S) ^ N :=
          pow_le_pow_left₀ (by positivity)
            (by linarith [le_max_left 1 S, le_max_right 1 S]) N
      _ = 2 ^ N * (max 1 S) ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + S ^ N) := by
          gcongr
          rcases le_total 1 S with h | h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h, one_pow]; linarith [pow_nonneg hS0 N]
  have hkey : ‖ftRn n φ (fun j => (m j : ℝ))‖ * weight n (N / 2 : ℝ) m
              ≤ 2 ^ N * (L0 + LN) := by
    calc ‖ftRn n φ (fun j => (m j : ℝ))‖ * weight n (N / 2 : ℝ) m
        ≤ ‖ftRn n φ (fun j => (m j : ℝ))‖ * (2 ^ N * (1 + S ^ N)) := by gcongr
      _ = 2 ^ N * (‖ftRn n φ (fun j => (m j : ℝ))‖
                    + S ^ N * ‖ftRn n φ (fun j => (m j : ℝ))‖) := by ring
      _ ≤ 2 ^ N * (L0 + LN) := by gcongr
  have hwinv : weight n (-(N / 2 : ℝ)) m = (weight n (N / 2 : ℝ) m)⁻¹ := by
    have h := weight_mul (-(N / 2 : ℝ)) (N / 2 : ℝ) m
    rw [neg_add_cancel, weight_zero] at h
    exact eq_inv_of_mul_eq_one_left h
  rw [hwinv, ← div_eq_mul_inv, le_div_iff₀ (weight_pos _ _)]
  linarith [hkey]

end NashEmbedding.Sobolev

end

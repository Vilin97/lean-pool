/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Parametric Differentiation for Homotopy Integrals

Lemmas for differentiating contour integrals under a C² homotopy
parameter, including the Schwarz theorem for mixed partial
derivatives and the key vanishing-derivative result used in
homotopy invariance of contour integrals.

## Main Results

* `intervalIntegral_continuous_on_param` — continuity of a
    parametric interval integral
* `schwarz_partialDeriv_comm` — mixed partials of a C² function
    commute
* `hasDerivAt_homotopy_integral_zero` — derivative of the
    homotopy integral vanishes when boundary s-derivatives are
    zero
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

private noncomputable instance : ContinuousSMul ℝ ℂ :=
  ⟨(show (fun p : ℝ × ℂ => p.1 • p.2) = (fun p => (p.1 : ℂ) * p.2) from
    funext fun p => by simp [Complex.real_smul]) ▸
    (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd⟩

/-- Continuity of a parametric interval integral. -/
theorem intervalIntegral_continuous_on_param
    (f : ℝ → ℝ → ℂ) (a b : ℝ) (S : Set ℝ) (hab : a ≤ b)
    (hf_cont : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (_hf_int : ∀ s ∈ S,
      IntervalIntegrable (f · s) volume a b) :
    ContinuousOn (fun s => ∫ t in a..b, f t s) S := by
  intro s₀ _hs₀
  apply ContinuousAt.continuousWithinAt
  have hmeas : ∀ s,
      AEStronglyMeasurable (f · s)
        (volume.restrict (Set.uIoc a b)) := by
    intro s
    apply Continuous.aestronglyMeasurable
    exact hf_cont.comp
      (continuous_id.prodMk continuous_const)
  have hcont_pt : ∀ᵐ t ∂volume,
      t ∈ Set.uIoc a b →
        ContinuousAt (f t) s₀ := by
    filter_upwards with t _
    exact (hf_cont.comp
      (continuous_const.prodMk continuous_id)).continuousAt
  have hcompact :
      IsCompact (Icc a b ×ˢ Icc (s₀ - 1) (s₀ + 1)) :=
    isCompact_Icc.prod isCompact_Icc
  have hbound : ∃ M : ℝ,
      ∀ p ∈ Icc a b ×ˢ Icc (s₀ - 1) (s₀ + 1),
        ‖(fun p => f p.1 p.2) p‖ ≤ M :=
    hcompact.exists_bound_of_continuousOn
      hf_cont.continuousOn
  obtain ⟨M, hM⟩ := hbound
  apply intervalIntegral.continuousAt_of_dominated_interval
  · filter_upwards with s; exact hmeas s
  · have h_nhd : Ioo (s₀ - 1) (s₀ + 1) ∈ 𝓝 s₀ := by
      apply Ioo_mem_nhds <;> linarith
    filter_upwards [h_nhd] with s hs
    filter_upwards with t
    intro ht
    by_cases htab : t ∈ Icc a b
    · exact hM (t, s)
        ⟨htab, le_of_lt hs.1, le_of_lt hs.2⟩
    · rw [Set.uIoc_of_le hab] at ht
      exact absurd (Ioc_subset_Icc_self ht) htab
  · exact intervalIntegrable_const
  · exact hcont_pt

lemma contDiff_partialDeriv_snd_of_contDiff_two
    (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ =>
      deriv (fun s => H (p.1, s)) p.2) := by
  have h1 : ContDiff ℝ 1
      (fun p : ℝ × ℝ => fderiv ℝ H p) :=
    hH.fderiv_right le_rfl
  have h2 : ContDiff ℝ 1
      (fun p : ℝ × ℝ => (fderiv ℝ H p) (0, 1)) :=
    h1.clm_apply contDiff_const
  convert h2 using 1
  ext p
  have hH_diff : Differentiable ℝ H :=
    hH.differentiable
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have h_emb_diff :
      DifferentiableAt ℝ (fun s : ℝ => (p.1, s)) p.2 :=
    (differentiableAt_const p.1).prodMk differentiableAt_id
  change deriv (fun s => H (p.1, s)) p.2 = fderiv ℝ H p (0, 1)
  calc deriv (fun s => H (p.1, s)) p.2
      = (fderiv ℝ H (p.1, p.2)) (deriv (fun s => (p.1, s)) p.2) :=
        fderiv_comp_deriv p.2 (hH_diff (p.1, p.2)) h_emb_diff
    _ = (fderiv ℝ H p) (0, 1) := by
        congr 1
        exact ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)).deriv

lemma contDiff_partialDeriv_fst_of_contDiff_two
    (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ =>
      deriv (fun t => H (t, p.2)) p.1) := by
  have h1 : ContDiff ℝ 1
      (fun p : ℝ × ℝ => fderiv ℝ H p) :=
    hH.fderiv_right le_rfl
  have h2 : ContDiff ℝ 1
      (fun p : ℝ × ℝ => (fderiv ℝ H p) (1, 0)) :=
    h1.clm_apply contDiff_const
  convert h2 using 1
  ext p
  have hH_diff : Differentiable ℝ H :=
    hH.differentiable
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have h_emb_diff :
      DifferentiableAt ℝ (fun t : ℝ => (t, p.2)) p.1 :=
    differentiableAt_id.prodMk (differentiableAt_const p.2)
  change deriv (fun t => H (t, p.2)) p.1 = fderiv ℝ H p (1, 0)
  calc deriv (fun t => H (t, p.2)) p.1
      = (fderiv ℝ H (p.1, p.2)) (deriv (fun t => (t, p.2)) p.1) :=
        fderiv_comp_deriv p.1 (hH_diff (p.1, p.2)) h_emb_diff
    _ = (fderiv ℝ H p) (1, 0) := by
        congr 1
        exact ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)).deriv

/-- Schwarz theorem: mixed partials of a C² function commute. -/
lemma schwarz_partialDeriv_comm
    (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (t s : ℝ) :
    deriv (fun s' =>
      deriv (fun t' => H (t', s')) t) s =
    deriv (fun t' =>
      deriv (fun s' => H (t', s')) s) t := by
  have h_symm : IsSymmSndFDerivAt ℝ H (t, s) :=
    (hH.contDiffAt).isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField, le_refl])
  have hH_diff : Differentiable ℝ H :=
    hH.differentiable
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hH1 : ContDiff ℝ 1
      (fun p : ℝ × ℝ => fderiv ℝ H p) :=
    hH.fderiv_right le_rfl
  have hfH : Differentiable ℝ (fun p => fderiv ℝ H p) :=
    hH1.differentiable one_ne_zero
  have h_inner_t : ∀ s',
      deriv (fun t' => H (t', s')) t =
        fderiv ℝ H (t, s') (1, 0) := fun s' => by
    have h_emb :
        DifferentiableAt ℝ (fun t' : ℝ => (t', s')) t :=
      differentiableAt_id.prodMk
        (differentiableAt_const s')
    have h_has_deriv :
        HasDerivAt (fun t' => (t', s')) (1, 0) t := by
      have h1 : HasDerivAt (fun t' => t') 1 t :=
        hasDerivAt_id t
      have h2 : HasDerivAt (fun _ : ℝ => s') 0 t :=
        hasDerivAt_const t s'
      exact h1.prodMk h2
    calc deriv (fun t' => H (t', s')) t
        = (fderiv ℝ H (t, s'))
            (deriv (fun t' => (t', s')) t) :=
          fderiv_comp_deriv t (hH_diff (t, s')) h_emb
      _ = (fderiv ℝ H (t, s')) (1, 0) := by
          rw [h_has_deriv.deriv]
  have h_inner_s : ∀ t',
      deriv (fun s' => H (t', s')) s =
        fderiv ℝ H (t', s) (0, 1) := fun t' => by
    have h_emb :
        DifferentiableAt ℝ (fun s' : ℝ => (t', s')) s :=
      (differentiableAt_const t').prodMk differentiableAt_id
    have h_has_deriv :
        HasDerivAt (fun s' => (t', s')) (0, 1) s := by
      have h1 : HasDerivAt (fun _ : ℝ => t') 0 s :=
        hasDerivAt_const s t'
      have h2 : HasDerivAt (fun s' => s') 1 s :=
        hasDerivAt_id s
      exact h1.prodMk h2
    calc deriv (fun s' => H (t', s')) s
        = (fderiv ℝ H (t', s))
            (deriv (fun s' => (t', s')) s) :=
          fderiv_comp_deriv s (hH_diff (t', s)) h_emb
      _ = (fderiv ℝ H (t', s)) (0, 1) := by
          rw [h_has_deriv.deriv]
  simp_rw [h_inner_t, h_inner_s]
  have h_emb_s : DifferentiableAt ℝ (fun s' : ℝ => (t, s')) s :=
    (differentiableAt_const t).prodMk differentiableAt_id
  have h_deriv_emb_s : deriv (fun s' => (t, s')) s = (0, 1) :=
    ((hasDerivAt_const s t).prodMk (hasDerivAt_id s)).deriv
  have h_emb_t : DifferentiableAt ℝ (fun t' : ℝ => (t', s)) t :=
    differentiableAt_id.prodMk (differentiableAt_const s)
  have h_deriv_emb_t : deriv (fun t' => (t', s)) t = (1, 0) :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t s)).deriv
  have hLHS :
      deriv (fun s' =>
        (fderiv ℝ H (t, s')) (1, 0)) s =
      (fderiv ℝ (fun p => fderiv ℝ H p) (t, s))
        (0, 1) (1, 0) := by
    have h_clm_diff :
        DifferentiableAt ℝ
          (fun s' => fderiv ℝ H (t, s')) s :=
      (hfH (t, s)).comp s h_emb_s
    have h_const_diff :
        DifferentiableAt ℝ
          (fun _ : ℝ => (1, 0) : ℝ → ℝ × ℝ) s :=
      differentiableAt_const (1, 0)
    rw [deriv_clm_apply h_clm_diff h_const_diff]
    simp only [deriv_const, map_zero, add_zero]
    have h_comp :
        (fun s' => fderiv ℝ H (t, s')) =
          (fun p => fderiv ℝ H p) ∘
            (fun s' => (t, s')) := rfl
    rw [h_comp,
      fderiv_comp_deriv s (hfH (t, s)) h_emb_s,
      h_deriv_emb_s]
  have hRHS :
      deriv (fun t' =>
        (fderiv ℝ H (t', s)) (0, 1)) t =
      (fderiv ℝ (fun p => fderiv ℝ H p) (t, s))
        (1, 0) (0, 1) := by
    have h_clm_diff :
        DifferentiableAt ℝ
          (fun t' => fderiv ℝ H (t', s)) t :=
      (hfH (t, s)).comp t h_emb_t
    have h_const_diff :
        DifferentiableAt ℝ
          (fun _ : ℝ => (0, 1) : ℝ → ℝ × ℝ) t :=
      differentiableAt_const (0, 1)
    rw [deriv_clm_apply h_clm_diff h_const_diff]
    simp only [deriv_const, map_zero, add_zero]
    have h_comp :
        (fun t' => fderiv ℝ H (t', s)) =
          (fun p => fderiv ℝ H p) ∘
            (fun t' => (t', s)) := rfl
    rw [h_comp,
      fderiv_comp_deriv t (hfH (t, s)) h_emb_t,
      h_deriv_emb_t]
  rw [hLHS, hRHS]
  exact h_symm.eq (0, 1) (1, 0)

private lemma differentiableAt_mul_of_contDiff
    (g : ℝ → ℂ) (h : ℝ → ℂ) (t : ℝ)
    (hg : DifferentiableAt ℝ g t)
    (hh : ContDiff ℝ 1 h) :
    DifferentiableAt ℝ (fun t' => g t' * h t') t :=
  hg.mul (hh.differentiable one_ne_zero t)

private lemma differentiableAt_comp_of_holomorphic
    (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (t s : ℝ)
    (hH : ContDiff ℝ 2 H)
    (hf : DifferentiableAt ℂ f (H (t, s))) :
    DifferentiableAt ℝ
      (fun t' => f (H (t', s))) t := by
  have hH_diff :
      DifferentiableAt ℝ (fun t' => H (t', s)) t := by
    have h := hH.differentiable
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    exact DifferentiableAt.comp t (h (t, s))
      (differentiableAt_id.prodMk
        (differentiableAt_const s))
  exact (hf.restrictScalars ℝ).comp t hH_diff

/-! ### Shared differentiability helpers for homotopy decomposition -/

/-- `s' ↦ H(t, s')` is differentiable when H is C². -/
private lemma homotopy_H_differentiableAt_s
    (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ) :
    DifferentiableAt ℝ (fun s' => H (t, s')) s :=
  (hH.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0) (t, s)).comp s
    ((differentiableAt_const t).prodMk differentiableAt_id)

/-- `t' ↦ H(t', s)` is differentiable when H is C². -/
private lemma homotopy_H_differentiableAt_t
    (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ) :
    DifferentiableAt ℝ (fun t' => H (t', s)) t :=
  (hH.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0) (t, s)).comp t
    (differentiableAt_id.prodMk (differentiableAt_const s))

/-- `s' ↦ f(H(t, s'))` is differentiable. -/
private lemma homotopy_fH_differentiableAt_s
    (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ)
    (hf : DifferentiableAt ℂ f (H (t, s))) :
    DifferentiableAt ℝ (fun s' => f (H (t, s'))) s :=
  (hf.restrictScalars ℝ).comp s (homotopy_H_differentiableAt_s H hH t s)

/-- `t' ↦ f(H(t', s))` is differentiable. -/
private lemma homotopy_fH_differentiableAt_t
    (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ)
    (hf : DifferentiableAt ℂ f (H (t, s))) :
    DifferentiableAt ℝ (fun t' => f (H (t', s))) t :=
  (hf.restrictScalars ℝ).comp t (homotopy_H_differentiableAt_t H hH t s)

/-- `s' ↦ ∂H/∂t(t, s')` is differentiable. -/
private lemma homotopy_partialT_differentiableAt_s
    (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ) :
    DifferentiableAt ℝ (fun s' => deriv (fun t' => H (t', s')) t) s := by
  have : (fun s' => deriv (fun t' => H (t', s')) t) =
      (fun p : ℝ × ℝ => deriv (fun t' => H (t', p.2)) p.1) ∘ (fun s' => (t, s')) := rfl
  rw [this]
  exact ((contDiff_partialDeriv_fst_of_contDiff_two H hH).differentiable one_ne_zero (t, s)).comp s
    ((differentiableAt_const t).prodMk differentiableAt_id)

/-- `t' ↦ ∂H/∂s(t', s)` is differentiable. -/
private lemma homotopy_partialS_differentiableAt_t
    (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ) :
    DifferentiableAt ℝ (fun t' => deriv (fun s' => H (t', s')) s) t := by
  have : (fun t' => deriv (fun s' => H (t', s')) s) =
      (fun p : ℝ × ℝ => deriv (fun s' => H (p.1, s')) p.2) ∘ (fun t' => (t', s)) := rfl
  rw [this]
  exact ((contDiff_partialDeriv_snd_of_contDiff_two H hH).differentiable one_ne_zero (t, s)).comp t
    (differentiableAt_id.prodMk (differentiableAt_const s))

/-- Chain rule for `s' ↦ f(H(t, s'))`. -/
private lemma homotopy_chain_rule_s
    (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ)
    (hf : Differentiable ℂ f) :
    deriv (fun s' => f (H (t, s'))) s =
      deriv f (H (t, s)) * deriv (fun s' => H (t, s')) s := by
  have : (fun s' => f (H (t, s'))) = f ∘ (fun s' => H (t, s')) := rfl
  rw [this]
  have := deriv.scomp s (hf (H (t, s))) (homotopy_H_differentiableAt_s H hH t s)
  simp only [smul_eq_mul, mul_comm] at this; exact this

/-- Chain rule for `t' ↦ f(H(t', s))`. -/
private lemma homotopy_chain_rule_t
    (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ)
    (hf : Differentiable ℂ f) :
    deriv (fun t' => f (H (t', s))) t =
      deriv f (H (t, s)) * deriv (fun t' => H (t', s)) t := by
  have : (fun t' => f (H (t', s))) = f ∘ (fun t' => H (t', s)) := rfl
  rw [this]
  have := deriv.scomp t (hf (H (t, s))) (homotopy_H_differentiableAt_t H hH t s)
  simp only [smul_eq_mul, mul_comm] at this; exact this

/-- The s-derivative of `f(H(t,s')) * ∂H/∂t(t,s')` equals the t-derivative
of `f(H(t',s)) * ∂H/∂s(t',s)`, via the product rule, chain rule, and
Schwarz symmetry of mixed partials. -/
private lemma homotopy_schwarz_product_rule
    (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ)
    (hf_at : DifferentiableAt ℂ f (H (t, s)))
    (hf : Differentiable ℂ f) :
    deriv (fun s' => f (H (t, s')) * deriv (fun t' => H (t', s')) t) s =
    deriv (fun t' => f (H (t', s)) * deriv (fun s'' => H (t', s'')) s) t := by
  have hLHS :
      deriv (fun s' => f (H (t, s')) * deriv (fun t' => H (t', s')) t) s =
        deriv (fun s' => f (H (t, s'))) s * deriv (fun t' => H (t', s)) t +
        f (H (t, s)) * deriv (fun s' => deriv (fun t' => H (t', s')) t) s := by
    change deriv ((fun s' => f (H (t, s'))) *
      (fun s' => deriv (fun t' => H (t', s')) t)) s = _
    exact deriv_mul (homotopy_fH_differentiableAt_s f H hH t s hf_at)
      (homotopy_partialT_differentiableAt_s H hH t s)
  have hRHS :
      deriv (fun t' => f (H (t', s)) * deriv (fun s'' => H (t', s'')) s) t =
        deriv (fun t' => f (H (t', s))) t * deriv (fun s' => H (t, s')) s +
        f (H (t, s)) * deriv (fun t' => deriv (fun s' => H (t', s')) s) t := by
    change deriv ((fun t' => f (H (t', s))) *
      (fun t' => deriv (fun s' => H (t', s')) s)) t = _
    exact deriv_mul (homotopy_fH_differentiableAt_t f H hH t s hf_at)
      (homotopy_partialS_differentiableAt_t H hH t s)
  rw [hLHS, hRHS, homotopy_chain_rule_s f H hH t s hf,
    homotopy_chain_rule_t f H hH t s hf,
    schwarz_partialDeriv_comm H hH t s]
  ring

/-! ### Helpers for `hasDerivAt_homotopy_param` -/

/-- Continuity of the mixed partial `(t, s') ↦ ∂/∂s' (∂H/∂t(t, s'))`. -/
private lemma homotopy_mixed_partial_continuous
    (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) :
    Continuous (fun p : ℝ × ℝ =>
      deriv (fun s' => deriv (fun t' => H (t', s')) p.1) p.2) := by
  have h_partialT := contDiff_partialDeriv_fst_of_contDiff_two H hH
  have h_eq : (fun p : ℝ × ℝ =>
      deriv (fun s' => deriv (fun t' => H (t', s')) p.1) p.2) =
    (fun p : ℝ × ℝ =>
      fderiv ℝ (fun p' : ℝ × ℝ => deriv (fun t' => H (t', p'.2)) p'.1) p (0, 1)) := by
    ext p
    have hg_diff : Differentiable ℝ (fun p' : ℝ × ℝ =>
        deriv (fun t' => H (t', p'.2)) p'.1) :=
      h_partialT.differentiable one_ne_zero
    have h_emb_diff : DifferentiableAt ℝ (fun s' : ℝ => (p.1, s')) p.2 :=
      (differentiableAt_const p.1).prodMk differentiableAt_id
    have h_deriv_emb : deriv (fun s' => (p.1, s')) p.2 = (0, 1) :=
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)).deriv
    calc deriv (fun s' => deriv (fun t' => H (t', s')) p.1) p.2
        = deriv ((fun p' : ℝ × ℝ =>
            deriv (fun t' => H (t', p'.2)) p'.1) ∘ (fun s' => (p.1, s'))) p.2 := rfl
      _ = (fderiv ℝ (fun p' => deriv (fun t' => H (t', p'.2)) p'.1) p)
            (deriv (fun s' => (p.1, s')) p.2) := by
          apply fderiv_comp_deriv p.2 (hg_diff p) h_emb_diff
      _ = (fderiv ℝ (fun p' => deriv (fun t' => H (t', p'.2)) p'.1) p) (0, 1) := by
          rw [h_deriv_emb]
  rw [h_eq]
  exact (h_partialT.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- The s-derivative of `f(H(t,s')) * ∂H/∂t(t,s')` has a closed-form expression. -/
private lemma homotopy_F'_eq
    (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (hf : Differentiable ℂ f) (t s' : ℝ) :
    deriv (fun s'' => f (H (t, s'')) * deriv (fun t' => H (t', s'')) t) s' =
      deriv f (H (t, s')) * deriv (fun s'' => H (t, s'')) s' *
        deriv (fun t' => H (t', s')) t +
      f (H (t, s')) * deriv (fun s'' => deriv (fun t' => H (t', s'')) t) s' := by
  have hfH_diff_s' : DifferentiableAt ℝ (fun s'' => f (H (t, s''))) s' :=
    (hf (H (t, s')) |>.restrictScalars ℝ).comp s' (homotopy_H_differentiableAt_s H hH t s')
  have h_chain : deriv (fun s'' => f (H (t, s''))) s' =
      deriv f (H (t, s')) * deriv (fun s'' => H (t, s'')) s' := by
    have : (fun s'' => f (H (t, s''))) = f ∘ (fun s'' => H (t, s'')) := rfl
    rw [this]
    have := deriv.scomp s' (hf (H (t, s'))) (homotopy_H_differentiableAt_s H hH t s')
    simp only [smul_eq_mul, mul_comm] at this; exact this
  change deriv ((fun s'' => f (H (t, s''))) *
    (fun s'' => deriv (fun t' => H (t', s'')) t)) s' = _
  have h_dm := deriv_mul hfH_diff_s' (homotopy_partialT_differentiableAt_s H hH t s')
  erw [h_dm, h_chain, mul_assoc]

/-- Continuity of `(t, s') ↦ ∂/∂s' [f(H(t,s')) * ∂H/∂t(t,s')]`. -/
private lemma homotopy_F'_continuous
    (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ)
    (hH : ContDiff ℝ 2 H)
    (hfH_cont : Continuous (f ∘ H))
    (hf : Differentiable ℂ f) :
    Continuous (fun p : ℝ × ℝ =>
      deriv (fun s'' => f (H (p.1, s'')) * deriv (fun t' => H (t', s'')) p.1) p.2) := by
  have h_partialT := contDiff_partialDeriv_fst_of_contDiff_two H hH
  have h_partialS := contDiff_partialDeriv_snd_of_contDiff_two H hH
  have h_derivf' : Continuous (fun p : ℝ × ℝ => deriv f (H (p.1, p.2))) :=
    (hf.contDiff (n := ⊤) |>.continuous_deriv le_top).comp hH.continuous
  have hF'_fun_eq : (fun p : ℝ × ℝ =>
      deriv (fun s'' => f (H (p.1, s'')) * deriv (fun t' => H (t', s'')) p.1) p.2) =
    (fun p : ℝ × ℝ =>
      deriv f (H (p.1, p.2)) * deriv (fun s'' => H (p.1, s'')) p.2 *
        deriv (fun t' => H (t', p.2)) p.1 +
      f (H (p.1, p.2)) * deriv (fun s'' => deriv (fun t' => H (t', s'')) p.1) p.2) := by
    ext ⟨t, s'⟩; exact homotopy_F'_eq f H hH hf t s'
  rw [hF'_fun_eq]
  exact ((h_derivf'.mul h_partialS.continuous).mul h_partialT.continuous).add
    (hfH_cont.mul (homotopy_mixed_partial_continuous H hH))

/-- Uniform bound on the s-derivative of the integrand over a compact set. -/
private lemma homotopy_uniform_bound
    (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (a b s : ℝ) (hab : a < b)
    (hH : ContDiff ℝ 2 H)
    (hfH_cont : Continuous (f ∘ H))
    (hf : Differentiable ℂ f) :
    ∃ (ε : ℝ) (M : ℝ), 0 < ε ∧
      (∀ᵐ t ∂volume, t ∈ Ι a b →
        ∀ s' ∈ Metric.ball s ε,
          ‖deriv (fun s'' => f (H (t, s'')) *
            deriv (fun t' => H (t', s'')) t) s'‖ ≤ M) ∧
      IntervalIntegrable (fun _ => M) volume a b ∧
      Metric.ball s ε ∈ 𝓝 s := by
  have h_F'_cont := homotopy_F'_continuous f H hH hfH_cont hf
  let ε : ℝ := 1 / 4
  have hε_pos : (0 : ℝ) < ε := by norm_num
  let K : Set (ℝ × ℝ) := Icc a b ×ˢ Icc (s - ε) (s + ε)
  have hK_compact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hK_ne : K.Nonempty :=
    ⟨(a, s), left_mem_Icc.mpr (le_of_lt hab), by constructor <;> linarith⟩
  obtain ⟨M_pt, _, hM_pt_max⟩ :=
    hK_compact.exists_isMaxOn hK_ne (continuous_norm.comp h_F'_cont).continuousOn
  let M : ℝ := ‖deriv (fun s'' => f (H (M_pt.1, s'')) *
    deriv (fun t' => H (t', s'')) M_pt.1) M_pt.2‖
  have h_ball_subset : Metric.ball s ε ⊆ Icc (s - ε) (s + ε) := by
    intro x hx; simp only [Metric.mem_ball, Real.dist_eq] at hx
    constructor <;> linarith [abs_lt.mp hx]
  have h_uIoc_subset : (Ι a b : Set ℝ) ⊆ Icc a b :=
    Set.uIoc_subset_uIcc.trans (Set.uIcc_of_le (le_of_lt hab)).subset
  refine ⟨ε, M, hε_pos, ?_, intervalIntegrable_const, Metric.ball_mem_nhds s hε_pos⟩
  filter_upwards with t ht s' hs'
  have h_mem_K : (t, s') ∈ K := ⟨h_uIoc_subset ht, h_ball_subset hs'⟩
  have h_le := hM_pt_max h_mem_K
  simp only [Set.mem_setOf_eq, Function.comp_apply] at h_le
  exact h_le

/-- Continuity of `t ↦ f(H(t,s')) * ∂H/∂t(t,s')` for fixed s'. -/
private lemma homotopy_F_continuous_t
    (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (hfH_cont : Continuous (f ∘ H)) (s' : ℝ) :
    Continuous (fun t => f (H (t, s')) * deriv (fun t' => H (t', s')) t) :=
  (hfH_cont.comp (continuous_id.prodMk continuous_const)).mul
    ((contDiff_partialDeriv_fst_of_contDiff_two H hH).continuous.comp
      (continuous_id.prodMk continuous_const))

private lemma hasDerivAt_homotopy_param
    (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (a b s : ℝ)
    (hab : a < b)
    (hH_smooth : ContDiff ℝ 2 H)
    (hf_diff : ∀ t ∈ Icc a b,
      ∀ s' ∈ Icc (0 : ℝ) 1,
        DifferentiableAt ℂ f (H (t, s')))
    (hfH_cont : Continuous (f ∘ H))
    (hs : s ∈ Set.Icc 0 1)
    (hf_differentiable : Differentiable ℂ f)
    (h_schwarz : ∀ t ∈ Ioo a b,
        deriv (fun s' =>
          f (H (t, s')) *
            deriv (fun t' => H (t', s')) t) s =
          deriv (fun t' =>
            f (H (t', s)) *
              deriv (fun s'' => H (t', s'')) s) t) :
    HasDerivAt (fun s' => ∫ t in a..b,
        f (H (t, s')) *
          deriv (fun t' => H (t', s')) t)
      (∫ t in a..b,
        deriv (fun t' =>
          f (H (t', s)) *
            deriv (fun s'' => H (t', s'')) s) t) s := by
  let F : ℝ → ℝ → ℂ := fun s' t =>
    f (H (t, s')) * deriv (fun t' => H (t', s')) t
  -- Integral equality via Schwarz
  have h_integral_eq :
      ∫ t in a..b, deriv (fun s' => F s' t) s =
      ∫ t in a..b, deriv (fun t' =>
        f (H (t', s)) * deriv (fun s'' => H (t', s'')) s) t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    rw [Set.uIoc_of_le (le_of_lt hab)] at ht
    by_cases htb : t = b
    · change deriv (fun s' => f (H (t, s')) * deriv (fun t' => H (t', s')) t) s = _
      exact homotopy_schwarz_product_rule f H hH_smooth t s
        (hf_diff t (by rw [htb]; exact ⟨le_of_lt hab, le_refl b⟩) s hs) hf_differentiable
    · exact h_schwarz t ⟨ht.1, lt_of_le_of_ne ht.2 htb⟩
  -- Measurability + integrability
  have hF_meas : ∀ᶠ s' in 𝓝 s,
      AEStronglyMeasurable (F s') (volume.restrict (Ι a b)) := by
    filter_upwards [Filter.univ_mem] with s' _
    exact (homotopy_F_continuous_t f H hH_smooth hfH_cont s').aestronglyMeasurable
  have hF_int : IntervalIntegrable (F s) volume a b :=
    (homotopy_F_continuous_t f H hH_smooth hfH_cont s).intervalIntegrable (a := a) (b := b)
  have hF'_meas : AEStronglyMeasurable
      (fun t => deriv (fun s' => F s' t) s) (volume.restrict (Ι a b)) :=
    ((homotopy_F'_continuous f H hH_smooth hfH_cont hf_differentiable).comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  -- Uniform bound + pointwise HasDerivAt
  obtain ⟨ε, M, _, h_bound, h_bound_int, h_ball_mem⟩ :=
    homotopy_uniform_bound f H a b s hab hH_smooth hfH_cont hf_differentiable
  have h_diff : ∀ᵐ t ∂volume, t ∈ Ι a b →
      ∀ s' ∈ Metric.ball s ε,
        HasDerivAt (fun s'' => F s'' t) (deriv (fun s'' => F s'' t) s') s' := by
    filter_upwards with t _ht s' _hs'
    exact ((homotopy_fH_differentiableAt_s f H hH_smooth t s'
      (hf_differentiable (H (t, s')))).mul
      (homotopy_partialT_differentiableAt_s H hH_smooth t s')).hasDerivAt
  -- Apply Leibniz
  rw [← h_integral_eq]
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    h_ball_mem hF_meas hF_int hF'_meas h_bound h_bound_int h_diff).2

/-! ### Helpers for `hasDerivAt_homotopy_integral_zero` -/

/-- Continuity of `t ↦ deriv_{t'} [f(H(t', s)) * ∂H/∂s(t', s)]` on `[a, b]`. -/
private lemma homotopy_J_deriv_continuousOn
    (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (a b s : ℝ)
    (hH : ContDiff ℝ 2 H)
    (hfH_cont : Continuous (f ∘ H))
    (hf_diff : ∀ t ∈ Icc a b, ∀ s' ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℂ f (H (t, s')))
    (hs : s ∈ Set.Icc 0 1)
    (hf : Differentiable ℂ f) :
    ContinuousOn (fun t =>
      deriv (fun t' => f (H (t', s)) * deriv (fun s'' => H (t', s'')) s) t)
      (Icc a b) := by
  have h_partialS := contDiff_partialDeriv_snd_of_contDiff_two H hH
  have h_partialT := contDiff_partialDeriv_fst_of_contDiff_two H hH
  have h_embed : Continuous (fun t : ℝ => (t, s)) :=
    continuous_id.prodMk continuous_const
  have h_partial_cont : Continuous (fun t => deriv (fun s'' => H (t, s'')) s) :=
    h_partialS.continuous.comp h_embed
  have h_partial_deriv_cont : Continuous (fun t =>
      deriv (fun t' => deriv (fun s'' => H (t', s'')) s) t) :=
    (h_partialS.comp (contDiff_id.prodMk contDiff_const) : ContDiff ℝ 1 _).continuous_deriv le_rfl
  have h_fH_cont : Continuous (fun t => f (H (t, s))) := hfH_cont.comp h_embed
  -- Product rule gives closed form
  have h_deriv_eq : ∀ t ∈ Icc a b,
      deriv (fun t' => f (H (t', s)) * deriv (fun s'' => H (t', s'')) s) t =
        deriv (fun t' => f (H (t', s))) t * deriv (fun s'' => H (t, s'')) s +
        f (H (t, s)) * deriv (fun t' => deriv (fun s'' => H (t', s'')) s) t := by
    intro t ht
    exact deriv_mul (homotopy_fH_differentiableAt_t f H hH t s (hf_diff t ht s hs))
      (homotopy_partialS_differentiableAt_t H hH t s)
  -- Show the closed form is continuous
  suffices h_rhs_cont : ContinuousOn (fun t =>
      deriv (fun t' => f (H (t', s))) t * deriv (fun s'' => H (t, s'')) s +
      f (H (t, s)) * deriv (fun t' => deriv (fun s'' => H (t', s'')) s) t)
      (Icc a b) by
    exact h_rhs_cont.congr (fun t ht => h_deriv_eq t ht)
  apply ContinuousOn.add
  · apply ContinuousOn.mul _ h_partial_cont.continuousOn
    -- Use chain rule to rewrite
    have h_chain : ∀ t ∈ Icc a b,
        deriv (fun t' => f (H (t', s))) t =
          deriv f (H (t, s)) * deriv (fun t' => H (t', s)) t := by
      intro t _; exact homotopy_chain_rule_t f H hH t s hf
    suffices ContinuousOn (fun t =>
        deriv f (H (t, s)) * deriv (fun t' => H (t', s)) t) (Icc a b) by
      exact this.congr (fun t ht => h_chain t ht)
    exact ((((hf.contDiff (n := ⊤) |>.continuous_deriv le_top).comp
      hH.continuous).comp h_embed).mul (h_partialT.continuous.comp h_embed)).continuousOn
  · exact (h_fH_cont.mul h_partial_deriv_cont).continuousOn

/-- Derivative of the homotopy integral vanishes. -/
theorem hasDerivAt_homotopy_integral_zero
    (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (a b s : ℝ)
    (hab : a < b)
    (hH_smooth : ContDiff ℝ 2 H)
    (hf_diff : ∀ t ∈ Icc a b,
      ∀ s' ∈ Icc (0 : ℝ) 1,
        DifferentiableAt ℂ f (H (t, s')))
    (hfH_cont : Continuous (f ∘ H))
    (hs : s ∈ Set.Icc 0 1)
    (hderiv_a :
      deriv (fun s' => H (a, s')) s = 0)
    (hderiv_b :
      deriv (fun s' => H (b, s')) s = 0)
    (hf_differentiable : Differentiable ℂ f) :
    HasDerivAt
      (fun s' => ∫ t in a..b,
        f (H (t, s')) *
          deriv (fun t' => H (t', s')) t) 0 s := by
  let J : ℝ → ℝ → ℂ := fun t s' =>
    f (H (t, s')) * deriv (fun s'' => H (t, s'')) s'
  have h_boundary : J b s - J a s = 0 := by
    simp only [J, hderiv_a, hderiv_b, mul_zero, sub_zero]
  -- Main derivation: derivative = J(b,s) - J(a,s) = 0
  have h_deriv : HasDerivAt (fun s' => ∫ t in a..b,
      f (H (t, s')) * deriv (fun t' => H (t', s')) t) (J b s - J a s) s := by
    -- J is differentiable in t
    have hJ_diff_t : ∀ t ∈ Icc a b,
        DifferentiableAt ℝ (fun t' => J t' s) t := by
      intro t ht; simp only [J]
      exact (homotopy_fH_differentiableAt_t f H hH_smooth t s (hf_diff t ht s hs)).mul
        (homotopy_partialS_differentiableAt_t H hH_smooth t s)
    -- FTC: integral of deriv J = J(b) - J(a)
    have h_ftc : ∫ t in a..b, deriv (fun t' => J t' s) t = J b s - J a s := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t ht
        exact (hJ_diff_t t (Set.uIcc_subset_Icc
          ⟨le_refl a, le_of_lt hab⟩ ⟨le_of_lt hab, le_refl b⟩ ht)).hasDerivAt
      · exact ContinuousOn.intervalIntegrable_of_Icc (le_of_lt hab)
          (homotopy_J_deriv_continuousOn f H a b s hH_smooth hfH_cont hf_diff hs hf_differentiable)
    -- Schwarz: s-deriv of F = t-deriv of J
    have h_schwarz : ∀ t ∈ Ioo a b,
        deriv (fun s' => f (H (t, s')) * deriv (fun t' => H (t', s')) t) s =
          deriv (fun t' => J t' s) t := by
      intro t ht; simp only [J]
      exact homotopy_schwarz_product_rule f H hH_smooth t s
        (hf_diff t (Ioo_subset_Icc_self ht) s hs) hf_differentiable
    -- Apply hasDerivAt_homotopy_param and FTC
    rw [← h_ftc]
    exact hasDerivAt_homotopy_param f H a b s hab hH_smooth hf_diff hfH_cont hs
      hf_differentiable (fun t ht => h_schwarz t ht)
  rw [h_boundary] at h_deriv
  exact h_deriv

end

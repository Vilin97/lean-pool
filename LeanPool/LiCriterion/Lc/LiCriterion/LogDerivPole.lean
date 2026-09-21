/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.NhdsWithin

/-!
Pole/unboundedness lemmas for logarithmic derivatives.

These are used in the reverse direction of Li's criterion to turn a zero of a holomorphic
function into an unboundedness statement for its logarithmic derivative.
-/

open scoped Topology
open Filter

namespace LiCriterion

lemma nhdsWithin_neBot_punctured (z0 : ℂ) : NeBot (𝓝[≠] z0) := by
  refine (nhdsWithin_neBot).2 ?_
  intro t ht
  rcases Metric.mem_nhds_iff.1 ht with ⟨r, hrpos, hrball⟩
  refine ⟨z0 + (r / 2 : ℝ), ?_⟩
  constructor
  · refine hrball ?_
    have hdist : dist (z0 + (r / 2 : ℝ)) z0 = |r| / 2 := by
      simp [dist_eq_norm]
    have : dist (z0 + (r / 2 : ℝ)) z0 < r := by
      have hrabs : |r| = r := abs_of_pos hrpos
      simpa [hdist, hrabs] using (half_lt_self hrpos)
    exact this
  · have hrhalf_ne : (r / 2 : ℝ) ≠ 0 := ne_of_gt (half_pos hrpos)
    intro h
    have : ((r / 2 : ℝ) : ℂ) = 0 := by
      have := congrArg (fun w : ℂ => w - z0) h
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    exact hrhalf_ne (by simpa using congrArg Complex.re this)

lemma not_continuousAt_of_tendsto_norm_atTop (f : ℂ → ℂ) (z0 : ℂ)
    (h : Tendsto (fun z : ℂ => ‖f z‖) (𝓝[≠] z0) atTop) :
    ¬ ContinuousAt f z0 := by
  intro hcont
  -- boundedness from continuity
  have hb : ∃ M : ℝ, ∀ᶠ z in 𝓝[≠] z0, ‖f z‖ ≤ M := by
    have hε : ∀ᶠ z in 𝓝 z0, ‖f z - f z0‖ < (1 : ℝ) := by
      have : ∀ᶠ z in 𝓝 z0, dist (f z) (f z0) < (1 : ℝ) := by
        simpa [Metric.tendsto_nhds] using
          (hcont.tendsto.eventually (Metric.ball_mem_nhds (f z0) (by norm_num)))
      simpa [dist_eq_norm] using this
    refine ⟨‖f z0‖ + 1, ?_⟩
    have hε' : ∀ᶠ z in 𝓝[≠] z0, ‖f z - f z0‖ < (1 : ℝ) :=
      eventually_nhdsWithin_of_eventually_nhds hε
    filter_upwards [hε'] with z hz
    have hz' : f z = (f z - f z0) + f z0 := by abel
    have htri : ‖f z‖ ≤ ‖f z0‖ + ‖f z - f z0‖ := by
      have hnorm : ‖f z‖ = ‖(f z - f z0) + f z0‖ := congrArg (fun w : ℂ => ‖w‖) hz'
      calc
        ‖f z‖ = ‖(f z - f z0) + f z0‖ := hnorm
        _ ≤ ‖f z - f z0‖ + ‖f z0‖ := norm_add_le _ _
        _ = ‖f z0‖ + ‖f z - f z0‖ := by ac_rfl
    have : ‖f z - f z0‖ ≤ 1 := le_of_lt hz
    linarith
  rcases hb with ⟨M, hM⟩
  have hlarge : ∀ᶠ z in 𝓝[≠] z0, M + 1 ≤ ‖f z‖ := (tendsto_atTop.1 h) (M + 1)
  have hfalse : ∀ᶠ z in 𝓝[≠] z0, False := by
    filter_upwards [hM, hlarge] with z hzM hzlarge
    have : M + 1 ≤ M := le_trans hzlarge hzM
    linarith
  have : (𝓝[≠] z0) = ⊥ := (eventually_false_iff_eq_bot).1 hfalse
  exact (nhdsWithin_neBot_punctured z0).ne this

lemma logDeriv_congr_of_eventuallyEq (f g : ℂ → ℂ) (z : ℂ) (h : f =ᶠ[𝓝 z] g) :
    _root_.logDeriv f z = _root_.logDeriv g z := by
  have hder : deriv f z = deriv g z := Filter.EventuallyEq.deriv_eq (f₁ := f) (f := g) (x := z) h
  have hval : f z = g z := Filter.EventuallyEq.eq_of_nhds h
  simp [_root_.logDeriv, hder, hval]

lemma tendsto_atTop_sub_of_bounded {α : Type} {l : Filter α}
    {f g : α → ℝ} (hf : Tendsto f l atTop) (hg : ∃ M, ∀ᶠ x in l, g x ≤ M) :
    Tendsto (fun x => f x - g x) l atTop := by
  refine tendsto_atTop.2 ?_
  intro A
  rcases hg with ⟨M, hM⟩
  have hf' : ∀ᶠ x in l, A + M + 1 ≤ f x := (tendsto_atTop.1 hf) (A + M + 1)
  filter_upwards [hf', hM] with x hxF hxG
  have : A ≤ f x - g x := by
    have : A + g x + 1 ≤ f x := by
      have : A + g x + 1 ≤ A + M + 1 := by linarith
      exact le_trans this hxF
    linarith
  exact this

lemma tendsto_norm_inv_sub (z0 : ℂ) : Tendsto (fun z : ℂ => ‖(z - z0)⁻¹‖) (𝓝[≠] z0) atTop := by
  have hinv0 : Tendsto (fun x : ℂ => ‖x⁻¹‖) (𝓝[≠] (0 : ℂ)) atTop :=
    (tendsto_norm_inv_nhdsNE_zero_atTop (α := ℂ))
  have hsub : Tendsto (fun z : ℂ => z - z0) (𝓝[≠] z0) (𝓝[≠] (0 : ℂ)) := by
    refine (tendsto_nhdsWithin_iff (α := ℂ) (β := ℂ) (a := (0 : ℂ)) (l := (𝓝[≠] z0))
      (s := {w : ℂ | w ≠ (0 : ℂ)}) (f := fun z : ℂ => z - z0)).2 ?_
    constructor
    · have : Tendsto (fun z : ℂ => z - z0) (𝓝 z0) (𝓝 (0 : ℂ)) := by
        simpa using
          (tendsto_id.sub (tendsto_const_nhds : Tendsto (fun _ : ℂ => z0) (𝓝 z0) (𝓝 z0)))
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    · have : ∀ᶠ z in 𝓝[≠] z0, z ≠ z0 :=
        (self_mem_nhdsWithin : {z : ℂ | z ≠ z0} ∈ 𝓝[{z : ℂ | z ≠ z0}] z0)
      exact this.mono (fun z hz => sub_ne_zero.mpr hz)
  simpa [Function.comp_def] using hinv0.comp hsub

lemma tendsto_norm_div_sub_atTop (n : ℂ) (hn : n ≠ 0) (z0 : ℂ) :
    Tendsto (fun z => ‖n / (z - z0)‖) (𝓝[≠] z0) atTop := by
  have hinv : Tendsto (fun z : ℂ => ‖(z - z0)⁻¹‖) (𝓝[≠] z0) atTop := tendsto_norm_inv_sub z0
  have hnpos : 0 < ‖n‖ := norm_pos_iff.2 hn
  have hmul : Tendsto (fun z => ‖n‖ * ‖(z - z0)⁻¹‖) (𝓝[≠] z0) atTop :=
    (Filter.Tendsto.pos_mul_atTop hnpos (tendsto_const_nhds) hinv)
  have hrew : (fun z => ‖n / (z - z0)‖) = fun z => ‖n‖ * ‖(z - z0)⁻¹‖ := by
    funext z
    simp [div_eq_mul_inv]
  simpa [hrew, div_eq_mul_inv] using hmul

lemma tendsto_norm_add_div_atTop (n : ℂ) (hn : n ≠ 0) (z0 : ℂ) (g : ℂ → ℂ)
    (hg : ∃ M, ∀ᶠ z in 𝓝[≠] z0, ‖g z‖ ≤ M) :
    Tendsto (fun z => ‖n / (z - z0) + g z‖) (𝓝[≠] z0) atTop := by
  have hdiv : Tendsto (fun z => ‖n / (z - z0)‖) (𝓝[≠] z0) atTop :=
    tendsto_norm_div_sub_atTop n hn z0
  have hsub : Tendsto (fun z => ‖n / (z - z0)‖ - ‖g z‖) (𝓝[≠] z0) atTop :=
    tendsto_atTop_sub_of_bounded hdiv hg
  refine tendsto_atTop_mono ?_ hsub
  intro z
  have htri : ‖n / (z - z0)‖ ≤ ‖n / (z - z0) + g z‖ + ‖g z‖ := by
    have : n / (z - z0) = (n / (z - z0) + g z) - g z := by ring
    calc
      ‖n / (z - z0)‖ = ‖(n / (z - z0) + g z) - g z‖ :=
        congrArg (fun w : ℂ => ‖w‖) this
      _ ≤ ‖n / (z - z0) + g z‖ + ‖g z‖ := norm_sub_le _ _
  linarith

/-- At a nontrivial zero of an analytic function, the logarithmic derivative has unbounded norm. -/
theorem tendsto_norm_logDeriv_of_analyticAt_of_eq_zero {f : ℂ → ℂ} {z0 : ℂ}
    (hf : AnalyticAt ℂ f z0) (hf0 : f z0 = 0) (hne : ¬ (∀ᶠ z in 𝓝 z0, f z = 0)) :
    Tendsto (fun z => ‖_root_.logDeriv f z‖) (𝓝[≠] z0) atTop := by
  classical
  rcases (AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff (f := f) (z₀ := z0) hf).2 hne with
    ⟨n, g, hg_an, hg0_ne, hfg⟩
  have hfg_mul : ∀ᶠ z in 𝓝 z0, f z = (z - z0) ^ n * g z := by
    filter_upwards [hfg] with z hz
    simpa using hz
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have hfg_eq : f =ᶠ[𝓝 z0] g := by
      have : ∀ᶠ z in 𝓝 z0, f z = g z := by
        filter_upwards [hfg_mul] with z hz
        simpa [hn0] using hz
      exact this
    have : f z0 = g z0 := Filter.EventuallyEq.eq_of_nhds hfg_eq
    exact hg0_ne (by simpa [hf0] using this.symm)
  have hmem : {z : ℂ | f z = (z - z0) ^ n * g z} ∈ 𝓝 z0 := hfg_mul
  rcases mem_nhds_iff.1 hmem with ⟨V, hVsub, hVopen, hz0V⟩
  have hVnhds : V ∈ 𝓝 z0 := hVopen.mem_nhds hz0V
  have hVevent : ∀ᶠ z in 𝓝[≠] z0, z ∈ V :=
    eventually_nhdsWithin_of_eventually_nhds (by simpa using hVnhds)
  have hne' : ∀ᶠ z in 𝓝[≠] z0, z ≠ z0 :=
    (self_mem_nhdsWithin : {z : ℂ | z ≠ z0} ∈ 𝓝[{z : ℂ | z ≠ z0}] z0)
  have hpow_ne : ∀ᶠ z in 𝓝[≠] z0, (z - z0) ^ n ≠ 0 := by
    filter_upwards [hne'] with z hz
    exact pow_ne_zero n (sub_ne_zero.mpr hz)
  have hgne : ∀ᶠ z in 𝓝[≠] z0, g z ≠ 0 := by
    have : ∀ᶠ z in 𝓝 z0, g z ≠ 0 := hg_an.continuousAt.eventually_ne hg0_ne
    exact eventually_nhdsWithin_of_eventually_nhds this
  have hgdiff : ∀ᶠ z in 𝓝[≠] z0, DifferentiableAt ℂ g z := by
    have : ∀ᶠ z in 𝓝 z0, DifferentiableAt ℂ g z :=
      (hg_an.eventually_analyticAt).mono (fun z hz => hz.differentiableAt)
    exact eventually_nhdsWithin_of_eventually_nhds this
  have hglog_an : AnalyticAt ℂ (_root_.logDeriv g) z0 := by
    have hgder : AnalyticAt ℂ (deriv g) z0 := hg_an.deriv
    simpa [_root_.logDeriv] using hgder.div hg_an hg0_ne
  have hglog_bdd : ∃ M, ∀ᶠ z in 𝓝[≠] z0, ‖(_root_.logDeriv g) z‖ ≤ M := by
    have hcont : ContinuousAt (_root_.logDeriv g) z0 := hglog_an.continuousAt
    have hε : ∀ᶠ z in 𝓝 z0, ‖(_root_.logDeriv g) z - (_root_.logDeriv g) z0‖ < (1 : ℝ) := by
      have : ∀ᶠ z in 𝓝 z0,
          dist ((_root_.logDeriv g) z) ((_root_.logDeriv g) z0) < (1 : ℝ) := by
        simpa [Metric.tendsto_nhds] using
          (hcont.tendsto.eventually
            (Metric.ball_mem_nhds ((_root_.logDeriv g) z0) (by norm_num)))
      simpa [dist_eq_norm] using this
    refine ⟨‖(_root_.logDeriv g) z0‖ + 1, ?_⟩
    have hε' : ∀ᶠ z in 𝓝[≠] z0,
        ‖(_root_.logDeriv g) z - (_root_.logDeriv g) z0‖ < (1 : ℝ) :=
      eventually_nhdsWithin_of_eventually_nhds hε
    filter_upwards [hε'] with z hz
    have hz' :
        (_root_.logDeriv g) z =
          ((_root_.logDeriv g) z - (_root_.logDeriv g) z0) + (_root_.logDeriv g) z0 := by
      abel
    have htri :
        ‖(_root_.logDeriv g) z‖ ≤
          ‖(_root_.logDeriv g) z0‖ + ‖(_root_.logDeriv g) z - (_root_.logDeriv g) z0‖ := by
      have hnorm :
          ‖(_root_.logDeriv g) z‖ =
            ‖((_root_.logDeriv g) z - (_root_.logDeriv g) z0) + (_root_.logDeriv g) z0‖ := by
        exact congrArg (fun w : ℂ => ‖w‖) hz'
      calc
        ‖(_root_.logDeriv g) z‖ =
            ‖((_root_.logDeriv g) z - (_root_.logDeriv g) z0) + (_root_.logDeriv g) z0‖ := hnorm
        _ ≤ ‖(_root_.logDeriv g) z - (_root_.logDeriv g) z0‖ + ‖(_root_.logDeriv g) z0‖ :=
            norm_add_le _ _
        _ = ‖(_root_.logDeriv g) z0‖ + ‖(_root_.logDeriv g) z - (_root_.logDeriv g) z0‖ := by
            ac_rfl
    have : ‖(_root_.logDeriv g) z - (_root_.logDeriv g) z0‖ ≤ 1 := le_of_lt hz
    linarith
  have hlog_eq : ∀ᶠ z in 𝓝[≠] z0,
      _root_.logDeriv f z = (n : ℂ) / (z - z0) + _root_.logDeriv g z := by
    filter_upwards [hVevent, hpow_ne, hgne, hgdiff] with z hzV hzpow hzgn hzdiff
    have hEqOn : ∀ w ∈ V, f w = (w - z0) ^ n * g w := fun w hw => hVsub hw
    have hev : f =ᶠ[𝓝 z] (fun w => (w - z0) ^ n * g w) := by
      have hVnhds_z : V ∈ 𝓝 z := hVopen.mem_nhds hzV
      have : ∀ᶠ w in 𝓝 z, w ∈ V := by simpa using hVnhds_z
      refine this.mono ?_
      intro w hw
      exact hEqOn w hw
    have hlogcongr :
        _root_.logDeriv f z = _root_.logDeriv (fun w => (w - z0) ^ n * g w) z :=
      logDeriv_congr_of_eventuallyEq f (fun w => (w - z0) ^ n * g w) z hev
    have hdf : DifferentiableAt ℂ (fun w : ℂ => (w - z0) ^ n) z := by
      have hsub : DifferentiableAt ℂ (fun w : ℂ => w - z0) z := by
        exact differentiableAt_id.sub (differentiableAt_const (c := z0))
      have hpow : DifferentiableAt ℂ (fun x : ℂ => x ^ n) (z - z0) := by
        exact differentiableAt_pow (𝕜 := ℂ) (n := n) (x := z - z0)
      change DifferentiableAt ℂ (fun w : ℂ => ((fun x : ℂ => x ^ n) ((fun w : ℂ => w - z0) w))) z
      exact hpow.comp z hsub
    have hmul :
        _root_.logDeriv (fun w => (w - z0) ^ n * g w) z =
          _root_.logDeriv (fun w : ℂ => (w - z0) ^ n) z + _root_.logDeriv g z := by
      exact
        (_root_.logDeriv_fun_mul (f := fun w : ℂ => (w - z0) ^ n) (g := g) (x := z)
          hzpow hzgn hdf hzdiff)
    have hlin : _root_.logDeriv (fun w : ℂ => (w - z0) ^ n) z = (n : ℂ) / (z - z0) := by
      by_cases hn0 : n = 0
      · subst hn0
        simp [_root_.logDeriv]
      · have hdf' : DifferentiableAt ℂ (fun w : ℂ => w - z0) z := by
          exact differentiableAt_id.sub (differentiableAt_const (c := z0))
        have hpow' := _root_.logDeriv_fun_pow (f := fun w : ℂ => w - z0) (x := z) hdf' n
        have hld : _root_.logDeriv (fun w : ℂ => w - z0) z = (1 : ℂ) / (z - z0) := by
          simp [_root_.logDeriv]
        simpa [hld, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hpow'
    calc
      _root_.logDeriv f z
          = _root_.logDeriv (fun w => (w - z0) ^ n * g w) z := hlogcongr
      _ = _root_.logDeriv (fun w : ℂ => (w - z0) ^ n) z + _root_.logDeriv g z := hmul
      _ = (n : ℂ) / (z - z0) + _root_.logDeriv g z := by simp [hlin]
  have hn_ne : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hnpos)
  have hunb : Tendsto (fun z => ‖(n : ℂ) / (z - z0) + _root_.logDeriv g z‖) (𝓝[≠] z0) atTop :=
    tendsto_norm_add_div_atTop (n := (n : ℂ)) hn_ne z0 (_root_.logDeriv g) hglog_bdd
  exact hunb.congr' (hlog_eq.mono (fun z hz => by simp [hz]))

/-- A nontrivial zero of an analytic function forces the logarithmic derivative
to be non-analytic. -/
theorem not_analyticAt_logDeriv_of_analyticAt_of_eq_zero {f : ℂ → ℂ} {z0 : ℂ}
    (hf : AnalyticAt ℂ f z0) (hf0 : f z0 = 0) (hne : ¬ (∀ᶠ z in 𝓝 z0, f z = 0)) :
    ¬ AnalyticAt ℂ (_root_.logDeriv f) z0 := by
  intro han
  have hcont : ContinuousAt (_root_.logDeriv f) z0 := han.continuousAt
  have hunb := tendsto_norm_logDeriv_of_analyticAt_of_eq_zero (f := f) (z0 := z0) hf hf0 hne
  exact not_continuousAt_of_tendsto_norm_atTop (_root_.logDeriv f) z0 hunb hcont

end LiCriterion

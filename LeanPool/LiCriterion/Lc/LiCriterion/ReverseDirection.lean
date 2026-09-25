/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/
module


public import LeanPool.LiCriterion.Lc.LiCriterion.Basic
public import LeanPool.LiCriterion.Lc.LiCriterion.LogDerivPole
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.OrderClosed

/-!
# Li positivity implies RH

The unconditional half of Li's criterion: if every Li–Keiper coefficient has nonnegative real
part then `φ = ξ ∘ (z ↦ 1/(1-z))` is zero-free on the unit disk, by a Pringsheim-type argument,
and the functional equation pins every nontrivial zero to the critical line.
-/

@[expose] public section

open Complex Real Set Function Filter
open scoped Topology

namespace LiCriterion

noncomputable section

private abbrev φ : ℂ → ℂ := phi riemannXi
private abbrev g : ℂ → ℂ := LiCriterion.logDeriv (φ := φ)

private lemma term_eq (n : ℕ) (z : ℂ) :
    ((n.factorial : ℂ)⁻¹ • (z - (0 : ℂ)) ^ n • iteratedDeriv n g 0)
      = taylorCoeff riemannXi n * z ^ n := by
  simp [taylorCoeff, g, iteratedDeriv_eq_iterate, div_eq_mul_inv, smul_eq_mul]
  ring

private lemma hasSum_taylorCoeff_logDeriv_on_ball {r : ℝ}
    (hdiff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) r))
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) r) :
    HasSum (fun n : ℕ => taylorCoeff riemannXi n * z ^ n) (g z) := by
  have h := Complex.hasSum_taylorSeries_on_ball (f := g) (c := (0 : ℂ)) (r := r) hdiff hz
  refine h.congr_fun ?_
  intro n
  exact (term_eq (n := n) (z := z)).symm

private lemma differentiableOn_logDeriv_phi_on_ball {r : ℝ} (hr1 : r < 1)
    (hnz : ∀ z : ℂ, z ∈ Metric.ball (0 : ℂ) r → φ z ≠ 0) :
    DifferentiableOn ℂ g (Metric.ball (0 : ℂ) r) := by
  intro z hz
  have hz' : ‖z‖ < 1 := by
    have : ‖z‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    exact lt_trans this hr1
  have hφ : AnalyticAt ℂ φ z := phi_analytic xi_entire hz'
  have hφne : φ z ≠ 0 := hnz z hz
  have hder : AnalyticAt ℂ (deriv φ) z := hφ.deriv
  have hquot : AnalyticAt ℂ (fun w => deriv φ w / φ w) z := hder.div hφ hφne
  have hg : AnalyticAt ℂ g z := by
    exact hquot
  exact hg.differentiableAt.differentiableWithinAt

private lemma not_eventuallyEq_zero_phi {z0 : ℂ} (hz0 : ‖z0‖ < 1) :
    ¬ (∀ᶠ z in 𝓝 z0, φ z = 0) := by
  have hφ0 : φ (0 : ℂ) ≠ 0 := by
    simpa using (phi_riemannXi_ne_zero_of_real (r := (0 : ℝ)) (by linarith) (by linarith))
  intro hev
  have hφ_an : AnalyticOnNhd ℂ φ (Metric.ball (0 : ℂ) (1 : ℝ)) := by
    intro z hz
    have hz' : ‖z‖ < (1 : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    exact phi_analytic xi_entire hz'
  have hpre : IsPreconnected (Metric.ball (0 : ℂ) (1 : ℝ)) :=
    (convex_ball (0 : ℂ) (1 : ℝ)).isPreconnected
  have hz0mem : z0 ∈ Metric.ball (0 : ℂ) (1 : ℝ) := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz0
  have hev' : φ =ᶠ[𝓝 z0] 0 := by
    simpa [Filter.EventuallyEq, Pi.zero_apply] using hev
  have hEq : EqOn φ 0 (Metric.ball (0 : ℂ) (1 : ℝ)) :=
    hφ_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hz0mem hev'
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (1 : ℝ) := by
    simp [Metric.mem_ball]
  have : φ (0 : ℂ) = 0 := by
    simpa using hEq h0mem
  exact hφ0 this

private lemma phi_min_zero {z₁ : ℂ} (hz₁ : φ z₁ = 0) (hz₁' : ‖z₁‖ < 1) :
    ∃ z₀ : ℂ, φ z₀ = 0 ∧ ‖z₀‖ ≤ ‖z₁‖ ∧ (∀ z : ℂ, φ z = 0 → ‖z‖ < ‖z₀‖ → False) := by
  classical
  let r₁ : ℝ := ‖z₁‖
  have hr₁ : r₁ < 1 := by simpa [r₁] using hz₁'
  let K : Set ℂ := Metric.closedBall (0 : ℂ) r₁
  have hK : IsCompact K := isCompact_closedBall (0 : ℂ) r₁
  let K' : Type := {z : ℂ // z ∈ K}
  have : CompactSpace K' := (isCompact_iff_compactSpace (s := K)).1 hK
  let Z : Set K' := {z : K' | φ (z : ℂ) = 0}
  have hz1K : z₁ ∈ K := by
    have : dist z₁ (0 : ℂ) ≤ r₁ := by
      simp [r₁, dist_eq_norm]
    simpa [K] using (Metric.mem_closedBall.2 this)
  have hZ_ne : Z.Nonempty := by
    refine ⟨⟨z₁, hz1K⟩, ?_⟩
    simpa [Z] using hz₁
  have hφ_cont : Continuous (fun z : K' => φ (z : ℂ)) := by
    refine continuous_iff_continuousAt.2 ?_
    intro z
    have hz : ‖(z : ℂ)‖ < 1 := by
      have hzmem : (z : ℂ) ∈ K := z.property
      have hdist : dist (z : ℂ) (0 : ℂ) ≤ r₁ := (Metric.mem_closedBall).1 hzmem
      have hzle : ‖(z : ℂ)‖ ≤ r₁ := by
        simpa [dist_eq_norm, K] using hdist
      exact lt_of_le_of_lt hzle hr₁
    have hφ : AnalyticAt ℂ φ (z : ℂ) := phi_analytic xi_entire hz
    exact ContinuousAt.comp (x := z)
      (f := fun w : K' => (w : ℂ)) (g := φ) hφ.continuousAt continuous_subtype_val.continuousAt
  have hZ_closed : IsClosed Z := by
    have : Z = (fun z : K' => φ (z : ℂ)) ⁻¹' {0} := by
      ext z
      simp [Z]
    rw [this]
    simpa using (isClosed_singleton.preimage hφ_cont)
  have hZ_comp : IsCompact Z := hZ_closed.isCompact
  have hnorm_cont : Continuous (fun z : K' => ‖(z : ℂ)‖) := by
    exact continuous_norm.comp continuous_subtype_val
  rcases hZ_comp.exists_isMinOn hZ_ne hnorm_cont.continuousOn with ⟨z₀', hz₀Z, hz₀min⟩
  refine ⟨(z₀' : ℂ), ?_, ?_, ?_⟩
  · simpa [Z] using hz₀Z
  · have hzmem : (z₀' : ℂ) ∈ K := z₀'.property
    have hdist : dist (z₀' : ℂ) (0 : ℂ) ≤ r₁ := (Metric.mem_closedBall).1 hzmem
    have hzle : ‖(z₀' : ℂ)‖ ≤ r₁ := by simpa [dist_eq_norm, K] using hdist
    simpa [r₁] using hzle
  · intro z hz0 hlt
    have hzK : z ∈ K := by
      have : dist z (0 : ℂ) ≤ r₁ := by
        have : ‖z‖ ≤ r₁ := le_trans (le_of_lt hlt) (by
          have hzmem : (z₀' : ℂ) ∈ K := z₀'.property
          have hdist : dist (z₀' : ℂ) (0 : ℂ) ≤ r₁ := (Metric.mem_closedBall).1 hzmem
          have hzle : ‖(z₀' : ℂ)‖ ≤ r₁ := by simpa [dist_eq_norm, K] using hdist
          simpa using hzle)
        simpa [dist_eq_norm] using this
      simpa [K] using (Metric.mem_closedBall.2 this)
    have hzZ : (⟨z, hzK⟩ : K') ∈ Z := hz0
    have hmin := hz₀min hzZ
    exact (not_lt_of_ge hmin) hlt

private lemma re_mul_ofReal_pow (c : ℂ) (hcim : c.im = 0) (r : ℝ) (n : ℕ) :
    (c * (r : ℂ) ^ n).re = c.re * r ^ n := by
  have hre : Complex.re ((r : ℂ) ^ n) = r ^ n := by
    exact RCLike.re_ofReal_pow (K := ℂ) r n
  have him : Complex.im ((r : ℂ) ^ n) = 0 := by
    exact RCLike.im_ofReal_pow (K := ℂ) r n
  simp [Complex.mul_re, hre, him, hcim]

private lemma norm_eq_re_of_im_eq_zero_of_re_nonneg (c : ℂ) (hcim : c.im = 0)
    (hcpos : 0 ≤ c.re) : ‖c‖ = c.re := by
  have hc : c = (c.re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hcim]
  rw [hc]
  have hnorm : ‖(c.re : ℂ)‖ = |c.re| := RCLike.norm_ofReal (K := ℂ) c.re
  rw [hnorm, abs_of_nonneg hcpos]
  simp

private lemma norm_mul_pow_le (c z : ℂ) (n : ℕ) (hcim : c.im = 0) (hcpos : 0 ≤ c.re) :
    ‖c * z ^ n‖ ≤ c.re * ‖z‖ ^ n := by
  have hcnorm : ‖c‖ = c.re := norm_eq_re_of_im_eq_zero_of_re_nonneg c hcim hcpos
  have hznorm : ‖z ^ n‖ = ‖z‖ ^ n := by
    exact Complex.norm_pow z n
  calc
    ‖c * z ^ n‖ = ‖c‖ * ‖z ^ n‖ := by
      exact norm_mul c (z ^ n)
    _ = c.re * ‖z‖ ^ n := by
      simp [hcnorm, hznorm]
    _ ≤ c.re * ‖z‖ ^ n := le_rfl

private lemma norm_logDeriv_le_of_norm {r : ℝ} (_hr0 : 0 < r) (hr1 : r < 1)
    (hnz : ∀ z : ℂ, z ∈ Metric.ball (0 : ℂ) r → φ z ≠ 0)
    (hpos : ∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) r) :
    ‖g z‖ ≤ (g (‖z‖ : ℂ)).re := by
  have hdiff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) r) :=
    differentiableOn_logDeriv_phi_on_ball (r := r) hr1 hnz
  have hz_norm : ‖z‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hsumz : HasSum (fun n : ℕ => taylorCoeff riemannXi n * z ^ n) (g z) :=
    hasSum_taylorCoeff_logDeriv_on_ball (r := r) hdiff hz
  have hrz : (‖z‖ : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    have : ‖(‖z‖ : ℂ)‖ < r := by
      simpa using hz_norm
    simpa [Metric.mem_ball, dist_eq_norm] using this
  have hsumr : HasSum (fun n : ℕ => taylorCoeff riemannXi n * (‖z‖ : ℂ) ^ n) (g (‖z‖ : ℂ)) :=
    hasSum_taylorCoeff_logDeriv_on_ball (r := r) hdiff hrz
  have hsumr_re :
      HasSum (fun n : ℕ => (taylorCoeff riemannXi n * (‖z‖ : ℂ) ^ n).re) (g (‖z‖ : ℂ)).re :=
    Complex.hasSum_re (h := hsumr)
  have hsum_major :
      HasSum (fun n : ℕ => (taylorCoeff riemannXi n).re * ‖z‖ ^ n) (g (‖z‖ : ℂ)).re := by
    refine hsumr_re.congr_fun ?_
    intro n
    have hcim : (taylorCoeff riemannXi n).im = 0 := taylorCoeff_riemannXi_im n
    simpa using
      (re_mul_ofReal_pow (c := taylorCoeff riemannXi n) (hcim := hcim) (r := ‖z‖) (n := n)).symm
  have hbound_term : ∀ n : ℕ,
      ‖taylorCoeff riemannXi n * z ^ n‖ ≤ (taylorCoeff riemannXi n).re * ‖z‖ ^ n := by
    intro n
    have hcim : (taylorCoeff riemannXi n).im = 0 := taylorCoeff_riemannXi_im n
    have hcpos : 0 ≤ (taylorCoeff riemannXi n).re := hpos n
    simpa using (norm_mul_pow_le (c := taylorCoeff riemannXi n) (z := z) (n := n) hcim hcpos)
  have hnorm_le : ‖g z‖ ≤ (g (‖z‖ : ℂ)).re :=
    HasSum.norm_le_of_bounded (hf := hsumz) (hg := hsum_major) hbound_term
  exact hnorm_le

private noncomputable def zseq (z0 : ℂ) (n : ℕ) : ℂ :=
  (((1 : ℝ) - ((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) * z0

private lemma tendsto_zseq_nhds (z0 : ℂ) : Tendsto (zseq z0) atTop (𝓝 z0) := by
  have hnat : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    have : Tendsto (fun n : ℕ => (fun m : ℕ => m) (n + 1)) atTop atTop :=
      (Filter.tendsto_add_atTop_iff_nat (f := fun m : ℕ => m)
        (l := (atTop : Filter ℕ)) 1).2 tendsto_id
    simpa using this
  have hreal : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_iff (R := ℝ)).2 hnat
  have hinv : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hreal
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
  have ht0 :
      Tendsto (fun n : ℕ => (1 : ℝ) - ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 ((1 : ℝ) - (0 : ℝ))) :=
    hconst.sub hinv
  have ht : Tendsto (fun n : ℕ => (1 : ℝ) - ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa using ht0
  have htC0 :
      Tendsto (Complex.ofReal ∘ fun n : ℕ => (1 : ℝ) - ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 (1 : ℂ)) :=
    (Complex.continuous_ofReal.continuousAt.tendsto.comp ht)
  have htC :
      Tendsto (fun n : ℕ => (((1 : ℝ) - ((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    refine (Filter.Tendsto.congr
      (f₁ := Complex.ofReal ∘ fun n : ℕ => (1 : ℝ) - ((n + 1 : ℕ) : ℝ)⁻¹)
      (f₂ := fun n : ℕ => (((1 : ℝ) - ((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) ?_) htC0
    intro n
    rfl
  have hz0 : Tendsto (fun _ : ℕ => z0) atTop (𝓝 z0) := tendsto_const_nhds
  have hmul0 :
      Tendsto (fun n : ℕ => (((1 : ℝ) - ((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) * z0) atTop
        (𝓝 ((1 : ℂ) * z0)) :=
    htC.mul hz0
  have hmul :
      Tendsto (fun n : ℕ => (((1 : ℝ) - ((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) * z0) atTop (𝓝 z0) := by
    simpa [one_mul] using hmul0
  refine (Filter.Tendsto.congr
      (f₁ := fun n : ℕ => (((1 : ℝ) - ((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) * z0)
      (f₂ := zseq z0) ?_) hmul
  intro n
  rfl

private lemma tendsto_zseq_punctured (z0 : ℂ) (hz0 : z0 ≠ 0) :
    Tendsto (zseq z0) atTop (𝓝[≠] z0) := by
  have hnhds : Tendsto (zseq z0) atTop (𝓝 z0) := tendsto_zseq_nhds z0
  have hne : ∀ᶠ n in (atTop : Filter ℕ), zseq z0 n ≠ z0 := by
    refine Filter.Eventually.of_forall ?_
    intro n
    have ht_ne1 : (1 : ℝ) - ((n + 1 : ℕ) : ℝ)⁻¹ ≠ (1 : ℝ) := by
      have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)⁻¹ := by
        have hpos' : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos n)
        simpa using (inv_pos.2 hpos')
      have : (1 : ℝ) - ((n + 1 : ℕ) : ℝ)⁻¹ < 1 := by linarith
      exact ne_of_lt this
    have htC_ne1 : (((1 : ℝ) - ((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) ≠ (1 : ℂ) := by
      intro h
      have : (1 : ℝ) - ((n + 1 : ℕ) : ℝ)⁻¹ = 1 := Complex.ofReal_inj.1 h
      exact ht_ne1 this
    intro hEq
    have h' : (((1 : ℝ) - ((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) = (1 : ℂ) := by
      have : (((1 : ℝ) - ((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) * z0 = (1 : ℂ) * z0 := by
        simpa [zseq] using hEq
      exact mul_right_cancel₀ hz0 this
    exact htC_ne1 h'
  refine (tendsto_nhdsWithin_iff).2 ?_
  refine ⟨hnhds, ?_⟩
  filter_upwards [hne] with n hn
  exact hn

private lemma t_lt_one (n : ℕ) : (1 : ℝ) - ((n + 1 : ℕ) : ℝ)⁻¹ < 1 := by
  have hpos : 0 < ((n + 1 : ℕ) : ℝ)⁻¹ := by
    have : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos n)
    simpa using (inv_pos.2 this)
  linarith

private lemma t_nonneg (n : ℕ) : 0 ≤ (1 : ℝ) - ((n + 1 : ℕ) : ℝ)⁻¹ := by
  have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hinv : ((n + 1 : ℕ) : ℝ)⁻¹ ≤ (1 : ℝ)⁻¹ := by
    have := one_div_le_one_div_of_le (by positivity : 0 < (1 : ℝ)) hn1
    simpa [one_div] using this
  have : ((n + 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
    simpa using (le_trans hinv (by simp))
  linarith

private lemma norm_zseq_lt (z0 : ℂ) (hz0 : z0 ≠ 0) (n : ℕ) : ‖zseq z0 n‖ < ‖z0‖ := by
  set t : ℝ := (1 : ℝ) - ((n + 1 : ℕ) : ℝ)⁻¹ with ht
  have ht_lt_one : t < 1 := by simpa [ht] using t_lt_one n
  have ht_nonneg : 0 ≤ t := by simpa [ht] using t_nonneg n
  have hz0pos : 0 < ‖z0‖ := norm_pos_iff.2 hz0
  have h1 : ‖zseq z0 n‖ = |t| * ‖z0‖ := by
    unfold zseq
    have hmul : ‖((t : ℂ)) * z0‖ = ‖(t : ℂ)‖ * ‖z0‖ := by
      exact norm_mul (t : ℂ) z0
    have hn : ‖(t : ℂ)‖ = |t| := by
      exact RCLike.norm_ofReal (K := ℂ) t
    rw [ht, hmul, hn]
  have habs : |t| = t := abs_of_nonneg ht_nonneg
  have : |t| * ‖z0‖ < 1 * ‖z0‖ := by
    simpa [habs] using (mul_lt_mul_of_pos_right ht_lt_one hz0pos)
  simpa [h1] using this

private lemma phi_nonzero_unit_disk_of_nonneg (hpos : ∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re) :
    ∀ z : ℂ, ‖z‖ < 1 → φ z ≠ 0 := by
  intro z1 hz1norm
  by_contra hz1
  rcases phi_min_zero (z₁ := z1) hz1 hz1norm with ⟨z0, hz0, hz0_le, hz0_min⟩
  set r0 : ℝ := ‖z0‖
  have hr0_lt_one : r0 < 1 := lt_of_le_of_lt (by simpa [r0] using hz0_le) hz1norm
  have hφ0 : φ (0 : ℂ) ≠ 0 := by
    simpa using (phi_riemannXi_ne_zero_of_real (r := (0 : ℝ)) (by linarith) (by linarith))
  have hz0_ne0 : z0 ≠ 0 := by
    intro hz
    have : φ (0 : ℂ) = 0 := by simpa [hz] using hz0
    exact hφ0 this
  have hr0_pos : 0 < r0 := by
    simpa [r0] using (norm_pos_iff.2 hz0_ne0)
  have hnz : ∀ z : ℂ, z ∈ Metric.ball (0 : ℂ) r0 → φ z ≠ 0 := by
    intro z hz
    have hz' : ‖z‖ < r0 := by
      simpa [Metric.mem_ball, dist_eq_norm, r0] using hz
    intro hzφ
    exact hz0_min z hzφ (by simpa [r0] using hz')
  have hz0norm : ‖z0‖ < 1 := by simpa [r0] using hr0_lt_one
  have hφ_an : AnalyticAt ℂ φ z0 := phi_analytic xi_entire hz0norm
  have hne : ¬ (∀ᶠ z in 𝓝 z0, φ z = 0) := not_eventuallyEq_zero_phi (z0 := z0) hz0norm
  have h_unbdd : Tendsto (fun z => ‖g z‖) (𝓝[≠] z0) atTop := by
    have h :=
      tendsto_norm_logDeriv_of_analyticAt_of_eq_zero (f := φ) (z0 := z0) hφ_an hz0 hne
    simpa [g, LiCriterion.logDeriv, _root_.logDeriv] using h
  have hseq_punct : Tendsto (zseq z0) atTop (𝓝[≠] z0) := tendsto_zseq_punctured z0 hz0_ne0
  have h_unbdd_seq : Tendsto (fun n => ‖g (zseq z0 n)‖) atTop atTop := h_unbdd.comp hseq_punct
  have hmem_seq : ∀ n : ℕ, zseq z0 n ∈ Metric.ball (0 : ℂ) r0 := by
    intro n
    have hlt : ‖zseq z0 n‖ < r0 := by
      simpa [r0] using (norm_zseq_lt z0 hz0_ne0 n)
    simpa [Metric.mem_ball, dist_eq_norm] using hlt
  have hdom : ∀ n : ℕ, ‖g (zseq z0 n)‖ ≤ (g (‖zseq z0 n‖ : ℂ)).re := by
    intro n
    exact
      norm_logDeriv_le_of_norm (r := r0) hr0_pos hr0_lt_one hnz hpos (hz := hmem_seq n)
  have h_re_unbdd : Tendsto (fun n => (g (‖zseq z0 n‖ : ℂ)).re) atTop atTop :=
    (tendsto_atTop_mono hdom) h_unbdd_seq
  have hnorm_lim : Tendsto (fun n => ‖zseq z0 n‖) atTop (𝓝 r0) := by
    have := (tendsto_zseq_nhds z0).norm
    simpa [r0] using this
  have hcont : ContinuousAt (fun r : ℝ => (g (r : ℂ)).re) r0 := by
    have han : AnalyticAt ℂ (_root_.logDeriv (phi riemannXi)) (r0 : ℂ) :=
      analyticAt_logDeriv_phi_riemannXi_of_real (r := r0) (by linarith [hr0_pos.le]) hr0_lt_one
    have hcontC : ContinuousAt (_root_.logDeriv (phi riemannXi)) (r0 : ℂ) := han.continuousAt
    have hcontg : ContinuousAt g (r0 : ℂ) := by
      exact hcontC
    have hcontOfReal : ContinuousAt (fun r : ℝ => (r : ℂ)) r0 :=
      Complex.continuous_ofReal.continuousAt
    have hcontComp : ContinuousAt (fun r : ℝ => g (r : ℂ)) r0 :=
      ContinuousAt.comp (x := r0) (f := fun r : ℝ => (r : ℂ)) (g := g)
        (hg := hcontg) (hf := hcontOfReal)
    have hcontRe : ContinuousAt Complex.re (g (r0 : ℂ)) :=
      Complex.continuous_re.continuousAt
    simpa [Function.comp_def] using
      (ContinuousAt.comp (x := r0) (f := fun r : ℝ => g (r : ℂ)) (g := Complex.re)
        (hg := hcontRe) (hf := hcontComp))
  have hre_lim :
      Tendsto (fun n => (g (‖zseq z0 n‖ : ℂ)).re) atTop (𝓝 (g (r0 : ℂ)).re) :=
    hcont.tendsto.comp hnorm_lim
  exact (not_tendsto_nhds_of_tendsto_atTop h_re_unbdd (g (r0 : ℂ)).re) hre_lim

private lemma re_le_half_of_phi_nonzero (hphi : ∀ z : ℂ, ‖z‖ < 1 → φ z ≠ 0) (ρ : NontrivialZero) :
    ρ.val.re ≤ 1 / 2 := by
  have hxi : riemannXi ρ.val = 0 := (xi_zeros_are_nontrivial_zeros ρ.val).2 ⟨ρ, rfl⟩
  have hz : φ (1 - 1 / ρ.val) = 0 :=
    phi_zeros (f := riemannXi) (ρ := ρ.val) (hρ := NontrivialZero.ne_zero ρ) hxi
  by_contra hgt
  have hmod : ‖(1 : ℂ) - 1 / ρ.val‖ < 1 := by
    have : ρ.val.re > 1 / 2 := lt_of_not_ge hgt
    exact (modulus_criterion ρ.val (NontrivialZero.ne_zero ρ)).2 this
  have hne : φ (1 - 1 / ρ.val) ≠ 0 := hphi (1 - 1 / ρ.val) (by simpa using hmod)
  exact hne (by simpa using hz)

/-- **Reverse direction**: If all Li coefficients are non-negative, then RH holds. -/
theorem positivity_implies_RH :
    (∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re) →
      (∀ s : ℂ, riemannZeta s = 0 → (0 < s.re ∧ s.re < 1) → s.re = 1/2) := by
  intro hpos s hsζ hsstrip
  have hphi : ∀ z : ℂ, ‖z‖ < 1 → φ z ≠ 0 := phi_nonzero_unit_disk_of_nonneg hpos
  let ρ : NontrivialZero := ⟨s, hsζ, hsstrip.1, hsstrip.2⟩
  have hre_le : ρ.val.re ≤ 1 / 2 := re_le_half_of_phi_nonzero hphi ρ
  have hre_ge : 1 / 2 ≤ ρ.val.re := by
    have hpaired : (pairedZero ρ).val.re ≤ 1 / 2 :=
      re_le_half_of_phi_nonzero hphi (pairedZero ρ)
    have : 1 - ρ.val.re ≤ 1 / 2 := by
      simpa [pairedZero_val, sub_re, one_re] using hpaired
    linarith
  have : ρ.val.re = 1 / 2 := le_antisymm hre_le hre_ge
  simpa using this

end

end LiCriterion

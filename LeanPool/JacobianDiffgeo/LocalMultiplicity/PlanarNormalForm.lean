/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: local-multiplicity (CC4). Planar normal form `f = f z₀ + φ ^ k`.
-/
import LeanPool.JacobianDiffgeo.LocalMultiplicity.KthRoot
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Planar normal form (Forster Thm 2.1, planar half)

* `RS.AnalyticAt.exists_openPartialHomeomorph`: packaged planar analytic inverse function
  theorem — an analytic `f` with `deriv f z₀ ≠ 0` agrees near `z₀` with an
  `OpenPartialHomeomorph` that is analytic with analytic inverse.
* `RS.AnalyticAt.exists_normal_form`: if the recentered vanishing order of `f` at `z₀` is
  `k ≠ 0`, then `f = f z₀ + φ ^ k` near `z₀` for an analytic local coordinate `φ`
  (`φ z₀ = 0`, `deriv φ z₀ ≠ 0`); also a packaged `OpenPartialHomeomorph` version.
* `RS.analyticOrderAt_left_comp_sub`: the recentered order is invariant under postcomposition
  with a bi-analytic germ (left twin of mathlib's `analyticOrderAt_comp_of_deriv_ne_zero`).
* `RS.image_pow_ball`: `(· ^ k)` maps `ball 0 ρ` onto `ball 0 (ρ ^ k)`.
-/

open Filter Complex Metric
open scoped Topology

namespace RS

/-- Packaged planar analytic IFT: analytic + `deriv ≠ 0` gives an `OpenPartialHomeomorph`
agreeing with `f` near `z₀`, analytic with analytic inverse. -/
theorem AnalyticAt.exists_openPartialHomeomorph {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hf' : deriv f z₀ ≠ 0) :
    ∃ φ : OpenPartialHomeomorph ℂ ℂ, z₀ ∈ φ.source ∧ (∀ z ∈ φ.source, φ z = f z) ∧
      AnalyticOnNhd ℂ φ φ.source ∧ AnalyticOnNhd ℂ φ.symm φ.target := by
  -- the IFT partial homeomorphism, with `⇑Φ₀ = f` definitionally
  set Φ₀ : OpenPartialHomeomorph ℂ ℂ :=
    (hf.hasStrictDerivAt.hasStrictFDerivAt_equiv hf').toOpenPartialHomeomorph f with hΦ₀
  have hΦ₀coe : ⇑Φ₀ = f := rfl
  -- shrink to an open set where `f` is analytic with nonvanishing derivative
  have hev : ∀ᶠ z in 𝓝 z₀, (AnalyticAt ℂ f z ∧ deriv f z ≠ 0) ∧ z ∈ Φ₀.source := by
    refine (hf.eventually_analyticAt.and
      (hf.deriv.continuousAt.eventually_ne hf')).and ?_
    exact Φ₀.open_source.mem_nhds
      (HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _)
  obtain ⟨s, hsub, hso, hz₀s⟩ := _root_.mem_nhds_iff.mp hev
  refine ⟨Φ₀.restrOpen s hso, ⟨(hsub hz₀s).2, hz₀s⟩, fun z _ ↦ rfl, ?_, ?_⟩
  · -- `φ` is analytic on its source
    intro z hz
    exact (hsub hz.2).1.1
  · -- `φ.symm` is analytic on the target
    intro w hw
    set φ := Φ₀.restrOpen s hso with hφ
    have hzsrc : φ.symm w ∈ φ.source := φ.map_target hw
    obtain ⟨⟨hfz, hdz⟩, -⟩ := hsub hzsrc.2
    have hfzw : f (φ.symm w) = w := φ.right_inv hw
    -- mathlib's analytic local inverse at `φ.symm w`
    have hinv := hfz.analyticAt_localInverse hdz
    rw [hfzw] at hinv
    refine hinv.congr ?_
    -- the local inverse agrees with `φ.symm` near `w`
    have hleft := hfz.hasStrictDerivAt.eventually_left_inverse hdz
    have hcont : ContinuousAt φ.symm w := φ.continuousAt_symm hw
    filter_upwards [φ.open_target.mem_nhds hw, hcont.tendsto.eventually hleft] with w' hw' h
    have h2 : f (φ.symm w') = w' := φ.right_inv hw'
    calc hfz.hasStrictDerivAt.localInverse f _ _ hdz w'
        = hfz.hasStrictDerivAt.localInverse f _ _ hdz (f (φ.symm w')) := by rw [h2]
      _ = φ.symm w' := h

/-- Local normal form (Forster 2.1, planar half): finite recentered order `k ≥ 1` means
`f = f z₀ + φ ^ k` with `φ` an analytic local coordinate at `z₀`. -/
theorem AnalyticAt.exists_normal_form {f : ℂ → ℂ} {z₀ : ℂ} {k : ℕ}
    (hf : AnalyticAt ℂ f z₀) (hk : analyticOrderAt (f · - f z₀) z₀ = k) (hk₀ : k ≠ 0) :
    ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ z₀ ∧ φ z₀ = 0 ∧ deriv φ z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝 z₀, f z = f z₀ + φ z ^ k := by
  have hfa : AnalyticAt ℂ (f · - f z₀) z₀ := hf.sub analyticAt_const
  obtain ⟨g, hg, hg0, hfg⟩ := hfa.analyticOrderAt_eq_natCast.mp hk
  obtain ⟨r, hr, hr0, hrk⟩ := AnalyticAt.exists_pow_eq hg hg0 hk₀
  refine ⟨fun z ↦ (z - z₀) * r z, (analyticAt_id.sub analyticAt_const).mul hr, by simp, ?_, ?_⟩
  · -- derivative at `z₀` is `r z₀ ≠ 0`
    have hd : HasDerivAt (fun z ↦ (z - z₀) * r z) (1 * r z₀ + (z₀ - z₀) * deriv r z₀) z₀ :=
      ((hasDerivAt_id z₀).sub_const z₀).mul hr.differentiableAt.hasDerivAt
    have : deriv (fun z ↦ (z - z₀) * r z) z₀ = r z₀ := by
      simpa using hd.deriv
    rw [this]; exact hr0
  · filter_upwards [hfg, hrk] with z h1 h2
    have : f z - f z₀ = ((z - z₀) * r z) ^ k := by
      rw [h1, mul_pow, h2, smul_eq_mul]
    linear_combination this

/-- Normal form, packaged as an analytic-with-analytic-inverse partial homeomorphism. -/
theorem AnalyticAt.exists_normal_form_openPartialHomeomorph {f : ℂ → ℂ} {z₀ : ℂ} {k : ℕ}
    (hf : AnalyticAt ℂ f z₀) (hk : analyticOrderAt (f · - f z₀) z₀ = k) (hk₀ : k ≠ 0) :
    ∃ φ : OpenPartialHomeomorph ℂ ℂ, z₀ ∈ φ.source ∧ φ z₀ = 0 ∧
      AnalyticOnNhd ℂ φ φ.source ∧ AnalyticOnNhd ℂ φ.symm φ.target ∧
      ∀ z ∈ φ.source, f z = f z₀ + φ z ^ k := by
  obtain ⟨φ₀, hφ₀, hφ₀0, hφ₀', hev⟩ := AnalyticAt.exists_normal_form hf hk hk₀
  obtain ⟨Φ, hz₀, hΦeq, hΦan, hΦsymm⟩ := AnalyticAt.exists_openPartialHomeomorph hφ₀ hφ₀'
  -- shrink into the set where the normal form equation holds
  obtain ⟨s, hsub, hso, hz₀s⟩ := _root_.mem_nhds_iff.mp hev
  refine ⟨Φ.restrOpen s hso, ⟨hz₀, hz₀s⟩,
    by rw [show (Φ.restrOpen s hso) z₀ = φ₀ z₀ from hΦeq z₀ hz₀]; exact hφ₀0, ?_, ?_, ?_⟩
  · exact fun z hz ↦ hΦan z hz.1
  · exact fun w hw ↦ hΦsymm w hw.1
  · intro z hz
    rw [show (Φ.restrOpen s hso) z = φ₀ z from hΦeq z hz.1]
    exact hsub hz.2

/-- Recentered order is invariant under postcomposition with a bi-analytic germ.
(Left twin of mathlib's `analyticOrderAt_comp_of_deriv_ne_zero`; upstreamable.) -/
theorem analyticOrderAt_left_comp_sub {h f : ℂ → ℂ} {z₀ : ℂ}
    (hh : AnalyticAt ℂ h (f z₀)) (hh' : deriv h (f z₀) ≠ 0) (hf : AnalyticAt ℂ f z₀) :
    analyticOrderAt (fun z ↦ h (f z) - h (f z₀)) z₀ = analyticOrderAt (f · - f z₀) z₀ := by
  have h1 : analyticOrderAt ((h · - h (f z₀)) ∘ f) z₀ =
      analyticOrderAt (h · - h (f z₀)) (f z₀) * analyticOrderAt (f · - f z₀) z₀ :=
    (hh.sub analyticAt_const).analyticOrderAt_comp hf
  rw [hh.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hh', one_mul] at h1
  exact h1

/-- `z ↦ z ^ k` maps balls onto balls (fibre-counting geometry for mapping-degree). -/
theorem image_pow_ball {k : ℕ} (hk : k ≠ 0) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (· ^ k) '' Metric.ball (0 : ℂ) ρ = Metric.ball 0 (ρ ^ k) := by
  ext v
  simp only [Set.mem_image, mem_ball_zero_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [norm_pow]
    exact pow_lt_pow_left₀ hw (norm_nonneg w) hk
  · intro hv
    have hka : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    have hρpos : 0 < ρ := by
      rcases hρ.lt_or_eq with hρ' | hρ'
      · exact hρ'
      · exfalso
        rw [← hρ', zero_pow hk] at hv
        exact absurd hv (norm_nonneg v).not_gt
    rcases eq_or_ne v 0 with rfl | hv0
    · exact ⟨0, by simpa using hρpos, zero_pow hk⟩
    · refine ⟨exp (log v / k), ?_, ?_⟩
      · -- `‖exp (log v / k)‖ ^ k = ‖v‖ < ρ ^ k`
        have hpow : exp (log v / k) ^ k = v := by
          rw [← exp_nat_mul]
          rw [show (k : ℂ) * (log v / k) = log v by
            field_simp]
          exact exp_log hv0
        have : ‖exp (log v / k)‖ ^ k < ρ ^ k := by
          rw [← norm_pow, hpow]; exact hv
        exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hρ hk).mp this
      · rw [← exp_nat_mul, show (k : ℂ) * (log v / k) = log v by field_simp]
        exact exp_log hv0

end RS

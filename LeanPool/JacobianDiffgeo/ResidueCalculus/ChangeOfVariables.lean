/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: residue-calculus. Chart invariance of the residue of a 1-form integrand.
-/
import LeanPool.JacobianDiffgeo.ResidueCalculus.Residue
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Change of variables for residues (residue-calculus)

`RS.resAt_comp_mul_deriv` — chart invariance: for a local analytic isomorphism `φ` at `w₀` with
`φ w₀ = z₀`, the residue of the pulled-back 1-form integrand `(f ∘ φ) · φ'` at `w₀` equals the
residue of `f` at `z₀`. This is what makes `Res_p(ω)` on a Riemann surface chart-independent
(residue-theorem unit). Purely algebraic (route (a) of the design doc): no contour integration.

Main export: `RS.resAt_comp_mul_deriv`, and the `=ᶠ`-robust corollary
`RS.resAt_comp_mul_deriv_of_eventuallyEq`.
-/

open Filter Topology Metric Function

namespace RS

variable {f : ℂ → ℂ} {z₀ w₀ : ℂ}

/-- Chain rule for a `zpow` of a shifted, locally-differentiable function, in `HasDerivAt` form.
The workhorse for the `k ≤ -2` case of `resAt_comp_mul_deriv`. -/
private theorem hasDerivAt_sub_zpow_comp {φ : ℂ → ℂ} {w z₀ : ℂ} (hφ : DifferentiableAt ℂ φ w)
    (m : ℤ) (hm : φ w - z₀ ≠ 0 ∨ 0 ≤ m) :
    HasDerivAt (fun v => (φ v - z₀) ^ m) ((m : ℂ) * (φ w - z₀) ^ (m - 1) * deriv φ w) w := by
  have hsub : HasDerivAt (fun v => φ v - z₀) (deriv φ w) w := hφ.hasDerivAt.sub_const z₀
  simpa [Function.comp_def] using (hasDerivAt_zpow m (φ w - z₀) hm).comp w hsub

/-- Chart invariance of the residue of a 1-form integrand (Forster 9.9-flavored): for a local
analytic isomorphism `φ` at `w₀` with `φ w₀ = z₀`, the residue of `(f ∘ φ)·φ'` at `w₀` equals
the residue of `f` at `z₀`. Makes `Res_p(ω)` on a surface chart-independent (residue-theorem
unit). -/
theorem resAt_comp_mul_deriv {φ : ℂ → ℂ} (hφ : AnalyticAt ℂ φ w₀) (hφ' : deriv φ w₀ ≠ 0)
    (hφ₀ : φ w₀ = z₀) (hf : MeromorphicAt f z₀) :
    resAt (fun w => f (φ w) * deriv φ w) w₀ = resAt f z₀ := by
  -- Step 1: transport of the punctured filter.
  have hT : Tendsto φ (𝓝[≠] w₀) (𝓝[≠] z₀) := by
    have hthis := hφ.differentiableAt.hasDerivAt.tendsto_nhdsNE hφ'
    rwa [hφ₀] at hthis
  -- Step 2: decompose `f` into principal part + analytic remainder, pull back along `φ`.
  obtain ⟨h, hh, _, hdecomp⟩ := MeromorphicAt.exists_principalPart_add_analyticAt hf
  have hpullback : (fun w => f (φ w)) =ᶠ[𝓝[≠] w₀]
      fun w => principalPartAt f z₀ (φ w) + h (φ w) := hT.eventually hdecomp
  set a := (meromorphicOrderAt f z₀).untop₀ with hadef
  have hexact : (fun w => f (φ w) * deriv φ w) =ᶠ[𝓝[≠] w₀]
      fun w => (∑ k ∈ Finset.Icc a (-1), laurentCoeffAt f z₀ k * ((φ w - z₀) ^ k * deriv φ w))
        + h (φ w) * deriv φ w := by
    filter_upwards [hpullback] with w hw
    rw [hw]
    change (∑ k ∈ Finset.Icc a (-1), laurentCoeffAt f z₀ k * (φ w - z₀) ^ k + h (φ w))
        * deriv φ w = _
    rw [add_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [resAt_congr hexact]
  -- meromorphy facts, gathered once.
  have hhcompφ : AnalyticAt ℂ (fun w => h (φ w)) w₀ := hh.comp_of_eq hφ hφ₀
  have hzero : MeromorphicAt (fun w => h (φ w) * deriv φ w) w₀ :=
    hhcompφ.meromorphicAt.mul hφ.deriv.meromorphicAt
  have hsummand : ∀ k : ℤ,
      MeromorphicAt (fun w => laurentCoeffAt f z₀ k * ((φ w - z₀) ^ k * deriv φ w)) w₀ := by
    intro k
    have h1 : MeromorphicAt (fun w => φ w - z₀) w₀ :=
      hφ.meromorphicAt.sub analyticAt_const.meromorphicAt
    exact (MeromorphicAt.const _ w₀).mul ((h1.zpow k).mul hφ.deriv.meromorphicAt)
  rw [resAt_fun_add (MeromorphicAt.fun_sum fun k _ => hsummand k) hzero]
  have hhphi : AnalyticAt ℂ (fun w => h (φ w) * deriv φ w) w₀ := hhcompφ.mul hφ.deriv
  rw [resAt_of_analyticAt hhphi, add_zero, resAt_fun_sum (fun k _ => hsummand k)]
  -- Now compute each term: `k = -1` contributes `1`, `k ≤ -2` contributes `0`.
  have hterm : ∀ k ∈ Finset.Icc a (-1),
      resAt (fun w => laurentCoeffAt f z₀ k * ((φ w - z₀) ^ k * deriv φ w)) w₀
        = laurentCoeffAt f z₀ k * (if k = -1 then 1 else 0) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    rw [resAt_const_mul]
    congr 1
    by_cases hkm1 : k = -1
    · subst hkm1
      rw [if_pos rfl]
      -- log-derivative argument: `(φ - z₀)⁻¹ · φ' = deriv g / g` for `g := φ - z₀`, order `1`.
      have hgan : AnalyticAt ℂ (fun w => φ w - z₀) w₀ := hφ.sub analyticAt_const
      have horder1 : analyticOrderAt (fun w => φ w - φ w₀) w₀ = 1 :=
        hφ.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hφ'
      rw [hφ₀] at horder1
      have hmorder1 : meromorphicOrderAt (fun w => φ w - z₀) w₀ = 1 := by
        rw [hgan.meromorphicOrderAt_eq, horder1]; rfl
      have huntop1 : (meromorphicOrderAt (fun w => φ w - z₀) w₀).untop₀ = 1 := by
        rw [hmorder1]; rfl
      have hresdivg : resAt (fun w => deriv (fun v => φ v - z₀) w / (φ w - z₀)) w₀ = 1 := by
        have hrdd := MeromorphicAt.resAt_deriv_div hgan.meromorphicAt
        rw [huntop1] at hrdd
        simpa using hrdd
      have hfun_eq : (fun w => (φ w - z₀) ^ (-1 : ℤ) * deriv φ w)
          = fun w => deriv (fun v => φ v - z₀) w / (φ w - z₀) := by
        funext w
        rw [zpow_neg_one, deriv_sub_const, div_eq_inv_mul]
      rw [hfun_eq, hresdivg]
    · rw [if_neg hkm1]
      -- derivative argument: `(φ - z₀)^k · φ' = deriv F` for `F := (k+1)⁻¹ · (φ - z₀)^(k+1)`.
      have hkk1 : ((k : ℂ) + 1) ≠ 0 := by
        intro hcon
        exact hkm1 (by exact_mod_cast add_eq_zero_iff_eq_neg.mp hcon)
      have hFmero : MeromorphicAt (fun w => ((k : ℂ) + 1)⁻¹ * (φ w - z₀) ^ (k + 1)) w₀ := by
        have h1 : MeromorphicAt (fun w => φ w - z₀) w₀ :=
          hφ.meromorphicAt.sub analyticAt_const.meromorphicAt
        exact (MeromorphicAt.const _ w₀).mul (h1.zpow (k + 1))
      have hFderivEq : ∀ᶠ w in 𝓝[≠] w₀,
          deriv (fun v => ((k : ℂ) + 1)⁻¹ * (φ v - z₀) ^ (k + 1)) w
            = (φ w - z₀) ^ k * deriv φ w := by
        have hφdiffEv : ∀ᶠ w in 𝓝[≠] (w₀ : ℂ), DifferentiableAt ℂ φ w :=
          (Filter.Eventually.filter_mono nhdsWithin_le_nhds hφ.eventually_analyticAt).mono
            fun w hw => hw.differentiableAt
        have hTeventually : ∀ᶠ w in 𝓝[≠] w₀, φ w ≠ z₀ := hT.eventually self_mem_nhdsWithin
        filter_upwards [hφdiffEv, hTeventually] with w hwdiff hwne
        have hne : φ w - z₀ ≠ 0 := sub_ne_zero.2 hwne
        have hderivAt := hasDerivAt_sub_zpow_comp (z₀ := z₀) hwdiff (k + 1) (Or.inl hne)
        have hderivAt2 := hderivAt.const_mul ((k : ℂ) + 1)⁻¹
        have hval : ((k : ℂ) + 1)⁻¹ * (((k + 1 : ℤ) : ℂ) * (φ w - z₀) ^ (k + 1 - 1) * deriv φ w)
            = (φ w - z₀) ^ k * deriv φ w := by
          have hcast : ((k + 1 : ℤ) : ℂ) = (k : ℂ) + 1 := by push_cast; ring
          have hexp : (k + 1 - 1 : ℤ) = k := by ring
          rw [hcast, hexp]
          field_simp
        rw [hval] at hderivAt2
        exact hderivAt2.deriv
      have hcongr : (fun w => (φ w - z₀) ^ k * deriv φ w) =ᶠ[𝓝[≠] w₀]
          deriv (fun v => ((k : ℂ) + 1)⁻¹ * (φ v - z₀) ^ (k + 1)) :=
        Filter.EventuallyEq.symm hFderivEq
      rw [resAt_congr hcongr]
      exact MeromorphicAt.resAt_deriv hFmero
  rw [Finset.sum_congr rfl hterm]
  by_cases ha : a ≤ -1
  · rw [Finset.sum_eq_single (-1)
      (fun k hk hkne => by rw [if_neg hkne, mul_zero])
      (fun hnmem => absurd (Finset.mem_Icc.mpr ⟨ha, le_refl _⟩) hnmem)]
    rw [if_pos rfl, mul_one]
    rfl
  · push Not at ha
    have hempty : Finset.Icc a (-1) = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty]
    symm
    apply resAt_of_order_nonneg
    have h0a : (0 : ℤ) ≤ a := by omega
    rw [hadef] at h0a
    exact WithTop.untop₀_nonneg.mp h0a

/-- Corollary (residue-theorem convenience): the chart-invariance identity survives replacing
the integrand by anything `=ᶠ[𝓝[≠] w₀]`-equal to it. -/
theorem resAt_comp_mul_deriv_of_eventuallyEq {φ : ℂ → ℂ} (hφ : AnalyticAt ℂ φ w₀)
    (hφ' : deriv φ w₀ ≠ 0) (hφ₀ : φ w₀ = z₀) (hf : MeromorphicAt f z₀)
    {F : ℂ → ℂ} (hF : F =ᶠ[𝓝[≠] w₀] fun w => f (φ w) * deriv φ w) :
    resAt F w₀ = resAt f z₀ := by
  rw [resAt_congr hF]
  exact resAt_comp_mul_deriv hφ hφ' hφ₀ hf

end RS

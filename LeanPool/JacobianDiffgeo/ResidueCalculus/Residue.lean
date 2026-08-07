/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: residue-calculus. The residue functional `resAt` and its algebra.
-/
import LeanPool.JacobianDiffgeo.ResidueCalculus.PrincipalPart
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# The residue functional (residue-calculus)

`RS.resAt f z₀` is the `(-1)`-st Laurent coefficient of `f` at `z₀` — the residue. Purely
algebraic here; the circle-integral characterization is
`RS.circleIntegral_eq_two_pi_I_mul_resAt` (`IntegralBridge.lean`).

Main exports:
* Inherited ℂ-linear algebra: `RS.resAt_congr`, `RS.resAt_add`/`_fun_add`/`_const_mul`/`_neg`/
  `_sub`/`_fun_sum`;
* `RS.resAt_of_analyticAt`, `RS.resAt_of_order_nonneg` — vanishing off the pole locus;
* `RS.resAt_zpow_monomial`, `RS.resAt_sub_inv` — monomial residues;
* `RS.MeromorphicAt.resAt_deriv` — the residue of a derivative vanishes;
* `RS.MeromorphicAt.resAt_deriv_div` — the log-derivative residue is the order (argument
  principle atom);
* `RS.resAt_tail_mul`, `RS.resAt_analyticAt_mul`, `RS.resAt_mul` — Serre-pairing atoms
  (Miranda VI.3 `Res_ω` shape `Σ c_n a_{−1−n}`).
-/

open Filter Topology Metric Function

namespace RS

variable {f g h : ℂ → ℂ} {z₀ : ℂ} {k n : ℤ}

/-- The residue of `f` at `z₀`: the `(-1)`-st Laurent coefficient. Purely algebraic; the
circle-integral characterization is `RS.circleIntegral_eq_two_pi_I_mul_resAt`. -/
noncomputable def resAt (f : ℂ → ℂ) (z₀ : ℂ) : ℂ := laurentCoeffAt f z₀ (-1)

theorem resAt_congr (hfg : f =ᶠ[𝓝[≠] z₀] g) : resAt f z₀ = resAt g z₀ :=
  laurentCoeffAt_congr hfg (-1)

theorem resAt_fun_add (hf : MeromorphicAt f z₀) (hg : MeromorphicAt g z₀) :
    resAt (fun z => f z + g z) z₀ = resAt f z₀ + resAt g z₀ :=
  laurentCoeffAt_fun_add hf hg (-1)

theorem resAt_add (hf : MeromorphicAt f z₀) (hg : MeromorphicAt g z₀) :
    resAt (f + g) z₀ = resAt f z₀ + resAt g z₀ :=
  laurentCoeffAt_add hf hg (-1)

theorem resAt_const_mul (c : ℂ) : resAt (fun z => c * f z) z₀ = c * resAt f z₀ :=
  laurentCoeffAt_const_mul c (-1)

theorem resAt_neg : resAt (fun z => -f z) z₀ = -resAt f z₀ :=
  laurentCoeffAt_neg (-1)

theorem resAt_sub (hf : MeromorphicAt f z₀) (hg : MeromorphicAt g z₀) :
    resAt (fun z => f z - g z) z₀ = resAt f z₀ - resAt g z₀ :=
  laurentCoeffAt_sub hf hg (-1)

theorem resAt_fun_sum {ι : Type*} {s : Finset ι} {F : ι → ℂ → ℂ}
    (hF : ∀ i ∈ s, MeromorphicAt (F i) z₀) :
    resAt (fun z => ∑ i ∈ s, F i z) z₀ = ∑ i ∈ s, resAt (F i) z₀ :=
  laurentCoeffAt_fun_sum hF (-1)

theorem resAt_zero_fun : resAt (fun _ => (0 : ℂ)) z₀ = 0 :=
  laurentCoeffAt_zero_fun (-1)

@[simp] theorem resAt_of_analyticAt (hf : AnalyticAt ℂ f z₀) : resAt f z₀ = 0 := by
  rw [resAt, laurentCoeffAt_of_analyticAt hf]
  norm_num

theorem resAt_of_order_nonneg (h : 0 ≤ meromorphicOrderAt f z₀) : resAt f z₀ = 0 := by
  apply laurentCoeffAt_eq_zero_of_lt_order
  calc ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ) := by exact_mod_cast (by omega : (-1:ℤ) < 0)
    _ ≤ meromorphicOrderAt f z₀ := by exact_mod_cast h

@[simp] theorem resAt_zpow_monomial (m : ℤ) :
    resAt (fun z => (z - z₀) ^ m) z₀ = if m = -1 then 1 else 0 := by
  change laurentCoeffAt (fun z => (z - z₀) ^ m) z₀ (-1) = _
  rw [laurentCoeffAt_zpow_monomial]
  split_ifs <;> first | rfl | omega

@[simp] theorem resAt_sub_inv : resAt (fun z => (z - z₀)⁻¹) z₀ = 1 := by
  have hfun : (fun z => (z - z₀)⁻¹) = fun z => (z - z₀) ^ (-1 : ℤ) := by
    funext z; rw [zpow_neg_one]
  rw [hfun, resAt_zpow_monomial]
  simp

/-- Derivative of a monomial factor, in closed form and UNCONDITIONALLY (no nonvanishing side
condition needed — both sides are the mathlib `deriv`/`zpow` junk values, and they agree even
at `z = z₀`). The workhorse for `resAt_deriv`. -/
theorem deriv_sub_zpow (z₀ : ℂ) (m : ℤ) (z : ℂ) :
    deriv (fun w => (w - z₀) ^ m) z = (m : ℂ) * (z - z₀) ^ (m - 1) := by
  have h1 := deriv_comp_sub_const (fun v : ℂ => v ^ m) z₀ z
  rwa [deriv_zpow] at h1

/-- Residue of a derivative vanishes (Serre/Abel bookkeeping; the `k ≤ -2` engine of
change-of-variables). -/
theorem MeromorphicAt.resAt_deriv (hf : MeromorphicAt f z₀) : resAt (deriv f) z₀ = 0 := by
  obtain ⟨r, hr, _, hdecomp⟩ := MeromorphicAt.exists_principalPart_add_analyticAt hf
  have hderivEq : deriv f =ᶠ[𝓝[≠] z₀] deriv (fun z => principalPartAt f z₀ z + r z) :=
    hdecomp.nhdsNE_deriv
  have hrEventually : ∀ᶠ z in 𝓝[≠] (z₀ : ℂ), AnalyticAt ℂ r z :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hr.eventually_analyticAt
  have hsplit : deriv (fun z => principalPartAt f z₀ z + r z)
      =ᶠ[𝓝[≠] z₀] fun z => deriv (principalPartAt f z₀) z + deriv r z := by
    filter_upwards [self_mem_nhdsWithin, hrEventually] with z hzne hzan
    exact deriv_fun_add ((analyticOnNhd_principalPartAt z hzne).differentiableAt)
      hzan.differentiableAt
  have hPderiv : ∀ z, z ≠ z₀ →
      deriv (principalPartAt f z₀) z
        = ∑ k ∈ Finset.Icc (meromorphicOrderAt f z₀).untop₀ (-1),
            laurentCoeffAt f z₀ k * ((k : ℂ) * (z - z₀) ^ (k - 1)) := by
    intro z hz
    change deriv (fun z => ∑ k ∈ Finset.Icc (meromorphicOrderAt f z₀).untop₀ (-1),
        laurentCoeffAt f z₀ k * (z - z₀) ^ k) z = _
    rw [deriv_fun_sum (fun k _ => by
      have hzne : z - z₀ ≠ 0 := sub_ne_zero.2 hz
      have hzpow : DifferentiableAt ℂ (fun z => (z - z₀) ^ k) z :=
        (show DifferentiableAt ℂ (fun w : ℂ => w - z₀) z by fun_prop).zpow (Or.inl hzne)
      exact (differentiableAt_const _).mul hzpow)]
    exact Finset.sum_congr rfl fun k _ => by rw [deriv_const_mul_field, deriv_sub_zpow]
  have hPdEq : deriv (principalPartAt f z₀) =ᶠ[𝓝[≠] z₀]
      fun z => ∑ k ∈ Finset.Icc (meromorphicOrderAt f z₀).untop₀ (-1),
        laurentCoeffAt f z₀ k * ((k : ℂ) * (z - z₀) ^ (k - 1)) := by
    filter_upwards [self_mem_nhdsWithin] with z hzne using hPderiv z hzne
  have hfinal : deriv f =ᶠ[𝓝[≠] z₀]
      fun z => (∑ k ∈ Finset.Icc (meromorphicOrderAt f z₀).untop₀ (-1),
          laurentCoeffAt f z₀ k * ((k : ℂ) * (z - z₀) ^ (k - 1))) + deriv r z :=
    hderivEq.trans (hsplit.trans (hPdEq.add (Filter.EventuallyEq.rfl)))
  rw [resAt_congr hfinal, resAt_fun_add (MeromorphicAt.fun_sum fun k _ => by fun_prop)
    (hr.deriv.meromorphicAt), resAt_of_analyticAt hr.deriv, add_zero,
    resAt_fun_sum (fun k _ => by fun_prop)]
  apply Finset.sum_eq_zero
  intro k hk
  simp only [Finset.mem_Icc] at hk
  rw [resAt_const_mul, resAt_const_mul, resAt_zpow_monomial, if_neg (by omega : k - 1 ≠ -1)]
  ring

/-- Log-derivative residue = order (THE argument-principle atom; meromorphic-trace input).
Junk-robust: no order hypothesis (order `⊤` gives `0 = untop₀ ⊤`). -/
theorem MeromorphicAt.resAt_deriv_div (hf : MeromorphicAt f z₀) :
    resAt (fun z => deriv f z / f z) z₀ = ((meromorphicOrderAt f z₀).untop₀ : ℂ) := by
  by_cases h₂ : meromorphicOrderAt f z₀ = ⊤
  · have hf0 : f =ᶠ[𝓝[≠] z₀] fun _ => (0 : ℂ) := meromorphicOrderAt_eq_top_iff.1 h₂
    have hderiv0 : deriv f =ᶠ[𝓝[≠] z₀] deriv (fun _ : ℂ => (0 : ℂ)) := hf0.nhdsNE_deriv
    have hcongr : (fun z => deriv f z / f z) =ᶠ[𝓝[≠] z₀] fun _ => (0 : ℂ) := by
      filter_upwards [hderiv0, hf0] with z hz1 hz2
      rw [hz1, hz2]; simp
    rw [resAt_congr hcongr, resAt_zero_fun, h₂, WithTop.untop₀_top]
    norm_num
  · obtain ⟨u, h₁u, h₂u, h₃u⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h₂
    simp only [smul_eq_mul] at h₃u
    set m := (meromorphicOrderAt f z₀).untop₀ with hm
    have huEventually : ∀ᶠ z in 𝓝[≠] (z₀ : ℂ), u z ≠ 0 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (h₁u.continuousAt.eventually_ne h₂u)
    have huDiffEventually : ∀ᶠ z in 𝓝[≠] (z₀ : ℂ), DifferentiableAt ℂ u z :=
      (Filter.Eventually.filter_mono nhdsWithin_le_nhds h₁u.eventually_analyticAt).mono
        fun z hz => hz.differentiableAt
    have hderivEq : deriv f =ᶠ[𝓝[≠] z₀] deriv (fun z => (z - z₀) ^ m * u z) := h₃u.nhdsNE_deriv
    have hquot : (fun z => deriv f z / f z) =ᶠ[𝓝[≠] z₀]
        fun z => (m : ℂ) / (z - z₀) + deriv u z / u z := by
      filter_upwards [hderivEq, h₃u, huEventually, huDiffEventually, self_mem_nhdsWithin]
        with z hz1 hz2 hune hudiff hzne
      have hzz : z - z₀ ≠ 0 := sub_ne_zero.2 hzne
      have hfz : (z - z₀) ^ m * u z ≠ 0 := mul_ne_zero (zpow_ne_zero m hzz) hune
      have hdiffzpow : DifferentiableAt ℂ (fun w : ℂ => (w - z₀) ^ m) z :=
        (show DifferentiableAt ℂ (fun w : ℂ => w - z₀) z by fun_prop).zpow (Or.inl hzz)
      have hlog : logDeriv (fun w => (w - z₀) ^ m * u w) z
          = logDeriv (fun w => (w - z₀) ^ m) z + logDeriv u z :=
        logDeriv_mul z (zpow_ne_zero m hzz) hune hdiffzpow hudiff
      have hzsub : logDeriv (fun w : ℂ => w - z₀) z = 1 / (z - z₀) := by
        rw [logDeriv_apply, deriv_sub_const, deriv_id'']
      have hpow : logDeriv (fun w => (w - z₀) ^ m) z = (m : ℂ) * logDeriv (fun w => w - z₀) z :=
        logDeriv_fun_zpow (by fun_prop) m
      rw [hz1, hz2, ← logDeriv_apply]
      rw [hlog, hpow, hzsub, mul_one_div, logDeriv_apply]
    rw [resAt_congr hquot]
    have h1 : MeromorphicAt (fun z => (m : ℂ) / (z - z₀)) z₀ := by fun_prop
    have h2 : MeromorphicAt (fun z => deriv u z / u z) z₀ :=
        h₁u.deriv.meromorphicAt.div h₁u.meromorphicAt
    rw [resAt_fun_add h1 h2]
    have hterm1 : resAt (fun z => (m : ℂ) / (z - z₀)) z₀ = (m : ℂ) := by
      have : (fun z : ℂ => (m : ℂ) / (z - z₀)) = fun z => (m : ℂ) * (z - z₀)⁻¹ := by
        funext z; rw [div_eq_mul_inv]
      rw [this, resAt_const_mul, resAt_sub_inv, mul_one]
    have hterm2 : resAt (fun z => deriv u z / u z) z₀ = 0 :=
      resAt_of_analyticAt (h₁u.deriv.div h₁u h₂u)
    rw [hterm1, hterm2, add_zero]

/-- Multiplying by `(· - z₀) ^ m` shifts the residue (special case of `laurentCoeffAt_zpow_mul`
at `k = -1`). -/
theorem resAt_zpow_mul (hg : MeromorphicAt g z₀) (m : ℤ) :
    resAt (fun z => (z - z₀) ^ m * g z) z₀ = laurentCoeffAt g z₀ (-1 - m) :=
  laurentCoeffAt_zpow_mul hg m (-1)

/-- Serre-pairing atom, tail form (Miranda VI.3 eq. shape `Σ c_n a_{−1−n}`): residue of an
explicit Laurent tail times a meromorphic germ. -/
theorem resAt_tail_mul {c : ℤ → ℂ} {s : Finset ℤ} (hg : MeromorphicAt g z₀) :
    resAt (fun z => (∑ k ∈ s, c k * (z - z₀) ^ k) * g z) z₀
      = ∑ k ∈ s, c k * laurentCoeffAt g z₀ (-1 - k) := by
  have hfun : (fun z => (∑ k ∈ s, c k * (z - z₀) ^ k) * g z)
      = fun z => ∑ k ∈ s, c k * ((z - z₀) ^ k * g z) := by
    funext z
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hfun, resAt_fun_sum (fun k _ => by fun_prop)]
  exact Finset.sum_congr rfl fun k _ => by rw [resAt_const_mul, resAt_zpow_mul hg k]

/-- Residue of `h · (· - z₀) ^ m` for `h` analytic: computed by a single Taylor coefficient
of `h` (both cases — `m ≤ -1` genuinely picks it out, `m ≥ 0` gives an analytic product and `0`,
uniformly via the `if`). -/
theorem resAt_analyticAt_mul_zpow (hh : AnalyticAt ℂ h z₀) (m : ℤ) :
    resAt (fun z => h z * (z - z₀) ^ m) z₀
      = if 0 ≤ -1 - m then taylorCoeffAt h z₀ (-1 - m).toNat else 0 := by
  have hcomm : (fun z => h z * (z - z₀) ^ m) = fun z => (z - z₀) ^ m * h z := by
    funext z; ring
  rw [resAt, hcomm, laurentCoeffAt_zpow_mul hh.meromorphicAt, laurentCoeffAt_of_analyticAt hh]

/-- Serre-pairing atom, analytic-multiplier form: residue of `h·f` through `h`'s Taylor
coefficients against `f`'s principal Laurent coefficients (finite sum against the tail).
`n` is any integer lower bound for the order that the consumer holds. -/
theorem resAt_analyticAt_mul (hh : AnalyticAt ℂ h z₀) (hf : MeromorphicAt f z₀)
    {n : ℤ} (hn : (n : WithTop ℤ) ≤ meromorphicOrderAt f z₀) :
    resAt (fun z => h z * f z) z₀
      = ∑ k ∈ Finset.Icc n (-1), taylorCoeffAt h z₀ (-1 - k).toNat * laurentCoeffAt f z₀ k := by
  obtain ⟨r, hr, _, hdecomp⟩ := MeromorphicAt.exists_principalPart_add_analyticAt hf
  have hmulcongr : (fun z => h z * f z)
      =ᶠ[𝓝[≠] z₀] fun z => h z * principalPartAt f z₀ z + h z * r z := by
    filter_upwards [hdecomp] with z hz
    rw [hz]; ring
  have hPmero : MeromorphicAt (fun z => h z * principalPartAt f z₀ z) z₀ :=
    hh.meromorphicAt.mul meromorphicAt_principalPartAt
  have hRmero : MeromorphicAt (fun z => h z * r z) z₀ := hh.meromorphicAt.mul hr.meromorphicAt
  have hhr : AnalyticAt ℂ (fun z => h z * r z) z₀ := hh.mul hr
  rw [resAt_congr hmulcongr, resAt_fun_add hPmero hRmero, resAt_of_analyticAt hhr,
    add_zero]
  set m := (meromorphicOrderAt f z₀).untop₀ with hmdef
  have hexpand : (fun z => h z * principalPartAt f z₀ z)
      = fun z => ∑ k ∈ Finset.Icc m (-1), laurentCoeffAt f z₀ k * (h z * (z - z₀) ^ k) := by
    funext z
    change h z * (∑ k ∈ Finset.Icc m (-1), laurentCoeffAt f z₀ k * (z - z₀) ^ k) = _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hexpand, resAt_fun_sum (fun k _ => by fun_prop)]
  have hterm : ∀ k ∈ Finset.Icc m (-1),
      resAt (fun z => laurentCoeffAt f z₀ k * (h z * (z - z₀) ^ k)) z₀
        = taylorCoeffAt h z₀ (-1 - k).toNat * laurentCoeffAt f z₀ k := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    rw [resAt_const_mul, resAt_analyticAt_mul_zpow hh k, if_pos (by omega : (0:ℤ) ≤ -1 - k)]
    ring
  rw [Finset.sum_congr rfl hterm]
  by_cases h₂ : meromorphicOrderAt f z₀ = ⊤
  · have hmz : m = 0 := by rw [hmdef, h₂, WithTop.untop₀_top]
    rw [hmz]
    have hempty : Finset.Icc (0 : ℤ) (-1) = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty]
    symm
    apply Finset.sum_eq_zero
    intro k _
    rw [laurentCoeffAt_of_order_eq_top h₂, mul_zero]
  · have hnm : n ≤ m := by
      have hne : (n : WithTop ℤ) ≤ ((m : ℤ) : WithTop ℤ) := by
        rwa [hmdef, WithTop.coe_untop₀_of_ne_top h₂]
      exact_mod_cast hne
    apply Finset.sum_subset (Finset.Icc_subset_Icc hnm le_rfl)
    intro k hk hk'
    simp only [Finset.mem_Icc] at hk hk'
    have : laurentCoeffAt f z₀ k = 0 := by
      apply laurentCoeffAt_eq_zero_of_lt_order
      have : k < m := by omega
      calc (k : WithTop ℤ) < (m : WithTop ℤ) := by exact_mod_cast this
        _ = meromorphicOrderAt f z₀ := (WithTop.coe_untop₀_of_ne_top h₂).symm ▸ rfl
    rw [this, mul_zero]

/-- Combining two "one-sided" convolution sums (indices `≤ -1` resp. `≥ 0`) into the full
convolution sum, given the two sequences vanish below their respective bounds. The Cauchy-product
bookkeeping engine of `resAt_mul`: every integer `k` is either `≤ -1` or `≥ 0`, and the sums
`Icc n (-1)`/`Icc 0 (-1-m)` are always disjoint, so the only content is that
`Icc n (-1-m) ⊆ Icc n (-1) ∪ Icc 0 (-1-m)` with vanishing spillover. -/
private theorem sum_Icc_add_sum_Icc_eq_sum_Icc {n m : ℤ} (F G : ℤ → ℂ)
    (hF : ∀ k < n, F k = 0) (hG : ∀ k < m, G k = 0) :
    (∑ k ∈ Finset.Icc n (-1), F k * G (-1 - k))
        + (∑ k ∈ Finset.Icc 0 (-1 - m), F k * G (-1 - k))
      = ∑ k ∈ Finset.Icc n (-1 - m), F k * G (-1 - k) := by
  have hsub : Finset.Icc n (-1 - m) ⊆ Finset.Icc n (-1) ∪ Finset.Icc 0 (-1 - m) := by
    intro x hx
    simp only [Finset.mem_Icc] at hx
    simp only [Finset.mem_union, Finset.mem_Icc]
    rcases lt_or_ge x 0 with h | h
    · exact Or.inl ⟨hx.1, by omega⟩
    · exact Or.inr ⟨h, hx.2⟩
  have hdisj : Disjoint (Finset.Icc n (-1) : Finset ℤ) (Finset.Icc 0 (-1 - m)) := by
    apply Finset.disjoint_left.2
    intro a ha hb
    simp only [Finset.mem_Icc] at ha hb
    omega
  have hzero : ∀ x ∈ Finset.Icc n (-1) ∪ Finset.Icc 0 (-1 - m), x ∉ Finset.Icc n (-1 - m) →
      F x * G (-1 - x) = 0 := by
    intro x hx hx'
    simp only [Finset.mem_union, Finset.mem_Icc] at hx
    simp only [Finset.mem_Icc] at hx'
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hgt : -1 - m < x := by by_contra hcon; exact hx' ⟨h1, by omega⟩
      rw [hG (-1 - x) (by omega), mul_zero]
    · have hlt : x < n := by by_contra hcon; exact hx' ⟨by omega, h2⟩
      rw [hF x hlt, zero_mul]
  rw [← Finset.sum_union hdisj]
  exact (Finset.sum_subset hsub hzero).symm

/-- General product formula (both meromorphic; subsumes the two above — provided because
laurent-tails' `μ_f` operators multiply tails by meromorphic functions). -/
theorem resAt_mul (hf : MeromorphicAt f z₀) (hg : MeromorphicAt g z₀)
    {n m : ℤ} (hn : (n : WithTop ℤ) ≤ meromorphicOrderAt f z₀)
    (hm : (m : WithTop ℤ) ≤ meromorphicOrderAt g z₀) :
    resAt (fun z => f z * g z) z₀
      = ∑ k ∈ Finset.Icc n (-1 - m), laurentCoeffAt f z₀ k * laurentCoeffAt g z₀ (-1 - k) := by
  obtain ⟨rf, hrf, hrfcoeff, hfdecomp⟩ := MeromorphicAt.exists_principalPart_add_analyticAt hf
  have hmulcongr : (fun z => f z * g z)
      =ᶠ[𝓝[≠] z₀] fun z => principalPartAt f z₀ z * g z + rf z * g z := by
    filter_upwards [hfdecomp] with z hz
    rw [hz]; ring
  have hPmero : MeromorphicAt (fun z => principalPartAt f z₀ z * g z) z₀ :=
    meromorphicAt_principalPartAt.mul hg
  have hRmero : MeromorphicAt (fun z => rf z * g z) z₀ := hrf.meromorphicAt.mul hg
  rw [resAt_congr hmulcongr, resAt_fun_add hPmero hRmero]
  set a := (meromorphicOrderAt f z₀).untop₀ with hadef
  -- first term: `principalPartAt f z₀ · g` — tail form
  have hexpand : (fun z => principalPartAt f z₀ z * g z)
      = fun z => (∑ k ∈ Finset.Icc a (-1), laurentCoeffAt f z₀ k * (z - z₀) ^ k) * g z := rfl
  rw [hexpand, resAt_tail_mul hg]
  -- second term: `rf · g` — analytic-multiplier form
  rw [resAt_analyticAt_mul hrf hg hm]
  have hreindex : ∑ j ∈ Finset.Icc m (-1), taylorCoeffAt rf z₀ (-1 - j).toNat * laurentCoeffAt g
      z₀ j
      = ∑ k ∈ Finset.Icc 0 (-1 - m), laurentCoeffAt f z₀ k * laurentCoeffAt g z₀ (-1 - k) := by
    apply Finset.sum_nbij' (fun j => -1 - j) (fun k => -1 - k)
    · intro j hj; simp only [Finset.mem_Icc] at hj; simp only [Finset.mem_Icc]; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk; simp only [Finset.mem_Icc]; omega
    · intro j _; omega
    · intro k _; omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      have hidx : (-1 : ℤ) - (-1 - j) = j := by omega
      rw [hrfcoeff (-1 - j).toNat, Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -1 - j), hidx]
  rw [hreindex]
  -- pad the tail term from `Icc a (-1)` (the actual order) up to `Icc n (-1)` (the given bound)
  have hpad : ∑ k ∈ Finset.Icc a (-1), laurentCoeffAt f z₀ k * laurentCoeffAt g z₀ (-1 - k)
      = ∑ k ∈ Finset.Icc n (-1), laurentCoeffAt f z₀ k * laurentCoeffAt g z₀ (-1 - k) := by
    by_cases h₂ : meromorphicOrderAt f z₀ = ⊤
    · have haz : a = 0 := by rw [hadef, h₂, WithTop.untop₀_top]
      rw [haz]
      have hempty : Finset.Icc (0 : ℤ) (-1) = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hempty, Finset.sum_empty]
      exact (Finset.sum_eq_zero fun k _ => by rw [laurentCoeffAt_of_order_eq_top h₂, zero_mul]).symm
    · have hna : n ≤ a := by
        have hle : (n : WithTop ℤ) ≤ ((a : ℤ) : WithTop ℤ) := by
          rwa [hadef, WithTop.coe_untop₀_of_ne_top h₂]
        exact_mod_cast hle
      apply Finset.sum_subset (Finset.Icc_subset_Icc hna le_rfl)
      intro k hk hk'
      simp only [Finset.mem_Icc] at hk hk'
      have hklt : k < a := by omega
      have : laurentCoeffAt f z₀ k = 0 := by
        apply laurentCoeffAt_eq_zero_of_lt_order
        calc (k : WithTop ℤ) < (a : WithTop ℤ) := by exact_mod_cast hklt
          _ = meromorphicOrderAt f z₀ := WithTop.coe_untop₀_of_ne_top h₂
      rw [this, zero_mul]
  rw [hpad]
  exact sum_Icc_add_sum_Icc_eq_sum_Icc (laurentCoeffAt f z₀) (laurentCoeffAt g z₀)
    (fun k hk => laurentCoeffAt_eq_zero_of_lt_order
      (lt_of_lt_of_le (by exact_mod_cast hk) hn))
    (fun k hk => laurentCoeffAt_eq_zero_of_lt_order
      (lt_of_lt_of_le (by exact_mod_cast hk) hm))

end RS

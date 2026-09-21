/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

import LeanPool.LiCriterion.Lc.LiCriterion.Basic
import LeanPool.LiCriterion.Hadamard.OrderOne.OrderFromMaxModulus

/-!
# The order of the completed zeta function `ξ`

This file proves the two analytic facts that the Li-criterion biconditional
(`LiCriterion.biconditional_rh_li_of_hadamard_order_one`) still needs:

* `LiCriterion.riemannXi_hasFiniteOrder` : `ξ` is an entire function of finite order;
* `LiCriterion.riemannXi_order_le_one`   : the order of `ξ` is at most `1`.

## The route

The classical route bounds `ξ = ½ s (s-1) π^{-s/2} Γ(s/2) ζ(s)` factor by factor, and then owes a
polynomial bound for `ζ` in the critical strip -- which is not in Mathlib, and is the hard part.

This file avoids `ζ` entirely.  Mathlib builds `completedRiemannZeta₀` as a Mellin transform:

  `completedRiemannZeta₀ s = (mellin f_modif (s/2)) / 2`,

where `f_modif` is the modified theta kernel of the functional-equation pair
`HurwitzZeta.hurwitzEvenFEPair 0` -- explicitly `Θ(x) - 1` on `(1, ∞)` and `Θ(x) - x^{-1/2}` on
`(0, 1)`.  The kernel decays exponentially at `∞` (`isBigO_atTop_evenKernel_sub`), and the kernel
functional equation transports that decay to `0`.  Bounding the Mellin integral against those two
exponentials gives `‖Λ₀(w)‖ ≤ exp (O (‖w‖ log ‖w‖))` for *every* `w`, with no case split on the
critical strip, no Stirling expansion, and no growth bound for `ζ`.

The elementary majorant `u ^ A * exp (-p u) ≤ exp (A log (A/p))` (`rpow_mul_exp_neg_le`) does the
work that Stirling would otherwise do; it is just `log t ≤ t - 1`.
-/

namespace LiCriterion.XiGrowth

open Complex Real Set Filter MeasureTheory HurwitzZeta
open scoped Topology


/-! ## Part A: an elementary majorant -/

/-- The elementary bound `u ^ A * exp (-(p * u)) ≤ exp (A * log (A / p))`, valid for all
`u > 0`, `A ≥ 0`, `p > 0`.  This replaces any appeal to Stirling: it is just `log t ≤ t - 1`. -/
lemma rpow_mul_exp_neg_le {u A p : ℝ} (hu : 0 < u) (hA : 0 ≤ A) (hp : 0 < p) :
    u ^ A * rexp (-(p * u)) ≤ rexp (A * Real.log (A / p)) := by
  rcases eq_or_lt_of_le hA with rfl | hA'
  · have : rexp (-(p * u)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith : -(p * u) ≤ 0)
    simpa using this
  -- `A > 0`: take logarithms.
  have hAp : 0 < A / p := div_pos hA' hp
  have hkey : A * Real.log u - p * u ≤ A * Real.log (A / p) := by
    -- `log (u * p / A) ≤ u * p / A - 1`
    have h := Real.log_le_sub_one_of_pos (x := u * p / A) (by positivity)
    have hlog : Real.log (u * p / A) = Real.log u - Real.log (A / p) := by
      rw [Real.log_div (by positivity) (ne_of_gt hA'), Real.log_div (ne_of_gt hA') (ne_of_gt hp),
        Real.log_mul (ne_of_gt hu) (ne_of_gt hp)]
      ring
    rw [hlog] at h
    have hmul := mul_le_mul_of_nonneg_left h hA
    have : A * (u * p / A - 1) = p * u - A := by field_simp
    nlinarith [hA'.le]
  calc u ^ A * rexp (-(p * u))
      = rexp (A * Real.log u) * rexp (-(p * u)) := by
        rw [Real.rpow_def_of_pos hu]; ring_nf
    _ = rexp (A * Real.log u - p * u) := by rw [← Real.exp_add]; ring_nf
    _ ≤ rexp (A * Real.log (A / p)) := Real.exp_le_exp.2 hkey

/-! ## Part B: exponential decay of the theta kernel -/

/-- The even kernel at `a = 0` decays exponentially: there are `C, p > 0` with
`|Θ(x) - 1| ≤ C exp (-p x)` for every `x ≥ 1`.  Mathlib supplies the asymptotic; the content
here is upgrading it from `atTop` to all of `[1, ∞)` by compactness. -/
lemma exists_kernel_bound :
    ∃ C p : ℝ, 0 < C ∧ 0 < p ∧ ∀ x : ℝ, 1 ≤ x → |evenKernel 0 x - 1| ≤ C * rexp (-(p * x)) := by
  obtain ⟨p, hp, hO⟩ := isBigO_atTop_evenKernel_sub 0
  obtain ⟨c, hc⟩ := hO.bound
  obtain ⟨R, hR⟩ := eventually_atTop.1 hc
  set R' : ℝ := max R 1 with hR'
  have hR'1 : 1 ≤ R' := le_max_right _ _
  -- bound on the compact piece `[1, R']`
  have hcompact : IsCompact (Icc (1:ℝ) R') := isCompact_Icc
  have hcont : ContinuousOn (fun x : ℝ => evenKernel 0 x - 1) (Icc (1:ℝ) R') := by
    refine ContinuousOn.sub ?_ continuousOn_const
    exact (continuousOn_evenKernel 0).mono (fun x hx => lt_of_lt_of_le zero_lt_one hx.1)
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨max (max c 0) (max (M * rexp (p * R')) 0) + 1, p, by positivity, hp, ?_⟩
  intro x hx1
  set C := max (max c 0) (max (M * rexp (p * R')) 0) + 1 with hC
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  rcases le_or_gt x R' with hle | hgt
  · -- compact range: use the sup bound, paying `exp (p R')`
    have h1 : |evenKernel 0 x - 1| ≤ M := by simpa using hM x ⟨hx1, hle⟩
    have h2 : M * rexp (p * R') * rexp (-(p * x)) ≤ C * rexp (-(p * x)) := by
      have : M * rexp (p * R') ≤ C := by
        have := le_max_left (M * rexp (p * R')) 0
        have h' := le_max_right (max c 0) (max (M * rexp (p * R')) 0)
        simp only [hC]; linarith [le_trans this h']
      exact mul_le_mul_of_nonneg_right this (le_of_lt (Real.exp_pos _))
    refine le_trans (le_trans h1 ?_) h2
    have hexp : (1:ℝ) ≤ rexp (p * R') * rexp (-(p * x)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    nlinarith [le_trans (abs_nonneg _) h1, Real.exp_pos (p * R'), Real.exp_pos (-(p*x))]
  · -- tail: use the `atTop` bound
    have hxR : R ≤ x := le_trans (le_max_left R 1) (le_of_lt hgt)
    have h1 : ‖evenKernel 0 x - 1‖ ≤ c * ‖rexp (-p * x)‖ := by simpa using hR x hxR
    have h2 : c ≤ C := by
      have := le_max_left c 0
      have h' := le_max_left (max c 0) (max (M * rexp (p * R')) 0)
      simp only [hC]; linarith [le_trans this h']
    have hnorm : ‖rexp (-p * x)‖ = rexp (-(p * x)) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; ring_nf
    rw [Real.norm_eq_abs, hnorm] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (le_of_lt (Real.exp_pos _)))

/-! ## Part C: the modified kernel `f_modif` of the Riemann FE-pair -/

/-- The Riemann functional-equation pair, whose `Λ₀` is the completed zeta. -/
noncomputable abbrev PR : WeakFEPair ℂ := hurwitzEvenFEPair 0

lemma completedRiemannZeta₀_eq_mellin (s : ℂ) :
    completedRiemannZeta₀ s = (mellin PR.f_modif (s / 2)) / 2 := rfl

lemma f_modif_eq_of_one_lt {x : ℝ} (hx : 1 < x) :
    PR.f_modif x = (evenKernel 0 x : ℂ) - 1 := by
  simp [WeakFEPair.f_modif, hurwitzEvenFEPair, hx, not_lt.2 hx.le, Set.mem_Ioi, Set.mem_Ioo]

lemma f_modif_eq_of_lt_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    PR.f_modif x = (evenKernel 0 x : ℂ) - ((x ^ (-(1/2) : ℝ) : ℝ) : ℂ) := by
  have hnot : ¬ (1 < x) := not_lt.2 hx1.le
  simp [WeakFEPair.f_modif, hurwitzEvenFEPair, hnot, hx0, hx1, Set.mem_Ioi, Set.mem_Ioo]

/-- On `(1, ∞)` the modified kernel inherits the exponential decay of the theta kernel. -/
lemma norm_f_modif_of_one_lt {C p : ℝ}
    (hker : ∀ x : ℝ, 1 ≤ x → |evenKernel 0 x - 1| ≤ C * rexp (-(p * x)))
    {x : ℝ} (hx : 1 < x) : ‖PR.f_modif x‖ ≤ C * rexp (-(p * x)) := by
  rw [f_modif_eq_of_one_lt hx]
  have : ‖((evenKernel 0 x : ℂ) - 1)‖ = |evenKernel 0 x - 1| := by
    rw [show ((evenKernel 0 x : ℂ) - 1) = ((evenKernel 0 x - 1 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.norm_real _
  rw [this]
  exact hker x hx.le

/-- On `(0, 1)` the functional equation of the theta kernel converts the decay at `∞` into
decay at `0`: `‖f_modif x‖ ≤ C x^(-1/2) exp (-p/x)`. -/
lemma norm_f_modif_of_lt_one {C p : ℝ}
    (hker : ∀ x : ℝ, 1 ≤ x → |evenKernel 0 x - 1| ≤ C * rexp (-(p * x)))
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ‖PR.f_modif x‖ ≤ x ^ (-(1/2) : ℝ) * (C * rexp (-(p / x))) := by
  have hinv : 1 ≤ 1 / x := by rw [le_div_iff₀ hx0]; linarith
  -- the functional equation, at `a = 0`
  have hFE : evenKernel 0 x = x ^ (-(1/2) : ℝ) * evenKernel 0 (1 / x) := by
    rw [evenKernel_functional_equation 0 x, evenKernel_eq_cosKernel_of_zero,
      Real.rpow_neg hx0.le]
    ring
  have hval : PR.f_modif x = ((x ^ (-(1/2) : ℝ) * (evenKernel 0 (1 / x) - 1) : ℝ) : ℂ) := by
    rw [f_modif_eq_of_lt_one hx0 hx1, hFE]
    push_cast
    ring
  rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
  have hb := hker (1 / x) hinv
  have hpx : p * (1 / x) = p / x := by ring
  rw [hpx] at hb
  exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hx0.le _)

/-! ## Part D: the Mellin integral estimate -/

/-- Pointwise bound for the Mellin integrand on `(0, 1]`. -/
lemma integrand_le_of_mem_Ioc {C p : ℝ} (hC : 0 < C) (hp : 0 < p)
    (hker : ∀ x : ℝ, 1 ≤ x → |evenKernel 0 x - 1| ≤ C * rexp (-(p * x)))
    (w : ℂ) {x : ℝ} (hx : x ∈ Ioc (0:ℝ) 1) :
    ‖(x : ℂ) ^ (w - 1) • PR.f_modif x‖ ≤
      C * rexp (max (3/2 - w.re) 0 * Real.log (max (3/2 - w.re) 0 / p)) := by
  obtain ⟨hx0, hx1⟩ := hx
  set A := max (3/2 - w.re) 0 with hAdef
  have hA0 : 0 ≤ A := le_max_right _ _
  rcases eq_or_lt_of_le hx1 with rfl | hlt
  · -- at `x = 1` the modified kernel vanishes
    have h1 : PR.f_modif 1 = 0 := by
      simp [WeakFEPair.f_modif, Set.mem_Ioi, Set.mem_Ioo]
    simp only [h1, smul_zero, norm_zero]
    positivity
  · -- `0 < x < 1`
    have hnorm : ‖(x : ℂ) ^ (w - 1) • PR.f_modif x‖ = x ^ (w.re - 1) * ‖PR.f_modif x‖ := by
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      simp
    rw [hnorm]
    have hfb := norm_f_modif_of_lt_one hker hx0 hlt
    have hstep : x ^ (w.re - 1) * ‖PR.f_modif x‖
        ≤ x ^ (w.re - 1) * (x ^ (-(1/2) : ℝ) * (C * rexp (-(p / x)))) :=
      mul_le_mul_of_nonneg_left hfb (Real.rpow_nonneg hx0.le _)
    refine le_trans hstep ?_
    -- collect the powers of `x`
    have hxx : x ^ (w.re - 1) * x ^ (-(1/2) : ℝ) = x ^ (w.re - 3/2) := by
      rw [← Real.rpow_add hx0]; ring_nf
    have hcollect : x ^ (w.re - 1) * (x ^ (-(1/2) : ℝ) * (C * rexp (-(p / x))))
        = C * (x ^ (w.re - 3/2) * rexp (-(p / x))) := by
      rw [← hxx]; ring
    rw [hcollect]
    refine mul_le_mul_of_nonneg_left ?_ hC.le
    -- `x ^ (σ - 3/2) ≤ x ^ (-A)` because `x ≤ 1` and `-A ≤ σ - 3/2`
    have hmono : x ^ (w.re - 3/2) ≤ x ^ (-A) := by
      apply Real.rpow_le_rpow_of_exponent_ge hx0 hlt.le
      have : -A ≤ w.re - 3/2 := by
        simp only [hAdef, neg_le, le_max_iff]
        left; linarith
      linarith
    refine le_trans (mul_le_mul_of_nonneg_right hmono (Real.exp_pos _).le) ?_
    -- now apply the elementary majorant with `u = 1/x`
    have hu : (0:ℝ) < 1 / x := by positivity
    have hkey := rpow_mul_exp_neg_le (u := 1/x) (A := A) (p := p) hu hA0 hp
    have h1 : x ^ (-A) = (1/x) ^ A := by
      rw [one_div, Real.inv_rpow hx0.le, Real.rpow_neg hx0.le]
    have h2 : -(p / x) = -(p * (1/x)) := by ring
    rw [h1, h2]
    exact hkey

/-- Pointwise bound for the Mellin integrand on `(1, ∞)`. -/
lemma integrand_le_of_mem_Ioi {C p : ℝ} (hC : 0 < C) (hp : 0 < p)
    (hker : ∀ x : ℝ, 1 ≤ x → |evenKernel 0 x - 1| ≤ C * rexp (-(p * x)))
    (w : ℂ) {x : ℝ} (hx : x ∈ Ioi (1:ℝ)) :
    ‖(x : ℂ) ^ (w - 1) • PR.f_modif x‖ ≤
      C * rexp (max (w.re - 1) 0 * Real.log (max (w.re - 1) 0 / (p/2))) * rexp (-(p/2 * x)) := by
  have hx1 : (1:ℝ) < x := hx
  have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx1
  set B := max (w.re - 1) 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hnorm : ‖(x : ℂ) ^ (w - 1) • PR.f_modif x‖ = x ^ (w.re - 1) * ‖PR.f_modif x‖ := by
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    simp
  rw [hnorm]
  have hfb := norm_f_modif_of_one_lt hker hx1
  have hstep : x ^ (w.re - 1) * ‖PR.f_modif x‖ ≤ x ^ (w.re - 1) * (C * rexp (-(p * x))) :=
    mul_le_mul_of_nonneg_left hfb (Real.rpow_nonneg hx0.le _)
  refine le_trans hstep ?_
  -- `x ^ (σ - 1) ≤ x ^ B` because `x ≥ 1`
  have hmono : x ^ (w.re - 1) ≤ x ^ B :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (le_max_left _ _)
  have hstep2 : x ^ (w.re - 1) * (C * rexp (-(p * x))) ≤ x ^ B * (C * rexp (-(p * x))) := by
    have : (0:ℝ) ≤ C * rexp (-(p * x)) := by positivity
    exact mul_le_mul_of_nonneg_right hmono this
  refine le_trans hstep2 ?_
  -- split the exponential and apply the elementary majorant at rate `p/2`
  have hsplit : rexp (-(p * x)) = rexp (-(p/2 * x)) * rexp (-(p/2 * x)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit]
  have hkey := rpow_mul_exp_neg_le (u := x) (A := B) (p := p/2) hx0 hB0 (by positivity)
  calc x ^ B * (C * (rexp (-(p/2 * x)) * rexp (-(p/2 * x))))
      = C * (x ^ B * rexp (-(p/2 * x))) * rexp (-(p/2 * x)) := by ring
    _ ≤ C * rexp (B * Real.log (B / (p/2))) * rexp (-(p/2 * x)) := by
        have hxB : x ^ B * rexp (-(p/2 * x)) ≤ rexp (B * Real.log (B / (p/2))) := by
          have : -(p / 2 * x) = -(p/2 * x) := rfl
          exact hkey
        have hnn : (0:ℝ) ≤ rexp (-(p/2 * x)) := (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxB hC.le) hnn

/-- **The Mellin bound.**  The Mellin transform of the modified theta kernel is bounded by an
explicit expression in `Re w` alone.  No growth bound for `ζ` enters: the decay of the theta
kernel at `∞`, transported to `0` by the functional equation, is the whole input. -/
lemma norm_mellin_f_modif_le {C p : ℝ} (hC : 0 < C) (hp : 0 < p)
    (hker : ∀ x : ℝ, 1 ≤ x → |evenKernel 0 x - 1| ≤ C * rexp (-(p * x))) (w : ℂ) :
    ‖mellin PR.f_modif w‖ ≤
      C * rexp (max (3/2 - w.re) 0 * Real.log (max (3/2 - w.re) 0 / p))
      + C * rexp (max (w.re - 1) 0 * Real.log (max (w.re - 1) 0 / (p/2))) * (2/p) := by
  have hp2 : (0:ℝ) < p/2 := by positivity
  set K₁ := C * rexp (max (3/2 - w.re) 0 * Real.log (max (3/2 - w.re) 0 / p)) with hK1
  set K₂ := C * rexp (max (w.re - 1) 0 * Real.log (max (w.re - 1) 0 / (p/2))) with hK2
  have hK1nn : 0 ≤ K₁ := by rw [hK1]; positivity
  have hK2nn : 0 ≤ K₂ := by rw [hK2]; positivity
  -- integrability of the Mellin integrand, for free from the FE-pair machinery
  have hint : IntegrableOn (fun t : ℝ => (t:ℂ) ^ (w - 1) • PR.f_modif t) (Ioi 0) :=
    (PR.isStrongFEPair_toStrongFEPair.hasMellin w).1
  set F : ℝ → ℝ := fun x => ‖(x:ℂ) ^ (w - 1) • PR.f_modif x‖ with hFdef
  have hFint : IntegrableOn F (Ioi 0) := hint.norm
  have hFint1 : IntegrableOn F (Ioc 0 1) := hFint.mono_set Ioc_subset_Ioi_self
  have hFint2 : IntegrableOn F (Ioi 1) := hFint.mono_set (Ioi_subset_Ioi zero_le_one)
  -- ‖∫‖ ≤ ∫ ‖·‖, then split at 1
  have hstep1 : ‖mellin PR.f_modif w‖ ≤ ∫ x in Ioi (0:ℝ), F x :=
    norm_integral_le_integral_norm _
  have hdisj : Disjoint (Ioc (0:ℝ) 1) (Ioi (1:ℝ)) := by
    rw [Set.disjoint_left]
    intro a ha ha'
    exact absurd (mem_Ioi.1 ha') (not_lt.2 ha.2)
  have hsplit : ∫ x in Ioi (0:ℝ), F x = (∫ x in Ioc (0:ℝ) 1, F x) + ∫ x in Ioi (1:ℝ), F x := by
    rw [← setIntegral_union hdisj measurableSet_Ioi hFint1 hFint2,
      Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  -- the piece over `(0, 1]`
  have hb1 : (∫ x in Ioc (0:ℝ) 1, F x) ≤ K₁ := by
    have hconst : IntegrableOn (fun _ : ℝ => K₁) (Ioc (0:ℝ) 1) :=
      integrableOn_const (hs := measure_Ioc_lt_top.ne)
    have hmono : (∫ x in Ioc (0:ℝ) 1, F x) ≤ ∫ _x in Ioc (0:ℝ) 1, K₁ :=
      setIntegral_mono_on hFint1 hconst measurableSet_Ioc
        (fun x hx => integrand_le_of_mem_Ioc hC hp hker w hx)
    simpa using hmono
  -- the piece over `(1, ∞)`
  have hb2 : (∫ x in Ioi (1:ℝ), F x) ≤ K₂ * (2/p) := by
    have hexpint : IntegrableOn (fun x : ℝ => rexp (-(p/2 * x))) (Ioi 1) := by
      have := (integrableOn_Ioi_comp_mul_left_iff (fun u : ℝ => rexp (-u)) 1 hp2).2
        (integrableOn_exp_neg_Ioi (p/2 * 1))
      simpa using this
    have hgint : IntegrableOn (fun x : ℝ => K₂ * rexp (-(p/2 * x))) (Ioi 1) :=
      hexpint.const_mul K₂
    have hmono : (∫ x in Ioi (1:ℝ), F x) ≤ ∫ x in Ioi (1:ℝ), K₂ * rexp (-(p/2 * x)) :=
      setIntegral_mono_on hFint2 hgint measurableSet_Ioi
        (fun x hx => integrand_le_of_mem_Ioi hC hp hker w hx)
    have hcomp : (∫ x in Ioi (1:ℝ), K₂ * rexp (-(p/2 * x))) = K₂ * ((p/2)⁻¹ * rexp (-(p/2))) := by
      rw [integral_const_mul]
      congr 1
      have h := integral_comp_mul_left_Ioi (fun u : ℝ => rexp (-u)) 1 hp2
      rw [mul_one, integral_exp_neg_Ioi, smul_eq_mul] at h
      exact h
    rw [hcomp] at hmono
    refine le_trans hmono ?_
    have hfac : (p/2)⁻¹ * rexp (-(p/2)) ≤ 2/p := by
      have h1 : rexp (-(p/2)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      have h2 : (0:ℝ) < (p/2)⁻¹ := by positivity
      have h3 : (p/2)⁻¹ * rexp (-(p/2)) ≤ (p/2)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h1 h2.le
      have h4 : (p/2)⁻¹ = 2/p := by field_simp
      linarith [h3, h4 ▸ h3]
    exact mul_le_mul_of_nonneg_left hfac hK2nn
  calc ‖mellin PR.f_modif w‖ ≤ ∫ x in Ioi (0:ℝ), F x := hstep1
    _ = (∫ x in Ioc (0:ℝ) 1, F x) + ∫ x in Ioi (1:ℝ), F x := hsplit
    _ ≤ K₁ + K₂ * (2/p) := add_le_add hb1 hb2

/-! ## Part E: from the Mellin bound to a bound on `Λ₀` and `ξ` -/

/-- Monotonicity bookkeeping: `a log (a/q)` is dominated by its value at the upper end,
after clipping the logarithm at `0`. -/
lemma term_le {a M q : ℝ} (ha : 0 ≤ a) (haM : a ≤ M) (hq : 0 < q) :
    a * Real.log (a / q) ≤ M * max (Real.log (M / q)) 0 := by
  have hM : 0 ≤ M := le_trans ha haM
  have hmaxnn : 0 ≤ max (Real.log (M / q)) 0 := le_max_right _ _
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp [mul_nonneg hM hmaxnn]
  rcases le_or_gt (Real.log (a / q)) 0 with hlog | hlog
  · have : a * Real.log (a / q) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hlog
    exact le_trans this (mul_nonneg hM hmaxnn)
  · have hle : Real.log (a / q) ≤ Real.log (M / q) :=
      Real.log_le_log (by positivity) (by gcongr)
    calc a * Real.log (a / q) ≤ M * Real.log (a / q) :=
          mul_le_mul_of_nonneg_right haM hlog.le
      _ ≤ M * Real.log (M / q) := mul_le_mul_of_nonneg_left hle hM
      _ ≤ M * max (Real.log (M / q)) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hM

/-- The explicit majorant, as a function of the radius. -/
noncomputable def bnd (C p r : ℝ) : ℝ :=
  C * rexp ((3/2 + r) * max (Real.log ((3/2 + r) / p)) 0)
  + C * rexp (r * max (Real.log (r / (p/2))) 0) * (2/p)

/-- `r ↦ max (log (r/q)) 0` is monotone on `[0, ∞)`, including at `r = 0`. -/
lemma maxlog_mono {q : ℝ} (hq : 0 < q) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    max (Real.log (a / q)) 0 ≤ max (Real.log (b / q)) 0 := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp
  · exact max_le_max_right 0 (Real.log_le_log (by positivity) (by gcongr))

/-- The majorant is monotone in the radius. -/
lemma bnd_mono {C p : ℝ} (hC : 0 < C) (hp : 0 < p) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    bnd C p a ≤ bnd C p b := by
  have hq : (0:ℝ) < p/2 := by positivity
  have h1 : (3/2 + a) * max (Real.log ((3/2 + a) / p)) 0
      ≤ (3/2 + b) * max (Real.log ((3/2 + b) / p)) 0 := by
    refine mul_le_mul (by linarith) (maxlog_mono hp (by linarith) (by linarith))
      (le_max_right _ _) (by linarith)
  have h2 : a * max (Real.log (a / (p/2))) 0 ≤ b * max (Real.log (b / (p/2))) 0 :=
    mul_le_mul hab (maxlog_mono hq ha hab) (le_max_right _ _) (le_trans ha hab)
  unfold bnd
  refine add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) hC.le) ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) hC.le) (by positivity)

/-- The Mellin transform of the modified kernel, bounded in terms of `‖w‖` alone. -/
lemma norm_mellin_le_bnd {C p : ℝ} (hC : 0 < C) (hp : 0 < p)
    (hker : ∀ x : ℝ, 1 ≤ x → |evenKernel 0 x - 1| ≤ C * rexp (-(p * x))) (w : ℂ) :
    ‖mellin PR.f_modif w‖ ≤ bnd C p ‖w‖ := by
  refine le_trans (norm_mellin_f_modif_le hC hp hker w) ?_
  have hre : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  have hre1 : w.re ≤ ‖w‖ := le_trans (le_abs_self _) hre
  have hre2 : -‖w‖ ≤ w.re := neg_le_of_abs_le hre
  have hA : max (3/2 - w.re) 0 ≤ 3/2 + ‖w‖ := by
    apply max_le <;> [linarith; positivity]
  have hB : max (w.re - 1) 0 ≤ ‖w‖ := by
    apply max_le <;> [linarith; positivity]
  have h1 := term_le (le_max_right (3/2 - w.re) 0) hA hp
  have h2 := term_le (le_max_right (w.re - 1) 0) hB (by positivity : (0:ℝ) < p/2)
  unfold bnd
  refine add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) hC.le) ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) hC.le) (by positivity)

/-- The completed zeta `Λ₀`, bounded on the circle of radius `r`. -/
lemma norm_completedRiemannZeta₀_le {C p : ℝ} (hC : 0 < C) (hp : 0 < p)
    (hker : ∀ x : ℝ, 1 ≤ x → |evenKernel 0 x - 1| ≤ C * rexp (-(p * x))) (z : ℂ) :
    ‖completedRiemannZeta₀ z‖ ≤ bnd C p ‖z‖ := by
  rw [completedRiemannZeta₀_eq_mellin, norm_div]
  have h := norm_mellin_le_bnd hC hp hker (z / 2)
  have hnorm : ‖z / 2‖ = ‖z‖ / 2 := by simp
  rw [hnorm] at h
  have hmono : bnd C p (‖z‖ / 2) ≤ bnd C p ‖z‖ :=
    bnd_mono hC hp (by positivity) (by linarith [norm_nonneg z])
  have h2 : ‖(2:ℂ)‖ = 2 := by simp
  rw [h2]
  have : ‖mellin PR.f_modif (z/2)‖ / 2 ≤ bnd C p ‖z‖ / 2 := by
    apply div_le_div_of_nonneg_right (le_trans h hmono) (by norm_num)
  refine le_trans this ?_
  have hb : 0 ≤ bnd C p ‖z‖ := by unfold bnd; positivity
  linarith

/-! ## Part F: the bound on `ξ`, and the two order facts -/

/-- The constant collecting the `p`-dependence of the logarithms. -/
noncomputable def cst (p : ℝ) : ℝ := |Real.log p| + |Real.log (2/p)| + Real.log 3 + 1

lemma cst_pos (p : ℝ) : 0 < cst p := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  unfold cst; positivity

/-- The majorant, collapsed into a single exponential, for radii `≥ 1`. -/
lemma bnd_le_exp {C p r : ℝ} (hC : 0 < C) (hp : 0 < p) (hr : 1 ≤ r) :
    bnd C p r ≤ (C * (1 + 2/p)) * rexp (4 * r * (Real.log r + cst p)) := by
  have hr0 : (0:ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr
  have hc := cst_pos p
  have hsum : 0 ≤ Real.log r + cst p := by linarith
  -- the two exponents
  set X := (3/2 + r) * max (Real.log ((3/2 + r) / p)) 0 with hX
  set Y := r * max (Real.log (r / (p/2))) 0 with hY
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  -- `X ≤ 3 r (log r + c)`
  have hXle : X ≤ 3 * r * (Real.log r + cst p) := by
    have h1 : max (Real.log ((3/2 + r) / p)) 0 ≤ Real.log r + cst p := by
      apply max_le _ hsum
      have hle : (3/2 + r) / p ≤ 3 * r / p := by
        apply div_le_div_of_nonneg_right _ hp.le
        linarith
      have h2 : Real.log ((3/2 + r) / p) ≤ Real.log (3 * r / p) :=
        Real.log_le_log (by positivity) hle
      have h3 : Real.log (3 * r / p) = Real.log 3 + Real.log r - Real.log p := by
        rw [Real.log_div (by positivity) (ne_of_gt hp), Real.log_mul (by norm_num) (ne_of_gt hr0)]
      have h4 : -Real.log p ≤ |Real.log p| := neg_le_abs _
      unfold cst
      have h5 : 0 ≤ |Real.log (2/p)| := abs_nonneg _
      linarith [h2, h3.le, h3.ge]
    have h2 : (3/2 + r) ≤ 3 * r := by linarith
    rw [hX]
    calc (3/2 + r) * max (Real.log ((3/2 + r) / p)) 0
        ≤ (3 * r) * max (Real.log ((3/2 + r) / p)) 0 :=
          mul_le_mul_of_nonneg_right h2 (le_max_right _ _)
      _ ≤ (3 * r) * (Real.log r + cst p) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 3 * r * (Real.log r + cst p) := by ring
  -- `Y ≤ r (log r + c)`
  have hYle : Y ≤ r * (Real.log r + cst p) := by
    have h1 : max (Real.log (r / (p/2))) 0 ≤ Real.log r + cst p := by
      apply max_le _ hsum
      have h3 : Real.log (r / (p/2)) = Real.log r - Real.log (p/2) := by
        rw [Real.log_div (ne_of_gt hr0) (by positivity)]
      have h4 : Real.log (p/2) = -Real.log (2/p) := by
        rw [← Real.log_inv]; congr 1; field_simp
      have h5 : Real.log (2/p) ≤ |Real.log (2/p)| := le_abs_self _
      unfold cst
      have h6 : 0 ≤ |Real.log p| := abs_nonneg _
      have h7 : 0 < Real.log 3 := Real.log_pos (by norm_num)
      linarith [h3.le, h3.ge, h4.le, h4.ge]
    rw [hY]
    exact mul_le_mul_of_nonneg_left h1 hr0.le
  -- collapse the sum of two exponentials
  have hkey : rexp X + rexp Y * (2/p) ≤ (1 + 2/p) * rexp (X + Y) := by
    have h1 : rexp X ≤ rexp (X + Y) := Real.exp_le_exp.2 (by linarith)
    have h2 : rexp Y ≤ rexp (X + Y) := Real.exp_le_exp.2 (by linarith)
    have hpp : (0:ℝ) < 2/p := by positivity
    nlinarith [Real.exp_pos (X + Y), h1, h2]
  have hXY : X + Y ≤ 4 * r * (Real.log r + cst p) := by linarith
  calc bnd C p r = C * rexp X + C * rexp Y * (2/p) := rfl
    _ = C * (rexp X + rexp Y * (2/p)) := by ring
    _ ≤ C * ((1 + 2/p) * rexp (X + Y)) := mul_le_mul_of_nonneg_left hkey hC.le
    _ ≤ C * ((1 + 2/p) * rexp (4 * r * (Real.log r + cst p))) := by
        have : rexp (X + Y) ≤ rexp (4 * r * (Real.log r + cst p)) := Real.exp_le_exp.2 hXY
        have hnn : (0:ℝ) ≤ 1 + 2/p := by positivity
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this hnn) hC.le
    _ = (C * (1 + 2/p)) * rexp (4 * r * (Real.log r + cst p)) := by ring

/-- **The growth bound for `ξ`.**  For every `z` with `‖z‖ ≥ 1`,
`‖ξ z‖ ≤ exp (‖z‖ * (4 log ‖z‖ + K))` for a constant `K` depending only on the kernel data. -/
lemma norm_riemannXi_le_exp {C p : ℝ} (hC : 0 < C) (hp : 0 < p)
    (hker : ∀ x : ℝ, 1 ≤ x → |evenKernel 0 x - 1| ≤ C * rexp (-(p * x)))
    {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖riemannXi z‖
      ≤ rexp (‖z‖ * (4 * Real.log ‖z‖ +
          (max (Real.log (C * (1 + 2/p) + 1)) 0 + 2 + 4 * cst p))) := by
  set r := ‖z‖ with hrdef
  have hr0 : (0:ℝ) < r := lt_of_lt_of_le zero_lt_one hz
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hz
  have hc := cst_pos p
  set D := C * (1 + 2/p) with hD
  have hD0 : 0 < D := by rw [hD]; positivity
  -- pointwise bound on ξ
  have hΛ : ‖completedRiemannZeta₀ z‖ ≤ bnd C p r := norm_completedRiemannZeta₀_le hC hp hker z
  have hxi : ‖riemannXi z‖ ≤ (1/2) * r * (r + 1) * bnd C p r + 1/2 := by
    have hdef : riemannXi z = (1/2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z + (1/2 : ℂ) := rfl
    rw [hdef]
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖(1/2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z‖
        = (1/2) * r * ‖z - 1‖ * ‖completedRiemannZeta₀ z‖ := by
      simp [hrdef]
    have h2 : ‖z - 1‖ ≤ r + 1 := le_trans (norm_sub_le _ _) (by simp [hrdef])
    have h3 : ‖(1/2 : ℂ)‖ = 1/2 := by simp
    rw [h1, h3]
    have hbn : 0 ≤ bnd C p r := by unfold bnd; positivity
    have hstep : (1/2) * r * ‖z - 1‖ * ‖completedRiemannZeta₀ z‖
        ≤ (1/2) * r * (r + 1) * bnd C p r := by
      apply mul_le_mul _ hΛ (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  -- collapse the majorant
  have hb := bnd_le_exp (C := C) (p := p) hC hp hz
  have hmul : (1/2) * r * (r + 1) * bnd C p r + 1/2
      ≤ (D + 1) * r ^ 2 * rexp (4 * r * (Real.log r + cst p)) := by
    have he1 : (1:ℝ) ≤ rexp (4 * r * (Real.log r + cst p)) :=
      Real.one_le_exp (by positivity)
    have hpoly : (1/2) * r * (r + 1) ≤ r ^ 2 := by nlinarith
    have hbn : 0 ≤ bnd C p r := by unfold bnd; positivity
    have h1 : (1/2) * r * (r + 1) * bnd C p r
        ≤ r ^ 2 * (D * rexp (4 * r * (Real.log r + cst p))) := by
      apply mul_le_mul hpoly hb hbn (by positivity)
    have h2 : (1:ℝ)/2 ≤ 1 * r ^ 2 * rexp (4 * r * (Real.log r + cst p)) := by
      nlinarith [sq_nonneg (r - 1), hz, Real.exp_pos (4 * r * (Real.log r + cst p))]
    nlinarith [h1, h2, Real.exp_pos (4 * r * (Real.log r + cst p))]
  -- turn the polynomial prefactor into an exponential
  have hr2 : rexp (2 * Real.log r) = r ^ 2 := by
    rw [show (2:ℝ) * Real.log r = Real.log r + Real.log r by ring, Real.exp_add,
      Real.exp_log hr0]
    ring
  have hpre : (D + 1) * r ^ 2 = rexp (Real.log (D + 1) + 2 * Real.log r) := by
    rw [Real.exp_add, Real.exp_log (by positivity), hr2]
  have hfinal : Real.log (D + 1) + 2 * Real.log r + 4 * r * (Real.log r + cst p)
      ≤ r * (4 * Real.log r + (max (Real.log (D + 1)) 0 + 2 + 4 * cst p)) := by
    have h1 : Real.log (D + 1) ≤ max (Real.log (D + 1)) 0 * r := by
      have hm : 0 ≤ max (Real.log (D + 1)) 0 := le_max_right _ _
      nlinarith [le_max_left (Real.log (D + 1)) 0]
    have h2 : 2 * Real.log r ≤ 2 * r := by
      nlinarith [Real.log_le_sub_one_of_pos hr0]
    nlinarith [hc.le]
  calc ‖riemannXi z‖ ≤ (1/2) * r * (r + 1) * bnd C p r + 1/2 := hxi
    _ ≤ (D + 1) * r ^ 2 * rexp (4 * r * (Real.log r + cst p)) := hmul
    _ = rexp (Real.log (D + 1) + 2 * Real.log r) * rexp (4 * r * (Real.log r + cst p)) := by
        rw [hpre]
    _ = rexp (Real.log (D + 1) + 2 * Real.log r + 4 * r * (Real.log r + cst p)) := by
        rw [← Real.exp_add]
    _ ≤ rexp (r * (4 * Real.log r + (max (Real.log (D + 1)) 0 + 2 + 4 * cst p))) :=
        Real.exp_le_exp.2 hfinal

/-! ## Part G: the two order facts -/

/-- The growth bound, with the kernel data packaged away. -/
lemma exists_xi_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, 1 ≤ ‖z‖ →
    ‖riemannXi z‖ ≤ rexp (‖z‖ * (4 * Real.log ‖z‖ + K)) := by
  obtain ⟨C, p, hC, hp, hker⟩ := exists_kernel_bound
  refine ⟨max (Real.log (C * (1 + 2/p) + 1)) 0 + 2 + 4 * cst p, ?_, ?_⟩
  · have h1 : 0 ≤ max (Real.log (C * (1 + 2/p) + 1)) 0 := le_max_right _ _
    have h2 := (cst_pos p).le
    linarith
  · intro z hz
    exact norm_riemannXi_le_exp hC hp hker hz

/-- **`ξ` is an entire function of finite order.** -/
theorem riemannXi_hasFiniteOrder : Hadamard.hasFiniteOrder riemannXi := by
  obtain ⟨K, hK, hbd⟩ := exists_xi_bound
  refine ⟨xi_entire, 2, ?_⟩
  have hev : ∀ᶠ r : ℝ in atTop, 4 * Real.log r + K < r := by
    have hlog : ∀ᶠ r : ℝ in atTop, ‖Real.log r‖ ≤ (1/8) * ‖r ^ (1:ℝ)‖ :=
      (isLittleO_log_rpow_atTop one_pos).def (by norm_num)
    filter_upwards [hlog, eventually_ge_atTop (2*(K+1)), eventually_ge_atTop (1:ℝ)]
      with r h1 h2 hr1
    have hr0 : (0:ℝ) < r := lt_of_lt_of_le zero_lt_one hr1
    rw [Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr0] at h1
    have h3 : Real.log r ≤ (1/8) * r := le_trans (le_abs_self _) h1
    linarith
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 (hev.and (eventually_ge_atTop (1:ℝ)))
  refine ⟨max R₀ 1, ?_⟩
  intro z hz
  have hz1 : 1 ≤ ‖z‖ := le_trans (le_max_right R₀ 1) hz
  have hzR : R₀ ≤ ‖z‖ := le_trans (le_max_left R₀ 1) hz
  obtain ⟨hlt, -⟩ := hR₀ ‖z‖ hzR
  have hz0 : (0:ℝ) < ‖z‖ := lt_of_lt_of_le zero_lt_one hz1
  refine lt_of_le_of_lt (hbd z hz1) ?_
  apply Real.exp_lt_exp.2
  have hsq : ‖z‖ ^ (2:ℝ) = ‖z‖ * ‖z‖ := by
    rw [show (2:ℝ) = (1:ℝ) + 1 by norm_num, Real.rpow_add hz0, Real.rpow_one]
  rw [hsq]
  exact mul_lt_mul_of_pos_left hlt hz0

/-- **The order of `ξ` is at most `1`.** -/
theorem riemannXi_order_le_one : Hadamard.order riemannXi ≤ 1 := by
  obtain ⟨K, hK, hbd⟩ := exists_xi_bound
  refine Hadamard.order_le_one_of_forall_pos_eventually_maxModulus_le_exp_rpow_one_add
    riemannXi xi_entire ?_
  intro ε hε
  have hlog : ∀ᶠ r : ℝ in atTop, ‖Real.log r‖ ≤ (1/8) * ‖r ^ ε‖ :=
    (isLittleO_log_rpow_atTop hε).def (by norm_num)
  have hKe : ∀ᶠ r : ℝ in atTop, 2 * K ≤ r ^ ε :=
    (tendsto_rpow_atTop hε).eventually_ge_atTop (2 * K)
  filter_upwards [hlog, hKe, eventually_ge_atTop (1:ℝ)] with r h1 h2 hr1
  have hr0 : (0:ℝ) < r := lt_of_lt_of_le zero_lt_one hr1
  have hrpow : (0:ℝ) < r ^ ε := Real.rpow_pos_of_pos hr0 ε
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hrpow] at h1
  have h3 : Real.log r ≤ (1/8) * r ^ ε := le_trans (le_abs_self _) h1
  refine Hadamard.maxModulus_le_of_forall_norm_le _ xi_entire.continuous hr0.le ?_
  intro z hzr
  have hz1 : 1 ≤ ‖z‖ := by rw [hzr]; exact hr1
  have hb := hbd z hz1
  rw [hzr] at hb
  refine le_trans hb (Real.exp_le_exp.2 ?_)
  have hstep : 4 * Real.log r + K ≤ r ^ ε := by linarith
  have hmul : r * (4 * Real.log r + K) ≤ r * r ^ ε :=
    mul_le_mul_of_nonneg_left hstep hr0.le
  have hcomb : r * r ^ ε = r ^ (1 + ε) := by
    rw [Real.rpow_add hr0, Real.rpow_one]
  linarith [hmul, hcomb.le, hcomb.ge]

end LiCriterion.XiGrowth

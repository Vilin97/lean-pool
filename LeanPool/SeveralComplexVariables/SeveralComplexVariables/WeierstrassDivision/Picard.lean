/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LocallyUniform
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.WeierstrassDivision.CoordinatePower

/-!
# Picard iteration for Weierstrass division

Starting from division by a coordinate power, we construct successive approximations for a small
perturbation of that divisor. A geometric error bound gives a holomorphic limit; convergence of
Taylor coefficients identifies its polynomial remainder. A separate contraction argument proves
uniqueness for the perturbed division equation.

These results supply the iterative step of [Jakóbczak–Jarnicki][JakobczakJarnicki2021], Theorem
1.7.3. Normalization of a general divisor is in `SeveralComplexVariables.WeierstrassDivision`.

## Main definitions

* `picardApprox`: The Picard-iteration approximations to the coordinate-power quotient of `g` by a
  small perturbation `h` of `z ^ d`: `s 0 = 0`, and `s (k+1)` is the coordinate-power quotient of `g
  - h * s k`.
* `picardApproxCoeff`: The remainder coefficients accompanying `picardApprox`'s quotient at each
  step.

## Main results

* `picardApprox_diff_bound`: **Contraction estimate for the Picard iteration.** Consecutive Picard
  approximations of the coordinate-power quotient by `g - h * s_k` differ by a geometrically
  shrinking amount, given the numerator bound `M` for `g` and the small-perturbation bound on `h`.
* `exists_tendstoUniformlyOn_picardApprox`: **Locally uniform limit of the Picard iteration.** Under
  the contraction estimate of `picardApprox_diff_bound`, the Picard approximations converge
  uniformly on the domain to an analytic limit, with the geometric tail bound summed over all later
  steps.
* `exists_weierstrassRemainder_eq_of_tendstoUniformlyOn_picardApprox`: **The remainder of a Picard
  limit is itself a Weierstrass remainder.** Given a bound on the distance from each Picard
  approximation to a limit `S` (as produced by `exists_tendstoUniformlyOn_picardApprox`), the
  limiting perturbed-division remainder `g - h * S - ζ ^ d * S` is the Weierstrass remainder of the
  coefficients obtained by passing derivatives of the numerator's slices to the limit.
* `eqOn_of_isWeierstrassDivisionOn_selfPerturbed`: **Direct uniqueness for the perturbed
  coordinate-power fixed-point equation.** If `h` is uniformly small relative to `R` on a domain,
  any two decompositions of the *same* `g` against the divisor `z ^ d + h`, each individually
  bounded there, agree.

## References

* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
-/

public noncomputable section

open Complex Filter Finset Metric Set
open scoped Real Topology

namespace SeveralComplexVariables.WeierstrassDivision

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {ι : Type*} [Fintype ι]

/-- The Picard-iteration approximations to the coordinate-power quotient of `g` by a small
perturbation `h` of `z ^ d`: `s 0 = 0`, and `s (k+1)` is the coordinate-power quotient of `g - h
* s k`. Each approximation is holomorphic on the fixed polydisc. -/
@[expose] noncomputable def picardApprox (d : ℕ) (r : ι → ℝ) (R : ℝ) (hr : ∀ i, 0 < r i)
    (hR : 0 < R)
    (h g : (ι → ℂ) × ℂ → ℂ) (hg : DifferentiableOn ℂ g (polydisc 0 r ×ˢ ball 0 R))
    (hh : DifferentiableOn ℂ h (polydisc 0 r ×ˢ ball 0 R)) :
    ℕ → {s : (ι → ℂ) × ℂ → ℂ // DifferentiableOn ℂ s (polydisc 0 r ×ˢ ball 0 R)}
  | 0 => ⟨0, differentiableOn_const 0⟩
  | (k + 1) =>
    let prev := picardApprox d r R hr hR h g hg hh k
    ⟨(coordinatePower_division d hR (hg.sub (hh.mul prev.2))).choose,
      (coordinatePower_division d hR
        (hg.sub (hh.mul prev.2))).choose_spec.choose_spec.1.differentiableOn_quotient⟩

/-- The remainder coefficients accompanying `picardApprox`'s quotient at each step. -/
noncomputable def picardApproxCoeff (d : ℕ) (r : ι → ℝ) (R : ℝ) (hr : ∀ i, 0 < r i) (hR : 0 < R)
    (h g : (ι → ℂ) × ℂ → ℂ) (hg : DifferentiableOn ℂ g (polydisc 0 r ×ˢ ball 0 R))
    (hh : DifferentiableOn ℂ h (polydisc 0 r ×ˢ ball 0 R)) (k : ℕ) :
    Fin d → (ι → ℂ) → ℂ :=
  (coordinatePower_division d hR
    (hg.sub (hh.mul (picardApprox d r R hr hR h g hg hh k).2))).choose_spec.choose

/-- Each Picard step genuinely divides `g - h * (previous step)` by `z ^ d`. -/
theorem picardApprox_succ_isWeierstrassDivisionOn (d : ℕ) (r : ι → ℝ) (R : ℝ) (hr : ∀ i, 0 < r i)
  (hR : 0 < R)
    (h g : (ι → ℂ) × ℂ → ℂ) (hg : DifferentiableOn ℂ g (polydisc 0 r ×ˢ ball 0 R))
    (hh : DifferentiableOn ℂ h (polydisc 0 r ×ˢ ball 0 R)) (k : ℕ) :
    IsWeierstrassDivisionOn (fun z => z.2 ^ d)
      (g - h * (picardApprox d r R hr hR h g hg hh k).1)
      (picardApprox d r R hr hR h g hg hh (k + 1)).1
      (picardApproxCoeff d r R hr hR h g hg hh k) (polydisc 0 r) R :=
  (coordinatePower_division d hR
    (hg.sub (hh.mul (picardApprox d r R hr hR h g hg hh k).2))).choose_spec.choose_spec.1

/-- The quotient bound of `coordinatePower_division`, specialized to a Picard step. -/
theorem picardApprox_succ_bound (d : ℕ) (r : ι → ℝ) (R : ℝ) (hr : ∀ i, 0 < r i) (hR : 0 < R)
    (h g : (ι → ℂ) × ℂ → ℂ) (hg : DifferentiableOn ℂ g (polydisc 0 r ×ˢ ball 0 R))
    (hh : DifferentiableOn ℂ h (polydisc 0 r ×ˢ ball 0 R)) (k : ℕ) (M : ℝ) (hM0 : 0 ≤ M)
    (hb : ∀ z ∈ polydisc 0 r ×ˢ ball 0 R,
      ‖(g - h * (picardApprox d r R hr hR h g hg hh k).1) z‖ ≤ M) :
    ∀ z ∈ polydisc 0 r ×ˢ ball 0 R,
      ‖(picardApprox d r R hr hR h g hg hh (k + 1)).1 z‖ ≤ ((d + 1 : ℕ) : ℝ) / R ^ d * M :=
  (coordinatePower_division d hR
    (hg.sub (hh.mul (picardApprox d r R hr hR h g hg hh k).2))).choose_spec.choose_spec.2.1 M
    hM0 hb

/-- Uniqueness of `coordinatePower_division`, specialized to a Picard step: any other valid
decomposition of the same numerator agrees with the Picard step's output. -/
theorem picardApprox_succ_unique (d : ℕ) (r : ι → ℝ) (R : ℝ) (hr : ∀ i, 0 < r i) (hR : 0 < R)
    (h g : (ι → ℂ) × ℂ → ℂ) (hg : DifferentiableOn ℂ g (polydisc 0 r ×ˢ ball 0 R))
    (hh : DifferentiableOn ℂ h (polydisc 0 r ×ˢ ball 0 R)) (k : ℕ)
    (q' : (ι → ℂ) × ℂ → ℂ) (a' : Fin d → (ι → ℂ) → ℂ)
    (hdiv' : IsWeierstrassDivisionOn (fun z => z.2 ^ d)
      (g - h * (picardApprox d r R hr hR h g hg hh k).1) q' a' (polydisc 0 r) R) :
    EqOn (picardApprox d r R hr hR h g hg hh (k + 1)).1 q'
        (polydisc 0 r ×ˢ ball 0 R) ∧
      ∀ j, EqOn (picardApproxCoeff d r R hr hR h g hg hh k j) (a' j) (polydisc 0 r) :=
  (coordinatePower_division d hR
    (hg.sub (hh.mul (picardApprox d r R hr hR h g hg hh k).2))).choose_spec.choose_spec.2.2 q' a'
    hdiv'

/-- Iterated derivatives converge along a locally uniform limit of holomorphic one-variable
functions, evaluated at any point of the domain. -/
theorem tendsto_iteratedDeriv_of_tendstoLocallyUniformlyOn {V : Set ℂ} (hV : IsOpen V) (j : ℕ) :
    ∀ (F : ℕ → ℂ → ℂ) (f' : ℂ → ℂ), TendstoLocallyUniformlyOn F f' atTop V →
      (∀ n, DifferentiableOn ℂ (F n) V) → ∀ {x : ℂ}, x ∈ V →
      Tendsto (fun n => iteratedDeriv j (F n) x) atTop (𝓝 (iteratedDeriv j f' x)) := by
  induction j with
  | zero =>
    intro F f' hF _hFa x hx
    simpa [iteratedDeriv_zero] using hF.tendsto_at hx
  | succ j ih =>
    intro F f' hF hFa x hx
    have hderiv : TendstoLocallyUniformlyOn (deriv ∘ F) (deriv f') atTop V :=
      hF.deriv (Filter.Eventually.of_forall hFa) hV
    have hderivDiff : ∀ n, DifferentiableOn ℂ (deriv (F n)) V := fun n =>
      (DifferentiableOn.analyticOnNhd_of_finiteDimensional (hFa n) hV).deriv.differentiableOn
    have := ih (deriv ∘ F) (deriv f') hderiv hderivDiff hx
    simpa [iteratedDeriv_succ', Function.comp_def] using this

/-- **Contraction estimate for the Picard iteration.** Consecutive Picard approximations
of the coordinate-power quotient by `g - h * s_k` differ by a geometrically shrinking
amount, given the numerator bound `M` for `g` and the small-perturbation bound on `h`. -/
theorem picardApprox_diff_bound (d : ℕ) (r : ι → ℝ) (R : ℝ) (hr : ∀ i, 0 < r i) (hR : 0 < R)
    (h g : (ι → ℂ) × ℂ → ℂ) (hg : DifferentiableOn ℂ g (polydisc 0 r ×ˢ ball 0 R))
    (hh : DifferentiableOn ℂ h (polydisc 0 r ×ˢ ball 0 R))
    (M : ℝ) (hM0 : 0 ≤ M) (hgb : ∀ z ∈ polydisc 0 r ×ˢ ball 0 R, ‖g z‖ ≤ M)
    (hhb : ∀ z ∈ polydisc 0 r ×ˢ ball 0 R, ‖h z‖ ≤ R ^ d / (2 * (d + 1))) :
    ∀ k, ∀ z ∈ polydisc 0 r ×ˢ ball 0 R,
      ‖(picardApprox d r R hr hR h g hg hh (k + 1)).1 z -
          (picardApprox d r R hr hR h g hg hh k).1 z‖ ≤
        ((d + 1 : ℕ) : ℝ) / R ^ d * M * (1 / 2) ^ k := by
  intro k
  induction k with
  | zero =>
    intro z hz
    have hb : ∀ z ∈ polydisc 0 r ×ˢ ball 0 R,
        ‖(g - h * (picardApprox d r R hr hR h g hg hh 0).1) z‖ ≤ M := by
      intro z hz
      show ‖g z - h z * (picardApprox d r R hr hR h g hg hh 0).1 z‖ ≤ M
      simpa [picardApprox] using hgb z hz
    have hbnd := picardApprox_succ_bound d r R hr hR h g hg hh 0 M hM0 hb z hz
    simpa [picardApprox] using hbnd
  | succ k ih =>
    intro z hz
    set sk := (picardApprox d r R hr hR h g hg hh k).1 with hskdef
    set sk1 := (picardApprox d r R hr hR h g hg hh (k + 1)).1 with hsk1def
    set sk2 := (picardApprox d r R hr hR h g hg hh (k + 2)).1 with hsk2def
    set ak := picardApproxCoeff d r R hr hR h g hg hh k with hakdef
    set ak1 := picardApproxCoeff d r R hr hR h g hg hh (k + 1) with hak1def
    have hdivk := picardApprox_succ_isWeierstrassDivisionOn d r R hr hR h g hg hh k
    have hdivk1 := picardApprox_succ_isWeierstrassDivisionOn d r R hr hR h g hg hh (k + 1)
    have hQA : IsWeierstrassDivisionOn (fun z => z.2 ^ d) (h * (sk1 - sk))
        (sk1 - sk2) (fun j => ak j - ak1 j) (polydisc 0 r) R := by
      refine ⟨(picardApprox d r R hr hR h g hg hh (k + 1)).2.sub
        (picardApprox d r R hr hR h g hg hh (k + 2)).2,
        fun j => (hdivk.differentiableOn_coeff j).sub (hdivk1.differentiableOn_coeff j), ?_⟩
      intro w hw
      have e1 := hdivk.eq hw
      have e2 := hdivk1.eq hw
      show h w * (sk1 w - sk w) = (sk1 w - sk2 w) * w.2 ^ d +
        weierstrassRemainder (fun j => ak j - ak1 j) w
      rw [← weierstrassRemainder_sub]
      have e1' : g w - h w * sk w = sk1 w * w.2 ^ d + weierstrassRemainder ak w := e1
      have e2' : g w - h w * sk1 w = sk2 w * w.2 ^ d + weierstrassRemainder ak1 w := e2
      have : h w * (sk1 w - sk w) = (sk1 w * w.2 ^ d + weierstrassRemainder ak w) -
          (sk2 w * w.2 ^ d + weierstrassRemainder ak1 w) := by
        rw [← e1', ← e2']; ring
      rw [this]; ring
    obtain ⟨q'', a'', hdiv'', hbound'', huniq''⟩ := coordinatePower_division d hR
      (hh.mul ((picardApprox d r R hr hR h g hg hh (k + 1)).2.sub
        (picardApprox d r R hr hR h g hg hh k).2))
    have hEq := (huniq'' (sk1 - sk2) (fun j => ak j - ak1 j) hQA).1
    have hbndM : ∀ z ∈ polydisc 0 r ×ˢ ball 0 R,
        ‖(h * (sk1 - sk)) z‖ ≤ (R ^ d / (2 * (d + 1))) *
          (((d + 1 : ℕ) : ℝ) / R ^ d * M * (1 / 2) ^ k) := by
      intro z hz
      show ‖h z * (sk1 z - sk z)‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul (hhb z hz) (ih z hz) (norm_nonneg _) (by positivity)
    have hq''bound := hbound'' _ (by positivity) hbndM z hz
    rw [hEq hz] at hq''bound
    have hQval : ‖(sk1 - sk2) z‖ = ‖sk2 z - sk1 z‖ := by
      rw [show (sk1 - sk2) z = sk1 z - sk2 z from rfl, ← norm_neg]
      congr 1; ring
    rw [hQval] at hq''bound
    calc ‖sk2 z - sk1 z‖ ≤ ((d + 1 : ℕ) : ℝ) / R ^ d *
        ((R ^ d / (2 * (d + 1))) * (((d + 1 : ℕ) : ℝ) / R ^ d * M * (1 / 2) ^ k)) := hq''bound
      _ = ((d + 1 : ℕ) : ℝ) / R ^ d * M * (1 / 2) ^ (k + 1) := by
          rw [pow_succ]
          have hRd : R ^ d ≠ 0 := by positivity
          have hd1 : ((d:ℝ) + 1) ≠ 0 := by positivity
          push_cast
          field_simp

/-- **Locally uniform limit of the Picard iteration.** Under the contraction estimate of
`picardApprox_diff_bound`, the Picard approximations converge uniformly on the domain to an
analytic limit, with the geometric tail bound summed over all later steps. -/
theorem exists_tendstoUniformlyOn_picardApprox (d : ℕ) (r : ι → ℝ) (R : ℝ) (hr : ∀ i, 0 < r i)
    (hR : 0 < R) (h g : (ι → ℂ) × ℂ → ℂ) (hg : DifferentiableOn ℂ g (polydisc 0 r ×ˢ ball
      0 R))
    (hh : DifferentiableOn ℂ h (polydisc 0 r ×ˢ ball 0 R))
    (M : ℝ) (hM0 : 0 ≤ M) (hgb : ∀ z ∈ polydisc 0 r ×ˢ ball 0 R, ‖g z‖ ≤ M)
    (hhb : ∀ z ∈ polydisc 0 r ×ˢ ball 0 R, ‖h z‖ ≤ R ^ d / (2 * (d + 1))) :
    ∃ S : (ι → ℂ) × ℂ → ℂ,
      AnalyticOnNhd ℂ S (polydisc 0 r ×ˢ ball 0 R) ∧
      ∀ n, ∀ z ∈ polydisc 0 r ×ˢ ball 0 R,
        ‖(picardApprox d r R hr hR h g hg hh n).1 z - S z‖ ≤
          ((d + 1 : ℕ) : ℝ) / R ^ d * M * (1 / 2) ^ n / (1 - 1 / 2) := by
  set sSeq := fun k => picardApprox d r R hr hR h g hg hh k with hsSeqdef
  set B : ℝ := ((d + 1 : ℕ) : ℝ) / R ^ d * M with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hdiff : ∀ k, ∀ z ∈ polydisc 0 r ×ˢ ball 0 R,
      ‖(sSeq (k + 1)).1 z - (sSeq k).1 z‖ ≤ B * (1 / 2) ^ k :=
    picardApprox_diff_bound d r R hr hR h g hg hh M hM0 hgb hhb
  have hpt : ∀ z ∈ polydisc 0 r ×ˢ ball 0 R, CauchySeq (fun k => (sSeq k).1 z) := by
    intro z hz
    apply cauchySeq_of_le_geometric (r := 1 / 2) (C := B) (by norm_num)
    intro n
    rw [dist_eq_norm, norm_sub_rev]
    exact hdiff n z hz
  have hex : ∀ z : (ι → ℂ) × ℂ, ∃ y : ℂ,
      z ∈ polydisc 0 r ×ˢ ball 0 R → Tendsto (fun k => (sSeq k).1 z) atTop (𝓝 y) := by
    intro z
    by_cases hz : z ∈ polydisc 0 r ×ˢ ball 0 R
    · obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (hpt z hz)
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun hz' => absurd hz' hz⟩
  choose S hStendsto using hex
  have hSbound : ∀ n, ∀ z ∈ polydisc 0 r ×ˢ ball 0 R,
      ‖(sSeq n).1 z - S z‖ ≤ B * (1 / 2) ^ n / (1 - 1 / 2) := by
    intro n z hz
    have h := dist_le_of_le_geometric_of_tendsto (r := 1 / 2) (C := B) (by norm_num)
      (f := fun k => (sSeq k).1 z) (fun k => by
        rw [dist_eq_norm, norm_sub_rev]; exact hdiff k z hz)
      (hStendsto z hz) n
    rwa [dist_eq_norm] at h
  have hTU : TendstoUniformlyOn (fun k z => (sSeq k).1 z) S atTop
      (polydisc 0 r ×ˢ ball 0 R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    rcases eq_or_lt_of_le hB0 with hB0' | hB0'
    · filter_upwards with n z hz
      rw [dist_comm, dist_eq_norm]
      calc ‖(sSeq n).1 z - S z‖ ≤ B * (1 / 2) ^ n / (1 - 1 / 2) := hSbound n z hz
        _ = 0 := by rw [← hB0']; ring
        _ < ε := hε
    · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
        (show (0:ℝ) < ε * (1 - 1/2) / B by positivity) (by norm_num : (1/2:ℝ) < 1)
      filter_upwards [eventually_ge_atTop N] with n hn z hz
      rw [dist_comm, dist_eq_norm]
      calc ‖(sSeq n).1 z - S z‖ ≤ B * (1 / 2) ^ n / (1 - 1 / 2) := hSbound n z hz
        _ ≤ B * (1 / 2) ^ N / (1 - 1 / 2) := by
              have hpow : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ N :=
                pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
              have hmul : B * (1 / 2 : ℝ) ^ n ≤ B * (1 / 2 : ℝ) ^ N :=
                mul_le_mul_of_nonneg_left hpow hB0
              exact div_le_div_of_nonneg_right hmul (by norm_num)
        _ < ε := by
              rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 1 - 1/2), mul_comm]
              exact (lt_div_iff₀ hB0').mp hN
  have hSanalytic : AnalyticOnNhd ℂ S (polydisc 0 r ×ˢ ball 0 R) :=
    TendstoLocallyUniformlyOn.analyticOnNhd_of_finiteDimensional
      hTU.tendstoLocallyUniformlyOn
      (Filter.Eventually.of_forall fun k =>
        (sSeq k).2.analyticOnNhd_of_finiteDimensional (isOpen_polydisc _ _ |>.prod
          isOpen_ball))
      (isOpen_polydisc _ _ |>.prod isOpen_ball)
  exact ⟨S, hSanalytic, hSbound⟩

/-- The geometric error bound for Picard approximations also controls the remainders uniformly on
each scalar slice. -/
private theorem tendstoUniformlyOn_picardRemainder
    (d : ℕ) (r : ι → ℝ) (R : ℝ) (hr : ∀ i, 0 < r i) (hR : 0 < R)
    (h g : (ι → ℂ) × ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (polydisc 0 r ×ˢ ball 0 R))
    (hh : DifferentiableOn ℂ h (polydisc 0 r ×ˢ ball 0 R))
    (hhb : ∀ z ∈ polydisc 0 r ×ˢ ball 0 R, ‖h z‖ ≤ R ^ d / (2 * (d + 1)))
    (M : ℝ) (hM0 : 0 ≤ M) (S : (ι → ℂ) × ℂ → ℂ)
    (hSbound : ∀ k, ∀ z ∈ polydisc 0 r ×ˢ ball 0 R,
      ‖(picardApprox d r R hr hR h g hg hh k).1 z - S z‖ ≤
        ((d + 1 : ℕ) : ℝ) / R ^ d * M * (1 / 2) ^ k / (1 - 1 / 2))
    {w : ι → ℂ} (hw : w ∈ polydisc 0 r) :
    TendstoUniformlyOn
      (fun k ζ => g (w, ζ) - h (w, ζ) * (picardApprox d r R hr hR h g hg hh k).1 (w, ζ) -
        ζ ^ d * (picardApprox d r R hr hR h g hg hh (k + 1)).1 (w, ζ))
      (fun ζ => g (w, ζ) - h (w, ζ) * S (w, ζ) - ζ ^ d * S (w, ζ))
      atTop (ball (0 : ℂ) R) := by
  let sSeq := fun k => picardApprox d r R hr hR h g hg hh k
  let B : ℝ := ((d + 1 : ℕ) : ℝ) / R ^ d * M
  let rFun := fun z => g z - h z * S z - z.2 ^ d * S z
  let Fk := fun k ζ => g (w, ζ) - h (w, ζ) * (sSeq k).1 (w, ζ) -
    ζ ^ d * (sSeq (k + 1)).1 (w, ζ)
  have hFkbound : ∀ k, ∀ ζ' ∈ ball (0 : ℂ) R, ‖Fk k ζ' - rFun (w, ζ')‖ ≤
      (R ^ d / (2 * (d + 1))) * (B * (1 / 2) ^ k / (1 - 1 / 2)) +
        R ^ d * (B * (1 / 2) ^ (k + 1) / (1 - 1 / 2)) := by
    intro k ζ' hζ'
    have hwz' : (w, ζ') ∈ polydisc 0 r ×ˢ ball 0 R := ⟨hw, hζ'⟩
    have hb1 := hSbound k (w, ζ') hwz'
    have hb2 := hSbound (k + 1) (w, ζ') hwz'
    have hζ'le : ‖ζ'‖ ≤ R := (mem_ball_zero_iff.mp hζ').le
    have hhle : ‖h (w, ζ')‖ ≤ R ^ d / (2 * (d + 1)) := hhb (w, ζ') hwz'
    have hdiff_eq : Fk k ζ' - rFun (w, ζ') =
        -(h (w, ζ') * ((sSeq k).1 (w, ζ') - S (w, ζ'))) -
          ζ' ^ d * ((sSeq (k + 1)).1 (w, ζ') - S (w, ζ')) := by
      show (g (w, ζ') - h (w, ζ') * (sSeq k).1 (w, ζ') -
          ζ' ^ d * (sSeq (k + 1)).1 (w, ζ')) -
        (g (w, ζ') - h (w, ζ') * S (w, ζ') - ζ' ^ d * S (w, ζ')) = _
      ring
    rw [hdiff_eq]
    calc ‖-(h (w, ζ') * ((sSeq k).1 (w, ζ') - S (w, ζ'))) -
          ζ' ^ d * ((sSeq (k + 1)).1 (w, ζ') - S (w, ζ'))‖
        = ‖h (w, ζ') * ((sSeq k).1 (w, ζ') - S (w, ζ')) +
            ζ' ^ d * ((sSeq (k + 1)).1 (w, ζ') - S (w, ζ'))‖ := by
          rw [← norm_neg]; congr 1; ring
      _ ≤ ‖h (w, ζ') * ((sSeq k).1 (w, ζ') - S (w, ζ'))‖ +
            ‖ζ' ^ d * ((sSeq (k + 1)).1 (w, ζ') - S (w, ζ'))‖ := norm_add_le _ _
      _ = ‖h (w, ζ')‖ * ‖(sSeq k).1 (w, ζ') - S (w, ζ')‖ +
            ‖ζ'‖ ^ d * ‖(sSeq (k + 1)).1 (w, ζ') - S (w, ζ')‖ := by
          rw [norm_mul, norm_mul, norm_pow]
      _ ≤ (R ^ d / (2 * (d + 1))) * (B * (1 / 2) ^ k / (1 - 1 / 2)) +
            R ^ d * (B * (1 / 2) ^ (k + 1) / (1 - 1 / 2)) := by
          gcongr
  have hFktendsto : Tendsto (fun k => (R ^ d / (2 * (d + 1))) * (B * (1 / 2) ^ k / (1 - 1 / 2)) +
      R ^ d * (B * (1 / 2) ^ (k + 1) / (1 - 1 / 2))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h2 : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) atTop (𝓝 0) :=
      h1.comp (tendsto_add_atTop_nat 1)
    have e1 : Tendsto (fun k => (R ^ d / (2 * (d + 1))) * (B * (1 / 2) ^ k / (1 - 1 / 2)))
        atTop (𝓝 ((R ^ d / (2 * (d + 1))) * (B * 0 / (1 - 1 / 2)))) :=
      ((h1.const_mul B).div_const (1 - 1/2)).const_mul _
    have e2 : Tendsto (fun k => R ^ d * (B * (1 / 2) ^ (k + 1) / (1 - 1 / 2)))
        atTop (𝓝 (R ^ d * (B * 0 / (1 - 1 / 2)))) :=
      ((h2.const_mul B).div_const (1 - 1/2)).const_mul _
    simpa using e1.add e2
  have hFkTU : TendstoUniformlyOn Fk (fun ζ' => rFun (w, ζ')) atTop (ball (0:ℂ) R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have := (Metric.tendsto_atTop.mp hFktendsto) ε hε
    obtain ⟨N, hN⟩ := this
    filter_upwards [eventually_ge_atTop N] with k hk ζ' hζ'
    rw [dist_comm, dist_eq_norm]
    calc ‖Fk k ζ' - rFun (w, ζ')‖ ≤ _ := hFkbound k ζ' hζ'
      _ = ‖(R ^ d / (2 * (d + 1))) * (B * (1 / 2) ^ k / (1 - 1 / 2)) +
            R ^ d * (B * (1 / 2) ^ (k + 1) / (1 - 1 / 2)) - 0‖ := by
          rw [sub_zero]
          rw [Real.norm_of_nonneg (by positivity)]
      _ < ε := hN k hk
  exact hFkTU

/-- A uniform limit of scalar polynomials of degree less than `d` is the polynomial formed from its
first `d` Taylor coefficients. Derivative convergence identifies the coefficients, and the
finite sum then passes to the limit. -/
private theorem eq_taylorPolynomial_of_tendstoUniformlyOn {d : ℕ} {R : ℝ} (hR : 0 < R)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {a : ℕ → Fin d → ℂ}
    (hpoly : ∀ k, EqOn (F k) (fun ζ => ∑ j : Fin d, a k j * ζ ^ (j : ℕ)) (ball 0 R))
    (hlim : TendstoUniformlyOn F f atTop (ball 0 R))
    (hdiff : ∀ k, DifferentiableOn ℂ (F k) (ball 0 R))
    {ζ : ℂ} (hζ : ζ ∈ ball 0 R) :
    f ζ = ∑ j : Fin d, (((j : ℕ).factorial : ℂ)⁻¹ * iteratedDeriv (j : ℕ) f 0) * ζ ^ (j : ℕ) := by
  have hcoeff (j : Fin d) : Tendsto (fun k => a k j) atTop
      (𝓝 (((j : ℕ).factorial : ℂ)⁻¹ * iteratedDeriv (j : ℕ) f 0)) := by
    have hder := tendsto_iteratedDeriv_of_tendstoLocallyUniformlyOn isOpen_ball
      (j : ℕ) F f hlim.tendstoLocallyUniformlyOn hdiff (mem_ball_self hR)
    have heq (k : ℕ) : iteratedDeriv (j : ℕ) (F k) 0 =
        ((j : ℕ).factorial : ℂ) * a k j := by
      rw [(Filter.eventuallyEq_of_mem (ball_mem_nhds 0 hR) (hpoly k)).iteratedDeriv_eq,
        iteratedDeriv_weierstrassRemainder_const, dite_eq_left j.isLt]
    have h := hder.const_mul (((j : ℕ).factorial : ℂ)⁻¹)
    have hfac : ((j : ℕ).factorial : ℂ) ≠ 0 := by exact_mod_cast (j : ℕ).factorial_ne_zero
    simpa only [heq, ← mul_assoc, inv_mul_cancel₀ hfac,
      one_mul] using h
  have hsum := tendsto_finsetSum Finset.univ (fun j _ => (hcoeff j).mul_const (ζ ^ (j : ℕ)))
  have hvalue : Tendsto (fun k => F k ζ) atTop
      (𝓝 (∑ j : Fin d, (((j : ℕ).factorial : ℂ)⁻¹ * iteratedDeriv (j : ℕ) f 0) * ζ ^ (j : ℕ))) :=
    hsum.congr' (.of_forall fun k => (hpoly k hζ).symm)
  exact tendsto_nhds_unique (hlim.tendsto_at hζ) hvalue

/-- **The remainder of a Picard limit is itself a Weierstrass remainder.** Given a bound
on the distance from each Picard approximation to a limit `S` (as produced by
`exists_tendstoUniformlyOn_picardApprox`), the limiting perturbed-division remainder
`g - h * S - ζ ^ d * S` is the Weierstrass remainder of the coefficients obtained by
passing derivatives of the numerator's slices to the limit. No identity theorem is used:
each Taylor coefficient of the remainder is recovered directly as the limit of the
corresponding coefficient of the finite Picard step. -/
theorem exists_weierstrassRemainder_eq_of_tendstoUniformlyOn_picardApprox
    (d : ℕ) (r : ι → ℝ) (R : ℝ) (hr : ∀ i, 0 < r i) (hR : 0 < R) (h g : (ι → ℂ) × ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (polydisc 0 r ×ˢ ball 0 R))
    (hh : DifferentiableOn ℂ h (polydisc 0 r ×ˢ ball 0 R))
    (hhb : ∀ z ∈ polydisc 0 r ×ˢ ball 0 R, ‖h z‖ ≤ R ^ d / (2 * (d + 1)))
    (M : ℝ) (hM0 : 0 ≤ M) (S : (ι → ℂ) × ℂ → ℂ)
    (hSdiff : DifferentiableOn ℂ S (polydisc 0 r ×ˢ ball 0 R))
    (hSbound : ∀ n, ∀ z ∈ polydisc 0 r ×ˢ ball 0 R,
      ‖(picardApprox d r R hr hR h g hg hh n).1 z - S z‖ ≤
        ((d + 1 : ℕ) : ℝ) / R ^ d * M * (1 / 2) ^ n / (1 - 1 / 2)) :
    ∃ a : Fin d → (ι → ℂ) → ℂ, (∀ j, DifferentiableOn ℂ (a j) (polydisc (0 : ι → ℂ) r)) ∧
      ∀ w ∈ polydisc (0 : ι → ℂ) r, ∀ ζ ∈ ball (0 : ℂ) R,
        g (w, ζ) - h (w, ζ) * S (w, ζ) - ζ ^ d * S (w, ζ) = weierstrassRemainder a (w, ζ) := by
  set sSeq := fun k => picardApprox d r R hr hR h g hg hh k with hsSeqdef
  set rFun : (ι → ℂ) × ℂ → ℂ := fun z => g z - h z * S z - z.2 ^ d * S z with hrFundef
  set aOut : Fin d → (ι → ℂ) → ℂ := fun j w =>
    ((j : ℕ).factorial : ℂ)⁻¹ * iteratedDeriv (j : ℕ) (fun ζ => rFun (w, ζ)) 0 with haOutdef
  have hrFunDiffFull : DifferentiableOn ℂ rFun (polydisc 0 r ×ˢ ball 0 R) := by
    have h4 : DifferentiableOn ℂ (fun z : (ι → ℂ) × ℂ => z.2 ^ d)
        (polydisc 0 r ×ˢ ball 0 R) := (differentiableOn_snd).pow d
    exact (hg.sub (hh.mul hSdiff)).sub (h4.mul hSdiff)
  have haDiff : ∀ j, DifferentiableOn ℂ (aOut j) (polydisc (0 : ι → ℂ) r) := fun j =>
    (differentiableOn_iteratedDeriv_snd_slice (isOpen_polydisc _ _)
      hrFunDiffFull hR (j : ℕ)).const_mul _
  refine ⟨aOut, haDiff, fun w hw ζ hζ => ?_⟩
  set Fk : ℕ → ℂ → ℂ := fun k ζ' =>
    g (w, ζ') - h (w, ζ') * (sSeq k).1 (w, ζ') - ζ' ^ d * (sSeq (k + 1)).1 (w, ζ') with hFkdef
  have hFkeq : ∀ k, ∀ ζ' ∈ ball (0 : ℂ) R, Fk k ζ' =
      weierstrassRemainder (picardApproxCoeff d r R hr hR h g hg hh k) (w, ζ') := by
    intro k ζ' hζ'
    have hthis := (picardApprox_succ_isWeierstrassDivisionOn d r R hr hR h g hg hh k).eq
      (⟨hw, hζ'⟩ : (w, ζ') ∈ polydisc 0 r ×ˢ ball 0 R)
    show g (w, ζ') - h (w, ζ') * (sSeq k).1 (w, ζ') - ζ' ^ d * (sSeq (k + 1)).1 (w, ζ') = _
    have hthis' : g (w, ζ') - h (w, ζ') * (sSeq k).1 (w, ζ') =
        (sSeq (k + 1)).1 (w, ζ') * ζ' ^ d +
          weierstrassRemainder (picardApproxCoeff d r R hr hR h g hg hh k) (w, ζ') := hthis
    rw [hthis']; ring
  have hFkTU : TendstoUniformlyOn Fk (fun ζ' => rFun (w, ζ')) atTop (ball (0 : ℂ) R) :=
    tendstoUniformlyOn_picardRemainder d r R hr hR h g hg hh hhb M hM0 S hSbound hw
  have hFkDiff : ∀ k, DifferentiableOn ℂ (Fk k) (ball (0 : ℂ) R) := by
    intro k
    have h1 : DifferentiableOn ℂ (fun ζ' => g (w, ζ')) (ball (0:ℂ) R) :=
      differentiableOn_snd_slice hg hw
    have h2 : DifferentiableOn ℂ (fun ζ' => h (w, ζ')) (ball (0:ℂ) R) :=
      differentiableOn_snd_slice hh hw
    have h3 : DifferentiableOn ℂ (fun ζ' => (sSeq k).1 (w, ζ')) (ball (0:ℂ) R) :=
      differentiableOn_snd_slice (sSeq k).2 hw
    have h4 : DifferentiableOn ℂ (fun ζ' => (sSeq (k+1)).1 (w, ζ')) (ball (0:ℂ) R) :=
      differentiableOn_snd_slice (sSeq (k+1)).2 hw
    exact (h1.sub (h2.mul h3)).sub ((differentiableOn_pow d).mul h4)
  exact eq_taylorPolynomial_of_tendstoUniformlyOn
    (a := fun k j => picardApproxCoeff d r R hr hR h g hg hh k j w)
    hR hFkeq hFkTU hFkDiff hζ

/-- **Direct uniqueness for the perturbed coordinate-power fixed-point equation.**
If `h` is uniformly small relative to `R` on a domain, any two decompositions of the
*same* `g` against the divisor `z ^ d + h`, each individually bounded there, agree. -/
theorem eqOn_of_isWeierstrassDivisionOn_selfPerturbed {d : ℕ} {r : ι → ℝ} {R : ℝ}
    (hR : 0 < R) (h g s s' : (ι → ℂ) × ℂ → ℂ) (a a' : Fin d → (ι → ℂ) → ℂ)
    (hh : DifferentiableOn ℂ h (polydisc 0 r ×ˢ ball 0 R))
    (hhb : ∀ z ∈ polydisc 0 r ×ˢ ball 0 R, ‖h z‖ ≤ R ^ d / (2 * (d + 1)))
    (hdiv : IsWeierstrassDivisionOn (fun z => z.2 ^ d) (g - h * s) s a (polydisc 0 r) R)
    (hdiv' : IsWeierstrassDivisionOn (fun z => z.2 ^ d) (g - h * s') s' a'
      (polydisc 0 r) R)
    (M : ℝ) (hM0 : 0 ≤ M) (hsb : ∀ z ∈ polydisc 0 r ×ˢ ball 0 R, ‖s z - s' z‖ ≤ M) :
    EqOn s s' (polydisc 0 r ×ˢ ball 0 R) ∧ ∀ j, EqOn (a j) (a' j) (polydisc 0 r)
      := by
  suffices hs : EqOn s s' (polydisc 0 r ×ˢ ball 0 R) by
    refine ⟨hs, ?_⟩
    have hdiv2 : IsWeierstrassDivisionOn (fun z => z.2 ^ d) (g - h * s) s' a'
        (polydisc 0 r) R :=
      ⟨hdiv'.differentiableOn_quotient,
        hdiv'.differentiableOn_coeff,
        fun z hz => by
          show (g z - h z * s z) = s' z * z.2 ^ d + weierstrassRemainder a' z
          rw [hs hz]
          exact hdiv'.eq hz⟩
    exact (unique_coordinatePower_division hdiv hdiv2 hR).2
  have hQA : ∀ M' : ℝ, 0 ≤ M' →
      (∀ z ∈ polydisc 0 r ×ˢ ball 0 R, ‖s z - s' z‖ ≤ M') →
      ∀ z ∈ polydisc 0 r ×ˢ ball 0 R, ‖s z - s' z‖ ≤ M' / 2 := by
    intro M' hM'0 hM' z hz
    have hQAdiv : IsWeierstrassDivisionOn (fun z => z.2 ^ d) (h * (s' - s)) (s - s')
        (fun j => a j - a' j) (polydisc 0 r) R := by
      refine ⟨hdiv.differentiableOn_quotient.sub hdiv'.differentiableOn_quotient,
        fun j => (hdiv.differentiableOn_coeff j).sub (hdiv'.differentiableOn_coeff j), ?_⟩
      intro w hw
      have e1 : g w - h w * s w = s w * w.2 ^ d + weierstrassRemainder a w := hdiv.eq hw
      have e2 : g w - h w * s' w = s' w * w.2 ^ d + weierstrassRemainder a' w := hdiv'.eq hw
      show h w * (s' w - s w) = (s w - s' w) * w.2 ^ d + weierstrassRemainder (fun j => a j - a'
        j) w
      rw [← weierstrassRemainder_sub]
      have : h w * (s' w - s w) = (s w * w.2 ^ d + weierstrassRemainder a w) -
          (s' w * w.2 ^ d + weierstrassRemainder a' w) := by rw [← e1, ← e2]; ring
      rw [this]; ring
    have hhdiff : DifferentiableOn ℂ (h * (s' - s)) (polydisc 0 r ×ˢ ball 0 R) :=
      hh.mul (hdiv'.differentiableOn_quotient.sub hdiv.differentiableOn_quotient)
    obtain ⟨q'', a'', hdiv'', hbound'', huniq''⟩ := coordinatePower_division d hR hhdiff
    have hEq := (huniq'' (s - s') (fun j => a j - a' j) hQAdiv).1
    have hb : ∀ z ∈ polydisc 0 r ×ˢ ball 0 R, ‖(h * (s' - s)) z‖ ≤
        (R ^ d / (2 * (d + 1))) * M' := by
      intro z hz
      show ‖h z * (s' z - s z)‖ ≤ _
      rw [norm_mul, ← norm_sub_rev (s z) (s' z)]
      exact mul_le_mul (hhb z hz) (hM' z hz) (norm_nonneg _) (by positivity)
    have hq''bound := hbound'' _ (by positivity) hb z hz
    rw [hEq hz] at hq''bound
    calc ‖s z - s' z‖ = ‖(s - s') z‖ := rfl
      _ ≤ ((d + 1 : ℕ) : ℝ) / R ^ d * ((R ^ d / (2 * (d + 1))) * M') := hq''bound
      _ = M' / 2 := by
          have hRd : R ^ d ≠ 0 := by positivity
          have hd1 : ((d : ℝ) + 1) ≠ 0 := by positivity
          push_cast
          field_simp
  have hind : ∀ n, ∀ z ∈ polydisc 0 r ×ˢ ball 0 R, ‖s z - s' z‖ ≤ M * (1 / 2) ^ n := by
    intro n
    induction n with
    | zero => simpa using hsb
    | succ n ih =>
      intro z hz
      have := hQA (M * (1/2)^n) (by positivity) ih z hz
      calc ‖s z - s' z‖ ≤ M * (1/2)^n / 2 := this
        _ = M * (1/2)^(n+1) := by ring
  intro z hz
  have htendsto : Tendsto (fun n => M * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2:ℝ)) (by norm_num) (by norm_num)
    simpa using this.const_mul M
  have hle : ‖s z - s' z‖ ≤ 0 :=
    ge_of_tendsto htendsto (Filter.Eventually.of_forall fun n => hind n z hz)
  have := norm_nonneg (s z - s' z)
  have heq0 : ‖s z - s' z‖ = 0 := le_antisymm hle this
  exact sub_eq_zero.mp (norm_eq_zero.mp heq0)

end SeveralComplexVariables.WeierstrassDivision

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/

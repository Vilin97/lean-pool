/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.CanonicalForms
import LeanPool.JacobianDiffgeo.ProjectiveLine.Charts
import LeanPool.JacobianDiffgeo.ResidueCalculus.PrincipalPart
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# residue-theorem: the `ℙ¹` base case — atoms (file 1/1, PARTIAL DELIVERY)

Unit: residue-theorem (`docs/design/residue-theorem.md` §6, `docs/design/form-trace-tower.md`
§RationalOnP1). Target headline: `∑ᶠ p, θ.resAt p = 0` for `θ : MForm (OnePoint ℂ)`, as the
genus-0 base case feeding the general-`X` reduction via a nonconstant map to `ℙ¹` (design §6).

**Status: the headline theorem is NOT proved here — read this note before building on this
file.** What follows is a complete (no open goals anywhere), independently useful collection of
atoms toward
it, plus an honest account of the one remaining gap and how to close it. See `Jacobian/
ResidueTheorem.lean` (unit root) for the full write-up of what is/isn't delivered and why.

## What IS built, zero sorries

* `RS.P1.formOfCoeFn`: packages an arbitrary meromorphic "coefficient in the finite chart"
  function `R : ℂ → ℂ` into a genuine `MFormData (OnePoint ℂ)`, given that its
  `invChart`-transported
  reading `fun w => -(w²)⁻¹ * R w⁻¹` is *also* meromorphic. The two-chart `compat` check reduces to
  "apply the transition rule twice returns to the start", independent of what `R` is.
* `RS.P1.coeffAt_coe_eq_coeffAt_coe`: any `MFormData (OnePoint ℂ)`'s finite-chart coefficient is
  the *same raw function* at every finite basepoint (all of `ℙ¹`'s finite points share `coeChart`).
* **The Liouville-free residue-at-infinity fact** (`RS.P1.circleIntegral_inv_eq_neg` +
  `RS.P1.resAt_neg_sq_inv_mul_comp_inv_eq_zero`): for `R_mid` differentiable on all of `ℂ`, the
  residue "at infinity" of its `invChart` reading vanishes — via Cauchy's theorem (an entire
  function's circle integral is `0` at every radius) transported through the `z ↦ z⁻¹` reindexing
  of the contour, NOT a polynomial-growth/degree argument. This is the "Liouville" ingredient the
  task brief anticipated, done more cheaply than the growth-bound route the non-quotient
  `form-trace-tower` design had budgeted for.
* `RS.P1.meromorphicAt_neg_sq_inv_mul_sub_inv_zpow` / `RS.P1.resAt_neg_sq_inv_mul_sub_inv_zpow`:
  the "companion pole at `∞`" bookkeeping for a single principal-part monomial `(w⁻¹ - a) ^ k`
  (`k < 0`) — meromorphic at `0`, with residue `-1` for the simple pole `k = -1` (Miranda's
  "`dz/(z-a)` has residues `1` at `a` and `-1` at `∞`") and `0` otherwise.

## What is NOT built: the assembly, and why (read before attempting it)

The intended proof: extract `θ`'s finite-chart coefficient `R`, subtract the finite sum of its
principal parts at its finitely many finite poles (`RS.principalPartAt`, already built) to get a
remainder `R_mid`, apply the Liouville-free fact above to conclude the remainder's residue at `∞`
vanishes, then telescope (the tail's own residue at `∞` is exactly minus the sum of residues it
reproduces at the finite poles it was built to match, by `resAt_neg_sq_inv_mul_sub_inv_zpow`).

**The blocker, found late and not resolved in the time available**:
`resAt_neg_sq_inv_mul_comp_inv_eq_zero`
needs `R_mid` genuinely `Differentiable ℂ` — but `R_mid := R - R_tail` is built from `MeromorphicAt`
data, whose junk convention at a pole/removable point does **not** force the value there to match
the analytic-repair limit (`MeromorphicAt f x` with witness order `n > 0` puts no constraint on
`f x` at all, since it is multiplied by `(x - x) ^ n = 0`). So `R_mid`, built by bare pointwise
subtraction, may fail to be *continuous* at the finitely many points of `θ`'s pole set even though
its *order* is `≥ 0` there (checked and proved separately, via `MeromorphicAt.orderAt_sub_
principalPartAt_nonneg` + a `Finset.analyticAt_fun_sum` argument — that part of the assembly DID
work, it is only the final "hence `Differentiable ℂ`, hence apply the Liouville-free fact" step
that does not follow as stated). Two fixes, either workable, neither attempted:
(a) weaken `resAt_neg_sq_inv_mul_comp_inv_eq_zero` to take an explicit radius `R₀` with
`R_mid` differentiable only on `closedBall 0 R₀ \ {0}` for `R₀` small enough to exclude the
(finite) pole set — the circle-integral argument only ever needs one such disk, and `resAt` at `0`
doesn't care which; or (b) repair `R_mid` first (canonical-forms' `MeroGermOn.holoRepr`-style
construction, already used elsewhere in this project, e.g. `MForm.d`) to an honestly continuous
representative before invoking Cauchy's theorem. Route (a) is probably the smaller patch — the
`Set.Finite`/`Metric` "there is a positive radius smaller than the nearest nonzero pole" lemma is
routine, and every other piece of the assembly (the finite-pole-sum construction, the order-≥0
argument, the `θ.coeffAt ∞` transition formula, the finite pole set extraction from `θ.divisor`)
was fully worked out and test-compiled during this build and is recorded in this design's build
notes for the next attempt; none of it is included here as code because it was written against the
now-known-insufficient `Differentiable ℂ R_mid` hypothesis and would need re-threading through
whichever fix is chosen.
-/

open scoped ContDiff Manifold OnePoint
open Set Filter Topology OnePoint Real Complex MeasureTheory

noncomputable section

namespace RS.P1

/-- `chartAt`'s target is `univ` at every point of `ℙ¹` (both charts have target `univ`). -/
theorem chartAt_target_eq_univ (x : OnePoint ℂ) : (chartAt ℂ x).target = Set.univ := by
  induction x using OnePoint.rec with
  | infty => rw [chartAt_infty, invChart_target]
  | coe z => rw [chartAt_coe, coeChart_target]

/-- The chart-coefficient family assembled from a "finite-chart" function `R`, forced to be a
genuine `MFormData (OnePoint ℂ)` by requiring its `invChart` reading (the transition-rule image)
to also be meromorphic. The two-chart `compat` check is a single "apply the transition rule twice
returns to the start" computation, independent of what `R` is. -/
def formOfCoeFn (R : ℂ → ℂ) (hR : MeromorphicOn R Set.univ)
    (hR' : MeromorphicOn (fun w => -(w ^ 2)⁻¹ * R w⁻¹) Set.univ) :
    RS.MFormData (OnePoint ℂ) where
  coeffAt x z := x.elim (-(z ^ 2)⁻¹ * R z⁻¹) (fun _ => R z)
  coeffAt_zero_off x z hz := absurd (chartAt_target_eq_univ x ▸ Set.mem_univ z) hz
  meromorphicOn_coeffAt x := by
    rw [chartAt_target_eq_univ x]
    induction x using OnePoint.rec with
    | infty =>
      have heq : (fun z => (∞ : OnePoint ℂ).elim (-(z ^ 2)⁻¹ * R z⁻¹) (fun _ => R z))
          = fun z => -(z ^ 2)⁻¹ * R z⁻¹ := by funext z; rfl
      rw [heq]; exact hR'
    | coe p =>
      have heq : (fun z => ((p : OnePoint ℂ)).elim (-(z ^ 2)⁻¹ * R z⁻¹) (fun _ => R z))
          = fun z => R z := by funext z; rfl
      rw [heq]; exact hR
  compat x y z hz := by
    induction x using OnePoint.rec with
    | infty => induction y using OnePoint.rec with
      | infty =>
        rw [chartAt_infty] at hz ⊢
        simp only [OnePoint.elim_infty]
        have hval : invChart (invChart.symm z) = z := invChart.right_inv (Set.mem_univ z)
        have heq : (⇑invChart ∘ ⇑invChart.symm : ℂ → ℂ) = id := by
          funext w; exact invChart.right_inv (Set.mem_univ w)
        rw [hval, heq, deriv_id, one_mul]
      | coe q =>
        rw [chartAt_infty, chartAt_coe] at hz ⊢
        have hzne : z ≠ 0 := by
          obtain ⟨p, hp, rfl⟩ := hz
          have hpne : p ≠ (∞ : OnePoint ℂ) := by
            have := hp.2; rwa [coeChart_source, Set.mem_compl_iff, Set.mem_singleton_iff] at this
          obtain ⟨v, rfl⟩ := ne_infty_iff_exists.mp hpne
          have := hp.1
          rw [invChart_source, Set.mem_compl_iff, Set.mem_singleton_iff, coe_eq_coe] at this
          rwa [coeChart_apply_coe]
        simp only [OnePoint.elim, Option.elim]
        rw [show (⇑invChart (⇑coeChart.symm z) : ℂ) = z⁻¹ by
          rw [coeChart_symm_apply, invChart_apply_coe]]
        have hcomp : (⇑invChart ∘ ⇑coeChart.symm : ℂ → ℂ) = Inv.inv := by
          funext w
          change invChart (coeChart.symm w) = w⁻¹
          rw [coeChart_symm_apply, invChart_apply_coe]
        rw [hcomp, deriv_inv, inv_inv]
        have h1 : ((z⁻¹) ^ 2)⁻¹ = z ^ 2 := by field_simp
        rw [h1]; field_simp
    | coe p => induction y using OnePoint.rec with
      | infty =>
        rw [chartAt_infty, chartAt_coe] at hz ⊢
        have hzne : z ≠ 0 := by
          obtain ⟨q, hq, rfl⟩ := hz
          have hqne : q ≠ ((0:ℂ) : OnePoint ℂ) := by
            have := hq.2
            rwa [invChart_source, Set.mem_compl_iff, Set.mem_singleton_iff] at this
          have hqne' : q ≠ (∞ : OnePoint ℂ) := by
            have := hq.1
            rw [coeChart_source, Set.mem_compl_iff, Set.mem_singleton_iff] at this
            exact this
          obtain ⟨v, rfl⟩ := ne_infty_iff_exists.mp hqne'
          have hvne : v ≠ 0 := fun hcon => hqne (by rw [hcon])
          rw [invChart_apply_coe]
          exact inv_ne_zero hvne
        simp only [OnePoint.elim, Option.elim]
        rw [show (⇑coeChart (⇑invChart.symm z) : ℂ) = z⁻¹ by
          rw [invChart_symm_apply, coeChart_inversion_coe]]
        have hcomp : (⇑coeChart ∘ ⇑invChart.symm : ℂ → ℂ) = Inv.inv := by
          funext w
          change coeChart (invChart.symm w) = w⁻¹
          rw [invChart_symm_apply]
          by_cases hw : w = 0
          · subst hw; simp
          · rw [inversion_coe hw, coeChart_apply_coe]
        rw [hcomp, deriv_inv]
      | coe q =>
        simp only [chartAt_coe] at hz ⊢
        simp only [OnePoint.elim]
        have hval : coeChart (coeChart.symm z) = z := coeChart.right_inv (Set.mem_univ z)
        have heq : (⇑coeChart ∘ ⇑coeChart.symm : ℂ → ℂ) = id := by
          funext w; exact coeChart.right_inv (Set.mem_univ w)
        rw [hval, heq, deriv_id, one_mul]
        rfl

/-- The `coeChart` reading of an `MFormData (OnePoint ℂ)` is the same function for every finite
basepoint (`ℙ¹`'s finite points all share the identical `coeChart`, and `compat` with the
identity transition forces literal equality of the raw functions, not just a germ agreement). -/
theorem coeffAt_coe_eq_coeffAt_coe (θ : RS.MFormData (OnePoint ℂ)) (a b : ℂ) :
    θ.coeffAt ((a : ℂ) : OnePoint ℂ) = θ.coeffAt ((b : ℂ) : OnePoint ℂ) := by
  funext z
  have hz : z ∈ ⇑(chartAt ℂ ((b : ℂ) : OnePoint ℂ)) ''
      ((chartAt ℂ ((a : ℂ) : OnePoint ℂ)).source ∩ (chartAt ℂ ((b : ℂ) : OnePoint ℂ)).source) := by
    rw [chartAt_coe, chartAt_coe]
    exact ⟨coeChart.symm z,
      ⟨coeChart.map_target (Set.mem_univ z), coeChart.map_target (Set.mem_univ z)⟩,
      coeChart.right_inv (Set.mem_univ z)⟩
  have hc := θ.compat ((a : ℂ) : OnePoint ℂ) ((b : ℂ) : OnePoint ℂ) z hz
  rw [chartAt_coe, chartAt_coe] at hc
  rw [hc]
  have hderiv1 : deriv (⇑coeChart ∘ ⇑coeChart.symm) z = 1 := by
    have heq : (⇑coeChart ∘ ⇑coeChart.symm : ℂ → ℂ) = id := by
      funext w; exact coeChart.right_inv (Set.mem_univ w)
    rw [heq, deriv_id]
  rw [hderiv1, one_mul, coeChart.right_inv (Set.mem_univ z)]

/-! ### The Liouville-free "residue at infinity of an entire function vanishes" fact -/

/-- Circle integral under `z ↦ z⁻¹` reindexing: reading the same integrand through the inversion
at reciprocal radius reverses orientation (a `-1` sign), the classical "residue at infinity"
substitution, via `circleMap_zero_inv` + a period-shift of the parametrizing integral. -/
theorem circleIntegral_inv_eq_neg (R_mid : ℂ → ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∮ w in C(0, ρ), -(w ^ 2)⁻¹ * R_mid w⁻¹) = -(∮ z in C(0, ρ⁻¹), R_mid z) := by
  have hρne : ρ ≠ 0 := hρ.ne'
  have hshift : (∫ x : ℝ in (0:ℝ)..2 * π,
        deriv (circleMap 0 ρ⁻¹) (-x) • R_mid (circleMap 0 ρ⁻¹ (-x)))
      = ∫ θ : ℝ in (0:ℝ)..2 * π, deriv (circleMap 0 ρ⁻¹) θ • R_mid (circleMap 0 ρ⁻¹ θ) := by
    rw [intervalIntegral.integral_comp_neg
      (fun θ => deriv (circleMap 0 ρ⁻¹) θ • R_mid (circleMap 0 ρ⁻¹ θ))]
    have hper : Function.Periodic
        (fun θ : ℝ => deriv (circleMap 0 ρ⁻¹) θ • R_mid (circleMap 0 ρ⁻¹ θ)) (2 * π) := by
      intro θ
      simp only [deriv_circleMap]
      rw [periodic_circleMap 0 ρ⁻¹ θ]
    simpa using hper.intervalIntegral_add_eq (-(2 * π)) 0
  change (∫ θ : ℝ in (0:ℝ)..2 * π,
      deriv (circleMap 0 ρ) θ • (-(circleMap 0 ρ θ ^ 2)⁻¹ * R_mid (circleMap 0 ρ θ)⁻¹))
    = -(∫ θ : ℝ in (0:ℝ)..2 * π, deriv (circleMap 0 ρ⁻¹) θ • R_mid (circleMap 0 ρ⁻¹ θ))
  rw [← hshift]
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [smul_eq_mul, deriv_circleMap]
  rw [circleMap_zero_inv]
  have hcnz : circleMap 0 ρ θ ≠ 0 := circleMap_ne_center hρne
  rw [show circleMap 0 ρ θ * I * (-(circleMap 0 ρ θ ^ 2)⁻¹ * R_mid (circleMap 0 ρ⁻¹ (-θ)))
      = -(circleMap 0 ρ⁻¹ (-θ) * I) * R_mid (circleMap 0 ρ⁻¹ (-θ)) by
    rw [← circleMap_zero_inv]; field_simp]
  ring

/-- **The Liouville-free key fact.** The residue "at infinity" (i.e. the residue at `0` of the
`invChart`-transported reading `-(w²)⁻¹ R_mid w⁻¹`) of an ENTIRE `R_mid` always vanishes: Cauchy's
theorem gives `R_mid`'s own circle integral `0` at every radius, and `circleIntegral_inv_eq_neg`
transports this to the transported reading's circle integral at every (reciprocal) radius, hence
its residue is `0`. No polynomial-growth/degree bookkeeping needed anywhere. -/
theorem resAt_neg_sq_inv_mul_comp_inv_eq_zero {R_mid : ℂ → ℂ} (hdiff : Differentiable ℂ R_mid)
    (hg : MeromorphicAt (fun w => -(w ^ 2)⁻¹ * R_mid w⁻¹) 0) :
    RS.resAt (fun w => -(w ^ 2)⁻¹ * R_mid w⁻¹) 0 = 0 := by
  set g : ℂ → ℂ := fun w => -(w ^ 2)⁻¹ * R_mid w⁻¹ with hg_def
  have hgdiff : ∀ w : ℂ, w ∈ Metric.closedBall (0:ℂ) 1 \ {0} → DifferentiableAt ℂ g w := by
    rintro w ⟨-, hw0⟩
    have hwne : w ≠ 0 := hw0
    have h1 : DifferentiableAt ℂ (fun v : ℂ => v⁻¹) w := differentiableAt_inv hwne
    have h2 : DifferentiableAt ℂ (fun v : ℂ => R_mid v⁻¹) w := (hdiff (w⁻¹)).comp w h1
    have h3 : DifferentiableAt ℂ (fun v : ℂ => -(v ^ 2)⁻¹) w := by
      have hp : DifferentiableAt ℂ (fun v : ℂ => v ^ 2) w := by fun_prop
      exact (hp.inv (pow_ne_zero 2 hwne)).neg
    exact h3.mul h2
  have hkey := RS.circleIntegral_eq_two_pi_I_mul_resAt (f := g) (z₀ := 0) one_pos hg hgdiff
  have hzero : (∮ w in C(0, (1:ℝ)), g w) = 0 := by
    rw [hg_def, circleIntegral_inv_eq_neg R_mid one_pos]
    have hRanalytic : AnalyticAt ℂ R_mid 0 := hdiff.analyticAt 0
    have hRres : RS.resAt R_mid 0 = 0 := RS.resAt_of_analyticAt hRanalytic
    have hRint := RS.circleIntegral_eq_two_pi_I_mul_resAt (f := R_mid) (z₀ := 0)
      (show (0:ℝ) < 1⁻¹ by norm_num) hRanalytic.meromorphicAt
      (fun z _ => hdiff z)
    rw [hRres, mul_zero] at hRint
    rw [hRint]
    ring
  rw [hzero] at hkey
  have h2pi : (2 * (π : ℂ) * I) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  exact (mul_eq_zero.mp hkey.symm).resolve_left h2pi

/-! ### The finite-pole/`z⁻¹` compatibility of `principalPartAt`'s monomials -/

/-- Each monomial `(w⁻¹ - a) ^ k` composed with the inversion, weighted by the `dz ↦ dw` factor
`-(w²)⁻¹`, is meromorphic at `0` (the "companion pole at `∞`" bookkeeping): the closed form
`-(1 - a w) ^ k * w ^ (-k - 2)` shows it directly, for any `a : ℂ`, `k : ℤ`. -/
theorem meromorphicAt_neg_sq_inv_mul_sub_inv_zpow (a : ℂ) (k : ℤ) :
    MeromorphicAt (fun w => -(w ^ 2)⁻¹ * (w⁻¹ - a) ^ k) (0:ℂ) := by
  have hrhs : MeromorphicAt (fun w : ℂ => -((1 - a * w) ^ k * w ^ (-k - 2))) (0:ℂ) := by
    apply MeromorphicAt.neg
    apply MeromorphicAt.mul
    · exact (((MeromorphicAt.const (1:ℂ) 0).sub ((MeromorphicAt.const a 0).mul
        (MeromorphicAt.id 0)))).zpow k
    · exact (MeromorphicAt.id (0:ℂ)).zpow (-k-2)
  have hcongr : (fun w : ℂ => -((1 - a * w) ^ k * w ^ (-k - 2)))
      =ᶠ[𝓝[≠] (0:ℂ)] fun w => -(w ^ 2)⁻¹ * (w⁻¹ - a) ^ k := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hwne : w ≠ 0 := hw
    have hz1 : (w⁻¹ - a) = (1 - a * w) * w⁻¹ := by field_simp
    change (-((1 - a * w) ^ k * w ^ (-k - 2)) : ℂ) = -(w ^ 2)⁻¹ * (w⁻¹ - a) ^ k
    rw [hz1, mul_zpow]
    have h1 : (w ^ 2)⁻¹ = w ^ (-2 : ℤ) := by rw [zpow_neg]; norm_num; try rfl
    have h2 : (w⁻¹ : ℂ) ^ k = w ^ (-k) := by rw [← zpow_neg_one, ← zpow_mul, neg_one_mul]
    rw [h1, h2]
    rw [show (-(w ^ (-2:ℤ)) * ((1 - a*w)^k * w ^ (-k)) : ℂ)
        = -((1-a*w)^k * (w ^ (-2:ℤ) * w ^ (-k))) by ring]
    rw [← zpow_add₀ hwne]
    congr 3
    ring
  exact hrhs.congr hcongr

/-- The residue at `0` of the transported monomial `-(w²)⁻¹ (w⁻¹ - a) ^ k`, for `k < 0` (the only
exponents `RS.principalPartAt` ever produces): `-1` for the simple pole `k = -1` (the "companion
at `∞`"), `0` otherwise — the elementary case split. -/
theorem resAt_neg_sq_inv_mul_sub_inv_zpow (a : ℂ) {k : ℤ} (hk : k < 0) :
    RS.resAt (fun w => -(w ^ 2)⁻¹ * (w⁻¹ - a) ^ k) 0 = if k = -1 then -1 else 0 := by
  have hcongr : (fun w : ℂ => -(w ^ 2)⁻¹ * (w⁻¹ - a) ^ k)
      =ᶠ[𝓝[≠] (0:ℂ)] fun w => -((1 - a * w) ^ k * w ^ (-k - 2)) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hwne : w ≠ 0 := hw
    have hz1 : (w⁻¹ - a) = (1 - a * w) * w⁻¹ := by field_simp
    change (-(w ^ 2)⁻¹ * (w⁻¹ - a) ^ k : ℂ) = -((1 - a * w) ^ k * w ^ (-k - 2))
    rw [hz1, mul_zpow]
    have h1 : (w ^ 2)⁻¹ = w ^ (-2 : ℤ) := by rw [zpow_neg]; norm_num; try rfl
    have h2 : (w⁻¹ : ℂ) ^ k = w ^ (-k) := by rw [← zpow_neg_one, ← zpow_mul, neg_one_mul]
    rw [h1, h2]
    rw [show (-(w ^ (-2:ℤ)) * ((1 - a*w)^k * w ^ (-k)) : ℂ)
        = -((1-a*w)^k * (w ^ (-2:ℤ) * w ^ (-k))) by ring]
    rw [← zpow_add₀ hwne]
    congr 3
    ring
  rw [RS.resAt_congr hcongr, RS.resAt_neg]
  have hganalytic : AnalyticAt ℂ (fun w : ℂ => (1 - a * w) ^ k) 0 := by
    have hbase : AnalyticAt ℂ (fun w : ℂ => 1 - a * w) 0 := by fun_prop
    have hbase0 : (1 - a * (0:ℂ)) ≠ 0 := by simp
    exact hbase.zpow hbase0
  have hval : (fun w : ℂ => (1 - a * w) ^ k) 0 = 1 := by simp
  have hcomm : (fun w : ℂ => (1 - a * w) ^ k * w ^ (-k - 2))
      = fun w : ℂ => (w - 0) ^ (-k - 2) * (1 - a * w) ^ k := by
    funext w; rw [sub_zero]; ring
  rw [hcomm, RS.resAt_zpow_mul hganalytic.meromorphicAt (-k - 2)]
  rw [RS.laurentCoeffAt_of_analyticAt hganalytic]
  by_cases hkm1 : k = -1
  · subst hkm1
    rw [show ((-1:ℤ)-(-(-1:ℤ)-2)) = (0:ℤ) by ring, if_pos (le_refl (0:ℤ))]
    simp [RS.taylorCoeffAt_zero_apply]
  · have hneg : ¬ (0 : ℤ) ≤ -1 - (-k - 2) := by omega
    rw [if_neg hneg, if_neg hkm1, neg_zero]

end RS.P1

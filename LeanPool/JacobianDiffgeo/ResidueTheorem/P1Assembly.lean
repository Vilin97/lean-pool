/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.ResidueTheorem.RationalOnP1
import LeanPool.JacobianDiffgeo.ResidueTheorem.MFormCompat
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# residue-theorem: the `ℙ¹` base case, assembled

Unit: residue-theorem (`docs/design/residue-theorem.md` §6). This file closes Gap 1 of the
previous partial delivery (see `RationalOnP1.lean`'s module docstring): the headline

* `RS.P1.sum_resAt_eq_zero : ∑ᶠ y, Θ.resAt y = 0` for every `Θ : MForm (OnePoint ℂ)`.

The junk-value blocker documented in `RationalOnP1.lean` ("the remainder `R_mid`, built by bare
pointwise subtraction of `MeromorphicAt`-junk-valued functions, has order `≥ 0` at the former
poles but need not be continuous there") is repaired via mathlib's meromorphic **normal form**
machinery rather than a weakened contour radius:

* `RS.P1.exists_differentiable_of_ord_nonneg` — a planar function meromorphic on all of `ℂ`
  with everywhere-nonnegative order admits an ENTIRE representative agreeing with it at every
  point where it is honestly analytic (`toMeromorphicNFOn`, which only changes values on the
  non-normal-form set).

The proof of the headline follows the design: subtract the finite principal-part tail at the
(finitely many, via the divisor) finite poles, repair the remainder to an entire `Rf`, kill the
remainder's residue at `∞` by the Liouville-free contour fact
(`resAt_neg_sq_inv_mul_comp_inv_eq_zero`), and compute the tail's companion residue at `∞` as
`-∑ (finite residues)` by the monomial computation (`resAt_neg_sq_inv_mul_sub_inv_zpow`). The
key honesty input making the `∞`-chart congruences legitimate for a RAW representative is
`coeffAt_infty_eq` (the two-chart `compat` identity, valid POINTWISE on `ℂ \ {0}`), which also
forces `R` to be honestly analytic near `∞`.
-/

open scoped ContDiff Manifold OnePoint
open Set Filter Topology OnePoint Real Complex MeasureTheory

noncomputable section

namespace RS.P1

/-! ### The normal-form repair -/

/-- **Repair lemma**: a function meromorphic on all of `ℂ` with everywhere-nonnegative order
admits an entire representative that agrees with it wherever it is honestly analytic (and in
particular on a punctured neighborhood of every point). -/
theorem exists_differentiable_of_ord_nonneg {g : ℂ → ℂ}
    (hg : MeromorphicOn g Set.univ) (hord : ∀ z : ℂ, 0 ≤ meromorphicOrderAt g z) :
    ∃ gf : ℂ → ℂ, Differentiable ℂ gf ∧ (∀ z : ℂ, AnalyticAt ℂ g z → gf z = g z) ∧
      ∀ z : ℂ, gf =ᶠ[𝓝[≠] z] g := by
  refine ⟨toMeromorphicNFOn g Set.univ, ?_, ?_, ?_⟩
  · intro z
    have hNF : MeromorphicNFAt (toMeromorphicNFOn g Set.univ) z :=
      meromorphicNFOn_toMeromorphicNFOn g Set.univ (Set.mem_univ z)
    have hordz : 0 ≤ meromorphicOrderAt (toMeromorphicNFOn g Set.univ) z := by
      rw [meromorphicOrderAt_toMeromorphicNFOn hg (Set.mem_univ z)]
      exact hord z
    exact (hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 hordz).differentiableAt
  · intro z hz
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hg (Set.mem_univ z),
      toMeromorphicNFAt_eq_self.2 hz.meromorphicNFAt]
  · intro z
    exact hg.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)

/-! ### The two-chart compatibility identity, pointwise -/

/-- The `∞`-chart coefficient of any raw 1-form on `ℙ¹` is the transition-rule image of the
shared finite-chart coefficient — POINTWISE on `ℂ \ {0}` (this is `compat` itself, not a germ
statement, so it survives junk values). -/
theorem coeffAt_infty_eq (θ : RS.MFormData (OnePoint ℂ)) {z : ℂ} (hz : z ≠ 0) :
    θ.coeffAt (∞ : OnePoint ℂ) z
      = -(z ^ 2)⁻¹ * θ.coeffAt (((0 : ℂ) : OnePoint ℂ)) z⁻¹ := by
  have hmem : z ∈ ⇑(chartAt ℂ (∞ : OnePoint ℂ)) ''
      ((chartAt ℂ (((0 : ℂ) : OnePoint ℂ))).source ∩ (chartAt ℂ (∞ : OnePoint ℂ)).source) := by
    rw [chartAt_infty, chartAt_coe]
    refine ⟨((z⁻¹ : ℂ) : OnePoint ℂ), ⟨?_, ?_⟩, ?_⟩
    · rw [coeChart_source]
      exact fun hcon => (OnePoint.coe_ne_infty (z⁻¹ : ℂ)) hcon
    · rw [invChart_source]
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, OnePoint.coe_eq_coe]
      exact inv_ne_zero hz
    · rw [invChart_apply_coe, inv_inv]
  have hc := θ.compat (((0 : ℂ) : OnePoint ℂ)) (∞ : OnePoint ℂ) z hmem
  rw [chartAt_infty, chartAt_coe] at hc
  have hcomp : (⇑coeChart ∘ ⇑invChart.symm : ℂ → ℂ) = Inv.inv := by
    funext w
    change coeChart (invChart.symm w) = w⁻¹
    rw [invChart_symm_apply, coeChart_inversion_coe]
  have hval : coeChart (invChart.symm z) = z⁻¹ := by
    rw [invChart_symm_apply, coeChart_inversion_coe]
  rw [hval, hcomp, deriv_inv] at hc
  exact hc

/-! ### THE `ℙ¹` base case -/

/-- After subtracting the principal parts at every pole, the remainder is holomorphic everywhere.
Split out of `sum_resAt_eq_zero` for the 200-line proof size we hold ourselves to; `tail`/`Rmid`
are rebuilt here so the body reads as it did inline. -/
private theorem meromorphicOrderAt_sub_tail_nonneg {R : ℂ → ℂ} (hR : MeromorphicOn R Set.univ)
    (P : Finset ℂ) (hmemP : ∀ a : ℂ, a ∈ P ↔ meromorphicOrderAt R a < 0)
    (htail_anal : ∀ v : ℂ, (∀ a ∈ P, v ≠ a) →
      AnalyticAt ℂ (fun v => ∑ a ∈ P, RS.principalPartAt R a v) v) :
    ∀ v : ℂ, 0 ≤ meromorphicOrderAt (fun v => R v - ∑ a ∈ P, RS.principalPartAt R a v) v := by
  set tail : ℂ → ℂ := fun v => ∑ a ∈ P, RS.principalPartAt R a v with htail_def
  set Rmid : ℂ → ℂ := fun v => R v - tail v with hRmid_def
  change ∀ v : ℂ, 0 ≤ meromorphicOrderAt Rmid v
  intro v
  by_cases hvP : v ∈ P
  · set f₁ : ℂ → ℂ := fun u => R u - RS.principalPartAt R v u with hf₁_def
    set f₂ : ℂ → ℂ := fun u => -(∑ a ∈ P.erase v, RS.principalPartAt R a u) with hf₂_def
    have hsplit : Rmid = f₁ + f₂ := by
      funext u
      change R u - tail u = f₁ u + f₂ u
      rw [hf₁_def, hf₂_def, htail_def]
      simp only
      rw [← Finset.add_sum_erase P (fun a => RS.principalPartAt R a u) hvP]
      ring
    have hf₁m : MeromorphicAt f₁ v :=
      (hR v (Set.mem_univ v)).sub RS.meromorphicAt_principalPartAt
    have hf₂anal : AnalyticAt ℂ (fun u => ∑ a ∈ P.erase v, RS.principalPartAt R a u) v := by
      apply Finset.analyticAt_fun_sum
      intro a ha
      have hne : v ≠ a := fun hcon => (Finset.ne_of_mem_erase ha) (hcon ▸ rfl)
      exact RS.analyticOnNhd_principalPartAt v hne
    have hf₂m : MeromorphicAt f₂ v := hf₂anal.neg.meromorphicAt
    have h1 : 0 ≤ meromorphicOrderAt f₁ v :=
      RS.MeromorphicAt.orderAt_sub_principalPartAt_nonneg (hR v (Set.mem_univ v))
    have h2 : 0 ≤ meromorphicOrderAt f₂ v := hf₂anal.neg.meromorphicOrderAt_nonneg
    rw [hsplit]
    exact le_trans (le_min h1 h2) (meromorphicOrderAt_add hf₁m hf₂m)
  · have hvne : ∀ a ∈ P, v ≠ a := fun a ha hcon => hvP (hcon ▸ ha)
    have h1 : 0 ≤ meromorphicOrderAt R v :=
      not_lt.1 (fun hlt => hvP ((hmemP v).2 hlt))
    have h2anal : AnalyticAt ℂ (fun u => -(tail u)) v := (htail_anal v hvne).neg
    have hsplit : Rmid = R + fun u => -(tail u) := by
      funext u
      change R u - tail u = R u + -(tail u)
      ring
    rw [hsplit]
    exact le_trans (le_min h1 h2anal.meromorphicOrderAt_nonneg)
      (meromorphicOrderAt_add (hR v (Set.mem_univ v)) h2anal.meromorphicAt)

/-- A meromorphic coefficient that is meromorphic at `∞` is analytic outside a large disc.
Split out of `sum_resAt_eq_zero` for the 200-line proof size we hold ourselves to. -/
private theorem exists_analyticAt_far {θ : RS.MFormData (OnePoint ℂ)} {R : ℂ → ℂ}
    (hInfMero : MeromorphicAt (θ.coeffAt (∞ : OnePoint ℂ)) 0)
    (hcompat : ∀ z : ℂ, z ≠ 0 → θ.coeffAt (∞ : OnePoint ℂ) z = -(z ^ 2)⁻¹ * R z⁻¹) :
    ∃ M : ℝ, 0 < M ∧ ∀ v : ℂ, M < ‖v‖ → AnalyticAt ℂ R v := by
  have hev : ∀ᶠ w in 𝓝[≠] (0 : ℂ), AnalyticAt ℂ (θ.coeffAt (∞ : OnePoint ℂ)) w :=
    hInfMero.eventually_analyticAt
  rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨ε⁻¹, by positivity, ?_⟩
  intro v hv
  have hv0 : v ≠ 0 := by
    intro hcon
    rw [hcon, norm_zero] at hv
    exact absurd hv (not_lt.2 (by positivity))
  have hvinv : AnalyticAt ℂ (θ.coeffAt (∞ : OnePoint ℂ)) v⁻¹ := by
    apply hball
    constructor
    · rw [Metric.mem_ball, dist_zero_right, norm_inv]
      exact inv_lt_of_inv_lt₀ hε hv
    · exact inv_ne_zero hv0
  have hAcomp : AnalyticAt ℂ
      (fun u : ℂ => -(u ^ 2)⁻¹ * θ.coeffAt (∞ : OnePoint ℂ) u⁻¹) v := by
    apply AnalyticAt.mul
    · exact ((analyticAt_id.pow 2).inv (pow_ne_zero 2 hv0)).neg
    · exact hvinv.comp (analyticAt_id.inv hv0)
  apply hAcomp.congr
  filter_upwards [isOpen_compl_singleton.mem_nhds
    (Set.mem_compl_singleton_iff.mpr hv0)] with u hu
  have hu0 : u ≠ 0 := hu
  have h1 := hcompat u⁻¹ (inv_ne_zero hu0)
  rw [inv_inv, inv_pow, inv_inv] at h1
  rw [h1, show -(u ^ 2)⁻¹ * (-(u ^ 2) * R u) = ((u ^ 2)⁻¹ * u ^ 2) * R u by ring,
    inv_mul_cancel₀ (pow_ne_zero 2 hu0), one_mul]

/-- Only finitely many points carry a pole of the finite-chart coefficient. Split out of
`sum_resAt_eq_zero` for the 200-line proof size we hold ourselves to. -/
private theorem finite_setOf_meromorphicOrderAt_neg {θ : RS.MFormData (OnePoint ℂ)} {R : ℂ → ℂ}
    (hord_coe : ∀ v : ℂ, (RS.MForm.mk θ).ord ((v : ℂ) : OnePoint ℂ) = meromorphicOrderAt R v) :
    {v : ℂ | meromorphicOrderAt R v < 0}.Finite := by
  have hfin := RS.MForm.finite_setOf_ord_neg (RS.MForm.mk θ)
  have hsub : {v : ℂ | meromorphicOrderAt R v < 0}
      ⊆ (fun v : ℂ => ((v : ℂ) : OnePoint ℂ)) ⁻¹'
        {y : OnePoint ℂ | (RS.MForm.mk θ).ord y < 0} := by
    intro v hv
    simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hv ⊢
    rw [hord_coe v]
    exact hv
  exact Set.Finite.subset
    (hfin.preimage (Set.injOn_of_injective OnePoint.coe_injective)) hsub

open scoped Classical in
/-- **The residue theorem on `ℙ¹`** (the genus-0 base case of the residue theorem, task item 2):
the residues of any meromorphic 1-form on the projective line sum to zero. -/
theorem sum_resAt_eq_zero (Θ : RS.MForm (OnePoint ℂ)) : ∑ᶠ y, Θ.resAt y = 0 := by
  obtain ⟨θ, rfl⟩ := RS.MForm.exists_rep Θ
  set R : ℂ → ℂ := θ.coeffAt (((0 : ℂ) : OnePoint ℂ)) with hR_def
  have hR : MeromorphicOn R Set.univ := by
    have h := θ.meromorphicOn_coeffAt (((0 : ℂ) : OnePoint ℂ))
    rwa [chartAt_target_eq_univ] at h
  -- the ∞-chart coefficient and its pointwise relation to `R`
  have hInfMero : MeromorphicAt (θ.coeffAt (∞ : OnePoint ℂ)) 0 := by
    have h := θ.meromorphicAt_coeffAt (∞ : OnePoint ℂ)
    rwa [chartAt_infty, invChart_apply_infty] at h
  have hcompat : ∀ z : ℂ, z ≠ 0 → θ.coeffAt (∞ : OnePoint ℂ) z = -(z ^ 2)⁻¹ * R z⁻¹ :=
    fun z hz => coeffAt_infty_eq θ hz
  -- `R` is honestly analytic near `∞`
  have hRfar := exists_analyticAt_far hInfMero hcompat
  obtain ⟨M, hM0, hRfarM⟩ := hRfar
  -- residue/order readings at the two kinds of points
  have hord_coe : ∀ v : ℂ,
      (RS.MForm.mk θ).ord ((v : ℂ) : OnePoint ℂ) = meromorphicOrderAt R v := by
    intro v
    change meromorphicOrderAt (θ.coeffAt (((v : ℂ) : OnePoint ℂ)))
      (chartAt ℂ (((v : ℂ) : OnePoint ℂ)) (((v : ℂ) : OnePoint ℂ))) = _
    rw [coeffAt_coe_eq_coeffAt_coe θ v 0, chartAt_coe, coeChart_apply_coe, ← hR_def]
  have hres_coe : ∀ v : ℂ,
      (RS.MForm.mk θ).resAt ((v : ℂ) : OnePoint ℂ) = RS.resAt R v := by
    intro v
    change RS.resAt (θ.coeffAt (((v : ℂ) : OnePoint ℂ)))
      (chartAt ℂ (((v : ℂ) : OnePoint ℂ)) (((v : ℂ) : OnePoint ℂ))) = _
    rw [coeffAt_coe_eq_coeffAt_coe θ v 0, chartAt_coe, coeChart_apply_coe, ← hR_def]
  -- the finite pole set
  have hfinP := finite_setOf_meromorphicOrderAt_neg hord_coe
  set P : Finset ℂ := hfinP.toFinset with hP_def
  have hmemP : ∀ a : ℂ, a ∈ P ↔ meromorphicOrderAt R a < 0 := fun a =>
    hfinP.mem_toFinset
  -- the principal-part tail and the remainder
  set tail : ℂ → ℂ := fun v => ∑ a ∈ P, RS.principalPartAt R a v with htail_def
  set Rmid : ℂ → ℂ := fun v => R v - tail v with hRmid_def
  have htail_anal : ∀ v : ℂ, (∀ a ∈ P, v ≠ a) → AnalyticAt ℂ tail v := by
    intro v hv
    apply Finset.analyticAt_fun_sum
    intro a ha
    exact RS.analyticOnNhd_principalPartAt v (hv a ha)
  have htail_mero : ∀ v : ℂ, MeromorphicAt tail v := by
    intro v
    apply MeromorphicAt.fun_sum
    intro a _
    by_cases hva : v = a
    · subst hva
      exact RS.meromorphicAt_principalPartAt
    · exact (RS.analyticOnNhd_principalPartAt v hva).meromorphicAt
  have hmid_mero : MeromorphicOn Rmid Set.univ :=
    fun v _ => (hR v (Set.mem_univ v)).sub (htail_mero v)
  have hmid_ord := meromorphicOrderAt_sub_tail_nonneg hR P hmemP htail_anal
  -- a bound past which `Rmid` is honestly analytic
  obtain ⟨B, hB⟩ := Set.Finite.bddAbove (P.finite_toSet.image fun a : ℂ => ‖a‖)
  set C : ℝ := max M B with hC_def
  have hC0 : 0 < C := lt_of_lt_of_le hM0 (le_max_left M B)
  have hmid_far : ∀ v : ℂ, C < ‖v‖ → AnalyticAt ℂ Rmid v := by
    intro v hv
    have h1 : AnalyticAt ℂ R v := hRfarM v (lt_of_le_of_lt (le_max_left M B) hv)
    have h2 : AnalyticAt ℂ tail v := by
      apply htail_anal v
      intro a ha hcon
      have hle : ‖a‖ ≤ B := hB ⟨a, Finset.mem_coe.2 ha, rfl⟩
      rw [hcon] at hv
      exact absurd (lt_of_le_of_lt (le_max_right M B) hv) (not_lt.2 hle)
    exact h1.sub h2
  -- the entire repair of the remainder
  obtain ⟨Rf, hRfdiff, hRfval, -⟩ := exists_differentiable_of_ord_nonneg hmid_mero hmid_ord
  -- the ∞-chart readings
  set G : ℂ → ℂ := fun w => -(w ^ 2)⁻¹ * R w⁻¹ with hG_def
  set Gmid : ℂ → ℂ := fun w => -(w ^ 2)⁻¹ * Rmid w⁻¹ with hGmid_def
  set Gtail : ℂ → ℂ := fun w => -(w ^ 2)⁻¹ * tail w⁻¹ with hGtail_def
  have hGsplit : ∀ w : ℂ, G w = Gmid w + Gtail w := by
    intro w
    change -(w ^ 2)⁻¹ * R w⁻¹ = -(w ^ 2)⁻¹ * (R w⁻¹ - tail w⁻¹) + -(w ^ 2)⁻¹ * tail w⁻¹
    ring
  have hG_mero : MeromorphicAt G 0 := by
    apply hInfMero.congr
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact hcompat w hw
  have hGtail_eq : Gtail = fun w => ∑ a ∈ P,
      ∑ k ∈ Finset.Icc (meromorphicOrderAt R a).untop₀ (-1 : ℤ),
        RS.laurentCoeffAt R a k * (-(w ^ 2)⁻¹ * (w⁻¹ - a) ^ k) := by
    funext w
    change -(w ^ 2)⁻¹ * tail w⁻¹ = _
    rw [htail_def]
    simp only [RS.principalPartAt]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hterm_mero : ∀ a ∈ P, MeromorphicAt (fun w : ℂ =>
      ∑ k ∈ Finset.Icc (meromorphicOrderAt R a).untop₀ (-1 : ℤ),
        RS.laurentCoeffAt R a k * (-(w ^ 2)⁻¹ * (w⁻¹ - a) ^ k)) 0 := by
    intro a _
    apply MeromorphicAt.fun_sum
    intro k _
    exact (MeromorphicAt.const _ 0).mul (meromorphicAt_neg_sq_inv_mul_sub_inv_zpow a k)
  have hGtail_mero : MeromorphicAt Gtail 0 := by
    rw [hGtail_eq]
    exact MeromorphicAt.fun_sum hterm_mero
  have hGmid_mero : MeromorphicAt Gmid 0 := by
    have heq : Gmid = fun w => G w - Gtail w := by
      funext w
      rw [hGsplit w]
      ring
    rw [heq]
    exact hG_mero.sub hGtail_mero
  -- the remainder's residue at ∞ vanishes (Liouville-free contour fact + repair)
  have hGmid_res : RS.resAt Gmid 0 = 0 := by
    have hgerm : Gmid =ᶠ[𝓝[≠] (0 : ℂ)] fun w => -(w ^ 2)⁻¹ * Rf w⁻¹ := by
      have hball : Metric.ball (0 : ℂ) C⁻¹ ∈ 𝓝 (0 : ℂ) :=
        Metric.ball_mem_nhds _ (by positivity)
      filter_upwards [mem_nhdsWithin_of_mem_nhds hball, self_mem_nhdsWithin] with w hw1 hw2
      have hw0 : w ≠ 0 := hw2
      have hwlt : ‖w‖ < C⁻¹ := by rwa [Metric.mem_ball, dist_zero_right] at hw1
      have hfar : C < ‖w⁻¹‖ := by
        rw [norm_inv]
        exact (lt_inv_comm₀ (norm_pos_iff.2 hw0) hC0).1 hwlt
      change -(w ^ 2)⁻¹ * Rmid w⁻¹ = -(w ^ 2)⁻¹ * Rf w⁻¹
      rw [(hRfval _ (hmid_far _ hfar)).symm]
    rw [RS.resAt_congr hgerm]
    exact resAt_neg_sq_inv_mul_comp_inv_eq_zero hRfdiff (hGmid_mero.congr hgerm)
  -- the tail's residue at ∞ is minus the sum of finite residues
  have hGtail_res : RS.resAt Gtail 0 = -∑ a ∈ P, RS.resAt R a := by
    rw [hGtail_eq, RS.resAt_fun_sum hterm_mero, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a haP
    have hsummand : ∀ k ∈ Finset.Icc (meromorphicOrderAt R a).untop₀ (-1 : ℤ),
        MeromorphicAt
          (fun w : ℂ => RS.laurentCoeffAt R a k * (-(w ^ 2)⁻¹ * (w⁻¹ - a) ^ k)) 0 :=
      fun k _ =>
        (MeromorphicAt.const _ 0).mul (meromorphicAt_neg_sq_inv_mul_sub_inv_zpow a k)
    rw [RS.resAt_fun_sum hsummand]
    have hterm : ∀ k ∈ Finset.Icc (meromorphicOrderAt R a).untop₀ (-1 : ℤ),
        RS.resAt (fun w => RS.laurentCoeffAt R a k * (-(w ^ 2)⁻¹ * (w⁻¹ - a) ^ k)) 0
          = if k = -1 then -(RS.laurentCoeffAt R a k) else 0 := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [RS.resAt_const_mul, resAt_neg_sq_inv_mul_sub_inv_zpow a (by omega : k < 0)]
      split_ifs with h
      · ring
      · ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    have hlt : meromorphicOrderAt R a < 0 := (hmemP a).1 haP
    have hne : meromorphicOrderAt R a ≠ ⊤ := hlt.ne_top
    have hmem : (-1 : ℤ) ∈ Finset.Icc (meromorphicOrderAt R a).untop₀ (-1 : ℤ) := by
      rw [Finset.mem_Icc]
      refine ⟨?_, le_refl _⟩
      have hcast : ((meromorphicOrderAt R a).untop₀ : WithTop ℤ) = meromorphicOrderAt R a :=
        WithTop.coe_untop₀_of_ne_top hne
      have hlt' : ((meromorphicOrderAt R a).untop₀ : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ) := by
        rw [hcast]
        exact_mod_cast hlt
      have := WithTop.coe_lt_coe.1 hlt'
      omega
    rw [if_pos hmem]
    rfl
  -- the residue at ∞
  have hres_infty : (RS.MForm.mk θ).resAt (∞ : OnePoint ℂ) = -∑ a ∈ P, RS.resAt R a := by
    have h0 : (RS.MForm.mk θ).resAt (∞ : OnePoint ℂ)
        = RS.resAt (θ.coeffAt (∞ : OnePoint ℂ)) 0 := by
      change RS.resAt (θ.coeffAt (∞ : OnePoint ℂ))
        (chartAt ℂ (∞ : OnePoint ℂ) (∞ : OnePoint ℂ)) = _
      rw [chartAt_infty, invChart_apply_infty]
    have h1 : RS.resAt (θ.coeffAt (∞ : OnePoint ℂ)) 0 = RS.resAt G 0 := by
      apply RS.resAt_congr
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact hcompat w hw
    have h2 : RS.resAt G 0 = RS.resAt Gmid 0 + RS.resAt Gtail 0 := by
      have hfun : G = fun w => Gmid w + Gtail w := funext hGsplit
      rw [hfun]
      exact RS.resAt_fun_add hGmid_mero hGtail_mero
    rw [h0, h1, h2, hGmid_res, hGtail_res, zero_add]
  -- assemble the finite sum
  set T : Finset (OnePoint ℂ) :=
    P.image (fun a : ℂ => ((a : ℂ) : OnePoint ℂ)) ∪ {(∞ : OnePoint ℂ)} with hT_def
  have hsupp : Function.support (fun y => (RS.MForm.mk θ).resAt y) ⊆ ↑T := by
    intro y hy
    rw [Function.mem_support] at hy
    induction y using OnePoint.rec with
    | infty =>
      exact Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_singleton_self _))
    | coe a =>
      have haP : a ∈ P := by
        by_contra hcon
        apply hy
        rw [hres_coe a]
        exact RS.resAt_of_order_nonneg (not_lt.1 (fun hlt => hcon ((hmemP a).2 hlt)))
      exact Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ haP))
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp]
  have hdisjT : Disjoint (P.image (fun a : ℂ => ((a : ℂ) : OnePoint ℂ)))
      ({(∞ : OnePoint ℂ)} : Finset (OnePoint ℂ)) := by
    rw [Finset.disjoint_singleton_right]
    simp only [Finset.mem_image, not_exists, not_and]
    exact fun a _ => OnePoint.coe_ne_infty a
  rw [hT_def, Finset.sum_union hdisjT, Finset.sum_singleton, hres_infty,
    Finset.sum_image (fun a _ b _ h => OnePoint.coe_injective h)]
  rw [Finset.sum_congr rfl (fun a _ => hres_coe a)]
  exact add_neg_cancel _

end RS.P1

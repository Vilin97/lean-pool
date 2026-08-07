/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.CanonicalForms.LinearSystems
import LeanPool.JacobianDiffgeo.Finiteness.Chi
import Mathlib.Analysis.Calculus.MeanValue

/-!
# D9: existence of a nonconstant meromorphic function and a nonzero meromorphic 1-form

Unit: canonical-forms (`docs/design/canonical-forms.md` §2 D9, §4.4, proof plan §5 P-exist).
This is the unit's raison d'être: `finiteness-and-chi`'s χ ledger, gated on cech's Skyscraper
fragment, has now LANDED (`Jacobian/Finiteness/Chi.lean`), so the file the design's own file
plan flagged as "the ONLY file gated on finiteness-and-chi" can finally be written.

## What this file delivers

* **`Function.locallyFinsuppWithin.degree_single`** — closes the §1.6 gap note honestly: no
  separate `Divisor.single` constructor was ever needed. Mathlib's own
  `Function.locallyFinsuppWithin.single` already lands in `locallyFinsuppWithin (Set.univ) Y`
  (see its statement in `Mathlib/Topology/LocallyFinsupp.lean:153`), which *is* `RS.Divisor X`
  (the `abbrev` unfolds), so `Function.locallyFinsuppWithin.single P n` is directly usable as a
  point-divisor of any integer value `n` at `P`. `Finiteness/Chi.lean`'s own `degree_single`
  already exploits exactly this (at the fixed value `n = 1`); this generalizes it to arbitrary
  `n`, needed to build divisors of prescribed degree in the existence argument below.
* **`MForm.d_ne_zero`** (moved, not duplicated): `residue-theorem`'s `Reduction.lean` had already
  proved "the differential of a nonconstant meromorphic function is nonzero" — but purely as an
  internal step of *its own* theorem, using only canonical-forms/meromorphic-and-divisors
  machinery (no residue-theorem-specific content: no `ℙ¹`, no trace, no calibration). Since
  `residue-theorem` is DOWNSTREAM of `canonical-forms` (its root docstring calls
  `exists_nonconstant_mero` "canonical-forms D9's exact export shape"), importing it *back* from
  here would be a cycle. This is exactly the D9 existence-chain's own nonzero-ness step (§2 D9:
  "`exists_ne_zero_mform` is then `⟨MForm.d f, ...⟩`"), so canonical-forms is its clean home; the
  proof is transplanted verbatim (renaming the bound meromorphic function `φ ↦ f` to match
  `MForm.d`'s
  own parameter name), and residue-theorem's `Reduction.lean` now imports it from here instead
  (see that file's updated note).
* **`exists_nonconstant_mero`/`exists_ne_zero_mform`** (D9 itself, Forster 16.11 pattern): pick
  any point `P`; choose a divisor `D := single P n` of large enough degree that
  `chi 0 + D.degree ≥ 2` (always possible, `n` is free); `chi_zero_add_degree_le_l` gives
  `l D ≥ 2`; since `l 0 = 1` (Liouville, `linSys_zero_eq_span_one`) and `LinSys 0 ≤ LinSys D`
  (`linSys_mono`, `0 ≤ D`), the finite-dimensional inclusion `LinSys 0 ≤ LinSys D` is proper
  (unequal finrank), so some `f ∈ LinSys D` lies outside `LinSys 0 = span{1}` — i.e. `f` is not
  any constant. `exists_ne_zero_mform` is the one-liner `⟨MForm.d f, MForm.d_ne_zero hf⟩`.
* **`exists_canonicalDivisor`**: the D10 existence corollary — a canonical divisor concretely
  exists (D10's `canonicalDivisorOf`/`canonicalDivisorOf_linearEquiv`, already proved in
  `OneDimensional.lean` since they have no finiteness dependence, need a witness `θ₀ ≠ 0` to be
  instantiated at all; D9 supplies it).
-/

open scoped ContDiff Manifold
open Set IsManifold Filter Topology

/-! ### Compat: `Function.locallyFinsuppWithin.degree_single` at an arbitrary value -/

namespace Function.locallyFinsuppWithin

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [DecidableEq X]

/-- Compat (upstream candidate; generalizes `RS.Finiteness.degree_single`'s fixed value `1` to an
arbitrary `n`): the degree of the point-divisor `single P n` is `n`. -/
theorem degree_single (P : X) (n : ℤ) :
    (Function.locallyFinsuppWithin.single P n : RS.Divisor X).degree = n := by
  rw [Function.locallyFinsuppWithin.degree_eq_sum_of_subset
    (S := ({P} : Finset X)) (fun x hx => by
      simp only [Function.mem_support, ne_eq] at hx
      by_contra hxP
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hxP
      exact hx (by rw [Function.locallyFinsuppWithin.single_apply, if_neg hxP]))]
  simp

end Function.locallyFinsuppWithin

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### `MForm.d_ne_zero`: moved here from `residue-theorem/Reduction.lean` (clean home, see the
module docstring above for why the import direction forced the move). -/

open scoped Classical in
/-- The differential of a nonconstant meromorphic function is a nonzero meromorphic 1-form
(identity-theorem dichotomy: were `d f = 0`, the chart derivative would vanish near some
nonnegative-order point, forcing `f.holoRepr` to be locally — hence codiscretely — constant). -/
theorem MForm.d_ne_zero [T2Space X] [ConnectedSpace X] {f : ℳ X}
    (hf : ∀ c : ℂ, f ≠ algebraMap ℂ (ℳ X) c) : MForm.d f ≠ 0 := by
  intro hd0
  have hf0 : f ≠ 0 := by
    have h := hf 0
    rwa [map_zero] at h
  have hf'mero : MeromorphicOnX f.holoRepr Set.univ :=
    MeroGermOn.meromorphicOnX_holoRepr isOpen_univ f
  -- a point of nonnegative order
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : X, 0 ≤ f.ord x₁ := by
    set x₀ := Classical.arbitrary X with hx₀_def
    rcases le_or_gt 0 (f.ord x₀) with hle | hlt
    · exact ⟨x₀, hle⟩
    · obtain ⟨y, hy⟩ := (RS.eventually_ord_eq_zero hf0 x₀).exists
      exact ⟨y, le_of_eq hy.symm⟩
  have hcmd : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f.holoRepr x₁ :=
    MeroGermOn.holoRepr_contMDiffAt isOpen_univ (Set.mem_univ x₁) hx₁
  have hgan : AnalyticAt ℂ (f.holoRepr ∘ ⇑(chartAt ℂ x₁).symm) (chartAt ℂ x₁ x₁) :=
    RS.contMDiffAt_iff_analyticAt_comp_chartAt.mp hcmd
  -- `d f = 0` forces the chart derivative to vanish on a punctured neighborhood
  have hd_top : meromorphicOrderAt (deriv (f.holoRepr ∘ ⇑(chartAt ℂ x₁).symm))
      (chartAt ℂ x₁ x₁) = ⊤ := by
    have h1 : (MForm.d f).ord x₁ = ⊤ := by
      rw [hd0]
      exact MForm.ord_zero x₁
    have h2 : (MForm.d f).ord x₁
        = meromorphicOrderAt ((MFormData.d f).coeffAt x₁) (chartAt ℂ x₁ x₁) := rfl
    rw [h2] at h1
    have h3 : (MFormData.d f).coeffAt x₁ =ᶠ[𝓝[≠] (chartAt ℂ x₁ x₁)]
        deriv (f.holoRepr ∘ ⇑(chartAt ℂ x₁).symm) := by
      have htarget : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x₁ x₁), z ∈ (chartAt ℂ x₁).target :=
        eventually_nhdsWithin_of_eventually_nhds
          ((chartAt ℂ x₁).open_target.mem_nhds (mem_chart_target ℂ x₁))
      filter_upwards [htarget] with z hz
      change (if z ∈ (chartAt ℂ x₁).target then
        deriv (f.holoRepr ∘ ⇑(chartAt ℂ x₁).symm) z else 0) = _
      rw [if_pos hz]
    rw [meromorphicOrderAt_congr h3] at h1
    exact h1
  have hderiv0 : deriv (f.holoRepr ∘ ⇑(chartAt ℂ x₁).symm)
      =ᶠ[𝓝[≠] (chartAt ℂ x₁ x₁)] 0 := meromorphicOrderAt_eq_top_iff.1 hd_top
  -- upgrade to a full neighborhood
  have hdc : AnalyticAt ℂ (deriv (f.holoRepr ∘ ⇑(chartAt ℂ x₁).symm)) (chartAt ℂ x₁ x₁) :=
    hgan.deriv
  have hval0 : deriv (f.holoRepr ∘ ⇑(chartAt ℂ x₁).symm) (chartAt ℂ x₁ x₁) = 0 := by
    have h1 : Tendsto (deriv (f.holoRepr ∘ ⇑(chartAt ℂ x₁).symm)) (𝓝[≠] (chartAt ℂ x₁ x₁))
        (𝓝 (deriv (f.holoRepr ∘ ⇑(chartAt ℂ x₁).symm) (chartAt ℂ x₁ x₁))) :=
      hdc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (deriv (f.holoRepr ∘ ⇑(chartAt ℂ x₁).symm)) (𝓝[≠] (chartAt ℂ x₁ x₁))
        (𝓝 0) := by
      rw [tendsto_congr' hderiv0]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  have hderiv0' : deriv (f.holoRepr ∘ ⇑(chartAt ℂ x₁).symm) =ᶠ[𝓝 (chartAt ℂ x₁ x₁)] 0 :=
    eventuallyEq_nhds_of_eventuallyEq_nhdsNE hderiv0 (by simpa using hval0)
  -- constant on a small ball
  have hanev : ∀ᶠ w in 𝓝 (chartAt ℂ x₁ x₁),
      AnalyticAt ℂ (f.holoRepr ∘ ⇑(chartAt ℂ x₁).symm) w := hgan.eventually_analyticAt
  obtain ⟨r, hr0, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hanev.and hderiv0')
  have hconst : ∀ w ∈ Metric.ball (chartAt ℂ x₁ x₁) r,
      (f.holoRepr ∘ ⇑(chartAt ℂ x₁).symm) w
        = (f.holoRepr ∘ ⇑(chartAt ℂ x₁).symm) (chartAt ℂ x₁ x₁) := by
    intro w hw
    exact Metric.isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball (chartAt ℂ x₁ x₁) r).isPreconnected
      (fun v hv => ((hball v hv).1).differentiableAt.differentiableWithinAt)
      (fun v hv => (hball v hv).2) hw (Metric.mem_ball_self hr0)
  set cval : ℂ := (f.holoRepr ∘ ⇑(chartAt ℂ x₁).symm) (chartAt ℂ x₁ x₁) with hcval_def
  -- back on `X`: `f.holoRepr` is constant near `x₁`
  have hXconst : ∀ᶠ p in 𝓝 x₁, f.holoRepr p = cval := by
    have hmem : (chartAt ℂ x₁).source ∩
        ⇑(chartAt ℂ x₁) ⁻¹' Metric.ball (chartAt ℂ x₁ x₁) r ∈ 𝓝 x₁ := by
      apply Filter.inter_mem
      · exact (chartAt ℂ x₁).open_source.mem_nhds (mem_chart_source ℂ x₁)
      · exact ((chartAt ℂ x₁).continuousAt (mem_chart_source ℂ x₁)).preimage_mem_nhds
          (Metric.ball_mem_nhds _ hr0)
    filter_upwards [hmem] with p hp
    have h := hconst (chartAt ℂ x₁ p) hp.2
    rwa [Function.comp_apply, (chartAt ℂ x₁).left_inv hp.1] at h
  -- hence `f` is a constant class — contradiction
  have hsubmero : MeromorphicOnX (fun p => f.holoRepr p - cval) Set.univ :=
    fun p hp => (hf'mero p hp).sub (meromorphicAtX_const cval)
  have htop : ordAtX (fun p => f.holoRepr p - cval) x₁ = ⊤ := by
    rw [ordAtX_eq_top_iff]
    filter_upwards [hXconst.filter_mono nhdsWithin_le_nhds] with p hp
    change f.holoRepr p - cval = 0
    rw [hp, sub_self]
  rcases hsubmero.eventuallyEq_zero_or_forall_ordAtX_ne_top with hzero | hnetop
  · apply hf cval
    rw [← MeroGermOn.mk_holoRepr isOpen_univ f, MeroGermOn.algebraMap_mk]
    apply MeroGermOn.mk_eq_mk.2
    have h1 : ∀ᶠ p in Filter.codiscrete X, f.holoRepr p - cval = 0 := hzero
    filter_upwards [h1] with p hp
    exact sub_eq_zero.1 hp
  · exact hnetop x₁ htop

/-! ### D9: the existence chain -/

section Existence

variable [T2Space X] [CompactSpace X] [ConnectedSpace X]

/-- **D9** (Forster 16.11 pattern): a compact connected Riemann surface admits a nonconstant
meromorphic function. Proved from `finiteness-and-chi`'s χ-ledger: at a divisor `D := single P n`
of large enough degree, `χ(0) + deg D ≤ l(D)` forces `l(D) ≥ 2 > 1 = l(0)`, so `L(0) = span{1}`
is a PROPER subspace of `L(D)` — any witness outside it is not a constant. -/
theorem exists_nonconstant_mero : ∃ f : ℳ X, ∀ c : ℂ, f ≠ algebraMap ℂ (ℳ X) c := by
  classical
  set P := Classical.arbitrary X with hP_def
  set chi0 : ℤ := RS.Finiteness.chi (0 : Divisor X) with hchi0_def
  set D : Divisor X := Function.locallyFinsuppWithin.single P (|chi0| + 2) with hD_def
  have hDdeg : D.degree = |chi0| + 2 := by
    rw [hD_def]; exact Function.locallyFinsuppWithin.degree_single P _
  have hDnn : 0 ≤ D := by
    rw [hD_def]
    exact Function.locallyFinsuppWithin.single_nonneg.2 (by positivity)
  have hchi2 : 2 ≤ chi0 + D.degree := by
    rw [hDdeg]
    have h1 := neg_abs_le chi0
    omega
  have hlD : (2 : ℤ) ≤ (l D : ℤ) :=
    le_trans hchi2 (RS.Finiteness.chi_zero_add_degree_le_l D)
  have hl0 : l (0 : Divisor X) = 1 := l_zero
  have hlDnat : 2 ≤ l D := by exact_mod_cast hlD
  have hle : LinSys (0 : Divisor X) ≤ LinSys D := linSys_mono hDnn
  have hne : LinSys (0 : Divisor X) ≠ LinSys D := fun heq => by
    have hleq : l (0 : Divisor X) = l D := by
      change Module.finrank ℂ (LinSys (0 : Divisor X)) = Module.finrank ℂ (LinSys D)
      rw [heq]
    rw [hl0] at hleq
    omega
  obtain ⟨f, hfD, hf0⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  rw [linSys_zero_eq_span_one] at hf0
  refine ⟨f, fun c hc => hf0 ?_⟩
  rw [hc, Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self 1)

/-- **D9**: a compact connected Riemann surface admits a nonzero meromorphic 1-form — the
differential of the nonconstant function `exists_nonconstant_mero` supplies. -/
theorem exists_ne_zero_mform : ∃ θ : MForm X, θ ≠ 0 := by
  obtain ⟨f, hf⟩ := exists_nonconstant_mero (X := X)
  exact ⟨MForm.d f, MForm.d_ne_zero hf⟩

end Existence

/-! ### D10 corollary: a canonical divisor concretely exists -/

/-- A canonical divisor exists (D10's `canonicalDivisorOf`/`canonicalDivisorOf_linearEquiv`,
already proved finiteness-free in `OneDimensional.lean`, need a witness `θ₀ ≠ 0` to be
instantiated at all — D9 supplies it). -/
theorem exists_canonicalDivisor [T2Space X] [CompactSpace X] [ConnectedSpace X] :
    ∃ (K : Divisor X) (θ₀ : MForm X), θ₀ ≠ 0 ∧ K = canonicalDivisorOf θ₀ := by
  obtain ⟨θ₀, hθ₀⟩ := exists_ne_zero_mform (X := X)
  exact ⟨canonicalDivisorOf θ₀, θ₀, hθ₀, rfl⟩

end RS

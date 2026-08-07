/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.CanonicalForms.Differential
import LeanPool.JacobianDiffgeo.Meromorphic.Gluing

/-!
# One-dimensionality over `ℳ(X)` (D8) and the canonical divisor `K` (D10)

Unit: canonical-forms (`docs/design/canonical-forms.md` §2 D8/D10, proof plan §5 P5).

* `MForm.smul_eq_zero_iff`/`MForm.smul_left_injective`: `ℳ(X)`-scaling by a nonzero form is
  injective (the D5 dichotomy + the `ord_smul_mero` dictionary).
* **D8** `MForm.exists_unique_smul_of_ne_zero`: `MForm X` is one-dimensional over `ℳ X` — every
  meromorphic 1-form is a unique `ℳ(X)`-multiple of any fixed nonzero reference `θ₀`. The ratio
  is built chart-locally (`q x := θ.coeffAt x / θ₀.coeffAt x`, transitions cancel — "the ratio of
  two 1-forms is a function") and glued by `MeroGermOn.exists_glue`; on the QUOTIENT the class
  equation needs only `𝓝[≠]`-agreement at each center, where `θ₀`'s coefficient is eventually
  nonzero (D5), so no removable-singularity repair is needed at the zeros of `θ₀`.
* **D10** `canonicalDivisorOf θ₀ := θ₀.divisor` ("a" canonical divisor, seeded by an explicit
  nonzero reference — no silent choice), `MForm.divisor_smul_mero` (divisors add under the
  `ℳ(X)`-action), and `canonicalDivisorOf_linearEquiv` (any two canonical divisors differ by a
  principal divisor — Forster 16.7-style well-definedness up to linear equivalence).

D10 lives here rather than in the design's `Existence.lean` slot because `Existence.lean` (D9)
remains gated on `Jacobian/Finiteness/Chi.lean` (not on disk); `canonicalDivisorOf` has no
finiteness dependence.

Hypothesis note: D8 needs only `[T1Space X] [ConnectedSpace X]` (the design listed an extra
`[T2Space X]`, which is not required — the dichotomy and `Mero.ord_ne_top` are `T1`-level).
-/

open scoped ContDiff Manifold
open Set IsManifold Filter Topology

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace MForm

/-- `ℳ(X)`-scaling detects zero (the uniqueness engine for D8): `h • Θ = 0` iff one factor is. -/
theorem smul_eq_zero_iff [T1Space X] [ConnectedSpace X] {h : ℳ X} {Θ : MForm X} :
    h • Θ = 0 ↔ h = 0 ∨ Θ = 0 := by
  constructor
  · intro hz
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hh, hΘ⟩ := hcon
    have h1 : (h • Θ).ord (Classical.arbitrary X) = ⊤ := by rw [hz]; exact ord_zero _
    rw [ord_smul_mero] at h1
    exact WithTop.add_ne_top.2 ⟨Mero.ord_ne_top hh _, ord_ne_top hΘ _⟩ h1
  · rintro (rfl | rfl)
    · exact zero_smul (ℳ X) Θ
    · exact smul_zero h

/-- Scaling a fixed nonzero reference is injective (D8 uniqueness half). -/
theorem smul_left_injective [T1Space X] [ConnectedSpace X] {Θ₀ : MForm X} (h₀ : Θ₀ ≠ 0) :
    Function.Injective (fun h : ℳ X => h • Θ₀) := by
  intro a b hab
  have hab' : a • Θ₀ = b • Θ₀ := hab
  have hsub : (a - b) • Θ₀ = 0 := by rw [sub_smul, hab', sub_self]
  rcases smul_eq_zero_iff.1 hsub with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h h₀

section Existence

variable [T1Space X] [ConnectedSpace X]

/-- D8, existence half: every meromorphic 1-form is an `ℳ(X)`-multiple of any fixed nonzero
reference (chart-local ratio + `MeroGermOn.exists_glue`). -/
theorem exists_smul_eq {Θ₀ : MForm X} (h₀ : Θ₀ ≠ 0) (Θ : MForm X) :
    ∃ h : ℳ X, Θ = h • Θ₀ := by
  obtain ⟨θ, rfl⟩ := exists_rep Θ
  obtain ⟨θ₀, rfl⟩ := exists_rep Θ₀
  -- the chart-local ratio, as an X-level function per chart
  set q : X → X → ℂ := fun x w =>
    θ.coeffAt x (chartAt ℂ x w) / θ₀.coeffAt x (chartAt ℂ x w) with hq_def
  -- A. each ratio is meromorphic on its chart source
  have hmero : ∀ x : X, MeromorphicOnX (q x) (chartAt ℂ x).source := by
    intro x p hp
    rw [meromorphicAtX_iff_of_mem_source (chart_mem_maximalAtlas x) hp]
    have hzt : chartAt ℂ x p ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hp
    have heq : (fun z => θ.coeffAt x z / θ₀.coeffAt x z) =ᶠ[𝓝[≠] (chartAt ℂ x p)]
        (q x) ∘ ⇑(chartAt ℂ x).symm := by
      have hev : ∀ᶠ z in 𝓝 (chartAt ℂ x p), z ∈ (chartAt ℂ x).target :=
        (chartAt ℂ x).open_target.mem_nhds hzt
      filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with z hz
      change θ.coeffAt x z / θ₀.coeffAt x z =
        θ.coeffAt x (chartAt ℂ x ((chartAt ℂ x).symm z)) /
          θ₀.coeffAt x (chartAt ℂ x ((chartAt ℂ x).symm z))
      rw [(chartAt ℂ x).right_inv hz]
    have hdiv : MeromorphicAt (fun z => θ.coeffAt x z / θ₀.coeffAt x z) (chartAt ℂ x p) :=
      (θ.meromorphicOn_coeffAt x _ hzt).div (θ₀.meromorphicOn_coeffAt x _ hzt)
    exact hdiv.congr heq
  set φ : ∀ x : X, MeroGermOn X (chartAt ℂ x).source :=
    fun x => MeroGermOn.mk (q x) (hmero x) with hφ_def
  -- B. the ratios agree on overlaps: the transition derivative cancels
  have hagree : ∀ x y : X, ∀ p ∈ (chartAt ℂ x).source ∩ (chartAt ℂ y).source,
      q x =ᶠ[𝓝[≠] p] q y := by
    intro x y p hp
    obtain ⟨hσ, hσ'⟩ := analyticAt_transition (chart_mem_maximalAtlas y)
      (chart_mem_maximalAtlas x) hp.2 hp.1
    -- hσ : AnalyticAt ℂ (chartAt x ∘ (chartAt y).symm) (chartAt y p), hσ' : its deriv ≠ 0 there
    have hcont : ContinuousAt
        (fun w => deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) (chartAt ℂ y w)) p :=
      hσ.deriv.continuousAt.comp ((chartAt ℂ y).continuousAt hp.2)
    have hne : ∀ᶠ w in 𝓝 p,
        deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) (chartAt ℂ y w) ≠ 0 :=
      hcont.eventually_ne hσ'
    have hmem : ∀ᶠ w in 𝓝 p, w ∈ (chartAt ℂ x).source ∩ (chartAt ℂ y).source :=
      ((chartAt ℂ x).open_source.inter (chartAt ℂ y).open_source).mem_nhds hp
    filter_upwards [hne.filter_mono nhdsWithin_le_nhds,
      hmem.filter_mono nhdsWithin_le_nhds] with w hw1 hw2
    have hli : (chartAt ℂ y).symm (chartAt ℂ y w) = w := (chartAt ℂ y).left_inv hw2.2
    have hcθ := θ.compat x y (chartAt ℂ y w) ⟨w, hw2, rfl⟩
    have hcθ₀ := θ₀.compat x y (chartAt ℂ y w) ⟨w, hw2, rfl⟩
    rw [hli] at hcθ hcθ₀
    change θ.coeffAt x (chartAt ℂ x w) / θ₀.coeffAt x (chartAt ℂ x w) =
      θ.coeffAt y (chartAt ℂ y w) / θ₀.coeffAt y (chartAt ℂ y w)
    rw [hcθ, hcθ₀, mul_div_mul_left _ _ hw1]
  have hcompat : ∀ x y : X,
      MeroGermOn.restrict (Set.inter_subset_left (s := (chartAt ℂ x).source)
        (t := (chartAt ℂ y).source)) (φ x) =
      MeroGermOn.restrict (Set.inter_subset_right (s := (chartAt ℂ x).source)
        (t := (chartAt ℂ y).source)) (φ y) := by
    intro x y
    rw [hφ_def]
    rw [MeroGermOn.restrict_mk, MeroGermOn.restrict_mk]
    refine MeroGermOn.mk_eq_mk.mpr ?_
    rw [eventuallyEq_codiscreteWithin_iff_of_isOpen
      ((chartAt ℂ x).open_source.inter (chartAt ℂ y).open_source)]
    exact hagree x y
  -- C. glue
  obtain ⟨Φ, hΦ⟩ := MeroGermOn.exists_glue (fun x : X => (chartAt ℂ x).open_source) φ hcompat
  have huniv : (Set.univ : Set X) ⊆ ⋃ x : X, (chartAt ℂ x).source :=
    fun p _ => Set.mem_iUnion.2 ⟨p, mem_chart_source ℂ p⟩
  refine ⟨MeroGermOn.restrict huniv Φ, ?_⟩
  set h : ℳ X := MeroGermOn.restrict huniv Φ with hh_def
  -- D. the glued class's canonical representative is the local ratio, near every point
  have hrepr : ∀ x : X, h.holoRepr =ᶠ[𝓝[≠] x] q x := by
    intro x
    have hrestr : MeroGermOn.restrict (Set.subset_univ (chartAt ℂ x).source) h = φ x := by
      rw [hh_def, MeroGermOn.restrict_restrict]
      exact hΦ x
    have h3 : Set.EqOn ((φ x).holoRepr) h.holoRepr (chartAt ℂ x).source := by
      have h4 := MeroGermOn.holoRepr_restrict (Set.subset_univ (chartAt ℂ x).source)
        (chartAt ℂ x).open_source isOpen_univ h
      rw [hrestr] at h4
      exact h4
    have h5 : (φ x).holoRepr =ᶠ[𝓝[≠] x] q x :=
      MeroGermOn.holoRepr_eventuallyEq_nhdsNE (chartAt ℂ x).open_source
        (mem_chart_source ℂ x) (φ x) rfl
    have h6 : ∀ᶠ w in 𝓝[≠] x, w ∈ (chartAt ℂ x).source :=
      eventually_nhdsWithin_of_eventually_nhds
        ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
    filter_upwards [h5, h6] with w hw5 hw6
    rw [← h3 hw6]
    exact hw5
  -- E. the class equation, center by center
  refine sound fun x => ?_
  have hnz : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), θ₀.coeffAt x z ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (θ₀.meromorphicAt_coeffAt x)).1
      (ord_ne_top h₀ x)
  have hq : (h.holoRepr ∘ ⇑(chartAt ℂ x).symm) =ᶠ[𝓝[≠] (chartAt ℂ x x)]
      ((q x) ∘ ⇑(chartAt ℂ x).symm) :=
    eventuallyEq_nhdsNE_comp_chart_iff.mp (hrepr x)
  have htarget : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), z ∈ (chartAt ℂ x).target :=
    eventually_nhdsWithin_of_eventually_nhds
      ((chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x))
  filter_upwards [hnz, hq, htarget] with z h1 h2 h3
  simp only [Function.comp_apply] at h2
  change θ.coeffAt x z = h.holoRepr ((chartAt ℂ x).symm z) * θ₀.coeffAt x z
  rw [h2]
  have hqz : q x ((chartAt ℂ x).symm z) = θ.coeffAt x z / θ₀.coeffAt x z := by
    change θ.coeffAt x (chartAt ℂ x ((chartAt ℂ x).symm z)) /
      θ₀.coeffAt x (chartAt ℂ x ((chartAt ℂ x).symm z)) = _
    rw [(chartAt ℂ x).right_inv h3]
  rw [hqz, div_mul_cancel₀ _ h1]

/-- **D8, one-dimensionality**: every meromorphic 1-form is a UNIQUE `ℳ(X)`-multiple of any
fixed nonzero reference `θ₀` — `MForm X` is a one-dimensional `ℳ(X)`-vector space. -/
theorem exists_unique_smul_of_ne_zero {Θ₀ : MForm X} (h₀ : Θ₀ ≠ 0) (Θ : MForm X) :
    ∃! h : ℳ X, Θ = h • Θ₀ := by
  obtain ⟨h, hh⟩ := exists_smul_eq h₀ Θ
  refine ⟨h, hh, fun h' hh' => smul_left_injective h₀ ?_⟩
  change h' • Θ₀ = h • Θ₀
  rw [← hh', ← hh]

end Existence

end MForm

/-! ### D10: the canonical divisor `K` -/

/-- D10: "a" canonical divisor, seeded by an explicit nonzero reference (no silent
`Classical.choice`-baked default; downstream fixes one when a definite `K` is needed). -/
noncomputable abbrev canonicalDivisorOf [T1Space X]
    (Θ₀ : MForm X) : Divisor X := Θ₀.divisor

/-- Divisors add under the `ℳ(X)`-action (pointwise from `ord_smul_mero`; both orders are finite
by the D5 dichotomy and `Mero.ord_ne_top`). -/
theorem MForm.divisor_smul_mero [T1Space X] [T2Space X] [ConnectedSpace X]
    {h : ℳ X} {Θ : MForm X} (hh : h ≠ 0) (hΘ : Θ ≠ 0) :
    (h • Θ).divisor = RS.divisor h + Θ.divisor := by
  apply Function.locallyFinsuppWithin.ext
  intro y
  rw [Divisor.add_apply, MForm.divisor_apply, MForm.divisor_apply, RS.divisor_apply,
    MForm.ord_smul_mero]
  exact WithTop.untop₀_add (Mero.ord_ne_top hh y) (MForm.ord_ne_top hΘ y)

/-- **D10 (Forster 16.7)**: the canonical divisor is well defined up to linear equivalence — any
two nonzero references have divisors differing by a principal divisor. -/
theorem canonicalDivisorOf_linearEquiv [T1Space X] [T2Space X]
    [ConnectedSpace X] {Θ₀ Θ₀' : MForm X} (h₀ : Θ₀ ≠ 0) (h₀' : Θ₀' ≠ 0) :
    ∃ f : ℳ X, f ≠ 0 ∧ canonicalDivisorOf Θ₀' = canonicalDivisorOf Θ₀ + divisor f := by
  obtain ⟨h, hh, -⟩ := MForm.exists_unique_smul_of_ne_zero h₀ Θ₀'
  have hne : h ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hh
    exact h₀' hh
  refine ⟨h, hne, ?_⟩
  change Θ₀'.divisor = Θ₀.divisor + divisor h
  rw [hh, MForm.divisor_smul_mero hne h₀, add_comm]

end RS

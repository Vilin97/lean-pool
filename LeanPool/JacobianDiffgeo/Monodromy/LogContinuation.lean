/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Monodromy.OpenLocus
import LeanPool.JacobianDiffgeo.Meromorphic
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# `monodromy`: continuation of `log f` along pole/zero-avoiding paths

Unit: monodromy (`docs/design/monodromy.md` §4.2). The DAG-critical deliverable: a continuous
branch of `log f` (equivalently, a primitive of `dlog f = df/f`) along any path avoiding the
zeros/poles of a meromorphic function `f : ℳ X`, with the defining exponential compatibility
`exp (F t) = f.holoRepr (γ.extend t)`.

`dlogForm` is built by *reusing* `Jacobian/Forms/MDifferential.lean`'s `RS.mdifferential`
(the differential of a holomorphic function) and `RS.Form1.smulFun` (multiplication of a form by
a holomorphic function) — both already proved *generically* over any `X` satisfying the standing
surface hypotheses — instantiated with `X := poleZeroLocus f` (the open locus, `Jacobian/Monodromy
/OpenLocus.lean`). This sidesteps entirely the chart-transition/`subtypeRestr` bookkeeping a
from-scratch `Form1CoeffData` construction would need: `f.holoRepr` restricted to the locus is
`ContMDiff` (`mathlib`'s `contMDiffAt_subtype_iff` — smoothness of an open-submanifold restriction
is exactly a per-point statement), nonvanishing there (order `0` at every point of the locus, by
construction), hence its logarithmic derivative `(f.holoRepr)⁻¹ • d(f.holoRepr)` assembles as a
genuine `Form1 (poleZeroLocus f)` via the two already-built combinators, no new coefficient-data
proof needed.

The exponential-compatibility theorem (`exp_eq_holoRepr_of_isPrimitiveAlong`) shows any primitive
of `dlogForm` normalized at the starting value is an honest branch of `log f`, by exhibiting
`H t := f.holoRepr (γ.extend t) * exp (-(F t))` as locally constant (zero-derivative argument, via
`RS.eventuallyEq_of_hasDerivAt_eq`) and hence globally constant (`ℝ` preconnected) — no branch-cut
case analysis on `Complex.log`/`Complex.arg` anywhere.

Main declarations:
* `RS.Monodromy.poleZeroLocus`, `RS.Monodromy.dlogForm` — the pole/zero-free locus and the
  logarithmic-derivative 1-form on it.
* `RS.Monodromy.exp_eq_holoRepr_of_isPrimitiveAlong` — the exponential-compatibility theorem.
* `RS.Monodromy.exists_logBranchAlong`, `RS.Monodromy.logBranchAlong_unique` — existence with a
  prescribed initial branch value, and uniqueness (both bookkeeping over `Path`'s already-built
  existence/uniqueness API).
-/

open scoped ContDiff Manifold Topology
open Set Filter TopologicalSpace

noncomputable section

namespace RS.Monodromy

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The pole/zero-free locus -/

/-- The zero/pole locus of `f` as an open pole-free locus (`(divisor f).support` is finite by
compactness, hence closed by `T2Space`). -/
noncomputable def poleZeroLocus (f : ℳ X) : Opens X :=
  openLocusOfFinite (RS.finite_support_divisor f)

theorem mem_poleZeroLocus_iff {f : ℳ X} (hf : f ≠ 0) {x : X} :
    x ∈ poleZeroLocus f ↔ f.ord x = 0 := by
  change x ∈ openLocusOfFinite (RS.finite_support_divisor f) ↔ f.ord x = 0
  rw [mem_openLocusOfFinite, Function.mem_support, not_not, RS.divisor_apply,
    WithTop.untop₀_eq_zero]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h (RS.Mero.ord_ne_top hf x)
  · exact Or.inl

/-- Lift a path avoiding `f`'s zeros/poles into `poleZeroLocus f`.

NB: this is a thin specialization of `Path.liftOpenLocus` (`OpenLocus.lean`) landing *directly* in
`poleZeroLocus f` rather than in the definitionally-equal-but-syntactically-different
`openLocusOfFinite (finite_support_divisor f)`. This is not cosmetic: with the general
`Path.liftOpenLocus (finite_support_divisor f).isClosed γ hγ` spelling, `X`'s `ChartedSpace`/
`IsManifold` instance search for `RS.IsPrimitiveAlong`/`RS.Form1` gets confused whenever both that
term's type and a separately-mentioned `poleZeroLocus f` (from `dlogForm f hf`) occur in the same
elaboration problem — Lean's instance cache keys on the syntactic form, and the two (defeq) forms
of the locus type produce inconsistent cached instance terms, a `synthInstance` failure with no
direct paper-mathematics content (confirmed by direct trace inspection: `Opens.instChartedSpace`
resolves correctly for either form in isolation, but not when both appear together). Landing
`liftPoleZeroLocus`'s output type in `poleZeroLocus f` syntactically, once and for all, sidesteps
the issue for every downstream use. -/
def Path.liftPoleZeroLocus {f : ℳ X} {x y : X} (γ : Path x y)
    (hγ : ∀ t : ↥unitInterval, γ t ∉ (RS.divisor f).support) :
    Path (⟨x, (mem_openLocusOfFinite (RS.finite_support_divisor f)).mpr (γ.source ▸ hγ 0)⟩
        : poleZeroLocus f)
      (⟨y, (mem_openLocusOfFinite (RS.finite_support_divisor f)).mpr (γ.target ▸ hγ 1)⟩
        : poleZeroLocus f) where
  toFun t := ⟨γ t, (mem_openLocusOfFinite (RS.finite_support_divisor f)).mpr (hγ t)⟩
  continuous_toFun := by fun_prop
  source' := by simp [γ.source]
  target' := by simp [γ.target]

omit [ConnectedSpace X] in
/-- The lift's `extend` recovers `γ.extend` pointwise. -/
theorem Path.liftPoleZeroLocus_extend {f : ℳ X} {x y : X} (γ : Path x y)
    (hγ : ∀ t : ↥unitInterval, γ t ∉ (RS.divisor f).support) (t : ℝ) :
    ((Path.liftPoleZeroLocus γ hγ).extend t : X) = γ.extend t := by
  by_cases ht : t ≤ 0
  · rw [(Path.liftPoleZeroLocus γ hγ).extend_of_le_zero ht, γ.extend_of_le_zero ht]
  · rw [not_le] at ht
    by_cases ht1 : t ≤ 1
    · rw [(Path.liftPoleZeroLocus γ hγ).extend_apply ⟨ht.le, ht1⟩, γ.extend_apply ⟨ht.le, ht1⟩]
      rfl
    · rw [not_le] at ht1
      rw [(Path.liftPoleZeroLocus γ hγ).extend_of_one_le ht1.le, γ.extend_of_one_le ht1.le]

/-! ### `f.holoRepr` restricted to the locus is a nonvanishing holomorphic function -/

theorem contMDiff_holoRepr_poleZeroLocus (f : ℳ X) (hf : f ≠ 0) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun p : poleZeroLocus f => f.holoRepr (p : X)) := by
  intro p
  rw [contMDiffAt_subtype_iff]
  exact RS.MeroGermOn.holoRepr_contMDiffAt isOpen_univ (mem_univ (p : X))
    (le_of_eq (mem_poleZeroLocus_iff hf |>.mp p.2).symm)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- `f.holoRepr` does not vanish anywhere on the order-zero locus (a helper for the general
"order exactly zero ⇒ the canonical representative is nonzero there" fact, R2 in the design). -/
theorem holoRepr_ne_zero_of_ord_eq_zero {f : ℳ X} {x : X} (h0 : f.ord x = 0) :
    f.holoRepr x ≠ 0 := by
  have hcm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f.holoRepr x :=
    RS.MeroGermOn.holoRepr_contMDiffAt isOpen_univ (mem_univ x) (le_of_eq h0.symm)
  have hAn : AnalyticAt ℂ (f.holoRepr ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
    RS.contMDiffAt_iff_analyticAt_comp_chartAt.mp hcm
  have hordAmb : meromorphicOrderAt (f.holoRepr ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) = 0 := by
    change RS.ordAtX f.holoRepr x = 0
    have hmk : RS.MeroGermOn.mk f.holoRepr (RS.MeroGermOn.meromorphicOnX_holoRepr isOpen_univ f)
        = f := RS.MeroGermOn.mk_holoRepr isOpen_univ f
    calc RS.ordAtX f.holoRepr x
        = (RS.MeroGermOn.mk f.holoRepr
            (RS.MeroGermOn.meromorphicOnX_holoRepr isOpen_univ f)).ord x := by
          rw [RS.MeroGermOn.ord_mk isOpen_univ (mem_univ x)]
      _ = f.ord x := by rw [hmk]
      _ = 0 := h0
  have hNF : MeromorphicNFAt (f.holoRepr ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
      hAn.meromorphicNFAt
  have hne := hNF.meromorphicOrderAt_eq_zero_iff.mp hordAmb
  simpa [Function.comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)] using hne

theorem holoRepr_poleZeroLocus_ne_zero (f : ℳ X) (hf : f ≠ 0) (p : poleZeroLocus f) :
    f.holoRepr (p : X) ≠ 0 :=
  holoRepr_ne_zero_of_ord_eq_zero (mem_poleZeroLocus_iff hf |>.mp p.2)

/-! ### `dlogForm`: the logarithmic-derivative 1-form on the locus -/

/-- The logarithmic-derivative 1-form `df/f` of `f`, a genuine holomorphic 1-form on the
pole/zero-free open locus `poleZeroLocus f` — assembled from `RS.mdifferential`/`RS.Form1.smulFun`
(both already built, generically over any surface satisfying the standing hypotheses),
instantiated with `X := poleZeroLocus f`. -/
noncomputable def dlogForm (f : ℳ X) (hf : f ≠ 0) : RS.Form1 (poleZeroLocus f) :=
  RS.Form1.smulFun (fun p : poleZeroLocus f => (f.holoRepr (p : X))⁻¹)
    ((contMDiff_holoRepr_poleZeroLocus f hf).inv₀ (holoRepr_poleZeroLocus_ne_zero f hf))
    (RS.mdifferential (fun p : poleZeroLocus f => f.holoRepr (p : X))
      (contMDiff_holoRepr_poleZeroLocus f hf))

/-- `dlogForm`'s coefficient in any maximal-atlas chart of the locus, on the chart target: the
familiar `(f'/f)`-shape logarithmic derivative, read through the chart. -/
theorem coeffIn_dlogForm (f : ℳ X) (hf : f ≠ 0)
    {e : OpenPartialHomeomorph (poleZeroLocus f) ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω (poleZeroLocus f)) {z : ℂ} (hz : z ∈ e.target) :
    RS.coeffIn e (dlogForm f hf) z =
      (f.holoRepr ((e.symm z : X)))⁻¹ *
        deriv ((fun p : poleZeroLocus f => f.holoRepr (p : X)) ∘ ⇑e.symm) z := by
  change RS.coeffIn e (RS.Form1.smulFun _ _
    (RS.mdifferential (fun p : poleZeroLocus f => f.holoRepr (p : X))
      (contMDiff_holoRepr_poleZeroLocus f hf))) z = _
  rw [RS.coeffIn_smulFun]
  congr 1
  exact RS.coeffIn_mdifferential he (contMDiff_holoRepr_poleZeroLocus f hf) hz

/-! ### The exponential-compatibility theorem -/

/-- **The exponential-compatibility theorem.** Any primitive of `dlogForm f hf` along a
pole/zero-avoiding path is an honest continuous branch of `log f` along the path, PROVIDED it is
normalized so that `exp (F 0) = f.holoRepr x`: `exp (F t) = f.holoRepr (γ.extend t)` for every
`t`. Proved by exhibiting `H t := f.holoRepr (γ.extend t) * exp (-(F t))` as locally constant
(zero-derivative argument on each chart) and hence globally constant (`ℝ` preconnected) — no
branch-cut case analysis on `Complex.log`/`Complex.arg` anywhere. -/
theorem exp_eq_holoRepr_of_isPrimitiveAlong {f : ℳ X} (hf : f ≠ 0) {x y : X} {γ : Path x y}
    (hγ : ∀ t : ↥unitInterval, γ t ∉ (RS.divisor f).support) {F : ℝ → ℂ}
    (hF : RS.IsPrimitiveAlong (Path.liftPoleZeroLocus γ hγ)
      (dlogForm f hf) F)
    (hc₀ : Complex.exp (F 0) = f.holoRepr x) :
    ∀ t : ℝ, Complex.exp (F t) = f.holoRepr (γ.extend t) := by
  set γ' := Path.liftPoleZeroLocus γ hγ with hγ'_def
  set H : ℝ → ℂ := fun t => f.holoRepr (γ.extend t) * Complex.exp (-(F t)) with hH_def
  have hlc : IsLocallyConstant H := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t₀
    set p₀ : poleZeroLocus f := γ'.extend t₀ with hp₀_def
    set e : OpenPartialHomeomorph (poleZeroLocus f) ℂ := chartAt ℂ p₀ with he_def
    obtain ⟨g', hg', hFeq'⟩ := hF.rechart (mem_univ t₀)
      γ'.continuous_extend.continuousWithinAt
      (IsManifold.chart_mem_maximalAtlas p₀) (mem_chart_source ℂ p₀)
    rw [nhdsWithin_univ] at hFeq'
    -- restrict the local-primitive data to the (open) chart target, where `coeffIn_dlogForm`
    -- gives the explicit `(f'/f)`-shaped coefficient formula
    have hg'' : ∀ᶠ z in 𝓝 (e p₀), HasDerivAt g'
        ((f.holoRepr ((e.symm z : X)))⁻¹ *
          deriv ((fun p : poleZeroLocus f => f.holoRepr (p : X)) ∘ ⇑e.symm) z) z := by
      filter_upwards [hg', e.open_target.mem_nhds (e.map_source (mem_chart_source ℂ p₀))]
        with z hz1 hz2
      rwa [coeffIn_dlogForm f hf (IsManifold.chart_mem_maximalAtlas p₀) hz2] at hz1
    -- `φ` tests `g'` against `f.holoRepr`; it has zero derivative throughout the chart target
    set φ : ℂ → ℂ := fun z => f.holoRepr ((e.symm z : X)) * Complex.exp (-(g' z)) with hφ_def
    have hφderiv : ∀ᶠ z in 𝓝 (e p₀), HasDerivAt φ 0 z := by
      filter_upwards [hg'', e.open_target.mem_nhds (e.map_source (mem_chart_source ℂ p₀))]
        with z hgz hzt
      have hAn : AnalyticAt ℂ ((fun p : poleZeroLocus f => f.holoRepr (p : X)) ∘ ⇑e.symm) z := by
        have hcm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
            (fun p : poleZeroLocus f => f.holoRepr (p : X)) (e.symm z) :=
          contMDiff_holoRepr_poleZeroLocus f hf (e.symm z)
        have h := (RS.contMDiffAt_iff_analyticAt_of_mem_source
          (chart_mem_atlas ℂ p₀) (e.map_target hzt)).mp hcm
        rwa [e.right_inv hzt] at h
      have hne : f.holoRepr ((e.symm z : X)) ≠ 0 := holoRepr_poleZeroLocus_ne_zero f hf (e.symm z)
      have hderivRepr : HasDerivAt (fun w => f.holoRepr ((e.symm w : X)))
          (deriv ((fun p : poleZeroLocus f => f.holoRepr (p : X)) ∘ ⇑e.symm) z) z :=
        hAn.differentiableAt.hasDerivAt
      have hderivExp : HasDerivAt (fun w => Complex.exp (-(g' w)))
          (Complex.exp (-(g' z)) *
            -((f.holoRepr ((e.symm z : X)))⁻¹ *
                deriv ((fun p : poleZeroLocus f => f.holoRepr (p : X)) ∘ ⇑e.symm) z)) z :=
        hgz.neg.cexp
      have hprod := hderivRepr.mul hderivExp
      have hval : deriv ((fun p : poleZeroLocus f => f.holoRepr (p : X)) ∘ ⇑e.symm) z *
            Complex.exp (-(g' z)) +
          f.holoRepr ((e.symm z : X)) *
            (Complex.exp (-(g' z)) *
              -((f.holoRepr ((e.symm z : X)))⁻¹ *
                  deriv ((fun p : poleZeroLocus f => f.holoRepr (p : X)) ∘ ⇑e.symm) z)) = 0 := by
        have hcancel := mul_inv_cancel₀ hne
        linear_combination
          (-(deriv ((fun p : poleZeroLocus f => f.holoRepr (p : X)) ∘ ⇑e.symm) z *
            Complex.exp (-(g' z)))) * hcancel
      rwa [hval] at hprod
    have hφconst : φ =ᶠ[𝓝 (e p₀)] fun _ => φ (e p₀) :=
      RS.eventuallyEq_of_hasDerivAt_eq hφderiv
        (Filter.Eventually.of_forall fun z => hasDerivAt_const z (φ (e p₀))) rfl
    -- transport back along `t ↦ e (γ'.extend t)`, continuous at `t₀` with value `e p₀`
    have hktendsto : Tendsto (fun t => e (γ'.extend t)) (𝓝 t₀) (𝓝 (e p₀)) :=
      (e.continuousAt (mem_chart_source ℂ p₀)).comp γ'.continuous_extend.continuousAt
    have hHeq_of : ∀ {t : ℝ}, γ'.extend t ∈ e.source ∧ F t = g' (e (γ'.extend t)) →
        H t = φ (e (γ'.extend t)) := by
      intro t ht
      change f.holoRepr (γ.extend t) * Complex.exp (-(F t)) =
        f.holoRepr ((e.symm (e (γ'.extend t)) : X)) * Complex.exp (-(g' (e (γ'.extend t))))
      rw [e.left_inv ht.1, ← ht.2, Path.liftPoleZeroLocus_extend]
    have hHeq : ∀ᶠ t in 𝓝 t₀, H t = φ (e (γ'.extend t)) := hFeq'.mono fun t ht => hHeq_of ht
    have hHt₀ : H t₀ = φ (e p₀) := hHeq_of hFeq'.self_of_nhds
    filter_upwards [hHeq, hktendsto.eventually hφconst] with t ht1 ht2
    rw [ht1, ht2, hHt₀]
  have h0 : H 0 = 1 := by
    change f.holoRepr (γ.extend 0) * Complex.exp (-(F 0)) = 1
    rw [γ.extend_zero, ← hc₀, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  intro t
  have hHt : H t = H 0 := hlc.apply_eq_of_preconnectedSpace t 0
  rw [h0] at hHt
  have hexpand : H t * Complex.exp (F t) = f.holoRepr (γ.extend t) := by
    change f.holoRepr (γ.extend t) * Complex.exp (-(F t)) * Complex.exp (F t) =
      f.holoRepr (γ.extend t)
    rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  calc Complex.exp (F t) = 1 * Complex.exp (F t) := (one_mul _).symm
    _ = H t * Complex.exp (F t) := by rw [hHt]
    _ = f.holoRepr (γ.extend t) := hexpand

/-! ### Existence and uniqueness of a log branch with a prescribed initial value -/

/-- **Existence**, with a prescribed initial branch value: a continuous branch of `log f` along
any path avoiding the zeros/poles of `f`, starting at a chosen `c₀` with `exp c₀ = f.holoRepr x`. -/
theorem exists_logBranchAlong {f : ℳ X} (hf : f ≠ 0) {x y : X} (γ : Path x y)
    (hγ : ∀ t : ↥unitInterval, γ t ∉ (RS.divisor f).support) {c₀ : ℂ}
    (hc₀ : Complex.exp c₀ = f.holoRepr x) :
    ∃ F : ℝ → ℂ, RS.IsPrimitiveAlong (Path.liftPoleZeroLocus γ hγ)
      (dlogForm f hf) F ∧ F 0 = c₀ ∧ ∀ t : ℝ, Complex.exp (F t) = f.holoRepr (γ.extend t) := by
  obtain ⟨F₀, hF₀, hF₀0⟩ :=
    RS.exists_isPrimitiveAlong (Path.liftPoleZeroLocus γ hγ)
      (dlogForm f hf)
  refine ⟨fun t => F₀ t + c₀, hF₀.add_const c₀, by change F₀ 0 + c₀ = c₀; rw [hF₀0, zero_add], ?_⟩
  refine exp_eq_holoRepr_of_isPrimitiveAlong hf hγ (hF₀.add_const c₀) ?_
  show Complex.exp (F₀ 0 + c₀) = f.holoRepr x
  rw [hF₀0, zero_add]
  exact hc₀

/-- **Uniqueness** (free, from `Path`'s own `sub_eq_sub`): two branches agreeing at `t = 0` agree
everywhere — no new proof, a direct instantiation over the open locus. -/
theorem logBranchAlong_unique {f : ℳ X} (hf : f ≠ 0) {x y : X} {γ : Path x y}
    {hγ : ∀ t : ↥unitInterval, γ t ∉ (RS.divisor f).support} {F F' : ℝ → ℂ}
    (hF : RS.IsPrimitiveAlong (Path.liftPoleZeroLocus γ hγ)
      (dlogForm f hf) F)
    (hF' : RS.IsPrimitiveAlong (Path.liftPoleZeroLocus γ hγ)
      (dlogForm f hf) F')
    (h0 : F 0 = F' 0) : F = F' := by
  funext t
  have h := hF.sub_eq_sub isPreconnected_univ
    (Path.liftPoleZeroLocus γ hγ).continuous_extend.continuousOn
    hF' (mem_univ (0 : ℝ)) (mem_univ t)
  rw [h0, sub_self] at h
  exact sub_eq_zero.mp h

end RS.Monodromy

end

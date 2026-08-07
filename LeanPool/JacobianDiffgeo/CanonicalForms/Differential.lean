/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.CanonicalForms.Quotient

/-!
# `ofForm1`, the `ℳ(X)`-module structure, `d`, `dlog` (D7), data + quotient layers

Unit: canonical-forms (`docs/design/canonical-forms.md` §2 D7, §4.3, proof plan §5 P1).

Data layer (`MFormData`, raw):
* `MFormData.ofForm1`/`Form1.toMFormData`: the holomorphic special case, using `η`'s own analytic
  chart coefficients (`Form1.analyticOnNhd_coeffIn`) and the SAME transition rule `coeffIn_trans`
  already proves — no new computation.
* `MFormData.smul`: the `ℳ(X)`-action, via the canonical, choice-free `MeroGermOn.holoRepr`.
* `MFormData.d`: the differential of a meromorphic function; the `compat`-at-poles case split is
  isolated as the reusable `deriv_comp_chart_congr` (no hypothesis on the transported function —
  poles are handled by the junk-collapse argument in BOTH directions).

Quotient layer (`MForm`, the honest 1-form type):
* `MForm.ofForm1`/`Form1.toMForm : Form1 X →ₗ[ℂ] MForm X` (the design's frozen bridge name).
* `SMul (ℳ X) (MForm X)`, the **full `Module (ℳ X) (MForm X)` instance**, plus
  `IsScalarTower ℂ (ℳ X) (MForm X)`/`SMulCommClass ℂ (ℳ X) (MForm X)`. The module laws that FAIL
  for raw families (`add_smul`/`mul_smul`/`one_smul` need `holoRepr`-of-a-sum identities that
  break at poles) hold on the quotient: `holoRepr` of `f + g`/`f * g`/`c • f` agrees with the
  pointwise combination on `𝓝[≠] x` for EVERY `x` (`holoRepr_eventuallyEq_nhdsNE` against the
  combined representative), which is exactly the quotient's equality granularity.
* `MForm.d` with `MForm.d_add` (same mechanism: `(f+g).holoRepr` agrees with
  `f.holoRepr + g.holoRepr` near every center, and `deriv` respects punctured-neighborhood
  agreement, `Filter.EventuallyEq.nhdsNE_deriv`) and `MForm.d_const`.
* `MForm.dlog f := f⁻¹ • MForm.d f`, with the argument-principle atom `MForm.resAt_dlog`
  (junk-robust, no `f ≠ 0` hypothesis — via `MeromorphicAt.resAt_deriv_div`).
* `MForm.ord_smul_mero : (h • Θ).ord x = h.ord x + Θ.ord x` (the D10/D11 divisor dictionary's
  pointwise engine).
-/

open scoped ContDiff Manifold
open Set IsManifold Filter Topology

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

omit [IsManifold 𝓘(ℂ) ω X] in
/-- Chart-invariance of `DifferentiableAt`, both directions (spike-verified, `scratch_canon.lean`
item 4): if `g ∘ e.symm` is differentiable at `e p`, so is `g ∘ e'.symm` at `e' p`, for any two
maximal-atlas charts both containing `p`. No hypothesis on `g`. -/
theorem differentiableAt_comp_chart_of_mem_source {g : X → ℂ} {e e' : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω X) {p : X}
    (hp : p ∈ e.source) (hp' : p ∈ e'.source)
    (hd : DifferentiableAt ℂ (g ∘ ⇑e.symm) (e p)) :
    DifferentiableAt ℂ (g ∘ ⇑e'.symm) (e' p) := by
  have hτ : DifferentiableAt ℂ (⇑e ∘ ⇑e'.symm) (e' p) :=
    differentiableAt_trans he he' (e'.map_source hp') (by rw [e'.left_inv hp']; exact hp)
  have heq : (g ∘ ⇑e'.symm) =ᶠ[nhds (e' p)] (g ∘ ⇑e.symm) ∘ (⇑e ∘ ⇑e'.symm) := by
    have hCA : ContinuousAt (⇑e'.symm) (e' p) := e'.continuousAt_symm (e'.map_source hp')
    have h1 : ⇑e'.symm ⁻¹' e.source ∈ nhds (e' p) :=
      hCA.preimage_mem_nhds (by rw [e'.left_inv hp']; exact e.open_source.mem_nhds hp)
    filter_upwards [h1] with w hw
    simp only [Function.comp_apply, e.left_inv hw]
  rw [heq.differentiableAt_iff]
  have hτp : (⇑e ∘ ⇑e'.symm) (e' p) = e p := by
    simp only [Function.comp_apply]; rw [e'.left_inv hp']
  exact hτp ▸ hd |>.comp (e' p) hτ

omit [IsManifold 𝓘(ℂ) ω X] in
/-- **The unit's central new lemma** (P1, `scratch_canon.lean` item 4, generalized to a full
`by_cases` on differentiability): for ANY `g : X → ℂ` (no hypothesis at all — poles handled by the
junk-collapse of both sides to `0`), the derivative-through-charts transition rule. -/
theorem deriv_comp_chart_congr {g : X → ℂ} {e e' : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω X) {z : ℂ}
    (hz : z ∈ ⇑e' '' (e.source ∩ e'.source)) :
    deriv (g ∘ ⇑e'.symm) z = deriv (⇑e ∘ ⇑e'.symm) z * deriv (g ∘ ⇑e.symm) (e (e'.symm z)) := by
  obtain ⟨p, hp, rfl⟩ := hz
  have hsp : e'.symm (e' p) = p := e'.left_inv hp.2
  rw [hsp]
  by_cases hd : DifferentiableAt ℂ (g ∘ ⇑e.symm) (e p)
  · have hτ : DifferentiableAt ℂ (⇑e ∘ ⇑e'.symm) (e' p) :=
      differentiableAt_trans he he' (e'.map_source hp.2) (by rw [hsp]; exact hp.1)
    have heq : (g ∘ ⇑e'.symm) =ᶠ[nhds (e' p)] (g ∘ ⇑e.symm) ∘ (⇑e ∘ ⇑e'.symm) := by
      have hCA : ContinuousAt (⇑e'.symm) (e' p) := e'.continuousAt_symm (e'.map_source hp.2)
      have h1 : ⇑e'.symm ⁻¹' e.source ∈ nhds (e' p) :=
        hCA.preimage_mem_nhds (by rw [hsp]; exact e.open_source.mem_nhds hp.1)
      filter_upwards [h1] with w hw
      simp only [Function.comp_apply, e.left_inv hw]
    have hτp : (⇑e ∘ ⇑e'.symm) (e' p) = e p := by
      simp only [Function.comp_apply]; rw [hsp]
    rw [heq.deriv_eq, deriv_comp (e' p) (hτp ▸ hd) hτ, hτp]
    ring
  · have hd' : ¬ DifferentiableAt ℂ (g ∘ ⇑e'.symm) (e' p) := fun hcon =>
      hd (differentiableAt_comp_chart_of_mem_source he' he hp.2 hp.1 hcon)
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd', mul_zero]

/-! ### `MFormData.ofForm1`: the holomorphic special case (D7) -/

namespace MFormData

open scoped Classical in
/-- The holomorphic special case: a `Form1` gives an `MFormData` with the same chart coefficients
(no poles). `compat` is exactly `coeffIn_trans` — no new work. -/
noncomputable def ofForm1 (η : Form1 X) : MFormData X where
  coeffAt x z := if z ∈ (chartAt ℂ x).target then coeffIn (chartAt ℂ x) η z else 0
  coeffAt_zero_off x z hz := if_neg hz
  meromorphicOn_coeffAt x := by
    have hf : MeromorphicOn (coeffIn (chartAt ℂ x) η) (chartAt ℂ x).target :=
      (η.analyticOnNhd_coeffIn (chart_mem_maximalAtlas x)).meromorphicOn
    exact hf.congr (fun z hz => (if_pos hz).symm) (chartAt ℂ x).open_target
  compat x y z hz := by
    obtain ⟨p, hp, rfl⟩ := hz
    have hyt : chartAt ℂ y p ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hp.2
    have hxt : chartAt ℂ x ((chartAt ℂ y).symm (chartAt ℂ y p)) ∈ (chartAt ℂ x).target := by
      rw [(chartAt ℂ y).left_inv hp.2]; exact (chartAt ℂ x).map_source hp.1
    change
      (if chartAt ℂ y p ∈ (chartAt ℂ y).target then coeffIn (chartAt ℂ y) η (chartAt ℂ y p)
        else 0) =
      deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) (chartAt ℂ y p) *
        (if chartAt ℂ x ((chartAt ℂ y).symm (chartAt ℂ y p)) ∈ (chartAt ℂ x).target then
          coeffIn (chartAt ℂ x) η (chartAt ℂ x ((chartAt ℂ y).symm (chartAt ℂ y p))) else 0)
    rw [if_pos hyt, if_pos hxt]
    exact coeffIn_trans (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas y) η ⟨p, hp, rfl⟩

open scoped Classical in
theorem ofForm1_add (η η' : Form1 X) : ofForm1 (η + η') = ofForm1 η + ofForm1 η' := by
  ext x z hz
  change (if z ∈ (chartAt ℂ x).target then coeffIn (chartAt ℂ x) (η + η') z else 0) =
    (if z ∈ (chartAt ℂ x).target then coeffIn (chartAt ℂ x) η z else 0) +
      (if z ∈ (chartAt ℂ x).target then coeffIn (chartAt ℂ x) η' z else 0)
  rw [if_pos hz, if_pos hz, if_pos hz, coeffIn_add]

open scoped Classical in
theorem ofForm1_smul (c : ℂ) (η : Form1 X) : ofForm1 (c • η) = c • ofForm1 η := by
  ext x z hz
  change (if z ∈ (chartAt ℂ x).target then coeffIn (chartAt ℂ x) (c • η) z else 0) =
    c * (if z ∈ (chartAt ℂ x).target then coeffIn (chartAt ℂ x) η z else 0)
  rw [if_pos hz, if_pos hz, coeffIn_smul]

open scoped Classical in
theorem ofForm1_zero : ofForm1 (0 : Form1 X) = 0 := by
  ext x z hz
  change (if z ∈ (chartAt ℂ x).target then coeffIn (chartAt ℂ x) (0 : Form1 X) z else 0) = 0
  rw [if_pos hz, coeffIn_zero]

/-- The holomorphic-to-meromorphic bridge as a `ℂ`-linear map (item 3(d) of the task brief). -/
noncomputable def _root_.RS.Form1.toMFormData : Form1 X →ₗ[ℂ] MFormData X where
  toFun := ofForm1
  map_add' := ofForm1_add
  map_smul' := ofForm1_smul

/-- Holomorphic 1-forms give `MFormData`s with nonnegative order everywhere (they land in
`OmegaSpace 0`, D12/§6). -/
theorem ofForm1_ord_nonneg (η : Form1 X) (x : X) : 0 ≤ (ofForm1 η).ord x := by
  have heq : (ofForm1 η).coeffAt x =ᶠ[nhds (chartAt ℂ x x)] coeffIn (chartAt ℂ x) η := by
    filter_upwards [(chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x)] with z hz
    exact if_pos hz
  change 0 ≤ meromorphicOrderAt ((ofForm1 η).coeffAt x) (chartAt ℂ x x)
  rw [meromorphicOrderAt_congr (heq.filter_mono nhdsWithin_le_nhds)]
  exact (η.analyticAt_coeffAt x).meromorphicOrderAt_nonneg

/-! ### `MFormData.smul`: the `ℳ(X)`-module action (D7) -/

/-- Multiplication of a meromorphic 1-form by a meromorphic function, via the canonical,
choice-free representative `MeroGermOn.holoRepr`. -/
noncomputable def smul (h : ℳ X) (θ : MFormData X) : MFormData X where
  coeffAt x z := h.holoRepr ((chartAt ℂ x).symm z) * θ.coeffAt x z
  coeffAt_zero_off x z hz := by rw [θ.coeffAt_zero_off x z hz, mul_zero]
  meromorphicOn_coeffAt x := by
    have hh : MeromorphicOn (fun z => h.holoRepr ((chartAt ℂ x).symm z)) (chartAt ℂ x).target := by
      intro z₀ hz₀
      have hp₀ : (chartAt ℂ x).symm z₀ ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz₀
      have hiff := meromorphicAtX_iff_of_mem_source (f := h.holoRepr) (chart_mem_maximalAtlas x) hp₀
      have hz0 : (chartAt ℂ x) ((chartAt ℂ x).symm z₀) = z₀ := (chartAt ℂ x).right_inv hz₀
      rw [hz0] at hiff
      exact hiff.mp (MeroGermOn.meromorphicOnX_holoRepr isOpen_univ h _ (mem_univ _))
    exact hh.mul (θ.meromorphicOn_coeffAt x)
  compat x y z hz := by
    obtain ⟨p, hp, rfl⟩ := hz
    have hsy : (chartAt ℂ y).symm (chartAt ℂ y p) = p := (chartAt ℂ y).left_inv hp.2
    change h.holoRepr ((chartAt ℂ y).symm (chartAt ℂ y p)) * θ.coeffAt y (chartAt ℂ y p) =
      deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) (chartAt ℂ y p) *
        (h.holoRepr ((chartAt ℂ x).symm (chartAt ℂ x ((chartAt ℂ y).symm (chartAt ℂ y p)))) *
          θ.coeffAt x (chartAt ℂ x ((chartAt ℂ y).symm (chartAt ℂ y p))))
    rw [θ.compat x y (chartAt ℂ y p) ⟨p, hp, rfl⟩, hsy, (chartAt ℂ x).left_inv hp.1]
    ring

instance : SMul (ℳ X) (MFormData X) := ⟨smul⟩

@[simp] theorem coeffAt_smul_mero (h : ℳ X) (θ : MFormData X) (x : X) (z : ℂ) :
    (h • θ).coeffAt x z = h.holoRepr ((chartAt ℂ x).symm z) * θ.coeffAt x z := rfl

/-! ### `MFormData.d`: the differential of a meromorphic function (D7, P1) -/

open scoped Classical in
/-- The differential of a meromorphic function `f`, via `f.holoRepr` — a genuine,
`Classical.choice`-free function `ℳ X → MFormData X`. `compat` (the pole case-split) is
`deriv_comp_chart_congr` instantiated at `g := f.holoRepr`. -/
noncomputable def d (f : ℳ X) : MFormData X where
  coeffAt x z := if z ∈ (chartAt ℂ x).target then deriv (f.holoRepr ∘ (chartAt ℂ x).symm) z else 0
  coeffAt_zero_off x z hz := if_neg hz
  meromorphicOn_coeffAt x := by
    have hh : MeromorphicOn (deriv (f.holoRepr ∘ (chartAt ℂ x).symm)) (chartAt ℂ x).target := by
      intro z₀ hz₀
      have hp₀ : (chartAt ℂ x).symm z₀ ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz₀
      have hiff := meromorphicAtX_iff_of_mem_source (f := f.holoRepr) (chart_mem_maximalAtlas x) hp₀
      have hz0 : (chartAt ℂ x) ((chartAt ℂ x).symm z₀) = z₀ := (chartAt ℂ x).right_inv hz₀
      rw [hz0] at hiff
      have hmerof : MeromorphicAtX f.holoRepr ((chartAt ℂ x).symm z₀) :=
        MeroGermOn.meromorphicOnX_holoRepr isOpen_univ f _ (mem_univ _)
      exact (hiff.mp hmerof).deriv
    exact hh.congr (fun z hz => (if_pos hz).symm) (chartAt ℂ x).open_target
  compat x y z hz := by
    obtain ⟨p, hp, rfl⟩ := hz
    have hyt : chartAt ℂ y p ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hp.2
    have hxt : chartAt ℂ x ((chartAt ℂ y).symm (chartAt ℂ y p)) ∈ (chartAt ℂ x).target := by
      rw [(chartAt ℂ y).left_inv hp.2]; exact (chartAt ℂ x).map_source hp.1
    change
      (if chartAt ℂ y p ∈ (chartAt ℂ y).target then
        deriv (f.holoRepr ∘ ⇑(chartAt ℂ y).symm) (chartAt ℂ y p) else 0) =
      deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) (chartAt ℂ y p) *
        (if chartAt ℂ x ((chartAt ℂ y).symm (chartAt ℂ y p)) ∈ (chartAt ℂ x).target then
          deriv (f.holoRepr ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x ((chartAt ℂ y).symm
            (chartAt ℂ y p))) else 0)
    rw [if_pos hyt, if_pos hxt]
    exact deriv_comp_chart_congr (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas y) ⟨p, hp, rfl⟩

theorem coeffAt_d (f : ℳ X) (x : X) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target) :
    (d f).coeffAt x z = deriv (f.holoRepr ∘ ⇑(chartAt ℂ x).symm) z := if_pos hz

/-- `d` of a constant is `0` (no poles at all, hence no junk subtlety). -/
theorem d_const (c : ℂ) : d (algebraMap ℂ (ℳ X) c) = 0 := by
  have heq : (algebraMap ℂ (ℳ X) c).holoRepr = fun _ => c := by
    funext w
    change (algebraMap ℂ (ℳ X) c).evalAt w = c
    rw [MeroGermOn.algebraMap_mk]
    exact MeroGermOn.evalAt_mk_of_contMDiffAt isOpen_univ (mem_univ w) contMDiffAt_const
  ext x z hz
  rw [coeffAt_d _ x hz, coeffAt_zero]
  have heq' : (algebraMap ℂ (ℳ X) c).holoRepr ∘ ⇑(chartAt ℂ x).symm = fun _ => c := by
    rw [heq]; rfl
  rw [heq', deriv_const]

/-! ### `MFormData.dlog` -/

/-- The logarithmic differential `dlog f := f⁻¹ • df`. -/
noncomputable def dlog (f : ℳ X) : MFormData X := smul f⁻¹ (d f)

end MFormData

/-! ### `holoRepr` germ identities for the quotient module laws

`holoRepr` of a sum/product/scalar is NOT the pointwise combination (junk at poles), but it
AGREES with it on `𝓝[≠] x` for every `x` (`holoRepr_eventuallyEq_nhdsNE` read against the
combined representative) — exactly the granularity of `MFormData.Eqv`, which is why the
`Module (ℳ X) (MForm X)` laws hold on the quotient. -/

theorem Mero.holoRepr_add (f g : ℳ X) (x : X) :
    (f + g).holoRepr =ᶠ[𝓝[≠] x] f.holoRepr + g.holoRepr := by
  have hrep : MeroGermOn.mk (f.holoRepr + g.holoRepr)
      ((MeroGermOn.meromorphicOnX_holoRepr isOpen_univ f).add
        (MeroGermOn.meromorphicOnX_holoRepr isOpen_univ g)) = f + g := by
    rw [← MeroGermOn.mk_add, MeroGermOn.mk_holoRepr isOpen_univ f,
      MeroGermOn.mk_holoRepr isOpen_univ g]
    all_goals exact MeroGermOn.meromorphicOnX_holoRepr isOpen_univ _
  exact MeroGermOn.holoRepr_eventuallyEq_nhdsNE isOpen_univ (mem_univ x) (f + g) hrep

theorem Mero.holoRepr_mul (f g : ℳ X) (x : X) :
    (f * g).holoRepr =ᶠ[𝓝[≠] x] f.holoRepr * g.holoRepr := by
  have hrep : MeroGermOn.mk (f.holoRepr * g.holoRepr)
      ((MeroGermOn.meromorphicOnX_holoRepr isOpen_univ f).mul
        (MeroGermOn.meromorphicOnX_holoRepr isOpen_univ g)) = f * g := by
    rw [← MeroGermOn.mk_mul, MeroGermOn.mk_holoRepr isOpen_univ f,
      MeroGermOn.mk_holoRepr isOpen_univ g]
    all_goals exact MeroGermOn.meromorphicOnX_holoRepr isOpen_univ _
  exact MeroGermOn.holoRepr_eventuallyEq_nhdsNE isOpen_univ (mem_univ x) (f * g) hrep

theorem Mero.holoRepr_smul (c : ℂ) (f : ℳ X) (x : X) :
    (c • f).holoRepr =ᶠ[𝓝[≠] x] c • f.holoRepr := by
  have hrep : MeroGermOn.mk (c • f.holoRepr)
      ((MeroGermOn.meromorphicOnX_holoRepr isOpen_univ f).smul c) = c • f := by
    rw [← MeroGermOn.mk_smul, MeroGermOn.mk_holoRepr isOpen_univ f]
    all_goals exact MeroGermOn.meromorphicOnX_holoRepr isOpen_univ _
  exact MeroGermOn.holoRepr_eventuallyEq_nhdsNE isOpen_univ (mem_univ x) (c • f) hrep

theorem Mero.holoRepr_inv (f : ℳ X) (x : X) :
    f⁻¹.holoRepr =ᶠ[𝓝[≠] x] (f.holoRepr)⁻¹ := by
  have hrep : MeroGermOn.mk (f.holoRepr)⁻¹
      (MeroGermOn.meromorphicOnX_holoRepr isOpen_univ f).inv = f⁻¹ := by
    rw [← MeroGermOn.mk_inv, MeroGermOn.mk_holoRepr isOpen_univ f]
    all_goals exact MeroGermOn.meromorphicOnX_holoRepr isOpen_univ _
  exact MeroGermOn.holoRepr_eventuallyEq_nhdsNE isOpen_univ (mem_univ x) f⁻¹ hrep

theorem Mero.holoRepr_zero (x : X) :
    (0 : ℳ X).holoRepr =ᶠ[𝓝[≠] x] fun _ => (0 : ℂ) :=
  MeroGermOn.holoRepr_eventuallyEq_nhdsNE isOpen_univ (mem_univ x) 0 MeroGermOn.mk_zero

theorem Mero.holoRepr_one (x : X) :
    (1 : ℳ X).holoRepr =ᶠ[𝓝[≠] x] fun _ => (1 : ℂ) :=
  MeroGermOn.holoRepr_eventuallyEq_nhdsNE isOpen_univ (mem_univ x) 1 MeroGermOn.mk_one

/-- The order of a meromorphic-function class, read through `holoRepr` in the preferred chart
(the form the `ord_smul_mero` dictionary consumes). -/
theorem Mero.ord_eq_meromorphicOrderAt_holoRepr (f : ℳ X) (x : X) :
    f.ord x = meromorphicOrderAt (f.holoRepr ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) := by
  conv_lhs => rw [← MeroGermOn.mk_holoRepr isOpen_univ f]
  exact MeroGermOn.ord_mk isOpen_univ (mem_univ x)

/-! ### Quotient layer: `MForm.ofForm1`, the `Module (ℳ X)` structure, `MForm.d`, `MForm.dlog` -/

namespace MForm

/-- D7: the holomorphic embedding, on classes. -/
noncomputable def ofForm1 (η : Form1 X) : MForm X := mk (MFormData.ofForm1 η)

theorem ofForm1_ord_nonneg (η : Form1 X) (x : X) : 0 ≤ (ofForm1 η).ord x :=
  MFormData.ofForm1_ord_nonneg η x

/-- The holomorphic-to-meromorphic bridge as a `ℂ`-linear map (the design's frozen name,
targeting the QUOTIENT; the raw version is `Form1.toMFormData`). -/
noncomputable def _root_.RS.Form1.toMForm : Form1 X →ₗ[ℂ] MForm X where
  toFun := ofForm1
  map_add' η η' := congrArg mk (MFormData.ofForm1_add η η')
  map_smul' c η := congrArg mk (MFormData.ofForm1_smul c η)

open scoped Classical in
/-- `ofForm1` is injective into classes: punctured-neighborhood agreement of the ANALYTIC
coefficients at each center forces value agreement at the center by continuity (D12's
injectivity half). -/
theorem ofForm1_injective : Function.Injective (ofForm1 : Form1 X → MForm X) := by
  intro η η' h
  have hEqv := mk_eq_mk.1 h
  refine Form1.ext_coeffAt fun x => ?_
  have htarget : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), z ∈ (chartAt ℂ x).target :=
    eventually_nhdsWithin_of_eventually_nhds
      ((chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x))
  have h2 : coeffIn (chartAt ℂ x) η =ᶠ[𝓝[≠] (chartAt ℂ x x)] coeffIn (chartAt ℂ x) η' := by
    filter_upwards [hEqv x, htarget] with z hz hzt
    have hL : (MFormData.ofForm1 η).coeffAt x z = coeffIn (chartAt ℂ x) η z := by
      change (if z ∈ (chartAt ℂ x).target then coeffIn (chartAt ℂ x) η z else 0) = _
      rw [if_pos hzt]
    have hR : (MFormData.ofForm1 η').coeffAt x z = coeffIn (chartAt ℂ x) η' z := by
      change (if z ∈ (chartAt ℂ x).target then coeffIn (chartAt ℂ x) η' z else 0) = _
      rw [if_pos hzt]
    rw [← hL, ← hR]
    exact hz
  have hη : Tendsto (coeffIn (chartAt ℂ x) η) (𝓝[≠] (chartAt ℂ x x))
      (𝓝 (coeffIn (chartAt ℂ x) η (chartAt ℂ x x))) :=
    (η.analyticAt_coeffAt x).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hη' : Tendsto (coeffIn (chartAt ℂ x) η') (𝓝[≠] (chartAt ℂ x x))
      (𝓝 (coeffIn (chartAt ℂ x) η' (chartAt ℂ x x))) :=
    (η'.analyticAt_coeffAt x).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  change coeffIn (chartAt ℂ x) η (chartAt ℂ x x) = coeffIn (chartAt ℂ x) η' (chartAt ℂ x x)
  exact tendsto_nhds_unique (hη.congr' h2) hη'

/-! #### The `ℳ(X)`-module structure -/

noncomputable instance : SMul (ℳ X) (MForm X) :=
  ⟨fun h => Quotient.map (fun θ => MFormData.smul h θ) fun θ θ' hθ x => by
    filter_upwards [hθ x] with z hz
    change h.holoRepr ((chartAt ℂ x).symm z) * θ.coeffAt x z =
      h.holoRepr ((chartAt ℂ x).symm z) * θ'.coeffAt x z
    rw [hz]⟩

@[simp] theorem mero_smul_mk (h : ℳ X) (θ : MFormData X) :
    h • mk θ = mk (MFormData.smul h θ) := rfl

noncomputable instance : Module (ℳ X) (MForm X) where
  one_smul Θ := by
    obtain ⟨θ, rfl⟩ := exists_rep Θ
    refine sound fun x => ?_
    have h1 := eventuallyEq_nhdsNE_comp_chart_iff.mp (Mero.holoRepr_one (X := X) x)
    filter_upwards [h1] with z hz
    simp only [Function.comp_apply] at hz
    change (1 : ℳ X).holoRepr ((chartAt ℂ x).symm z) * θ.coeffAt x z = θ.coeffAt x z
    rw [hz, one_mul]
  mul_smul h h' Θ := by
    obtain ⟨θ, rfl⟩ := exists_rep Θ
    refine sound fun x => ?_
    have h1 := eventuallyEq_nhdsNE_comp_chart_iff.mp (Mero.holoRepr_mul h h' x)
    filter_upwards [h1] with z hz
    simp only [Function.comp_apply, Pi.mul_apply] at hz
    change (h * h').holoRepr ((chartAt ℂ x).symm z) * θ.coeffAt x z =
      h.holoRepr ((chartAt ℂ x).symm z) * (h'.holoRepr ((chartAt ℂ x).symm z) * θ.coeffAt x z)
    rw [hz]
    ring
  smul_zero h := sound fun x => Filter.Eventually.of_forall fun z => by
    change h.holoRepr ((chartAt ℂ x).symm z) * (0 : MFormData X).coeffAt x z =
      (0 : MFormData X).coeffAt x z
    simp
  smul_add h Θ₁ Θ₂ := by
    refine Quotient.inductionOn₂ Θ₁ Θ₂ fun θ η => ?_
    refine sound fun x => Filter.Eventually.of_forall fun z => ?_
    change h.holoRepr ((chartAt ℂ x).symm z) * (θ + η).coeffAt x z =
      h.holoRepr ((chartAt ℂ x).symm z) * θ.coeffAt x z +
        h.holoRepr ((chartAt ℂ x).symm z) * η.coeffAt x z
    simp only [MFormData.coeffAt_add]
    ring
  add_smul h h' Θ := by
    obtain ⟨θ, rfl⟩ := exists_rep Θ
    refine sound fun x => ?_
    have h1 := eventuallyEq_nhdsNE_comp_chart_iff.mp (Mero.holoRepr_add h h' x)
    filter_upwards [h1] with z hz
    simp only [Function.comp_apply, Pi.add_apply] at hz
    change (h + h').holoRepr ((chartAt ℂ x).symm z) * θ.coeffAt x z =
      h.holoRepr ((chartAt ℂ x).symm z) * θ.coeffAt x z +
        h'.holoRepr ((chartAt ℂ x).symm z) * θ.coeffAt x z
    rw [hz]
    ring
  zero_smul Θ := by
    obtain ⟨θ, rfl⟩ := exists_rep Θ
    refine sound fun x => ?_
    have h1 := eventuallyEq_nhdsNE_comp_chart_iff.mp (Mero.holoRepr_zero (X := X) x)
    filter_upwards [h1] with z hz
    simp only [Function.comp_apply] at hz
    change (0 : ℳ X).holoRepr ((chartAt ℂ x).symm z) * θ.coeffAt x z =
      (0 : MFormData X).coeffAt x z
    rw [hz, zero_mul]
    rfl

instance : IsScalarTower ℂ (ℳ X) (MForm X) where
  smul_assoc c h Θ := by
    obtain ⟨θ, rfl⟩ := exists_rep Θ
    refine sound fun x => ?_
    have h1 := eventuallyEq_nhdsNE_comp_chart_iff.mp (Mero.holoRepr_smul c h x)
    filter_upwards [h1] with z hz
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at hz
    change (c • h).holoRepr ((chartAt ℂ x).symm z) * θ.coeffAt x z =
      c * (h.holoRepr ((chartAt ℂ x).symm z) * θ.coeffAt x z)
    rw [hz]
    ring

instance : SMulCommClass ℂ (ℳ X) (MForm X) where
  smul_comm c h Θ := by
    obtain ⟨θ, rfl⟩ := exists_rep Θ
    refine sound fun x => Filter.Eventually.of_forall fun z => ?_
    change c * (h.holoRepr ((chartAt ℂ x).symm z) * θ.coeffAt x z) =
      h.holoRepr ((chartAt ℂ x).symm z) * (c * θ.coeffAt x z)
    ring

/-- The order dictionary for the `ℳ(X)`-action: orders add (the D10/D11 engine). Junk-robust —
no nonvanishing hypotheses (`⊤`-arithmetic absorbs the degenerate cases). -/
theorem ord_smul_mero (h : ℳ X) (Θ : MForm X) (x : X) :
    (h • Θ).ord x = h.ord x + Θ.ord x := by
  obtain ⟨θ, rfl⟩ := exists_rep Θ
  have h1 : MeromorphicAt (h.holoRepr ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
    MeroGermOn.meromorphicOnX_holoRepr isOpen_univ h x (mem_univ x)
  have h2 : MeromorphicAt (θ.coeffAt x) (chartAt ℂ x x) := θ.meromorphicAt_coeffAt x
  have hmul := meromorphicOrderAt_mul h1 h2
  change meromorphicOrderAt ((MFormData.smul h θ).coeffAt x) (chartAt ℂ x x) = _
  have hfun : (MFormData.smul h θ).coeffAt x =
      (h.holoRepr ∘ ⇑(chartAt ℂ x).symm) * θ.coeffAt x := rfl
  rw [hfun, hmul, ← Mero.ord_eq_meromorphicOrderAt_holoRepr h x]
  rfl

/-! #### `MForm.d` and `MForm.dlog` -/

/-- D7: the differential of a meromorphic function, on classes (a genuine,
`Classical.choice`-free function `ℳ X → MForm X` via `holoRepr`). -/
noncomputable def d (f : ℳ X) : MForm X := mk (MFormData.d f)

theorem d_const (c : ℂ) : d (algebraMap ℂ (ℳ X) c) = 0 :=
  congrArg mk (MFormData.d_const c)

open scoped Classical in
/-- Additivity of the differential — FALSE at the raw-family level (junk of `holoRepr` at the
poles of the summands), true on the quotient: `(f+g).holoRepr` agrees with
`f.holoRepr + g.holoRepr` near every center, and `deriv` respects punctured agreement. -/
theorem d_add (f g : ℳ X) : d (f + g) = d f + d g := by
  refine sound fun x => ?_
  have htarget : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), z ∈ (chartAt ℂ x).target :=
    eventually_nhdsWithin_of_eventually_nhds
      ((chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x))
  have hadd : ((f + g).holoRepr ∘ ⇑(chartAt ℂ x).symm) =ᶠ[𝓝[≠] (chartAt ℂ x x)]
      ((f.holoRepr + g.holoRepr) ∘ ⇑(chartAt ℂ x).symm) :=
    eventuallyEq_nhdsNE_comp_chart_iff.mp (Mero.holoRepr_add f g x)
  have hderiv := hadd.nhdsNE_deriv
  have hfm : MeromorphicAt (f.holoRepr ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
    MeroGermOn.meromorphicOnX_holoRepr isOpen_univ f x (mem_univ x)
  have hgm : MeromorphicAt (g.holoRepr ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
    MeroGermOn.meromorphicOnX_holoRepr isOpen_univ g x (mem_univ x)
  filter_upwards [htarget, hderiv, hfm.eventually_analyticAt, hgm.eventually_analyticAt] with
    z hz hdz hfz hgz
  change (if z ∈ (chartAt ℂ x).target then deriv ((f + g).holoRepr ∘ ⇑(chartAt ℂ x).symm) z
      else 0) =
    (if z ∈ (chartAt ℂ x).target then deriv (f.holoRepr ∘ ⇑(chartAt ℂ x).symm) z else 0) +
      (if z ∈ (chartAt ℂ x).target then deriv (g.holoRepr ∘ ⇑(chartAt ℂ x).symm) z else 0)
  rw [if_pos hz, if_pos hz, if_pos hz, hdz]
  have hsplit : (f.holoRepr + g.holoRepr) ∘ ⇑(chartAt ℂ x).symm =
      (f.holoRepr ∘ ⇑(chartAt ℂ x).symm) + (g.holoRepr ∘ ⇑(chartAt ℂ x).symm) := rfl
  rw [hsplit, deriv_add hfz.differentiableAt hgz.differentiableAt]

/-- D7: the logarithmic differential, on classes. -/
noncomputable def dlog (f : ℳ X) : MForm X := f⁻¹ • d f

open scoped Classical in
/-- **The argument-principle atom** (design §4.3 item 4): the residue of `dlog f` at `x` is the
order of `f` at `x`. Junk-robust: no `f ≠ 0` hypothesis (for `f = 0` both sides are `0`). -/
theorem resAt_dlog (f : ℳ X) (x : X) :
    (dlog f).resAt x = ((f.ord x).untop₀ : ℂ) := by
  have hFm : MeromorphicAt (f.holoRepr ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
    MeroGermOn.meromorphicOnX_holoRepr isOpen_univ f x (mem_univ x)
  have htarget : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), z ∈ (chartAt ℂ x).target :=
    eventually_nhdsWithin_of_eventually_nhds
      ((chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x))
  have hinv : (f⁻¹.holoRepr ∘ ⇑(chartAt ℂ x).symm) =ᶠ[𝓝[≠] (chartAt ℂ x x)]
      ((f.holoRepr)⁻¹ ∘ ⇑(chartAt ℂ x).symm) :=
    eventuallyEq_nhdsNE_comp_chart_iff.mp (Mero.holoRepr_inv f x)
  have hcoeff : (MFormData.smul f⁻¹ (MFormData.d f)).coeffAt x =ᶠ[𝓝[≠] (chartAt ℂ x x)]
      fun z => deriv (f.holoRepr ∘ ⇑(chartAt ℂ x).symm) z /
        (f.holoRepr ∘ ⇑(chartAt ℂ x).symm) z := by
    filter_upwards [htarget, hinv] with z hz hzinv
    simp only [Function.comp_apply, Pi.inv_apply] at hzinv
    change f⁻¹.holoRepr ((chartAt ℂ x).symm z) *
        (if z ∈ (chartAt ℂ x).target then deriv (f.holoRepr ∘ ⇑(chartAt ℂ x).symm) z else 0) = _
    rw [if_pos hz, hzinv]
    show (f.holoRepr ((chartAt ℂ x).symm z))⁻¹ * deriv (f.holoRepr ∘ ⇑(chartAt ℂ x).symm) z =
      deriv (f.holoRepr ∘ ⇑(chartAt ℂ x).symm) z / (f.holoRepr ∘ ⇑(chartAt ℂ x).symm) z
    rw [div_eq_mul_inv, mul_comm]
    rfl
  have hres : (dlog f).resAt x = RS.resAt (fun z => deriv (f.holoRepr ∘ ⇑(chartAt ℂ x).symm) z /
      (f.holoRepr ∘ ⇑(chartAt ℂ x).symm) z) (chartAt ℂ x x) := by
    change RS.resAt ((MFormData.smul f⁻¹ (MFormData.d f)).coeffAt x) (chartAt ℂ x x) = _
    exact resAt_congr hcoeff
  rw [hres, MeromorphicAt.resAt_deriv_div hFm, ← Mero.ord_eq_meromorphicOrderAt_holoRepr f x]

end MForm

end RS

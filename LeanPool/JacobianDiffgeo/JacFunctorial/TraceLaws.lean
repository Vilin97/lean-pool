/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.JacFunctorial.Trace
import LeanPool.JacobianDiffgeo.ProperDegree.ChallengeDegree

/-!
# Functoriality laws and the projection formula for `Form1.trace` (jacobian-functoriality §6.5, §9)

Unit: jacobian-functoriality. The `Form1`-level laws feeding the Jacobian-level pullback
functoriality and `pushforward_pullback`:

* `RS.Form1.trace_id` — `Tr_id = id`.
* `RS.Form1.trace_comp` — `Tr_{g∘f} = Tr_g ∘ Tr_f` (via the doubly-regular density argument).
* `RS.Form1.trace_pullback` — the projection formula `Tr_f (f^* η) = (deg f) • η`.

All three are proved at regular values via `RS.coeffAt_traceForm_of_isRegularValue` and extended
everywhere by `RS.Form1.eq_of_eqOn_dense` (density of regular values).
-/

open scoped ContDiff Manifold Topology
open Set Filter Metric IsManifold

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-! ### Nonvanishing of the chart-read derivative at unramified points -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [T2Space Y] [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/-- At a point where `f` reads as `z ↦ z^1` in adapted charts, the chart-read derivative of `f`
does not vanish. -/
theorem deriv_chartRead_ne_zero {f : X → Y} {x : X} {k : ℕ} (A : RS.AdaptedChartsAt f x k)
    (hk : k = 1) {e₀ : OpenPartialHomeomorph Y ℂ} (he₀ : e₀ ∈ maximalAtlas 𝓘(ℂ) ω Y)
    (hfx : f x ∈ e₀.source) :
    deriv (⇑e₀ ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) ≠ 0 := by
  subst hk
  rw [deriv_chartRead_eq_of_adapted A he₀ A.mem_source hfx]
  have hprod := deriv_transition_mul he₀ A.mem_maximalAtlas' hfx (A.mapsTo A.mem_source)
  have hT : deriv (⇑e₀ ∘ ⇑A.e'.symm) (A.e' (f x)) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hprod
    exact zero_ne_one hprod
  have hB := deriv_transition_ne_zero A.mem_maximalAtlas A.mem_source
  simp only [Nat.cast_one, Nat.sub_self, pow_zero, mul_one]
  exact mul_ne_zero hT hB

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- `X` (a positive-dimensional charted space) carries no constant identity: `id` is
nonconstant. -/
theorem not_exists_const_id : ¬ ∃ c : X, ∀ x : X, (id : X → X) x = c := by
  rintro ⟨c, hc⟩
  have hne : (𝓝[≠] (c : X)).NeBot := RS.nhdsNE_neBot c
  obtain ⟨z, hz⟩ : ∃ z : X, z ≠ c := by
    by_contra h'
    push Not at h'
    have hempty : ({c}ᶜ : Set X) = ∅ := by
      ext u
      simp [h' u]
    have hbot : (𝓝[≠] (c : X)) = ⊥ := by
      unfold nhdsWithin
      rw [hempty]
      simp
    exact hne.ne hbot
  exact hz (hc z)

/-! ### `trace_id` -/

theorem Form1.trace_id : Form1.trace (id : X → X) contMDiff_id = LinearMap.id := by
  have hne : ¬ ∃ c : X, ∀ x : X, (id : X → X) x = c := not_exists_const_id
  apply LinearMap.ext
  intro η
  rw [Form1.trace_apply contMDiff_id hne η, LinearMap.id_apply]
  apply Form1.eq_of_eqOn_dense (s := (Set.univ : Set X)) dense_univ
  intro yhat _
  have hreg : RS.IsRegularValue (id : X → X) yhat := by
    intro x _ hram
    have hnc : ¬ Filter.EventuallyConst (id : X → X) (𝓝 x) :=
      RS.not_eventuallyConst contMDiff_id hne x
    have h1 : RS.multiplicity (id : X → X) x = 1 :=
      (RS.multiplicity_eq_one_iff_injOn contMDiffAt_id hnc).mpr
        ⟨Set.univ, Filter.univ_mem, fun a _ b _ h => h⟩
    have h2 : 2 ≤ RS.multiplicity (id : X → X) x := hram
    omega
  change coeffAt yhat (traceForm contMDiff_id hne η) = coeffAt yhat η
  rw [coeffAt_traceForm_of_isRegularValue contMDiff_id hne η hreg]
  have hfib : (id : X → X) ⁻¹' {yhat} = {yhat} := by
    ext u
    simp
  rw [hfib, finsum_mem_singleton]
  change (deriv (⇑(chartAt ℂ yhat) ∘ (id : X → X) ∘ ⇑(chartAt ℂ yhat).symm) (chartAt ℂ yhat yhat))⁻¹
      * coeffAt yhat η = coeffAt yhat η
  have hid : (⇑(chartAt ℂ yhat) ∘ (id : X → X) ∘ ⇑(chartAt ℂ yhat).symm)
      =ᶠ[𝓝 (chartAt ℂ yhat yhat)] id := by
    filter_upwards [(chartAt ℂ yhat).open_target.mem_nhds (mem_chart_target ℂ yhat)] with z hz
    simp only [Function.comp_apply, id_eq]
    exact (chartAt ℂ yhat).right_inv hz
  rw [hid.deriv_eq, deriv_id, inv_one, one_mul]

/-! ### `trace_comp` -/

section Comp

variable [CompactSpace Y] [ConnectedSpace Y]
variable {Z : Type*} [TopologicalSpace Z] [T2Space Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
variable {f : X → Y} {g : Y → Z}

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [T2Space Z] [IsManifold 𝓘(ℂ, ℂ) ω Z] in
/-- Chain rule for `qCoeff`: the canonical coefficient of a composite splits through the
preferred chart at the intermediate point. Unconditional (junk-inverse compatible). -/
theorem qCoeff_comp (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    {e₂ : OpenPartialHomeomorph Z ℂ} (he₂ : e₂ ∈ maximalAtlas 𝓘(ℂ) ω Z)
    {x : X} (hgfx : g (f x) ∈ e₂.source) (η : Form1 X) :
    qCoeff (g ∘ f) η e₂ x
      = (deriv (⇑e₂ ∘ g ∘ ⇑(chartAt ℂ (f x)).symm) (chartAt ℂ (f x) (f x)))⁻¹
        * qCoeff f η (chartAt ℂ (f x)) x := by
  have hsymm0 : (chartAt ℂ x).symm (chartAt ℂ x x) = x :=
    (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have hptr : (⇑(chartAt ℂ (f x)) ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)
      = chartAt ℂ (f x) (f x) := by
    simp only [Function.comp_apply, hsymm0]
  have houter : DifferentiableAt ℂ (⇑e₂ ∘ g ∘ ⇑(chartAt ℂ (f x)).symm)
      ((⇑(chartAt ℂ (f x)) ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)) := by
    rw [hptr]
    exact (analyticAt_of_mem_maximalAtlas (hg (f x)) (chart_mem_maximalAtlas (f x))
      (mem_chart_source ℂ (f x)) he₂ hgfx).differentiableAt
  have hinner : DifferentiableAt ℂ (⇑(chartAt ℂ (f x)) ∘ f ∘ ⇑(chartAt ℂ x).symm)
      (chartAt ℂ x x) :=
    (analyticAt_of_mem_maximalAtlas (hf x) (chart_mem_maximalAtlas x) (mem_chart_source ℂ x)
      (chart_mem_maximalAtlas (f x)) (mem_chart_source ℂ (f x))).differentiableAt
  have heq : (⇑e₂ ∘ (g ∘ f) ∘ ⇑(chartAt ℂ x).symm) =ᶠ[𝓝 (chartAt ℂ x x)]
      (⇑e₂ ∘ g ∘ ⇑(chartAt ℂ (f x)).symm) ∘ (⇑(chartAt ℂ (f x)) ∘ f ∘ ⇑(chartAt ℂ x).symm) := by
    have hcont : ContinuousAt (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) := by
      have hfc : ContinuousAt f ((chartAt ℂ x).symm (chartAt ℂ x x)) := by
        rw [hsymm0]
        exact (hf x).continuousAt
      exact hfc.comp ((chartAt ℂ x).continuousAt_symm (mem_chart_target ℂ x))
    have hmem : (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) ∈ (chartAt ℂ (f x)).source := by
      simp only [Function.comp_apply, hsymm0]
      exact mem_chart_source ℂ (f x)
    filter_upwards [hcont.preimage_mem_nhds
      ((chartAt ℂ (f x)).open_source.mem_nhds hmem)] with z hz
    have hz' : f ((chartAt ℂ x).symm z) ∈ (chartAt ℂ (f x)).source := hz
    simp only [Function.comp_apply, (chartAt ℂ (f x)).left_inv hz']
  have hD := deriv_eq_of_eventuallyEq_comp' houter hinner heq
  change (deriv (⇑e₂ ∘ (g ∘ f) ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x))⁻¹ * coeffAt x η
    = (deriv (⇑e₂ ∘ g ∘ ⇑(chartAt ℂ (f x)).symm) (chartAt ℂ (f x) (f x)))⁻¹
      * ((deriv (⇑(chartAt ℂ (f x)) ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x))⁻¹
          * coeffAt x η)
  rw [hD, hptr, mul_inv]
  ring

/-- **`trace_comp`**: the trace is functorial, `Tr_{g∘f} = Tr_g ∘ Tr_f`. -/
theorem Form1.trace_comp (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    Form1.trace (g ∘ f) (hg.comp hf) = (Form1.trace g hg).comp (Form1.trace f hf) := by
  by_cases hfc : ∃ c, ∀ x, f x = c
  · obtain ⟨c, hc⟩ := hfc
    have hgfc : ∃ d, ∀ x, (g ∘ f) x = d := ⟨g c, fun x => by simp [Function.comp, hc x]⟩
    rw [Form1.trace_of_forall_eq (hg.comp hf) hgfc, Form1.trace_of_forall_eq hf ⟨c, hc⟩,
      LinearMap.comp_zero]
  · by_cases hgc : ∃ c, ∀ y, g y = c
    · obtain ⟨c, hc⟩ := hgc
      have hgfc : ∃ d, ∀ x, (g ∘ f) x = d := ⟨c, fun x => hc (f x)⟩
      rw [Form1.trace_of_forall_eq (hg.comp hf) hgfc, Form1.trace_of_forall_eq hg ⟨c, hc⟩,
        LinearMap.zero_comp]
    · have hgfne : ¬ ∃ c, ∀ x, (g ∘ f) x = c := by
        rintro ⟨c, hc⟩
        apply hgc
        refine ⟨c, fun y => ?_⟩
        obtain ⟨x, rfl⟩ := RS.surjective_of_not_const' hf hfc y
        exact hc x
      apply LinearMap.ext
      intro η
      rw [Form1.trace_apply (hg.comp hf) hgfne η, LinearMap.comp_apply,
        Form1.trace_apply hf hfc η, Form1.trace_apply hg hgc (traceForm hf hfc η)]
      set B : Set Z := branchLocus (g ∘ f) ∪ (branchLocus g ∪ g '' branchLocus f) with hB_def
      have hBfin : B.Finite :=
        (RS.branchLocus_finite (hg.comp hf) hgfne).union
          ((RS.branchLocus_finite hg hgc).union ((RS.branchLocus_finite hf hfc).image g))
      have hdense : Dense Bᶜ := by
        rw [← interior_eq_empty_iff_dense_compl, Set.eq_empty_iff_forall_notMem]
        intro z hz
        exact (infinite_of_mem_nhds z (mem_interior_iff_mem_nhds.mp hz)) hBfin
      apply Form1.eq_of_eqOn_dense hdense
      intro z₀ hz₀
      have hreg_gf : RS.IsRegularValue (g ∘ f) z₀ :=
        (RS.isRegularValue_iff_notMem_branchLocus _ _).mpr fun h => hz₀ (Or.inl h)
      have hreg_g : RS.IsRegularValue g z₀ :=
        (RS.isRegularValue_iff_notMem_branchLocus _ _).mpr fun h => hz₀ (Or.inr (Or.inl h))
      have hnimg : z₀ ∉ g '' branchLocus f := fun h => hz₀ (Or.inr (Or.inr h))
      change coeffAt z₀ (traceForm (hg.comp hf) hgfne η)
        = coeffAt z₀ (traceForm hg hgc (traceForm hf hfc η))
      rw [coeffAt_traceForm_of_isRegularValue (hg.comp hf) hgfne η hreg_gf,
        coeffAt_traceForm_of_isRegularValue hg hgc (traceForm hf hfc η) hreg_g]
      have hstep : ∀ y ∈ g ⁻¹' {z₀}, qCoeff g (traceForm hf hfc η) (chartAt ℂ z₀) y
          = ∑ᶠ x ∈ f ⁻¹' {y}, qCoeff (g ∘ f) η (chartAt ℂ z₀) x := by
        intro y hy
        have hgy : g y = z₀ := hy
        have hyreg : RS.IsRegularValue f y := by
          rw [RS.isRegularValue_iff_notMem_branchLocus]
          intro hyB
          exact hnimg ⟨y, hyB, hgy⟩
        change (deriv (⇑(chartAt ℂ z₀) ∘ g ∘ ⇑(chartAt ℂ y).symm) (chartAt ℂ y y))⁻¹
            * coeffAt y (traceForm hf hfc η)
          = ∑ᶠ x ∈ f ⁻¹' {y}, qCoeff (g ∘ f) η (chartAt ℂ z₀) x
        rw [coeffAt_traceForm_of_isRegularValue hf hfc η hyreg, mul_finsum_mem]
        apply finsum_mem_congr rfl
        intro x hx
        have hfx : f x = y := hx
        have hgfx : g (f x) ∈ (chartAt ℂ z₀).source := by
          rw [hfx, hgy]
          exact mem_chart_source ℂ z₀
        rw [qCoeff_comp hf hg (chart_mem_maximalAtlas z₀) hgfx η, hfx]
      rw [finsum_mem_congr rfl hstep]
      have hI : (g ⁻¹' {z₀}).Finite := RS.fiber_finite hg hgc z₀
      have ht : ∀ y ∈ g ⁻¹' {z₀}, (f ⁻¹' {y}).Finite := fun y _ => RS.fiber_finite hf hfc y
      have hdisj : (g ⁻¹' {z₀}).PairwiseDisjoint (fun y => f ⁻¹' {y}) := by
        intro y₁ _ y₂ _ hne12
        apply Set.disjoint_left.mpr
        intro x hx1 hx2
        exact hne12 ((hx1 : f x = y₁) ▸ (hx2 : f x = y₂))
      have hunion : (⋃ y ∈ g ⁻¹' {z₀}, f ⁻¹' {y}) = (g ∘ f) ⁻¹' {z₀} := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
          Function.comp_apply]
        constructor
        · rintro ⟨y, hy, hxy⟩
          rw [hxy]
          exact hy
        · intro h
          exact ⟨f x, h, rfl⟩
      rw [← finsum_mem_biUnion hdisj hI ht, hunion]

end Comp

/-! ### The projection formula -/

section Projection

variable [CompactSpace Y] [ConnectedSpace Y]
variable {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hne : ¬ ∃ c, ∀ x, f x = c)

include hf hne in
omit [CompactSpace Y] [ConnectedSpace Y] [T2Space X] [CompactSpace X] in
/-- Per-point cancellation: the canonical trace coefficient of a pulled-back form at an
unramified fibre point is the coefficient of the original form. -/
theorem qCoeff_pullback {yhat : Y} (hyhat : RS.IsRegularValue f yhat) {x : X} (hx : f x = yhat)
    (η : Form1 Y) :
    qCoeff f (Form1.pullback f hf η) (chartAt ℂ yhat) x = coeffAt yhat η := by
  subst hx
  have hmult : RS.multiplicity f x = 1 :=
    RS.multiplicity_eq_one_of_isRegularValue hf hne hyhat rfl
  obtain ⟨A, -⟩ := RS.exists_adaptedChartsAt (hf x) (RS.not_eventuallyConst hf hne x)
    (Filter.univ_mem)
  have hDne : deriv (⇑(chartAt ℂ (f x)) ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) ≠ 0 :=
    deriv_chartRead_ne_zero A hmult (chart_mem_maximalAtlas (f x)) (mem_chart_source ℂ (f x))
  change (deriv (⇑(chartAt ℂ (f x)) ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x))⁻¹
      * coeffAt x (Form1.pullback f hf η) = coeffAt (f x) η
  rw [coeffAt_pullback, ← mul_assoc, inv_mul_cancel₀ hDne, one_mul]

omit [CompactSpace Y] in
/-- **The projection formula (raw form)**: `Tr_f (f^* η) = (deg f) • η`. -/
theorem traceForm_pullback (η : Form1 Y) :
    traceForm hf hne (Form1.pullback f hf η) = (RS.degree f : ℂ) • η := by
  apply Form1.eq_of_eqOn_dense (RS.dense_setOf_isRegularValue hf hne)
  intro yhat hyhat
  change coeffAt yhat (traceForm hf hne (Form1.pullback f hf η))
    = coeffAt yhat ((RS.degree f : ℂ) • η)
  rw [coeffAt_traceForm_of_isRegularValue hf hne _ hyhat, coeffAt_smul]
  have hterm : ∀ x ∈ f ⁻¹' {yhat},
      qCoeff f (Form1.pullback f hf η) (chartAt ℂ yhat) x = coeffAt yhat η := fun x hx =>
    qCoeff_pullback hf hne hyhat hx η
  rw [finsum_mem_congr rfl hterm]
  have hfin : (f ⁻¹' {yhat}).Finite := RS.fiber_finite hf hne yhat
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const]
  have hcard : hfin.toFinset.card = RS.degree f := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact RS.ncard_fiber_of_isRegularValue hf hne hyhat
  rw [hcard, nsmul_eq_mul]

variable (f) in
omit [CompactSpace Y] in
/-- **The projection formula (challenge form)**: `Form1.trace f hf ∘ Form1.pullback f hf` is
multiplication by the challenge degree `ContMDiff.degree f hf` — including the constant case
(both sides vanish). -/
theorem Form1.trace_pullback (η : Form1 Y) :
    Form1.trace f hf (Form1.pullback f hf η) = (ContMDiff.degree f hf : ℂ) • η := by
  by_cases hc : ∃ c, ∀ x, f x = c
  · rw [Form1.trace_of_forall_eq hf hc]
    obtain ⟨c, hcc⟩ := hc
    have hdeg : RS.degree f = 0 := by
      have hfeq : f = fun _ : X => c := funext hcc
      rw [hfeq]
      exact RS.degree_of_forall_eq c
    rw [ContMDiff.degree_eq, hdeg, Nat.cast_zero]
    rw [LinearMap.zero_apply]
    exact (zero_smul ℂ η).symm
  · rw [Form1.trace_apply hf hc, traceForm_pullback hf hc η, ContMDiff.degree_eq]

end Projection

end RS

end

/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Meromorphic.GermSpace
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# Order, canonical value, and `holoRepr` on germ classes (CC3, D3/D5)

Unit: meromorphic-and-divisors (`docs/design/meromorphic-and-divisors.md` §4.4, proof plans
§6.4/6.5).

* `MeroGermOn.ord φ x : WithTop ℤ`: the order of a class at a point (junk `0` off
  `IsOpen U ∧ x ∈ U`); descends from `ordAtX` (meromorphy-free congr).
* `MeroGermOn.evalAt φ x : ℂ`: the canonical value (D5) — the limit along `𝓝[≠] x` when
  `0 ≤ ord`, junk `0` else.
* `MeroGermOn.holoRepr φ : X → ℂ := fun x => φ.evalAt x`: the canonical repaired representative.
  `holoRepr_contMDiffAt` shows it is honestly holomorphic wherever `0 ≤ ord`; `mk_holoRepr` shows
  it recovers `φ` as a class. This is the rigidified normal form the blueprint needs for Čech.
-/

open scoped ContDiff Manifold
open Set Filter Topology

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {U V : Set X} {x : X} {c : ℂ}

/-- `limUnder` respects `EventuallyEq` (via `Filter.map_congr`, since `limUnder l f = lim (map f
    l)`). -/
theorem limUnder_congr {α : Type*} {l : Filter α} {g g' : α → ℂ} (h : g =ᶠ[l] g') :
    Filter.limUnder l g = Filter.limUnder l g' := by
  unfold Filter.limUnder
  rw [Filter.map_congr h]

namespace MeroGermOn

/-! ### `ord` -/

open scoped Classical in
/-- Order of a germ class at a point; junk `0` unless `IsOpen U ∧ x ∈ U` (D3). -/
noncomputable def ord (φ : MeroGermOn X U) (x : X) : WithTop ℤ :=
  φ.1.liftOn (fun f => if IsOpen U ∧ x ∈ U then ordAtX f x else 0)
    (fun f g hfg => by
      change (if IsOpen U ∧ x ∈ U then ordAtX f x else 0) =
        (if IsOpen U ∧ x ∈ U then ordAtX g x else 0)
      by_cases hgate : IsOpen U ∧ x ∈ U
      · rw [ite_eq_left hgate, ite_eq_left hgate]
        exact ordAtX_congr (((eventuallyEq_codiscreteWithin_iff_of_isOpen hgate.1).1 hfg) x hgate.2)
      · rw [ite_eq_right hgate, ite_eq_right hgate])

open scoped Classical in
theorem ord_apply_mk (f : X → ℂ) (hf : MeromorphicOnX f U) (x : X) :
    (mk f hf).ord x = if IsOpen U ∧ x ∈ U then ordAtX f x else 0 := rfl

@[simp] theorem ord_mk (hU : IsOpen U) (hx : x ∈ U) {f : X → ℂ} {hf : MeromorphicOnX f U} :
    (mk f hf).ord x = ordAtX f x := by
  rw [ord_apply_mk, ite_eq_left ⟨hU, hx⟩]

theorem ord_restrict (h : V ⊆ U) (hV : IsOpen V) (hU : IsOpen U) {x : X} (hx : x ∈ V)
    (φ : MeroGermOn X U) : (restrict h φ).ord x = φ.ord x := by
  obtain ⟨f, hf, rfl⟩ := exists_rep φ
  rw [restrict_mk, ord_mk hU (h hx)]
  -- `exact` (full defeq) rather than another `rw`: the restricted germ's `mk` proof argument is
  -- not syntactically the lemma's, so rewriting cannot see the match
  exact ord_mk hV hx

open scoped Classical in
theorem ord_zero : (0 : MeroGermOn X U).ord x = if IsOpen U ∧ x ∈ U then ⊤ else 0 := by
  rw [← mk_zero, ord_apply_mk]
  by_cases hgate : IsOpen U ∧ x ∈ U
  · rw [ite_eq_left hgate, ite_eq_left hgate]
    exact ordAtX_zero
  · rw [ite_eq_right hgate, ite_eq_right hgate]

theorem ord_one (hU : IsOpen U) (hx : x ∈ U) : (1 : MeroGermOn X U).ord x = 0 := by
  rw [← mk_one, ord_mk hU hx]
  exact ordAtX_one

theorem ord_add (hU : IsOpen U) (hx : x ∈ U) (φ ψ : MeroGermOn X U) :
    min (φ.ord x) (ψ.ord x) ≤ (φ + ψ).ord x := by
  obtain ⟨f, hf, rfl⟩ := exists_rep φ
  obtain ⟨g, hg, rfl⟩ := exists_rep ψ
  simp only [mk_add, ord_mk hU hx]
  exact ordAtX_add (hf x hx) (hg x hx)

theorem ord_add_of_ne (hU : IsOpen U) (hx : x ∈ U) {φ ψ : MeroGermOn X U}
    (h : φ.ord x ≠ ψ.ord x) : (φ + ψ).ord x = min (φ.ord x) (ψ.ord x) := by
  obtain ⟨f, hf, rfl⟩ := exists_rep φ
  obtain ⟨g, hg, rfl⟩ := exists_rep ψ
  simp only [mk_add, ord_mk hU hx] at h ⊢
  exact ordAtX_add_of_ne (hf x hx) (hg x hx) h

theorem ord_mul (hU : IsOpen U) (hx : x ∈ U) (φ ψ : MeroGermOn X U) :
    (φ * ψ).ord x = φ.ord x + ψ.ord x := by
  obtain ⟨f, hf, rfl⟩ := exists_rep φ
  obtain ⟨g, hg, rfl⟩ := exists_rep ψ
  simp only [mk_mul, ord_mk hU hx]
  exact ordAtX_mul (hf x hx) (hg x hx)

theorem ord_neg (φ : MeroGermOn X U) : (-φ).ord x = φ.ord x := by
  obtain ⟨f, hf, rfl⟩ := exists_rep φ
  rw [mk_neg, ord_apply_mk, ord_apply_mk]
  by_cases hgate : IsOpen U ∧ x ∈ U
  · rw [ite_eq_left hgate, ite_eq_left hgate, ordAtX_neg]
  · rw [ite_eq_right hgate, ite_eq_right hgate]

theorem ord_smul (hU : IsOpen U) (hx : x ∈ U) (hc : c ≠ 0) (φ : MeroGermOn X U) :
    (c • φ).ord x = φ.ord x := by
  obtain ⟨f, hf, rfl⟩ := exists_rep φ
  rw [mk_smul, ord_mk hU hx, ord_mk hU hx]
  exact ordAtX_smul hc

theorem ord_algebraMap (hU : IsOpen U) (hx : x ∈ U) (hc : c ≠ 0) :
    (algebraMap ℂ (MeroGermOn X U) c).ord x = 0 := by
  rw [algebraMap_mk, ord_mk hU hx, ordAtX_const, ite_eq_right hc]

/-! ### `evalAt` (D5) -/

open scoped Classical in
/-- Canonical value (D5): the limit along `𝓝[≠] x` when `0 ≤ ord`, junk `0` else. -/
noncomputable def evalAt (φ : MeroGermOn X U) (x : X) : ℂ :=
  φ.1.liftOn
    (fun f => if (IsOpen U ∧ x ∈ U) ∧ 0 ≤ ordAtX f x then Filter.limUnder (𝓝[≠] x) f else 0)
    (fun f g hfg => by
      change (if (IsOpen U ∧ x ∈ U) ∧ 0 ≤ ordAtX f x then Filter.limUnder (𝓝[≠] x) f else 0) =
        (if (IsOpen U ∧ x ∈ U) ∧ 0 ≤ ordAtX g x then Filter.limUnder (𝓝[≠] x) g else 0)
      by_cases hgate : (IsOpen U ∧ x ∈ U) ∧ 0 ≤ ordAtX f x
      · have hxU := hgate.1
        have hfg' : f =ᶠ[𝓝[≠] x] g :=
          (eventuallyEq_codiscreteWithin_iff_of_isOpen hxU.1).1 hfg x hxU.2
        have hgate' : (IsOpen U ∧ x ∈ U) ∧ 0 ≤ ordAtX g x :=
          ⟨hxU, (ordAtX_congr hfg') ▸ hgate.2⟩
        rw [ite_eq_left hgate, ite_eq_left hgate']
        exact limUnder_congr hfg'
      · have hgate2 : ¬((IsOpen U ∧ x ∈ U) ∧ 0 ≤ ordAtX g x) := by
          rintro ⟨hxU, hg0⟩
          exact hgate ⟨hxU, (ordAtX_congr
            ((eventuallyEq_codiscreteWithin_iff_of_isOpen hxU.1).1 hfg x hxU.2)).symm ▸ hg0⟩
        rw [ite_eq_right hgate, ite_eq_right hgate2])

open scoped Classical in
theorem evalAt_apply_mk (f : X → ℂ) (hf : MeromorphicOnX f U) (x : X) :
    (mk f hf).evalAt x =
      if (IsOpen U ∧ x ∈ U) ∧ 0 ≤ ordAtX f x then Filter.limUnder (𝓝[≠] x) f else 0 := rfl

theorem tendsto_evalAt (hU : IsOpen U) (hx : x ∈ U) (φ : MeroGermOn X U) (h : 0 ≤ φ.ord x)
    {f : X → ℂ} {hf : MeromorphicOnX f U} (hrep : mk f hf = φ) :
    Tendsto f (𝓝[≠] x) (𝓝 (φ.evalAt x)) := by
  subst hrep
  rw [ord_mk hU hx] at h
  obtain ⟨d, hd⟩ := (tendsto_nhds_iff_ordAtX_nonneg (hf x hx)).2 h
  rw [evalAt_apply_mk, ite_eq_left ⟨⟨hU, hx⟩, h⟩, hd.limUnder_eq]
  exact hd

@[simp] theorem evalAt_of_not_nonneg {φ : MeroGermOn X U} {x : X} (h : ¬ 0 ≤ φ.ord x) :
    φ.evalAt x = 0 := by
  obtain ⟨f, hf, rfl⟩ := exists_rep φ
  rw [evalAt_apply_mk]
  by_cases hgate : IsOpen U ∧ x ∈ U
  · rw [ord_mk hgate.1 hgate.2] at h
    exact ite_eq_right (fun hc => h hc.2)
  · exact ite_eq_right (fun hc => hgate hc.1)

/-! From here on, chart invariance is needed (`ContMDiffAt`/`AnalyticAt` bridges). -/

variable [IsManifold 𝓘(ℂ) ω X]

theorem evalAt_mk_of_contMDiffAt (hU : IsOpen U) (hx : x ∈ U) {f : X → ℂ}
    {hf : MeromorphicOnX f U} (hc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) :
    (mk f hf).evalAt x = f x := by
  have h0 : 0 ≤ (mk f hf).ord x := by
    rw [ord_mk hU hx]; exact RS.ContMDiffAt.ordAtX_nonneg hc
  have htend := tendsto_evalAt hU hx (mk f hf) h0 rfl
  have hcont : Tendsto f (𝓝[≠] x) (𝓝 (f x)) :=
    hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique htend hcont

omit [IsManifold 𝓘(ℂ) ω X] in
theorem evalAt_add (hU : IsOpen U) (hx : x ∈ U) {φ ψ : MeroGermOn X U} (h1 : 0 ≤ φ.ord x)
    (h2 : 0 ≤ ψ.ord x) : (φ + ψ).evalAt x = φ.evalAt x + ψ.evalAt x := by
  obtain ⟨f, hf, rfl⟩ := exists_rep φ
  obtain ⟨g, hg, rfl⟩ := exists_rep ψ
  have h12 : 0 ≤ (mk f hf + mk g hg).ord x :=
    le_trans (le_min h1 h2) (ord_add hU hx (mk f hf) (mk g hg))
  have e1 := tendsto_evalAt hU hx (mk f hf) h1 rfl
  have e2 := tendsto_evalAt hU hx (mk g hg) h2 rfl
  have e3 := tendsto_evalAt hU hx (mk f hf + mk g hg) h12 mk_add.symm
  have e4 : Tendsto (f + g) (𝓝[≠] x) (𝓝 ((mk f hf).evalAt x + (mk g hg).evalAt x)) := e1.add e2
  exact tendsto_nhds_unique e3 e4

theorem evalAt_smul (hU : IsOpen U) (hx : x ∈ U) {φ : MeroGermOn X U} (h : 0 ≤ φ.ord x) :
    (c • φ).evalAt x = c * φ.evalAt x := by
  obtain ⟨f, hf, rfl⟩ := exists_rep φ
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul, zero_mul, ← mk_zero]
    exact evalAt_mk_of_contMDiffAt hU hx contMDiffAt_const
  · have h1 : 0 ≤ (c • mk f hf).ord x := by rw [ord_smul hU hx hc]; exact h
    have e1 := tendsto_evalAt hU hx (mk f hf) h rfl
    have e2 := tendsto_evalAt hU hx (c • mk f hf) h1 (mk_smul c).symm
    have e3 : Tendsto (c • f) (𝓝[≠] x) (𝓝 (c * (mk f hf).evalAt x)) := by
      have h2 := e1.const_smul c
      simp only [smul_eq_mul] at h2
      exact h2
    exact tendsto_nhds_unique e2 e3

omit [IsManifold 𝓘(ℂ) ω X] in
theorem evalAt_mul (hU : IsOpen U) (hx : x ∈ U) {φ ψ : MeroGermOn X U} (h1 : 0 ≤ φ.ord x)
    (h2 : 0 ≤ ψ.ord x) : (φ * ψ).evalAt x = φ.evalAt x * ψ.evalAt x := by
  obtain ⟨f, hf, rfl⟩ := exists_rep φ
  obtain ⟨g, hg, rfl⟩ := exists_rep ψ
  have h12 : 0 ≤ (mk f hf * mk g hg).ord x := by
    rw [ord_mul hU hx]; exact add_nonneg h1 h2
  have e1 := tendsto_evalAt hU hx (mk f hf) h1 rfl
  have e2 := tendsto_evalAt hU hx (mk g hg) h2 rfl
  have e3 := tendsto_evalAt hU hx (mk f hf * mk g hg) h12 mk_mul.symm
  have e4 : Tendsto (f * g) (𝓝[≠] x) (𝓝 ((mk f hf).evalAt x * (mk g hg).evalAt x)) := e1.mul e2
  exact tendsto_nhds_unique e3 e4

omit [IsManifold 𝓘(ℂ) ω X] in
theorem evalAt_restrict (h : V ⊆ U) (hV : IsOpen V) (hU : IsOpen U) {x : X} (hx : x ∈ V)
    (φ : MeroGermOn X U) : (restrict h φ).evalAt x = φ.evalAt x := by
  obtain ⟨f, hf, rfl⟩ := exists_rep φ
  rw [restrict_mk]
  by_cases h0 : 0 ≤ (mk f hf).ord x
  · rw [ord_mk hU (h hx)] at h0
    have e1 :=
        tendsto_evalAt hV hx (mk f (fun y hy => hf y (h hy))) (le_of_le_of_eq h0
          (ord_mk hV hx).symm)
      rfl
    have e2 := tendsto_evalAt hU (h hx) (mk f hf) (by rw [ord_mk hU (h hx)]; exact h0) rfl
    exact tendsto_nhds_unique e1 e2
  · have h0' : ¬ 0 ≤ (mk f (fun y hy => hf y (h hy))).ord x := by
      rw [ord_mk hU (h hx)] at h0
      exact fun hle => h0 (le_of_le_of_eq hle (ord_mk hV hx))
    rw [evalAt_of_not_nonneg h0, evalAt_of_not_nonneg h0']

/-! ### `holoRepr` (D5) -/

/-- CC3's `holoRepr` (D5): the canonical repaired representative. -/
noncomputable def holoRepr (φ : MeroGermOn X U) : X → ℂ := fun x => φ.evalAt x

/-- `holoRepr` agrees with any representative off `x` (unconditionally on `ord`: near `x` the
representative is automatically chart-analytic, `MeromorphicAt.eventually_analyticAt`). -/
theorem holoRepr_eventuallyEq_nhdsNE (hU : IsOpen U) (hx : x ∈ U) (φ : MeroGermOn X U)
    {f : X → ℂ} {hf : MeromorphicOnX f U} (hrep : mk f hf = φ) :
    φ.holoRepr =ᶠ[𝓝[≠] x] f := by
  subst hrep
  have h1 : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) z :=
    MeromorphicAt.eventually_analyticAt (hf x hx)
  have h2 : ∀ᶠ y in 𝓝[≠] x, AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x y) :=
    eventually_nhdsNE_comp_chart_apply_iff.mpr h1
  have h3 : ∀ᶠ y in 𝓝[≠] x, y ∈ (chartAt ℂ x).source :=
    eventually_nhdsWithin_of_eventually_nhds
      ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
  have h4 : ∀ᶠ y in 𝓝[≠] x, y ∈ U := eventually_nhdsWithin_of_eventually_nhds (hU.mem_nhds hx)
  filter_upwards [h2, h3, h4] with y h2y h3y h4y
  have hcy : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f y :=
    (contMDiffAt_iff_analyticAt_of_mem_source (chart_mem_atlas ℂ x) h3y).2 h2y
  change (mk f hf).evalAt y = f y
  exact evalAt_mk_of_contMDiffAt hU h4y hcy

theorem holoRepr_contMDiffAt (hU : IsOpen U) (hx : x ∈ U) {φ : MeroGermOn X U}
    (h : 0 ≤ φ.ord x) : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω φ.holoRepr x := by
  obtain ⟨f, hf, rfl⟩ := exists_rep φ
  set c := chartAt ℂ x with hc_def
  set z₀ := c x with hz₀_def
  have hFmero : MeromorphicAt (f ∘ c.symm) z₀ := hf x hx
  have h0 : 0 ≤ ordAtX f x := by rw [ord_mk hU hx] at h; exact h
  have h0' : 0 ≤ meromorphicOrderAt (f ∘ c.symm) z₀ := h0
  set h' := toMeromorphicNFAt (f ∘ c.symm) z₀ with hh'_def
  have heqNF : (f ∘ c.symm) =ᶠ[𝓝[≠] z₀] h' := hFmero.eq_nhdsNE_toMeromorphicNFAt
  have hNF : MeromorphicNFAt h' z₀ := meromorphicNFAt_toMeromorphicNFAt
  have hordh' : meromorphicOrderAt h' z₀ = meromorphicOrderAt (f ∘ c.symm) z₀ :=
    (meromorphicOrderAt_congr heqNF).symm
  have hAnalytic : AnalyticAt ℂ h' z₀ :=
    hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 (hordh' ▸ h0')
  have hoff : ((fun y => (mk f hf).evalAt y) ∘ c.symm) =ᶠ[𝓝[≠] z₀] h' := by
    have heq := holoRepr_eventuallyEq_nhdsNE hU hx (mk f hf) rfl
    have heq2 : ((fun y => (mk f hf).evalAt y) ∘ c.symm) =ᶠ[𝓝[≠] z₀] (f ∘ c.symm) :=
      eventuallyEq_nhdsNE_comp_chart_iff.mp heq
    exact heq2.trans heqNF
  have hcsymm : c.symm z₀ = x := c.left_inv (mem_chart_source ℂ x)
  have hatz0 : ((fun y => (mk f hf).evalAt y) ∘ c.symm) z₀ = h' z₀ := by
    change (mk f hf).evalAt (c.symm z₀) = h' z₀
    rw [hcsymm]
    have htend : Tendsto f (𝓝[≠] x) (𝓝 ((mk f hf).evalAt x)) := tendsto_evalAt hU hx (mk f hf) h rfl
    have htend2 : Tendsto (f ∘ c.symm) (𝓝[≠] z₀) (𝓝 ((mk f hf).evalAt x)) :=
      tendsto_nhdsNE_comp_chart_iff.mp htend
    have htend3 : Tendsto h' (𝓝[≠] z₀) (𝓝 (h' z₀)) :=
      hAnalytic.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have htend4 : Tendsto (f ∘ c.symm) (𝓝[≠] z₀) (𝓝 (h' z₀)) := htend3.congr' heqNF.symm
    exact tendsto_nhds_unique htend2 htend4
  have key : ((fun y => (mk f hf).evalAt y) ∘ c.symm) =ᶠ[𝓝 z₀] h' := by
    have hoff' : ∀ᶠ w in 𝓝[≠] z₀, ((fun y => (mk f hf).evalAt y) ∘ c.symm) w = h' w := hoff
    rw [eventually_nhdsWithin_iff] at hoff'
    filter_upwards [hoff'] with w hw
    rcases eq_or_ne w z₀ with rfl | hwz
    · exact hatz0
    · exact hw hwz
  change ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun y => (mk f hf).evalAt y) x
  rw [RS.contMDiffAt_iff_analyticAt_comp_chartAt]
  exact hAnalytic.congr key.symm

theorem holoRepr_contMDiffOn (hU : IsOpen U) {φ : MeroGermOn X U} (h : ∀ x ∈ U, 0 ≤ φ.ord x) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω φ.holoRepr U :=
  fun x hx => (holoRepr_contMDiffAt hU hx (h x hx)).contMDiffWithinAt

theorem holoRepr_contMDiff {φ : ℳ X} (h : ∀ x, 0 ≤ φ.ord x) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ.holoRepr :=
  fun x => holoRepr_contMDiffAt isOpen_univ (mem_univ x) (h x)

theorem meromorphicOnX_holoRepr (hU : IsOpen U) (φ : MeroGermOn X U) :
    MeromorphicOnX φ.holoRepr U := by
  intro x hx
  obtain ⟨f, hf, rfl⟩ := exists_rep φ
  by_cases h0 : 0 ≤ (mk f hf).ord x
  · exact RS.ContMDiffAt.meromorphicAtX (holoRepr_contMDiffAt hU hx h0)
  · exact (hf x hx).congr (holoRepr_eventuallyEq_nhdsNE hU hx (mk f hf) rfl).symm

theorem mk_holoRepr (hU : IsOpen U) (φ : MeroGermOn X U) :
    mk φ.holoRepr (meromorphicOnX_holoRepr hU φ) = φ := by
  obtain ⟨f, hf, rfl⟩ := exists_rep φ
  rw [mk_eq_mk]
  exact (eventuallyEq_codiscreteWithin_iff_of_isOpen hU).mpr
    (fun y hy => holoRepr_eventuallyEq_nhdsNE hU hy (mk f hf) rfl)

omit [IsManifold 𝓘(ℂ) ω X] in
theorem holoRepr_restrict (h : V ⊆ U) (hV : IsOpen V) (hU : IsOpen U) (φ : MeroGermOn X U) :
    Set.EqOn ((restrict h φ).holoRepr) φ.holoRepr V :=
  fun _y hy => evalAt_restrict h hV hU hy φ

theorem continuousAt_holoRepr (hU : IsOpen U) (hx : x ∈ U) {φ : MeroGermOn X U}
    (h : 0 ≤ φ.ord x) : ContinuousAt φ.holoRepr x :=
  (holoRepr_contMDiffAt hU hx h).continuousAt

theorem tendsto_holoRepr_cobounded_iff (hU : IsOpen U) (hx : x ∈ U) (φ : MeroGermOn X U) :
    Tendsto φ.holoRepr (𝓝[≠] x) (Bornology.cobounded ℂ) ↔ φ.ord x < 0 := by
  obtain ⟨f, hf, rfl⟩ := exists_rep φ
  rw [Filter.tendsto_congr' (holoRepr_eventuallyEq_nhdsNE hU hx (mk f hf) rfl),
    tendsto_cobounded_iff_ordAtX_neg (hf x hx), ord_mk hU hx]

end MeroGermOn

end RS

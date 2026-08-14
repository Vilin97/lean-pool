/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Cech.Colimit
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Local Laurent windows and the skyscraper data (CC8, D7, proof plan §6.8)

Unit: cech-cohomology (`docs/design/cech-cohomology.md` §4.6).

* `ordGe p m`: germs at the chart source of `p` with order `≥ m` at `p`.
* `tailGerm p m`: the local tail germ `(z − z_p)^m` (junk off the chart source).
* `leadCoeff p m`: the one-step leading-coefficient functional (D7) — no iterative Laurent
  coefficient extraction.
* `WindowAt p d d'`: the abstract Laurent window at `p` between orders `−d'` and `−d`.
* `diffSupp`, `Window D D'`: the skyscraper `⊕_q ℂ^{(D'−D)(q)}` in abstract form.
* `windowMap`: the truncation `L(D') → Window D D'` (purely structural).

The explicit dimension counts `finrank_windowAt`/`finrank_window` (finiteness-and-chi's χ-ledger
inputs) are exported from `WindowRank.lean` instead, via a one-step splitting
`WindowAt p d d' ≃ₗ WindowAt p d (d'-1) × ℂ` and induction (no `θ`-basis/independence argument
needed); the *structural* exactness in this file does not depend on them.
-/

open scoped ContDiff Manifold Topology
open Set TopologicalSpace RS.Cech Filter

namespace RS.Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### `ordGe` -/

/-- Germs at the chart source of `p` with order `≥ m` at `p`. -/
noncomputable def ordGe (p : X) (m : ℤ) : Submodule ℂ (RS.MeroGermOn X ((chartAt ℂ p).source)) where
  carrier := {ψ | (m : WithTop ℤ) ≤ ψ.ord p}
  zero_mem' := by
    change (m : WithTop ℤ) ≤ (0 : RS.MeroGermOn X _).ord p
    rw [RS.MeroGermOn.ord_zero,
      ite_eq_left ⟨(chartAt ℂ p).open_source, mem_chart_source ℂ p⟩]
    exact le_top
  add_mem' := by
    intro ψ φ hψ hφ
    change (m : WithTop ℤ) ≤ (ψ + φ).ord p
    exact le_trans (le_min hψ hφ)
      (RS.MeroGermOn.ord_add (chartAt ℂ p).open_source (mem_chart_source ℂ p) ψ φ)
  smul_mem' := by
    intro a ψ hψ
    change (m : WithTop ℤ) ≤ (a • ψ).ord p
    rcases eq_or_ne a 0 with rfl | ha
    · rw [zero_smul, RS.MeroGermOn.ord_zero,
        ite_eq_left ⟨(chartAt ℂ p).open_source, mem_chart_source ℂ p⟩]
      exact le_top
    · rw [RS.MeroGermOn.ord_smul (chartAt ℂ p).open_source (mem_chart_source ℂ p) ha]
      exact hψ

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mem_ordGe_iff {p : X} {m : ℤ} {ψ : RS.MeroGermOn X ((chartAt ℂ p).source)} :
    ψ ∈ ordGe p m ↔ (m : WithTop ℤ) ≤ ψ.ord p := Iff.rfl

/-! ### `tailGerm` -/

theorem meromorphicOnX_tailGerm (p : X) (m : ℤ) :
    RS.MeromorphicOnX (fun y => (chartAt ℂ p y - chartAt ℂ p p) ^ m) (chartAt ℂ p).source := by
  intro x hx
  rw [RS.meromorphicAtX_iff_of_mem_source (IsManifold.chart_mem_maximalAtlas p) hx]
  have hbase : MeromorphicAt (fun z : ℂ => (z - chartAt ℂ p p) ^ m) (chartAt ℂ p x) :=
    ((MeromorphicAt.id (chartAt ℂ p x)).sub
      (MeromorphicAt.const (chartAt ℂ p p) (chartAt ℂ p x))).zpow m
  refine hbase.congr (Filter.EventuallyEq.filter_mono ?_ nhdsWithin_le_nhds)
  have htarget_nhds : (chartAt ℂ p).target ∈ 𝓝 (chartAt ℂ p x) :=
    (chartAt ℂ p).open_target.mem_nhds ((chartAt ℂ p).map_source hx)
  filter_upwards [htarget_nhds] with z hz
  change (z - chartAt ℂ p p) ^ m = (chartAt ℂ p ((chartAt ℂ p).symm z) - chartAt ℂ p p) ^ m
  rw [(chartAt ℂ p).right_inv hz]

/-- The local tail germ `(z − z_p)^m` (junk off the chart source). -/
noncomputable def tailGerm (p : X) (m : ℤ) : RS.MeroGermOn X ((chartAt ℂ p).source) :=
  RS.MeroGermOn.mk (fun y => (chartAt ℂ p y - chartAt ℂ p p) ^ m) (meromorphicOnX_tailGerm p m)

theorem ord_tailGerm_self (p : X) (m : ℤ) : (tailGerm p m).ord p = (m : WithTop ℤ) := by
  rw [tailGerm, RS.MeroGermOn.ord_mk (chartAt ℂ p).open_source (mem_chart_source ℂ p),
    RS.ordAtX_eq_of_mem_source (IsManifold.chart_mem_maximalAtlas p) (mem_chart_source ℂ p)]
  have heq : (fun y => (chartAt ℂ p y - chartAt ℂ p p) ^ m) ∘ (chartAt ℂ p).symm
      =ᶠ[𝓝 (chartAt ℂ p p)] (fun z : ℂ => (z - chartAt ℂ p p) ^ m) := by
    have htarget_nhds : (chartAt ℂ p).target ∈ 𝓝 (chartAt ℂ p p) :=
      (chartAt ℂ p).open_target.mem_nhds ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
    filter_upwards [htarget_nhds] with z hz
    change (chartAt ℂ p ((chartAt ℂ p).symm z) - chartAt ℂ p p) ^ m = (z - chartAt ℂ p p) ^ m
    rw [(chartAt ℂ p).right_inv hz]
  rw [meromorphicOrderAt_congr (heq.filter_mono nhdsWithin_le_nhds)]
  exact meromorphicOrderAt_zpow_id_sub_const

/-- The one-step leading-coefficient functional (D7): `ψ ↦ (θ_{p,−m}·ψ).evalAt p` on
`ordGe p m`. -/
noncomputable def leadCoeff (p : X) (m : ℤ) : ordGe p m →ₗ[ℂ] ℂ where
  toFun ψ := ((tailGerm p (-m)) * (ψ : RS.MeroGermOn X ((chartAt ℂ p).source))).evalAt p
  map_add' ψ ψ' := by
    have h1 : (0 : WithTop ℤ) ≤ (tailGerm p (-m) * (ψ : RS.MeroGermOn X _)).ord p := by
      rw [RS.MeroGermOn.ord_mul (chartAt ℂ p).open_source (mem_chart_source ℂ p),
        ord_tailGerm_self]
      have hψm := ψ.2
      rw [mem_ordGe_iff] at hψm
      have : (-m + m : WithTop ℤ) ≤ (-m : WithTop ℤ) + ψ.1.ord p := add_le_add le_rfl hψm
      simpa using this
    have h2 : (0 : WithTop ℤ) ≤ (tailGerm p (-m) * (ψ' : RS.MeroGermOn X _)).ord p := by
      rw [RS.MeroGermOn.ord_mul (chartAt ℂ p).open_source (mem_chart_source ℂ p),
        ord_tailGerm_self]
      have hψ'm := ψ'.2
      rw [mem_ordGe_iff] at hψ'm
      have : (-m + m : WithTop ℤ) ≤ (-m : WithTop ℤ) + ψ'.1.ord p := add_le_add le_rfl hψ'm
      simpa using this
    change ((tailGerm p (-m)) * ((ψ : RS.MeroGermOn X ((chartAt ℂ p).source)) +
      (ψ' : RS.MeroGermOn X ((chartAt ℂ p).source)))).evalAt p = _
    rw [mul_add,
      RS.MeroGermOn.evalAt_add (chartAt ℂ p).open_source (mem_chart_source ℂ p) h1 h2]
  map_smul' a ψ := by
    have h1 : (0 : WithTop ℤ) ≤ (tailGerm p (-m) * (ψ : RS.MeroGermOn X _)).ord p := by
      rw [RS.MeroGermOn.ord_mul (chartAt ℂ p).open_source (mem_chart_source ℂ p),
        ord_tailGerm_self]
      have hψm := ψ.2
      rw [mem_ordGe_iff] at hψm
      have : (-m + m : WithTop ℤ) ≤ (-m : WithTop ℤ) + ψ.1.ord p := add_le_add le_rfl hψm
      simpa using this
    change ((tailGerm p (-m)) * (a • (ψ : RS.MeroGermOn X _))).evalAt p = a * _
    rw [mul_smul_comm,
      RS.MeroGermOn.evalAt_smul (chartAt ℂ p).open_source (mem_chart_source ℂ p) h1]

/-! ### `WindowAt` (the abstract Laurent window) -/

/-- The Laurent window at `p` between orders `−d'` and `−d`, as an abstract quotient (D7) — no
coefficient recursion. -/
noncomputable abbrev WindowAt (p : X) (d d' : ℤ) : Type _ :=
  ordGe p (-d') ⧸ (ordGe p (-d)).comap (ordGe p (-d')).subtype

/-- The quotient map onto the window at `p`: a germ of order at least `-d'`, taken modulo those of
order at least `-d`. -/
noncomputable def WindowAt.mk (p : X) (d d' : ℤ) : ordGe p (-d') →ₗ[ℂ] WindowAt p d d' :=
  Submodule.mkQ _

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem WindowAt.mk_eq_zero_iff {p : X} {d d' : ℤ} (ψ : ordGe p (-d')) :
    WindowAt.mk p d d' ψ = 0 ↔
      ((-d : ℤ) : WithTop ℤ) ≤ (ψ : RS.MeroGermOn X ((chartAt ℂ p).source)).ord p := by
  rw [WindowAt.mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  rfl

/-! ### `diffSupp`, `Window` -/

variable [T2Space X] [CompactSpace X]

/-- Support of the difference divisor, as a `Finset` (compactness). -/
noncomputable def diffSupp (D D' : RS.Divisor X) : Finset X :=
  ((D - D').finiteSupport isCompact_univ).toFinset

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mem_diffSupp_iff {D D' : RS.Divisor X} {q : X} : q ∈ diffSupp D D' ↔ D q ≠ D' q := by
  rw [diffSupp, Set.Finite.mem_toFinset, Function.mem_support, Divisor.sub_apply, sub_ne_zero]

/-- The skyscraper window `⊕_q ℂ^{(D'−D)(q)}` in abstract form. -/
noncomputable abbrev Window (D D' : RS.Divisor X) : Type _ :=
  ∀ q : diffSupp D D', WindowAt (q : X) (D q) (D' q)

/-! ### `windowMap` -/

/-- Restriction of a global section to the chart source at `q`, landing in the `ordGe` bound
coming from `L(D')`-membership. -/
noncomputable def restrictToChart (D' : RS.Divisor X) (q : X) :
    RS.LinSys D' →ₗ[ℂ] ordGe q (-(D' q)) :=
  LinearMap.codRestrict (ordGe q (-(D' q)))
    ((RS.MeroGermOn.restrict (Set.subset_univ (chartAt ℂ q).source)).toLinearMap.comp
      (RS.LinSys D').subtype)
    (fun φ => by
      change ((-(D' q) : ℤ) : WithTop ℤ) ≤
        (RS.MeroGermOn.restrict (Set.subset_univ (chartAt ℂ q).source)
          (φ : RS.MeroGermOn X (Set.univ : Set X))).ord q
      rw [RS.MeroGermOn.ord_restrict (Set.subset_univ (chartAt ℂ q).source) (chartAt ℂ
          q).open_source
        isOpen_univ (mem_chart_source ℂ q)]
      exact φ.2 q)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] [CompactSpace X] in
theorem restrictToChart_apply_coe (D' : RS.Divisor X) (q : X) (φ : RS.LinSys D') :
    (restrictToChart D' q φ : RS.MeroGermOn X ((chartAt ℂ q).source)) =
      RS.MeroGermOn.restrict (Set.subset_univ (chartAt ℂ q).source)
        (φ : RS.MeroGermOn X (Set.univ : Set X)) := rfl

/-- Truncation `β : L(D') → Window D D'` — purely structural (D7). -/
noncomputable def windowMap {D D' : RS.Divisor X} (_h : D ≤ D') :
    RS.LinSys D' →ₗ[ℂ] Window D D' :=
  LinearMap.pi fun q => (WindowAt.mk (q : X) (D q) (D' q)).comp (restrictToChart D' q)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem windowMap_apply {D D' : RS.Divisor X} (h : D ≤ D') (φ : RS.LinSys D')
    (q : diffSupp D D') :
    windowMap h φ q = WindowAt.mk (q : X) (D q) (D' q) (restrictToChart D' q φ) := rfl

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem windowMap_eq_zero_iff {D D' : RS.Divisor X} (h : D ≤ D') (φ : RS.LinSys D') :
    windowMap h φ = 0 ↔ (φ : RS.Mero X) ∈ RS.LinSys D := by
  constructor
  · intro hz
    rw [RS.mem_linSys_iff]
    intro x
    by_cases hx : D x = D' x
    · rw [hx]; exact φ.2 x
    · have hxmem : x ∈ diffSupp D D' := mem_diffSupp_iff.2 hx
      have hcomp := congrFun hz ⟨x, hxmem⟩
      rw [windowMap_apply, Pi.zero_apply, WindowAt.mk_eq_zero_iff, restrictToChart_apply_coe,
        RS.MeroGermOn.ord_restrict (Set.subset_univ (chartAt ℂ x).source) (chartAt ℂ x).open_source
          isOpen_univ (mem_chart_source ℂ x)] at hcomp
      exact hcomp
  · intro hDφ
    funext q
    rw [windowMap_apply, Pi.zero_apply, WindowAt.mk_eq_zero_iff, restrictToChart_apply_coe,
      RS.MeroGermOn.ord_restrict (Set.subset_univ (chartAt ℂ (q : X)).source)
        (chartAt ℂ (q : X)).open_source isOpen_univ (mem_chart_source ℂ (q : X))]
    exact (RS.mem_linSys_iff.1 hDφ) (q : X)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Exactness at `L(D')`: the window map's kernel is exactly `L(D)` (bottom half of the
six-term fragment, `Skyscraper.lean` supplies the top half). -/
theorem exact_inclusion_windowMap {D D' : RS.Divisor X} (h : D ≤ D') :
    Function.Exact (Submodule.inclusion (RS.linSys_mono h)) (windowMap h) := by
  intro φ
  rw [windowMap_eq_zero_iff]
  constructor
  · intro hφ
    exact ⟨⟨(φ : RS.Mero X), hφ⟩, rfl⟩
  · rintro ⟨ψ, rfl⟩
    exact ψ.2

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] [CompactSpace X] in
theorem inclusion_injective {D D' : RS.Divisor X} (h : D ≤ D') :
    Function.Injective (Submodule.inclusion (RS.linSys_mono h)) :=
  Submodule.inclusion_injective (RS.linSys_mono h)

/-!
### Dimension counts: see `WindowRank.lean`

`finrank_windowAt (h : d ≤ d') : Module.finrank ℂ (WindowAt p d d') = (d' - d).toNat` and
`finrank_window (h : D ≤ D') : Module.finrank ℂ (Window D D') = ((D' - D).degree).toNat`,
plus the `FiniteDimensional` instances, are proved in `WindowRank.lean` (which imports this
file) — via a one-step splitting `WindowAt p d d' ≃ₗ WindowAt p d (d'-1) × ℂ`
(`LinearMap.quotKerEquivRange` on an explicit "subtract off the leading term" map) and induction
on `(d' - d).toNat`, **not** the `θ`-basis/independence argument originally planned in design
§6.8 (that argument needed `leadCoeff` to be defined on the whole numerator `ordGe p (-d')` for
every basis index simultaneously, which it isn't; the one-step splitting sidesteps this by only
ever using `leadCoeff p (-d')`, which *is* defined on the whole numerator). Every export in
*this* file (`ordGe`, `tailGerm`, `leadCoeff`, `WindowAt`, `Window`, `windowMap` and its
exactness/injectivity) is proved with zero sorries and does not depend on the dimension counts.
-/

end RS.Cech

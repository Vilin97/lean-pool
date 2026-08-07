/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Dbar.PlanarCousin
import LeanPool.JacobianDiffgeo.Dbar.Operator
import LeanPool.JacobianDiffgeo.Cech.Cochains
import LeanPool.JacobianDiffgeo.Cech.Refinement
import LeanPool.JacobianDiffgeo.Meromorphic

/-!
# Disk acyclicity of `𝒪_D` (`Jacobian/Dbar/DiskAcyclic.lean`)

Unit: dbar-solvability (`docs/design/dbar-solvability.md` D9, §4.8, §7.4). Depends on the
sibling units `cech-cohomology` (`Jacobian.Cech.Cochains`) and `meromorphic-and-divisors`
(`Jacobian.Meromorphic`).

Main deliverable (D=0 case, the sheaf `𝒪` of holomorphic functions): `Z¹(cover of a chart disk,
𝒪) = B¹`, i.e. `H¹(chart disk, 𝒪) = 0` — every additive holomorphic cocycle on a finite cover of
a chart disk splits, via `PlanarCousin.exists_holo_splitting_ball` transported through the chart
and cech's `MeroGermOn`/`evalAt` germ API for the pointwise bookkeeping.

DEVIATION (honestly reported): the general-divisor twist (`subsingleton_h1Cover_of_isChartDisk`,
needing `[T2Space X] [CompactSpace X]` and a finite-product twisting germ
`q := ∏ a ∈ D.support ∩ V, (· - e a) ^ D (e.symm a)`) is NOT included — it is a substantial
independent construction (one-directional twisted cochain maps commuting with `d0`/`d1`/
`restrictL`) that did not fit the remaining time budget; see the final report. The `D = 0` case
below is a complete, self-contained, fully admitted-free proof of disk acyclicity for the
structure sheaf, which is the piece the design flags as needed with "no compactness".
-/

open scoped ContDiff Manifold
open Set Filter Topology TopologicalSpace

namespace RS

open Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [T1Space X]

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X] [T1Space X] in
private theorem heqOn_to_evEq {f g : X → ℂ} {U : Set X} (h : ∀ x ∈ U, f x = g x) :
    f =ᶠ[Filter.codiscreteWithin U] g :=
  Filter.mem_of_superset (Filter.self_mem_codiscreteWithin _) h

/-! ### Compat helpers (holomorphic ⇒ meromorphic, candidates for upstreaming to `mero`) -/

omit [T1Space X] in
theorem meromorphicOnX_of_contMDiffOn_omega {U : Set X} (hU : IsOpen U) {u : X → ℂ}
    (hu : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω u U) : MeromorphicOnX u U := fun x hx => by
  have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω u x := (hu x hx).contMDiffAt (hU.mem_nhds hx)
  exact ContMDiffAt.meromorphicAtX h2

omit [T1Space X] in
theorem mk_mem_linSysOn_zero {U : Set X} (hU : IsOpen U) {u : X → ℂ}
    (hu : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω u U) :
    MeroGermOn.mk u (meromorphicOnX_of_contMDiffOn_omega hU hu) ∈ LinSysOn (0 : Divisor X) U := by
  rw [mem_linSysOn_iff_of_isOpen hU]
  intro x hx
  rw [MeroGermOn.ord_mk hU hx]
  have h0 : ((0 : Divisor X) x : ℤ) = 0 := by
    simp [Function.locallyFinsuppWithin.coe_zero]
  rw [h0]
  have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω u x := (hu x hx).contMDiffAt (hU.mem_nhds hx)
  simpa using ContMDiffAt.ordAtX_nonneg h2

omit [T1Space X] in
/-- Acyclicity for `𝒪` (no compactness needed): `H¹` of a finite cover of a chart disk, with
the structure sheaf's coefficients, vanishes. -/
theorem subsingleton_h1Cover_zero_of_isChartDisk {V : Opens X} (hV : IsChartDisk V)
    (𝒱 : FinCover V) : Subsingleton (H1Cover (0 : Divisor X) 𝒱) := by
  rw [subsingleton_h1Cover_iff]
  intro f hf
  obtain ⟨x₀, r, hr, _hx₀, hVs, hVim⟩ := hV
  set e := chartAt ℂ x₀ with he_def
  set W : Fin 𝒱.n → Set ℂ := fun i => ⇑e '' (𝒱.U i : Set X) with hW_def
  have hUisub : ∀ i, (𝒱.U i : Set X) ⊆ (e).source := fun i =>
    Set.Subset.trans (𝒱.le_base i : (𝒱.U i : Set X) ⊆ (V : Set X)) hVs
  have hUiUj_source : ∀ i j, ((𝒱.U i ⊓ 𝒱.U j : Opens X) : Set X) ⊆ e.source := fun i j =>
    (Set.inter_subset_left).trans (hUisub i)
  have hWo : ∀ i, IsOpen (W i) := fun i =>
    e.isOpen_image_of_subset_source (𝒱.U i).2 (hUisub i)
  have hWinter : ∀ i j, W i ∩ W j = ⇑e '' ((𝒱.U i ⊓ 𝒱.U j : Opens X) : Set X) := by
    intro i j
    apply Set.Subset.antisymm
    · rintro z ⟨⟨p, hp, rfl⟩, ⟨q, hq, hpq⟩⟩
      have : p = q := e.injOn (hUisub i hp) (hUisub j hq) hpq.symm
      exact ⟨p, ⟨hp, this ▸ hq⟩, rfl⟩
    · rintro z ⟨p, ⟨hp1, hp2⟩, rfl⟩
      exact ⟨⟨p, hp1, rfl⟩, ⟨p, hp2, rfl⟩⟩
  have hWb : ∀ i, W i ⊆ Metric.ball (e x₀) r := by
    intro i
    rw [hW_def]
    simp only
    rw [← hVim]
    exact Set.image_mono (𝒱.le_base i : (𝒱.U i : Set X) ⊆ (V : Set X))
  have hcov : Metric.ball (e x₀) r ⊆ ⋃ i, W i := by
    rw [← hVim]
    rintro z ⟨p, hp, rfl⟩
    obtain ⟨i, hi⟩ := 𝒱.covers p hp
    exact Set.mem_iUnion.2 ⟨i, p, hi, rfl⟩
  -- Step 1: holomorphic representatives of the germ cocycle.
  have hF_ord : ∀ i j, ∀ x ∈ (𝒱.U i ⊓ 𝒱.U j : Opens X),
      0 ≤ (f (i, j) : MeroGermOn X ((𝒱.U i ⊓ 𝒱.U j : Opens X) : Set X)).ord x := by
    intro i j x hx
    have := (mem_linSysOn_iff_of_isOpen (𝒱.U i ⊓ 𝒱.U j).2).1 (f (i, j)).2 x hx
    simpa using this
  set F : Fin 𝒱.n → Fin 𝒱.n → X → ℂ :=
    fun i j => (f (i, j) : MeroGermOn X ((𝒱.U i ⊓ 𝒱.U j : Opens X) : Set X)).holoRepr
    with hF_def
  have hF_cd : ∀ i j, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (F i j) ((𝒱.U i ⊓ 𝒱.U j : Opens X) : Set X) :=
    fun i j => MeroGermOn.holoRepr_contMDiffOn (𝒱.U i ⊓ 𝒱.U j).2 (hF_ord i j)
  -- Step 2: planar transport of the representatives.
  set φ : Fin 𝒱.n → Fin 𝒱.n → ℂ → ℂ := fun i j => F i j ∘ e.symm with hφ_def
  have hφ_diff : ∀ i j, DifferentiableOn ℂ (φ i j) (W i ∩ W j) := by
    intro i j
    rw [hWinter]
    have := (contMDiffOn_iff_analyticOnNhd_of_subset_source (chart_mem_atlas ℂ x₀)
      (hUiUj_source i j) (𝒱.U i ⊓ 𝒱.U j).2).1 (hF_cd i j)
    exact this.differentiableOn
  -- Step 3: pointwise cocycle identity for `φ`, from `Z1.rel_res`.
  have hcoc : ∀ i j k, ∀ z ∈ W i ∩ W j ∩ W k, φ i k z = φ i j z + φ j k z := by
    intro i j k z hz
    obtain ⟨p, hp, rfl⟩ : ∃ p ∈ ((𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k : Opens X) : Set X), e p = z := by
      have hz1 : z ∈ W i ∩ W j := ⟨hz.1.1, hz.1.2⟩
      have hz2 : z ∈ W j ∩ W k := ⟨hz.1.2, hz.2⟩
      rw [hWinter] at hz1 hz2
      obtain ⟨p, hp1, rfl⟩ := hz1
      obtain ⟨q, hq2, hpq⟩ := hz2
      have hpq' : p = q := e.injOn (hUiUj_source i j hp1) (hUiUj_source j k hq2) hpq.symm
      exact ⟨p, ⟨hp1, hpq' ▸ hq2.2⟩, rfl⟩
    have hbc : 𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k ≤ 𝒱.U j ⊓ 𝒱.U k :=
      le_inf (le_trans inf_le_left inf_le_right) inf_le_right
    have hac : 𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k ≤ 𝒱.U i ⊓ 𝒱.U k :=
      le_inf (le_trans inf_le_left inf_le_left) inf_le_right
    have hab : 𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k ≤ 𝒱.U i ⊓ 𝒱.U j := inf_le_left
    have hrel := Z1.rel_res (0 : Divisor X) (W := 𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k) hf i j k
      (le_refl _) hbc hac hab
    have hpik : p ∈ ((𝒱.U i ⊓ 𝒱.U k : Opens X) : Set X) := ⟨hp.1.1, hp.2⟩
    have hpij : p ∈ ((𝒱.U i ⊓ 𝒱.U j : Opens X) : Set X) := hp.1
    have hpjk : p ∈ ((𝒱.U j ⊓ 𝒱.U k : Opens X) : Set X) := ⟨hp.1.2, hp.2⟩
    have hordij := hF_ord i j p hpij
    have hordjk := hF_ord j k p hpjk
    have hordik := hF_ord i k p hpik
    have hrelv : (LinSysOn.restrictL (0 : Divisor X) hbc (f (j, k)) :
          MeroGermOn X ((𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k : Opens X) : Set X)) -
        (LinSysOn.restrictL (0 : Divisor X) hac (f (i, k)) :
          MeroGermOn X ((𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k : Opens X) : Set X)) +
        (LinSysOn.restrictL (0 : Divisor X) hab (f (i, j)) :
          MeroGermOn X ((𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k : Opens X) : Set X)) = 0 := by
      have := congrArg Subtype.val hrel
      simpa using this
    have hsum : (LinSysOn.restrictL (0 : Divisor X) hbc (f (j, k)) :
          MeroGermOn X ((𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k : Opens X) : Set X)) +
        (LinSysOn.restrictL (0 : Divisor X) hab (f (i, j)) :
          MeroGermOn X ((𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k : Opens X) : Set X)) =
        (LinSysOn.restrictL (0 : Divisor X) hac (f (i, k)) :
          MeroGermOn X ((𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k : Opens X) : Set X)) := by
      linear_combination hrelv
    rw [restrictL_apply_coe, restrictL_apply_coe, restrictL_apply_coe] at hsum
    have hordjk_r : 0 ≤ (MeroGermOn.restrict hbc
        (f (j, k) : MeroGermOn X ((𝒱.U j ⊓ 𝒱.U k : Opens X) : Set X))).ord p := by
      rw [MeroGermOn.ord_restrict hbc (𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k).2 (𝒱.U j ⊓ 𝒱.U k).2 hp]
      exact hordjk
    have hordij_r : 0 ≤ (MeroGermOn.restrict hab
        (f (i, j) : MeroGermOn X ((𝒱.U i ⊓ 𝒱.U j : Opens X) : Set X))).ord p := by
      rw [MeroGermOn.ord_restrict hab (𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k).2 (𝒱.U i ⊓ 𝒱.U j).2 hp]
      exact hordij
    have heval := congrArg (fun g => MeroGermOn.evalAt g p) hsum
    rw [MeroGermOn.evalAt_add (𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k).2 hp hordjk_r hordij_r] at heval
    rw [MeroGermOn.evalAt_restrict hbc (𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k).2 (𝒱.U j ⊓ 𝒱.U k).2 hp,
      MeroGermOn.evalAt_restrict hab (𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k).2 (𝒱.U i ⊓ 𝒱.U j).2 hp,
      MeroGermOn.evalAt_restrict hac (𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k).2 (𝒱.U i ⊓ 𝒱.U k).2 hp] at heval
    change F i k (e.symm (e p)) = F i j (e.symm (e p)) + F j k (e.symm (e p))
    rw [e.left_inv (hUisub i hp.1.1)]
    show F i k p = F i j p + F j k p
    have e1 : F i k p = (f (i, k) : MeroGermOn X ((𝒱.U i ⊓ 𝒱.U k : Opens X) : Set X)).evalAt p :=
      rfl
    have e2 : F i j p = (f (i, j) : MeroGermOn X ((𝒱.U i ⊓ 𝒱.U j : Opens X) : Set X)).evalAt p :=
      rfl
    have e3 : F j k p = (f (j, k) : MeroGermOn X ((𝒱.U j ⊓ 𝒱.U k : Opens X) : Set X)).evalAt p :=
      rfl
    rw [e1, e2, e3]
    linear_combination -heval
  -- Step 4: apply the planar holomorphic Cousin splitting.
  obtain ⟨u, hu_diff, hu_split⟩ := exists_holo_splitting_ball hr hWo hWb hcov hφ_diff hcoc
  -- Step 5: pull back to `X` and assemble a `C0` cochain witnessing `f ∈ B1`.
  set v : Fin 𝒱.n → X → ℂ := fun i => u i ∘ e with hv_def
  have hv_cd : ∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (v i) (𝒱.U i : Set X) := by
    intro i
    apply (contMDiffOn_iff_analyticOnNhd_of_subset_source (chart_mem_atlas ℂ x₀)
      (hUisub i) (𝒱.U i).2).2
    rw [show (⇑e '' (𝒱.U i : Set X)) = W i from rfl]
    apply AnalyticOnNhd.congr (hWo i) ((hu_diff i).analyticOnNhd (hWo i))
    rintro z ⟨q, hq, rfl⟩
    change u i (e q) = v i (e.symm (e q))
    rw [e.left_inv (hUisub i hq)]
    rfl
  set h : C0 (0 : Divisor X) 𝒱 := fun i =>
    ⟨MeroGermOn.mk (v i) (meromorphicOnX_of_contMDiffOn_omega (𝒱.U i).2 (hv_cd i)),
      mk_mem_linSysOn_zero (𝒱.U i).2 (hv_cd i)⟩ with hh_def
  have hpointwise : ∀ i j, ∀ p ∈ ((𝒱.U i ⊓ 𝒱.U j : Opens X) : Set X), F i j p = v j p - v i p := by
    intro i j p hp
    have hpi : p ∈ (𝒱.U i : Set X) := hp.1
    have hpj : p ∈ (𝒱.U j : Set X) := hp.2
    have hz : e p ∈ W i ∩ W j := ⟨⟨p, hpi, rfl⟩, ⟨p, hpj, rfl⟩⟩
    have hsplit := hu_split i j (e p) hz
    have hFip : φ i j (e p) = F i j p := by
      change F i j (e.symm (e p)) = F i j p
      rw [e.left_inv (hUisub i hpi)]
    change F i j p = v j p - v i p
    rw [← hFip, hsplit]
    show u j (e p) - u i (e p) = v j p - v i p
    rfl
  have hd0h : d0 (0 : Divisor X) 𝒱 h = f := by
    funext p
    obtain ⟨i, j⟩ := p
    apply Subtype.ext
    rw [d0_apply]
    change (MeroGermOn.restrict inf_le_right (h j : MeroGermOn X (𝒱.U (i, j).2 : Set X)) -
        MeroGermOn.restrict inf_le_left (h i : MeroGermOn X (𝒱.U (i, j).1 : Set X)) :
        MeroGermOn X ((𝒱.U (i, j).1 ⊓ 𝒱.U (i, j).2 : Opens X) : Set X)) =
      (f (i, j) : MeroGermOn X ((𝒱.U (i, j).1 ⊓ 𝒱.U (i, j).2 : Opens X) : Set X))
    change MeroGermOn.restrict inf_le_right (MeroGermOn.mk (v j)
        (meromorphicOnX_of_contMDiffOn_omega (𝒱.U j).2 (hv_cd j))) -
      MeroGermOn.restrict inf_le_left (MeroGermOn.mk (v i)
        (meromorphicOnX_of_contMDiffOn_omega (𝒱.U i).2 (hv_cd i))) =
      (f (i, j) : MeroGermOn X ((𝒱.U (i, j).1 ⊓ 𝒱.U (i, j).2 : Opens X) : Set X))
    rw [MeroGermOn.restrict_mk, MeroGermOn.restrict_mk,
      ← MeroGermOn.mk_holoRepr (𝒱.U (i, j).1 ⊓ 𝒱.U (i, j).2).2
        (f (i, j) : MeroGermOn X ((𝒱.U (i, j).1 ⊓ 𝒱.U (i, j).2 : Opens X) : Set X)),
      ]
    -- `rw` cannot instantiate the proof-valued arguments of `mk`; `refine` matches up to defeq
    refine MeroGermOn.mk_sub.trans ?_
    apply MeroGermOn.mk_eq_mk.2
    apply heqOn_to_evEq
    intro p hp
    change v j p - v i p = F i j p
    exact (hpointwise i j p hp).symm
  rw [← hd0h]
  exact LinearMap.mem_range_self _ _

/-! ### General-divisor twist: `subsingleton_h1Cover_of_isChartDisk`

The remaining honestly-deferred piece from the DEVIATION note above (§D9(b) of
`docs/design/dbar-solvability.md`): the general-divisor case, needed by
`dolbeault-comparison/Leray.lean`'s member-splitting step. Built here under that unit's
SPECIAL AUTHORIZATION (the cross-unit dependencies were present, it was deferred on time, not
difficulty). Route: a finite Weierstrass-factor germ `t` on `V` with `ord t = D` there
(`t w := ∏_{a ∈ S} (w - e a) ^ D a`, `S := D.support ∩ V`, pulled back through the chart
`e := chartAt ℂ x₀`); multiplying a `D`-cocycle by (restrictions of) `t` gives a `0`-cocycle,
reducing to `subsingleton_h1Cover_zero_of_isChartDisk` above; dividing a `0`-splitting by `t`
gives back a `D`-splitting. -/

section Twist

variable [T2Space X] [CompactSpace X]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [T1Space X] [T2Space X] [CompactSpace X] in
/-- A cocycle member multiplied by the restriction of a germ of divisor order exactly `D` lands in
the trivial linear system. Split out of `subsingleton_h1Cover_of_isChartDisk` to keep that proof
under the 200-line size we hold ourselves to. -/
private theorem mul_restrict_mem_linSysOn {V : Opens X} {D : Divisor X} {𝒱 : FinCover V}
    (f : C1 D 𝒱) {t : RS.MeroGermOn X (V : Set X)}
    (hWleV : ∀ p : Fin 𝒱.n × Fin 𝒱.n, (𝒱.U p.1 ⊓ 𝒱.U p.2 : Opens X) ≤ V)
    (hord_t : ∀ {x : X}, x ∈ (V : Set X) → t.ord x = (D x : WithTop ℤ)) :
    ∀ p : Fin 𝒱.n × Fin 𝒱.n,
      (RS.MeroGermOn.restrict (hWleV p) t) *
          (f p : RS.MeroGermOn X ((𝒱.U p.1 ⊓ 𝒱.U p.2 : Opens X) : Set X)) ∈
        RS.LinSysOn (0 : Divisor X) ((𝒱.U p.1 ⊓ 𝒱.U p.2 : Opens X) : Set X) := by
  intro p
  refine (mem_linSysOn_iff_of_isOpen ((𝒱.U p.1 ⊓ 𝒱.U p.2 : Opens X)).2).2 ?_
  intro x hx
  have hordmul : (RS.MeroGermOn.restrict (hWleV p) t *
      (f p : RS.MeroGermOn X ((𝒱.U p.1 ⊓ 𝒱.U p.2 : Opens X) : Set X))).ord x =
      (RS.MeroGermOn.restrict (hWleV p) t).ord x +
        (f p : RS.MeroGermOn X ((𝒱.U p.1 ⊓ 𝒱.U p.2 : Opens X) : Set X)).ord x :=
    RS.MeroGermOn.ord_mul ((𝒱.U p.1 ⊓ 𝒱.U p.2 : Opens X)).2 hx _ _
  rw [hordmul, RS.MeroGermOn.ord_restrict (hWleV p) ((𝒱.U p.1 ⊓ 𝒱.U p.2 : Opens X)).2 V.2 hx,
    hord_t (hWleV p hx)]
  have hfp : ((-(D x) : ℤ) : WithTop ℤ) ≤
      (f p : RS.MeroGermOn X ((𝒱.U p.1 ⊓ 𝒱.U p.2 : Opens X) : Set X)).ord x :=
    (mem_linSysOn_iff_of_isOpen ((𝒱.U p.1 ⊓ 𝒱.U p.2 : Opens X)).2).1 (f p).2 x hx
  have hz0 : ((-(0 : Divisor X) x : ℤ) : WithTop ℤ) = 0 := by simp
  have hcancel : ((D x : ℤ) : WithTop ℤ) + ((-(D x) : ℤ) : WithTop ℤ) = 0 := by
    rw [← WithTop.coe_add, add_neg_cancel, WithTop.coe_zero]
  rw [hz0, ← hcancel]
  gcongr

/-- **MAIN deliverable** (owed to cech §7 / consumed by dolbeault-comparison's Leray 12.8):
disk acyclicity of the Čech complex of `𝒪_D` on chart disks, for an ARBITRARY divisor `D`. -/
theorem subsingleton_h1Cover_of_isChartDisk {V : Opens X} (hV : IsChartDisk V) (D : Divisor X)
    (𝒱 : FinCover V) : Subsingleton (H1Cover D 𝒱) := by
  rw [subsingleton_h1Cover_iff]
  intro f hf
  obtain ⟨x₀, r, hr, hx₀, hVs, hVim⟩ := hV
  set e := chartAt ℂ x₀ with he_def
  have heatlas : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X := IsManifold.chart_mem_maximalAtlas x₀
  classical
  -- The finite twisting set `S := D.support ∩ V`.
  have hSfin : (D.support ∩ (V : Set X)).Finite :=
    (D.finiteSupport isCompact_univ).subset Set.inter_subset_left
  set S : Finset X := hSfin.toFinset with hS_def
  have hSmem : ∀ {a : X}, a ∈ S ↔ D a ≠ 0 ∧ a ∈ (V : Set X) := by
    intro a; rw [hS_def, hSfin.mem_toFinset]; exact Iff.rfl
  have hSsubV : ∀ a ∈ S, a ∈ (V : Set X) := fun a ha => (hSmem.1 ha).2
  -- The Weierstrass-factor function on the chart target.
  set q : ℂ → ℂ := fun w => ∏ a ∈ S, (w - e a) ^ (D a) with hq_def
  have hq_eq : q = ∏ a ∈ S, (fun w : ℂ => (w - e a) ^ (D a)) := by
    funext w; rw [hq_def, Finset.prod_apply]
  have hq_mero : ∀ z : ℂ, MeromorphicAt q z := by
    rw [hq_eq]
    exact fun z => MeromorphicAt.prod fun a _ =>
      MeromorphicAt.zpow ((analyticAt_id.sub analyticAt_const).meromorphicAt) (D a)
  -- Transport `q ∘ e ∘ e.symm = q` near `e x` for `x ∈ V`.
  have hEq : ∀ {x : X}, x ∈ (V : Set X) → (q ∘ e ∘ e.symm) =ᶠ[nhds (e x)] q := by
    intro x hx
    have h2 : ∀ᶠ z in nhds (e x), e (e.symm z) = z := by
      filter_upwards [e.open_target.eventually_mem (e.map_source (hVs hx))] with z hz
        using e.right_inv hz
    filter_upwards [h2] with z hz
    change q (e (e.symm z)) = q z
    rw [hz]
  have hqe_mero : MeromorphicOnX (q ∘ e) (V : Set X) := by
    intro x hx
    rw [meromorphicAtX_iff_of_mem_source heatlas (hVs hx)]
    exact MeromorphicAt.congr (hq_mero (e x)) ((hEq hx).symm.filter_mono nhdsWithin_le_nhds)
  set t : MeroGermOn X (V : Set X) := MeroGermOn.mk (q ∘ e) hqe_mero with ht_def
  -- The order of a single Weierstrass atom.
  have hatom : ∀ {x : X}, x ∈ (V : Set X) → ∀ {a : X}, a ∈ S →
      meromorphicOrderAt (fun w => (w - e a) ^ (D a)) (e x) =
        if a = x then (D x : WithTop ℤ) else 0 := by
    intro x hx a ha
    by_cases hax : a = x
    · subst hax
      rw [if_pos rfl]
      exact meromorphicOrderAt_zpow_id_sub_const
    · rw [if_neg hax]
      have hane : e a ≠ e x := fun heq => hax (e.injOn (hVs (hSsubV a ha)) (hVs hx) heq)
      have hval : (e x - e a) ≠ 0 := sub_ne_zero.mpr (Ne.symm hane)
      have hanalytic : AnalyticAt ℂ (fun w => w - e a) (e x) := analyticAt_id.sub analyticAt_const
      have hzpow : AnalyticAt ℂ (fun w => (w - e a) ^ (D a)) (e x) := hanalytic.zpow hval
      rw [hzpow.meromorphicOrderAt_eq, hzpow.analyticOrderAt_eq_zero.mpr (zpow_ne_zero _ hval)]
      rfl
  -- The order of `t` on `V`: `ord t x = D x`.
  have hord_t : ∀ {x : X}, x ∈ (V : Set X) → t.ord x = (D x : WithTop ℤ) := by
    intro x hx
    rw [ht_def, MeroGermOn.ord_mk V.2 hx, ordAtX_eq_of_mem_source heatlas (hVs hx)]
    have hcong : meromorphicOrderAt ((q ∘ e) ∘ e.symm) (e x) = meromorphicOrderAt q (e x) :=
      meromorphicOrderAt_congr ((hEq hx).filter_mono nhdsWithin_le_nhds)
    rw [hcong, hq_eq]
    have hmerAtoms : ∀ a ∈ S, MeromorphicAt (fun w => (w - e a) ^ (D a)) (e x) := fun a _ =>
      MeromorphicAt.zpow ((analyticAt_id.sub analyticAt_const).meromorphicAt) (D a)
    rw [meromorphicOrderAt_prod hmerAtoms, Finset.sum_congr rfl fun a ha => hatom hx ha,
      Finset.sum_ite_eq' S x (fun _ : X => (D x : WithTop ℤ))]
    by_cases hxS : x ∈ S
    · rw [if_pos hxS]
    · rw [if_neg hxS]
      have hDx0 : D x = 0 := by
        by_contra hDx
        exact hxS (hSmem.2 ⟨hDx, hx⟩)
      rw [hDx0]; rfl
  -- Cancellation `t * t⁻¹ = 1` (off the finite set `S`, codiscreteWithin `V`).
  have ht_mul_inv : t * t⁻¹ = 1 := by
    rw [ht_def, MeroGermOn.mk_inv, MeroGermOn.mk_mul, ← MeroGermOn.mk_one (U := (V : Set X))]
    apply MeroGermOn.mk_eq_mk.2
    refine (eventuallyEq_codiscreteWithin_iff_of_isOpen V.2).2 ?_
    intro x hxV
    have hclosed : IsClosed ((S.erase x : Finset X) : Set X) := (S.erase x).isClosed
    have hnbhd : (V : Set X) ∩ ((S.erase x : Finset X) : Set X)ᶜ ∈ nhds x :=
      IsOpen.mem_nhds (V.2.inter hclosed.isOpen_compl) ⟨hxV, Finset.notMem_erase x S⟩
    have hpunct : (V : Set X) ∩ ((S.erase x : Finset X) : Set X)ᶜ ∈ nhdsWithin x {x}ᶜ :=
      mem_nhdsWithin_of_mem_nhds hnbhd
    filter_upwards [hpunct, self_mem_nhdsWithin] with y hy hyne
    have hyV : y ∈ (V : Set X) := hy.1
    have hyne' : y ≠ x := hyne
    have hyS : y ∉ (S.erase x : Finset X) := fun hmem => hy.2 (Finset.mem_coe.mpr hmem)
    have hyS' : y ∉ S := fun hmem => hyS (Finset.mem_erase.mpr ⟨hyne', hmem⟩)
    change (q ∘ e) y * ((q ∘ e) y)⁻¹ = 1
    apply mul_inv_cancel₀
    change q (e y) ≠ 0
    rw [hq_def]
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    apply zpow_ne_zero
    refine sub_ne_zero.mpr fun heq => hyS' ?_
    have hya := e.injOn (hVs hyV) (hVs (hSsubV a ha)) heq
    exact hya ▸ ha
  -- Twist the `D`-cocycle `f` into a `0`-cocycle `g`.
  set W : Fin 𝒱.n × Fin 𝒱.n → Opens X := fun p => 𝒱.U p.1 ⊓ 𝒱.U p.2 with hW_def
  have hWleV : ∀ p, W p ≤ V := fun p => inf_le_left.trans (𝒱.le_base p.1)
  have hmem_g := mul_restrict_mem_linSysOn f hWleV hord_t
  set g : C1 (0 : Divisor X) 𝒱 := fun p =>
    ⟨(RS.MeroGermOn.restrict (hWleV p) t) * (f p : RS.MeroGermOn X (W p : Set X)), hmem_g p⟩
    with hg_def
  have hg_coe : ∀ p, (g p : RS.MeroGermOn X (W p : Set X)) =
      (RS.MeroGermOn.restrict (hWleV p) t) * (f p : RS.MeroGermOn X (W p : Set X)) := fun _ => rfl
  have hg_Z1 : g ∈ Z1 (0 : Divisor X) 𝒱 := by
    rw [mem_Z1_iff]
    rintro ⟨i, j, k⟩
    apply Subtype.ext
    rw [d1_apply]
    set Uijk : Opens X := 𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k with hUijk_def
    have hUijkV : Uijk ≤ V := (inf_le_left.trans inf_le_left).trans (𝒱.le_base i)
    have hbc : Uijk ≤ 𝒱.U j ⊓ 𝒱.U k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have hac : Uijk ≤ 𝒱.U i ⊓ 𝒱.U k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hab : Uijk ≤ 𝒱.U i ⊓ 𝒱.U j := inf_le_left
    have key := Z1.rel_res D hf i j k (le_refl Uijk) hbc hac hab
    have hval : (LinSysOn.restrictL D hbc (f (j, k)) : RS.MeroGermOn X (Uijk : Set X)) -
        (LinSysOn.restrictL D hac (f (i, k)) : RS.MeroGermOn X (Uijk : Set X)) +
        (LinSysOn.restrictL D hab (f (i, j)) : RS.MeroGermOn X (Uijk : Set X)) = 0 := by
      have hcast := congrArg Subtype.val key
      simpa using hcast
    rw [restrictL_apply_coe, restrictL_apply_coe, restrictL_apply_coe] at hval
    change (LinSysOn.restrictL (0 : Divisor X) hbc (g (j, k)) : RS.MeroGermOn X (Uijk : Set X)) -
        (LinSysOn.restrictL (0 : Divisor X) hac (g (i, k)) : RS.MeroGermOn X (Uijk : Set X)) +
        (LinSysOn.restrictL (0 : Divisor X) hab (g (i, j)) : RS.MeroGermOn X (Uijk : Set X)) = 0
    rw [restrictL_apply_coe, restrictL_apply_coe, restrictL_apply_coe, hg_coe, hg_coe, hg_coe,
      map_mul, map_mul, map_mul,
      MeroGermOn.restrict_restrict (hWleV (j, k)) hbc t,
      MeroGermOn.restrict_restrict (hWleV (i, k)) hac t,
      MeroGermOn.restrict_restrict (hWleV (i, j)) hab t]
    have hcomb : (RS.MeroGermOn.restrict hUijkV t) *
          (RS.MeroGermOn.restrict hbc (f (j, k) : RS.MeroGermOn X (W (j, k) : Set X))) -
        (RS.MeroGermOn.restrict hUijkV t) *
          (RS.MeroGermOn.restrict hac (f (i, k) : RS.MeroGermOn X (W (i, k) : Set X))) +
        (RS.MeroGermOn.restrict hUijkV t) *
          (RS.MeroGermOn.restrict hab (f (i, j) : RS.MeroGermOn X (W (i, j) : Set X))) =
        (RS.MeroGermOn.restrict hUijkV t) *
          ((RS.MeroGermOn.restrict hbc (f (j, k) : RS.MeroGermOn X (W (j, k) : Set X))) -
            (RS.MeroGermOn.restrict hac (f (i, k) : RS.MeroGermOn X (W (i, k) : Set X))) +
            (RS.MeroGermOn.restrict hab (f (i, j) : RS.MeroGermOn X (W (i, j) : Set X)))) := by
      ring
    rw [hcomb, hval, mul_zero]
  -- Apply the `D = 0` case to split `g`, then untwist the splitting for `f`.
  have hgB1 : (g : C1 (0 : Divisor X) 𝒱) ∈ B1 (0 : Divisor X) 𝒱 :=
    ((subsingleton_h1Cover_iff (0 : Divisor X) 𝒱).mp
      (subsingleton_h1Cover_zero_of_isChartDisk ⟨x₀, r, hr, hx₀, hVs, hVim⟩ 𝒱)) hg_Z1
  obtain ⟨h, hdh⟩ := hgB1
  have hUiV : ∀ i : Fin 𝒱.n, 𝒱.U i ≤ V := 𝒱.le_base
  have hmem_h' : ∀ i : Fin 𝒱.n,
      (RS.MeroGermOn.restrict (hUiV i) t⁻¹) * (h i : RS.MeroGermOn X (𝒱.U i : Set X)) ∈
        RS.LinSysOn D (𝒱.U i : Set X) := by
    intro i
    refine (mem_linSysOn_iff_of_isOpen (𝒱.U i).2).2 ?_
    intro x hx
    have hordmul : (RS.MeroGermOn.restrict (hUiV i) t⁻¹ *
        (h i : RS.MeroGermOn X (𝒱.U i : Set X))).ord x =
        (RS.MeroGermOn.restrict (hUiV i) t⁻¹).ord x +
          (h i : RS.MeroGermOn X (𝒱.U i : Set X)).ord x :=
      RS.MeroGermOn.ord_mul (𝒱.U i).2 hx _ _
    rw [hordmul, RS.MeroGermOn.ord_restrict (hUiV i) (𝒱.U i).2 V.2 hx,
      RS.MeroGermOn.ord_inv V.2 (hUiV i hx) t, hord_t (hUiV i hx)]
    have hhi : (0 : WithTop ℤ) ≤ (h i : RS.MeroGermOn X (𝒱.U i : Set X)).ord x := by
      have hmem := (mem_linSysOn_iff_of_isOpen (𝒱.U i).2).1 (h i).2 x hx
      simpa using hmem
    exact le_add_of_nonneg_right hhi
  set h' : C0 D 𝒱 := fun i =>
    ⟨(RS.MeroGermOn.restrict (hUiV i) t⁻¹) * (h i : RS.MeroGermOn X (𝒱.U i : Set X)), hmem_h' i⟩
    with hh'_def
  have hh'_coe : ∀ i, (h' i : RS.MeroGermOn X (𝒱.U i : Set X)) =
      (RS.MeroGermOn.restrict (hUiV i) t⁻¹) * (h i : RS.MeroGermOn X (𝒱.U i : Set X)) :=
    fun _ => rfl
  have ht_inv_mul : t⁻¹ * t = 1 := (mul_comm t⁻¹ t).trans ht_mul_inv
  have hd0h' : d0 D 𝒱 h' = (f : C1 D 𝒱) := by
    funext p
    obtain ⟨i, j⟩ := p
    have hij_r : 𝒱.U i ⊓ 𝒱.U j ≤ 𝒱.U j := inf_le_right
    have hij_l : 𝒱.U i ⊓ 𝒱.U j ≤ 𝒱.U i := inf_le_left
    apply Subtype.ext
    have hcg0 := congrFun hdh (i, j)
    rw [d0_apply] at hcg0
    have hcg : (RS.MeroGermOn.restrict hij_r (h j : RS.MeroGermOn X (𝒱.U j : Set X)) -
        RS.MeroGermOn.restrict hij_l (h i : RS.MeroGermOn X (𝒱.U i : Set X)) :
        RS.MeroGermOn X (𝒱.U i ⊓ 𝒱.U j : Set X)) =
        (g (i, j) : RS.MeroGermOn X (𝒱.U i ⊓ 𝒱.U j : Set X)) := by
      have hcast := congrArg Subtype.val hcg0
      exact hcast
    change (RS.MeroGermOn.restrict hij_r (h' j : RS.MeroGermOn X (𝒱.U j : Set X)) -
        RS.MeroGermOn.restrict hij_l (h' i : RS.MeroGermOn X (𝒱.U i : Set X)) :
        RS.MeroGermOn X (𝒱.U i ⊓ 𝒱.U j : Set X)) =
      (f (i, j) : RS.MeroGermOn X (𝒱.U i ⊓ 𝒱.U j : Set X))
    rw [hh'_coe, hh'_coe, map_mul, map_mul,
      MeroGermOn.restrict_restrict (hUiV j) hij_r t⁻¹,
      MeroGermOn.restrict_restrict (hUiV i) hij_l t⁻¹]
    have hcomb : (RS.MeroGermOn.restrict (hWleV (i, j)) t⁻¹) *
          (RS.MeroGermOn.restrict hij_r (h j : RS.MeroGermOn X (𝒱.U j : Set X))) -
        (RS.MeroGermOn.restrict (hWleV (i, j)) t⁻¹) *
          (RS.MeroGermOn.restrict hij_l (h i : RS.MeroGermOn X (𝒱.U i : Set X))) =
        (RS.MeroGermOn.restrict (hWleV (i, j)) t⁻¹) *
          ((RS.MeroGermOn.restrict hij_r (h j : RS.MeroGermOn X (𝒱.U j : Set X))) -
            (RS.MeroGermOn.restrict hij_l (h i : RS.MeroGermOn X (𝒱.U i : Set X)))) := by
      ring
    rw [hcomb, hcg, hg_coe, ← mul_assoc, ← map_mul, ht_inv_mul, map_one, one_mul]
  exact ⟨h', hd0h'⟩

end Twist

end RS

/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Cech.Skyscraper
import LeanPool.JacobianDiffgeo.Cech.WindowRank

/-!
# The six-term skyscraper fragment (CC8, D7, proof plan §6.9(c)-(g))

Unit: cech-cohomology (`docs/design/cech-cohomology.md` §4.7, §6.9).

* `C1.retype_mem_Z1'`: the general (non-coboundary) retype-preserves-`Z1` fact.
* `h1CoverIncl_mk_retype`: the `D`-inclusion of a retyped `Z1 D 𝒰` class recovers the original
  `Z1 D' 𝒰` class.
* `memLD_of_isAdapted`: on a cover adapted to `diffSupp D D'`, every `Z1 D' 𝒰`-cocycle already
  satisfies the (smaller) `D`-bound — diagonal components vanish to order `⊤`
  (`Z1.ord_diag`), off-diagonal components avoid the finite set where `D ≠ D'`
  (`FinCover.IsAdapted.not_mem_inf`), so `D = D'` pointwise there.
* `H1Incl_surjective`: **no `H²`, no long exact sequence, no snake lemma** — every class of
  `H1 D'` is already represented, on a suitably adapted cover, by a genuine `Z1 D`-cocycle.
* `exists_tail_approx` ("Lemma B"): any germ near `q` of order `≥ -d'` is approximated, to
  order `> -d - 1` at `q`, by a chart-source germ in `ordGe q (-d')` — a finite Laurent tail,
  built by iterating the one-step leading-coefficient subtraction (`exists_tail_step`; same
  correction step as WindowRank's splitting, redone on an arbitrary open `W ∋ q` because
  `leadCoeff` is chart-source-bound).
* `windowDefect` + `Realizes` (§6.9(c), D7): the pointwise-`ord` realization predicate. The
  design's `(w q).out` form is replaced by quantification over *all* representatives of `w q`
  (equivalent by `windowDefect_bound_of_mk_eq`; strictly easier to consume).
* `exists_realization` (§6.9(c)) and `mlClass_eq_of_realizes` (§6.9(d), "Lemma A" — proved
  without any adaptedness hypothesis: only the `Realizes` bounds and `D = D'` off `diffSupp`
  enter).
* `windowConnect`/`windowConnect_spec` (§6.9(d)): the connecting map `Window D D' →ₗ H¹(D)`.
* `exact_windowMap_windowConnect` (§6.9(e)), `exact_windowConnect_H1Incl` (§6.9(f)):
  with `Window.lean`'s `exact_inclusion_windowMap`/`inclusion_injective` and
  `H1Incl_surjective` below, this completes the six-term fragment
  `0 → L(D) → L(D') → Window D D' → H¹(D) → H¹(D') → 0`.
-/

open scoped ContDiff Manifold Topology
open Set Filter TopologicalSpace RS.Cech


namespace RS.Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Ω : Opens X} {𝒰 : FinCover Ω} {D D' : RS.Divisor X}

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- General (non-coboundary) version of `C1.retype_mem_Z1`: retyping a `Z1 D'`-cocycle whose
components all satisfy the `D`-bound gives a `Z1 D`-cocycle. -/
theorem C1.retype_mem_Z1' {f : C1 D' 𝒰} (hf : f ∈ Z1 D' 𝒰) (hmem : f.MemLD D) :
    C1.retype f hmem ∈ Z1 D 𝒰 := by
  rw [mem_Z1_iff]
  intro t
  apply Subtype.ext
  have hcoe : (d1 D 𝒰 (C1.retype f hmem) t :
      RS.MeroGermOn X ((𝒰.U t.1 ⊓ 𝒰.U t.2.1 ⊓ 𝒰.U t.2.2 : Opens X) : Set X)) =
      (d1 D' 𝒰 f t :
      RS.MeroGermOn X ((𝒰.U t.1 ⊓ 𝒰.U t.2.1 ⊓ 𝒰.U t.2.2 : Opens X) : Set X)) := rfl
  rw [hcoe, (mem_Z1_iff D' 𝒰 f).1 hf t]
  simp

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- The `D`-inclusion of a retyped `Z1 D 𝒰` class recovers the original `Z1 D' 𝒰` class. -/
theorem h1CoverIncl_mk_retype (h : D ≤ D') {f : C1 D' 𝒰} (hf : f ∈ Z1 D' 𝒰) (hmem : f.MemLD D) :
    h1CoverIncl D 𝒰 h (H1Cover.mk D 𝒰 ⟨C1.retype f hmem, C1.retype_mem_Z1' hf hmem⟩) =
      H1Cover.mk D' 𝒰 ⟨f, hf⟩ := by
  rw [h1CoverIncl_mk]
  congr 1

/-! ### Small order arithmetic helpers -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
private theorem le_ord_sub {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U)
    {φ ψ : RS.MeroGermOn X U} {m : WithTop ℤ} (h1 : m ≤ φ.ord x) (h2 : m ≤ ψ.ord x) :
    m ≤ (φ - ψ).ord x := by
  rw [sub_eq_add_neg]
  refine le_trans (le_min h1 ?_) (RS.MeroGermOn.ord_add hU hx φ (-ψ))
  rw [RS.MeroGermOn.ord_neg]
  exact h2

private theorem one_le_of_pos {s : WithTop ℤ} (h : 0 < s) : 1 ≤ s := by
  rcases eq_or_ne s ⊤ with rfl | hs
  · exact le_top
  · obtain ⟨k, rfl⟩ := WithTop.ne_top_iff_exists.1 hs
    have hk : (0 : ℤ) < k := by exact_mod_cast h
    exact_mod_cast (show (1 : ℤ) ≤ k by omega)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem WindowAt.mk_surjective (p : X) (d d' : ℤ) : Function.Surjective (WindowAt.mk p d d') :=
  Submodule.mkQ_surjective _

/-! ### Local tail approximation ("Lemma B", §6.9(c) input)

A germ `γ` near `q` of order `≥ -d'` at `q` is approximated to order `≥ -d` by a genuine
chart-source germ in `ordGe q (-d')` — a finite Laurent tail. Built by iterating the one-step
leading-coefficient subtraction (the same correction as `WindowRank.lean`'s splitting, redone
here on an arbitrary open `W ∋ q` because `leadCoeff` is chart-source-bound). -/

theorem tailGerm_mul_tailGerm_neg [T1Space X] (q : X) (m : ℤ) :
    tailGerm q m * tailGerm q (-m) = 1 := by
  rw [tailGerm, tailGerm, RS.MeroGermOn.mk_mul, ← RS.MeroGermOn.mk_one, RS.MeroGermOn.mk_eq_mk,
    RS.eventuallyEq_codiscreteWithin_iff_of_isOpen (chartAt ℂ q).open_source]
  intro x hx
  have hsrc : ∀ᶠ y in 𝓝[≠] x, y ∈ (chartAt ℂ q).source :=
    eventually_nhdsWithin_of_eventually_nhds ((chartAt ℂ q).open_source.mem_nhds hx)
  have hne : ∀ᶠ y in 𝓝[≠] x, y ≠ q := by
    rcases eq_or_ne x q with rfl | hxq
    · exact self_mem_nhdsWithin
    · exact eventually_nhdsWithin_of_eventually_nhds
        (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.2 hxq))
  filter_upwards [hsrc, hne] with y hy hyq
  have hne0 : chartAt ℂ q y - chartAt ℂ q q ≠ 0 := by
    rw [sub_ne_zero]
    intro heq
    apply hyq
    have hsymm := congrArg (chartAt ℂ q).symm heq
    rwa [(chartAt ℂ q).left_inv hy, (chartAt ℂ q).left_inv (mem_chart_source ℂ q)] at hsymm
  change (chartAt ℂ q y - chartAt ℂ q q) ^ m * (chartAt ℂ q y - chartAt ℂ q q) ^ (-m) = 1
  rw [← zpow_add₀ hne0, add_neg_cancel, zpow_zero]

/-- One-step leading-coefficient subtraction on an arbitrary open `W ∋ q` inside the chart
source: subtracting `c • θ_{q,m}` (for the canonical value `c` of `θ_{q,-m}·γ` at `q`) raises
the order at `q` by at least one. -/
private theorem exists_tail_step [T1Space X] (q : X) {W : Set X} (hW : IsOpen W)
    (hWs : W ⊆ (chartAt ℂ q).source) (hq : q ∈ W) {m : ℤ} (γ : RS.MeroGermOn X W)
    (hγ : (m : WithTop ℤ) ≤ γ.ord q) :
    ∃ c : ℂ, ((m + 1 : ℤ) : WithTop ℤ) ≤
      (γ - c • RS.MeroGermOn.restrict hWs (tailGerm q m)).ord q := by
  set T : RS.MeroGermOn X W := RS.MeroGermOn.restrict hWs (tailGerm q m) with hT_def
  set t : RS.MeroGermOn X W := RS.MeroGermOn.restrict hWs (tailGerm q (-m)) with ht_def
  have hordT : T.ord q = (m : WithTop ℤ) := by
    rw [hT_def, RS.MeroGermOn.ord_restrict hWs hW (chartAt ℂ q).open_source hq, ord_tailGerm_self]
  have hordt : t.ord q = ((-m : ℤ) : WithTop ℤ) := by
    rw [ht_def, RS.MeroGermOn.ord_restrict hWs hW (chartAt ℂ q).open_source hq, ord_tailGerm_self]
  have hTt : T * t = 1 := by
    rw [hT_def, ht_def, ← map_mul, tailGerm_mul_tailGerm_neg, map_one]
  set u : RS.MeroGermOn X W := t * γ with hu_def
  have hordu : (0 : WithTop ℤ) ≤ u.ord q := by
    rw [hu_def, RS.MeroGermOn.ord_mul hW hq, hordt]
    have hstep : (((-m : ℤ) : WithTop ℤ) + (m : WithTop ℤ)) ≤ ((-m : ℤ) : WithTop ℤ) + γ.ord q :=
      add_le_add le_rfl hγ
    have hz : (((-m : ℤ) : WithTop ℤ) + (m : WithTop ℤ)) = 0 := by
      exact_mod_cast (show (-m + m : ℤ) = 0 by ring)
    rwa [hz] at hstep
  set c : ℂ := u.evalAt q with hc_def
  refine ⟨c, ?_⟩
  have hpos : (0 : WithTop ℤ) < (u - c • 1).ord q := by
    rcases eq_or_ne c 0 with hc0 | hc0
    · rw [hc0, zero_smul, sub_zero]
      have hu0 : u.evalAt q = 0 := by rw [← hc_def]; exact hc0
      exact (RS.Cech.MeroGermOn.evalAt_eq_zero_iff hW hq u hordu).1 hu0
    · have hord1 : ((-c) • (1 : RS.MeroGermOn X W)).ord q = 0 := by
        rw [RS.MeroGermOn.ord_smul hW hq (neg_ne_zero.2 hc0), RS.MeroGermOn.ord_one hW hq]
      have hordsum : (0 : WithTop ℤ) ≤ (u + (-c) • 1).ord q :=
        le_trans (le_min hordu (le_of_eq hord1.symm)) (RS.MeroGermOn.ord_add hW hq _ _)
      have heval1 : (1 : RS.MeroGermOn X W).evalAt q = 1 := by
        rw [← RS.MeroGermOn.mk_one]
        exact RS.MeroGermOn.evalAt_mk_of_contMDiffAt hW hq contMDiffAt_const
      have hevalsum : (u + (-c) • 1).evalAt q = 0 := by
        rw [RS.MeroGermOn.evalAt_add hW hq hordu (le_of_eq hord1.symm),
          RS.MeroGermOn.evalAt_smul hW hq (le_of_eq (RS.MeroGermOn.ord_one hW hq).symm), heval1,
          ← hc_def]
        ring
      have hsub_eq : u - c • 1 = u + (-c) • 1 := by rw [sub_eq_add_neg, neg_smul]
      rw [hsub_eq]
      exact (RS.Cech.MeroGermOn.evalAt_eq_zero_iff hW hq _ hordsum).1 hevalsum
  have hfactor : γ - c • T = T * (u - c • 1) := by
    rw [hu_def, mul_sub, ← mul_assoc, hTt, one_mul, mul_smul_comm, mul_one]
  rw [hfactor, RS.MeroGermOn.ord_mul hW hq, hordT]
  have hcast : ((m + 1 : ℤ) : WithTop ℤ) = (m : WithTop ℤ) + 1 := by norm_cast
  rw [hcast]
  exact add_le_add le_rfl (one_le_of_pos hpos)

private theorem exists_tail_approx_aux [T1Space X] (q : X) {W : Set X} (hW : IsOpen W)
    (hWs : W ⊆ (chartAt ℂ q).source) (hq : q ∈ W) :
    ∀ (n : ℕ) (d d' : ℤ), d' - d ≤ (n : ℤ) →
      ∀ γ : RS.MeroGermOn X W, ((-d' : ℤ) : WithTop ℤ) ≤ γ.ord q →
      ∃ ψ : ordGe q (-d'), ((-d : ℤ) : WithTop ℤ) ≤
        (γ - RS.MeroGermOn.restrict hWs
          (ψ : RS.MeroGermOn X ((chartAt ℂ q).source))).ord q := by
  intro n
  induction n with
  | zero =>
    intro d d' hdd γ hγ
    refine ⟨0, ?_⟩
    have h0 : RS.MeroGermOn.restrict hWs ((0 : ordGe q (-d')) : RS.MeroGermOn X _) = 0 := by
      rw [ZeroMemClass.coe_zero, map_zero]
    rw [h0, sub_zero]
    refine le_trans ?_ hγ
    exact_mod_cast (show (-d : ℤ) ≤ -d' by omega)
  | succ n ih =>
    intro d d' hdd γ hγ
    by_cases hcase : d' - d ≤ (n : ℤ)
    · exact ih d d' hcase γ hγ
    · obtain ⟨c, hc⟩ := exists_tail_step q hW hWs hq (m := -d') γ hγ
      have hint : (-d' + 1 : ℤ) = -(d' - 1) := by ring
      rw [hint] at hc
      set γ₁ := γ - c • RS.MeroGermOn.restrict hWs (tailGerm q (-d')) with hγ₁def
      obtain ⟨ψ₁, hψ₁⟩ := ih d (d' - 1) (by omega) γ₁ hc
      have htm : tailGerm q (-d') ∈ ordGe q (-d') :=
        mem_ordGe_iff.2 (le_of_eq (ord_tailGerm_self q (-d')).symm)
      have hψ₁m : (ψ₁ : RS.MeroGermOn X ((chartAt ℂ q).source)) ∈ ordGe q (-d') := by
        rw [mem_ordGe_iff]
        refine le_trans ?_ (mem_ordGe_iff.1 ψ₁.2)
        exact_mod_cast (show (-d' : ℤ) ≤ -(d' - 1) by omega)
      refine ⟨⟨c • tailGerm q (-d') + (ψ₁ : RS.MeroGermOn X _),
        Submodule.add_mem _ (Submodule.smul_mem _ c htm) hψ₁m⟩, ?_⟩
      change ((-d : ℤ) : WithTop ℤ) ≤
        (γ - RS.MeroGermOn.restrict hWs
          (c • tailGerm q (-d') + (ψ₁ : RS.MeroGermOn X ((chartAt ℂ q).source)))).ord q
      have hrw : γ - RS.MeroGermOn.restrict hWs
          (c • tailGerm q (-d') + (ψ₁ : RS.MeroGermOn X ((chartAt ℂ q).source))) =
          γ₁ - RS.MeroGermOn.restrict hWs (ψ₁ : RS.MeroGermOn X ((chartAt ℂ q).source)) := by
        rw [map_add, map_smul, hγ₁def]
        abel
      rw [hrw]
      exact hψ₁

/-- **Local tail approximation** ("Lemma B"): a germ `γ` on an open `W ∋ q` inside the chart
source with `ord_q γ ≥ -d'` is matched, to order `≥ -d` at `q`, by a chart-source germ of
`ordGe q (-d')` (a finite Laurent tail `Σ c_m θ_{q,m}`). -/
theorem exists_tail_approx [T1Space X] (q : X) {W : Set X} (hW : IsOpen W)
    (hWs : W ⊆ (chartAt ℂ q).source) (hq : q ∈ W) {d d' : ℤ} (hdd : d ≤ d')
    (γ : RS.MeroGermOn X W) (hγ : ((-d' : ℤ) : WithTop ℤ) ≤ γ.ord q) :
    ∃ ψ : ordGe q (-d'), ((-d : ℤ) : WithTop ℤ) ≤
      (γ - RS.MeroGermOn.restrict hWs (ψ : RS.MeroGermOn X ((chartAt ℂ q).source))).ord q :=
  exists_tail_approx_aux q hW hWs hq (d' - d).toNat d d' (by omega) γ hγ

/-- Meromorphic germs have isolated poles: an open zone `N ∋ q` on which `γ` is pole-free off
`q` (mero's `eventually_ordAtX_eq_zero`/`eventually_ordAtX_eq_top` on a representative). -/
private theorem exists_pole_free_zone [T1Space X] {U : Set X} (hU : IsOpen U) {q : X}
    (hq : q ∈ U) (γ : RS.MeroGermOn X U) :
    ∃ N : Opens X, q ∈ N ∧ (N : Set X) ⊆ U ∧ ∀ x ∈ (N : Set X), x ≠ q → 0 ≤ γ.ord x := by
  obtain ⟨f, hf, rfl⟩ := RS.MeroGermOn.exists_rep γ
  have hev : ∀ᶠ y in 𝓝 q, y ≠ q → 0 ≤ RS.ordAtX f y := by
    by_cases htop : RS.ordAtX f q = ⊤
    · filter_upwards [RS.eventually_ordAtX_eq_top htop] with y hy _
      rw [hy]
      exact le_top
    · have h0 := RS.eventually_ordAtX_eq_zero (hf q hq) htop
      rw [eventually_nhdsWithin_iff] at h0
      filter_upwards [h0] with y hy hyq
      rw [hy (Set.mem_compl_singleton_iff.2 hyq)]
  have hev' : {y | y ≠ q → 0 ≤ RS.ordAtX f y} ∈ 𝓝 q := hev
  obtain ⟨s, hsub, hsopen, hqs⟩ := mem_nhds_iff.1 (Filter.inter_mem (hU.mem_nhds hq) hev')
  refine ⟨⟨s, hsopen⟩, hqs, fun x hx => (hsub hx).1, fun x hx hxq => ?_⟩
  have h0 := (hsub hx).2 hxq
  rwa [RS.MeroGermOn.ord_mk hU (hsub hx).1]

/-! ### The window defect (D7): the pointwise-`ord` comparison germ -/

/-- The comparison germ of a local section `γ` (on a member `V`) against a chart-source germ
`ψ` at `q`, on the common open `V ∩ (chartAt ℂ q).source` (D7: all realization bookkeeping is a
pointwise `ord` bound on this germ). -/
noncomputable def windowDefect {V : Opens X} {q : X} (γ : RS.MeroGermOn X (V : Set X))
    (ψ : RS.MeroGermOn X ((chartAt ℂ q).source)) :
    RS.MeroGermOn X ((V : Set X) ∩ (chartAt ℂ q).source) :=
  RS.MeroGermOn.restrict Set.inter_subset_left γ -
    RS.MeroGermOn.restrict Set.inter_subset_right ψ

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- The `ord` of the defect at `q` can be computed after restricting both germs to any open
`T ∋ q` inside both domains (the normalization workhorse for all defect bookkeeping). -/
theorem windowDefect_ord_congr {V : Opens X} {q : X} {T : Set X} (hT : IsOpen T)
    (hTV : T ⊆ (V : Set X)) (hTs : T ⊆ (chartAt ℂ q).source) (hqT : q ∈ T)
    (γ : RS.MeroGermOn X (V : Set X)) (ψ : RS.MeroGermOn X ((chartAt ℂ q).source)) :
    (windowDefect γ ψ).ord q =
      (RS.MeroGermOn.restrict hTV γ - RS.MeroGermOn.restrict hTs ψ).ord q := by
  have hsub : T ⊆ (V : Set X) ∩ (chartAt ℂ q).source := Set.subset_inter hTV hTs
  rw [← RS.MeroGermOn.ord_restrict hsub hT (V.2.inter (chartAt ℂ q).open_source) hqT
    (windowDefect γ ψ)]
  congr 1
  rw [windowDefect, map_sub, RS.MeroGermOn.restrict_restrict, RS.MeroGermOn.restrict_restrict]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Restricting the local section to a smaller member does not change the defect's `ord`. -/
theorem windowDefect_ord_restrict {V V' : Opens X} {q : X} (hVV' : V' ≤ V) (hq : q ∈ V')
    (γ : RS.MeroGermOn X (V : Set X)) (ψ : RS.MeroGermOn X ((chartAt ℂ q).source)) :
    (windowDefect (RS.MeroGermOn.restrict hVV' γ) ψ).ord q = (windowDefect γ ψ).ord q := by
  rw [windowDefect_ord_congr (V'.2.inter (chartAt ℂ q).open_source)
    (fun x hx => hVV' hx.1) Set.inter_subset_right ⟨hq, mem_chart_source ℂ q⟩ γ ψ]
  congr 1
  rw [windowDefect]
  congr 1
  exact RS.MeroGermOn.restrict_restrict _ _ γ

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Rep-change: the defect bound only depends on the `WindowAt`-class of the chart-source germ
(two representatives differ by `ordGe q (-dq)`, which is absorbed by `ord_add`). This is why
`Realizes` may quantify over all representatives. -/
theorem windowDefect_bound_of_mk_eq {V : Opens X} {q : X} (hq : q ∈ V) {dq d'q : ℤ}
    {γ : RS.MeroGermOn X (V : Set X)} {ψ₀ ψ : ordGe q (-d'q)}
    (hmk : WindowAt.mk q dq d'q ψ₀ = WindowAt.mk q dq d'q ψ)
    (hb : ((-dq : ℤ) : WithTop ℤ) ≤
      (windowDefect γ (ψ₀ : RS.MeroGermOn X ((chartAt ℂ q).source))).ord q) :
    ((-dq : ℤ) : WithTop ℤ) ≤
      (windowDefect γ (ψ : RS.MeroGermOn X ((chartAt ℂ q).source))).ord q := by
  have hz : WindowAt.mk q dq d'q (ψ₀ - ψ) = 0 := by rw [map_sub, hmk, sub_self]
  rw [WindowAt.mk_eq_zero_iff] at hz
  have hzc : ((-dq : ℤ) : WithTop ℤ) ≤
      ((ψ₀ : RS.MeroGermOn X ((chartAt ℂ q).source)) -
        (ψ : RS.MeroGermOn X ((chartAt ℂ q).source))).ord q := hz
  have hopen : IsOpen ((V : Set X) ∩ (chartAt ℂ q).source) :=
    V.2.inter (chartAt ℂ q).open_source
  have hqmem : q ∈ (V : Set X) ∩ (chartAt ℂ q).source := ⟨hq, mem_chart_source ℂ q⟩
  have hdec : windowDefect γ (ψ : RS.MeroGermOn X ((chartAt ℂ q).source)) =
      windowDefect γ (ψ₀ : RS.MeroGermOn X ((chartAt ℂ q).source)) +
        RS.MeroGermOn.restrict Set.inter_subset_right
          ((ψ₀ : RS.MeroGermOn X ((chartAt ℂ q).source)) -
            (ψ : RS.MeroGermOn X ((chartAt ℂ q).source))) := by
    rw [windowDefect, windowDefect, map_sub]
    abel
  rw [hdec]
  refine le_trans (le_min hb ?_) (RS.MeroGermOn.ord_add hopen hqmem _ _)
  rw [RS.MeroGermOn.ord_restrict Set.inter_subset_right hopen (chartAt ℂ q).open_source hqmem]
  exact hzc

/-! ### `C1.MemLD` closure properties -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem C1.MemLD.res {𝒱 : FinCover Ω} {f : C1 D' 𝒰} (hf : f.MemLD D)
    (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ) : (resC1 D' τ hτ f).MemLD D := by
  intro p
  change RS.MeroGermOn.restrict (inf_le_inf (hτ p.1) (hτ p.2))
      (f (τ p.1, τ p.2) : RS.MeroGermOn X ((𝒰.U (τ p.1) ⊓ 𝒰.U (τ p.2) : Opens X) : Set X)) ∈
    RS.LinSysOn D ((𝒱.U p.1 ⊓ 𝒱.U p.2 : Opens X) : Set X)
  exact RS.restrict_mem_linSysOn (inf_le_inf (hτ p.1) (hτ p.2))
    (𝒱.U p.1 ⊓ 𝒱.U p.2).isOpen (𝒰.U (τ p.1) ⊓ 𝒰.U (τ p.2)).isOpen (hf (τ p.1, τ p.2))

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem memLD_d0_res {𝒱 : FinCover Ω} {g : C0 D' 𝒰} (hg : (d0 D' 𝒰 g).MemLD D)
    (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ) :
    (d0 D' 𝒱 (resC0 D' τ hτ g)).MemLD D := by
  have hcomm : resC1 D' τ hτ (d0 D' 𝒰 g) = d0 D' 𝒱 (resC0 D' τ hτ g) :=
    LinearMap.congr_fun (resC1_comp_d0 D' τ hτ) g
  rw [← hcomm]
  exact hg.res τ hτ

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem C1.MemLD.add {f f' : C1 D' 𝒰} (hf : f.MemLD D) (hf' : f'.MemLD D) :
    (f + f').MemLD D := by
  intro p
  change ((f p : RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X)) +
      (f' p : RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X))) ∈
    RS.LinSysOn D ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X)
  exact Submodule.add_mem _ (hf p) (hf' p)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem C1.MemLD.smul (a : ℂ) {f : C1 D' 𝒰} (hf : f.MemLD D) : (a • f).MemLD D := by
  intro p
  change (a • (f p : RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X))) ∈
    RS.LinSysOn D ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X)
  exact Submodule.smul_mem _ a (hf p)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem memLD_d0_add {g g' : C0 D' 𝒰} (hg : (d0 D' 𝒰 g).MemLD D)
    (hg' : (d0 D' 𝒰 g').MemLD D) : (d0 D' 𝒰 (g + g')).MemLD D := by
  rw [map_add]
  exact hg.add hg'

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem memLD_d0_smul (a : ℂ) {g : C0 D' 𝒰} (hg : (d0 D' 𝒰 g).MemLD D) :
    (d0 D' 𝒰 (a • g)).MemLD D := by
  rw [map_smul]
  exact hg.smul a

/-! ### `mlClass` is refinement-stable (§6.9(a), `mlClass_res`) -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mlClass_res {𝒰 𝒱 : FinCover (⊤ : Opens X)} (τ : Fin 𝒱.n → Fin 𝒰.n)
    (hτ : IsRefIdx 𝒰 𝒱 τ) (g : C0 D' 𝒰) (hg : (d0 D' 𝒰 g).MemLD D)
    (hgr : (d0 D' 𝒱 (resC0 D' τ hτ g)).MemLD D) :
    mlClass 𝒱 (resC0 D' τ hτ g) hgr = mlClass 𝒰 g hg := by
  have hcomm : resC1 D' τ hτ (d0 D' 𝒰 g) = d0 D' 𝒱 (resC0 D' τ hτ g) :=
    LinearMap.congr_fun (resC1_comp_d0 D' τ hτ) g
  have hkey : (⟨C1.retype (d0 D' 𝒱 (resC0 D' τ hτ g)) hgr, C1.retype_mem_Z1 hgr⟩ : Z1 D 𝒱) =
      resZ1 D τ hτ ⟨C1.retype (d0 D' 𝒰 g) hg, C1.retype_mem_Z1 hg⟩ := by
    apply Subtype.ext
    rw [resZ1_apply_coe]
    funext p
    apply Subtype.ext
    rw [C1.retype_apply_coe, ← congrFun hcomm p]
    rfl
  simp only [mlClass]
  rw [hkey, ← resH1_mk, toH1_resH1]

variable [T2Space X] [CompactSpace X]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- On a cover adapted to `diffSupp D D'`, every `Z1 D'`-cocycle already satisfies the `D`-bound
componentwise: diagonal components vanish to order `⊤`, off-diagonal components avoid the finite
set where `D ≠ D'` (adaptedness), hence `D = D'` there and the `D'`-bound *is* the `D`-bound. -/
theorem memLD_of_isAdapted {𝒲 : FinCover (⊤ : Opens X)} (hadapt : 𝒲.IsAdapted (diffSupp D D'))
    {f : C1 D' 𝒲} (hf : f ∈ Z1 D' 𝒲) : f.MemLD D := by
  rintro ⟨i, j⟩
  by_cases hij : i = j
  · subst hij
    rw [RS.mem_linSysOn_iff_of_isOpen (𝒲.U i ⊓ 𝒲.U i).isOpen]
    intro x hx
    rw [Z1.ord_diag D' 𝒲 hf i hx]
    exact le_top
  · rw [RS.mem_linSysOn_iff_of_isOpen (𝒲.U i ⊓ 𝒲.U j).isOpen]
    intro x hx
    have hxDeq : D x = D' x := by
      by_contra hne
      exact hadapt.not_mem_inf (mem_diffSupp_iff.2 hne) hij hx
    have hbound := (RS.mem_linSysOn_iff_of_isOpen (𝒲.U i ⊓ 𝒲.U j).isOpen).1 (f (i, j)).2 x hx
    rwa [hxDeq]

-- **The six-term fragment, part (g)**: `H1Incl` is surjective — no `H²`, no long exact
-- sequence, no snake lemma anywhere. Every class of `H1 D'` is already, on a cover adapted to
-- `diffSupp D D'`, represented by a genuine `Z1 D`-cocycle (retyping across the finite set where
-- `D ≠ D'` costs nothing since cocycles vanish there anyway).
omit [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Pushing a cocycle to a refinement does not change its colimit class. Split out for the same
budget reason as `H1Incl_toH1_retype`. -/
private theorem toH1_mk_resZ1 {𝒰₀ 𝒲 : FinCover (⊤ : Opens X)} (τ : Fin 𝒲.n → Fin 𝒰₀.n)
    (hτ : IsRefIdx 𝒰₀ 𝒲 τ) (f' : Z1 D' 𝒰₀) :
    toH1 D' 𝒲 (H1Cover.mk D' 𝒲 (resZ1 D' τ hτ f')) = toH1 D' 𝒰₀ (H1Cover.mk D' 𝒰₀ f') := by
  rw [← resH1_mk, toH1_resH1 D' τ hτ]

omit [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- `H1Incl` sends the retyped class of a `D`-bounded `D'`-cocycle back to the cocycle's own
class. Split out of `H1Incl_surjective`: these two rewrites go through `H1Cover`'s direct-limit
types and, kept inline, push that proof past the default heartbeat budget. -/
private theorem H1Incl_toH1_retype (h : D ≤ D') {𝒲 : FinCover (⊤ : Opens X)} (g : Z1 D' 𝒲)
    (hmemld : (g : C1 D' 𝒲).MemLD D) :
    H1Incl D h (toH1 D 𝒲 (H1Cover.mk D 𝒲
        ⟨C1.retype (g : C1 D' 𝒲) hmemld, C1.retype_mem_Z1' g.2 hmemld⟩)) =
      toH1 D' 𝒲 (H1Cover.mk D' 𝒲 g) := by
  rw [H1Incl_toH1, h1CoverIncl_mk_retype h g.2 hmemld]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem H1Incl_surjective (h : D ≤ D') : Function.Surjective (H1Incl D h) := by
  intro ξ'
  obtain ⟨𝒰₀, f'c, hf'c⟩ := exists_rep D' ξ'
  obtain ⟨f', hf'⟩ := H1Cover.mk_surjective D' 𝒰₀ f'c
  obtain ⟨𝒲, hle, hadapt, -⟩ := exists_adapted_refinement 𝒰₀ (diffSupp D D')
    (fun _ _ => trivial) (fun _ => ⊤) (fun _ _ => trivial)
  -- opaque refinement index: `toH1_resH1` holds for any of them, and leaving
  -- `chosenRefIdx hle` visible makes `whnf` unfold the choice term on every rewrite below.
  obtain ⟨τ, hτspec⟩ : ∃ τ, IsRefIdx 𝒰₀ 𝒲 τ := ⟨chosenRefIdx hle, chosenRefIdx_spec hle⟩
  obtain ⟨g', hg'_def⟩ : ∃ g', g' = resZ1 D' τ hτspec f' := ⟨_, rfl⟩
  have hgmem : (g' : C1 D' 𝒲) ∈ Z1 D' 𝒲 := g'.2
  have hmemld : (g' : C1 D' 𝒲).MemLD D := memLD_of_isAdapted hadapt hgmem
  refine ⟨toH1 D 𝒲 (H1Cover.mk D 𝒲 ⟨C1.retype (g' : C1 D' 𝒲) hmemld,
    C1.retype_mem_Z1' hgmem hmemld⟩), ?_⟩
  rw [H1Incl_toH1_retype h g' hmemld, hg'_def, toH1_mk_resZ1 τ hτspec f', hf', hf'c]

/-! ### `Realizes` (§6.9(c), D7): the pointwise-`ord` realization predicate -/

/-- `g` realizes the window vector `w` (pointwise-`ord` form, D7): at every `q` of
`diffSupp D D'` and every member containing `q`, the defect of `g`'s component against *any*
representative of `w q` has order `≥ -(D q)` at `q`. (Deviation from the design's `(w q).out`
formulation: quantifying over all representatives is equivalent by
`windowDefect_bound_of_mk_eq`, and strictly easier to consume.) -/
def Realizes (𝒰 : FinCover (⊤ : Opens X)) (g : C0 D' 𝒰) (w : Window D D') : Prop :=
  ∀ (q : diffSupp D D') (ψ : ordGe (q : X) (-(D' (q : X)))),
    WindowAt.mk (q : X) (D (q : X)) (D' (q : X)) ψ = w q →
    ∀ i : Fin 𝒰.n, (q : X) ∈ 𝒰.U i →
      ((-(D (q : X)) : ℤ) : WithTop ℤ) ≤
        (windowDefect (g i : RS.MeroGermOn X (𝒰.U i : Set X))
          (ψ : RS.MeroGermOn X ((chartAt ℂ (q : X)).source))).ord (q : X)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem Realizes.res {𝒰 𝒱 : FinCover (⊤ : Opens X)} {g : C0 D' 𝒰} {w : Window D D'}
    (hr : Realizes 𝒰 g w) (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ) :
    Realizes 𝒱 (resC0 D' τ hτ g) w := by
  intro q ψ hψ k hqk
  have hb := hr q ψ hψ (τ k) (hτ k hqk)
  have hgerm : (resC0 D' τ hτ g k : RS.MeroGermOn X (𝒱.U k : Set X)) =
      RS.MeroGermOn.restrict (hτ k) (g (τ k) : RS.MeroGermOn X (𝒰.U (τ k) : Set X)) := rfl
  rw [hgerm, windowDefect_ord_restrict (hτ k) hqk]
  exact hb

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem Realizes.add {𝒰 : FinCover (⊤ : Opens X)} {g g' : C0 D' 𝒰} {w w' : Window D D'}
    (hr : Realizes 𝒰 g w) (hr' : Realizes 𝒰 g' w') : Realizes 𝒰 (g + g') (w + w') := by
  intro q ψ hψ i hqi
  obtain ⟨ψ₁, hψ₁⟩ := WindowAt.mk_surjective (q : X) (D (q : X)) (D' (q : X)) (w q)
  obtain ⟨ψ₂, hψ₂⟩ := WindowAt.mk_surjective (q : X) (D (q : X)) (D' (q : X)) (w' q)
  have hb₁ := hr q ψ₁ hψ₁ i hqi
  have hb₂ := hr' q ψ₂ hψ₂ i hqi
  have hmk : WindowAt.mk (q : X) (D (q : X)) (D' (q : X)) (ψ₁ + ψ₂) =
      WindowAt.mk (q : X) (D (q : X)) (D' (q : X)) ψ := by
    rw [map_add, hψ₁, hψ₂, hψ, Pi.add_apply]
  refine windowDefect_bound_of_mk_eq hqi hmk ?_
  have hsum : windowDefect ((g + g') i : RS.MeroGermOn X (𝒰.U i : Set X))
      ((ψ₁ + ψ₂ : ordGe (q : X) (-(D' (q : X)))) :
        RS.MeroGermOn X ((chartAt ℂ (q : X)).source)) =
      windowDefect (g i : RS.MeroGermOn X (𝒰.U i : Set X))
        (ψ₁ : RS.MeroGermOn X ((chartAt ℂ (q : X)).source)) +
      windowDefect (g' i : RS.MeroGermOn X (𝒰.U i : Set X))
        (ψ₂ : RS.MeroGermOn X ((chartAt ℂ (q : X)).source)) := by
    change RS.MeroGermOn.restrict Set.inter_subset_left
        ((g i : RS.MeroGermOn X (𝒰.U i : Set X)) + (g' i : RS.MeroGermOn X (𝒰.U i : Set X))) -
      RS.MeroGermOn.restrict Set.inter_subset_right
        ((ψ₁ : RS.MeroGermOn X ((chartAt ℂ (q : X)).source)) +
          (ψ₂ : RS.MeroGermOn X ((chartAt ℂ (q : X)).source))) = _
    rw [map_add, map_add, windowDefect, windowDefect]
    abel
  rw [hsum]
  exact le_trans (le_min hb₁ hb₂) (RS.MeroGermOn.ord_add
    ((𝒰.U i).2.inter (chartAt ℂ (q : X)).open_source) ⟨hqi, mem_chart_source ℂ (q : X)⟩ _ _)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem Realizes.smul {𝒰 : FinCover (⊤ : Opens X)} (a : ℂ) {g : C0 D' 𝒰} {w : Window D D'}
    (hr : Realizes 𝒰 g w) : Realizes 𝒰 (a • g) (a • w) := by
  intro q ψ hψ i hqi
  have hopen : IsOpen ((𝒰.U i : Set X) ∩ (chartAt ℂ (q : X)).source) :=
    (𝒰.U i).2.inter (chartAt ℂ (q : X)).open_source
  have hqmem : (q : X) ∈ (𝒰.U i : Set X) ∩ (chartAt ℂ (q : X)).source :=
    ⟨hqi, mem_chart_source ℂ (q : X)⟩
  rcases eq_or_ne a 0 with rfl | ha
  · have hw0 : WindowAt.mk (q : X) (D (q : X)) (D' (q : X)) ψ = 0 := by
      rw [hψ]
      exact zero_smul ℂ (w q)
    rw [WindowAt.mk_eq_zero_iff] at hw0
    have hg0 : ((0 : ℂ) • g) i = 0 := by rw [Pi.smul_apply, zero_smul]
    have hdz : windowDefect (((0 : ℂ) • g) i : RS.MeroGermOn X (𝒰.U i : Set X))
        (ψ : RS.MeroGermOn X ((chartAt ℂ (q : X)).source)) =
        - RS.MeroGermOn.restrict Set.inter_subset_right
            (ψ : RS.MeroGermOn X ((chartAt ℂ (q : X)).source)) := by
      rw [windowDefect,
        show (((0 : ℂ) • g) i : RS.MeroGermOn X (𝒰.U i : Set X)) = 0 from by rw [hg0]; rfl,
        map_zero, zero_sub]
    rw [hdz, RS.MeroGermOn.ord_neg, RS.MeroGermOn.ord_restrict Set.inter_subset_right hopen
      (chartAt ℂ (q : X)).open_source hqmem]
    exact hw0
  · obtain ⟨ψ₁, hψ₁⟩ := WindowAt.mk_surjective (q : X) (D (q : X)) (D' (q : X)) (w q)
    have hb₁ := hr q ψ₁ hψ₁ i hqi
    have hmk : WindowAt.mk (q : X) (D (q : X)) (D' (q : X)) (a • ψ₁) =
        WindowAt.mk (q : X) (D (q : X)) (D' (q : X)) ψ := by
      rw [map_smul, hψ₁, hψ, Pi.smul_apply]
    refine windowDefect_bound_of_mk_eq hqi hmk ?_
    have hsm : windowDefect ((a • g) i : RS.MeroGermOn X (𝒰.U i : Set X))
        ((a • ψ₁ : ordGe (q : X) (-(D' (q : X)))) :
          RS.MeroGermOn X ((chartAt ℂ (q : X)).source)) =
        a • windowDefect (g i : RS.MeroGermOn X (𝒰.U i : Set X))
          (ψ₁ : RS.MeroGermOn X ((chartAt ℂ (q : X)).source)) := by
      change RS.MeroGermOn.restrict Set.inter_subset_left
          (a • (g i : RS.MeroGermOn X (𝒰.U i : Set X))) -
        RS.MeroGermOn.restrict Set.inter_subset_right
          (a • (ψ₁ : RS.MeroGermOn X ((chartAt ℂ (q : X)).source))) = _
      rw [map_smul, map_smul, windowDefect, smul_sub]
    rw [hsm, RS.MeroGermOn.ord_smul hopen hqmem ha]
    exact hb₁

/-! ### Lemma A (§6.9(d)): independence of the realization -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- **Lemma A (§6.9(d))**: any two Mittag-Leffler realizations of the same window vector give
the same `H¹(D)`-class. No adaptedness is needed: at `diffSupp`-points the two `Realizes`
bounds control the difference, everywhere else `D = D'` and the `D'`-bounds do. -/
theorem mlClass_eq_of_realizes {𝒰 𝒰' : FinCover (⊤ : Opens X)} {g : C0 D' 𝒰} {g' : C0 D' 𝒰'}
    (hg : (d0 D' 𝒰 g).MemLD D) (hg' : (d0 D' 𝒰' g').MemLD D) {w : Window D D'}
    (hr : Realizes 𝒰 g w) (hr' : Realizes 𝒰' g' w) :
    mlClass 𝒰 g hg = mlClass 𝒰' g' hg' := by
  obtain ⟨τ, hτ⟩ := le_meet_left 𝒰 𝒰'
  obtain ⟨τ', hτ'⟩ := le_meet_right 𝒰 𝒰'
  have hG : (d0 D' (𝒰.meet 𝒰') (resC0 D' τ hτ g)).MemLD D := memLD_d0_res hg τ hτ
  have hG' : (d0 D' (𝒰.meet 𝒰') (resC0 D' τ' hτ' g')).MemLD D := memLD_d0_res hg' τ' hτ'
  have hrG : Realizes (𝒰.meet 𝒰') (resC0 D' τ hτ g) w := hr.res τ hτ
  have hrG' : Realizes (𝒰.meet 𝒰') (resC0 D' τ' hτ' g') w := hr'.res τ' hτ'
  rw [← mlClass_res τ hτ g hg hG, ← mlClass_res τ' hτ' g' hg' hG']
  set G := resC0 D' τ hτ g with hGdef
  set G' := resC0 D' τ' hτ' g' with hG'def
  -- the connecting `D`-cochain: `G - G'` is componentwise `D`-bounded
  have hmemk : ∀ k : Fin (𝒰.meet 𝒰').n,
      ((G k : RS.MeroGermOn X ((𝒰.meet 𝒰').U k : Set X)) -
        (G' k : RS.MeroGermOn X ((𝒰.meet 𝒰').U k : Set X))) ∈
      RS.LinSysOn D (((𝒰.meet 𝒰').U k : Opens X) : Set X) := by
    intro k
    rw [RS.mem_linSysOn_iff_of_isOpen ((𝒰.meet 𝒰').U k).isOpen]
    intro x hx
    by_cases hxS : x ∈ diffSupp D D'
    · obtain ⟨ψ, hψ⟩ := WindowAt.mk_surjective x (D x) (D' x) (w ⟨x, hxS⟩)
      have hb := hrG ⟨x, hxS⟩ ψ hψ k hx
      have hb' := hrG' ⟨x, hxS⟩ ψ hψ k hx
      have hopen : IsOpen (((𝒰.meet 𝒰').U k : Set X) ∩ (chartAt ℂ x).source) :=
        ((𝒰.meet 𝒰').U k).2.inter (chartAt ℂ x).open_source
      have hxmem : x ∈ ((𝒰.meet 𝒰').U k : Set X) ∩ (chartAt ℂ x).source :=
        ⟨hx, mem_chart_source ℂ x⟩
      have hdiff : windowDefect (G k : RS.MeroGermOn X ((𝒰.meet 𝒰').U k : Set X))
            (ψ : RS.MeroGermOn X ((chartAt ℂ x).source)) -
          windowDefect (G' k : RS.MeroGermOn X ((𝒰.meet 𝒰').U k : Set X))
            (ψ : RS.MeroGermOn X ((chartAt ℂ x).source)) =
          RS.MeroGermOn.restrict Set.inter_subset_left
            ((G k : RS.MeroGermOn X ((𝒰.meet 𝒰').U k : Set X)) -
              (G' k : RS.MeroGermOn X ((𝒰.meet 𝒰').U k : Set X))) := by
        rw [windowDefect, windowDefect, map_sub]
        abel
      have hbound := le_ord_sub hopen hxmem hb hb'
      rw [hdiff] at hbound
      rwa [RS.MeroGermOn.ord_restrict Set.inter_subset_left hopen ((𝒰.meet 𝒰').U k).2 hxmem]
        at hbound
    · have hDx : D x = D' x := by
        by_contra hne
        exact hxS (mem_diffSupp_iff.2 hne)
      have hmem' := Submodule.sub_mem (RS.LinSysOn D' (((𝒰.meet 𝒰').U k : Opens X) : Set X))
        (G k).2 (G' k).2
      have hb := (RS.mem_linSysOn_iff_of_isOpen ((𝒰.meet 𝒰').U k).isOpen).1 hmem' x hx
      rw [hDx]
      exact hb
  set hcw : C0 D (𝒰.meet 𝒰') := fun k =>
    ⟨(G k : RS.MeroGermOn X ((𝒰.meet 𝒰').U k : Set X)) -
      (G' k : RS.MeroGermOn X ((𝒰.meet 𝒰').U k : Set X)), hmemk k⟩ with hcwdef
  have hz : H1Cover.mk D (𝒰.meet 𝒰') ⟨C1.retype (d0 D' (𝒰.meet 𝒰') G) hG,
        C1.retype_mem_Z1 hG⟩ =
      H1Cover.mk D (𝒰.meet 𝒰') ⟨C1.retype (d0 D' (𝒰.meet 𝒰') G') hG',
        C1.retype_mem_Z1 hG'⟩ := by
    rw [← sub_eq_zero, ← map_sub, H1Cover.mk_eq_zero_iff]
    refine ⟨hcw, ?_⟩
    funext p
    apply Subtype.ext
    change RS.MeroGermOn.restrict inf_le_right
          ((G p.2 : RS.MeroGermOn X ((𝒰.meet 𝒰').U p.2 : Set X)) -
            (G' p.2 : RS.MeroGermOn X ((𝒰.meet 𝒰').U p.2 : Set X))) -
        RS.MeroGermOn.restrict inf_le_left
          ((G p.1 : RS.MeroGermOn X ((𝒰.meet 𝒰').U p.1 : Set X)) -
            (G' p.1 : RS.MeroGermOn X ((𝒰.meet 𝒰').U p.1 : Set X))) =
      (RS.MeroGermOn.restrict inf_le_right
          (G p.2 : RS.MeroGermOn X ((𝒰.meet 𝒰').U p.2 : Set X)) -
        RS.MeroGermOn.restrict inf_le_left
          (G p.1 : RS.MeroGermOn X ((𝒰.meet 𝒰').U p.1 : Set X))) -
      (RS.MeroGermOn.restrict inf_le_right
          (G' p.2 : RS.MeroGermOn X ((𝒰.meet 𝒰').U p.2 : Set X)) -
        RS.MeroGermOn.restrict inf_le_left
          (G' p.1 : RS.MeroGermOn X ((𝒰.meet 𝒰').U p.1 : Set X)))
    rw [map_sub, map_sub]
    abel
  rw [mlClass, mlClass, hz]

/-! ### `exists_realization` (§6.9(c)) -/

/-- **Adapted-cover realization (§6.9(c))**: every window vector is realized by a
Mittag-Leffler `0`-cochain on a cover adapted to `diffSupp D D'` — on the (unique) member
through `q`, the restriction of a chart-source representative of `w q`, shrunk into a pole-free
zone avoiding all other points of `diffSupp D D' ∪ supp D ∪ supp D'`; `0` elsewhere. -/
theorem exists_realization (_h : D ≤ D') (w : Window D D') :
    ∃ (𝒰 : FinCover (⊤ : Opens X)) (g : C0 D' 𝒰) (_hg : (d0 D' 𝒰 g).MemLD D),
      Realizes 𝒰 g w ∧ 𝒰.IsAdapted (diffSupp D D') := by
  classical
  set S' : Finset X := diffSupp D D' ∪ (D.finiteSupport isCompact_univ).toFinset ∪
    ((D').finiteSupport isCompact_univ).toFinset with hS'def
  have hSS' : diffSupp D D' ⊆ S' := fun x hx =>
    Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hD'0 : ∀ x, x ∉ S' → D' x = 0 := by
    intro x hx
    by_contra hne
    apply hx
    refine Finset.mem_union_right _ ?_
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    exact hne
  -- chart-source representatives of the window components
  have hrep : ∀ q : diffSupp D D', ∃ ψ : ordGe (q : X) (-(D' (q : X))),
      WindowAt.mk (q : X) (D (q : X)) (D' (q : X)) ψ = w q := fun q =>
    WindowAt.mk_surjective (q : X) (D (q : X)) (D' (q : X)) (w q)
  choose ψ hψ using hrep
  -- pole-free zones
  have hzone : ∀ q : diffSupp D D', ∃ N : Opens X, (q : X) ∈ N ∧
      (N : Set X) ⊆ (chartAt ℂ (q : X)).source ∧ ∀ x ∈ (N : Set X), x ≠ (q : X) →
        0 ≤ (ψ q : RS.MeroGermOn X ((chartAt ℂ (q : X)).source)).ord x := fun q =>
    exists_pole_free_zone (chartAt ℂ (q : X)).open_source (mem_chart_source ℂ (q : X)) _
  choose N hqN hNsub hNord using hzone
  -- prescribed neighbourhoods: zone ⊓ complement of the other special points
  set O : X → Opens X := fun x =>
    if hx : x ∈ diffSupp D D' then N ⟨x, hx⟩ ⊓ compOpens (S'.erase x) else ⊤ with hOdef
  have hOc : ∀ q : diffSupp D D', O (q : X) = N q ⊓ compOpens (S'.erase (q : X)) := by
    intro q
    simp only [hOdef]
    rw [dif_pos q.2, Subtype.coe_eta]
  have hO : ∀ p ∈ diffSupp D D', p ∈ O p := by
    intro p hp
    rw [show O p = N ⟨p, hp⟩ ⊓ compOpens (S'.erase p) from hOc ⟨p, hp⟩]
    exact ⟨hqN ⟨p, hp⟩, mem_compOpens.2 (Finset.notMem_erase p S')⟩
  obtain ⟨𝒱, hle, hadapt, hOcl⟩ := exists_adapted_refinement (FinCover.single (⊤ : Opens X))
    (diffSupp D D') (fun _ _ => trivial) O hO
  -- members through `q` sit inside the zone of `q` and meet `S'` only in `q`
  have hmem_zone : ∀ (q : diffSupp D D') (k : Fin 𝒱.n), (q : X) ∈ 𝒱.U k →
      𝒱.U k ≤ N q ∧ ∀ x ∈ (𝒱.U k : Set X), x ≠ (q : X) → x ∉ S' := by
    intro q k hqk
    have hsub := hOcl (q : X) q.2 k hqk
    rw [hOc q] at hsub
    refine ⟨le_trans hsub inf_le_left, fun x hx hxq => ?_⟩
    have hxc : x ∈ compOpens (S'.erase (q : X)) := (le_trans hsub inf_le_right) hx
    rw [mem_compOpens] at hxc
    intro hxS'
    exact hxc (Finset.mem_erase_of_ne_of_mem hxq hxS')
  have hsubk : ∀ (k : Fin 𝒱.n) (q : diffSupp D D'), (q : X) ∈ 𝒱.U k →
      (𝒱.U k : Set X) ⊆ (chartAt ℂ (q : X)).source := fun k q hqk x hx =>
    hNsub q ((hmem_zone q k hqk).1 hx)
  -- the realizing cochain
  have hmemg : ∀ (k : Fin 𝒱.n) (hk : ∃ q : diffSupp D D', (q : X) ∈ 𝒱.U k),
      RS.MeroGermOn.restrict (hsubk k hk.choose hk.choose_spec)
        (ψ hk.choose : RS.MeroGermOn X ((chartAt ℂ (hk.choose : X)).source)) ∈
      RS.LinSysOn D' (𝒱.U k : Set X) := by
    intro k hk
    rw [RS.mem_linSysOn_iff_of_isOpen (𝒱.U k).isOpen]
    intro x hx
    rw [RS.MeroGermOn.ord_restrict (hsubk k hk.choose hk.choose_spec) (𝒱.U k).2
      (chartAt ℂ (hk.choose : X)).open_source hx]
    rcases eq_or_ne x (hk.choose : X) with rfl | hne
    · exact mem_ordGe_iff.1 (ψ hk.choose).2
    · have h0 : 0 ≤
          (ψ hk.choose : RS.MeroGermOn X ((chartAt ℂ (hk.choose : X)).source)).ord x :=
        hNord hk.choose x ((hmem_zone hk.choose k hk.choose_spec).1 hx) hne
      have hxS' : x ∉ S' := (hmem_zone hk.choose k hk.choose_spec).2 x hx hne
      rw [hD'0 x hxS']
      simpa using h0
  set g : C0 D' 𝒱 := fun k =>
    if hk : ∃ q : diffSupp D D', (q : X) ∈ 𝒱.U k then
      ⟨RS.MeroGermOn.restrict (hsubk k hk.choose hk.choose_spec)
        (ψ hk.choose : RS.MeroGermOn X ((chartAt ℂ (hk.choose : X)).source)), hmemg k hk⟩
    else 0 with hgdef
  -- on any member through `q`, `g` restricts the representative of `w q`
  have hval : ∀ (i : Fin 𝒱.n) (q : diffSupp D D') (hqi : (q : X) ∈ 𝒱.U i),
      (g i : RS.MeroGermOn X (𝒱.U i : Set X)) =
        RS.MeroGermOn.restrict (hsubk i q hqi)
          (ψ q : RS.MeroGermOn X ((chartAt ℂ (q : X)).source)) := by
    intro i q hqi
    have hk : ∃ q' : diffSupp D D', (q' : X) ∈ 𝒱.U i := ⟨q, hqi⟩
    have hgen : ∀ (c : diffSupp D D') (hc : (c : X) ∈ 𝒱.U i), c = q →
        RS.MeroGermOn.restrict (hsubk i c hc)
          (ψ c : RS.MeroGermOn X ((chartAt ℂ (c : X)).source)) =
        RS.MeroGermOn.restrict (hsubk i q hqi)
          (ψ q : RS.MeroGermOn X ((chartAt ℂ (q : X)).source)) := by
      rintro c hc rfl
      rfl
    have hchoice : hk.choose = q := by
      apply Subtype.ext
      by_contra hne
      have hqO : (q : X) ∈ O (hk.choose : X) :=
        hOcl (hk.choose : X) hk.choose.2 i hk.choose_spec hqi
      rw [hOc hk.choose] at hqO
      have hqc : (q : X) ∈ compOpens (S'.erase (hk.choose : X)) := hqO.2
      rw [mem_compOpens] at hqc
      exact hqc (Finset.mem_erase_of_ne_of_mem (fun heq => hne heq.symm) (hSS' q.2))
    have hgi : g i = ⟨RS.MeroGermOn.restrict (hsubk i hk.choose hk.choose_spec)
        (ψ hk.choose : RS.MeroGermOn X ((chartAt ℂ (hk.choose : X)).source)),
        hmemg i hk⟩ := by
      simp only [hgdef]
      rw [dif_pos hk]
    rw [hgi]
    exact hgen hk.choose hk.choose_spec hchoice
  refine ⟨𝒱, g, memLD_of_isAdapted hadapt (B1_le_Z1 D' 𝒱 ⟨g, rfl⟩), ?_, hadapt⟩
  intro q ψ' hψ' i hqi
  have hdz : windowDefect (g i : RS.MeroGermOn X (𝒱.U i : Set X))
      (ψ q : RS.MeroGermOn X ((chartAt ℂ (q : X)).source)) = 0 := by
    rw [windowDefect, hval i q hqi, RS.MeroGermOn.restrict_restrict]
    exact sub_self _
  have hb0 : ((-(D (q : X)) : ℤ) : WithTop ℤ) ≤
      (windowDefect (g i : RS.MeroGermOn X (𝒱.U i : Set X))
        (ψ q : RS.MeroGermOn X ((chartAt ℂ (q : X)).source))).ord (q : X) := by
    rw [hdz, RS.MeroGermOn.ord_zero,
      if_pos ⟨(𝒱.U i).2.inter (chartAt ℂ (q : X)).open_source, hqi,
        mem_chart_source ℂ (q : X)⟩]
    exact le_top
  exact windowDefect_bound_of_mk_eq hqi ((hψ q).trans hψ'.symm) hb0

/-! ### The connecting map `windowConnect` (§6.9(d)) -/

private noncomputable def windowConnectRaw (h : D ≤ D') (w : Window D D') : H1 D :=
  mlClass (exists_realization h w).choose (exists_realization h w).choose_spec.choose
    (exists_realization h w).choose_spec.choose_spec.choose

private theorem windowConnectRaw_eq (h : D ≤ D') (w : Window D D')
    {𝒰 : FinCover (⊤ : Opens X)} {g : C0 D' 𝒰} (hg : (d0 D' 𝒰 g).MemLD D)
    (hr : Realizes 𝒰 g w) : windowConnectRaw h w = mlClass 𝒰 g hg :=
  mlClass_eq_of_realizes (exists_realization h w).choose_spec.choose_spec.choose hg
    (exists_realization h w).choose_spec.choose_spec.choose_spec.1 hr

/-- **The connecting map `δ` of the six-term skyscraper fragment (§6.9(d))**: realize the
window vector on an adapted cover (`exists_realization`), take the Mittag-Leffler class
(`mlClass`); well-defined by Lemma A (`mlClass_eq_of_realizes`), which also gives linearity. -/
noncomputable def windowConnect (h : D ≤ D') : Window D D' →ₗ[ℂ] H1 D where
  toFun := windowConnectRaw h
  map_add' w w' := by
    obtain ⟨𝒰₁, g₁, hg₁, hr₁, -⟩ := exists_realization h w
    obtain ⟨𝒰₂, g₂, hg₂, hr₂, -⟩ := exists_realization h w'
    obtain ⟨τ₁, hτ₁⟩ := le_meet_left 𝒰₁ 𝒰₂
    obtain ⟨τ₂, hτ₂⟩ := le_meet_right 𝒰₁ 𝒰₂
    have hG₁ : (d0 D' (𝒰₁.meet 𝒰₂) (resC0 D' τ₁ hτ₁ g₁)).MemLD D := memLD_d0_res hg₁ τ₁ hτ₁
    have hG₂ : (d0 D' (𝒰₁.meet 𝒰₂) (resC0 D' τ₂ hτ₂ g₂)).MemLD D := memLD_d0_res hg₂ τ₂ hτ₂
    have hG₁₂ : (d0 D' (𝒰₁.meet 𝒰₂) (resC0 D' τ₁ hτ₁ g₁ + resC0 D' τ₂ hτ₂ g₂)).MemLD D :=
      memLD_d0_add hG₁ hG₂
    rw [windowConnectRaw_eq h (w + w') hG₁₂ ((hr₁.res τ₁ hτ₁).add (hr₂.res τ₂ hτ₂)),
      windowConnectRaw_eq h w hG₁ (hr₁.res τ₁ hτ₁),
      windowConnectRaw_eq h w' hG₂ (hr₂.res τ₂ hτ₂)]
    exact mlClass_add _ _ hG₁ hG₂ hG₁₂
  map_smul' a w := by
    obtain ⟨𝒰₁, g₁, hg₁, hr₁, -⟩ := exists_realization h w
    have hga : (d0 D' 𝒰₁ (a • g₁)).MemLD D := memLD_d0_smul a hg₁
    simp only [RingHom.id_apply]
    rw [windowConnectRaw_eq h (a • w) hga (hr₁.smul a), windowConnectRaw_eq h w hg₁ hr₁]
    exact mlClass_smul a g₁ hg₁ hga

/-- `windowConnect` agrees with the Mittag-Leffler class of *any* realization (the working
form of the connecting map — this is what consumers should use). -/
theorem windowConnect_spec (h : D ≤ D') (w : Window D D') {𝒰 : FinCover (⊤ : Opens X)}
    {g : C0 D' 𝒰} (hg : (d0 D' 𝒰 g).MemLD D) (hr : Realizes 𝒰 g w) :
    windowConnect h w = mlClass 𝒰 g hg :=
  windowConnectRaw_eq h w hg hr

theorem H1Incl_windowConnect (h : D ≤ D') (w : Window D D') :
    H1Incl D h (windowConnect h w) = 0 := by
  obtain ⟨𝒰, g, hg, hr, -⟩ := exists_realization h w
  rw [windowConnect_spec h w hg hr]
  exact H1Incl_mlClass h g hg

/-! ### Exactness (§6.9(e)/(f)) -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] [CompactSpace X] in
/-- The `mlClass_eq_zero_iff`-side `ord` bound and the `windowDefect`-side bound agree (both
compute the same germ's order on `𝒰.U i ∩ chart source`). -/
private theorem ord_sub_global_eq_defect {𝒰 : FinCover (⊤ : Opens X)} {i : Fin 𝒰.n} {q : X}
    (hqi : q ∈ 𝒰.U i) (γ : RS.MeroGermOn X (𝒰.U i : Set X)) (φ : RS.LinSys D') :
    ((γ - RS.MeroGermOn.restrict (𝒰.le_base i)
        (φ : RS.MeroGermOn X (Set.univ : Set X))).ord q) =
      (windowDefect γ (restrictToChart D' q φ :
        RS.MeroGermOn X ((chartAt ℂ q).source))).ord q := by
  have hopen : IsOpen ((𝒰.U i : Set X) ∩ (chartAt ℂ q).source) :=
    (𝒰.U i).2.inter (chartAt ℂ q).open_source
  have hqmem : q ∈ (𝒰.U i : Set X) ∩ (chartAt ℂ q).source := ⟨hqi, mem_chart_source ℂ q⟩
  have hgerm : windowDefect γ (restrictToChart D' q φ :
      RS.MeroGermOn X ((chartAt ℂ q).source)) =
      RS.MeroGermOn.restrict Set.inter_subset_left
        (γ - RS.MeroGermOn.restrict (𝒰.le_base i)
          (φ : RS.MeroGermOn X (Set.univ : Set X))) := by
    rw [windowDefect, restrictToChart_apply_coe, map_sub, RS.MeroGermOn.restrict_restrict]
    congr 1
    exact (RS.MeroGermOn.restrict_restrict _ _ (φ : RS.MeroGermOn X (Set.univ : Set X))).symm
  rw [hgerm, RS.MeroGermOn.ord_restrict Set.inter_subset_left hopen (𝒰.U i).2 hqmem]

/-- **Exactness at `Window D D'` (§6.9(e))**: `windowConnect h w = 0` iff `w` is the window
vector of a global section of `L(D')`. -/
theorem exact_windowMap_windowConnect (h : D ≤ D') :
    Function.Exact (windowMap h) (windowConnect h) := by
  intro w
  constructor
  · intro hz
    obtain ⟨𝒰, g, hg, hr, -⟩ := exists_realization h w
    rw [windowConnect_spec h w hg hr] at hz
    obtain ⟨φ, hφ⟩ := (mlClass_eq_zero_iff h g hg).1 hz
    refine ⟨φ, ?_⟩
    funext q
    obtain ⟨i, hqi⟩ := 𝒰.covers (q : X) trivial
    obtain ⟨ψ, hψ⟩ := WindowAt.mk_surjective (q : X) (D (q : X)) (D' (q : X)) (w q)
    have hb := hr q ψ hψ i hqi
    have hbφ : ((-(D (q : X)) : ℤ) : WithTop ℤ) ≤
        (windowDefect (g i : RS.MeroGermOn X (𝒰.U i : Set X))
          (restrictToChart D' (q : X) φ :
            RS.MeroGermOn X ((chartAt ℂ (q : X)).source))).ord (q : X) := by
      rw [← ord_sub_global_eq_defect hqi]
      exact hφ i (q : X) hqi
    have hopen : IsOpen ((𝒰.U i : Set X) ∩ (chartAt ℂ (q : X)).source) :=
      (𝒰.U i).2.inter (chartAt ℂ (q : X)).open_source
    have hqmem : (q : X) ∈ (𝒰.U i : Set X) ∩ (chartAt ℂ (q : X)).source :=
      ⟨hqi, mem_chart_source ℂ (q : X)⟩
    have hsub := le_ord_sub hopen hqmem hbφ hb
    have hdd : windowDefect (g i : RS.MeroGermOn X (𝒰.U i : Set X))
          (restrictToChart D' (q : X) φ :
            RS.MeroGermOn X ((chartAt ℂ (q : X)).source)) -
        windowDefect (g i : RS.MeroGermOn X (𝒰.U i : Set X))
          (ψ : RS.MeroGermOn X ((chartAt ℂ (q : X)).source)) =
        RS.MeroGermOn.restrict Set.inter_subset_right
          ((ψ : RS.MeroGermOn X ((chartAt ℂ (q : X)).source)) -
            (restrictToChart D' (q : X) φ :
              RS.MeroGermOn X ((chartAt ℂ (q : X)).source))) := by
      rw [windowDefect, windowDefect, map_sub]
      abel
    rw [hdd, RS.MeroGermOn.ord_restrict Set.inter_subset_right hopen
      (chartAt ℂ (q : X)).open_source hqmem] at hsub
    rw [windowMap_apply, ← hψ]
    have hmz : WindowAt.mk (q : X) (D (q : X)) (D' (q : X))
        (restrictToChart D' (q : X) φ - ψ) = 0 := by
      rw [WindowAt.mk_eq_zero_iff]
      have hco : ((restrictToChart D' (q : X) φ - ψ : ordGe (q : X) (-(D' (q : X)))) :
          RS.MeroGermOn X ((chartAt ℂ (q : X)).source)) =
          -((ψ : RS.MeroGermOn X ((chartAt ℂ (q : X)).source)) -
            (restrictToChart D' (q : X) φ :
              RS.MeroGermOn X ((chartAt ℂ (q : X)).source))) := by
        rw [neg_sub]
        rfl
      rw [hco, RS.MeroGermOn.ord_neg]
      exact hsub
    rw [map_sub, sub_eq_zero] at hmz
    exact hmz
  · rintro ⟨φ, rfl⟩
    obtain ⟨𝒰, g, hg, hr, -⟩ := exists_realization h (windowMap h φ)
    rw [windowConnect_spec h (windowMap h φ) hg hr]
    apply mlClass_eq_zero_of_exists g hg φ
    intro i x hx
    by_cases hxS : x ∈ diffSupp D D'
    · have hb := hr ⟨x, hxS⟩ (restrictToChart D' x φ) (windowMap_apply h φ ⟨x, hxS⟩).symm i hx
      rw [ord_sub_global_eq_defect hx]
      exact hb
    · have hDx : D x = D' x := by
        by_contra hne
        exact hxS (mem_diffSupp_iff.2 hne)
      have hφmem0 : (φ : RS.MeroGermOn X (Set.univ : Set X)) ∈
          RS.LinSysOn D' (Set.univ : Set X) := by
        rw [RS.mem_linSysOn_iff_of_isOpen isOpen_univ]
        intro y _
        exact RS.mem_linSys_iff.1 φ.2 y
      have hmem' := Submodule.sub_mem (RS.LinSysOn D' (𝒰.U i : Set X)) (g i).2
        (RS.restrict_mem_linSysOn (𝒰.le_base i) (𝒰.U i).2 isOpen_univ hφmem0)
      have hb := (RS.mem_linSysOn_iff_of_isOpen (𝒰.U i).2).1 hmem' x hx
      rw [hDx]
      exact hb

/-- **Exactness at `H¹(D)` (§6.9(f))**: the kernel of `H1Incl` is exactly the image of the
connecting map — `toH1_injective` (Forster 12.4) turns the vanishing into a `D'`-coboundary
witness on the representing cover itself, and `exists_tail_approx` reads off its window
vector. -/
theorem exact_windowConnect_H1Incl (h : D ≤ D') :
    Function.Exact (windowConnect h) (H1Incl D h) := by
  intro ξ
  constructor
  · intro hξ
    obtain ⟨𝒱, c, hc⟩ := exists_rep D ξ
    obtain ⟨f, rfl⟩ := H1Cover.mk_surjective D 𝒱 c
    have hincl0 : h1CoverIncl D 𝒱 h (H1Cover.mk D 𝒱 f) = 0 := by
      apply toH1_injective D' 𝒱
      rw [map_zero, ← H1Incl_toH1, hc, hξ]
    rw [h1CoverIncl_mk, H1Cover.mk_eq_zero_iff] at hincl0
    obtain ⟨g', hg'd0⟩ := hincl0
    have hg'd0' : d0 D' 𝒱 g' = inclC1 D 𝒱 h (f : C1 D 𝒱) := by
      rw [hg'd0, LinearMap.coe_restrict_apply]
    have hmemld : (d0 D' 𝒱 g').MemLD D := by
      intro p
      rw [hg'd0']
      change (Submodule.inclusion (RS.Cech.linSysOn_mono h) ((f : C1 D 𝒱) p) :
        RS.MeroGermOn X ((𝒱.U p.1 ⊓ 𝒱.U p.2 : Opens X) : Set X)) ∈
        RS.LinSysOn D ((𝒱.U p.1 ⊓ 𝒱.U p.2 : Opens X) : Set X)
      rw [Submodule.coe_inclusion]
      exact ((f : C1 D 𝒱) p).2
    -- read off the window vector of `g'` via tail approximation
    have hbase : ∀ q : diffSupp D D', ∃ (i : Fin 𝒱.n) (_ : (q : X) ∈ 𝒱.U i)
        (ψ : ordGe (q : X) (-(D' (q : X)))),
        ((-(D (q : X)) : ℤ) : WithTop ℤ) ≤
          (windowDefect (g' i : RS.MeroGermOn X (𝒱.U i : Set X))
            (ψ : RS.MeroGermOn X ((chartAt ℂ (q : X)).source))).ord (q : X) := by
      intro q
      obtain ⟨i, hi⟩ := 𝒱.covers (q : X) trivial
      have hopen : IsOpen ((𝒱.U i : Set X) ∩ (chartAt ℂ (q : X)).source) :=
        (𝒱.U i).2.inter (chartAt ℂ (q : X)).open_source
      have hqmem : (q : X) ∈ (𝒱.U i : Set X) ∩ (chartAt ℂ (q : X)).source :=
        ⟨hi, mem_chart_source ℂ (q : X)⟩
      have hIL : (𝒱.U i : Set X) ∩ (chartAt ℂ (q : X)).source ⊆ (𝒱.U i : Set X) :=
        Set.inter_subset_left
      have hγord : ((-(D' (q : X)) : ℤ) : WithTop ℤ) ≤
          (RS.MeroGermOn.restrict hIL
            (g' i : RS.MeroGermOn X (𝒱.U i : Set X))).ord (q : X) := by
        rw [RS.MeroGermOn.ord_restrict hIL hopen (𝒱.U i).2 hqmem]
        exact (RS.mem_linSysOn_iff_of_isOpen (𝒱.U i).2).1 (g' i).2 (q : X) hi
      obtain ⟨ψ, hψb⟩ := exists_tail_approx (q : X) hopen Set.inter_subset_right hqmem
        (Function.locallyFinsuppWithin.le_def.1 h (q : X))
        (RS.MeroGermOn.restrict hIL
          (g' i : RS.MeroGermOn X (𝒱.U i : Set X))) hγord
      exact ⟨i, hi, ψ, hψb⟩
    choose i hi ψ hψb using hbase
    obtain ⟨w, hwdef⟩ : ∃ w : Window D D',
        w = fun q : ↥(diffSupp D D') =>
          WindowAt.mk (q : X) (D (q : X)) (D' (q : X)) (ψ q) := ⟨_, rfl⟩
    have hreal : Realizes 𝒱 g' w := by
      intro q ψ' hψ' j hqj
      have hstep : ((-(D (q : X)) : ℤ) : WithTop ℤ) ≤
          (windowDefect (g' j : RS.MeroGermOn X (𝒱.U j : Set X))
            (ψ q : RS.MeroGermOn X ((chartAt ℂ (q : X)).source))).ord (q : X) := by
        have hTopen : IsOpen ((((𝒱.U (i q) ⊓ 𝒱.U j : Opens X) : Set X)) ∩
            (chartAt ℂ (q : X)).source) :=
          (𝒱.U (i q) ⊓ 𝒱.U j).isOpen.inter (chartAt ℂ (q : X)).open_source
        have hqT : (q : X) ∈ (((𝒱.U (i q) ⊓ 𝒱.U j : Opens X) : Set X)) ∩
            (chartAt ℂ (q : X)).source := ⟨⟨hi q, hqj⟩, mem_chart_source ℂ (q : X)⟩
        have hTj : (((𝒱.U (i q) ⊓ 𝒱.U j : Opens X) : Set X)) ∩
            (chartAt ℂ (q : X)).source ⊆ (𝒱.U j : Set X) := fun x hx => hx.1.2
        have hTiq : (((𝒱.U (i q) ⊓ 𝒱.U j : Opens X) : Set X)) ∩
            (chartAt ℂ (q : X)).source ⊆ (𝒱.U (i q) : Set X) := fun x hx => hx.1.1
        have hTs : (((𝒱.U (i q) ⊓ 𝒱.U j : Opens X) : Set X)) ∩
            (chartAt ℂ (q : X)).source ⊆ (chartAt ℂ (q : X)).source :=
          Set.inter_subset_right
        have hTinf : (((𝒱.U (i q) ⊓ 𝒱.U j : Opens X) : Set X)) ∩
            (chartAt ℂ (q : X)).source ⊆ ((𝒱.U (i q) ⊓ 𝒱.U j : Opens X) : Set X) :=
          Set.inter_subset_left
        rw [windowDefect_ord_congr hTopen hTj hTs hqT]
        have hdec : RS.MeroGermOn.restrict hTj (g' j : RS.MeroGermOn X (𝒱.U j : Set X)) -
            RS.MeroGermOn.restrict hTs
              (ψ q : RS.MeroGermOn X ((chartAt ℂ (q : X)).source)) =
            (RS.MeroGermOn.restrict hTj (g' j : RS.MeroGermOn X (𝒱.U j : Set X)) -
              RS.MeroGermOn.restrict hTiq
                (g' (i q) : RS.MeroGermOn X (𝒱.U (i q) : Set X))) +
            (RS.MeroGermOn.restrict hTiq
                (g' (i q) : RS.MeroGermOn X (𝒱.U (i q) : Set X)) -
              RS.MeroGermOn.restrict hTs
                (ψ q : RS.MeroGermOn X ((chartAt ℂ (q : X)).source))) := by
          abel
        rw [hdec]
        refine le_trans (le_min ?_ ?_) (RS.MeroGermOn.ord_add hTopen hqT _ _)
        · have hd0mem := hmemld (i q, j)
          have hb0 := (RS.mem_linSysOn_iff_of_isOpen (𝒱.U (i q) ⊓ 𝒱.U j).isOpen).1 hd0mem
            (q : X) ⟨hi q, hqj⟩
          have hres : RS.MeroGermOn.restrict hTinf
              (d0 D' 𝒱 g' (i q, j) :
                RS.MeroGermOn X ((𝒱.U (i q) ⊓ 𝒱.U j : Opens X) : Set X)) =
              RS.MeroGermOn.restrict hTj (g' j : RS.MeroGermOn X (𝒱.U j : Set X)) -
                RS.MeroGermOn.restrict hTiq
                  (g' (i q) : RS.MeroGermOn X (𝒱.U (i q) : Set X)) := by
            change RS.MeroGermOn.restrict hTinf
                (RS.MeroGermOn.restrict inf_le_right
                    (g' j : RS.MeroGermOn X (𝒱.U j : Set X)) -
                  RS.MeroGermOn.restrict inf_le_left
                    (g' (i q) : RS.MeroGermOn X (𝒱.U (i q) : Set X))) = _
            rw [map_sub, RS.MeroGermOn.restrict_restrict, RS.MeroGermOn.restrict_restrict]
          rw [← hres, RS.MeroGermOn.ord_restrict hTinf hTopen
            (𝒱.U (i q) ⊓ 𝒱.U j).isOpen hqT]
          exact hb0
        · rw [← windowDefect_ord_congr hTopen hTiq hTs hqT]
          exact hψb q
      have hmkq : WindowAt.mk (q : X) (D (q : X)) (D' (q : X)) (ψ q) = w q := by
        rw [hwdef]
      exact windowDefect_bound_of_mk_eq hqj (hmkq.trans hψ'.symm) hstep
    refine ⟨w, ?_⟩
    rw [windowConnect_spec h w hmemld hreal]
    have hfz : (⟨C1.retype (d0 D' 𝒱 g') hmemld, C1.retype_mem_Z1 hmemld⟩ : Z1 D 𝒱) = f := by
      apply Subtype.ext
      funext p
      apply Subtype.ext
      rw [C1.retype_apply_coe, hg'd0']
      change (Submodule.inclusion (RS.Cech.linSysOn_mono h) ((f : C1 D 𝒱) p) :
        RS.MeroGermOn X ((𝒱.U p.1 ⊓ 𝒱.U p.2 : Opens X) : Set X)) =
        ((f : C1 D 𝒱) p : RS.MeroGermOn X ((𝒱.U p.1 ⊓ 𝒱.U p.2 : Opens X) : Set X))
      rw [Submodule.coe_inclusion]
    rw [mlClass, hfz]
    exact hc
  · rintro ⟨w, rfl⟩
    exact H1Incl_windowConnect h w

end RS.Cech

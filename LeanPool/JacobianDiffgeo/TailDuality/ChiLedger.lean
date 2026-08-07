/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.TailDuality.Duality

/-!
# The tail-χ ledger: `chiT` additivity (serre-duality-tails, chiT-ledger closure)

Unit: serre-duality-tails (`docs/design/serre-duality-tails.md` §4/§9, orchestrator addendum
2026-07-08's "prove the TAIL-level six-term fragment + tail-chi ledger internally" instruction).
This file discharges the ONE honest gap `Duality.lean`'s docstring flagged: `chiT`'s additivity
(`chiT D = chiT 0 + deg D`), which is genuinely independent content from Serre duality (Miranda
§2.3/2.6's own six-term exactness, not §3).

**The construction.** Exactly `Finiteness/Chi.lean`'s own recipe (`sixterm_rank1/2/3` →
`chi_of_le` → `chi_eq_chi_zero_add_degree`), transposed to the tail level by replacing Čech's
`H1 D`/`windowConnect`/`H1Incl` with the tail-level analogues built here:

* **`H1TailIncl (h : D ≤ D') : H1Tail D →ₗ H1Tail D'`**: the descent of `truncT h` through the
  `alphaL`-quotients (well-defined by `truncT_alpha`); surjective because `truncT h` already is.
* **`windowConnectT (h : D ≤ D') : Window D D' →ₗ H1Tail D := H1Tail.mk D ∘ₗ windowToT D D' h`**
  (`windowToT` is laurent-tails' already-built embedding of Čech's finite window into the tail
  space, `Jacobian/LaurentTail/TailSpace.lean`).

The two hard exactness facts (`ker windowConnectT = range windowMap`,
`ker H1TailIncl = range windowConnectT`) are proved **entirely elementarily**, at the tail level,
with NO reference to Čech's own `H1`/`mlClass`/cochain machinery: `H1Tail D` being literally
`T D ⧸ range(alphaL D)` (a coker, not a colimit of cochain complexes) makes both a matter of
DFinsupp/Submodule bookkeeping + one witness-representative choice per point, exactly as the
orchestrator's routing note anticipated ("H1Tail = coker(alphaL) makes the connecting/exactness
elementary"). In particular this file does **not** wait on `H1Tail.toH1`'s surjectivity (still
out of scope, per `Comparison.lean`/the root docstring) — it is not used here at all.

## Exports

* `H1TailIncl`, `H1TailIncl_mk`, `H1TailIncl_surjective`.
* `windowConnectT`, `windowConnectT_apply`.
* `exact_windowMap_windowConnectT : Function.Exact (RS.Cech.windowMap h) (windowConnectT h)`.
* `exact_windowConnectT_H1TailIncl : Function.Exact (windowConnectT h) (H1TailIncl h)`.
* `chiT_of_le (h : D ≤ D') : chiT D' = chiT D + (D' - D).degree` — the ledger step.
* **`chiT_single_add (D) (P) : chiT (D + single P 1) = chiT D + 1`** — the task's headline
  additivity statement.
* **`chiT_eq_chiT_zero_add_degree (D) : chiT D = chiT 0 + D.degree`** — the primary deliverable.
-/

open scoped ContDiff Manifold
open Set TopologicalSpace
open RS RS.LaurentTail

namespace RS.TailDuality

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]

/-! ### `H1TailIncl`: the truncation map descended to `H1Tail` -/

/-- The truncation `t^{D}_{D'}` descends to `H¹Tail`, since it carries `range(α_D)` into
`range(α_{D'})` (`truncT_alpha`). -/
noncomputable def H1TailIncl {D D' : RS.Divisor X} (h : D ≤ D') :
    H1Tail D →ₗ[ℂ] H1Tail D' :=
  Submodule.mapQ _ _ (truncT h) (by
    rintro τ ⟨f, rfl⟩
    exact ⟨f, (truncT_alpha h f).symm⟩)

theorem H1TailIncl_mk {D D' : RS.Divisor X} (h : D ≤ D') (τ : T D) :
    H1TailIncl h (H1Tail.mk D τ) = H1Tail.mk D' (truncT h τ) :=
  Submodule.mapQ_apply _ _ _ τ

theorem H1TailIncl_surjective {D D' : RS.Divisor X} (h : D ≤ D') :
    Function.Surjective (H1TailIncl h) := by
  intro y
  obtain ⟨τ, rfl⟩ := H1Tail.mk_surjective D' y
  obtain ⟨τ₀, rfl⟩ := truncT_surjective h τ
  exact ⟨H1Tail.mk D τ₀, H1TailIncl_mk h τ₀⟩

/-! ### `windowConnectT`: the connecting map `Window D D' → H1Tail D` -/

/-- The tail-level connecting map: embed the finite Čech window into the tail space
(`windowToT`), then project to `H1Tail D`. -/
noncomputable def windowConnectT {D D' : RS.Divisor X} (h : D ≤ D') :
    RS.Cech.Window D D' →ₗ[ℂ] H1Tail D :=
  (H1Tail.mk D).comp (RS.LaurentTail.windowToT D D' h)

theorem windowConnectT_apply {D D' : RS.Divisor X} (h : D ≤ D') (w : RS.Cech.Window D D') :
    windowConnectT h w = H1Tail.mk D (RS.LaurentTail.windowToT D D' h w) := rfl

omit [ConnectedSpace X] [T1Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- `windowToT`'s value off the witness `Finset` is `0` (unfolds `T.mk`). -/
theorem windowToT_apply_of_not_mem {D D' : RS.Divisor X} (h : D ≤ D') (w : RS.Cech.Window D D')
    {p : X} (hp : p ∉ RS.Cech.diffSupp D D') :
    RS.LaurentTail.windowToT D D' h w p = 0 := by
  change RS.LaurentTail.T.mk D (RS.Cech.diffSupp D D')
      (fun q => RS.LaurentTail.windowAtToTailAt (q : X) D (D' q) (w q)) p = 0
  exact RS.LaurentTail.T.mk_apply_not_mem hp

/-! ### Exactness at `Window D D'`: `ker (windowConnectT h) = range (windowMap h)` -/

/-- The key identity: `windowMap`'s image, embedded via `windowToT`, is exactly `alphaL D` of the
same global section — the tail-level shadow of Čech's own `Realizes`/`mlClass` machinery, but
here a direct pointwise computation (no cochains). -/
theorem windowToT_windowMap {D D' : RS.Divisor X} (h : D ≤ D') (φ : RS.LinSys D') :
    RS.LaurentTail.windowToT D D' h (RS.Cech.windowMap h φ) = alphaL D (φ : RS.Mero X) := by
  apply DFinsupp.ext
  intro p
  rw [alphaL_apply]
  by_cases hp : p ∈ RS.Cech.diffSupp D D'
  · rw [RS.LaurentTail.windowToT_apply D D' h (RS.Cech.windowMap h φ) ⟨p, hp⟩,
      RS.Cech.windowMap_apply, RS.LaurentTail.windowAtToTailAt_mk,
      RS.Cech.restrictToChart_apply_coe, alpha_apply]
  · rw [windowToT_apply_of_not_mem h _ hp, eq_comm, alpha_apply_eq_zero_iff]
    have hDeq : D p = D' p := by
      by_contra hne
      exact hp (RS.Cech.mem_diffSupp_iff.2 hne)
    rw [hDeq]
    exact RS.mem_linSys_iff.mp φ.2 p

theorem windowConnectT_windowMap {D D' : RS.Divisor X} (h : D ≤ D') (φ : RS.LinSys D') :
    windowConnectT h (RS.Cech.windowMap h φ) = 0 := by
  rw [windowConnectT_apply, windowToT_windowMap]
  exact (H1Tail.mk_eq_zero_iff D _).2 ⟨(φ : RS.Mero X), rfl⟩

/-- The harder half: a window class killed by `windowConnectT` already comes from `L(D')` via
`windowMap` — an entirely elementary reconstruction (choose a representative per marked point,
show the resulting global section lands in `L(D')` by a two-term order estimate). -/
theorem windowConnectT_eq_zero_iff {D D' : RS.Divisor X} (h : D ≤ D') (w : RS.Cech.Window D D') :
    windowConnectT h w = 0 ↔ w ∈ LinearMap.range (RS.Cech.windowMap h) := by
  constructor
  swap
  · rintro ⟨φ, rfl⟩
    exact windowConnectT_windowMap h φ
  intro hz
  rw [windowConnectT_apply, H1Tail.mk_eq_zero_iff] at hz
  obtain ⟨f, hf⟩ := hz
  -- a representative `ξ q` of `w q` in the numerator submodule, for each marked point
  set ξ : ∀ q : RS.Cech.diffSupp D D', RS.Cech.ordGe (q : X) (-(D' q)) :=
    fun q => (RS.Cech.WindowAt.mk_surjective (q : X) (D q) (D' q) (w q)).choose with hξ_def
  have hξspec : ∀ q : RS.Cech.diffSupp D D',
      RS.Cech.WindowAt.mk (q : X) (D q) (D' q) (ξ q) = w q :=
    fun q => (RS.Cech.WindowAt.mk_surjective (q : X) (D q) (D' q) (w q)).choose_spec
  -- the core order estimate, reused for both the `L(D')`-membership and the final `windowMap` match
  have hcore : ∀ q : RS.Cech.diffSupp D D',
      ((-(D (q : X)) : ℤ) : WithTop ℤ) ≤
        ((RS.MeroGermOn.restrict (Set.subset_univ _) f : RS.MeroGermOn X (chartAt ℂ (q : X)).source)
            - (ξ q : RS.MeroGermOn X (chartAt ℂ (q : X)).source)).ord (q : X) := by
    intro q
    have h1 : TailAt.mk (q : X) D (RS.MeroGermOn.restrict (Set.subset_univ _) f) =
        TailAt.mk (q : X) D (ξ q : RS.MeroGermOn X (chartAt ℂ (q : X)).source) := by
      rw [← alpha_apply, ← alphaL_apply, hf, RS.LaurentTail.windowToT_apply D D' h w q,
        ← hξspec q, RS.LaurentTail.windowAtToTailAt_mk]
    have h2 : TailAt.mk (q : X) D
        ((RS.MeroGermOn.restrict (Set.subset_univ _) f : RS.MeroGermOn X (chartAt ℂ (q : X)).source)
          - (ξ q : RS.MeroGermOn X (chartAt ℂ (q : X)).source)) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.2 h1
    rwa [TailAt.mk_eq_zero_iff] at h2
  have hmemD' : f ∈ RS.LinSys D' := by
    rw [RS.mem_linSys_iff]
    intro p
    by_cases hp : p ∈ RS.Cech.diffSupp D D'
    · set q : RS.Cech.diffSupp D D' := ⟨p, hp⟩ with hq_def
      have hxi_ord : ((-(D' p) : ℤ) : WithTop ℤ) ≤
          (ξ q : RS.MeroGermOn X (chartAt ℂ p).source).ord p := (ξ q).2
      have hDD' : D p ≤ D' p := Function.locallyFinsuppWithin.le_def.1 h p
      have hDp_le : ((-(D' p) : ℤ) : WithTop ℤ) ≤ ((-(D p) : ℤ) : WithTop ℤ) := by
        exact_mod_cast (show -(D' p) ≤ -(D p) from by omega)
      have hdiff_ord : ((-(D' p) : ℤ) : WithTop ℤ) ≤
          ((RS.MeroGermOn.restrict (Set.subset_univ _) f : RS.MeroGermOn X (chartAt ℂ p).source)
              - (ξ q : RS.MeroGermOn X (chartAt ℂ p).source)).ord p :=
        hDp_le.trans (hcore q)
      have hsum_eq : (ξ q : RS.MeroGermOn X (chartAt ℂ p).source) +
          ((RS.MeroGermOn.restrict (Set.subset_univ _) f : RS.MeroGermOn X (chartAt ℂ p).source)
            - (ξ q : RS.MeroGermOn X (chartAt ℂ p).source))
          = RS.MeroGermOn.restrict (Set.subset_univ _) f := by abel
      have hadd := RS.MeroGermOn.ord_add (chartAt ℂ p).open_source (mem_chart_source ℂ p)
        (ξ q : RS.MeroGermOn X (chartAt ℂ p).source)
        ((RS.MeroGermOn.restrict (Set.subset_univ _) f : RS.MeroGermOn X (chartAt ℂ p).source)
          - (ξ q : RS.MeroGermOn X (chartAt ℂ p).source))
      rw [hsum_eq] at hadd
      have hrestr : ((-(D' p) : ℤ) : WithTop ℤ) ≤
          (RS.MeroGermOn.restrict (Set.subset_univ _) f :
            RS.MeroGermOn X (chartAt ℂ p).source).ord p :=
        (le_min hxi_ord hdiff_ord).trans hadd
      rwa [RS.MeroGermOn.ord_restrict (Set.subset_univ _) (chartAt ℂ p).open_source isOpen_univ
        (mem_chart_source ℂ p)] at hrestr
    · have hDeq : D p = D' p := by
        by_contra hne
        exact hp (RS.Cech.mem_diffSupp_iff.2 hne)
      have h0 : alpha D f p = 0 := by
        rw [← alphaL_apply, hf, windowToT_apply_of_not_mem h _ hp]
      rw [alpha_apply_eq_zero_iff, hDeq] at h0
      exact h0
  refine ⟨⟨f, hmemD'⟩, ?_⟩
  funext q
  have hval : (RS.Cech.restrictToChart D' (q : X) (⟨f, hmemD'⟩ : RS.LinSys D') :
      RS.MeroGermOn X (chartAt ℂ (q : X)).source) =
      RS.MeroGermOn.restrict (Set.subset_univ _) f :=
    RS.Cech.restrictToChart_apply_coe D' (q : X) ⟨f, hmemD'⟩
  have hzero : RS.Cech.WindowAt.mk (q : X) (D q) (D' q)
      (RS.Cech.restrictToChart D' (q : X) ⟨f, hmemD'⟩) -
      RS.Cech.WindowAt.mk (q : X) (D q) (D' q) (ξ q) = 0 := by
    rw [← map_sub, RS.Cech.WindowAt.mk_eq_zero_iff]
    change ((-(D (q : X)) : ℤ) : WithTop ℤ) ≤
        ((RS.Cech.restrictToChart D' (q : X) ⟨f, hmemD'⟩ :
            RS.MeroGermOn X (chartAt ℂ (q : X)).source) -
          (ξ q : RS.MeroGermOn X (chartAt ℂ (q : X)).source)).ord (q : X)
    rw [hval]
    exact hcore q
  have heq : RS.Cech.WindowAt.mk (q : X) (D q) (D' q)
      (RS.Cech.restrictToChart D' (q : X) ⟨f, hmemD'⟩) =
      RS.Cech.WindowAt.mk (q : X) (D q) (D' q) (ξ q) := sub_eq_zero.1 hzero
  rw [RS.Cech.windowMap_apply, heq, hξspec q]

/-- **Exactness at `Window D D'`**: `ker (windowConnectT h) = range (windowMap h)`. -/
theorem exact_windowMap_windowConnectT {D D' : RS.Divisor X} (h : D ≤ D') :
    Function.Exact (RS.Cech.windowMap h) (windowConnectT h) :=
  fun w => windowConnectT_eq_zero_iff h w

/-! ### Exactness at `H1Tail D`: `ker (H1TailIncl h) = range (windowConnectT h)` -/

omit [ConnectedSpace X] [T1Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- The window's image, truncated one step further, vanishes IDENTICALLY (not merely mod
`range(alphaL D')`) — the tail-level shadow of Čech's `H1Incl_windowConnect`, but here a direct
computation: a window representative already has order `≥ -(D' p)` at its marked point, so
truncating to `T D'` kills it outright. -/
theorem truncT_windowToT_eq_zero {D D' : RS.Divisor X} (h : D ≤ D') (w : RS.Cech.Window D D') :
    truncT h (RS.LaurentTail.windowToT D D' h w) = 0 := by
  apply DFinsupp.ext
  intro p
  rw [truncT_apply, DFinsupp.zero_apply]
  by_cases hp : p ∈ RS.Cech.diffSupp D D'
  · obtain ⟨ξ, hξ⟩ := RS.Cech.WindowAt.mk_surjective p (D p) (D' p) (w ⟨p, hp⟩)
    have hval : RS.LaurentTail.windowToT D D' h w p = TailAt.mk p D (ξ : RS.MeroGermOn X _) := by
      rw [RS.LaurentTail.windowToT_apply D D' h w ⟨p, hp⟩, ← hξ,
        RS.LaurentTail.windowAtToTailAt_mk]
    rw [hval, truncAt_mk, TailAt.mk_eq_zero_iff]
    exact ξ.2
  · rw [windowToT_apply_of_not_mem h w hp, map_zero]

/-- The harder half: a class killed by `H1TailIncl` already comes from `windowConnectT` — an
elementary reconstruction via a per-point representative choice (`H1Tail` being a genuine coker,
not a colimit of cochain complexes, makes this a DFinsupp bookkeeping exercise, no cohomological
machinery). -/
theorem H1TailIncl_eq_zero_iff {D D' : RS.Divisor X} (h : D ≤ D') (z : H1Tail D) :
    H1TailIncl h z = 0 ↔ z ∈ LinearMap.range (windowConnectT h) := by
  constructor
  swap
  · rintro ⟨w, rfl⟩
    rw [windowConnectT_apply, H1TailIncl_mk, truncT_windowToT_eq_zero h w, map_zero]
  intro hz
  obtain ⟨τ, rfl⟩ := H1Tail.mk_surjective D z
  rw [H1TailIncl_mk, H1Tail.mk_eq_zero_iff] at hz
  obtain ⟨f, hf⟩ := hz
  set τ' : T D := τ - alphaL D f with hτ'_def
  have htrunc0 : truncT h τ' = 0 := by
    rw [hτ'_def, map_sub, truncT_alpha, hf, sub_self]
  set ψ : ∀ q : RS.Cech.diffSupp D D', RS.MeroGermOn X (chartAt ℂ (q : X)).source :=
    fun q => (TailAt.mk_surjective (q : X) D (τ' (q : X))).choose with hψ_def
  have hψspec : ∀ q : RS.Cech.diffSupp D D', TailAt.mk (q : X) D (ψ q) = τ' (q : X) :=
    fun q => (TailAt.mk_surjective (q : X) D (τ' (q : X))).choose_spec
  have hψmem : ∀ q : RS.Cech.diffSupp D D',
      ((-(D' q) : ℤ) : WithTop ℤ) ≤ (ψ q).ord (q : X) := by
    intro q
    have h1 : truncAt (q : X) h (τ' (q : X)) = 0 := by
      have h2 := DFunLike.congr_fun htrunc0 (q : X)
      rwa [truncT_apply, DFinsupp.zero_apply] at h2
    rw [← hψspec q, truncAt_mk] at h1
    rwa [TailAt.mk_eq_zero_iff] at h1
  set w : RS.Cech.Window D D' :=
    fun q => RS.Cech.WindowAt.mk (q : X) (D q) (D' q) ⟨ψ q, hψmem q⟩ with hw_def
  have hweq : RS.LaurentTail.windowToT D D' h w = τ' := by
    apply DFinsupp.ext
    intro p
    by_cases hp : p ∈ RS.Cech.diffSupp D D'
    · rw [RS.LaurentTail.windowToT_apply D D' h w ⟨p, hp⟩]
      change RS.LaurentTail.windowAtToTailAt p D (D' p)
          (RS.Cech.WindowAt.mk p (D p) (D' p) ⟨ψ ⟨p, hp⟩, hψmem ⟨p, hp⟩⟩) = τ' p
      rw [RS.LaurentTail.windowAtToTailAt_mk]
      exact hψspec ⟨p, hp⟩
    · rw [windowToT_apply_of_not_mem h w hp]
      have hDeq : D p = D' p := by
        by_contra hne
        exact hp (RS.Cech.mem_diffSupp_iff.2 hne)
      obtain ⟨ψ₀, hψ₀⟩ := TailAt.mk_surjective p D (τ' p)
      have h1 : truncAt p h (τ' p) = 0 := by
        have h2 := DFunLike.congr_fun htrunc0 p
        rwa [truncT_apply, DFinsupp.zero_apply] at h2
      rw [← hψ₀, truncAt_mk, TailAt.mk_eq_zero_iff] at h1
      rw [← hψ₀, eq_comm, TailAt.mk_eq_zero_iff, hDeq]
      exact h1
  refine ⟨w, ?_⟩
  rw [windowConnectT_apply, hweq, hτ'_def, map_sub,
    show H1Tail.mk D (alphaL D f) = 0 from (H1Tail.mk_eq_zero_iff D _).2 ⟨f, rfl⟩, sub_zero]

/-- **Exactness at `H1Tail D`**: `ker (H1TailIncl h) = range (windowConnectT h)`. -/
theorem exact_windowConnectT_H1TailIncl {D D' : RS.Divisor X} (h : D ≤ D') :
    Function.Exact (windowConnectT h) (H1TailIncl h) :=
  fun z => H1TailIncl_eq_zero_iff h z

/-! ### The rank ledger, and `chiT`'s additivity -/

omit [T1Space X] [DecidableEq X] in
/-- `sixterm_rank1`'s tail-level analogue — unchanged from `Finiteness.Chi`'s own proof (no `H¹`
appears in it at all: it is purely about `L(D)`/`L(D')`/`Window D D'`). -/
private theorem sixterm_rankT1 {D D' : RS.Divisor X} (h : D ≤ D') :
    RS.l D' = RS.l D + Module.finrank ℂ (LinearMap.range (RS.Cech.windowMap h)) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (RS.Cech.windowMap h)
  have hexact : LinearMap.ker (RS.Cech.windowMap h) =
      LinearMap.range (Submodule.inclusion (RS.linSys_mono h)) :=
    (LinearMap.exact_iff).1 (RS.Cech.exact_inclusion_windowMap h)
  rw [hexact] at hrn
  have hrange_eq : Module.finrank ℂ
      (LinearMap.range (Submodule.inclusion (RS.linSys_mono h))) = RS.l D := by
    rw [RS.l]
    exact (LinearEquiv.ofInjective _ (RS.Cech.inclusion_injective h)).finrank_eq.symm
  rw [hrange_eq] at hrn
  change RS.l D' = RS.l D + Module.finrank ℂ (LinearMap.range (RS.Cech.windowMap h))
  unfold RS.l at hrn ⊢
  omega

private theorem sixterm_rankT2 {D D' : RS.Divisor X} (h : D ≤ D') :
    Module.finrank ℂ (RS.Cech.Window D D') =
      Module.finrank ℂ (LinearMap.range (RS.Cech.windowMap h)) +
        Module.finrank ℂ (LinearMap.range (windowConnectT h)) := by
  have hWfin : FiniteDimensional ℂ (RS.Cech.Window D D') :=
    RS.Cech.finiteDimensional_window D D' h
  have hrn := LinearMap.finrank_range_add_finrank_ker (windowConnectT h)
  have hexact : LinearMap.ker (windowConnectT h) = LinearMap.range (RS.Cech.windowMap h) :=
    (LinearMap.exact_iff).1 (exact_windowMap_windowConnectT h)
  rw [hexact] at hrn
  omega

private theorem sixterm_rankT3 {D D' : RS.Divisor X} (h : D ≤ D') :
    h1T D = Module.finrank ℂ (LinearMap.range (windowConnectT h)) + h1T D' := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (H1TailIncl h)
  have hexact : LinearMap.ker (H1TailIncl h) = LinearMap.range (windowConnectT h) :=
    (LinearMap.exact_iff).1 (exact_windowConnectT_H1TailIncl h)
  rw [hexact] at hrn
  have hsurj : LinearMap.range (H1TailIncl h) = ⊤ :=
    LinearMap.range_eq_top.2 (H1TailIncl_surjective h)
  have hrange_eq : Module.finrank ℂ (LinearMap.range (H1TailIncl h)) = h1T D' := by
    rw [hsurj]
    change Module.finrank ℂ (⊤ : Submodule ℂ (H1Tail D')) = Module.finrank ℂ (H1Tail D')
    exact finrank_top ℂ (H1Tail D')
  rw [hrange_eq] at hrn
  change h1T D = Module.finrank ℂ (LinearMap.range (windowConnectT h)) + h1T D'
  unfold h1T at hrn ⊢
  omega

theorem sixterm_ranksT {D D' : RS.Divisor X} (h : D ≤ D') :
    ∃ p q : ℕ, RS.l D' = RS.l D + p ∧ Module.finrank ℂ (RS.Cech.Window D D') = p + q ∧
      h1T D = q + h1T D' :=
  ⟨Module.finrank ℂ (LinearMap.range (RS.Cech.windowMap h)),
    Module.finrank ℂ (LinearMap.range (windowConnectT h)),
    sixterm_rankT1 h, sixterm_rankT2 h, sixterm_rankT3 h⟩

/-- **The tail ledger step**: `χT(D') = χT(D) + deg(D' − D)` for `D ≤ D'`. -/
theorem chiT_of_le {D D' : RS.Divisor X} (h : D ≤ D') :
    chiT D' = chiT D + (D' - D).degree := by
  obtain ⟨p, q, hp, hpq, hq⟩ := sixterm_ranksT h
  rw [RS.Cech.finrank_window h] at hpq
  have hnn : (0 : ℤ) ≤ (D' - D).degree :=
    Function.locallyFinsuppWithin.degree_nonneg_of_nonneg (sub_nonneg.2 h)
  have hcast : (((D' - D).degree).toNat : ℤ) = (D' - D).degree := Int.toNat_of_nonneg hnn
  unfold chiT
  omega

/-- **The task's headline additivity statement**: adding a single point of multiplicity `1`
raises `χT` by exactly `1`. -/
theorem chiT_single_add (D : RS.Divisor X) (P : X) :
    chiT (D + Function.locallyFinsuppWithin.single P (1 : ℤ)) = chiT D + 1 := by
  have hle : D ≤ D + Function.locallyFinsuppWithin.single P (1 : ℤ) := by
    refine le_add_of_nonneg_right ?_
    exact Function.locallyFinsuppWithin.single_nonneg.mpr (by norm_num)
  have hdeg : ((D + Function.locallyFinsuppWithin.single P (1 : ℤ)) - D).degree = 1 := by
    rw [add_sub_cancel_left, Function.locallyFinsuppWithin.degree_single]
  rw [chiT_of_le hle, hdeg]

/-- **The primary deliverable**: `χT(D) = χT(0) + deg D` for every `D` (`D' := D ⊔ 0`, two
applications of `chiT_of_le`, exactly `Finiteness.chi_eq_chi_zero_add_degree`'s own recipe). -/
theorem chiT_eq_chiT_zero_add_degree (D : RS.Divisor X) :
    chiT D = chiT (0 : RS.Divisor X) + D.degree := by
  set D' := D ⊔ 0 with hD'_def
  have e1 := chiT_of_le (D := D) (D' := D') le_sup_left
  have e2 := chiT_of_le (D := (0 : RS.Divisor X)) (D' := D') le_sup_right
  have hdeg1 : (D' - D).degree = D'.degree - D.degree := by
    rw [sub_eq_add_neg, Function.locallyFinsuppWithin.degree_add,
      Function.locallyFinsuppWithin.degree_neg]
    ring
  have hdeg2 : (D' - (0 : RS.Divisor X)).degree = D'.degree := by rw [sub_zero]
  rw [hdeg1] at e1
  rw [hdeg2] at e2
  omega

end RS.TailDuality

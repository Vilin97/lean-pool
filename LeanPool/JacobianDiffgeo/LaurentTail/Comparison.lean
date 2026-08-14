/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.LaurentTail.Truncation

/-!
# The comparison `H1Tail D ≃ₗ Cech.H1 D` (laurent-tails, design §4.3/§5)

Unit: laurent-tails (`docs/design/laurent-tails.md`).

**Status (honest, full account in the file-end note; this is a FINISHER-pass update — three of
the unit's four original deferrals are now closed):**

* `tailToH1 : T D →ₗ[ℂ] Cech.H1 D` — **fully built** (zero sorries), constructed from scratch via
  a per-point Mittag-Leffler class `mlClassAt D p ψ : H1 D` (a 2-member cover `{V, X∖{p}}`
  realizing `ψ` on a clean neighbourhood `V`), proved independent of every choice involved
  (`mlClassAtOf_agree`), then assembled via `Submodule.liftQ`/`DFinsupp.lsum`.
* `tailToH1_alpha` (`tailToH1 D (alphaL D f) = 0`) — **CLOSED**. The needed multi-point
  combination is built via `mlSumCochain`/`alphaPatch`/`alphaAuxD` (an `(|S|+1)`-member adapted
  cover realizing a *global* `f`'s restriction at each of its finitely many "bad" points, `0` on
  background) plus a `Finset.induction_on` combination (`CLAIM1` relates each point's `mlClassAt`
  to the big cover via a `pairCover`-to-`𝒱` refinement, `mlClass_add` combines two at a time);
  the whole sum vanishes via `mlClass_eq_zero_of_exists` with the *global* witness `f` itself,
  using that off-diagonal cover overlaps never meet the marked-point Finset `S` (pure adaptedness).
* `H1Tail.toH1 : H1Tail D →ₗ[ℂ] Cech.H1 D` (`Submodule.liftQ` off `tailToH1_alpha`) and
  **`H1Tail.toH1_injective`** — **CLOSED** (both). Injectivity needed a *second*, independent
  multi-point construction (`injG`/`injPatch`/`injD'`, this time realizing an *arbitrary* tail
  datum `z : T D` via *chosen* representatives `ψ p` rather than one global function — no global
  `f` is available a priori, that is exactly what injectivity produces), then
  `Cech.mlClass_eq_zero_iff`'s `⇒` half (Forster 12.4, confirmed landed) extracts a global
  witness `φ : LinSys D'` realizing `z` pointwise, i.e. `z = alpha D φ`.
* `H1Tail.equivOfSurjective` — a genuine, honestly-parametrized (`CONVENTIONS.md` rule 3)
  conditional equivalence: `Function.Surjective (tailToH1 D) → H1Tail D ≃ₗ[ℂ] Cech.H1 D`, built
  from the now-unconditional `H1Tail.toH1_injective`. **Surjectivity itself is NOT proved** — see
  the file-end note for a full account of why (this is now a *proven-hard* fact, not a
  bookkeeping gap: it requires resolving an arbitrary Čech cohomology class into a sum of
  Mittag-Leffler local data, which after `dolbeault-comparison`'s Leray theorem gives
  cocycle-on-a-good-cover representatives but does *not* by itself resolve the "collapse an
  arbitrary good-cover cocycle to marked-point-supported data" step — genuinely new complex
  analysis, comparable in depth to a Mittag-Leffler/Cousin-I existence theorem, well beyond a
  single finisher session; the file-end note records the full risk analysis for whoever picks
  this up next).

An important build-engineering lesson recorded here for future large proofs in this codebase
(see the file-end note's "gotchas" section): composing an `Opens X`-level `≤` with a `Set X`-level
`⊆` via bare `.trans` (relying on the automatic coercion) causes catastrophic `isDefEq`/`whnf`
slowdowns (confirmed: a single lemma this way took >4,000,000 heartbeats and did not finish in
7+ minutes; converting the `Opens`-level term to an explicit `Set`-level inclusion *first*, then
using plain `Set.Subset.trans`, fixed it in under 10 seconds). Likewise, a single tactic proof
accumulating ~25 `have`/`set` steps hits a severe elaboration performance wall regardless of
`maxHeartbeats`; factoring the construction into separate top-level `def`/`theorem` declarations
(each against an explicit `variable`/`include` list) — mirroring how `tailToH1_alpha`'s own
helpers (`alphaPatch`/`mlSumCochain`/…) were already structured — restores normal compile times.
-/

open scoped ContDiff Manifold
open Set TopologicalSpace RS.Cech


namespace RS.LaurentTail

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]

/-! ### Small helper lemmas towards the construction -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [DecidableEq X] in
/-- Isolated-singularity fact for a general (not necessarily connected/global) germ: away from
`p`, `φ` is regular (order `≥ 0`) on some open neighbourhood of `p` inside its domain. -/
theorem exists_clean_nhds {U : Set X} (hU : IsOpen U) (φ : RS.MeroGermOn X U) {p : X}
    (hp : p ∈ U) :
    ∃ V : Opens X, p ∈ V ∧ (V : Set X) ⊆ U ∧
      ∀ x ∈ (V : Set X), x ≠ p → (0 : WithTop ℤ) ≤ φ.ord x := by
  obtain ⟨t, ht, hfin⟩ := (φ.divisorOn).supportLocallyFiniteWithinDomain p hp
  set F : Set X := (t ∩ (φ.divisorOn).support) \ {p} with hF_def
  have hFfin : F.Finite := hfin.subset (fun x hx => hx.1)
  have hpF : p ∉ F := fun h => h.2 rfl
  refine ⟨⟨(interior t \ F) ∩ U, (isOpen_interior.sdiff hFfin.isClosed).inter hU⟩,
    ⟨⟨mem_interior_iff_mem_nhds.2 ht, hpF⟩, hp⟩, inter_subset_right, fun x hx hxp => ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  have hxF : x ∈ F := by
    refine ⟨⟨interior_subset hx.1.1, ?_⟩, hxp⟩
    change (φ.divisorOn) x ≠ 0
    rw [RS.MeroGermOn.divisorOn_apply]
    intro heq
    rw [WithTop.untop₀_eq_zero] at heq
    rcases heq with heq | heq
    · rw [heq] at hcon; exact absurd hcon (lt_irrefl 0)
    · rw [heq] at hcon; exact absurd hcon (by simp)
  exact hx.1.2 hxF

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- `C1.retype` commutes with restriction along a refinement index (both sides are literally the
same restriction of the same underlying germ). -/
theorem resC1_retype {D D' : RS.Divisor X} {Ω : Opens X} {𝒰 𝒱 : RS.Cech.FinCover Ω}
    (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : RS.Cech.IsRefIdx 𝒰 𝒱 τ) (f : RS.Cech.C1 D' 𝒰)
    (hf : f.MemLD D) (hf' : (RS.Cech.resC1 D' τ hτ f).MemLD D) :
    RS.Cech.resC1 D τ hτ (RS.Cech.C1.retype f hf) =
      RS.Cech.C1.retype (RS.Cech.resC1 D' τ hτ f) hf' := by
  funext p
  apply Subtype.ext
  have hL : (RS.Cech.resC1 D τ hτ (RS.Cech.C1.retype f hf) p : RS.MeroGermOn X _) =
      RS.MeroGermOn.restrict (inf_le_inf (hτ p.1) (hτ p.2))
        (f (τ p.1, τ p.2) : RS.MeroGermOn X _) := by
    rw [RS.Cech.resC1_apply, RS.Cech.restrictL_apply_coe, RS.Cech.C1.retype_apply_coe]
  have hR : (RS.Cech.C1.retype (RS.Cech.resC1 D' τ hτ f) hf' p : RS.MeroGermOn X _) =
      RS.MeroGermOn.restrict (inf_le_inf (hτ p.1) (hτ p.2))
        (f (τ p.1, τ p.2) : RS.MeroGermOn X _) := by
    rw [RS.Cech.C1.retype_apply_coe, RS.Cech.resC1_apply, RS.Cech.restrictL_apply_coe]
  rw [hL, hR]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- `mlClass` is compatible with refining the underlying cover: pulling the realizing `0`-cochain
back along a refinement index gives the same class in `H1 D`. -/
theorem mlClass_res {D D' : RS.Divisor X} {𝒰 𝒱 : RS.Cech.FinCover (⊤ : Opens X)}
    (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : RS.Cech.IsRefIdx 𝒰 𝒱 τ) (g : RS.Cech.C0 D' 𝒰)
    (hg : (RS.Cech.d0 D' 𝒰 g).MemLD D)
    (hg' : (RS.Cech.d0 D' 𝒱 (RS.Cech.resC0 D' τ hτ g)).MemLD D) :
    RS.Cech.mlClass 𝒰 g hg = RS.Cech.mlClass 𝒱 (RS.Cech.resC0 D' τ hτ g) hg' := by
  have hd0 : RS.Cech.d0 D' 𝒱 (RS.Cech.resC0 D' τ hτ g) =
      RS.Cech.resC1 D' τ hτ (RS.Cech.d0 D' 𝒰 g) :=
    (LinearMap.congr_fun (RS.Cech.resC1_comp_d0 D' τ hτ) g).symm
  have hg'' : (RS.Cech.resC1 D' τ hτ (RS.Cech.d0 D' 𝒰 g)).MemLD D := hd0 ▸ hg'
  have key : RS.Cech.resZ1 D τ hτ
      ⟨RS.Cech.C1.retype (RS.Cech.d0 D' 𝒰 g) hg, RS.Cech.C1.retype_mem_Z1 hg⟩ =
      ⟨RS.Cech.C1.retype (RS.Cech.d0 D' 𝒱 (RS.Cech.resC0 D' τ hτ g)) hg',
        RS.Cech.C1.retype_mem_Z1 hg'⟩ := by
    apply Subtype.ext
    rw [RS.Cech.resZ1_apply_coe]
    change RS.Cech.resC1 D τ hτ (RS.Cech.C1.retype (RS.Cech.d0 D' 𝒰 g) hg) =
      (RS.Cech.C1.retype (RS.Cech.d0 D' 𝒱 (RS.Cech.resC0 D' τ hτ g)) hg' : RS.Cech.C1 D 𝒱)
    rw [resC1_retype τ hτ (RS.Cech.d0 D' 𝒰 g) hg hg'']
    congr 1
    exact hd0.symm
  simp only [RS.Cech.mlClass]
  rw [← RS.Cech.toH1_resH1 D τ hτ, RS.Cech.resH1_mk, key]

/-! ### The per-point construction: realizing a clean representative -/

/-- The 2-member cover `{V, X ∖ {p}}`, used to realize a single tail datum at `p`. -/
@[reducible] noncomputable def pairCover (p : X) (V : Opens X) (hpV : p ∈ V) :
    RS.Cech.FinCover (⊤ : Opens X) where
  n := 2
  U := ![V, ⟨{p}ᶜ, isOpen_compl_singleton⟩]
  le_base _ := le_top
  covers x _ := by
    by_cases hx : x = p
    · exact ⟨0, by simpa [hx] using hpV⟩
    · exact ⟨1, by simpa using hx⟩

omit [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] in
theorem pairCover_U_zero (p : X) (V : Opens X) (hpV : p ∈ V) :
    (pairCover p V hpV).U (0 : Fin 2) = V := rfl

omit [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] in
theorem pairCover_U_one (p : X) (V : Opens X) (hpV : p ∈ V) :
    (pairCover p V hpV).U (1 : Fin 2) = ⟨{p}ᶜ, isOpen_compl_singleton⟩ := rfl

/-- The `0`-cochain realizing `ψV` on `V`, `0` on the background `X ∖ {p}`. -/
noncomputable def gOf (p : X) (V : Opens X) (hpV : p ∈ V) (D' : RS.Divisor X)
    (ψV : RS.LinSysOn D' (V : Set X)) : RS.Cech.C0 D' (pairCover p V hpV) := by
  change ∀ i : Fin 2, RS.LinSysOn D' (((pairCover p V hpV).U i : Opens X) : Set X)
  intro i
  by_cases h : i = 0
  · subst h; rw [pairCover_U_zero]; exact ψV
  · have h1 : i = 1 := by omega
    subst h1; rw [pairCover_U_one]; exact 0

/-- The bump divisor supported only at `p`, covering `-(ψ.ord p)` there. -/
noncomputable def bumpDivisor (p : X) (n : ℤ) : RS.Divisor X :=
  Function.locallyFinsuppWithin.single p n

omit [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X]
    [T1Space X] in
@[simp] theorem bumpDivisor_apply_self (p : X) (n : ℤ) : bumpDivisor p n p = n := by
  simp [bumpDivisor, Function.locallyFinsuppWithin.single_apply]

omit [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X]
    [T1Space X] in
theorem bumpDivisor_apply_of_ne {p x : X} (hx : x ≠ p) (n : ℤ) : bumpDivisor p n x = 0 := by
  simp [bumpDivisor, Function.locallyFinsuppWithin.single_apply, hx]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem d0_pairCover_diag {D' : RS.Divisor X} (p : X) (V : Opens X) (hpV : p ∈ V)
    (g : RS.Cech.C0 D' (pairCover p V hpV)) (i : Fin 2) :
    RS.Cech.d0 D' (pairCover p V hpV) g (i, i) = 0 := by
  rw [RS.Cech.d0_apply, sub_eq_zero]

/-! ### `mlClass` invariance under raising the auxiliary divisor `D'` (from
    `scratch_ltails2.lean`) -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem d0_inclC0_coe {Ω : Opens X} {𝒰 : RS.Cech.FinCover Ω} {D₁ D₂ : RS.Divisor X}
    (h : D₁ ≤ D₂) (g : RS.Cech.C0 D₁ 𝒰) (p : Fin 𝒰.n × Fin 𝒰.n) :
    (RS.Cech.d0 D₂ 𝒰 (RS.Cech.inclC0 D₁ 𝒰 h g) p :
        RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X)) =
      (RS.Cech.d0 D₁ 𝒰 g p : RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X)) := by
  rw [RS.Cech.d0_apply, RS.Cech.d0_apply, Submodule.coe_sub, Submodule.coe_sub,
    RS.Cech.restrictL_apply_coe, RS.Cech.restrictL_apply_coe,
    RS.Cech.restrictL_apply_coe, RS.Cech.restrictL_apply_coe,
    RS.Cech.inclC0_apply, RS.Cech.inclC0_apply]
  rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem memLD_inclC0 {Ω : Opens X} {𝒰 : RS.Cech.FinCover Ω} {D₁ D₂ D : RS.Divisor X}
    (h : D₁ ≤ D₂) {g : RS.Cech.C0 D₁ 𝒰} (hg : (RS.Cech.d0 D₁ 𝒰 g).MemLD D) :
    (RS.Cech.d0 D₂ 𝒰 (RS.Cech.inclC0 D₁ 𝒰 h g)).MemLD D := by
  intro p
  rw [d0_inclC0_coe]
  exact hg p

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mlClass_inclC0 {𝒰 : RS.Cech.FinCover (⊤ : Opens X)} {D₁ D₂ D : RS.Divisor X}
    (h : D₁ ≤ D₂) {g : RS.Cech.C0 D₁ 𝒰} (hg : (RS.Cech.d0 D₁ 𝒰 g).MemLD D) :
    RS.Cech.mlClass 𝒰 (RS.Cech.inclC0 D₁ 𝒰 h g) (memLD_inclC0 h hg) = RS.Cech.mlClass 𝒰 g hg := by
  have hval : RS.Cech.C1.retype (RS.Cech.d0 D₂ 𝒰 (RS.Cech.inclC0 D₁ 𝒰 h g)) (memLD_inclC0 h hg) =
      RS.Cech.C1.retype (RS.Cech.d0 D₁ 𝒰 g) hg := by
    funext p
    apply Subtype.ext
    simp only [RS.Cech.C1.retype_apply_coe]
    rw [d0_inclC0_coe]
  change RS.Cech.toH1 D 𝒰 (RS.Cech.H1Cover.mk D 𝒰
      ⟨RS.Cech.C1.retype (RS.Cech.d0 D₂ 𝒰 (RS.Cech.inclC0 D₁ 𝒰 h g)) (memLD_inclC0 h hg),
        RS.Cech.C1.retype_mem_Z1 (memLD_inclC0 h hg)⟩) =
    RS.Cech.toH1 D 𝒰 (RS.Cech.H1Cover.mk D 𝒰
      ⟨RS.Cech.C1.retype (RS.Cech.d0 D₁ 𝒰 g) hg, RS.Cech.C1.retype_mem_Z1 hg⟩)
  exact congrArg (RS.Cech.toH1 D 𝒰) (congrArg (RS.Cech.H1Cover.mk D 𝒰) (Subtype.ext hval))

/-! ### `gOf` algebra -/

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] in
theorem gOf_add (p : X) (V : Opens X) (hpV : p ∈ V) (D' : RS.Divisor X)
    (ψV ψV' : RS.LinSysOn D' (V : Set X)) :
    gOf p V hpV D' (ψV + ψV') = gOf p V hpV D' ψV + gOf p V hpV D' ψV' := by
  funext i
  fin_cases i
  · apply Subtype.ext; rfl
  · apply Subtype.ext
    change (0 : RS.MeroGermOn X _) = (0:RS.MeroGermOn X _) + (0:RS.MeroGermOn X _)
    exact (add_zero 0).symm

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] in
theorem gOf_smul (c : ℂ) (p : X) (V : Opens X) (hpV : p ∈ V) (D' : RS.Divisor X)
    (ψV : RS.LinSysOn D' (V : Set X)) :
    gOf p V hpV D' (c • ψV) = c • gOf p V hpV D' ψV := by
  funext i
  fin_cases i
  · apply Subtype.ext; rfl
  · apply Subtype.ext
    change (0 : RS.MeroGermOn X _) = c • (0:RS.MeroGermOn X _)
    exact (smul_zero c).symm

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] in
theorem gOf_zero (p : X) (V : Opens X) (hpV : p ∈ V) (D' : RS.Divisor X) :
    gOf p V hpV D' 0 = 0 := by
  funext i
  fin_cases i
  · apply Subtype.ext; rfl
  · apply Subtype.ext; rfl

/-! ### A clean neighborhood also avoiding `D`'s other poles -/

/-- A chart neighbourhood of `p` clean for `ψ`: small enough that `ψ` is the only departure from `D`
on it. -/
noncomputable def cleanNbhd (D : RS.Divisor X) (p : X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) : Opens X :=
  (exists_clean_nhds (chartAt ℂ p).open_source ψ (mem_chart_source ℂ p)).choose ⊓
    compOpens ((D.finiteSupport isCompact_univ).toFinset.erase p)

omit [ConnectedSpace X] in
theorem mem_cleanNbhd (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    p ∈ cleanNbhd D p ψ :=
  ⟨(exists_clean_nhds (chartAt ℂ p).open_source ψ (mem_chart_source ℂ p)).choose_spec.1,
    mem_compOpens.mpr (fun h => (Finset.mem_erase.mp h).1 rfl)⟩

omit [ConnectedSpace X] in
theorem cleanNbhd_sub_source (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    (cleanNbhd D p ψ : Set X) ⊆ (chartAt ℂ p).source :=
  fun _x hx =>
      (exists_clean_nhds (chartAt ℂ p).open_source ψ (mem_chart_source ℂ p)).choose_spec.2.1 hx.1

omit [ConnectedSpace X] in
theorem cleanNbhd_ord_nonneg (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    ∀ x ∈ (cleanNbhd D p ψ : Set X), x ≠ p → (0 : WithTop ℤ) ≤ ψ.ord x :=
  fun x hx hxp => (exists_clean_nhds (chartAt ℂ p).open_source ψ
    (mem_chart_source ℂ p)).choose_spec.2.2 x hx.1 hxp

omit [ConnectedSpace X] in
theorem cleanNbhd_D_eq_zero (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    ∀ x ∈ (cleanNbhd D p ψ : Set X), x ≠ p → D x = 0 := by
  intro x hx hxp
  by_contra hDx
  have hmem : x ∈ (D.finiteSupport isCompact_univ).toFinset.erase p :=
    Finset.mem_erase.mpr ⟨hxp, (D.finiteSupport isCompact_univ).mem_toFinset.mpr
      (Function.mem_support.mpr hDx)⟩
  exact (mem_compOpens.mp hx.2) hmem

/-! ### The auxiliary divisor `D'` bumped at `p` -/

/-- The order of the pole that `ψ` contributes at `p`. -/
noncomputable def nOf (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) : ℤ :=
  max (D p) (-(ψ.ord p).untop₀)

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] [T1Space X]
    [DecidableEq X] in
theorem D_p_le_nOf (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    D p ≤ nOf D p ψ := le_max_left _ _

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] [T1Space X]
    [DecidableEq X] in
theorem neg_nOf_le_ord (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    ((-(nOf D p ψ) : ℤ) : WithTop ℤ) ≤ ψ.ord p := by
  rcases eq_or_ne (ψ.ord p) ⊤ with h | h
  · rw [h]; exact le_top
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp h
    have hnk : -k ≤ nOf D p ψ := by
      rw [nOf, ← hk, WithTop.untop₀_coe]
      exact le_max_right _ _
    rw [← hk]
    have hfin : -(nOf D p ψ) ≤ k := by linarith
    exact_mod_cast hfin

/-- The auxiliary divisor admitting `ψ` at `p` on top of `D`. -/
noncomputable def DPrimeOf (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    RS.Divisor X :=
  D + bumpDivisor p (nOf D p ψ - D p)

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] [T1Space X] in
theorem DPrimeOf_apply_self (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    DPrimeOf D p ψ p = nOf D p ψ := by
  change (D + bumpDivisor p (nOf D p ψ - D p)) p = nOf D p ψ
  have hstep : (D + bumpDivisor p (nOf D p ψ - D p)) p =
      D p + bumpDivisor p (nOf D p ψ - D p) p :=
    congrFun (Function.locallyFinsuppWithin.coe_add D _) p
  rw [hstep, bumpDivisor_apply_self]
  ring

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] [T1Space X] in
theorem DPrimeOf_apply_of_ne (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source)
    {x : X} (hx : x ≠ p) : DPrimeOf D p ψ x = D x := by
  change (D + bumpDivisor p (nOf D p ψ - D p)) x = D x
  have hstep : (D + bumpDivisor p (nOf D p ψ - D p)) x =
      D x + bumpDivisor p (nOf D p ψ - D p) x :=
    congrFun (Function.locallyFinsuppWithin.coe_add D _) x
  rw [hstep, bumpDivisor_apply_of_ne hx]
  ring

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] [T1Space X] in
theorem D_le_DPrimeOf (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    D ≤ DPrimeOf D p ψ := by
  rw [Function.locallyFinsuppWithin.le_def]
  intro x
  rcases eq_or_ne x p with rfl | hx
  · rw [DPrimeOf_apply_self]; exact D_p_le_nOf D x ψ
  · rw [DPrimeOf_apply_of_ne D p ψ hx]

/-! ### The membership witness for `gOf`'s `V`-component -/

omit [ConnectedSpace X] in
theorem restrict_ψ_mem_linSysOn (D : RS.Divisor X) (p : X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    RS.MeroGermOn.restrict (cleanNbhd_sub_source D p ψ) ψ ∈
      RS.LinSysOn (DPrimeOf D p ψ) (cleanNbhd D p ψ : Set X) := by
  refine (RS.mem_linSysOn_iff_of_isOpen (cleanNbhd D p ψ).2).2 ?_
  intro x hx
  rw [RS.MeroGermOn.ord_restrict (cleanNbhd_sub_source D p ψ) (cleanNbhd D p ψ).2
    (chartAt ℂ p).open_source hx]
  rcases eq_or_ne x p with rfl | hxp
  · rw [DPrimeOf_apply_self]; exact neg_nOf_le_ord D x ψ
  · rw [DPrimeOf_apply_of_ne D p ψ hxp, cleanNbhd_D_eq_zero D p ψ x hx hxp]
    simpa using cleanNbhd_ord_nonneg D p ψ x hx hxp

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] in
theorem gOf_apply_zero (p : X) (V : Opens X) (hpV : p ∈ V) (D' : RS.Divisor X)
    (ψV : RS.LinSysOn D' (V : Set X)) :
    gOf p V hpV D' ψV (0 : Fin 2) = ψV := rfl

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] in
theorem gOf_apply_one (p : X) (V : Opens X) (hpV : p ∈ V) (D' : RS.Divisor X)
    (ψV : RS.LinSysOn D' (V : Set X)) :
    gOf p V hpV D' ψV (1 : Fin 2) = 0 := rfl

/-- `ψ` restricted to its clean neighbourhood, as a section of the auxiliary linear system. -/
noncomputable def ψVOf (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    RS.LinSysOn (DPrimeOf D p ψ) (cleanNbhd D p ψ : Set X) :=
  ⟨RS.MeroGermOn.restrict (cleanNbhd_sub_source D p ψ) ψ, restrict_ψ_mem_linSysOn D p ψ⟩

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] in
/-- Generic version: `gOf`'s coboundary is `D`-bounded whenever `V` is clean for `ψ` away from
`p` and avoids `D`'s other poles, and `D'` agrees with `D` away from `p`. Stated with fully
abstract `V`/`ψV`/`D'` (no unfolding of `cleanNbhd`/`ψVOf`/`DPrimeOf` needed inside the proof). -/
theorem gOf_memLD_of_clean (p : X) (D D' : RS.Divisor X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source)
    (V : Opens X) (hpV : p ∈ V) (hVsub : (V : Set X) ⊆ (chartAt ℂ p).source)
    (hVclean : ∀ x ∈ (V : Set X), x ≠ p → (0 : WithTop ℤ) ≤ ψ.ord x)
    (hVDzero : ∀ x ∈ (V : Set X), x ≠ p → D x = 0)
    (ψV : RS.LinSysOn D' (V : Set X))
    (hψV : (ψV : RS.MeroGermOn X (V : Set X)) = RS.MeroGermOn.restrict hVsub ψ) :
    (RS.Cech.d0 D' (pairCover p V hpV) (gOf p V hpV D' ψV)).MemLD D := by
  rintro ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> dsimp only
  · rw [d0_pairCover_diag]; exact Submodule.zero_mem _
  · erw [RS.Cech.d0_apply, gOf_apply_one, gOf_apply_zero, map_zero, zero_sub]
    refine (RS.mem_linSysOn_iff_of_isOpen ((pairCover p V hpV).U _ ⊓
        (pairCover p V hpV).U _).2).2 ?_
    intro x hx
    have hxV : x ∈ (V : Set X) := hx.1
    have hxp : x ≠ p := hx.2
    rw [Submodule.coe_neg, RS.MeroGermOn.ord_neg,
      RS.Cech.ord_restrictL D' inf_le_left hx ψV, hψV]
    have hordeq : ((RS.MeroGermOn.restrict hVsub) ψ).ord x = ψ.ord x :=
      RS.MeroGermOn.ord_restrict hVsub V.2 (chartAt ℂ p).open_source hxV ψ
    have hbound : (((-D x : ℤ) : WithTop ℤ)) ≤ ψ.ord x := by
      rw [hVDzero x hxV hxp]; simpa using hVclean x hxV hxp
    exact hbound.trans_eq hordeq.symm
  · erw [RS.Cech.d0_apply, gOf_apply_zero, gOf_apply_one, map_zero, sub_zero]
    refine (RS.mem_linSysOn_iff_of_isOpen ((pairCover p V hpV).U _ ⊓
        (pairCover p V hpV).U _).2).2 ?_
    intro x hx
    have hxV : x ∈ (V : Set X) := hx.2
    have hxp : x ≠ p := hx.1
    rw [RS.Cech.ord_restrictL D' inf_le_right hx ψV, hψV]
    have hordeq : ((RS.MeroGermOn.restrict hVsub) ψ).ord x = ψ.ord x :=
      RS.MeroGermOn.ord_restrict hVsub V.2 (chartAt ℂ p).open_source hxV ψ
    have hbound : (((-D x : ℤ) : WithTop ℤ)) ≤ ψ.ord x := by
      rw [hVDzero x hxV hxp]; simpa using hVclean x hxV hxp
    exact hbound.trans_eq hordeq.symm
  · rw [d0_pairCover_diag]; exact Submodule.zero_mem _

/-! ### `gOf` commutes with `inclC0` and with refinement (`resC0`) -/

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] in
theorem gOf_inclC0 (p : X) (V : Opens X) (hpV : p ∈ V) {D'₁ D'₂ : RS.Divisor X}
    (h : D'₁ ≤ D'₂) (ψV : RS.LinSysOn D'₁ (V : Set X)) :
    RS.Cech.inclC0 D'₁ (pairCover p V hpV) h (gOf p V hpV D'₁ ψV) =
      gOf p V hpV D'₂ (Submodule.inclusion (RS.Cech.linSysOn_mono h) ψV) := by
  funext k
  fin_cases k <;> apply Subtype.ext <;> rfl

omit [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] in
theorem pairCover_isRefIdx (p : X) (V W : Opens X) (hpV : p ∈ V) (hpW : p ∈ W) (hWV : W ≤ V) :
    RS.Cech.IsRefIdx (pairCover p V hpV) (pairCover p W hpW) id := by
  intro k
  fin_cases k
  · exact hWV
  · exact le_refl _

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] in
theorem gOf_resC0 (p : X) (V W : Opens X) (hpV : p ∈ V) (hpW : p ∈ W) (hWV : W ≤ V)
    (D' : RS.Divisor X) (ψV : RS.LinSysOn D' (V : Set X)) :
    RS.Cech.resC0 (𝒰 := pairCover p V hpV) (𝒱 := pairCover p W hpW) D' id
        (pairCover_isRefIdx p V W hpV hpW hWV) (gOf p V hpV D' ψV) =
      gOf p W hpW D' (RS.Cech.LinSysOn.restrictL D' hWV ψV) := by
  funext k
  fin_cases k <;> apply Subtype.ext <;> rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Transport `mlClass` along an equality of the underlying `0`-cochain (avoids the
"motive is not type correct" failure of `rw` on `mlClass`'s dependent `hg` argument). -/
theorem mlClass_congr {𝒰 : RS.Cech.FinCover (⊤ : Opens X)} {D D' : RS.Divisor X}
    {g g' : RS.Cech.C0 D' 𝒰} (heq : g = g') {hg : (RS.Cech.d0 D' 𝒰 g).MemLD D} :
    RS.Cech.mlClass 𝒰 g hg = RS.Cech.mlClass 𝒰 g' (heq ▸ hg) := by
  subst heq; rfl

/-! ### The single-point Mittag-Leffler class, and its independence of choices -/

/-- The Mittag-Leffler class of `ψ` at `p`, computed through a chosen clean neighbourhood `V`. -/
noncomputable def mlClassAtOf (p : X) (D D' : RS.Divisor X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) (V : Opens X) (hpV : p ∈ V)
    (hVsub : (V : Set X) ⊆ (chartAt ℂ p).source)
    (hVclean : ∀ x ∈ (V : Set X), x ≠ p → (0 : WithTop ℤ) ≤ ψ.ord x)
    (hVDzero : ∀ x ∈ (V : Set X), x ≠ p → D x = 0)
    (ψV : RS.LinSysOn D' (V : Set X))
    (hψV : (ψV : RS.MeroGermOn X (V : Set X)) = RS.MeroGermOn.restrict hVsub ψ) :
    RS.Cech.H1 D :=
  RS.Cech.mlClass (pairCover p V hpV) (gOf p V hpV D' ψV)
    (gOf_memLD_of_clean p D D' ψ V hpV hVsub hVclean hVDzero ψV hψV)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Raise-then-refine identity: `mlClassAtOf` computed via `(D',V)` equals the one computed via
`(D'', W)` for `W ≤ V` and `D' ≤ D''`, provided the `D''`-typed representative on `W` is again
`restrict ψ`. -/
theorem mlClassAtOf_raise_res (p : X) (D D' D'' : RS.Divisor X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) (V W : Opens X) (hpV : p ∈ V) (hpW : p ∈ W)
    (hWV : W ≤ V) (hVsub : (V : Set X) ⊆ (chartAt ℂ p).source)
    (hVclean : ∀ x ∈ (V : Set X), x ≠ p → (0 : WithTop ℤ) ≤ ψ.ord x)
    (hVDzero : ∀ x ∈ (V : Set X), x ≠ p → D x = 0)
    (hWsub : (W : Set X) ⊆ (chartAt ℂ p).source)
    (hWclean : ∀ x ∈ (W : Set X), x ≠ p → (0 : WithTop ℤ) ≤ ψ.ord x)
    (hWDzero : ∀ x ∈ (W : Set X), x ≠ p → D x = 0)
    (h : D' ≤ D'') (ψV : RS.LinSysOn D' (V : Set X))
    (hψV : (ψV : RS.MeroGermOn X (V : Set X)) = RS.MeroGermOn.restrict hVsub ψ)
    (ψW : RS.LinSysOn D'' (W : Set X))
    (hψW : (ψW : RS.MeroGermOn X (W : Set X)) = RS.MeroGermOn.restrict hWsub ψ) :
    mlClassAtOf p D D' ψ V hpV hVsub hVclean hVDzero ψV hψV =
      mlClassAtOf p D D'' ψ W hpW hWsub hWclean hWDzero ψW hψW := by
  unfold mlClassAtOf
  set ψV'' : RS.LinSysOn D'' (V : Set X) :=
      Submodule.inclusion (RS.Cech.linSysOn_mono h) ψV with hψV''def
  have hψV'' : (ψV'' : RS.MeroGermOn X (V : Set X)) = RS.MeroGermOn.restrict hVsub ψ := hψV
  -- step 1: raise D' to D'' on the same cover `pairCover p V hpV`
  have e1 : RS.Cech.mlClass (pairCover p V hpV) (gOf p V hpV D' ψV)
        (gOf_memLD_of_clean p D D' ψ V hpV hVsub hVclean hVDzero ψV hψV) =
      RS.Cech.mlClass (pairCover p V hpV) (gOf p V hpV D'' ψV'')
        (gOf_memLD_of_clean p D D'' ψ V hpV hVsub hVclean hVDzero ψV'' hψV'') :=
    (mlClass_inclC0 h (gOf_memLD_of_clean p D D' ψ V hpV hVsub hVclean hVDzero ψV hψV)).symm.trans
      (mlClass_congr (gOf_inclC0 p V hpV h ψV))
  rw [e1]
  -- step 2: refine the cover from `V` down to `W`
  have e2 : RS.Cech.mlClass (pairCover p V hpV) (gOf p V hpV D'' ψV'')
        (gOf_memLD_of_clean p D D'' ψ V hpV hVsub hVclean hVDzero ψV'' hψV'') =
      RS.Cech.mlClass (pairCover p W hpW)
          (gOf p W hpW D'' (RS.Cech.LinSysOn.restrictL D'' hWV ψV''))
        (gOf_memLD_of_clean p D D'' ψ W hpW hWsub hWclean hWDzero
          (RS.Cech.LinSysOn.restrictL D'' hWV ψV'')
          (by rw [RS.Cech.restrictL_apply_coe, hψV'']
              exact RS.MeroGermOn.restrict_restrict _ _ ψ)) :=
    (mlClass_res (𝒰 := pairCover p V hpV) (𝒱 := pairCover p W hpW) id
      (pairCover_isRefIdx p V W hpV hpW hWV) (gOf p V hpV D'' ψV'')
      (gOf_memLD_of_clean p D D'' ψ V hpV hVsub hVclean hVDzero ψV'' hψV'')
      (by rw [gOf_resC0]
          exact gOf_memLD_of_clean p D D'' ψ W hpW hWsub hWclean hWDzero
            (RS.Cech.LinSysOn.restrictL D'' hWV ψV'')
            (by rw [RS.Cech.restrictL_apply_coe, hψV'']
                exact RS.MeroGermOn.restrict_restrict _ _ ψ))).trans
      (mlClass_congr (gOf_resC0 p V W hpV hpW hWV D'' ψV''))
  rw [e2]
  have hval : gOf p W hpW D'' (RS.Cech.LinSysOn.restrictL D'' hWV ψV'') = gOf p W hpW D'' ψW :=
    congrArg (gOf p W hpW D'') (Subtype.ext (by
      rw [RS.Cech.restrictL_apply_coe, hψV'']
      exact (RS.MeroGermOn.restrict_restrict _ _ ψ).trans hψW.symm))
  exact mlClass_congr hval

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- **Independence of choices.** `mlClassAtOf`'s value does not depend on which valid
`(V, D', ψV)` data is used to represent the same ambient germ `ψ`. -/
theorem mlClassAtOf_agree (p : X) (D : RS.Divisor X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source)
    {D'₁ D'₂ : RS.Divisor X} {V₁ V₂ : Opens X} (hpV₁ : p ∈ V₁) (hpV₂ : p ∈ V₂)
    (hV₁sub : (V₁ : Set X) ⊆ (chartAt ℂ p).source)
    (hV₁clean : ∀ x ∈ (V₁ : Set X), x ≠ p → (0 : WithTop ℤ) ≤ ψ.ord x)
    (hV₁Dzero : ∀ x ∈ (V₁ : Set X), x ≠ p → D x = 0)
    (hV₂sub : (V₂ : Set X) ⊆ (chartAt ℂ p).source)
    (hV₂clean : ∀ x ∈ (V₂ : Set X), x ≠ p → (0 : WithTop ℤ) ≤ ψ.ord x)
    (hV₂Dzero : ∀ x ∈ (V₂ : Set X), x ≠ p → D x = 0)
    (ψV₁ : RS.LinSysOn D'₁ (V₁ : Set X))
    (hψV₁ : (ψV₁ : RS.MeroGermOn X (V₁ : Set X)) = RS.MeroGermOn.restrict hV₁sub ψ)
    (ψV₂ : RS.LinSysOn D'₂ (V₂ : Set X))
    (hψV₂ : (ψV₂ : RS.MeroGermOn X (V₂ : Set X)) = RS.MeroGermOn.restrict hV₂sub ψ) :
    mlClassAtOf p D D'₁ ψ V₁ hpV₁ hV₁sub hV₁clean hV₁Dzero ψV₁ hψV₁ =
      mlClassAtOf p D D'₂ ψ V₂ hpV₂ hV₂sub hV₂clean hV₂Dzero ψV₂ hψV₂ := by
  set W : Opens X := V₁ ⊓ V₂ with hWdef
  have hpW : p ∈ W := ⟨hpV₁, hpV₂⟩
  have hWV₁ : W ≤ V₁ := inf_le_left
  have hWV₂ : W ≤ V₂ := inf_le_right
  have hWsub : (W : Set X) ⊆ (chartAt ℂ p).source := fun x hx => hV₁sub hx.1
  have hWclean : ∀ x ∈ (W : Set X), x ≠ p → (0 : WithTop ℤ) ≤ ψ.ord x :=
    fun x hx hxp => hV₁clean x (hWV₁ hx) hxp
  have hWDzero : ∀ x ∈ (W : Set X), x ≠ p → D x = 0 := fun x hx hxp => hV₁Dzero x (hWV₁ hx) hxp
  set D'' : RS.Divisor X := D'₁ ⊔ D'₂ with hD''def
  have h₁ : D'₁ ≤ D'' := le_sup_left
  have h₂ : D'₂ ≤ D'' := le_sup_right
  have hψWmem : RS.MeroGermOn.restrict hWsub ψ ∈ RS.LinSysOn D'' (W : Set X) := by
    refine (RS.mem_linSysOn_iff_of_isOpen W.2).2 ?_
    intro x hx
    rw [RS.MeroGermOn.ord_restrict hWsub W.2 (chartAt ℂ p).open_source hx]
    have hb1 : ((-(D'₁ x) : ℤ) : WithTop ℤ) ≤ ψ.ord x := by
      have hmem := (RS.mem_linSysOn_iff_of_isOpen V₁.2).1 ψV₁.2 x (hWV₁ hx)
      rwa [hψV₁, RS.MeroGermOn.ord_restrict hV₁sub V₁.2 (chartAt ℂ p).open_source (hWV₁ hx)] at hmem
    have hDsup : D'' x = D'₁ x ⊔ D'₂ x := Function.locallyFinsuppWithin.max_apply
    have hcast : ((-(D'' x) : ℤ) : WithTop ℤ) ≤ ((-(D'₁ x) : ℤ) : WithTop ℤ) := by
      rw [hDsup]
      exact_mod_cast neg_le_neg (le_max_left (D'₁ x) (D'₂ x))
    exact hcast.trans hb1
  set ψW : RS.LinSysOn D'' (W : Set X) := ⟨RS.MeroGermOn.restrict hWsub ψ, hψWmem⟩ with hψWdef
  have hψW : (ψW : RS.MeroGermOn X (W : Set X)) = RS.MeroGermOn.restrict hWsub ψ := rfl
  have hL := mlClassAtOf_raise_res p D D'₁ D'' ψ V₁ W hpV₁ hpW hWV₁ hV₁sub hV₁clean hV₁Dzero
    hWsub hWclean hWDzero h₁ ψV₁ hψV₁ ψW hψW
  have hR := mlClassAtOf_raise_res p D D'₂ D'' ψ V₂ W hpV₂ hpW hWV₂ hV₂sub hV₂clean hV₂Dzero
    hWsub hWclean hWDzero h₂ ψV₂ hψV₂ ψW hψW
  rw [hL, hR]

/-! ### `mlClassAt` (the canonical single-point construction) -/

/-- The Mittag-Leffler class in `H¹(D)` of a germ `ψ` at the point `p`. -/
noncomputable def mlClassAt (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    RS.Cech.H1 D :=
  mlClassAtOf p D (DPrimeOf D p ψ) ψ (cleanNbhd D p ψ) (mem_cleanNbhd D p ψ)
    (cleanNbhd_sub_source D p ψ) (cleanNbhd_ord_nonneg D p ψ) (cleanNbhd_D_eq_zero D p ψ)
    (ψVOf D p ψ) rfl

omit [ConnectedSpace X] in
theorem mlClassAt_eq_of_valid (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source)
    {D' : RS.Divisor X} {V : Opens X} (hpV : p ∈ V) (hVsub : (V : Set X) ⊆ (chartAt ℂ p).source)
    (hVclean : ∀ x ∈ (V : Set X), x ≠ p → (0 : WithTop ℤ) ≤ ψ.ord x)
    (hVDzero : ∀ x ∈ (V : Set X), x ≠ p → D x = 0) (ψV : RS.LinSysOn D' (V : Set X))
    (hψV : (ψV : RS.MeroGermOn X (V : Set X)) = RS.MeroGermOn.restrict hVsub ψ) :
    mlClassAt D p ψ = mlClassAtOf p D D' ψ V hpV hVsub hVclean hVDzero ψV hψV :=
  mlClassAtOf_agree p D ψ (mem_cleanNbhd D p ψ) hpV (cleanNbhd_sub_source D p ψ)
    (cleanNbhd_ord_nonneg D p ψ) (cleanNbhd_D_eq_zero D p ψ) hVsub hVclean hVDzero
    (ψVOf D p ψ) rfl ψV hψV

omit [ConnectedSpace X] in
theorem mlClassAt_eq_zero_of_mem_ordGe (D : RS.Divisor X) (p : X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) (hp : (-(D p) : WithTop ℤ) ≤ ψ.ord p) :
    mlClassAt D p ψ = 0 := by
  have hmem : RS.MeroGermOn.restrict (cleanNbhd_sub_source D p ψ) ψ ∈
      RS.LinSysOn D (cleanNbhd D p ψ : Set X) := by
    refine (RS.mem_linSysOn_iff_of_isOpen (cleanNbhd D p ψ).2).2 ?_
    intro x hx
    rw [RS.MeroGermOn.ord_restrict (cleanNbhd_sub_source D p ψ) (cleanNbhd D p ψ).2
      (chartAt ℂ p).open_source hx]
    rcases eq_or_ne x p with rfl | hxp
    · exact hp
    · rw [cleanNbhd_D_eq_zero D p ψ x hx hxp]
      simpa using cleanNbhd_ord_nonneg D p ψ x hx hxp
  set ψV0 : RS.LinSysOn D (cleanNbhd D p ψ : Set X) :=
    ⟨RS.MeroGermOn.restrict (cleanNbhd_sub_source D p ψ) ψ, hmem⟩ with hψV0def
  rw [mlClassAt_eq_of_valid D p ψ (mem_cleanNbhd D p ψ) (cleanNbhd_sub_source D p ψ)
    (cleanNbhd_ord_nonneg D p ψ) (cleanNbhd_D_eq_zero D p ψ) ψV0 rfl]
  unfold mlClassAtOf
  apply RS.Cech.mlClass_eq_zero_of_exists _ _ (0 : RS.LinSys D)
  intro i x hx
  fin_cases i <;> dsimp only
  · erw [gOf_apply_zero, map_zero, sub_zero]
    exact (RS.mem_linSysOn_iff_of_isOpen (cleanNbhd D p ψ).2).1 hmem x hx
  · erw [gOf_apply_one, map_zero, sub_zero, RS.MeroGermOn.ord_zero, ite_eq_left
      ⟨isOpen_compl_singleton, hx⟩]
    exact le_top

/-! ### `mlClassAt` is additive and `ℂ`-linear -/

omit [ConnectedSpace X] in
theorem mlClassAt_add (D : RS.Divisor X) (p : X) (ψ ψ' : RS.MeroGermOn X (chartAt ℂ p).source) :
    mlClassAt D p (ψ + ψ') = mlClassAt D p ψ + mlClassAt D p ψ' := by
  set V : Opens X := cleanNbhd D p ψ ⊓ cleanNbhd D p ψ' with hVdef
  have hpV : p ∈ V := ⟨mem_cleanNbhd D p ψ, mem_cleanNbhd D p ψ'⟩
  have hVsub : (V : Set X) ⊆ (chartAt ℂ p).source := fun x hx => cleanNbhd_sub_source D p ψ hx.1
  have hVclean : ∀ x ∈ (V : Set X), x ≠ p → (0 : WithTop ℤ) ≤ ψ.ord x :=
    fun x hx hxp => cleanNbhd_ord_nonneg D p ψ x hx.1 hxp
  have hVclean' : ∀ x ∈ (V : Set X), x ≠ p → (0 : WithTop ℤ) ≤ ψ'.ord x :=
    fun x hx hxp => cleanNbhd_ord_nonneg D p ψ' x hx.2 hxp
  have hVcleansum : ∀ x ∈ (V : Set X), x ≠ p → (0 : WithTop ℤ) ≤ (ψ + ψ').ord x := by
    intro x hx hxp
    exact le_trans (le_min (hVclean x hx hxp) (hVclean' x hx hxp))
      (RS.MeroGermOn.ord_add (chartAt ℂ p).open_source (hVsub hx) ψ ψ')
  have hVDzero : ∀ x ∈ (V : Set X), x ≠ p → D x = 0 :=
      fun x hx hxp => cleanNbhd_D_eq_zero D p ψ x hx.1 hxp
  set D' : RS.Divisor X := DPrimeOf D p ψ ⊔ DPrimeOf D p ψ' with hD'def
  have hDψ : D' p ≥ nOf D p ψ := by
    rw [hD'def]
    calc nOf D p ψ = DPrimeOf D p ψ p := (DPrimeOf_apply_self D p ψ).symm
      _ ≤ DPrimeOf D p ψ p ⊔ DPrimeOf D p ψ' p := le_sup_left
      _ = (DPrimeOf D p ψ ⊔ DPrimeOf D p ψ') p := (Function.locallyFinsuppWithin.max_apply).symm
  have hDψ' : D' p ≥ nOf D p ψ' := by
    rw [hD'def]
    calc nOf D p ψ' = DPrimeOf D p ψ' p := (DPrimeOf_apply_self D p ψ').symm
      _ ≤ DPrimeOf D p ψ p ⊔ DPrimeOf D p ψ' p := le_sup_right
      _ = (DPrimeOf D p ψ ⊔ DPrimeOf D p ψ') p := (Function.locallyFinsuppWithin.max_apply).symm
  have hD'x : ∀ x ≠ p, D' x = D x := by
    intro x hx
    rw [hD'def]
    change DPrimeOf D p ψ x ⊔ DPrimeOf D p ψ' x = D x
    rw [DPrimeOf_apply_of_ne D p ψ hx, DPrimeOf_apply_of_ne D p ψ' hx, sup_idem]
  have hboundψ : ((-(D' p) : ℤ) : WithTop ℤ) ≤ ψ.ord p := by
    calc ((-(D' p) : ℤ) : WithTop ℤ) ≤ ((-(nOf D p ψ) : ℤ) : WithTop ℤ) :=
        by exact_mod_cast neg_le_neg hDψ
      _ ≤ ψ.ord p := neg_nOf_le_ord D p ψ
  have hboundψ' : ((-(D' p) : ℤ) : WithTop ℤ) ≤ ψ'.ord p := by
    calc ((-(D' p) : ℤ) : WithTop ℤ) ≤ ((-(nOf D p ψ') : ℤ) : WithTop ℤ) :=
        by exact_mod_cast neg_le_neg hDψ'
      _ ≤ ψ'.ord p := neg_nOf_le_ord D p ψ'
  have hmemψ : RS.MeroGermOn.restrict hVsub ψ ∈ RS.LinSysOn D' (V : Set X) := by
    refine (RS.mem_linSysOn_iff_of_isOpen V.2).2 ?_
    intro x hx
    rw [RS.MeroGermOn.ord_restrict hVsub V.2 (chartAt ℂ p).open_source hx]
    rcases eq_or_ne x p with rfl | hxp
    · exact hboundψ
    · rw [hD'x x hxp, hVDzero x hx hxp]; simpa using hVclean x hx hxp
  have hmemψ' : RS.MeroGermOn.restrict hVsub ψ' ∈ RS.LinSysOn D' (V : Set X) := by
    refine (RS.mem_linSysOn_iff_of_isOpen V.2).2 ?_
    intro x hx
    rw [RS.MeroGermOn.ord_restrict hVsub V.2 (chartAt ℂ p).open_source hx]
    rcases eq_or_ne x p with rfl | hxp
    · exact hboundψ'
    · rw [hD'x x hxp, hVDzero x hx hxp]; simpa using hVclean' x hx hxp
  set ψVd : RS.LinSysOn D' (V : Set X) := ⟨RS.MeroGermOn.restrict hVsub ψ, hmemψ⟩ with hψVddef
  set ψV'd : RS.LinSysOn D' (V : Set X) := ⟨RS.MeroGermOn.restrict hVsub ψ', hmemψ'⟩ with hψV'ddef
  have hψVd : (ψVd : RS.MeroGermOn X (V : Set X)) = RS.MeroGermOn.restrict hVsub ψ := rfl
  have hψV'd : (ψV'd : RS.MeroGermOn X (V : Set X)) = RS.MeroGermOn.restrict hVsub ψ' := rfl
  have hψVsumd : ((ψVd + ψV'd : RS.LinSysOn D' (V : Set X)) : RS.MeroGermOn X (V : Set X)) =
      RS.MeroGermOn.restrict hVsub (ψ + ψ') := by
    rw [Submodule.coe_add, hψVd, hψV'd, map_add]
  have key1 : mlClassAt D p ψ = mlClassAtOf p D D' ψ V hpV hVsub hVclean hVDzero ψVd hψVd :=
    mlClassAt_eq_of_valid D p ψ hpV hVsub hVclean hVDzero ψVd hψVd
  have key2 : mlClassAt D p ψ' = mlClassAtOf p D D' ψ' V hpV hVsub hVclean' hVDzero ψV'd hψV'd :=
    mlClassAt_eq_of_valid D p ψ' hpV hVsub hVclean' hVDzero ψV'd hψV'd
  have key3 : mlClassAt D p (ψ + ψ') = mlClassAtOf p D D' (ψ + ψ') V hpV hVsub hVcleansum hVDzero
      (ψVd + ψV'd) hψVsumd :=
    mlClassAt_eq_of_valid D p (ψ + ψ') hpV hVsub hVcleansum hVDzero (ψVd + ψV'd) hψVsumd
  rw [key1, key2, key3]
  unfold mlClassAtOf
  exact (mlClass_congr (gOf_add p V hpV D' ψVd ψV'd)).trans
    (RS.Cech.mlClass_add _ _ _ _ _)

omit [ConnectedSpace X] in
theorem mlClassAt_smul (D : RS.Divisor X) (p : X) (c : ℂ)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    mlClassAt D p (c • ψ) = c • mlClassAt D p ψ := by
  have hψV : (ψVOf D p ψ : RS.MeroGermOn X (cleanNbhd D p ψ : Set X)) =
      RS.MeroGermOn.restrict (cleanNbhd_sub_source D p ψ) ψ := rfl
  have hmemc : RS.MeroGermOn.restrict (cleanNbhd_sub_source D p ψ) (c • ψ) ∈
      RS.LinSysOn (DPrimeOf D p ψ) (cleanNbhd D p ψ : Set X) := by
    rw [map_smul]
    exact Submodule.smul_mem _ c (restrict_ψ_mem_linSysOn D p ψ)
  set ψVc : RS.LinSysOn (DPrimeOf D p ψ) (cleanNbhd D p ψ : Set X) :=
    ⟨RS.MeroGermOn.restrict (cleanNbhd_sub_source D p ψ) (c • ψ), hmemc⟩ with hψVcdef
  have hψVc : (ψVc : RS.MeroGermOn X (cleanNbhd D p ψ : Set X)) =
      RS.MeroGermOn.restrict (cleanNbhd_sub_source D p ψ) (c • ψ) := rfl
  have hψVcsmul : ((c • ψVOf D p ψ : RS.LinSysOn (DPrimeOf D p ψ) (cleanNbhd D p ψ : Set X)) :
      RS.MeroGermOn X (cleanNbhd D p ψ : Set X)) =
      RS.MeroGermOn.restrict (cleanNbhd_sub_source D p ψ) (c • ψ) := by
    rw [Submodule.coe_smul, hψV, map_smul]
  have hVclean : ∀ x ∈ (cleanNbhd D p (c • ψ) : Set X), x ≠ p → (0 : WithTop ℤ) ≤ (c • ψ).ord x :=
    cleanNbhd_ord_nonneg D p (c • ψ)
  have key1 : mlClassAt D p (c • ψ) = mlClassAtOf p D (DPrimeOf D p ψ) (c • ψ)
      (cleanNbhd D p ψ) (mem_cleanNbhd D p ψ) (cleanNbhd_sub_source D p ψ)
      (fun x hx hxp => by
        rcases eq_or_ne c 0 with rfl | hc
        · rw [zero_smul, RS.MeroGermOn.ord_zero,
            ite_eq_left ⟨(chartAt ℂ p).open_source, cleanNbhd_sub_source D p ψ hx⟩]
          exact le_top
        · rw [RS.MeroGermOn.ord_smul (chartAt ℂ p).open_source (cleanNbhd_sub_source D p ψ hx) hc]
          exact cleanNbhd_ord_nonneg D p ψ x hx hxp)
      (cleanNbhd_D_eq_zero D p ψ) ψVc hψVc :=
    mlClassAt_eq_of_valid D p (c • ψ) (mem_cleanNbhd D p ψ) (cleanNbhd_sub_source D p ψ) _
      (cleanNbhd_D_eq_zero D p ψ) ψVc hψVc
  rw [key1]
  unfold mlClassAt mlClassAtOf
  have hgeq : gOf p (cleanNbhd D p ψ) (mem_cleanNbhd D p ψ) (DPrimeOf D p ψ) ψVc =
      c • gOf p (cleanNbhd D p ψ) (mem_cleanNbhd D p ψ) (DPrimeOf D p ψ) (ψVOf D p ψ) := by
    rw [← gOf_smul]
    congr 1
    apply Subtype.ext
    rw [hψVc, Submodule.coe_smul, hψV, map_smul]
  exact (mlClass_congr hgeq).trans (RS.Cech.mlClass_smul _ _ _ _)

/-! ### The ambient linear map, and its descent to `TailAt p D` / `T D` -/

/-- `AddCommGroup (H1 D)`, registered globally: `Module.DirectLimit.addCommGroup` is stated with
`G`/`f` as leading *explicit* arguments (not instance-implicit), so plain `inferInstance`/typeclass
search for `AddCommGroup (H1 D)` does not find it automatically through the `H1` abbrev — needed
explicitly here so `Submodule.liftQ`'s own instance search (for its codomain) succeeds. -/
noncomputable instance instAddCommGroupH1 (D : RS.Divisor X) : AddCommGroup (RS.Cech.H1 D) :=
  Module.DirectLimit.addCommGroup (fun 𝒰 : RS.Cech.FinCover (⊤ : Opens X) => RS.Cech.H1Cover D 𝒰)
    (fun _ _ h => RS.Cech.resH1' D h)

/-- `mlClassAt` packaged as a linear map on germs at `p`. -/
noncomputable def mlClassAtRaw (D : RS.Divisor X) (p : X) :
    RS.MeroGermOn X (chartAt ℂ p).source →ₗ[ℂ] RS.Cech.H1 D where
  toFun := mlClassAt D p
  map_add' := mlClassAt_add D p
  map_smul' := mlClassAt_smul D p

omit [ConnectedSpace X] in
theorem mlClassAtRaw_apply (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    mlClassAtRaw D p ψ = mlClassAt D p ψ := rfl

/-- The tail-to-cohomology map at a single point. -/
noncomputable def tailAtToH1 (D : RS.Divisor X) (p : X) : TailAt p D →ₗ[ℂ] RS.Cech.H1 D :=
  Submodule.liftQ (RS.Cech.ordGe p (-(D p))) (mlClassAtRaw D p) (fun ψ hψ => by
    rw [LinearMap.mem_ker, mlClassAtRaw_apply]
    exact mlClassAt_eq_zero_of_mem_ordGe D p ψ (RS.Cech.mem_ordGe_iff.mp hψ))

omit [ConnectedSpace X] in
theorem tailAtToH1_mk (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    tailAtToH1 D p (TailAt.mk p D ψ) = mlClassAt D p ψ :=
  Submodule.liftQ_apply _ _ ψ

/-- The tail-to-cohomology map on the whole tail space `T D`. -/
noncomputable def tailToH1 (D : RS.Divisor X) : T D →ₗ[ℂ] RS.Cech.H1 D :=
  DFinsupp.lsum ℕ (fun p => tailAtToH1 D p)

omit [ConnectedSpace X] in
theorem tailToH1_apply_single (D : RS.Divisor X) (p : X) (τ : TailAt p D) :
    tailToH1 D (DFinsupp.single p τ) = tailAtToH1 D p τ := by
  rw [tailToH1, DFinsupp.lsum_single]



/-! ### General helpers -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem d0_diag_eq_zero {Ω : Opens X} {𝒰 : RS.Cech.FinCover Ω} {D' : RS.Divisor X}
    (g : RS.Cech.C0 D' 𝒰) (i : Fin 𝒰.n) :
    RS.Cech.d0 D' 𝒰 g (i, i) = 0 := by
  rw [RS.Cech.d0_apply, sub_eq_zero]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mlClass_zero {𝒰 : RS.Cech.FinCover (⊤ : Opens X)} {D D' : RS.Divisor X}
    (hg : (RS.Cech.d0 D' 𝒰 (0 : RS.Cech.C0 D' 𝒰)).MemLD D) :
    RS.Cech.mlClass 𝒰 (0 : RS.Cech.C0 D' 𝒰) hg = 0 := by
  have h := RS.Cech.mlClass_smul (0 : ℂ) (0 : RS.Cech.C0 D' 𝒰) hg (by simpa using hg)
  simpa using h

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] [T1Space X]
    [DecidableEq X] in
theorem restrict_mem_linSysOn_of_mem_linSys {D' : RS.Divisor X} {f : RS.Mero X}
    (hf : f ∈ RS.LinSys D') (V : Set X) (hV : IsOpen V) :
    RS.MeroGermOn.restrict (Set.subset_univ V) f ∈ RS.LinSysOn D' V := by
  rw [RS.mem_linSysOn_iff_of_isOpen hV]
  intro x hx
  rw [RS.MeroGermOn.ord_restrict (Set.subset_univ V) hV isOpen_univ hx]
  exact (RS.mem_linSys_iff.1 hf) x

/-- The auxiliary divisor `D ⊔ (-div f)`, which admits `f`. -/
noncomputable def alphaAuxD (D : RS.Divisor X) (f : RS.Mero X) : RS.Divisor X :=
  D ⊔ (-(RS.divisor f))

omit [CompactSpace X] [DecidableEq X] in
theorem mem_linSys_alphaAuxD (D : RS.Divisor X) {f : RS.Mero X} (hf : f ≠ 0) :
    f ∈ RS.LinSys (alphaAuxD D f) := by
  rw [RS.mem_linSys_iff]
  intro x
  have h1 : (-(RS.divisor f) : RS.Divisor X) x ≤ alphaAuxD D f x := le_sup_right
  rw [RS.Divisor.neg_apply] at h1
  have h2 : (-(alphaAuxD D f x) : ℤ) ≤ RS.divisor f x := by linarith
  have h3 : ((RS.divisor f x : ℤ) : WithTop ℤ) = f.ord x := by
    rw [RS.divisor_apply]
    exact WithTop.coe_untop₀_of_ne_top (RS.Mero.ord_ne_top hf x)
  calc ((-(alphaAuxD D f x) : ℤ) : WithTop ℤ) ≤ ((RS.divisor f x : ℤ) : WithTop ℤ) := by
        exact_mod_cast h2
    _ = f.ord x := h3

/-! ### The clean patch at a marked point, avoiding the other marked points -/

/-- A neighbourhood of `p` clean for `f` and meeting no other marked point of `S`. -/
noncomputable def alphaPatch (D : RS.Divisor X) (f : RS.Mero X) (S : Finset X) (p : X) : Opens X :=
  cleanNbhd D p (RS.MeroGermOn.restrict (Set.subset_univ _) f) ⊓ RS.Cech.compOpens (S.erase p)

omit [ConnectedSpace X] in
theorem mem_alphaPatch (D : RS.Divisor X) (f : RS.Mero X) (S : Finset X) (p : X) :
    p ∈ alphaPatch D f S p :=
  ⟨mem_cleanNbhd D p _, RS.Cech.mem_compOpens.mpr (Finset.notMem_erase p S)⟩

omit [ConnectedSpace X] in
theorem alphaPatch_sub_source (D : RS.Divisor X) (f : RS.Mero X) (S : Finset X) (p : X) :
    (alphaPatch D f S p : Set X) ⊆ (chartAt ℂ p).source :=
  fun _x hx => cleanNbhd_sub_source D p _ hx.1

omit [ConnectedSpace X] in
theorem alphaPatch_clean (D : RS.Divisor X) (f : RS.Mero X) (S : Finset X) (p : X) :
    ∀ x ∈ (alphaPatch D f S p : Set X), x ≠ p →
      (0 : WithTop ℤ) ≤
        (RS.MeroGermOn.restrict (Set.subset_univ (chartAt ℂ p).source) f :
          RS.MeroGermOn X (chartAt ℂ p).source).ord x :=
  fun x hx hxp => cleanNbhd_ord_nonneg D p _ x hx.1 hxp

omit [ConnectedSpace X] in
theorem alphaPatch_D_eq_zero (D : RS.Divisor X) (f : RS.Mero X) (S : Finset X) (p : X) :
    ∀ x ∈ (alphaPatch D f S p : Set X), x ≠ p → D x = 0 :=
  fun x hx hxp => cleanNbhd_D_eq_zero D p _ x hx.1 hxp

omit [ConnectedSpace X] in
theorem alphaPatch_excl (D : RS.Divisor X) (f : RS.Mero X) (S : Finset X) (p : X) :
    ∀ x ∈ (alphaPatch D f S p : Set X), x ∉ S.erase p :=
  fun _x hx => RS.Cech.mem_compOpens.mp hx.2

/-! ### The Finset-indexed Mittag-Leffler cochain -/

open scoped Classical in
/-- The 0-cochain assembling `f`'s local data over the marked points of `T`. -/
noncomputable def mlSumCochain {𝒱 : RS.Cech.FinCover (⊤ : Opens X)} (D' : RS.Divisor X)
    (f : RS.Mero X) (hf : f ∈ RS.LinSys D') (T : Finset X) : RS.Cech.C0 D' 𝒱 :=
  fun k => if _h : ∃ p ∈ T, p ∈ 𝒱.U k then
      ⟨RS.MeroGermOn.restrict (Set.subset_univ _) f,
        restrict_mem_linSysOn_of_mem_linSys hf _ (𝒱.U k).isOpen⟩
    else 0

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] [T1Space X]
    [DecidableEq X] in
theorem mlSumCochain_apply_of_mem {𝒱 : RS.Cech.FinCover (⊤ : Opens X)} (D' : RS.Divisor X)
    (f : RS.Mero X) (hf : f ∈ RS.LinSys D') (T : Finset X) (k : Fin 𝒱.n) {p : X} (hpT : p ∈ T)
    (hpk : p ∈ 𝒱.U k) :
    mlSumCochain (𝒱 := 𝒱) D' f hf T k =
      ⟨RS.MeroGermOn.restrict (Set.subset_univ _) f,
        restrict_mem_linSysOn_of_mem_linSys hf _ (𝒱.U k).isOpen⟩ := by
  unfold mlSumCochain
  rw [dite_eq_left ⟨p, hpT, hpk⟩]

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] [T1Space X]
    [DecidableEq X] in
theorem mlSumCochain_apply_of_not_mem {𝒱 : RS.Cech.FinCover (⊤ : Opens X)} (D' : RS.Divisor X)
    (f : RS.Mero X) (hf : f ∈ RS.LinSys D') (T : Finset X) (k : Fin 𝒱.n)
    (hnot : ∀ p ∈ T, p ∉ 𝒱.U k) : mlSumCochain (𝒱 := 𝒱) D' f hf T k = 0 := by
  unfold mlSumCochain
  rw [dite_eq_right (fun ⟨p, hpT, hpk⟩ => hnot p hpT hpk)]

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] [T1Space X]
    [DecidableEq X] in
theorem mlSumCochain_empty {𝒱 : RS.Cech.FinCover (⊤ : Opens X)} (D' : RS.Divisor X)
    (f : RS.Mero X) (hf : f ∈ RS.LinSys D') :
    mlSumCochain (𝒱 := 𝒱) D' f hf (∅ : Finset X) = 0 := by
  funext k
  exact mlSumCochain_apply_of_not_mem D' f hf ∅ k (fun p hp => absurd hp (Finset.notMem_empty p))

/-! ### Pieces of `tailToH1_alpha`

The theorem is assembled from these lemmas rather than written as one proof: as a single
declaration it exceeded both the default heartbeat budget and the 200-line size we hold ourselves
to. `alphaFinset D f` / `alphaAuxD D f` are spelled out rather than generalized over, because the
proofs below use that definitional identity. -/

section AlphaPieces

variable (D : RS.Divisor X) (f : RS.Mero X) {𝒱 : RS.Cech.FinCover (⊤ : Opens X)}

/-- Distinct members of an adapted cover never meet on a marked point. -/
private theorem alpha_hoffdiag (h𝒱Adapted : 𝒱.IsAdapted (alphaFinset D f)) :
    ∀ k l : Fin 𝒱.n, k ≠ l → ∀ x ∈ (𝒱.U k ⊓ 𝒱.U l : Opens X), x ∉ alphaFinset D f := by
    intro k l hkl x hx hxS
    obtain ⟨m, -, hmuniq⟩ := h𝒱Adapted x hxS
    exact hkl ((hmuniq k hx.1).trans (hmuniq l hx.2).symm)

/-- A marked point's own member excludes every other marked point. -/
private theorem alpha_hexcl
    (hOclause : ∀ p ∈ alphaFinset D f, ∀ k, p ∈ 𝒱.U k →
      𝒱.U k ≤ alphaPatch D f (alphaFinset D f) p) :
    ∀ q ∈ alphaFinset D f, ∀ k, q ∈ 𝒱.U k → ∀ p ∈ alphaFinset D f, p ≠ q → p ∉ 𝒱.U k := by
    intro q hq k hqk p hp hpq hpk
    have hle := hOclause q hq k hqk
    have hpA : p ∈ alphaPatch D f (alphaFinset D f) q := hle hpk
    exact (alphaPatch_excl D f (alphaFinset D f) q p hpA) (Finset.mem_erase.mpr ⟨hpq, hp⟩)

variable (hfD' : f ∈ RS.LinSys (alphaAuxD D f))

/-- Order bound for the multi-point cochain away from the marked set. -/
private theorem alpha_hmember_ord :
    ∀ (T : Finset X) (k : Fin 𝒱.n) (x : X), x ∈ (𝒱.U k : Set X) → x ∉ alphaFinset D f →
      ((-(D x) : ℤ) : WithTop ℤ) ≤
        (mlSumCochain (𝒱 := 𝒱) (alphaAuxD D f) f hfD' T k :
          RS.MeroGermOn X (𝒱.U k : Set X)).ord x := by
    intro T k x hx hxS
    by_cases hex : ∃ q ∈ T, q ∈ 𝒱.U k
    · obtain ⟨q, hqT, hqk⟩ := hex
      rw [mlSumCochain_apply_of_mem (alphaAuxD D f) f hfD' T k hqT hqk]
      change ((-(D x) : ℤ) : WithTop ℤ) ≤
        (RS.MeroGermOn.restrict (Set.subset_univ _) f : RS.MeroGermOn X (𝒱.U k : Set X)).ord x
      rw [RS.MeroGermOn.ord_restrict (Set.subset_univ _) (𝒱.U k).isOpen isOpen_univ hx]
      exact not_mem_alphaFinset D f hxS
    · rw [mlSumCochain_apply_of_not_mem (alphaAuxD D f) f hfD' T k (fun q hqT hqk => hex ⟨q, hqT,
        hqk⟩)]
      change ((-(D x) : ℤ) : WithTop ℤ) ≤ (0 : RS.MeroGermOn X (𝒱.U k : Set X)).ord x
      rw [RS.MeroGermOn.ord_zero, ite_eq_left ⟨(𝒱.U k).isOpen, hx⟩]
      exact le_top

/-- The multi-point cochain has `D`-bounded coboundary, at any finite `T`. -/
private theorem alpha_hg_MemLD (h𝒱Adapted : 𝒱.IsAdapted (alphaFinset D f)) :
    ∀ T : Finset X, (RS.Cech.d0 (alphaAuxD D f) 𝒱
      (mlSumCochain (𝒱 := 𝒱) (alphaAuxD D f) f hfD' T)).MemLD D := by
    intro T
    rintro ⟨k, l⟩
    rcases eq_or_ne k l with rfl | hkl
    · rw [d0_diag_eq_zero]
      exact Submodule.zero_mem _
    · refine (RS.mem_linSysOn_iff_of_isOpen (𝒱.U k ⊓ 𝒱.U l).isOpen).2 fun x hx => ?_
      have hxS : x ∉ (alphaFinset D f) := alpha_hoffdiag D f h𝒱Adapted k l hkl x hx
      have hk := alpha_hmember_ord D f hfD' T k x hx.1 hxS
      have hl := alpha_hmember_ord D f hfD' T l x hx.2 hxS
      rw [RS.Cech.d0_apply]
      change ((-(D x) : ℤ) : WithTop ℤ) ≤
        ((LinSysOn.restrictL (alphaAuxD D f) (inf_le_right : (𝒱.U k ⊓ 𝒱.U l : Opens X) ≤ 𝒱.U l)
              (mlSumCochain (𝒱 := 𝒱) (alphaAuxD D f) f hfD' T l) -
            LinSysOn.restrictL (alphaAuxD D f) (inf_le_left : (𝒱.U k ⊓ 𝒱.U l : Opens X) ≤ 𝒱.U k)
              (mlSumCochain (𝒱 := 𝒱) (alphaAuxD D f) f hfD' T k) :
          RS.LinSysOn (alphaAuxD D f) (𝒱.U k ⊓ 𝒱.U l : Set X)) : RS.MeroGermOn X (𝒱.U k ⊓ 𝒱.U l :
              Set X)).ord x
      rw [Submodule.coe_sub, sub_eq_add_neg]
      refine le_trans ?_ (RS.MeroGermOn.ord_add (𝒱.U k ⊓ 𝒱.U l).isOpen hx _ _)
      rw [RS.MeroGermOn.ord_neg]
      have hkR :=
          RS.Cech.ord_restrictL (alphaAuxD D f) (inf_le_left : (𝒱.U k ⊓ 𝒱.U l : Opens X) ≤ 𝒱.U k) hx
        (mlSumCochain (𝒱 := 𝒱) (alphaAuxD D f) f hfD' T k)
      have hlR := RS.Cech.ord_restrictL (alphaAuxD D f)
          (inf_le_right : (𝒱.U k ⊓ 𝒱.U l : Opens X) ≤ 𝒱.U l) hx
        (mlSumCochain (𝒱 := 𝒱) (alphaAuxD D f) f hfD' T l)
      rw [hkR, hlR]
      exact le_min hl hk
  -- the global witness `f` realizes the FULL cochain `mlSumCochain (alphaAuxD D f) f hfD'
  -- (alphaFinset D f)` with vanishing

/-- A single marked point's `mlClassAt` equals the adapted cover's `mlClass` of the one-point
cochain. Split out of `tailToH1_alpha` for the heartbeat budget. -/
private theorem alpha_claim1 (h𝒱Adapted : 𝒱.IsAdapted (alphaFinset D f))
    (hOclause : ∀ p ∈ alphaFinset D f, ∀ k, p ∈ 𝒱.U k →
      𝒱.U k ≤ alphaPatch D f (alphaFinset D f) p) :
    ∀ p ∈ alphaFinset D f, mlClassAt D p (RS.MeroGermOn.restrict (Set.subset_univ _) f) =
      RS.Cech.mlClass 𝒱 (mlSumCochain (𝒱 := 𝒱) (alphaAuxD D f) f hfD' {p})
        (alpha_hg_MemLD D f hfD' h𝒱Adapted {p}) := by
  intro p hp
  set ψp : RS.MeroGermOn X (chartAt ℂ p).source :=
    RS.MeroGermOn.restrict (Set.subset_univ _) f with hψp_def
  set Vp : Opens X := alphaPatch D f (alphaFinset D f) p with hVp_def
  have hpVp : p ∈ Vp := mem_alphaPatch D f (alphaFinset D f) p
  have hVpsub : (Vp : Set X) ⊆ (chartAt ℂ p).source := alphaPatch_sub_source D f (alphaFinset D f) p
  have hVpclean := alphaPatch_clean D f (alphaFinset D f) p
  have hVpDzero := alphaPatch_D_eq_zero D f (alphaFinset D f) p
  set ψVp : RS.LinSysOn (alphaAuxD D f) (Vp : Set X) :=
    ⟨RS.MeroGermOn.restrict (Set.subset_univ (Vp : Set X)) f,
      restrict_mem_linSysOn_of_mem_linSys hfD' _ Vp.isOpen⟩ with hψVp_def
  have hψVp : (ψVp : RS.MeroGermOn X (Vp : Set X)) = RS.MeroGermOn.restrict hVpsub ψp := by
    change RS.MeroGermOn.restrict (Set.subset_univ (Vp : Set X)) f =
      RS.MeroGermOn.restrict hVpsub (RS.MeroGermOn.restrict (Set.subset_univ _) f)
    rw [RS.MeroGermOn.restrict_restrict]
  have key1 : mlClassAt D p ψp =
      mlClassAtOf p D (alphaAuxD D f) ψp Vp hpVp hVpsub hVpclean hVpDzero ψVp hψVp :=
    mlClassAt_eq_of_valid D p ψp hpVp hVpsub hVpclean hVpDzero ψVp hψVp
  rw [key1]
  unfold mlClassAtOf
  obtain ⟨kp, hkp_mem, hkp_uniq⟩ := h𝒱Adapted p hp
  set τp : Fin 𝒱.n → Fin 2 := fun k => if k = kp then 0 else 1 with hτp_def
  have hτp_zero_iff : ∀ k, τp k = 0 ↔ k = kp := by
    intro k
    simp only [hτp_def]
    split_ifs with hk <;> simp [hk]
  have hτp_one_iff : ∀ k, τp k = 1 ↔ k ≠ kp := by
    intro k
    simp only [hτp_def]
    split_ifs with hk <;> simp [hk]
  have hτp : RS.Cech.IsRefIdx (pairCover p Vp hpVp) 𝒱 τp := by
    intro k
    show 𝒱.U k ≤ (pairCover p Vp hpVp).U (τp k)
    by_cases hk : k = kp
    · rw [(hτp_zero_iff k).mpr hk, pairCover_U_zero, hk]
      exact hOclause p hp kp hkp_mem
    · rw [(hτp_one_iff k).mpr hk, pairCover_U_one]
      intro x hx
      change x ∈ ({p}ᶜ : Set X)
      intro hxp
      rw [Set.mem_singleton_iff] at hxp
      subst hxp
      exact hk (hkp_uniq k hx)
  -- a generic per-index computation of the refined cochain's value, avoiding a dependent
  -- rewrite on `τp k` by quantifying over the index and its refinement proof directly
  have gp_eq_at : ∀ (k : Fin 𝒱.n) (j : Fin 2) (hj : 𝒱.U k ≤ (pairCover p Vp hpVp).U j),
      (j = 0 → p ∈ 𝒱.U k) → (j = 1 → p ∉ 𝒱.U k) →
      (RS.MeroGermOn.restrict hj (gOf p Vp hpVp (alphaAuxD D f) ψVp j :
            RS.MeroGermOn X ((pairCover p Vp hpVp).U j : Set X)) :
          RS.MeroGermOn X (𝒱.U k : Set X)) =
        (mlSumCochain (𝒱 := 𝒱) (alphaAuxD D f) f hfD' {p} k : RS.MeroGermOn X (𝒱.U k : Set X)) := by
    rintro k j hj h0 h1
    fin_cases j
    · rw [mlSumCochain_apply_of_mem (alphaAuxD D f) f hfD' {p} k (Finset.mem_singleton_self p) (h0
        rfl)]
      change RS.MeroGermOn.restrict hj (gOf p Vp hpVp (alphaAuxD D f) ψVp (0 : Fin 2) :
        RS.MeroGermOn X ((pairCover p Vp hpVp).U (0 : Fin 2) : Set X)) = _
      rw [gOf_apply_zero]
      exact RS.MeroGermOn.restrict_restrict (Set.subset_univ (Vp : Set X)) hj f
    · rw [mlSumCochain_apply_of_not_mem (alphaAuxD D f) f hfD' {p} k (fun q hq hqk => by
        rw [Finset.mem_singleton] at hq
        exact (h1 rfl) (hq ▸ hqk))]
      change RS.MeroGermOn.restrict hj (gOf p Vp hpVp (alphaAuxD D f) ψVp (1 : Fin 2) :
        RS.MeroGermOn X ((pairCover p Vp hpVp).U (1 : Fin 2) : Set X)) = (0 : RS.MeroGermOn X _)
      rw [gOf_apply_one]
      exact map_zero _
  have hgp_eq : RS.Cech.resC0 (alphaAuxD D f) τp hτp (gOf p Vp hpVp (alphaAuxD D f) ψVp) =
      mlSumCochain (𝒱 := 𝒱) (alphaAuxD D f) f hfD' {p} := by
    funext k
    apply Subtype.ext
    rw [RS.Cech.resC0_apply, RS.Cech.restrictL_apply_coe]
    exact gp_eq_at k (τp k) (hτp k)
      (fun h => by rw [(hτp_zero_iff k).mp h]; exact hkp_mem)
      (fun h hpk => (hτp_one_iff k).mp h (hkp_uniq k hpk))
  rw [(mlClass_res τp hτp (gOf p Vp hpVp (alphaAuxD D f) ψVp)
    (gOf_memLD_of_clean p D (alphaAuxD D f) ψp Vp hpVp hVpsub hVpclean hVpDzero ψVp hψVp)
    (hgp_eq ▸ (alpha_hg_MemLD D f hfD' h𝒱Adapted) {p}))]
  exact mlClass_congr hgp_eq
-- the multi-point induction: combine the per-point classes over any `T ⊆ (alphaFinset D f)`

/-- The multi-point induction: the per-point classes sum to the cover's class of the multi-point
cochain, for any `T ⊆ alphaFinset D f`. Split out of `tailToH1_alpha` for the heartbeat budget. -/
private theorem alpha_main (h𝒱Adapted : 𝒱.IsAdapted (alphaFinset D f))
    (hOclause : ∀ p ∈ alphaFinset D f, ∀ k, p ∈ 𝒱.U k →
      𝒱.U k ≤ alphaPatch D f (alphaFinset D f) p) :
    ∀ T : Finset X, T ⊆ alphaFinset D f →
      ∑ q ∈ T, mlClassAt D q (RS.MeroGermOn.restrict (Set.subset_univ _) f) =
        RS.Cech.mlClass 𝒱 (mlSumCochain (𝒱 := 𝒱) (alphaAuxD D f) f hfD' T)
          (alpha_hg_MemLD D f hfD' h𝒱Adapted T) := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    rw [Finset.sum_empty, mlClass_congr (mlSumCochain_empty (𝒱 := 𝒱) (alphaAuxD D f) f hfD')]
    exact (mlClass_zero _).symm
  | insert p T' hpT' ih =>
    intro hsub
    have hpS : p ∈ (alphaFinset D f) := hsub (Finset.mem_insert_self p T')
    have hT'sub : T' ⊆ (alphaFinset D f) := (Finset.subset_insert p T').trans hsub
    have hsum_eq : mlSumCochain (𝒱 := 𝒱) (alphaAuxD D f) f hfD' {p} + mlSumCochain (𝒱 := 𝒱)
        (alphaAuxD D f) f hfD' T' =
        mlSumCochain (𝒱 := 𝒱) (alphaAuxD D f) f hfD' (insert p T') := by
      funext k
      by_cases hpk : p ∈ 𝒱.U k
      · rw [Pi.add_apply,
          mlSumCochain_apply_of_mem (alphaAuxD D f) f hfD' {p} k (Finset.mem_singleton_self p) hpk,
          mlSumCochain_apply_of_not_mem (alphaAuxD D f) f hfD' T' k (fun q hqT' hqk =>
            (alpha_hexcl D f hOclause) p hpS k hpk q (hT'sub hqT') (fun he => hpT' (he ▸ hqT'))
                hqk),
          mlSumCochain_apply_of_mem (alphaAuxD D f) f hfD' (insert p T') k
              (Finset.mem_insert_self p T') hpk]
        simp
      · by_cases hex' : ∃ q ∈ T', q ∈ 𝒱.U k
        · obtain ⟨q, hqT', hqk⟩ := hex'
          rw [Pi.add_apply, mlSumCochain_apply_of_not_mem (alphaAuxD D f) f hfD' {p} k (fun q' hq'
              hq'k => by
              rw [Finset.mem_singleton] at hq'; exact hpk (hq' ▸ hq'k)),
            mlSumCochain_apply_of_mem (alphaAuxD D f) f hfD' T' k hqT' hqk,
            mlSumCochain_apply_of_mem (alphaAuxD D f) f hfD' (insert p T') k
              (Finset.mem_insert_of_mem hqT') hqk]
          simp
        · rw [Pi.add_apply, mlSumCochain_apply_of_not_mem (alphaAuxD D f) f hfD' {p} k (fun q' hq'
            hq'k => by
              rw [Finset.mem_singleton] at hq'; exact hpk (hq' ▸ hq'k)),
            mlSumCochain_apply_of_not_mem (alphaAuxD D f) f hfD' T' k
                (fun q hqT' hqk => hex' ⟨q, hqT', hqk⟩),
            mlSumCochain_apply_of_not_mem (alphaAuxD D f) f hfD' (insert p T') k (fun q hq hqk => by
              rw [Finset.mem_insert] at hq
              rcases hq with rfl | hq
              · exact hpk hqk
              · exact hex' ⟨q, hq, hqk⟩)]
          simp
    rw [Finset.sum_insert hpT', ih hT'sub, (alpha_claim1 D f hfD' h𝒱Adapted hOclause) p hpS,
      ← RS.Cech.mlClass_add (mlSumCochain (𝒱 := 𝒱) (alphaAuxD D f) f hfD' {p})
        (mlSumCochain (𝒱 := 𝒱) (alphaAuxD D f) f hfD' T')
            ((alpha_hg_MemLD D f hfD' h𝒱Adapted) {p}) ((alpha_hg_MemLD D f hfD' h𝒱Adapted) T')
        (by rw [hsum_eq]; exact (alpha_hg_MemLD D f hfD' h𝒱Adapted) (insert p T'))]
    exact mlClass_congr hsum_eq

end AlphaPieces

/-! ### The main theorem -/

open scoped Classical in
theorem tailToH1_alpha (D : RS.Divisor X) (f : RS.Mero X) : tailToH1 D (alphaL D f) = 0 := by
  rw [alphaL_apply]
  rcases eq_or_ne f 0 with rfl | hf
  · have : alpha D (0 : RS.Mero X) = 0 := by
      have h0 := (alphaL D).map_zero
      rwa [alphaL_apply] at h0
    rw [this, map_zero]
  set S := alphaFinset D f with hS_def
  set D' := alphaAuxD D f with hD'_def
  have hfD' : f ∈ RS.LinSys D' := mem_linSys_alphaAuxD D hf
  obtain ⟨𝒱, -, h𝒱Adapted, hOclause⟩ := RS.Cech.exists_adapted_refinement
    (RS.Cech.FinCover.single (⊤ : Opens X)) S (fun p _ => trivial) (alphaPatch D f S)
    (fun p _ => mem_alphaPatch D f S p)
  -- off-diagonal overlaps of distinct members never meet `S` (pure adaptedness)
  have hoffdiag := alpha_hoffdiag D f h𝒱Adapted
  -- a marked point's own dedicated member excludes every other point of `S`
  have hexcl := alpha_hexcl D f hOclause
  -- the order of the multi-point cochain's value at any member, at any point outside `S`
  have hmember_ord := alpha_hmember_ord D f (𝒱 := 𝒱) hfD'
  -- `MemLD D` for the multi-point cochain, at ANY `T` (diagonal trivial; off-diagonal via
  -- `hoffdiag` + `hmember_ord`)
  have hg_MemLD := alpha_hg_MemLD D f hfD' h𝒱Adapted
  -- (indeed literally-zero-or-`D`-bounded) difference everywhere
  have hφ : ∀ k : Fin 𝒱.n, ∀ x ∈ (𝒱.U k : Set X),
      ((-(D x) : ℤ) : WithTop ℤ) ≤
        ((mlSumCochain (𝒱 := 𝒱) D' f hfD' S k : RS.MeroGermOn X (𝒱.U k : Set X)) -
          RS.MeroGermOn.restrict (𝒱.le_base k)
            ((⟨f, hfD'⟩ : RS.LinSys D') : RS.MeroGermOn X (Set.univ : Set X))).ord x := by
    intro k x hx
    by_cases hex : ∃ q ∈ S, q ∈ 𝒱.U k
    · obtain ⟨q, hqS, hqk⟩ := hex
      rw [mlSumCochain_apply_of_mem D' f hfD' S k hqS hqk]
      change ((-(D x) : ℤ) : WithTop ℤ) ≤
        ((RS.MeroGermOn.restrict (Set.subset_univ _) f : RS.MeroGermOn X (𝒱.U k : Set X)) -
          RS.MeroGermOn.restrict (𝒱.le_base k) f).ord x
      rw [sub_self, RS.MeroGermOn.ord_zero, ite_eq_left ⟨(𝒱.U k).isOpen, hx⟩]
      exact le_top
    · rw [mlSumCochain_apply_of_not_mem D' f hfD' S k (fun q hqS hqk => hex ⟨q, hqS, hqk⟩)]
      have hxS : x ∉ S := fun hxS => hex ⟨x, hxS, hx⟩
      change ((-(D x) : ℤ) : WithTop ℤ) ≤
        ((0 : RS.MeroGermOn X (𝒱.U k : Set X)) - RS.MeroGermOn.restrict (𝒱.le_base k) f).ord x
      rw [zero_sub, RS.MeroGermOn.ord_neg,
        RS.MeroGermOn.ord_restrict (𝒱.le_base k) (𝒱.U k).isOpen isOpen_univ hx]
      exact not_mem_alphaFinset D f hxS
  have hzero : RS.Cech.mlClass 𝒱 (mlSumCochain (𝒱 := 𝒱) D' f hfD' S) (hg_MemLD S) = 0 :=
    RS.Cech.mlClass_eq_zero_of_exists (mlSumCochain (𝒱 := 𝒱) D' f hfD' S) (hg_MemLD S)
      (⟨f, hfD'⟩ : RS.LinSys D') hφ
  -- CLAIM1: a single marked point's `mlClassAt` equals the big cover's `mlClass` restricted to
  -- the single-point cochain `mlSumCochain D' f hfD' {p}`
  have CLAIM1 := alpha_claim1 D f hfD' h𝒱Adapted hOclause
  have main := alpha_main D f hfD' h𝒱Adapted hOclause
  have hsum0 : ∑ q ∈ S, mlClassAt D q (RS.MeroGermOn.restrict (Set.subset_univ _) f) = 0 :=
    (main S (Finset.Subset.refl S)).trans hzero
  -- assemble: `tailToH1 D (alpha D f)` unfolds to exactly this sum
  have hsupp : (alpha D f).support ⊆ S := by
    intro q hq
    by_contra hqS
    exact (DFinsupp.mem_support_iff.mp hq)
      ((alpha_apply_eq_zero_iff D f q).2 (not_mem_alphaFinset D f hqS))
  have hlsum : tailToH1 D (alpha D f) = ∑ q ∈ S, tailAtToH1 D q (alpha D f q) := by
    rw [tailToH1, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply]
    unfold DFinsupp.sum
    apply Finset.sum_subset hsupp
    intro q _ hq
    rw [DFinsupp.mem_support_iff, not_not] at hq
    simp [hq]
  rw [hlsum]
  rw [show (∑ q ∈ S, tailAtToH1 D q (alpha D f q)) =
      ∑ q ∈ S, mlClassAt D q (RS.MeroGermOn.restrict (Set.subset_univ _) f) from
    Finset.sum_congr rfl (fun q _ => by rw [alpha_apply, tailAtToH1_mk])]
  exact hsum0

/-! ### `H1Tail.toH1` -/

/-- The induced map from the tail quotient to `H¹(D)`. -/
noncomputable def H1Tail.toH1 (D : RS.Divisor X) : H1Tail D →ₗ[ℂ] RS.Cech.H1 D :=
  Submodule.liftQ (LinearMap.range (alphaL D)) (tailToH1 D) (by
    intro z hz
    obtain ⟨f, rfl⟩ := hz
    exact tailToH1_alpha D f)

theorem H1Tail.toH1_mk (D : RS.Divisor X) (z : T D) :
    H1Tail.toH1 D (H1Tail.mk D z) = tailToH1 D z :=
  Submodule.liftQ_apply _ _ z

/-! ### Injectivity: helper constructions, factored to top-level declarations for elaboration
speed (a single giant tactic proof accumulating ~25 `have`s/`set`s hits a severe performance wall:
confirmed by direct experiment, `set_option maxHeartbeats 20000000` still did not finish in
10 minutes of wall-clock time). Each piece below is proved against only the section variables it
actually needs, mirroring `tailToH1_alpha`'s own successful top-level-helper structure. -/

variable (ψ : ∀ p : X, RS.MeroGermOn X (chartAt ℂ p).source) (S : Finset X)

/-- The clean patch at a marked point `p`, avoiding the other points of `S` (generalizes
`alphaPatch` to an arbitrary per-point representative `ψ`, not tied to one global function). -/
noncomputable def injPatch (D : RS.Divisor X) (p : X) : Opens X :=
  cleanNbhd D p (ψ p) ⊓ RS.Cech.compOpens (S.erase p)

omit [ConnectedSpace X] in
theorem mem_injPatch (D : RS.Divisor X) (p : X) : p ∈ injPatch ψ S D p :=
  ⟨mem_cleanNbhd D p (ψ p), RS.Cech.mem_compOpens.mpr (Finset.notMem_erase p S)⟩

omit [ConnectedSpace X] in
theorem injPatch_sub (D : RS.Divisor X) (p : X) : (injPatch ψ S D p : Set X) ⊆
    (chartAt ℂ p).source :=
  fun _x hx => cleanNbhd_sub_source D p (ψ p) hx.1

omit [ConnectedSpace X] in
theorem injPatch_excl (D : RS.Divisor X) (p : X) :
    ∀ x ∈ (injPatch ψ S D p : Set X), x ∉ S.erase p :=
  fun _x hx => RS.Cech.mem_compOpens.mp hx.2

variable (D : RS.Divisor X)

/-- A single auxiliary divisor dominating `DPrimeOf` at every point of `S`. -/
noncomputable def injD' (hSne : S.Nonempty) : RS.Divisor X :=
  S.sup' hSne (fun p => DPrimeOf D p (ψ p))

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] [T1Space X] in
theorem injD'_mem (hSne : S.Nonempty) : ∀ p ∈ S, DPrimeOf D p (ψ p) ≤ injD' ψ S D hSne :=
  fun _p hp => Finset.le_sup' (fun p => DPrimeOf D p (ψ p)) hp

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] [T1Space X] in
theorem injD'_ge (hSne : S.Nonempty) : D ≤ injD' ψ S D hSne :=
  le_trans (D_le_DPrimeOf D hSne.choose (ψ hSne.choose))
    (injD'_mem ψ S D hSne hSne.choose hSne.choose_spec)

variable (D' : RS.Divisor X) (hD'mem : ∀ p ∈ S, DPrimeOf D p (ψ p) ≤ D')

/-- The `D'`-typed representative at each marked point, restricted to its own patch. -/
noncomputable def injψVD' (p : X) (hp : p ∈ S) : RS.LinSysOn D' (injPatch ψ S D p : Set X) :=
  RS.Cech.LinSysOn.restrictL D' (inf_le_left : injPatch ψ S D p ≤ cleanNbhd D p (ψ p))
    (Submodule.inclusion (RS.Cech.linSysOn_mono (hD'mem p hp)) (ψVOf D p (ψ p)))

omit [ConnectedSpace X] in
theorem injψVD'_eq (p : X) (hp : p ∈ S) :
    (injψVD' ψ S D D' hD'mem p hp : RS.MeroGermOn X (injPatch ψ S D p : Set X)) =
      RS.MeroGermOn.restrict (injPatch_sub ψ S D p) (ψ p) := by
  unfold injψVD'
  rw [RS.Cech.restrictL_apply_coe, Submodule.coe_inclusion]
  exact RS.MeroGermOn.restrict_restrict (cleanNbhd_sub_source D p (ψ p))
    (inf_le_left : injPatch ψ S D p ≤ cleanNbhd D p (ψ p)) (ψ p)

variable {𝒱 : RS.Cech.FinCover (⊤ : Opens X)} (h𝒱Adapted : 𝒱.IsAdapted S)
  (hOclause : ∀ p ∈ S, ∀ k, p ∈ 𝒱.U k → 𝒱.U k ≤ injPatch ψ S D p)

include ψ S D D' h𝒱Adapted in
omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace X] [ConnectedSpace X] [T1Space X]
    [DecidableEq X] ψ D D' [ChartedSpace ℂ X] in
theorem inj_hoffdiag : ∀ k l : Fin 𝒱.n, k ≠ l → ∀ x ∈ (𝒱.U k ⊓ 𝒱.U l : Opens X), x ∉ S := by
  intro k l hkl x hx hxS
  obtain ⟨m, -, hmuniq⟩ := h𝒱Adapted x hxS
  exact hkl ((hmuniq k hx.1).trans (hmuniq l hx.2).symm)

include ψ S D D' hOclause in
omit [ConnectedSpace X] D' in
theorem inj_hexcl : ∀ q ∈ S, ∀ k, q ∈ 𝒱.U k → ∀ p ∈ S, p ≠ q → p ∉ 𝒱.U k := by
  intro q hq k hqk p hp hpq hpk
  have hle := hOclause q hq k hqk
  exact (injPatch_excl ψ S D q p (hle hpk)) (Finset.mem_erase.mpr ⟨hpq, hp⟩)

include ψ S D hOclause in
omit [ConnectedSpace X] in
theorem inj_hunique_S : ∀ p ∈ S, ∀ q ∈ S, ∀ k, p ∈ 𝒱.U k → q ∈ 𝒱.U k → p = q := by
  intro p hp q hq k hpk hqk
  by_contra hne
  exact inj_hexcl ψ S D hOclause q hq k hqk p hp hne hpk

open scoped Classical in
include ψ S D D' hD'mem h𝒱Adapted hOclause in
/-- The multi-point cochain, restricted to the marked points of `T` (intersected with `S`). -/
noncomputable def injG (T : Finset X) : RS.Cech.C0 D' 𝒱 :=
  fun k => if h : ∃ p ∈ T ∩ S, p ∈ 𝒱.U k then
      RS.Cech.LinSysOn.restrictL D'
        (hOclause h.choose (Finset.mem_of_mem_inter_right h.choose_spec.1) k h.choose_spec.2)
        (injψVD' ψ S D D' hD'mem h.choose (Finset.mem_of_mem_inter_right h.choose_spec.1))
    else 0

open scoped Classical in
include ψ S D D' hD'mem h𝒱Adapted hOclause in
omit [ConnectedSpace X] h𝒱Adapted in
theorem injG_apply_of_mem (T : Finset X) (k : Fin 𝒱.n) (p : X) (hpT : p ∈ T) (hpS : p ∈ S)
    (hpk : p ∈ 𝒱.U k) : injG ψ S D D' hD'mem hOclause T k =
      RS.Cech.LinSysOn.restrictL D' (hOclause p hpS k hpk) (injψVD' ψ S D D' hD'mem p hpS) := by
  have hex : ∃ q ∈ T ∩ S, q ∈ 𝒱.U k := ⟨p, Finset.mem_inter.mpr ⟨hpT, hpS⟩, hpk⟩
  have gen : ∀ (q : X) (hqTS : q ∈ T ∩ S) (hqk : q ∈ 𝒱.U k), q = p →
      RS.Cech.LinSysOn.restrictL D' (hOclause q (Finset.mem_of_mem_inter_right hqTS) k hqk)
        (injψVD' ψ S D D' hD'mem q (Finset.mem_of_mem_inter_right hqTS)) =
      RS.Cech.LinSysOn.restrictL D' (hOclause p hpS k hpk) (injψVD' ψ S D D' hD'mem p hpS) := by
    rintro q hqTS hqk rfl
    rfl
  change (if h : ∃ p ∈ T ∩ S, p ∈ 𝒱.U k then _ else _) = _
  rw [dite_eq_left hex]
  exact gen hex.choose hex.choose_spec.1 hex.choose_spec.2
    (inj_hunique_S ψ S D hOclause hex.choose
      (Finset.mem_of_mem_inter_right hex.choose_spec.1) p hpS k hex.choose_spec.2 hpk)

open scoped Classical in
include ψ S D D' hD'mem hOclause in
omit [ConnectedSpace X] in
theorem injG_apply_of_not_mem (T : Finset X) (k : Fin 𝒱.n) (hnot : ∀ p ∈ T, p ∈ S → p ∉ 𝒱.U k) :
    injG ψ S D D' hD'mem hOclause T k = 0 := by
  change (if h : ∃ p ∈ T ∩ S, p ∈ 𝒱.U k then _ else _) = _
  rw [dite_eq_right]
  rintro ⟨q, hqTS, hqk⟩
  exact hnot q (Finset.mem_of_mem_inter_left hqTS) (Finset.mem_of_mem_inter_right hqTS) hqk

include ψ S D D' hD'mem h𝒱Adapted hOclause in
omit [ConnectedSpace X] h𝒱Adapted in
theorem inj_hmember_ord (T : Finset X) (k : Fin 𝒱.n) (x : X) (hx : x ∈ (𝒱.U k : Set X))
    (hxS : x ∉ S) : ((-(D x) : ℤ) : WithTop ℤ) ≤
      (injG ψ S D D' hD'mem hOclause T k : RS.MeroGermOn X (𝒱.U k : Set X)).ord x := by
  by_cases hex : ∃ p ∈ T ∩ S, p ∈ 𝒱.U k
  · obtain ⟨p, hpTS, hpk⟩ := hex
    have hpT := Finset.mem_of_mem_inter_left hpTS
    have hpS := Finset.mem_of_mem_inter_right hpTS
    rw [injG_apply_of_mem ψ S D D' hD'mem hOclause T k p hpT hpS hpk]
    have hxp : x ≠ p := fun he => hxS (he ▸ hpS)
    have hxPatch : x ∈ (injPatch ψ S D p : Set X) := hOclause p hpS k hpk hx
    change ((-(D x) : ℤ) : WithTop ℤ) ≤
      (RS.Cech.LinSysOn.restrictL D' (hOclause p hpS k hpk) (injψVD' ψ S D D' hD'mem p hpS) :
        RS.MeroGermOn X (𝒱.U k : Set X)).ord x
    rw [RS.Cech.ord_restrictL D' (hOclause p hpS k hpk) hx (injψVD' ψ S D D' hD'mem p hpS),
      injψVD'_eq ψ S D D' hD'mem p hpS,
      RS.MeroGermOn.ord_restrict (fun y hy => injPatch_sub ψ S D p hy) (injPatch ψ S D p).isOpen
        (chartAt ℂ p).open_source hxPatch]
    rw [cleanNbhd_D_eq_zero D p (ψ p) x hxPatch.1 hxp]
    simpa using cleanNbhd_ord_nonneg D p (ψ p) x hxPatch.1 hxp
  · rw [injG_apply_of_not_mem ψ S D D' hD'mem hOclause T k
      (fun p hpT hpS hpk => hex ⟨p, Finset.mem_inter.mpr ⟨hpT, hpS⟩, hpk⟩)]
    change ((-(D x) : ℤ) : WithTop ℤ) ≤ (0 : RS.MeroGermOn X (𝒱.U k : Set X)).ord x
    rw [RS.MeroGermOn.ord_zero, ite_eq_left ⟨(𝒱.U k).isOpen, hx⟩]
    exact le_top

include ψ S D D' hD'mem h𝒱Adapted hOclause in
omit [ConnectedSpace X] in
theorem inj_hg_MemLD (T : Finset X) : (RS.Cech.d0 D' 𝒱 (injG ψ S D D' hD'mem hOclause T)).MemLD D :=
    by
  rintro ⟨k, l⟩
  rcases eq_or_ne k l with rfl | hkl
  · rw [d0_diag_eq_zero]
    exact Submodule.zero_mem _
  · refine (RS.mem_linSysOn_iff_of_isOpen (𝒱.U k ⊓ 𝒱.U l).isOpen).2 fun x hx => ?_
    have hxS : x ∉ S := inj_hoffdiag S h𝒱Adapted k l hkl x hx
    have hk := inj_hmember_ord ψ S D D' hD'mem hOclause T k x hx.1 hxS
    have hl := inj_hmember_ord ψ S D D' hD'mem hOclause T l x hx.2 hxS
    rw [RS.Cech.d0_apply]
    change ((-(D x) : ℤ) : WithTop ℤ) ≤
      ((LinSysOn.restrictL D' (inf_le_right : (𝒱.U k ⊓ 𝒱.U l : Opens X) ≤ 𝒱.U l)
            (injG ψ S D D' hD'mem hOclause T l) -
          LinSysOn.restrictL D' (inf_le_left : (𝒱.U k ⊓ 𝒱.U l : Opens X) ≤ 𝒱.U k)
            (injG ψ S D D' hD'mem hOclause T k) :
        RS.LinSysOn D' (𝒱.U k ⊓ 𝒱.U l : Set X)) : RS.MeroGermOn X (𝒱.U k ⊓ 𝒱.U l : Set X)).ord x
    rw [Submodule.coe_sub, sub_eq_add_neg]
    refine le_trans ?_ (RS.MeroGermOn.ord_add (𝒱.U k ⊓ 𝒱.U l).isOpen hx _ _)
    rw [RS.MeroGermOn.ord_neg]
    have hkR := RS.Cech.ord_restrictL D' (inf_le_left : (𝒱.U k ⊓ 𝒱.U l : Opens X) ≤ 𝒱.U k) hx
      (injG ψ S D D' hD'mem hOclause T k)
    have hlR := RS.Cech.ord_restrictL D' (inf_le_right : (𝒱.U k ⊓ 𝒱.U l : Opens X) ≤ 𝒱.U l) hx
      (injG ψ S D D' hD'mem hOclause T l)
    rw [hkR, hlR]
    exact le_min hl hk

include ψ S D D' hD'mem h𝒱Adapted hOclause in
omit [ConnectedSpace X] in
/-- CLAIM1-analogue: a single marked point's `mlClassAt` equals the big cover's `mlClass` of the
one-point cochain `injG {p}`. -/
theorem inj_CLAIM1 (p : X) (hp : p ∈ S) : mlClassAt D p (ψ p) =
    RS.Cech.mlClass 𝒱 (injG ψ S D D' hD'mem hOclause {p})
        (inj_hg_MemLD ψ S D D' hD'mem h𝒱Adapted hOclause {p}) := by
  have key1 : mlClassAt D p (ψ p) =
      mlClassAtOf p D D' (ψ p) (injPatch ψ S D p) (mem_injPatch ψ S D p) (injPatch_sub ψ S D p)
        (fun x hx hxp => cleanNbhd_ord_nonneg D p (ψ p) x hx.1 hxp)
        (fun x hx hxp => cleanNbhd_D_eq_zero D p (ψ p) x hx.1 hxp)
        (injψVD' ψ S D D' hD'mem p hp) (injψVD'_eq ψ S D D' hD'mem p hp) :=
    mlClassAt_eq_of_valid D p (ψ p) (mem_injPatch ψ S D p) (injPatch_sub ψ S D p) _ _
      (injψVD' ψ S D D' hD'mem p hp) (injψVD'_eq ψ S D D' hD'mem p hp)
  rw [key1]
  unfold mlClassAtOf
  obtain ⟨kp, hkp_mem, hkp_uniq⟩ := h𝒱Adapted p hp
  set τp : Fin 𝒱.n → Fin 2 := fun k => if k = kp then 0 else 1 with hτp_def
  have hτp_zero_iff : ∀ k, τp k = 0 ↔ k = kp := by
    intro k; simp only [hτp_def]; split_ifs with hk <;> simp [hk]
  have hτp_one_iff : ∀ k, τp k = 1 ↔ k ≠ kp := by
    intro k; simp only [hτp_def]; split_ifs with hk <;> simp [hk]
  have hτp : RS.Cech.IsRefIdx (pairCover p (injPatch ψ S D p) (mem_injPatch ψ S D p)) 𝒱 τp := by
    intro k
    show 𝒱.U k ≤ (pairCover p (injPatch ψ S D p) (mem_injPatch ψ S D p)).U (τp k)
    by_cases hk : k = kp
    · rw [(hτp_zero_iff k).mpr hk, pairCover_U_zero, hk]
      exact hOclause p hp kp hkp_mem
    · rw [(hτp_one_iff k).mpr hk, pairCover_U_one]
      intro x hx
      change x ∈ ({p}ᶜ : Set X)
      intro hxp
      rw [Set.mem_singleton_iff] at hxp
      subst hxp
      exact hk (hkp_uniq k hx)
  have gp_eq_at : ∀ (k : Fin 𝒱.n) (j : Fin 2)
      (hj : 𝒱.U k ≤ (pairCover p (injPatch ψ S D p) (mem_injPatch ψ S D p)).U j),
      (j = 0 → p ∈ 𝒱.U k) → (j = 1 → p ∉ 𝒱.U k) →
      (RS.MeroGermOn.restrict hj
          (gOf p (injPatch ψ S D p) (mem_injPatch ψ S D p) D' (injψVD' ψ S D D' hD'mem p hp) j :
            RS.MeroGermOn X
              ((pairCover p (injPatch ψ S D p) (mem_injPatch ψ S D p)).U j : Set X)) :
          RS.MeroGermOn X (𝒱.U k : Set X)) =
        (injG ψ S D D' hD'mem hOclause {p} k : RS.MeroGermOn X (𝒱.U k : Set X)) := by
    rintro k j hj h0 h1
    fin_cases j
    · rw [injG_apply_of_mem ψ S D D' hD'mem hOclause {p} k p
        (Finset.mem_singleton_self p) hp (h0 rfl)]
      change RS.MeroGermOn.restrict hj
        (gOf p (injPatch ψ S D p) (mem_injPatch ψ S D p) D' (injψVD' ψ S D D' hD'mem p hp)
          (0 : Fin 2) :
          RS.MeroGermOn X ((pairCover p (injPatch ψ S D p) (mem_injPatch ψ S D p)).U (0 : Fin 2) :
            Set X)) =
        (RS.Cech.LinSysOn.restrictL D' (hOclause p hp k (h0 rfl))
          (injψVD' ψ S D D' hD'mem p hp) : RS.MeroGermOn X (𝒱.U k : Set X))
      rw [gOf_apply_zero, RS.Cech.restrictL_apply_coe]
      rfl
    · rw [injG_apply_of_not_mem ψ S D D' hD'mem hOclause {p} k (fun q hq _ hqk => by
        rw [Finset.mem_singleton] at hq
        exact (h1 rfl) (hq ▸ hqk))]
      change RS.MeroGermOn.restrict hj
        (gOf p (injPatch ψ S D p) (mem_injPatch ψ S D p) D' (injψVD' ψ S D D' hD'mem p hp)
          (1 : Fin 2) :
          RS.MeroGermOn X ((pairCover p (injPatch ψ S D p) (mem_injPatch ψ S D p)).U (1 : Fin 2) :
            Set X)) =
        (0 : RS.MeroGermOn X (𝒱.U k : Set X))
      rw [gOf_apply_one]
      exact map_zero _
  have hgp_eq : RS.Cech.resC0 D' τp hτp
      (gOf p (injPatch ψ S D p) (mem_injPatch ψ S D p) D' (injψVD' ψ S D D' hD'mem p hp)) =
      injG ψ S D D' hD'mem hOclause {p} := by
    funext k
    apply Subtype.ext
    rw [RS.Cech.resC0_apply, RS.Cech.restrictL_apply_coe]
    exact gp_eq_at k (τp k) (hτp k)
      (fun h => by rw [(hτp_zero_iff k).mp h]; exact hkp_mem)
      (fun h hpk => (hτp_one_iff k).mp h (hkp_uniq k hpk))
  rw [(mlClass_res τp hτp
      (gOf p (injPatch ψ S D p) (mem_injPatch ψ S D p) D' (injψVD' ψ S D D' hD'mem p hp))
      (gOf_memLD_of_clean p D D' (ψ p) (injPatch ψ S D p) (mem_injPatch ψ S D p)
        (injPatch_sub ψ S D p) (fun x hx hxp => cleanNbhd_ord_nonneg D p (ψ p) x hx.1 hxp)
        (fun x hx hxp => cleanNbhd_D_eq_zero D p (ψ p) x hx.1 hxp)
        (injψVD' ψ S D D' hD'mem p hp) (injψVD'_eq ψ S D D' hD'mem p hp))
      (hgp_eq ▸ inj_hg_MemLD ψ S D D' hD'mem h𝒱Adapted hOclause {p}))]
  exact mlClass_congr hgp_eq

include ψ S D D' hD'mem h𝒱Adapted hOclause in
omit [ConnectedSpace X] in
/-- The multi-point induction: sum of individual `mlClassAt`s over any `T ⊆ S` equals the big
cover's `mlClass` of `injG T`. -/
theorem inj_main : ∀ T : Finset X, T ⊆ S →
    ∑ q ∈ T, mlClassAt D q (ψ q) =
      RS.Cech.mlClass 𝒱 (injG ψ S D D' hD'mem hOclause T)
        (inj_hg_MemLD ψ S D D' hD'mem h𝒱Adapted hOclause T) := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    have hgemp : injG ψ S D D' hD'mem hOclause ∅ = 0 := by
      funext k
      exact injG_apply_of_not_mem ψ S D D' hD'mem hOclause ∅ k
        (fun p hp => absurd hp (Finset.notMem_empty p))
    rw [Finset.sum_empty, mlClass_congr hgemp]
    exact (mlClass_zero _).symm
  | insert p T' hpT' ih =>
    intro hsub
    have hpS : p ∈ S := hsub (Finset.mem_insert_self p T')
    have hT'sub : T' ⊆ S := (Finset.subset_insert p T').trans hsub
    have hsum_eq : injG ψ S D D' hD'mem hOclause {p} + injG ψ S D D' hD'mem hOclause T' =
        injG ψ S D D' hD'mem hOclause (insert p T') := by
      funext k
      by_cases hpk : p ∈ 𝒱.U k
      · rw [Pi.add_apply,
          injG_apply_of_mem ψ S D D' hD'mem hOclause {p} k p
            (Finset.mem_singleton_self p) hpS hpk,
          injG_apply_of_not_mem ψ S D D' hD'mem hOclause T' k (fun q hqT' hqS hqk =>
            inj_hexcl ψ S D hOclause p hpS k hpk q hqS (fun he => hpT' (he ▸ hqT')) hqk),
          injG_apply_of_mem ψ S D D' hD'mem hOclause (insert p T') k p
            (Finset.mem_insert_self p T') hpS hpk]
        simp
      · by_cases hex' : ∃ q ∈ T' ∩ S, q ∈ 𝒱.U k
        · obtain ⟨q, hqTS, hqk⟩ := hex'
          have hqT' := Finset.mem_of_mem_inter_left hqTS
          have hqS := Finset.mem_of_mem_inter_right hqTS
          rw [Pi.add_apply,
            injG_apply_of_not_mem ψ S D D' hD'mem hOclause {p} k (fun q' hq' hq'S hq'k => by
              rw [Finset.mem_singleton] at hq'; exact hpk (hq' ▸ hq'k)),
            injG_apply_of_mem ψ S D D' hD'mem hOclause T' k q hqT' hqS hqk,
            injG_apply_of_mem ψ S D D' hD'mem hOclause (insert p T') k q
              (Finset.mem_insert_of_mem hqT') hqS hqk]
          simp
        · rw [Pi.add_apply,
            injG_apply_of_not_mem ψ S D D' hD'mem hOclause {p} k (fun q' hq' hq'S hq'k => by
              rw [Finset.mem_singleton] at hq'; exact hpk (hq' ▸ hq'k)),
            injG_apply_of_not_mem ψ S D D' hD'mem hOclause T' k (fun q hqT' hqS hqk =>
              hex' ⟨q, Finset.mem_inter.mpr ⟨hqT', hqS⟩, hqk⟩),
            injG_apply_of_not_mem ψ S D D' hD'mem hOclause (insert p T') k
              (fun q hq hqS hqk => by
                rw [Finset.mem_insert] at hq
                rcases hq with rfl | hq
                · exact hpk hqk
                · exact hex' ⟨q, Finset.mem_inter.mpr ⟨hq, hqS⟩, hqk⟩)]
          simp
    rw [Finset.sum_insert hpT', ih hT'sub, inj_CLAIM1 ψ S D D' hD'mem h𝒱Adapted hOclause p hpS,
      ← RS.Cech.mlClass_add (injG ψ S D D' hD'mem hOclause {p}) (injG ψ S D D' hD'mem hOclause T')
        (inj_hg_MemLD ψ S D D' hD'mem h𝒱Adapted hOclause {p})
        (inj_hg_MemLD ψ S D D' hD'mem h𝒱Adapted hOclause T')
        (by rw [hsum_eq]; exact inj_hg_MemLD ψ S D D' hD'mem h𝒱Adapted hOclause (insert p T'))]
    exact mlClass_congr hsum_eq

include ψ S D D' hD'mem hOclause in
omit [ConnectedSpace X] in
/-- The coboundary/order identity used to read `φ`'s bound back into `ψ q`'s tail data. -/
theorem inj_hcoe (φ : RS.LinSys D') (q : X) (hq : q ∈ S) (k : Fin 𝒱.n) (hqk : q ∈ 𝒱.U k) (x : X)
    (hx : x ∈ (𝒱.U k : Set X)) :
    (RS.Cech.LinSysOn.restrictL D' (hOclause q hq k hqk) (injψVD' ψ S D D' hD'mem q hq) -
        RS.MeroGermOn.restrict (𝒱.le_base k) (φ : RS.MeroGermOn X (Set.univ : Set X)) :
      RS.MeroGermOn X (𝒱.U k : Set X)).ord x =
    (ψ q - RS.MeroGermOn.restrict (Set.subset_univ (chartAt ℂ q).source)
      (φ : RS.MeroGermOn X (Set.univ : Set X))).ord x := by
  have hqk' : (𝒱.U k : Set X) ⊆ (injPatch ψ S D q : Set X) := hOclause q hq k hqk
  have hqk'' : (𝒱.U k : Set X) ⊆ (chartAt ℂ q).source := hqk'.trans (injPatch_sub ψ S D q)
  have heq : (RS.Cech.LinSysOn.restrictL D' (hOclause q hq k hqk) (injψVD' ψ S D D' hD'mem q hq) -
      RS.MeroGermOn.restrict (𝒱.le_base k) (φ : RS.MeroGermOn X (Set.univ : Set X)) :
      RS.MeroGermOn X (𝒱.U k : Set X)) =
    RS.MeroGermOn.restrict hqk''
      (ψ q - RS.MeroGermOn.restrict (Set.subset_univ (chartAt ℂ q).source)
        (φ : RS.MeroGermOn X (Set.univ : Set X))) := by
    rw [map_sub, RS.Cech.restrictL_apply_coe, injψVD'_eq ψ S D D' hD'mem q hq,
      RS.MeroGermOn.restrict_restrict]
    congr 1
    exact RS.MeroGermOn.restrict_restrict _ _ (ψ q)
  rw [heq, RS.MeroGermOn.ord_restrict hqk'' (𝒱.U k).isOpen (chartAt ℂ q).open_source hx]

open scoped Classical in
theorem H1Tail.toH1_injective (D : RS.Divisor X) : Function.Injective (H1Tail.toH1 D) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro ξ hξ
  obtain ⟨z, rfl⟩ := H1Tail.mk_surjective D ξ
  rw [LinearMap.mem_ker, H1Tail.toH1_mk] at hξ
  rw [H1Tail.mk_eq_zero_iff]
  rcases z.support.eq_empty_or_nonempty with hSemp | hSne
  · exact ⟨0, by rw [map_zero]; exact (DFinsupp.support_eq_empty.mp hSemp).symm⟩
  choose ψ hψ using fun p => TailAt.mk_surjective p D (z p)
  set S := z.support with hS_def
  set D' := injD' ψ S D hSne with hD'_def
  have hD'mem : ∀ p ∈ S, DPrimeOf D p (ψ p) ≤ D' := injD'_mem ψ S D hSne
  have hDD' : D ≤ D' := injD'_ge ψ S D hSne
  obtain ⟨𝒱, -, h𝒱Adapted, hOclause⟩ := RS.Cech.exists_adapted_refinement
    (RS.Cech.FinCover.single (⊤ : Opens X)) S (fun p _ => trivial) (injPatch ψ S D)
    (fun p _ => mem_injPatch ψ S D p)
  have hsum0 : ∑ q ∈ S, mlClassAt D q (ψ q) =
      RS.Cech.mlClass 𝒱 (injG ψ S D D' hD'mem hOclause S)
        (inj_hg_MemLD ψ S D D' hD'mem h𝒱Adapted hOclause S) :=
    inj_main ψ S D D' hD'mem h𝒱Adapted hOclause S (Finset.Subset.refl S)
  have hclass0 : RS.Cech.mlClass 𝒱 (injG ψ S D D' hD'mem hOclause S)
      (inj_hg_MemLD ψ S D D' hD'mem h𝒱Adapted hOclause S) = 0 := by
    have hlsum : tailToH1 D z = ∑ q ∈ S, tailAtToH1 D q (z q) := by
      rw [tailToH1, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply]
      unfold DFinsupp.sum
      rfl
    rw [hlsum] at hξ
    rw [show (∑ q ∈ S, tailAtToH1 D q (z q)) = ∑ q ∈ S, mlClassAt D q (ψ q) from
      Finset.sum_congr rfl (fun q _ => by rw [← hψ q, tailAtToH1_mk])] at hξ
    rw [← hsum0]
    exact hξ
  obtain ⟨φ, hφ⟩ := (RS.Cech.mlClass_eq_zero_iff hDD' (injG ψ S D D' hD'mem hOclause S)
    (inj_hg_MemLD ψ S D D' hD'mem h𝒱Adapted hOclause S)).1 hclass0
  refine ⟨(φ : RS.Mero X), ?_⟩
  apply DFinsupp.ext
  intro p
  rw [alphaL_apply]
  by_cases hp : p ∈ S
  · obtain ⟨kp, hkp_mem, -⟩ := h𝒱Adapted p hp
    have hφp := hφ kp p hkp_mem
    rw [injG_apply_of_mem ψ S D D' hD'mem hOclause S kp p hp hp hkp_mem,
      inj_hcoe ψ S D D' hD'mem hOclause φ p hp kp hkp_mem p hkp_mem] at hφp
    rw [alpha_apply, ← hψ p, ← sub_eq_zero, ← map_sub, TailAt.mk_eq_zero_iff,
      show RS.MeroGermOn.restrict (Set.subset_univ (chartAt ℂ p).source)
          (φ : RS.MeroGermOn X (Set.univ : Set X)) - ψ p =
        -(ψ p - RS.MeroGermOn.restrict (Set.subset_univ (chartAt ℂ p).source)
          (φ : RS.MeroGermOn X (Set.univ : Set X))) from by ring,
      RS.MeroGermOn.ord_neg]
    exact hφp
  · have hz0 : z p = 0 := DFinsupp.notMem_support_iff.mp hp
    rw [alpha_apply, hz0, TailAt.mk_eq_zero_iff]
    obtain ⟨k, hk⟩ := 𝒱.covers p trivial
    by_cases hex : ∃ q ∈ S, q ∈ 𝒱.U k
    · obtain ⟨q, hqS, hqk⟩ := hex
      have hφkp := hφ k p hk
      rw [injG_apply_of_mem ψ S D D' hD'mem hOclause S k q hqS hqS hqk,
        inj_hcoe ψ S D D' hD'mem hOclause φ q hqS k hqk p hk] at hφkp
      have hpq : p ≠ q := fun he => hp (he ▸ hqS)
      have hpPatch : p ∈ (injPatch ψ S D q : Set X) := hOclause q hqS k hqk hk
      have hDp0 : D p = 0 := cleanNbhd_D_eq_zero D q (ψ q) p hpPatch.1 hpq
      have hordψq : (0 : WithTop ℤ) ≤ (ψ q).ord p := cleanNbhd_ord_nonneg D q (ψ q) p hpPatch.1 hpq
      have hb2 : (0 : WithTop ℤ) ≤ (ψ q - RS.MeroGermOn.restrict
          (Set.subset_univ (chartAt ℂ q).source)
          (φ : RS.MeroGermOn X (Set.univ : Set X))).ord p := by
        rw [hDp0] at hφkp
        simpa using hφkp
      have hqPatch : p ∈ (chartAt ℂ q).source := injPatch_sub ψ S D q hpPatch
      have hordφ : (0 : WithTop ℤ) ≤
          (RS.MeroGermOn.restrict (Set.subset_univ (chartAt ℂ q).source)
            (φ : RS.MeroGermOn X (Set.univ : Set X))).ord p := by
        have hsplit : (RS.MeroGermOn.restrict (Set.subset_univ (chartAt ℂ q).source)
            (φ : RS.MeroGermOn X (Set.univ : Set X)) : RS.MeroGermOn X (chartAt ℂ q).source) =
          ψ q + (-(ψ q - RS.MeroGermOn.restrict (Set.subset_univ (chartAt ℂ q).source)
            (φ : RS.MeroGermOn X (Set.univ : Set X)))) := by ring
        rw [hsplit]
        refine le_trans ?_ (RS.MeroGermOn.ord_add (chartAt ℂ q).open_source hqPatch _ _)
        rw [RS.MeroGermOn.ord_neg]
        exact le_min hordψq hb2
      have hordφp : (RS.MeroGermOn.restrict (Set.subset_univ (chartAt ℂ p).source)
          (φ : RS.MeroGermOn X (Set.univ : Set X))).ord p =
        (RS.MeroGermOn.restrict (Set.subset_univ (chartAt ℂ q).source)
          (φ : RS.MeroGermOn X (Set.univ : Set X))).ord p := by
        rw [RS.MeroGermOn.ord_restrict (Set.subset_univ (chartAt ℂ p).source)
          (chartAt ℂ p).open_source isOpen_univ (mem_chart_source ℂ p),
          RS.MeroGermOn.ord_restrict (Set.subset_univ (chartAt ℂ q).source)
          (chartAt ℂ q).open_source isOpen_univ hqPatch]
      rw [hDp0, hordφp]
      exact hordφ
    · have hφkp := hφ k p hk
      rw [injG_apply_of_not_mem ψ S D D' hD'mem hOclause S k
          (fun q hqS _ hqk => hex ⟨q, hqS, hqk⟩),
        Submodule.coe_zero, zero_sub, RS.MeroGermOn.ord_neg,
        RS.MeroGermOn.ord_restrict (𝒱.le_base k) (𝒱.U k).isOpen isOpen_univ hk] at hφkp
      rwa [RS.MeroGermOn.ord_restrict (Set.subset_univ (chartAt ℂ p).source)
        (chartAt ℂ p).open_source isOpen_univ (mem_chart_source ℂ p)]

/-! ### `H1Tail.equiv`, conditional on surjectivity (§8 R1's own fallback: an honest
explicit-hypothesis statement, not a vacuous one, per `CONVENTIONS.md` rule 3) -/

theorem H1Tail.toH1_surjective_of_tailToH1_surjective (D : RS.Divisor X)
    (hsurj : Function.Surjective (tailToH1 D)) : Function.Surjective (H1Tail.toH1 D) := by
  intro ξ
  obtain ⟨z, hz⟩ := hsurj ξ
  exact ⟨H1Tail.mk D z, by rw [H1Tail.toH1_mk]; exact hz⟩

/-- CC8's mandate, conditional on `tailToH1`'s surjectivity (item 3 of the four deferrals,
gated on `dolbeault-comparison`'s Leray/Mittag-Leffler-existence machinery — see this file's
file-end note for the exact obstruction). Injectivity (`H1Tail.toH1_injective`) is unconditional
and fully proved above; this is the one remaining hypothesis. -/
noncomputable def H1Tail.equivOfSurjective (D : RS.Divisor X)
    (hsurj : Function.Surjective (tailToH1 D)) : H1Tail D ≃ₗ[ℂ] RS.Cech.H1 D :=
  LinearEquiv.ofBijective (H1Tail.toH1 D)
    ⟨H1Tail.toH1_injective D, H1Tail.toH1_surjective_of_tailToH1_surjective D hsurj⟩

end RS.LaurentTail

/-!
### File-end note (FINISHER pass): what closed, what's built, what's still deferred, and why

**Closed this pass (three of the unit's four original deferrals):**

1. **`tailToH1_alpha`** (`tailToH1 D (alphaL D f) = 0`). Built via a *from-scratch* multi-point
   Mittag-Leffler combination, specialized to the case where every local datum comes from
   restricting one *global* `f : ℳ X` (which is exactly `alpha D f`'s shape):
   - `alphaAuxD D f := D ⊔ (-(divisor f))` (a single auxiliary divisor bounding *both* `D` and
     `f` itself globally, `f ≠ 0` case; `f = 0` is handled first, trivially, via `map_zero`).
   - `alphaPatch D f S p := cleanNbhd D p (restrict f) ⊓ compOpens (S.erase p)` (`S :=
     alphaFinset D f`): the per-point clean patch, now *also* excluding every other point of `S`.
   - An adapted cover `𝒱` for `S` via `Cech.exists_adapted_refinement` with `O := alphaPatch D f S`
     (reused verbatim from the concurrent `SixTerm.lean` builder's own "prescribed neighbourhood"
     idiom, per the interface note the earlier build recorded).
   - `mlSumCochain D' f hf T`: the cochain that is `restrict f` on `T ∩ S`'s marked members, `0`
     elsewhere (a `dite` on `∃ p ∈ T ∩ S, p ∈ 𝒱.U k`, well-defined regardless of *which* witness
     `p` is chosen because `hunique_S`/`hexcl` — themselves consequences of adaptedness *and* the
     `compOpens (S.erase p)` exclusion, not of adaptedness alone: **a genuine subtlety** — two
     *different* marked points sharing one cover member is not excluded by `FinCover.IsAdapted`'s
     bare definition, only by this file's own choice of `O` shrinking each patch away from the
     rest of `S`).
   - **Off-diagonal cover overlaps never meet `S`** (`hoffdiag`, pure consequence of the `∃!` in
     `IsAdapted`, no `O`-shrinking needed): this is what makes `mlSumCochain`'s coboundary
     `D`-bounded everywhere (`hg_MemLD`) — diagonal is `0` trivially, off-diagonal points are
     automatically outside `S`, where `f` is regular and `D = 0` (`not_mem_alphaFinset`).
   - `CLAIM1`: each point's own `mlClassAt D p (restrict f)` equals `mlClass 𝒱 (mlSumCochain {p})`
     via a `pairCover p (alphaPatch …) → 𝒱` refinement (`mlClass_res`), packaged through the *same*
     `mlClassAt_eq_of_valid` used for `mlClassAt`'s original construction.
   - `main` (`Finset.induction_on`): combines `CLAIM1`'s individual classes across all of `S` via
     two-argument `mlClass_add`, giving `∑ p ∈ S, mlClassAt D p (restrict f) = mlClass 𝒱
     (mlSumCochain S)`.
   - Finally `mlClass 𝒱 (mlSumCochain S) = 0` directly via `mlClass_eq_zero_of_exists` with the
     *global* witness `f` itself (the difference `mlSumCochain S i - restrict f` is `0` exactly
     on marked members, `D`-bounded via off-`S` regularity elsewhere) — this is the "genuinely
     the same direct application" the design doc's §5.2(a) always expected, now unlocked.
2. **`H1Tail.toH1`/`H1Tail.toH1_injective`** — closed via `Submodule.liftQ` off (1), then a
   **second, independent** multi-point construction (`injPatch`/`injD'`/`injψVD'`/`injG`,
   `inj_CLAIM1`/`inj_main`/`inj_hcoe`), this time for an *arbitrary* `z : T D` (no global function
   available a priori — representatives `ψ p` are chosen via `TailAt.mk_surjective`, and the
   auxiliary divisor `D' := S.sup' hSne (fun p => DPrimeOf D p (ψ p))` needs a genuine `Finset.sup'`
   since `RS.Divisor X` has **no `OrderBot`** — confirmed by direct inspection of
   `Function.locallyFinsuppWithin`'s instances: divisors can be arbitrarily negative, so
   `Finset.sup` (which needs `⊥`) is unavailable; `Finset.sup'` with the Finset's own nonemptiness
   witness is the correct tool). Given `tailToH1 D z = 0`, the same "sum equals one big `mlClass`"
   machinery reduces this to `Cech.mlClass_eq_zero_iff`'s `⇒` half (Forster 12.4, `toH1_injective`,
   confirmed landed at `Injectivity.lean:247`), which hands back a *global* `φ : LinSys D'` with
   `∀ i x ∈ 𝒰.U i, D`-bounded `mlSumCochain-analogue i - restrict φ`; reading this bound off at
   each marked point `p` (`x = p`) gives `TailAt.mk p D (ψ p) = TailAt.mk p D (restrict φ)`
   directly via `TailAt.mk_eq_zero_iff`, i.e. `z = alpha D φ`. At non-marked points `p ∉ S`
   (where `z p = 0` already), the *same* bound read off at a **different** point `q ∈ S` sharing
   `p`'s cover member (or directly, if `p`'s member is unmarked) gives `φ`'s own order bound at
   `p`, via the *sum-splitting* trick `restrict φ = ψ q + (-(ψ q - restrict φ))` and `ord_add`/
   `ord_neg` (mirrors exactly how `gOf_memLD_of_clean` bounds a coboundary from two one-sided
   pieces, one level up).
3. **`H1Tail.equivOfSurjective`**: a conditional equivalence, parametrized by an explicit
   `Function.Surjective (tailToH1 D)` hypothesis (per `CONVENTIONS.md` rule 3 and the design's own
   R1 fallback plan) — an honest statement, not a vacuous one, ready the moment surjectivity lands.

**NOT closed: surjectivity of `tailToH1` (item 3).** This is the one item that resisted this
finisher pass, and — contrary to the previous builder's framing (design doc §5.2(b), "gated on
`dolbeault-comparison`'s Leray theorem, not yet on disk") — it is **not simply a citation away**
now that `Jacobian/DolbeaultComparison/Leray.lean` (677 lines, confirmed complete: `exists_trade`,
`toH1_surjective_of_isGood`, `h1CoverEquiv`) has landed. A careful proof attempt (recorded here so
the next builder does not have to redo this analysis) shows:
- `toH1_surjective_of_isGood` lets us represent any `ξ : Cech.H1 D` by a cocycle `f` on a **good**
  cover `𝒰₀` (all members chart disks). Refining `𝒰₀` to be **also adapted** to `D`'s support (via
  `exists_adapted_refinement`, no extra work) gives a representative `f'` on a refinement `𝒱` —
  this refinement step is free (`resZ1`/`toH1_resH1`, no surjectivity needed).
- The genuinely hard step is showing `f'`'s class is **already** of Mittag-Leffler shape (a sum of
  local `mlClassAt`-type contributions at `D`'s finitely many marked points) *modulo a coboundary
  on `𝒱`*. This is **not** implied by `𝒰₀` being good: the induced sub-cocycle on the
  "background" members (away from all marked points, where `D = 0`) is a *bona fide* Čech
  `H¹(𝒪_X)`-valued obstruction (dimension = genus), and there is no elementary reason it vanishes
  — indeed it should generically **not** vanish; what Mittag-Leffler theory guarantees is that the
  *marked-point tail data* can absorb it, which is a genuinely analytic fact (classically proved
  via dbar-solving with prescribed principal parts, i.e. subtracting a local singular correction
  then
  solving a *smooth* dbar-problem for the remainder) — **not** a fact this unit's editable surface
  (`Jacobian/LaurentTail/` only, per the task's hard rules) has the machinery to prove: it would
  need a genuinely new result in `Jacobian/Dbar/`/`Jacobian/DolbeaultComparison/` (a meromorphic,
  not smooth, dbar-existence theorem), which is out of scope for this unit to build even if time
  permitted, since those directories are not in this unit's edit surface.
- An inductive bootstrap from the `D = 0` case (`dolbeaultEquiv`/`cechToH01`, PDE-based, *is* built
  in `DolbeaultComparison/Comparison.lean`) via the six-term sequence's `H1Incl_surjective` was
  also considered: raising `D` one point at a time via `H1Incl` only transports surjectivity
  *forward* (from smaller to larger `D`), and a divisor with mixed-sign values can't be reached
  from `0` by a monotone chain in one direction only — this route does not close either without
  additional (unbuilt) input.
- **Recommendation for whoever picks this up**: either (a) prove a bespoke local statement in
  `Jacobian/Dbar/` (a meromorphic dbar-existence lemma: given a smooth `(0,1)`-form and finitely
  many
  prescribed principal parts, solve `dbar u = η` away from the marked points with `u` having exactly
  those principal parts — the classical route), filed as a `docs/requests/dolbeault-comparison.md`
  or `docs/requests/dbar-solvability.md` ask since it is outside this unit's own surface, or
  (b) accept `H1Tail.equivOfSurjective`'s conditional form as the unit's final deliverable on
  this point, matching the design's own R1 fallback plan exactly.

**Two build-engineering gotchas hit and fixed this pass (recorded so no one repeats the slow
path):**
- **`Opens X`-level `≤` composed with a `Set X`-level `⊆` via bare `.trans`** (relying on the
  automatic `Opens → Set` coercion to make the composition typecheck) causes catastrophic
  `isDefEq`/`whnf` slowdown once the surrounding terms are sufficiently abstract (fully generic
  `𝒱`/`D`/`q`, no concrete instantiation to short-circuit unification): confirmed by direct
  isolation, a single lemma (`inj_hcoe`) this way did not finish in 4,000,000 heartbeats / 7+
  minutes wall-clock, whereas rewriting it to *first* coerce to an explicit `(𝒱.U k : Set X) ⊆
  (patch : Set X)` term and *then* `.trans` (now a plain `Set.Subset.trans`, monomorphic, fast to
  resolve) closes in under 10 seconds. Grep for this pattern (`).trans (` immediately after an
  `Opens`-typed term) if a similar slowdown resurfaces elsewhere in this codebase.
- **A single tactic proof accumulating ~25 `have`/`set` steps hits a severe elaboration
  performance wall regardless of `maxHeartbeats`** (confirmed: `20,000,000` heartbeats, 10+
  minutes wall-clock, still did not finish) — *not* the same issue as the `.trans` one above (it
  persisted after that fix was applied in isolation). The fix is architectural: factor the
  construction into separate top-level `noncomputable def`/`theorem` declarations, each stated
  against an explicit `variable (…) := …` block plus `include … in` (Lean 4 does **not**
  auto-include a section `variable` into a declaration just because the declaration's *tactic
  proof* references it — only variables appearing in the stated *type* are auto-included;
  anything used only in the proof needs an explicit `include`, confirmed by direct experiment).
  This mirrors exactly how `tailToH1_alpha`'s own helpers (`alphaPatch`/`mlSumCochain`/…) were
  already structured, and is now the pattern used throughout `injPatch`/`injG`/`inj_*` as well.

**RiemannRoch.lean**: `Jacobian/Finiteness/Chi.lean` has **landed** (confirmed, `Finiteness.lean`'s
own root docstring: "Unit COMPLETE, all 7 design files, zero sorries") — that gate is now open.
The **sole remaining gate** for `RiemannRoch.lean` is `H1Tail.equiv` itself (unconditional
surjectivity, item 3 above); see that file for the exact transport recipe, unchanged and ready to
apply verbatim the moment surjectivity lands.
-/

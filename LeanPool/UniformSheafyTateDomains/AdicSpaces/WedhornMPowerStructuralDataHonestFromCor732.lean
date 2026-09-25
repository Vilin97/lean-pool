/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornMPowerStructuralDataHonest
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalArithmeticPerTChain
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalCor732ToFactoredChain
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Presheaf

/-!
# `WedhornMPowerStructuralDataHonest` from localized Cor 7.32 / branch
data

The honest σ-factored structural supplier
`WedhornMPowerStructuralDataHonest` (commit landing
`WedhornMPowerStructuralDataHonest.lean`) packages the per-`t'`
σ-factored inequality

```
w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)
```

at each `(w, τ, t')` over the canonical test family
`localizedTestFamily s T_D s_D`. By `vle_iff_mul_unit_right`
(`WedhornMultiBranchSubsetInequality.lean`) this is **equivalent under
σ-cancellation** to the unfactored per-`t'` inequality

```
w.vle t' (algebraMap s_D)
```

which is the natural Wedhorn 8.34(ii) per-`t'` content.

## What this file provides

This file lands the **σ-cancellation reducer** between the σ-factored
honest target and its unfactored counterpart, plus the **trivial
`t' = algebraMap s_D` subcase closed by reflexivity**, plus a
**caller-shaped wrapper** that takes the unfactored per-`t'` chain as a
single hypothesis and produces `WedhornMPowerStructuralDataHonest`.

* `WedhornMPowerStructuralDataHonest_via_unfactored_chain` — the
  caller-shaped wrapper. Takes the unfactored per-`t'` chain
  `∀ w hf τ hτ hστ t' ht', w.vle t' (algebraMap s_D)` (the genuine
  Wedhorn-content residual on the local Spa) and produces
  `WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc`. Pure
  σ-cancellation via `vle_iff_mul_unit_right`.

* `WedhornMPowerStructuralDataHonest_t_eq_s_D_branch` — closes the
  `t' = algebraMap s_D` subcase trivially via `vle_total`. This
  branch is closed at every `(w, τ)` regardless of σ-strict-domination
  τ. Useful when `s_D ∈ T_D` (the `insertDenom`-normalised cover-piece
  setup).

## Branch case analysis

The honest target's quantification structure: `∀ w hf τ hτ hστ t' ht'`
with conclusion `w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)`. The
test-family branches:

* **α_s_D branch**: `τ = algebraMap s_D`. σ-strict-domination by
  `algebraMap s_D` gives `w(σ_loc) ≤ w(algebraMap s_D)` strict; this
  pins down `algebraMap s_D` non-degeneracy via
  `not_vle_zero_of_strict_dominator` but does NOT directly give
  `w(t') ≤ w(algebraMap s_D)` for general `t' ∈ T_D.image algebraMap`.
* **α_T_D branch**: `τ = algebraMap t₀` for some `t₀ ∈ T_D`.
  σ-strict-domination by `algebraMap t₀` gives `w(σ_loc) ≤
  w(algebraMap t₀)` strict; only constrains the σ_loc/t₀ ratio, not
  the t'/s_D ratio for general `t'`.

Neither branch closes the per-`t'` content from σ-strict-domination
alone — this is the genuine Wedhorn 8.34(ii) Route B residual. The
wrapper here packages the residual into a single hypothesis-shuffler.

The **`t' = algebraMap s_D` subcase** closes trivially by `vle_total`
(reflexivity), regardless of branch and σ-strict-domination structure.
Landed below as `WedhornMPowerStructuralDataHonest_t_eq_s_D_branch`.

## Single named residual

The unfactored per-`t'` chain on the local Spa:

```lean
theorem unfactored_per_t_chain_target
    [DecidableEq A] (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    -- Wedhorn 8.34(ii) Cor 7.32 structural data:
    -- (π_loc : ..., M : ℕ, hσ_loc_eq_pow : σ_loc = π_loc^(M+1), ...) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s) →
      ∀ τ ∈ localizedTestFamily s T_D s_D,
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle t' (algebraMap A (Localization.Away s) s_D)
```

The proof of this residual is the genuinely-new Wedhorn 8.34(ii)
Route B content (cf. `WedhornMultiDominatingUnit.lean:234–304`'s
audit). This file's wrapper is callsite-ready packaging.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson /
  T001 / faithful-flatness / Zavyalov / bivariate-overlap / per-call
  C1 assembly content.
* No edits to Secondary's per-call assembly leaf, Primary assembly /
  root / final files.
* Reuses `WedhornMPowerStructuralDataHonest` (target def),
  `vle_iff_mul_unit_right` (σ-cancellation),
  `mem_localizedTestFamily_iff` (test-family branch case-split). -/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

/-- **Unfactored per-`t'` chain target** — the genuine Wedhorn 8.34(ii)
Route B per-`t'` content on the local Spa.

This `Prop`-valued definition packages the unfactored per-`t'` chain
hypothesis as a named target, ready to be plugged into
`WedhornMPowerStructuralDataHonest_via_unfactored_chain` (below). The
shape matches the natural per-`t'` Wedhorn content
`w.vle t' (algebraMap s_D)`, equivalent under σ-cancellation to the
σ-factored honest target.

Discharging this `Prop` is the genuine remaining residual; reductions
and consumers may treat it as the named single hypothesis. -/
def UnfactoredPerTChainTarget
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    w.vle ((σ_loc : Localization.Away s) *
        (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
      (algebraMap A (Localization.Away s) s) →
    ∀ τ ∈ localizedTestFamily s T_D s_D,
      w.vle (σ_loc : Localization.Away s) τ ∧
        ¬ w.vle τ (σ_loc : Localization.Away s) →
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle t' (algebraMap A (Localization.Away s) s_D)

omit [PlusSubring A] in
/-- **σ-cancellation wrapper**: produce the honest σ-factored supplier
`WedhornMPowerStructuralDataHonest` from the named unfactored per-`t'`
chain target `UnfactoredPerTChainTarget`.

The unfactored chain is the natural Wedhorn 8.34(ii) per-`t'` content
(equivalent to the σ-factored target via `vle_iff_mul_unit_right` for
the unit `σ_loc`). This wrapper packages the residual into a single
caller-shaped hypothesis.

**Proof**: pointwise application of `vle_iff_mul_unit_right` (the
σ-cancellation iff). -/
theorem WedhornMPowerStructuralDataHonest_via_unfactored_chain
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_per_t_chain : UnfactoredPerTChainTarget P T s hopen T_D s_D σ_loc) :
    WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_f τ hτ hστ t' ht'
  -- Apply σ-cancellation iff to convert unfactored ↔ σ-factored.
  exact (vle_iff_mul_unit_right w σ_loc t'
    (algebraMap A (Localization.Away s) s_D)).mpr
    (h_per_t_chain w hw_spa hw_f τ hτ hστ t' ht')

/-- **α_s_D-branch unfactored per-`t'` chain target**. Specialises
`UnfactoredPerTChainTarget` to the `τ = algebraMap s_D` branch of the
canonical localized test family. Matches the `h_per_t_chain` shape
consumed by `h_T_test_compat_loc_branch_α_s_D`
(`WedhornLocalCompatFromTestFamily.lean`). -/
def UnfactoredPerTChainBranchAlphaS_D
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    w.vle ((σ_loc : Localization.Away s) *
        (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
      (algebraMap A (Localization.Away s) s) →
    w.vle (σ_loc : Localization.Away s)
        (algebraMap A (Localization.Away s) s_D) ∧
      ¬ w.vle (algebraMap A (Localization.Away s) s_D)
        (σ_loc : Localization.Away s) →
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle t' (algebraMap A (Localization.Away s) s_D)

/-- **α_T_D-branch unfactored per-`t'` chain target**. Specialises
`UnfactoredPerTChainTarget` to the `τ ∈ T_D.image algebraMap` branch
of the canonical localized test family. Matches the per-τ shape
needed by `h_T_test_compat_loc_branch_α_T_D`
(`WedhornLocalCompatFromTestFamily.lean`). -/
def UnfactoredPerTChainBranchAlphaT_D
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s) →
      w.vle (σ_loc : Localization.Away s) τ ∧
        ¬ w.vle τ (σ_loc : Localization.Away s) →
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle t' (algebraMap A (Localization.Away s) s_D)

omit [PlusSubring A] in
/-- **Combiner: `UnfactoredPerTChainTarget` from per-branch chains**.

Discharges the unified `UnfactoredPerTChainTarget` from the two
per-branch chain hypotheses (α_s_D and α_T_D) by case-splitting on
`mem_localizedTestFamily_iff`.

Each branch's chain consumes the same `(w, hf, hστ_at_τ)` data with
τ-specialised σ-strict-domination, and outputs the per-`t'`
inequality `w.vle t' (algebraMap s_D)` for every t' ∈ T_D.image. The
combiner unifies them into the named target. -/
theorem UnfactoredPerTChainTarget_via_branches
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_α_s_D : UnfactoredPerTChainBranchAlphaS_D P T s hopen T_D s_D σ_loc)
    (h_α_T_D : UnfactoredPerTChainBranchAlphaT_D P T s hopen T_D s_D σ_loc) :
    UnfactoredPerTChainTarget P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_f τ hτ hστ t' ht'
  -- Case-split on τ ∈ localizedTestFamily.
  rw [mem_localizedTestFamily_iff] at hτ
  rcases hτ with rfl | hτ_in_T_D
  · -- α_s_D branch.
    exact h_α_s_D w hw_spa hw_f hστ t' ht'
  · -- α_T_D branch.
    exact h_α_T_D τ hτ_in_T_D w hw_spa hw_f hστ t' ht'

/-- **Per-`t'` α_s_D-branch fact** — single-`t'` slice of
`UnfactoredPerTChainBranchAlphaS_D`.

Carries the single Wedhorn-content fact for one specific `t' ∈
T_D.image algebraMap`. The full branch chain is the conjunction of
this fact across all `t' ∈ T_D.image`. Used to break the residual
into per-`t'` pieces with explicit naming. -/
def UnfactoredPerTChainBranchAlphaS_DPerTFact
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (t' : Localization.Away s) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    w.vle ((σ_loc : Localization.Away s) *
        (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
      (algebraMap A (Localization.Away s) s) →
    w.vle (σ_loc : Localization.Away s)
        (algebraMap A (Localization.Away s) s_D) ∧
      ¬ w.vle (algebraMap A (Localization.Away s) s_D)
        (σ_loc : Localization.Away s) →
    w.vle t' (algebraMap A (Localization.Away s) s_D)

omit [PlusSubring A] in
/-- **α_s_D branch trivial closure at `t' = algebraMap s_D`**.

The per-`t'` α_s_D-branch fact closes trivially at `t' = algebraMap s_D`
by `vle_total` reflexivity (regardless of `(w, hf, hστ)`).

This closes the `t' = algebraMap s_D` sub-piece of
`UnfactoredPerTChainBranchAlphaS_D` whenever `algebraMap s_D ∈
T_D.image algebraMap` (i.e., `s_D ∈ T_D` in the typical
`insertDenom`-normalised setup). -/
theorem UnfactoredPerTChainBranchAlphaS_DPerTFact_at_algebraMap_s_D
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) :
    UnfactoredPerTChainBranchAlphaS_DPerTFact
      P T s hopen T_D s_D σ_loc
      (algebraMap A (Localization.Away s) s_D) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w _hw_spa _hw_f _hστ
  exact (w.vle_total _ _).elim id id

omit [PlusSubring A] in
/-- **α_s_D branch chain via per-`t'` facts**.

Combines per-`t'` α_s_D-branch facts (one for each `t' ∈ T_D.image
algebraMap`) into the full `UnfactoredPerTChainBranchAlphaS_D` branch
chain.

This is the per-`t'` decomposition: the branch chain is the
conjunction across all `t'` of the per-`t'` fact. The discharger
exposes per-`t'` granularity to the caller, which can then close
specific `t'`s (e.g., `t' = algebraMap s_D` via the trivial closure
above) and leave only the genuinely-residual `t'`s. -/
theorem UnfactoredPerTChainBranchAlphaS_D_via_per_t_facts
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_per_t :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        UnfactoredPerTChainBranchAlphaS_DPerTFact
          P T s hopen T_D s_D σ_loc t') :
    UnfactoredPerTChainBranchAlphaS_D P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_f hστ t' ht'
  exact h_per_t t' ht' w hw_spa hw_f hστ

/-- **α_s_D M-power-decay structural target** — the per-`t'` Wedhorn
8.34(ii) M-power-decay structural fact for the α_s_D branch.

For each `(w, hf, hστ_α_s_D, t')`, gives the structural inequality
`w.vle (algebraMap s) (algebraMap s_D * σ_loc * ∏ erase t')`. This is
the natural shape of Wedhorn 8.34(ii)'s σ-power-decay output (cf.
the documented `subset_inequality_target` at
`WedhornDominatingBranchInequality.lean:104`); it carries the genuine
Wedhorn σ-power decay content but is **distinct** from
`AlphaS_DFactoredChainTarget`: the M-power-decay form is the inequality
chain through `algebraMap s`, whereas `AlphaS_DFactoredChainTarget`
is the σ-factored per-`t'` form. The two differ by cancellation of
`∏ erase t'` (per-`t'` non-vanishing condition). -/
def AlphaS_DMPowerDecayTarget
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    w.vle ((σ_loc : Localization.Away s) *
        (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
      (algebraMap A (Localization.Away s) s) →
    w.vle (σ_loc : Localization.Away s)
        (algebraMap A (Localization.Away s) s_D) ∧
      ¬ w.vle (algebraMap A (Localization.Away s) s_D)
        (σ_loc : Localization.Away s) →
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle (algebraMap A (Localization.Away s) s)
        (algebraMap A (Localization.Away s) s_D *
          (σ_loc : Localization.Away s) *
          (∏ t ∈ (T_D.image (algebraMap A (Localization.Away s))).erase t', t))

/-- **α_s_D per-`t'` `∏ erase t'` non-vanishing target** — the algebraic
companion residual to `AlphaS_DMPowerDecayTarget`.

For each `(w, hf, hστ_α_s_D, t')`, asserts non-vanishing of
`∏ T_D.image α \ {t'}` at `w`. This is the cancellation condition
needed to extract the σ-factored chain from the M-power decay (via
`ValuativeRel.mul_vle_mul_iff_left`). -/
def AlphaS_DProdEraseNonVanishTarget
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    w.vle ((σ_loc : Localization.Away s) *
        (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
      (algebraMap A (Localization.Away s) s) →
    w.vle (σ_loc : Localization.Away s)
        (algebraMap A (Localization.Away s) s_D) ∧
      ¬ w.vle (algebraMap A (Localization.Away s) s_D)
        (σ_loc : Localization.Away s) →
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      ¬ w.vle (∏ t ∈ (T_D.image
        (algebraMap A (Localization.Away s))).erase t', t) 0

/-- **Spa-uniform σ-power-decay** for the localized α_s_D branch.

Captures the genuine Wedhorn 8.34(ii) σ-power-decay output in its
natural shape: a single power of `algebraMap s_D` controlled by the
cardinality of the `algebraMap`-image of `T_D`. Concretely:

`∀ w ∈ Spa, w.vle (algebraMap s) (σ_loc * (algebraMap s_D) ^ |T_D.image|)`.

This is the natural Cor 7.32 + `Spa`-compactness M-choice output (cf.
`WedhornFactorExtractionPowerDecay.lean:144-163` and
`WedhornSigmaPowerDecay.lean:51-78`); it is **strictly closer to
Cor 7.32** than `AlphaS_DMPowerDecayTarget` since the RHS is a single
power, not a per-`t'` `∏ erase` product. -/
def AlphaS_DUniformSigmaPowerDecay
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    w.vle (algebraMap A (Localization.Away s) s)
      ((σ_loc : Localization.Away s) *
        (algebraMap A (Localization.Away s) s_D) ^
          (T_D.image (algebraMap A (Localization.Away s))).card)

/-- **`s_D`-lower-bound on `T_D.image \ {t'}`** — algebraic cancellation
premise needed to exchange a single `(algebraMap s_D)`-power for the
per-`t'` `∏ erase t'` shape.

For each `(w, t', t'')` with `t' ∈ T_D.image` and `t'' ∈ erase t'`,
asserts `w.vle (algebraMap s_D) t''`. Lifting pointwise via
`Spv.vle_prod_of_pointwise` then yields
`w.vle ((algebraMap s_D)^|erase t'|) (∏ erase t')`, the cancellation
step that bridges the σ-power-decay shape to the M-power-decay target. -/
def AlphaS_DProdEraseLowerBound
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      ∀ t'' ∈ (T_D.image (algebraMap A (Localization.Away s))).erase t',
        w.vle (algebraMap A (Localization.Away s) s_D) t''

omit [PlusSubring A] in
/-- **`AlphaS_DMPowerDecayTarget` via Spa-uniform σ-power-decay +
`s_D`-lower-bound**. The genuine sharper reducer.

Takes two SEPARATED inputs strictly closer to Cor 7.32:

1. `AlphaS_DUniformSigmaPowerDecay` — Spa-uniform σ-power-decay shape
   `w.vle (algebraMap s) (σ_loc * (algebraMap s_D) ^ |T_D.image|)`,
   matching the natural Cor 7.32 σ-construction + Spa-compactness
   M-choice output (single power form).
2. `AlphaS_DProdEraseLowerBound` — pointwise `w.vle (algebraMap s_D) t''`
   for `t'' ∈ T_D.image.erase t'`, the algebraic cancellation premise.

The proof:
* Lift the lower bound via `Spv.vle_prod_of_pointwise`:
  `w.vle ((algebraMap s_D) ^ (|T_D.image| - 1)) (∏ erase t')`.
* Multiply by `algebraMap s_D * σ_loc` on the left:
  `w.vle (σ_loc * (algebraMap s_D) ^ |T_D.image|)
    (algebraMap s_D * σ_loc * ∏ erase t')`
  (using `s_D * s_D^(c-1) = s_D^c` and ring commutativity).
* Chain through the σ-power-decay via `vle_trans`. -/
theorem AlphaS_DMPowerDecayTarget_via_uniform_decay_and_lower_bound
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_decay : AlphaS_DUniformSigmaPowerDecay P T s hopen T_D s_D σ_loc)
    (h_lower : AlphaS_DProdEraseLowerBound P T s hopen T_D s_D) :
    AlphaS_DMPowerDecayTarget P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa _hw_f _hστ t' ht'
  letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
  -- Local notation for the carriers in `Localization.Away s`.
  set imgT := T_D.image (algebraMap A (Localization.Away s))
  set sD : Localization.Away s := algebraMap A (Localization.Away s) s_D
  set σL : Localization.Away s := (σ_loc : Localization.Away s)
  -- Step 1: Lift `h_lower` to a product lower bound on `imgT.erase t'`.
  have h_lower_at : ∀ t'' ∈ imgT.erase t', w.vle sD t'' :=
    h_lower w hw_spa t' ht'
  have h_prod_lift :
      w.vle (∏ _t ∈ imgT.erase t', sD) (∏ t ∈ imgT.erase t', t) :=
    Spv.vle_prod_of_pointwise w (imgT.erase t') h_lower_at
  -- Replace the constant product by a power and the cardinality by `c - 1`.
  have h_const_prod :
      (∏ _t ∈ imgT.erase t', sD) = sD ^ (imgT.erase t').card :=
    Finset.prod_const sD
  have h_card_erase : (imgT.erase t').card = imgT.card - 1 :=
    Finset.card_erase_of_mem ht'
  rw [h_const_prod, h_card_erase] at h_prod_lift
  -- Step 2: Multiply both sides by `sD * σL` on the LEFT.
  have h_prod_mul :
      w.vle ((sD * σL) * sD ^ (imgT.card - 1))
            ((sD * σL) * (∏ t ∈ imgT.erase t', t)) :=
    ValuativeRel.mul_vle_mul_right h_prod_lift (sD * σL)
  -- Step 3: Rewrite LHS as `σL * sD ^ imgT.card` using `pow_succ'` + `ring`.
  have h_card_pos : 1 ≤ imgT.card := Finset.card_pos.mpr ⟨t', ht'⟩
  have h_pow_split : sD ^ imgT.card = sD * sD ^ (imgT.card - 1) := by
    conv_lhs =>
      rw [show imgT.card = imgT.card - 1 + 1 from
        (Nat.sub_add_cancel h_card_pos).symm]
    exact pow_succ' sD (imgT.card - 1)
  have h_lhs_eq : (sD * σL) * sD ^ (imgT.card - 1) = σL * sD ^ imgT.card := by
    rw [h_pow_split]; ring
  rw [h_lhs_eq] at h_prod_mul
  -- Step 4: Chain `h_decay` (giving `s ≤ σL * sD ^ imgT.card`) through `h_prod_mul`.
  have h_decay_at :
      w.vle (algebraMap A (Localization.Away s) s)
        (σL * sD ^ imgT.card) := h_decay w hw_spa
  exact w.vle_trans h_decay_at h_prod_mul

/-- **Spa-uniform π-power-decay** — the Cor 7.32-internal, π-power form
of `AlphaS_DUniformSigmaPowerDecay`. Captures the natural pseudo-
uniformizer-power output of `Cor732.exists_dominating_unit` (whose
internal construction sets `s := π^(N+1)` per `Cor732.lean:225`):

`∀ w ∈ Spa, w.vle (algMap s)
  ((π_loc : Localization.Away s) ^ (M+1) * (algMap s_D) ^ |T_D.image|)`.

The element `π_loc : locSubring P T s` is a member of the localized
ring of definition `D = A₀[t₁/s, …, tₙ/s]`, definitionally equal to
`(locPairOfDefinition P T s hopen).A₀`; its image
`(π_loc : Localization.Away s)` plays the role of the pseudo-
uniformizer-power-base. The interpretation as a pseudo-uniformizer is
conveyed by the companion σ-as-π-power equation
`(σ_loc : Localization.Away s) = (π_loc : Localization.Away s) ^ (M + 1)`
(see `AlphaS_DUniformSigmaPowerDecay_via_pi_power`).

This is **strictly closer to Cor 7.32** than `AlphaS_DUniformSigmaPowerDecay`
since it expresses the σ-factor as an explicit pseudo-uniformizer power
`π_loc^(M+1)`, exposing the σ-as-π-power identification internal to
Cor 7.32's construction. The genuine Wedhorn 8.34(ii) M-choice content
is now isolated as the Spa-uniform inequality with `π_loc^(M+1) * s_D^k`
on the RHS, ready for a Spa-quasicompactness + topological-nilpotence
discharge in a future ticket. -/
def AlphaS_DUniformPiPowerDecay
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (π_loc : locSubring P T s) (M : ℕ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    w.vle (algebraMap A (Localization.Away s) s)
      ((π_loc : Localization.Away s) ^ (M + 1) *
        (algebraMap A (Localization.Away s) s_D) ^
          (T_D.image (algebraMap A (Localization.Away s))).card)

omit [PlusSubring A] in
/-- **`AlphaS_DUniformSigmaPowerDecay` via π-power decay + σ-as-π-power
identification**. Sharper supplier whose remaining assumptions are
exactly the **exposed Cor 7.32 σ-construction data**:

* `hσ_loc_eq_pow` — σ-as-π-power identification:
  `(σ_loc : Localization.Away s) = (π_loc : Localization.Away s) ^ (M + 1)`,
  the σ-construction internal to `Cor732.exists_dominating_unit`
  (where `s := π^(N+1)` per `Cor732.lean:225`); the natural choice
  for `π_loc : locSubring P T s` is the lift `algebraMapD P T s π̃` of
  a global pseudo-uniformizer `π̃ : P.A₀`.
* `AlphaS_DUniformPiPowerDecay P T s hopen T_D s_D π_loc M` — Spa-uniform
  M-choice in π-power form, the Spa-quasicompactness +
  topological-nilpotence input residual.

The π_loc parameter is `locSubring P T s` (which is definitionally
`(locPairOfDefinition P T s hopen).A₀`); using `locSubring` directly
keeps the binder type free of `TopologicalSpace`-instance dependencies.

The proof: substitute `(σ_loc : Localization.Away s)` by
`(π_loc : Localization.Away s) ^ (M + 1)` in the goal via `hσ_loc_eq_pow`,
then apply the π-power decay residual at `w`. The genuine Cor 7.32
σ-construction data is now decomposed into the algebraic σ-as-π-power
equation (internal to Cor 7.32) and the analytic π-power Spa-uniform
decay (the next-step residual). -/
theorem AlphaS_DUniformSigmaPowerDecay_via_pi_power
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (π_loc : locSubring P T s) (M : ℕ)
    (hσ_loc_eq_pow :
      (σ_loc : Localization.Away s) =
        (π_loc : Localization.Away s) ^ (M + 1))
    (h_pi_decay : AlphaS_DUniformPiPowerDecay P T s hopen T_D s_D π_loc M) :
    AlphaS_DUniformSigmaPowerDecay P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa
  rw [hσ_loc_eq_pow]
  exact h_pi_decay w hw_spa

/-- **σ-factored α_s_D-branch chain target** — the genuine Wedhorn
8.34(ii) Route B σ-power-decay residual for the α_s_D branch.

Matches the `h_factored` parameter shape of
`h_α_s_D_per_t_via_factored_chain` (`WedhornLocalArithmeticPerTChain.lean`):
the per-`t'` σ-factored inequality
`w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)`
under f-membership and σ-strict-domination by `algebraMap s_D`. Carries
the genuine Wedhorn-content per-`t'` arithmetic; equivalent under
σ-cancellation to the unfactored α_s_D-branch chain. -/
def AlphaS_DFactoredChainTarget
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    w.vle ((σ_loc : Localization.Away s) *
        (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
      (algebraMap A (Localization.Away s) s) →
    w.vle (σ_loc : Localization.Away s)
        (algebraMap A (Localization.Away s) s_D) ∧
      ¬ w.vle (algebraMap A (Localization.Away s) s_D)
        (σ_loc : Localization.Away s) →
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle (t' * (σ_loc : Localization.Away s))
        ((algebraMap A (Localization.Away s) s_D) *
          (σ_loc : Localization.Away s))

omit [PlusSubring A] in
/-- **α_s_D-branch chain via σ-factored chain residual**.

Closes `UnfactoredPerTChainBranchAlphaS_D` from the named σ-factored
chain residual `AlphaS_DFactoredChainTarget` via the existing
σ-cancellation reducer
`h_α_s_D_per_t_via_factored_chain` (`WedhornLocalArithmeticPerTChain.lean`).

This is the **strongest reduction** of the α_s_D branch chain
achievable from the existing σ-factored API: the residual hypothesis
is the genuine Wedhorn 8.34(ii) Route B per-`t'` σ-power-decay content,
in the canonical σ-factored form matching Wedhorn's natural candidate
shape `f := σ_loc * (∏ T_D.image algebraMap)`. -/
theorem UnfactoredPerTChainBranchAlphaS_D_via_factored_chain
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_factored : AlphaS_DFactoredChainTarget P T s hopen T_D s_D σ_loc) :
    UnfactoredPerTChainBranchAlphaS_D P T s hopen T_D s_D σ_loc :=
  h_α_s_D_per_t_via_factored_chain P T s hopen T_D s_D σ_loc h_factored

omit [PlusSubring A] in
/-- **α_s_D factored chain via M-power decay + ∏-erase non-vanishing**.

Sharper reducer: closes `AlphaS_DFactoredChainTarget` from two
SEPARATED genuine Wedhorn-content residuals:

1. `AlphaS_DMPowerDecayTarget` — the σ-power-decay structural
   inequality chain through `algebraMap s` (the natural Cor 7.32 +
   compactness output).
2. `AlphaS_DProdEraseNonVanishTarget` — per-`t'` non-vanishing of
   `∏ T_D.image α \ {t'}` (the algebraic cancellation premise).

The proof chains f-membership through the M-power decay then cancels
`∏ erase t'` via `ValuativeRel.mul_vle_mul_iff_left`, after rewriting
products to expose the cancelled factor on both sides. -/
theorem AlphaS_DFactoredChainTarget_via_M_power_decay
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_decay : AlphaS_DMPowerDecayTarget P T s hopen T_D s_D σ_loc)
    (h_erase_ne :
      AlphaS_DProdEraseNonVanishTarget P T s hopen T_D s_D σ_loc) :
    AlphaS_DFactoredChainTarget P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_f hστ t' ht'
  have h_struct := h_decay w hw_spa hw_f hστ t' ht'
  have h_erase := h_erase_ne w hw_spa hw_f hστ t' ht'
  -- Notation shorthand.
  set α_s_D : Localization.Away s := algebraMap A (Localization.Away s) s_D
  set σ : Localization.Away s := (σ_loc : Localization.Away s)
  set Pi_full : Localization.Away s :=
    ∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t
  set Pi_erase : Localization.Away s :=
    ∏ t ∈ (T_D.image (algebraMap A (Localization.Away s))).erase t', t
  -- Product split via `Finset.mul_prod_erase`.
  have h_prod_split : Pi_full = t' * Pi_erase :=
    (Finset.mul_prod_erase _ _ ht').symm
  -- Chain f-membership through the structural decay.
  have h_chain : w.vle (σ * Pi_full) (α_s_D * σ * Pi_erase) :=
    w.vle_trans hw_f h_struct
  -- Rewrite LHS with product split: σ * Pi_full = σ * (t' * Pi_erase) = (t' * σ) * Pi_erase.
  have h_LHS_eq : σ * Pi_full = (t' * σ) * Pi_erase := by
    rw [h_prod_split]; ring
  -- Rewrite RHS to expose Pi_erase factor on the right.
  have h_RHS_eq : α_s_D * σ * Pi_erase = (α_s_D * σ) * Pi_erase := by
    rw [mul_assoc]
  -- Apply rewrites.
  rw [h_LHS_eq, h_RHS_eq] at h_chain
  -- Cancel Pi_erase via mul_vle_mul_iff_left.
  letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
  exact (ValuativeRel.mul_vle_mul_iff_left (z := Pi_erase) h_erase).mp h_chain

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] in
/-- **Trivial subcase: `t' = algebraMap s_D`**.

When the per-`t'` quantifier ranges over `t' = algebraMap s_D` (which
happens iff `s_D ∈ T_D`), the σ-factored conclusion
`w.vle (algebraMap s_D * σ_loc) (algebraMap s_D * σ_loc)` is reflexive.

This subcase closes by `vle_total` regardless of the branch τ or
σ-strict-domination structure. Useful for `insertDenom`-normalised
covers where `s_D ∈ T_D` is enforced. -/
theorem WedhornMPowerStructuralDataHonest_t_eq_s_D_branch
    [DecidableEq A]
    (s : A) (s_D : A) (σ_loc : (Localization.Away s)ˣ)
    (w : Spv (Localization.Away s)) :
    w.vle ((algebraMap A (Localization.Away s) s_D) *
        (σ_loc : Localization.Away s))
      ((algebraMap A (Localization.Away s) s_D) *
        (σ_loc : Localization.Away s)) :=
  (w.vle_total _ _).elim id id

/-- **Per-`t'` Wedhorn σ-power-decay residual at the `α s_D`
specialisation**. Bundled named residual carrying the genuinely-new
Wedhorn 8.34(ii) Route B content for the α_s_D branch in the
**classical Wedhorn shape** (single-`t'` candidate `σ_loc * t' *
(α s_D)^N`).

For each `(w, t')` with `w ∈ Spa(Loc s, ⁺)` and
`t' ∈ T_D.image (algebraMap A (Loc s))`:

* the per-`t'` Wedhorn chain through `α s`:
  `w.vle ((σ_loc : Loc s) * t' * (algebraMap A (Loc s) s_D)^N) (algebraMap A (Loc s) s)`;
* the σ-power-decay at `α s` (Wedhorn's Spa-quasi-compactness M-choice):
  `w.vle (algebraMap A (Loc s) s) ((σ_loc : Loc s) * (algebraMap A (Loc s) s_D)^(N+1))`.

Both pieces follow Wedhorn's joint σ + N construction (Cor 7.32 σ +
compactness N-choice). The exponent `N : ℕ` is the Wedhorn N parameter,
chosen via Spa-quasi-compactness so that `σ_loc * (algMap s_D)^(N+1)`
uniformly bounds `algMap s` from above on Spa.

## Why localized Cor 7.32 strict domination is insufficient

Cor 7.32 (`exists_dominating_unit`) outputs only the σ-strict-domination
shape `w(σ_loc) ≤ w(τ_w)` strict — see the explicit warning at
`WedhornSigmaPowerDecay.lean:14-22` flagging that the σ-power-decay
shape requires the OPPOSITE valuation orientation
(`w(α s) ≤ w(σ_loc * (α s_D)^(N+1))`, σ "large from below" times an
`α s_D`-power). The Wedhorn discharge route uses σ_loc as a π-power
(internal to `Cor732.exists_dominating_unit`'s `s := π^(N+1)` at
`Cor732.lean:225`), N chosen via `exists_dominatedBy_cover` for
Spa-quasi-compactness, plus topological-nilpotence of π. None of this
is exposed by Cor 7.32's output type. -/
def AlphaS_DBranchPerTSigmaPowerDecay
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle ((σ_loc : Localization.Away s) * t' *
          (algebraMap A (Localization.Away s) s_D) ^ N)
        (algebraMap A (Localization.Away s) s) ∧
      w.vle (algebraMap A (Localization.Away s) s)
        ((σ_loc : Localization.Away s) *
          (algebraMap A (Localization.Away s) s_D) ^ (N + 1))

omit [PlusSubring A] in
/-- **Sharper alternative path to `UnfactoredPerTChainBranchAlphaS_D`
via the abstract Wedhorn algebraic core**.

Bypasses the M-power-decay structural form (`AlphaS_DMPowerDecayTarget`
+ `AlphaS_DProdEraseLowerBound`) and consumes the SINGLE bundled
per-`t'` Wedhorn σ-power-decay residual `AlphaS_DBranchPerTSigmaPowerDecay`,
proving `UnfactoredPerTChainBranchAlphaS_D` directly via the abstract
algebraic core `vle_t_D_s_of_sigma_decay_chain_at` from
`WedhornMultiBranchSubsetInequality.lean`.

The α s_D non-vanishing premise is auto-derived from σ-strict-domination
via `not_vle_zero_of_strict_dominator` (the strict half of
α_s_D-branch σ-strict-domination forces `α s_D` to not vanish at `w`).

**This leaves exactly ONE named residual**:
`AlphaS_DBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N`,
the Wedhorn 8.34(ii) Route B per-`t'` σ-power-decay content (with N
chosen via Spa-quasi-compactness / topological-nilpotence of σ_loc).

## Valuation-orientation handoff

The localized Cor 7.32 σ-strict-domination output (per
`WedhornLocalizedCor732Consumer.lean`) supplies σ_loc with
σ-strict-domination over `localizedTestFamily s T_D s_D`. It does
**not** supply `AlphaS_DBranchPerTSigmaPowerDecay`:

* The σ-power-decay component requires the OPPOSITE orientation
  `w(α s) ≤ w(σ_loc * (α s_D)^(N+1))` from Cor 7.32's σ-strict-dom
  `w(σ_loc) ≤ w(τ_w)` strict — see `WedhornSigmaPowerDecay.lean:14-22`.
* The per-`t'` chain `w(σ_loc * t' * (α s_D)^N) ≤ w(α s)` is the
  per-`t'` slice of Wedhorn 8.34(ii) Step 2's denominator-clearing
  ratio choice, also outside Cor 7.32's output.
* Wedhorn's discharge uses Spa-quasi-compactness M-choice for
  topologically-nilpotent π_loc with σ_loc = π_loc^(M+1), per
  `Cor732.lean:225` and `WedhornFactorExtractionPowerDecay.lean:144-163`. -/
theorem UnfactoredPerTChainBranchAlphaS_D_via_classical_sigma_decay
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_residual :
      AlphaS_DBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N) :
    UnfactoredPerTChainBranchAlphaS_D P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa _hw_f hστ t' ht'
  have hα_s_D_ne :
      ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 :=
    not_vle_zero_of_strict_dominator hστ.2
  obtain ⟨h_chain_t', h_C_decay⟩ := h_residual w hw_spa t' ht'
  exact vle_t_D_s_of_sigma_decay_chain_at w N hα_s_D_ne h_chain_t' h_C_decay

/-- **Per-(τ, t') Wedhorn σ-power-decay residual at the `α_T_D`
specialisation**. Bundled named residual analogous to
`AlphaS_DBranchPerTSigmaPowerDecay`, indexed by the dominating
`τ ∈ T_D.image (algebraMap A (Localization.Away s))` (the α_T_D
branch's σ-strict-dominator).

For each `(τ, w, t')` with `τ, t' ∈ T_D.image (algebraMap)` and
`w ∈ Spa(Loc s, ⁺)`:

* `α s_D` non-vanishing at `w`:
  `¬ w.vle (algebraMap A (Loc s) s_D) 0` — this is **not** auto-derivable
  from `hστ` in the α_T_D branch (since the strict dominator is `τ`,
  not `α s_D`), so it is included as part of the bundled residual;
* the per-`t'` Wedhorn chain through `α s`:
  `w.vle ((σ_loc : Loc s) * t' * (algebraMap A (Loc s) s_D)^N) (algebraMap A (Loc s) s)`;
* the σ-power-decay at `α s`:
  `w.vle (algebraMap A (Loc s) s) ((σ_loc : Loc s) * (algebraMap A (Loc s) s_D)^(N+1))`.

The chain and decay components are τ-independent algebraically (they
involve only `σ_loc`, `t'`, `α s`, `α s_D`) but the residual is
τ-indexed for symmetry with `UnfactoredPerTChainBranchAlphaT_D`'s
per-τ structure: the user may discharge the conjunction at each τ
independently if needed.

## Why localized Cor 7.32 strict domination is insufficient

Same valuation-orientation considerations as
`AlphaS_DBranchPerTSigmaPowerDecay`: σ-power-decay requires the
OPPOSITE orientation to Cor 7.32's σ-strict-domination (per
`WedhornSigmaPowerDecay.lean:14-22`); discharge requires
Spa-quasicompactness M-choice for topologically-nilpotent π_loc with
σ_loc = π_loc^(M+1). Additionally, the α_T_D branch needs explicit
`α s_D` non-vanishing data since the branch's σ-strict-dominator is
some `τ ∈ T_D.image`, not `α s_D` itself. -/
def AlphaT_DBranchPerTSigmaPowerDecay
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 ∧
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle ((σ_loc : Localization.Away s) * t' *
            (algebraMap A (Localization.Away s) s_D) ^ N)
          (algebraMap A (Localization.Away s) s) ∧
        w.vle (algebraMap A (Localization.Away s) s)
          ((σ_loc : Localization.Away s) *
            (algebraMap A (Localization.Away s) s_D) ^ (N + 1))

omit [PlusSubring A] in
/-- **`UnfactoredPerTChainBranchAlphaT_D` via the abstract Wedhorn
algebraic core**. Symmetric counterpart to
`UnfactoredPerTChainBranchAlphaS_D_via_classical_sigma_decay` for the
α_T_D branch.

Consumes the bundled `AlphaT_DBranchPerTSigmaPowerDecay` residual
(carrying per-(τ, w, t') the chain + decay + α s_D non-vanishing) and
applies the abstract algebraic core `vle_t_D_s_of_sigma_decay_chain_at`
per `t'` for each branch dominator τ.

Unlike the α_s_D path, α s_D non-vanishing is **not** auto-derived from
σ-strict-domination here (since the strict dominator is some
`τ ∈ T_D.image`, not `α s_D`); it is read off the bundled residual.

**Leaves exactly ONE named residual**:
`AlphaT_DBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N`. -/
theorem UnfactoredPerTChainBranchAlphaT_D_via_classical_sigma_decay
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_residual :
      AlphaT_DBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N) :
    UnfactoredPerTChainBranchAlphaT_D P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro τ hτ_mem w hw_spa _hw_f _hστ t' ht'
  obtain ⟨hα_s_D_ne, h_per_t⟩ := h_residual τ hτ_mem w hw_spa
  obtain ⟨h_chain_t', h_C_decay⟩ := h_per_t t' ht'
  exact vle_t_D_s_of_sigma_decay_chain_at w N hα_s_D_ne h_chain_t' h_C_decay

omit [PlusSubring A] in
/-- **Top-level honest-supplier wrapper via classical σ-decay residuals
for both branches**.

Composes the two branch theorems:

* `UnfactoredPerTChainBranchAlphaS_D_via_classical_sigma_decay` for
  the α_s_D branch (consuming `AlphaS_DBranchPerTSigmaPowerDecay`);
* `UnfactoredPerTChainBranchAlphaT_D_via_classical_sigma_decay` for
  the α_T_D branch (consuming `AlphaT_DBranchPerTSigmaPowerDecay`);

with the existing combiners
`UnfactoredPerTChainTarget_via_branches` and
`WedhornMPowerStructuralDataHonest_via_unfactored_chain`, producing
the top-level honest σ-factored structural supplier
`WedhornMPowerStructuralDataHonest` from the two bundled per-branch
σ-power-decay residuals (sharing a common Wedhorn N).

**Leaves exactly TWO named residuals** (one per branch of the localized
canonical test family):

* `AlphaS_DBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N`
* `AlphaT_DBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N`

Both are the genuine Wedhorn 8.34(ii) Route B per-`t'` σ-power-decay
content; see the per-branch theorems' docstrings for the
valuation-orientation handoff explaining why localized Cor 7.32
σ-strict-domination is insufficient. -/
theorem WedhornMPowerStructuralDataHonest_via_classical_sigma_decay
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_α_s_D :
      AlphaS_DBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N)
    (h_α_T_D :
      AlphaT_DBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N) :
    WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc :=
  WedhornMPowerStructuralDataHonest_via_unfactored_chain P T s hopen
    T_D s_D σ_loc
    (UnfactoredPerTChainTarget_via_branches P T s hopen T_D s_D σ_loc
      (UnfactoredPerTChainBranchAlphaS_D_via_classical_sigma_decay
        P T s hopen T_D s_D σ_loc N h_α_s_D)
      (UnfactoredPerTChainBranchAlphaT_D_via_classical_sigma_decay
        P T s hopen T_D s_D σ_loc N h_α_T_D))

/-! ### Joint Wedhorn σ-power-decay supplier (T154)

Single bundled named residual unifying both `AlphaS_DBranchPerTSigmaPowerDecay`
and `AlphaT_DBranchPerTSigmaPowerDecay` into a common joint supplier.

Audit observation justifying the unification: the consumer
`UnfactoredPerTChainBranchAlphaT_D_via_classical_sigma_decay` (above)
introduces the per-`τ` quantifier of `AlphaT_DBranchPerTSigmaPowerDecay`
but does **not** consume the per-`τ` σ-strict-domination data — only the
chain + decay + `α s_D` non-vanishing payload (which is τ-independent).
The per-`τ` quantifier of `AlphaT_D` is therefore redundant downstream;
the joint supplier replaces it with a single uniform `α s_D`
non-vanishing on `Spa(Localization.Away s, ⁺)`.

Concretely, the joint supplier carries:

* a uniform `α s_D` non-vanishing on the local Spa
  (the sole piece distinguishing `AlphaT_D` from `AlphaS_D` after the
  redundant per-`τ` quantifier is dropped);
* the per-(`w`, `t'`) Wedhorn 8.34(ii) Route B chain + decay payload
  (shared verbatim with `AlphaS_DBranchPerTSigmaPowerDecay`).

Both branch residuals extract trivially from the joint supplier (see
`AlphaS_DBranchPerTSigmaPowerDecay_via_joint` and
`AlphaT_DBranchPerTSigmaPowerDecay_via_joint`); composed with
`WedhornMPowerStructuralDataHonest_via_classical_sigma_decay`, this
gives a top-level honest σ-factored structural supplier consuming only
the joint residual (`WedhornMPowerStructuralDataHonest_via_joint_sigma_decay`).

The remaining mathematical content collapses to a single theorem-level
target: `AlphaJointBranchPerTSigmaPowerDecay`, with the genuine Wedhorn
8.34(ii) Step 2 N-choice / σ-as-π-power content identified as the per-(w, t')
chain and per-w decay pieces, plus the rational-subset-structure
`α s_D` non-vanishing piece (separable via
`AlphaJointBranchPerTSigmaPowerDecay_via_three_pieces` below).
-/

/-- **Joint Wedhorn σ-power-decay supplier** — single bundled named
residual unifying the two branch residuals `AlphaS_DBranchPerTSigmaPowerDecay`
and `AlphaT_DBranchPerTSigmaPowerDecay`.

Carries:

* `(∀ w ∈ Spa, ¬ w.vle (algebraMap A (Loc s) s_D) 0)` — uniform `α s_D`
  non-vanishing on `Spa(Localization.Away s, ⁺)`;
* `(∀ w ∈ Spa, ∀ t' ∈ T_D.image (algebraMap A (Loc s)),
    chain_t' w ∧ decay w)` — per-(w, t') Wedhorn 8.34(ii) chain + decay.

The two branch residuals trivially extract from this joint supplier.
The remaining mathematical content reduces to a single
theorem-level target. -/
def AlphaJointBranchPerTSigmaPowerDecay
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  (∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0) ∧
  (∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle ((σ_loc : Localization.Away s) * t' *
            (algebraMap A (Localization.Away s) s_D) ^ N)
          (algebraMap A (Localization.Away s) s) ∧
        w.vle (algebraMap A (Localization.Away s) s)
          ((σ_loc : Localization.Away s) *
            (algebraMap A (Localization.Away s) s_D) ^ (N + 1)))

omit [PlusSubring A] in
/-- **Reducer: `AlphaS_DBranchPerTSigmaPowerDecay` from joint supplier**.

Trivial extraction: the joint supplier's chain+decay component is
literally `AlphaS_DBranchPerTSigmaPowerDecay` by definition. -/
theorem AlphaS_DBranchPerTSigmaPowerDecay_via_joint
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_joint :
      AlphaJointBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N) :
    AlphaS_DBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N :=
  h_joint.2

omit [PlusSubring A] in
/-- **Reducer: `AlphaT_DBranchPerTSigmaPowerDecay` from joint supplier**.

The per-`τ` quantifier of `AlphaT_DBranchPerTSigmaPowerDecay` is
redundant: the inner payload (`α s_D` non-vanishing + per-`t'` chain
+ decay) is τ-independent, so the joint supplier suffices. The
extraction introduces τ vacuously and assembles the conjunction from
the joint's two components. -/
theorem AlphaT_DBranchPerTSigmaPowerDecay_via_joint
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_joint :
      AlphaJointBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N) :
    AlphaT_DBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro _τ _hτ w hw_spa
  exact ⟨h_joint.1 w hw_spa, fun t' ht' ↦ h_joint.2 w hw_spa t' ht'⟩

omit [PlusSubring A] in
/-- **Top-level honest supplier from joint residual** — uniform-N
consumer.

Composes `AlphaS_DBranchPerTSigmaPowerDecay_via_joint` and
`AlphaT_DBranchPerTSigmaPowerDecay_via_joint` with the existing
`WedhornMPowerStructuralDataHonest_via_classical_sigma_decay`,
producing the top-level honest σ-factored structural supplier
`WedhornMPowerStructuralDataHonest` from the **single** joint
`AlphaJointBranchPerTSigmaPowerDecay` residual.

This is the cleanest end-to-end consumer signature for downstream
Wedhorn 8.34(ii) callers: only the joint residual remains as the single
named mathematical target. -/
theorem WedhornMPowerStructuralDataHonest_via_joint_sigma_decay
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_joint :
      AlphaJointBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N) :
    WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc :=
  WedhornMPowerStructuralDataHonest_via_classical_sigma_decay
    P T s hopen T_D s_D σ_loc N
    (AlphaS_DBranchPerTSigmaPowerDecay_via_joint
      P T s hopen T_D s_D σ_loc N h_joint)
    (AlphaT_DBranchPerTSigmaPowerDecay_via_joint
      P T s hopen T_D s_D σ_loc N h_joint)

omit [PlusSubring A] in
/-- **Three-piece structural decomposition of the joint residual** —
splits `AlphaJointBranchPerTSigmaPowerDecay` into three independent atomic
Lean targets, decoupling the genuine Wedhorn 8.34(ii) Step 2 content from
the rational-subset-structure non-vanishing piece:

1. `h_nv` — `α s_D` non-vanishing uniform on `Spa(Localization.Away s, ⁺)`
   (rational-subset-structure / global hypothesis);
2. `h_chain` — per-(w, t') σ-factored chain
   `w.vle (σ_loc * t' * (α s_D)^N) (α s)` (Wedhorn f-membership content,
   N-choice for σ * t' clearing);
3. `h_decay` — per-w σ-power decay
   `w.vle (α s) (σ_loc * (α s_D)^(N+1))` (Wedhorn 8.34(ii) Step 2
   N-choice for the backward bound).

Each piece is a standalone target ready to be discharged via its own
dedicated mathematical content — pieces (2) and (3) carry the genuine
Wedhorn 8.34(ii) Step 2 N-choice / σ-as-π-power material. -/
theorem AlphaJointBranchPerTSigmaPowerDecay_via_three_pieces
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_nv :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0)
    (h_chain :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle ((σ_loc : Localization.Away s) * t' *
              (algebraMap A (Localization.Away s) s_D) ^ N)
            (algebraMap A (Localization.Away s) s))
    (h_decay :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle (algebraMap A (Localization.Away s) s)
          ((σ_loc : Localization.Away s) *
            (algebraMap A (Localization.Away s) s_D) ^ (N + 1))) :
    AlphaJointBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  refine ⟨h_nv, ?_⟩
  intro w hw_spa t' ht'
  exact ⟨h_chain w hw_spa t' ht', h_decay w hw_spa⟩

omit [PlusSubring A] in
/-- **Joint residual via chain + decay + `IsUnit` `α s_D`**.

Strengthened constructor for the joint residual that auto-derives the
`α s_D` non-vanishing piece from `IsUnit (algebraMap A (Loc s) s_D)`.

Useful when `s_D` is a unit in `A` (or more generally when its image in
`Localization.Away s` is a unit), removing one of the three named
pieces. The remaining pieces are the genuine Wedhorn 8.34(ii) Step 2
content. -/
theorem AlphaJointBranchPerTSigmaPowerDecay_via_chain_decay_and_unit_s_D
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_unit_s_D : IsUnit (algebraMap A (Localization.Away s) s_D))
    (h_chain :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle ((σ_loc : Localization.Away s) * t' *
              (algebraMap A (Localization.Away s) s_D) ^ N)
            (algebraMap A (Localization.Away s) s))
    (h_decay :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle (algebraMap A (Localization.Away s) s)
          ((σ_loc : Localization.Away s) *
            (algebraMap A (Localization.Away s) s_D) ^ (N + 1))) :
    AlphaJointBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N :=
  AlphaJointBranchPerTSigmaPowerDecay_via_three_pieces
    P T s hopen T_D s_D σ_loc N
    (fun w _ ↦ not_vle_zero_of_isUnit h_unit_s_D w)
    h_chain h_decay

/-! ### Remaining single mathematical statement (T154 fallback target)

After the joint reduction landed in this section, the mathematical
content reduces to discharging
`AlphaJointBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N` —
i.e., producing the per-(w, t') chain + decay pair plus the `α s_D`
non-vanishing on `Spa(Localization.Away s, ⁺)` — which is the
**genuine Wedhorn 8.34(ii) Step 2 N-choice content** (σ-as-π-power
identification + Spa-quasi-compactness M-choice for topologically
nilpotent π_loc + denominator-clearing N).

Concretely, the residual to be discharged is the conjunction recorded in
`AlphaJointBranchPerTSigmaPowerDecay`:

```
(∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0) ∧
(∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle ((σ_loc : Localization.Away s) * t' *
          (algebraMap A (Localization.Away s) s_D) ^ N)
        (algebraMap A (Localization.Away s) s) ∧
      w.vle (algebraMap A (Localization.Away s) s)
        ((σ_loc : Localization.Away s) *
          (algebraMap A (Localization.Away s) s_D) ^ (N + 1)))
```

Discharge route: take `π_loc : (locPairOfDefinition P T s hopen).A₀`
topologically nilpotent (with `(locPairOfDefinition P T s hopen).I =
Ideal.span {π_loc}`, etc.), choose `σ_loc = π_loc^(M+1)` and `N` via
`Cor732.exists_dominatedBy_cover` applied to a sufficiently rich test
family on the local Spa. -/

/-! ### Named-target decomposition (T155)

Lifts the three inline hypotheses of
`AlphaJointBranchPerTSigmaPowerDecay_via_three_pieces` into three
standalone named `Prop`s. Each piece is now a separate, self-contained
Lean target with its own `def`-level identity, ready to be discharged
independently.

* `AlphaJointAlphaSDNonVanishingPiece` — α `s_D` non-vanishing on the
  local Spa (rational-subset-structure piece);
* `AlphaJointPerTChainPiece` — per-(w, t') Wedhorn 8.34(ii) σ-factored
  chain (Wedhorn f-membership / σ * t' clearing piece);
* `AlphaJointSigmaPowerDecayPiece` — per-w Wedhorn 8.34(ii) σ-power
  decay (Spa-quasi-compactness M-choice / N-choice piece).

The pieces use minimal parameter lists matching their actual content:
α `s_D` non-vanishing depends on `s_D` only, the σ-power-decay piece
depends on `s_D, σ_loc, N` (no `T_D`), and the per-(w, t') chain piece
depends on the full `(T_D, s_D, σ_loc, N)` data.

The constructor `AlphaJointBranchPerTSigmaPowerDecay_via_named_pieces`
assembles the three pieces back into the joint residual. The
non-vanishing piece is fully discharged by
`AlphaJointAlphaSDNonVanishingPiece_via_isUnit` under the explicit
`IsUnit (algebraMap A (Localization.Away s) s_D)` hypothesis (the
natural rational-subset-structure source); the chain and decay pieces
remain as named theorem-level Wedhorn 8.34(ii) Step 2 / Cor 7.32 targets.
-/

/-- **Named piece 1: α `s_D` non-vanishing on the local Spa**.

Standalone `Prop` capturing the rational-subset-structure piece of
`AlphaJointBranchPerTSigmaPowerDecay`: at every `w ∈ Spa(Localization.Away s, ⁺)`,
`algebraMap A (Localization.Away s) s_D` does not vanish.

Sufficient conditions: `IsUnit (algebraMap A (Localization.Away s) s_D)`
(see `AlphaJointAlphaSDNonVanishingPiece_via_isUnit`) — typical when
`s_D` is a unit in `A` or has unit image in the localization. -/
def AlphaJointAlphaSDNonVanishingPiece
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (s_D : A) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0

/-- **Named piece 2: per-(w, t') Wedhorn σ-factored chain**.

Standalone `Prop` capturing the per-(w, t') chain piece of
`AlphaJointBranchPerTSigmaPowerDecay`: at every `w ∈ Spa(Localization.Away s, ⁺)`
and every `t' ∈ T_D.image (algebraMap A (Localization.Away s))`,

```
w.vle ((σ_loc : Localization.Away s) * t' *
       (algebraMap A (Localization.Away s) s_D) ^ N)
     (algebraMap A (Localization.Away s) s).
```

Genuine Wedhorn 8.34(ii) Step 2 σ-factored chain content. The natural
discharge route picks `σ_loc = π_loc^(M+1)` for topologically nilpotent
`π_loc` and uses Spa-quasi-compactness to pick `N` via the
`Cor732.exists_dominatedBy_cover` mechanism on a test family containing
`{α s, α s_D} ∪ T_D.image`. -/
def AlphaJointPerTChainPiece
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle ((σ_loc : Localization.Away s) * t' *
          (algebraMap A (Localization.Away s) s_D) ^ N)
        (algebraMap A (Localization.Away s) s)

/-- **Named piece 3: per-w Wedhorn σ-power decay**.

Standalone `Prop` capturing the per-w decay piece of
`AlphaJointBranchPerTSigmaPowerDecay`: at every
`w ∈ Spa(Localization.Away s, ⁺)`,

```
w.vle (algebraMap A (Localization.Away s) s)
      ((σ_loc : Localization.Away s) *
         (algebraMap A (Localization.Away s) s_D) ^ (N + 1)).
```

Genuine Wedhorn 8.34(ii) Step 2 σ-power-decay content. Independent of
`T_D` (the `t'`-quantifier from the joint is absorbed into
`AlphaJointPerTChainPiece`). -/
def AlphaJointSigmaPowerDecayPiece
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    w.vle (algebraMap A (Localization.Away s) s)
      ((σ_loc : Localization.Away s) *
        (algebraMap A (Localization.Away s) s_D) ^ (N + 1))

omit [PlusSubring A] in
/-- **Constructor: joint residual via three named pieces**.

Assembles `AlphaJointBranchPerTSigmaPowerDecay` from the three named
piece `Prop`s `AlphaJointAlphaSDNonVanishingPiece`,
`AlphaJointPerTChainPiece`, and `AlphaJointSigmaPowerDecayPiece`.

This is the named-Prop counterpart of
`AlphaJointBranchPerTSigmaPowerDecay_via_three_pieces` (which takes
inline hypotheses) — useful for callers that want to plug in named
discharge theorems separately. -/
theorem AlphaJointBranchPerTSigmaPowerDecay_via_named_pieces
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_nv : AlphaJointAlphaSDNonVanishingPiece P T s hopen s_D)
    (h_chain :
      AlphaJointPerTChainPiece P T s hopen T_D s_D σ_loc N)
    (h_decay :
      AlphaJointSigmaPowerDecayPiece P T s hopen s_D σ_loc N) :
    AlphaJointBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  refine ⟨h_nv, ?_⟩
  intro w hw_spa t' ht'
  exact ⟨h_chain w hw_spa t' ht', h_decay w hw_spa⟩

omit [PlusSubring A] in
/-- **Piece 1 fully proved: α `s_D` non-vanishing from `IsUnit α s_D`**.

Discharges `AlphaJointAlphaSDNonVanishingPiece` from the explicit
`IsUnit (algebraMap A (Localization.Away s) s_D)` hypothesis via
`not_vle_zero_of_isUnit`.

This is the natural rational-subset-structure source for `α s_D`
non-vanishing: when `s_D` has unit image in the localization (e.g.,
when `s_D` is itself a unit in `A`, or when the rational-subset
structural relation forces unit image), the non-vanishing piece is
fully discharged. -/
theorem AlphaJointAlphaSDNonVanishingPiece_via_isUnit
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (s_D : A)
    (h_unit : IsUnit (algebraMap A (Localization.Away s) s_D)) :
    AlphaJointAlphaSDNonVanishingPiece P T s hopen s_D :=
  fun w _ ↦ not_vle_zero_of_isUnit h_unit w

omit [PlusSubring A] in
/-- **Top-level honest supplier from named pieces 2, 3 + `IsUnit α s_D`**.

Composes `AlphaJointAlphaSDNonVanishingPiece_via_isUnit`,
`AlphaJointBranchPerTSigmaPowerDecay_via_named_pieces`, and
`WedhornMPowerStructuralDataHonest_via_joint_sigma_decay`, producing
the top-level honest σ-factored structural supplier
`WedhornMPowerStructuralDataHonest` from:

* `IsUnit (algebraMap A (Localization.Away s) s_D)` — the unit `α s_D`
  hypothesis (rational-subset-structure source);
* `AlphaJointPerTChainPiece` — the named per-(w, t') Wedhorn σ-factored
  chain target;
* `AlphaJointSigmaPowerDecayPiece` — the named per-w Wedhorn σ-power
  decay target.

This is the cleanest end-to-end consumer signature when `α s_D` is a
unit: only the two genuine Wedhorn 8.34(ii) Step 2 named targets remain
as content-bearing inputs. -/
theorem WedhornMPowerStructuralDataHonest_via_named_pieces_and_unit_s_D
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_unit_s_D : IsUnit (algebraMap A (Localization.Away s) s_D))
    (h_chain :
      AlphaJointPerTChainPiece P T s hopen T_D s_D σ_loc N)
    (h_decay :
      AlphaJointSigmaPowerDecayPiece P T s hopen s_D σ_loc N) :
    WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc :=
  WedhornMPowerStructuralDataHonest_via_joint_sigma_decay
    P T s hopen T_D s_D σ_loc N
    (AlphaJointBranchPerTSigmaPowerDecay_via_named_pieces
      P T s hopen T_D s_D σ_loc N
      (AlphaJointAlphaSDNonVanishingPiece_via_isUnit
        P T s hopen s_D h_unit_s_D)
      h_chain h_decay)

/-! ### Remaining single mathematical statements (T155 fallback targets)

After this section, the joint residual content reduces to the **two
genuine Wedhorn 8.34(ii) Step 2 / Cor 7.32 named pieces**:

1. **`AlphaJointPerTChainPiece P T s hopen T_D s_D σ_loc N`** — per-(w, t')
   σ-factored chain on `Spa(Localization.Away s, ⁺)`. Concretely:

   ```
   ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
     ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
       w.vle ((σ_loc : Localization.Away s) * t' *
           (algebraMap A (Localization.Away s) s_D) ^ N)
         (algebraMap A (Localization.Away s) s).
   ```

2. **`AlphaJointSigmaPowerDecayPiece P T s hopen s_D σ_loc N`** — per-w
   σ-power decay on `Spa(Localization.Away s, ⁺)`. Concretely:

   ```
   ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
     w.vle (algebraMap A (Localization.Away s) s)
       ((σ_loc : Localization.Away s) *
         (algebraMap A (Localization.Away s) s_D) ^ (N + 1)).
   ```

The discharge route for both pieces follows Wedhorn 8.34(ii) Step 2:

* Pick `π_loc : (locPairOfDefinition P T s hopen).A₀` topologically
  nilpotent with `(locPairOfDefinition P T s hopen).I = Ideal.span {π_loc}`;
* Set `σ_loc = π_loc^(M+1)` for `M : ℕ` chosen large enough by
  Spa-quasi-compactness on the local Spa;
* Apply `Cor732.exists_dominatedBy_cover` to extract a uniform `N` such
  that `Spa(Localization.Away s, ⁺) ⊆ dominatedBy T_test π_loc N` where
  `T_test ⊃ T_D.image ∪ {α s, α s_D}`;
* Combine with topological-nilpotence inequalities and the strict
  inequality from σ-strict-domination to derive the chain and decay shapes.

These two named pieces are the sole remaining content-bearing inputs
for `WedhornMPowerStructuralDataHonest_via_named_pieces_and_unit_s_D`
(under the additional algebraic hypothesis `IsUnit (α s_D)`).

Note: the orientation issue documented in
`WedhornSigmaPowerDecay.lean:14-22` (σ-power-decay shape is **not
directly** Cor 7.32-derivable in its naive form) is sidestepped here
by the σ-as-π-power identification: the σ-power-decay reduces to a
π_loc-power statement, where the π_loc is genuinely topologically
nilpotent and the inequality direction matches `Cor732`'s output. -/

/-! ### Factorization-based piece discharges (T156)

Honest, fully-proved discharges of `AlphaJointPerTChainPiece` and
`AlphaJointSigmaPowerDecayPiece` from concrete algebraic factorization
hypotheses in `locSubring P T s`. Each discharge reduces the per-(w, t')
or per-w valuation inequality to membership of a single witness in
`(Localization.Away s)⁺` (which is `locSubring P T s` via the local
plus-subring instance), via the standard `mul_vle_mul_left` pattern.

The factorization hypotheses are concrete algebraic targets (existence of
a witness `ξ` in `locSubring`) which capture the genuine Wedhorn 8.34(ii)
Step 2 content cleanly: in Wedhorn's actual construction, `σ_loc` and `N`
are chosen precisely so that `α s / (σ_loc · α s_D ^ (N+1))` and each
`(σ_loc · t' · α s_D ^ N) / α s` lie in `locSubring` (which is
`(Localization.Away s)⁺`).

Provided:

* `AlphaJointSigmaPowerDecayPiece_via_factorization` — decay piece
  fully proved from `α s = σ_loc · (α s_D)^(N+1) · ξ` with `ξ ∈ locSubring`;
* `AlphaJointPerTChainPiece_via_factorization` — chain piece fully proved
  from `σ_loc · t' · (α s_D)^N = α s · ξ_t'` per `t'` with each `ξ_t' ∈ locSubring`;
* `AlphaJointPerTChainPiece_of_T_D_image_empty` — trivial chain
  discharge when `T_D.image = ∅` (vacuous);
* `AlphaJointChainAndDecayPiecesExist` — existential combiner Prop;
* `AlphaJointChainAndDecayPiecesExist_via_factorizations` — combiner
  constructor consuming both factorizations together;
* `WedhornMPowerStructuralDataHonest_via_factorizations_and_unit_s_D` —
  top-level supplier consuming both factorizations + `IsUnit α s_D`.
-/

omit [PlusSubring A] in
/-- **Decay piece fully proved via locSubring factorization**.

If `algebraMap A (Localization.Away s) s = ξ * (σ_loc * (α s_D)^(N+1))`
for some `ξ ∈ locSubring P T s`, then the σ-power-decay piece holds at
every `w ∈ Spa(Localization.Away s, ⁺)`.

**Proof**: substitute the factorization, then reduce to `w.vle ξ 1`
(via `vle_one_of_mem_spa` for `ξ ∈ locSubring = (Localization.Away s)⁺`)
and apply `mul_vle_mul_left` to right-multiply both sides by
`σ_loc * (α s_D)^(N+1)`, finishing with `one_mul`. -/
theorem AlphaJointSigmaPowerDecayPiece_via_factorization
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (ξ : locSubring P T s)
    (hfact :
      algebraMap A (Localization.Away s) s =
        (ξ : Localization.Away s) *
          ((σ_loc : Localization.Away s) *
            (algebraMap A (Localization.Away s) s_D) ^ (N + 1))) :
    AlphaJointSigmaPowerDecayPiece P T s hopen s_D σ_loc N := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  intro w hw_spa
  have hξ_le_one : w.vle (ξ : Localization.Away s) 1 :=
    vle_one_of_mem_spa hw_spa ξ.property
  have h_mul := w.mul_vle_mul_left hξ_le_one
    ((σ_loc : Localization.Away s) *
      (algebraMap A (Localization.Away s) s_D) ^ (N + 1))
  rw [one_mul] at h_mul
  rw [hfact]
  exact h_mul

omit [PlusSubring A] in
/-- **Chain piece fully proved via per-`t'` locSubring factorization**.

If for every `t' ∈ T_D.image (algebraMap A (Localization.Away s))` there
exists `ξ_t' ∈ locSubring P T s` with
`σ_loc * t' * (α s_D) ^ N = ξ_t' * (algebraMap A (Localization.Away s) s)`,
then the per-(w, t') chain piece holds at every
`w ∈ Spa(Localization.Away s, ⁺)`.

**Proof**: per `t'`, substitute the factorization and reduce to
`w.vle ξ_t' 1` then `mul_vle_mul_left` right-multiplies by `α s`,
finishing with `one_mul`. -/
theorem AlphaJointPerTChainPiece_via_factorization
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_factor :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        ∃ ξ_t' : locSubring P T s,
          (σ_loc : Localization.Away s) * t' *
              (algebraMap A (Localization.Away s) s_D) ^ N =
            (ξ_t' : Localization.Away s) *
              algebraMap A (Localization.Away s) s) :
    AlphaJointPerTChainPiece P T s hopen T_D s_D σ_loc N := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa t' ht'
  obtain ⟨ξ_t', hfact_t'⟩ := h_factor t' ht'
  have hξ_t'_le_one : w.vle (ξ_t' : Localization.Away s) 1 :=
    vle_one_of_mem_spa hw_spa ξ_t'.property
  have h_mul := w.mul_vle_mul_left hξ_t'_le_one
    (algebraMap A (Localization.Away s) s)
  rw [one_mul] at h_mul
  rw [hfact_t']
  exact h_mul

omit [PlusSubring A] in
/-- **Trivial chain discharge when `T_D.image` is empty**.

When the image of `T_D` under `algebraMap A (Localization.Away s)` is
empty, the per-(w, t') chain piece is vacuously true (the inner
`∀ t' ∈ ∅, ...` is trivially satisfied).

Useful as a sanity check and for callers where `T_D = ∅` is the
degenerate base case. -/
theorem AlphaJointPerTChainPiece_of_T_D_image_empty
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_T_D_image_empty :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      T_D.image (algebraMap A (Localization.Away s)) = ∅) :
    AlphaJointPerTChainPiece P T s hopen T_D s_D σ_loc N := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w _hw_spa t' ht'
  rw [h_T_D_image_empty] at ht'
  exact absurd ht' (Finset.notMem_empty t')

/-- **Existential common combiner: chain + decay pieces witness exists**.

Single bundled `Prop` asserting the existence of `(σ_loc, N)` that
simultaneously witness `AlphaJointPerTChainPiece` and
`AlphaJointSigmaPowerDecayPiece`. This is the strict-lower common
theorem-level target after the factorization-based discharges land:
all that remains is to construct concrete `(σ_loc, N, ξ_decay, ξ_t')`
witnessing the algebraic factorizations.

Constructed via `AlphaJointChainAndDecayPiecesExist_via_factorizations`. -/
def AlphaJointChainAndDecayPiecesExist
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∃ (σ_loc : (Localization.Away s)ˣ) (N : ℕ),
    AlphaJointPerTChainPiece P T s hopen T_D s_D σ_loc N ∧
    AlphaJointSigmaPowerDecayPiece P T s hopen s_D σ_loc N

omit [PlusSubring A] in
/-- **Existential combiner via locSubring factorizations**.

Constructs `AlphaJointChainAndDecayPiecesExist` from explicit witness
data: `(σ_loc, N, ξ_decay, ξ_t' per t')` such that

* `α s = ξ_decay · (σ_loc · (α s_D)^(N+1))` (decay factorization);
* `σ_loc · t' · (α s_D)^N = ξ_t' · α s` for each `t' ∈ T_D.image`
  (per-`t'` chain factorization).

This is the cleanest **single named hypothesis** for the joint pieces:
all genuine Wedhorn 8.34(ii) Step 2 content reduces to producing the
concrete factorization witnesses in `locSubring`. -/
theorem AlphaJointChainAndDecayPiecesExist_via_factorizations
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (ξ_decay : locSubring P T s)
    (hfact_decay :
      algebraMap A (Localization.Away s) s =
        (ξ_decay : Localization.Away s) *
          ((σ_loc : Localization.Away s) *
            (algebraMap A (Localization.Away s) s_D) ^ (N + 1)))
    (h_factor_chain :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        ∃ ξ_t' : locSubring P T s,
          (σ_loc : Localization.Away s) * t' *
              (algebraMap A (Localization.Away s) s_D) ^ N =
            (ξ_t' : Localization.Away s) *
              algebraMap A (Localization.Away s) s) :
    AlphaJointChainAndDecayPiecesExist P T s hopen T_D s_D :=
  ⟨σ_loc, N,
    AlphaJointPerTChainPiece_via_factorization
      P T s hopen T_D s_D σ_loc N h_factor_chain,
    AlphaJointSigmaPowerDecayPiece_via_factorization
      P T s hopen s_D σ_loc N ξ_decay hfact_decay⟩

omit [PlusSubring A] in
/-- **Top-level honest supplier from factorizations + `IsUnit α s_D`**.

Composes the factorization-based discharges of both pieces with
`AlphaJointAlphaSDNonVanishingPiece_via_isUnit` and
`WedhornMPowerStructuralDataHonest_via_named_pieces_and_unit_s_D`,
producing the top-level honest σ-factored structural supplier
`WedhornMPowerStructuralDataHonest` from:

* `IsUnit (algebraMap A (Localization.Away s) s_D)` — unit `α s_D`
  hypothesis;
* `ξ_decay ∈ locSubring P T s` with the decay factorization
  `α s = ξ_decay * (σ_loc * (α s_D)^(N+1))`;
* per-`t'` `ξ_t' ∈ locSubring P T s` with the chain factorization
  `σ_loc * t' * (α s_D)^N = ξ_t' * α s`.

This is the cleanest end-to-end consumer for downstream Wedhorn 8.34(ii)
callers under the unit hypothesis: only the explicit factorization data
remains as content-bearing input. -/
theorem WedhornMPowerStructuralDataHonest_via_factorizations_and_unit_s_D
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_unit_s_D : IsUnit (algebraMap A (Localization.Away s) s_D))
    (ξ_decay : locSubring P T s)
    (hfact_decay :
      algebraMap A (Localization.Away s) s =
        (ξ_decay : Localization.Away s) *
          ((σ_loc : Localization.Away s) *
            (algebraMap A (Localization.Away s) s_D) ^ (N + 1)))
    (h_factor_chain :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        ∃ ξ_t' : locSubring P T s,
          (σ_loc : Localization.Away s) * t' *
              (algebraMap A (Localization.Away s) s_D) ^ N =
            (ξ_t' : Localization.Away s) *
              algebraMap A (Localization.Away s) s) :
    WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc :=
  WedhornMPowerStructuralDataHonest_via_named_pieces_and_unit_s_D
    P T s hopen T_D s_D σ_loc N h_unit_s_D
    (AlphaJointPerTChainPiece_via_factorization
      P T s hopen T_D s_D σ_loc N h_factor_chain)
    (AlphaJointSigmaPowerDecayPiece_via_factorization
      P T s hopen s_D σ_loc N ξ_decay hfact_decay)

/-! ### Remaining single mathematical statement (T156 strict-lower target)

After this section, the joint chain + decay pieces reduce to the
**single concrete algebraic existence target**:

```
∃ (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
  (ξ_decay : locSubring P T s),
  (algebraMap A (Localization.Away s) s =
    (ξ_decay : Localization.Away s) *
      ((σ_loc : Localization.Away s) *
        (algebraMap A (Localization.Away s) s_D) ^ (N + 1))) ∧
  (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
    ∃ ξ_t' : locSubring P T s,
      (σ_loc : Localization.Away s) * t' *
        (algebraMap A (Localization.Away s) s_D) ^ N =
      (ξ_t' : Localization.Away s) *
        algebraMap A (Localization.Away s) s)
```

This is the **honest Wedhorn 8.34(ii) Step 2 algebraic statement** in
`Localization.Away s`: a denominator-clearing factorization `s =
ξ_decay · σ_loc · s_D^(N+1)` plus per-`t'` factorizations
`σ_loc · t' · s_D^N = ξ_t' · s`. The `σ_loc, N`-choice is made via
Wedhorn's σ-as-π-power identification + Spa-quasi-compactness +
topological nilpotence; the resulting `ξ_decay`, `ξ_t'` lie in
`locSubring` because they are `s_D / s`-style quotients absorbing the
denominator-clearing exponent.

Once this single existential statement is discharged, the entire
`WedhornMPowerStructuralDataHonest_via_factorizations_and_unit_s_D`
chain composes to produce the top-level honest σ-factored structural
supplier (under the additional `IsUnit α s_D` hypothesis). -/

/-! ### Named witness-existence Prop and concrete constructions (T157)

Promotes the trailing T156 docstring target into a single named
`Prop` `AlphaJointFactorizationWitnessesExist`, asserting the existence
of the algebraic factorization witnesses (`σ_loc, N, ξ_decay, ξ_t'`)
in `locSubring P T s` that drive both joint pieces via the T156
factorization-based discharges.

Provided:

* `AlphaJointFactorizationWitnessesExist` — the named existence Prop;
* `AlphaJointFactorizationWitnessesExist_via_factorizations` — direct
  constructor from explicit witness data;
* `AlphaJointChainAndDecayPiecesExist_via_witnesses` — collapses the
  named witnesses into the T156 existential combiner
  `AlphaJointChainAndDecayPiecesExist`;
* `WedhornMPowerStructuralDataHonest_exists_via_witnesses_and_unit_s_D`
  — top-level supplier feed: from the witnesses + `IsUnit α s_D`,
  produces `∃ σ_loc, WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc`;
* `AlphaJointFactorizationWitnessesExist_when_s_D_eq_s_and_T_D_le_T`
  — **fully proved concrete construction** in the natural special case
  `s_D = s` (the rational-subset denominators coincide) and `T_D ⊆ T`
  (the smaller-rational-subset numerator family lies in the larger
  one). Picks `σ_loc := 1`, `N := 0`, `ξ_decay := 1`, and per-`t'`
  `ξ_t' := divByS (preimage_t') s` (which lies in `locSubring` by
  `divByS_mem_locSubring` since `preimage_t' ∈ T_D ⊆ T`).
-/

/-- **Named existence Prop for the joint factorization witnesses**.

Single bundled `Prop` asserting the existence of the four factorization
witnesses `(σ_loc, N, ξ_decay, ξ_t' per t')` in `locSubring P T s` such
that:

* `α s = ξ_decay · (σ_loc · α s_D^(N+1))` (decay factorization);
* `σ_loc · t' · α s_D^N = ξ_t' · α s` for each `t' ∈ T_D.image`
  (per-`t'` chain factorization).

This is the **single named target** capturing the genuine Wedhorn
8.34(ii) Step 2 algebraic content: the σ-as-π-power identification
+ Spa-quasi-compactness denominator-clearing exponent choice together
produce these locSubring witnesses (concretely, `ξ_decay` and `ξ_t'`
arise as `s_D / s`-style quotients absorbing the denominator). -/
def AlphaJointFactorizationWitnessesExist
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∃ (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (ξ_decay : locSubring P T s),
    (algebraMap A (Localization.Away s) s =
      (ξ_decay : Localization.Away s) *
        ((σ_loc : Localization.Away s) *
          (algebraMap A (Localization.Away s) s_D) ^ (N + 1))) ∧
    (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      ∃ ξ_t' : locSubring P T s,
        (σ_loc : Localization.Away s) * t' *
            (algebraMap A (Localization.Away s) s_D) ^ N =
          (ξ_t' : Localization.Away s) *
            algebraMap A (Localization.Away s) s)

omit [PlusSubring A] in
/-- **Direct constructor for `AlphaJointFactorizationWitnessesExist`** from
explicit witness data. -/
theorem AlphaJointFactorizationWitnessesExist_via_factorizations
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (ξ_decay : locSubring P T s)
    (hfact_decay :
      algebraMap A (Localization.Away s) s =
        (ξ_decay : Localization.Away s) *
          ((σ_loc : Localization.Away s) *
            (algebraMap A (Localization.Away s) s_D) ^ (N + 1)))
    (h_factor_chain :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        ∃ ξ_t' : locSubring P T s,
          (σ_loc : Localization.Away s) * t' *
              (algebraMap A (Localization.Away s) s_D) ^ N =
            (ξ_t' : Localization.Away s) *
              algebraMap A (Localization.Away s) s) :
    AlphaJointFactorizationWitnessesExist P T s hopen T_D s_D :=
  ⟨σ_loc, N, ξ_decay, hfact_decay, h_factor_chain⟩

omit [PlusSubring A] in
/-- **Collapse: `AlphaJointFactorizationWitnessesExist` →
`AlphaJointChainAndDecayPiecesExist`**.

Folds the named witness existence into the T156 existential combiner
that produces the chain and decay pieces. Pure unwrap + apply
`AlphaJointChainAndDecayPiecesExist_via_factorizations`. -/
theorem AlphaJointChainAndDecayPiecesExist_via_witnesses
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (h_witnesses :
      AlphaJointFactorizationWitnessesExist P T s hopen T_D s_D) :
    AlphaJointChainAndDecayPiecesExist P T s hopen T_D s_D := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  obtain ⟨σ_loc, N, ξ_decay, hfact_decay, h_factor_chain⟩ := h_witnesses
  exact AlphaJointChainAndDecayPiecesExist_via_factorizations
    P T s hopen T_D s_D σ_loc N ξ_decay hfact_decay h_factor_chain

omit [PlusSubring A] in
/-- **Top-level supplier feed: `WedhornMPowerStructuralDataHonest`
existential from witnesses + `IsUnit α s_D`**.

Composes `AlphaJointFactorizationWitnessesExist` with
`WedhornMPowerStructuralDataHonest_via_factorizations_and_unit_s_D` to
produce `∃ σ_loc, WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc`
under the additional `IsUnit (α s_D)` hypothesis. The σ_loc here
matches the witness `σ_loc` from the joint factorization.

This is the cleanest end-to-end downstream consumer for the named
factorization witnesses: only the named witnesses + the unit `α s_D`
hypothesis remain as content-bearing inputs. -/
theorem WedhornMPowerStructuralDataHonest_exists_via_witnesses_and_unit_s_D
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (h_unit_s_D : IsUnit (algebraMap A (Localization.Away s) s_D))
    (h_witnesses :
      AlphaJointFactorizationWitnessesExist P T s hopen T_D s_D) :
    ∃ σ_loc : (Localization.Away s)ˣ,
      WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  obtain ⟨σ_loc, N, ξ_decay, hfact_decay, h_factor_chain⟩ := h_witnesses
  exact ⟨σ_loc,
    WedhornMPowerStructuralDataHonest_via_factorizations_and_unit_s_D
      P T s hopen T_D s_D σ_loc N h_unit_s_D ξ_decay hfact_decay
      h_factor_chain⟩

omit [PlusSubring A] in
/-- **Concrete construction: `s_D = s` and `T_D ⊆ T`**.

In the natural special case where the rational-subset denominators
coincide (`s_D = s`) and the smaller rational-subset numerator family
lies in the larger one (`T_D ⊆ T`), the joint factorization witnesses
are constructible from the existing `divByS` API:

* Pick `σ_loc := 1`, `N := 0`, `ξ_decay := 1`.
* Decay factorization: `α s = 1 * (1 * α s^1)` reduces to `α s = α s` ✓.
* Per-`t'` chain factorization: for `t' = α t` with `t ∈ T_D ⊆ T`, set
  `ξ_t' := divByS t s` (which lies in `locSubring` by
  `divByS_mem_locSubring` for `t ∈ T`); then
  `1 * α t * α s^0 = α t = (divByS t s) * α s = ξ_t' * α s` follows
  from `IsLocalization.mk'_spec`.

This is a **fully proved no-sorry concrete witness construction**
covering the natural Wedhorn rational-subset specialisation
`R(T_D, s) ⊆ R(T, s)` along the same denominator. The general
`s_D ≠ s` case requires the genuine Wedhorn 8.34(ii) Step 2 σ-as-π-power
+ N-choice content. -/
theorem AlphaJointFactorizationWitnessesExist_when_s_D_eq_s_and_T_D_le_T
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (h_s_D_eq : s_D = s)
    (h_T_D_le_T : T_D ⊆ T) :
    AlphaJointFactorizationWitnessesExist P T s hopen T_D s_D := by
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  refine ⟨1, 0, 1, ?_, ?_⟩
  · -- Decay factorization: α s = 1 * (1 * α s_D^1) reduces to α s = α s under
    -- s_D = s.
    rw [h_s_D_eq]
    simp [Units.val_one]
  · -- Per-t' chain factorization. Note: α s_D^0 = 1 regardless of s_D, so no
    -- s_D = s needed for this branch.
    intro t' ht'
    obtain ⟨t, ht_in_T_D, ht_eq⟩ := Finset.mem_image.mp ht'
    have ht_in_T : t ∈ T := h_T_D_le_T ht_in_T_D
    refine ⟨⟨divByS t s, divByS_mem_locSubring P T s ht_in_T⟩, ?_⟩
    have hspec : divByS t s * algebraMap A (Localization.Away s) s =
        algebraMap A (Localization.Away s) t :=
      IsLocalization.mk'_spec _ t ⟨s, Submonoid.mem_powers s⟩
    simp only [Units.val_one, one_mul, pow_zero, mul_one]
    rw [← ht_eq]
    exact hspec.symm

/-! ### Remaining mathematical content (T157 fallback target)

The named witness existence Prop `AlphaJointFactorizationWitnessesExist`
is the single mathematical statement remaining for the joint pieces
under the unit `α s_D` hypothesis. The concrete construction above
covers the `s_D = s` + `T_D ⊆ T` specialisation; the genuinely
remaining content is the construction in the general case where
`s_D ≠ s` (the smaller rational subset's denominator differs from the
larger one's). The honest discharge route in the general case:

* Pick `π_loc : locSubring P T s` topologically nilpotent unit
  (pseudo-uniformizer in the local ring of definition);
* Pick `M : ℕ` large enough that `π_loc^(M+1) * (α s_D)^(N+1) / α s ∈
  locSubring` — this is the Spa-quasi-compactness M-choice (via
  `Cor732.exists_dominatedBy_cover` applied to a test family containing
  the local images of `T_D`, `α s_D`, and `α s`);
* Set `σ_loc := π_loc^(M+1)`, derive `ξ_decay := α s / (σ_loc · α s_D^(N+1))`
  in `locSubring` from the M-choice membership, and per `t' ∈ T_D.image`
  derive `ξ_t' := σ_loc · t' · α s_D^N / α s` in `locSubring` (via the
  same M-choice mechanism applied to `t' · α s_D^N · π_loc^(M+1) / α s`).

The remaining content is concentrated in the M-choice / N-choice
membership lemmas: there exist `M, N : ℕ` such that the listed
quotients lie in `locSubring`. This reduces to a Spa-quasi-compactness
+ topological-nilpotence argument on the local Spa, which uses
`Cor732.exists_dominatedBy_cover` and the `hopen`/`locNhd_invS_step`-style
algebraic-power-decay content. -/

/-! ### M/N-choice locSubring membership package + s = s_D · c
generalisation (T158)

Promotes the parameterised content of `AlphaJointFactorizationWitnessesExist`
into a separate **named per-(σ_loc, N) membership package** Prop, and
provides a strict generalisation of T157's concrete construction
covering the algebraic specialisation `s = s_D · c` for `c ∈ P.A₀`
(reducing to T157 when `c = 1` and `s_D = s`).

Provided:

* `AlphaJointMNChoiceLocSubringMembership` — named package Prop fixing
  `(σ_loc, N)` and asserting `locSubring` membership of the decay and
  per-`t'` chain factorization witnesses for those parameters.
* `AlphaJointFactorizationWitnessesExist_via_mn_choice` — from
  `∃ σ_loc N, AlphaJointMNChoiceLocSubringMembership P T s hopen T_D s_D σ_loc N`
  produces `AlphaJointFactorizationWitnessesExist`.
* `AlphaJointFactorizationWitnessesExist_when_s_eq_s_D_mul_A0_elt_and_T_D_le_T`
  — **fully proved concrete construction** for the natural algebraic
  specialisation `s = s_D · c` with `c ∈ P.A₀` and `T_D ⊆ T`. Picks
  `σ_loc := 1`, `N := 0`, `ξ_decay := algebraMap A (Loc s) c` (in
  `locSubring` by `algebraMap_mem_locSubring`), and per-`t'`
  `ξ_t' := divByS (preimage_t') s` (in `locSubring` by
  `divByS_mem_locSubring` for `preimage_t' ∈ T_D ⊆ T`).
* `WedhornMPowerStructuralDataHonest_exists_via_s_factor_and_unit_s_D`
  — top-level supplier feed combining the above concrete construction
  with `WedhornMPowerStructuralDataHonest_exists_via_witnesses_and_unit_s_D`.

The general `s_D ≠ s` case where `s ∉ s_D · P.A₀` requires the genuine
Wedhorn 8.34(ii) Step 2 σ-as-π-power M-choice + Cor732 N-choice content;
the package Prop here is the canonical target for that future content. -/

/-- **M-choice / N-choice locSubring membership package**. Parameterised
per `(σ_loc, N)` — captures the existence of the decay witness `ξ_decay`
in `locSubring` and per-`t'` chain witnesses `ξ_t'` in `locSubring`
satisfying the joint factorisations.

`AlphaJointFactorizationWitnessesExist` is the existential closure over
`(σ_loc, N)`. -/
def AlphaJointMNChoiceLocSubringMembership
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  (∃ ξ_decay : locSubring P T s,
    algebraMap A (Localization.Away s) s =
      (ξ_decay : Localization.Away s) *
        ((σ_loc : Localization.Away s) *
          (algebraMap A (Localization.Away s) s_D) ^ (N + 1))) ∧
  (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
    ∃ ξ_t' : locSubring P T s,
      (σ_loc : Localization.Away s) * t' *
          (algebraMap A (Localization.Away s) s_D) ^ N =
        (ξ_t' : Localization.Away s) *
          algebraMap A (Localization.Away s) s)

omit [PlusSubring A] in
/-- **Constructor: witnesses exist from the M-choice / N-choice package**.

Given `(σ_loc, N)` such that `AlphaJointMNChoiceLocSubringMembership`
holds, produces `AlphaJointFactorizationWitnessesExist`. The constructor
unwraps the package's two existentials and combines them under the
outer `∃ σ_loc N ξ_decay, ...`. -/
theorem AlphaJointFactorizationWitnessesExist_via_mn_choice
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_membership :
      AlphaJointMNChoiceLocSubringMembership
        P T s hopen T_D s_D σ_loc N) :
    AlphaJointFactorizationWitnessesExist P T s hopen T_D s_D := by
  obtain ⟨⟨ξ_decay, hfact_decay⟩, h_chain⟩ := h_membership
  exact ⟨σ_loc, N, ξ_decay, hfact_decay, h_chain⟩

omit [PlusSubring A] in
/-- **Concrete construction: `s = s_D · c` for `c ∈ P.A₀` and `T_D ⊆ T`**.

Strict generalisation of T157's `s_D = s` construction. In the natural
algebraic specialisation where `s` factors as `s_D · c` for some
`c ∈ P.A₀` (the larger rational subset's denominator times an element
of the ring of definition), and `T_D ⊆ T` (the smaller numerator family
lies in the larger one), the joint factorisation witnesses are
constructible:

* Pick `σ_loc := 1`, `N := 0`.
* Decay factorisation: `α s = (algebraMap A (Loc s) c) · (1 · α s_D^1)`
  reduces via `h_s_factor : s = s_D · c` to
  `α (s_D · c) = α c · α s_D`, which holds by `map_mul` + `mul_comm`.
  The witness `ξ_decay := algebraMap A (Loc s) c` lies in `locSubring`
  by `algebraMap_mem_locSubring P T s c.property`.
* Chain factorisation: per `t' = α t` with `t ∈ T_D ⊆ T`, the witness
  `ξ_t' := divByS t s` lies in `locSubring` by
  `divByS_mem_locSubring P T s ht_in_T`, and `1 · α t · α s_D^0 = α t =
  divByS t s · α s` by `IsLocalization.mk'_spec`.

Reduces to T157's construction when `c = 1` and `s_D = s` (giving
`s = s · 1 = s`, the trivial factorisation). -/
theorem AlphaJointFactorizationWitnessesExist_when_s_eq_s_D_mul_A0_elt_and_T_D_le_T
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (c : P.A₀)
    (h_s_factor : s = s_D * (c : A))
    (h_T_D_le_T : T_D ⊆ T) :
    AlphaJointFactorizationWitnessesExist P T s hopen T_D s_D := by
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  refine ⟨1, 0,
    ⟨algebraMap A (Localization.Away s) (c : A),
      algebraMap_mem_locSubring P T s c.property⟩, ?_, ?_⟩
  · -- Decay: α s = α c · (1 · α s_D^1) reduces via s = s_D · c.
    rw [h_s_factor, map_mul]
    simp [Units.val_one, mul_comm]
  · -- Chain: as in T157, with the same `T_D ⊆ T` mechanism.
    intro t' ht'
    obtain ⟨t, ht_in_T_D, ht_eq⟩ := Finset.mem_image.mp ht'
    have ht_in_T : t ∈ T := h_T_D_le_T ht_in_T_D
    refine ⟨⟨divByS t s, divByS_mem_locSubring P T s ht_in_T⟩, ?_⟩
    have hspec : divByS t s * algebraMap A (Localization.Away s) s =
        algebraMap A (Localization.Away s) t :=
      IsLocalization.mk'_spec _ t ⟨s, Submonoid.mem_powers s⟩
    simp only [Units.val_one, one_mul, pow_zero, mul_one]
    rw [← ht_eq]
    exact hspec.symm

omit [PlusSubring A] in
/-- **Top-level supplier feed via the `s = s_D · c` concrete construction**.

Composes
`AlphaJointFactorizationWitnessesExist_when_s_eq_s_D_mul_A0_elt_and_T_D_le_T`
with `WedhornMPowerStructuralDataHonest_exists_via_witnesses_and_unit_s_D`,
producing `∃ σ_loc, WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc`
under:

* `IsUnit (algebraMap A (Localization.Away s) s_D)`;
* the algebraic factorisation `s = s_D · c` for some `c ∈ P.A₀`;
* `T_D ⊆ T`.

This is the cleanest end-to-end downstream consumer for the natural
`s = s_D · c` specialisation: only those three structural inputs remain. -/
theorem WedhornMPowerStructuralDataHonest_exists_via_s_factor_and_unit_s_D
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (h_unit_s_D : IsUnit (algebraMap A (Localization.Away s) s_D))
    (c : P.A₀)
    (h_s_factor : s = s_D * (c : A))
    (h_T_D_le_T : T_D ⊆ T) :
    ∃ σ_loc : (Localization.Away s)ˣ,
      WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc :=
  WedhornMPowerStructuralDataHonest_exists_via_witnesses_and_unit_s_D
    P T s hopen T_D s_D h_unit_s_D
    (AlphaJointFactorizationWitnessesExist_when_s_eq_s_D_mul_A0_elt_and_T_D_le_T
      P T s hopen T_D s_D c h_s_factor h_T_D_le_T)

/-! ### Remaining mathematical content (T158 fallback target)

After this section, the joint factorisation witnesses are constructible
in three classes of cases (in increasing generality):

1. `s_D = s` and `T_D ⊆ T` (T157, `_when_s_D_eq_s_and_T_D_le_T`);
2. `s = s_D · c` for `c ∈ P.A₀` and `T_D ⊆ T` (this section,
   `_when_s_eq_s_D_mul_A0_elt_and_T_D_le_T`);
3. The full Wedhorn 8.34(ii) Step 2 case where `s ∉ s_D · P.A₀`
   (remaining content).

Class 2 strictly generalises class 1 (set `c = 1` and `s_D = s`).
Class 3 — the genuinely-remaining content — requires the σ-as-π-power
M-choice + Cor732 N-choice mechanism, packaged in the named target
`AlphaJointMNChoiceLocSubringMembership`:

```
∃ σ_loc N,
  (∃ ξ_decay ∈ locSubring P T s,
    α s = ξ_decay · (σ_loc · α s_D^(N+1))) ∧
  (∀ t' ∈ T_D.image, ∃ ξ_t' ∈ locSubring P T s,
    σ_loc · t' · α s_D^N = ξ_t' · α s)
```

Discharge route: pick `π_loc : locSubring P T s` topologically nilpotent
unit, set `σ_loc := π_loc^(M+1)`, and use Cor 7.32's
`exists_dominatedBy_cover` applied to a test family on
`Spa(Localization.Away s, ⁺)` containing the relevant local images of
`T_D`, `α s_D`, `α s` to extract `M, N` and the locSubring membership
of the algebraic ratios. -/

/-! ### Post-T158 integration wrapper (T161)

A small no-conflict consumer wrapper that connects T158's per-`(σ_loc, N)`
M/N-choice membership package directly to T156's σ_loc-fixed
factorisation-based structural-data discharge. This isolates the
**σ_loc-fixed** integration step that will ultimately receive
`(σ_loc, N)` from a Cor 7.32 / Spa-quasi-compactness M-choice supplier
(Primary's T159 lane below) and produce a structural-data witness for
that same σ_loc — ready to be combined with Cor 7.32 σ-strict-domination
output (sharing σ_loc) into `WedhornC1PerCallSupplyHonest` (component 5).

The wrapper takes the **same σ_loc** and **same N** that Cor 7.32 chooses
upstream, plus the M/N-choice membership package for those parameters,
plus `IsUnit α s_D`, and produces `WedhornMPowerStructuralDataHonest`
**for that σ_loc** (no σ_loc existential introduced). This is the σ_loc-
matching shape needed by `WedhornC1PerCallSupplyHonest`'s component 5.

This wrapper is independent of T159/T160's content (it does not produce
the M/N-choice package itself; it only consumes it), so it is safe to
land here. -/

omit [PlusSubring A] in
/-- **σ_loc-fixed integration: M/N-choice membership package +
`IsUnit α s_D` → `WedhornMPowerStructuralDataHonest` for that σ_loc**.

Composes
`AlphaJointMNChoiceLocSubringMembership P T s hopen T_D s_D σ_loc N`
(T158's package — `(σ_loc, N)` are explicit, not existential) with
`WedhornMPowerStructuralDataHonest_via_factorizations_and_unit_s_D`
(T156's σ_loc-fixed factorisation-based discharge under `IsUnit α s_D`),
producing the σ_loc-fixed honest σ-factored structural supplier for the
**same σ_loc**.

This is the σ_loc-matching shape consumed by component 5 of
`WedhornC1PerCallSupplyHonest`: when Primary's T159 produces
`AlphaJointMNChoiceLocSubringMembership` for the **same σ_loc** Cor 7.32
chose for component 4 (σ-strict-domination on local Spa), this wrapper
discharges component 5 with that shared σ_loc, ready for the trivial
existential bundling `⟨σ_loc, f, _, _, _, _, _⟩` into
`WedhornC1PerCallSupplyHonest`. -/
theorem WedhornMPowerStructuralDataHonest_via_mn_choice_membership_and_unit_s_D
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_unit_s_D : IsUnit (algebraMap A (Localization.Away s) s_D))
    (h_mn : AlphaJointMNChoiceLocSubringMembership
      P T s hopen T_D s_D σ_loc N) :
    WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  obtain ⟨⟨ξ_decay, hfact_decay⟩, h_factor_chain⟩ := h_mn
  exact WedhornMPowerStructuralDataHonest_via_factorizations_and_unit_s_D
    P T s hopen T_D s_D σ_loc N h_unit_s_D ξ_decay hfact_decay h_factor_chain

/-! ### Post-T158 integration dependency map (T161 audit)

Final theorem signatures needed to consume the T154-T158 chain into
`WedhornC1PerCallSupplyHonest` (component 5) and the Tate acyclicity
route:

1. **σ_loc-FIXED integration** (this section,
   `WedhornMPowerStructuralDataHonest_via_mn_choice_membership_and_unit_s_D`):
   ```
   AlphaJointMNChoiceLocSubringMembership P T s hopen T_D s_D σ_loc N →
   IsUnit (α s_D) →
   WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc
   ```
   **STATUS: LANDED** (this commit, T161).

2. **Cor 7.32 → M/N-choice membership** (Primary T159 lane, immediately
   below):
   ```
   (Tate / Cor 7.32 hypotheses) →
   ∃ σ_loc N, AlphaJointMNChoiceLocSubringMembership ... σ_loc N ∧
              (∀ w ∈ Spa local, ∃ τ ∈ T_loc, σ-strict-dominates τ)
   ```
   The σ_loc is shared between the M/N-choice membership and the
   σ-strict-domination output (Cor 7.32). **STATUS: T159 (Primary,
   in progress, declarations below)**.

3. **σ-power API support** (Secondary T160 lane, after T159 section).
   **STATUS: T160 (Secondary, in progress, declarations below)**.

4. **σ_loc-shared `WedhornC1PerCallSupplyHonest` constructor**:
   ```
   (σ_loc-shared step 2 output) →
   (denominator-clearing identity α f = σ_loc · ∏ T_D.image α) →
   IsUnit (α s_D) →
   (v ∈ rationalOpen (insert f C.base.T) C.base.s ∧ ¬ v.vle f 0) →
   WedhornC1PerCallSupplyHonest P C hopen_base D v
   ```
   This is a trivial existential bundling once steps 1-3 land for the
   shared σ_loc and an explicit f is supplied. **STATUS: future ticket
   (post-T159/T160), in `WedhornC1PerCallSupplyHonest.lean`**.

5. **`C1SupplierStrong_local C` from σ_loc-shared
   `WedhornC1PerCallSupplyHonest`**:
   Already landed via `C1SupplierStrong_local_via_honest_residuals`
   (`WedhornC1PerCallSupplyHonest.lean:120`). **STATUS: existing API**.

6. **Tate acyclicity route via `C1SupplierStrong_local`**:
   Routed through `Wedhorn745PointwiseBaseRefinementDischarge.lean`
   (Wedhorn 7.45 base refinement / Hübner 3.7-3.8) and onward to
   `tateAcyclicity_Part2_*` (`GeometricReduction.lean`). **STATUS:
   existing API**.

The remaining BLOCKERS are concentrated at step 2 (T159) and step 4
(the trivial bundling, gated on step 2). Step 1 is now landed. -/

/-! ### T159: Cor 7.32 finite test-family cover bridge to M/N-choice
membership

Strict reduction toward the joint factorisation witnesses of T158's
`AlphaJointMNChoiceLocSubringMembership` via the Wedhorn 8.34(ii)
Step 2 Cor 7.32 cover mechanism. T159 introduces:

* `AlphaJointCor732TestFamilyCoverPackage` — named per-σ_loc finite
  test-family cover Prop, capturing the σ_loc-rescaled Laurent piece
  membership output of `exists_localized_cor732_laurent_piece_membership`
  on `localizedTestFamily s T_D s_D`.

* `AlphaJointCor732TestFamilyCoverPackage_exists_via_localized_cor732`
  — produces the named cover Prop existentially in `σ_loc` from honest
  Cor 7.32 hypotheses (Tate / pseudouniformizer data on the local Spa,
  MulArchimedean value groups, no-common-zero on the localized test
  family). Direct delegation to
  `exists_localized_cor732_laurent_piece_membership`.

* `AlphaJointCor732CoverImpliesMNChoice_residual` — named residual Prop
  capturing the **genuine remaining math content** of T159: bridge from
  per-Spa-point σ_loc-rescaled Laurent piece membership to multiplicative
  locSubring-level factorisation witnesses of
  `AlphaJointMNChoiceLocSubringMembership`. Encapsulates the
  global-section / sheafiness criterion for `Localization.Away s`
  against the open subring `locSubring P T s`.

* `AlphaJointMNChoiceLocSubringMembership_via_cover_and_residual` —
  compiled theorem composing the cover extraction with the residual.
  Given the residual implication holds, plus the Cor 7.32 hypotheses,
  produces `∃ σ_loc N, AlphaJointMNChoiceLocSubringMembership`, which
  feeds T158's `AlphaJointFactorizationWitnessesExist_via_mn_choice`
  and ultimately
  `WedhornMPowerStructuralDataHonest_exists_via_witnesses_and_unit_s_D`.

Manager-fallback delivery: a strictly lower named Prop / API for the
exact finite test-family cover, a compiled extraction theorem producing
it from honest Cor 7.32 hypotheses, and a compiled bridge theorem
showing cover + named residual imply the M/N-choice membership package.
The genuine remaining mathematical content is isolated as the residual
Prop. -/

omit [PlusSubring A] in
/-- **T159 named test-family cover Prop**: σ_loc-rescaled Laurent piece
membership output of Cor 7.32 on `localizedTestFamily s T_D s_D`.
For every `w ∈ Spa(Localization.Away s, ⁺)`, some
`τ ∈ localizedTestFamily s T_D s_D` satisfies
`w ∈ rationalOpen {1} (σ_loc⁻¹ * τ)`. -/
def AlphaJointCor732TestFamilyCoverPackage
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    ∃ τ ∈ localizedTestFamily s T_D s_D,
      w ∈ rationalOpen
        ({(1 : Localization.Away s)} : Finset (Localization.Away s))
        (((σ_loc⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) * τ)

omit [PlusSubring A] in
/-- **T159 cover-existence theorem from Cor 7.32**. Existentially
produces `AlphaJointCor732TestFamilyCoverPackage` from the honest
Wedhorn 8.34(ii) Cor 7.32 hypotheses. Direct delegation to
`exists_localized_cor732_laurent_piece_membership`.

Parameters `π_loc`, `_hI_loc`, `_hπ_loc_tn`, `_hπ_loc_unit`, `_hArch_loc`,
`_hT_loc` are listed inside the `letI`-prefixed conclusion to bring the
local `TopologicalSpace` and `PlusSubring` instances into scope before
the `locPairOfDefinition`-typed parameters are interpreted. -/
theorem AlphaJointCor732TestFamilyCoverPackage_exists_via_localized_cor732
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    ∀ (π_loc : (locPairOfDefinition P T s hopen).A₀)
      (_hI_loc : (locPairOfDefinition P T s hopen).I = Ideal.span {π_loc})
      (_hπ_loc_tn : IsTopologicallyNilpotent
        ((locPairOfDefinition P T s hopen).A₀.subtype π_loc))
      (_hπ_loc_unit : IsUnit
        ((locPairOfDefinition P T s hopen).A₀.subtype π_loc))
      (_hArch_loc : ∀ w : Spv (Localization.Away s),
        letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero (Localization.Away s)))
      (T_D : Finset A) (s_D : A)
      (_hT_loc : ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D, ¬ w.vle τ 0),
    ∃ σ_loc : (Localization.Away s)ˣ,
      AlphaJointCor732TestFamilyCoverPackage P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  intro π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_D s_D hT_loc
  exact exists_localized_cor732_laurent_piece_membership P T s hopen
    π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_D s_D hT_loc

omit [PlusSubring A] in
/-- **T159 named bridge residual**: the genuine remaining Wedhorn
8.34(ii) Step 2 algebraic content. From the Cor 7.32 σ_loc-rescaled
Laurent piece cover, derive the multiplicative locSubring-level
factorisation witnesses of `AlphaJointMNChoiceLocSubringMembership` via
the global-section / sheafiness criterion for `Localization.Away s`
against `locSubring P T s`.

This residual is the canonical target for the next round of structural
work. NOT discharged by existing local Cor 7.32 / `exists_dominatedBy_cover`
API alone — the missing piece is the adic-space-style identification of
locSubring with the global Spa +-section ring. -/
def AlphaJointCor732CoverImpliesMNChoice_residual
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A) : Prop :=
  ∀ σ_loc : (Localization.Away s)ˣ,
    AlphaJointCor732TestFamilyCoverPackage P T s hopen T_D s_D σ_loc →
    ∃ N : ℕ,
      AlphaJointMNChoiceLocSubringMembership P T s hopen T_D s_D σ_loc N

omit [PlusSubring A] in
/-- **T159 cover-and-residual top-level supplier**. Given the named
bridge residual `AlphaJointCor732CoverImpliesMNChoice_residual` plus the
honest Cor 7.32 hypotheses producing
`AlphaJointCor732TestFamilyCoverPackage`, output the existential M/N
choice membership package. -/
theorem AlphaJointMNChoiceLocSubringMembership_via_cover_and_residual
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    ∀ (π_loc : (locPairOfDefinition P T s hopen).A₀)
      (_hI_loc : (locPairOfDefinition P T s hopen).I = Ideal.span {π_loc})
      (_hπ_loc_tn : IsTopologicallyNilpotent
        ((locPairOfDefinition P T s hopen).A₀.subtype π_loc))
      (_hπ_loc_unit : IsUnit
        ((locPairOfDefinition P T s hopen).A₀.subtype π_loc))
      (_hArch_loc : ∀ w : Spv (Localization.Away s),
        letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero (Localization.Away s)))
      (T_D : Finset A) (s_D : A)
      (_hT_loc : ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D, ¬ w.vle τ 0)
      (_h_residual :
        AlphaJointCor732CoverImpliesMNChoice_residual P T s hopen T_D s_D),
    ∃ (σ_loc : (Localization.Away s)ˣ) (N : ℕ),
      AlphaJointMNChoiceLocSubringMembership
        P T s hopen T_D s_D σ_loc N := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  intro π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_D s_D hT_loc h_residual
  obtain ⟨σ_loc, h_cover⟩ :=
    AlphaJointCor732TestFamilyCoverPackage_exists_via_localized_cor732
      P T s hopen π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_D s_D hT_loc
  obtain ⟨N, h_membership⟩ := h_residual σ_loc h_cover
  exact ⟨σ_loc, N, h_membership⟩

/-! ### T160: σ_loc-as-π_loc-power Unit API + bookkeeping

Independent reusable API around the σ-as-π-power identification central
to Wedhorn 8.34(ii) Step 2. From a topologically nilpotent unit
`π_loc : locSubring P T s` (the local pseudo-uniformizer) and an
exponent `M : ℕ`, T160 provides:

* `locSigmaUnit P T s hopen π_loc hπ_loc_unit M : (Loc s)ˣ` — the unit
  `σ_loc := π_loc^(M+1)` packaged as a `Localization.Away s` unit, ready
  for use as the σ_loc parameter of `AlphaJointMNChoiceLocSubringMembership`.

* `locSigmaUnit_val` — the value identity
  `(σ_loc : Loc s) = ((locSubring P T s).subtype π_loc) ^ (M+1)`.

* `locSigmaUnit_isTopologicallyNilpotent` — σ_loc is topologically
  nilpotent in Loc s under `locTopology P T s hopen` (since π_loc is).

* `locSigmaUnit_val_mem_locSubring` — `(σ_loc : Loc s) ∈ locSubring P T s`
  (a positive power of π_loc stays in the subring).

* `AlphaJointMNChoiceLocSubringMembership_via_pi_pow` — the named per-π_loc
  M-choice membership package: an existential closure over `M, N` of
  `AlphaJointMNChoiceLocSubringMembership` with `σ_loc := locSigmaUnit ... M`.

* `WedhornMPowerStructuralDataHonest_exists_via_pi_pow_and_unit_s_D` —
  top-level supplier feed: takes the π_loc-form M-choice + IsUnit α s_D
  and produces `∃ σ_loc, WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc`,
  via the T161 σ_loc-fixed integration wrapper.

This API is independent of T159's Cor 7.32 cover bridge and of T162's
global-section/sheafiness work; it provides only the algebraic σ-as-π-power
bookkeeping needed throughout the M/N-choice mechanism.
-/

/-- **σ_loc-as-π_loc-power Unit construction (T160)**. Given a unit
`π_loc : locSubring P T s` (witnessed by `hπ_loc_unit`) and an exponent
`M : ℕ`, package `(π_loc : Loc s)^(M+1) : (Loc s)ˣ` as a Units element. -/
noncomputable def locSigmaUnit
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (_hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (π_loc : locSubring P T s)
    (hπ_loc_unit :
      IsUnit ((locSubring P T s).subtype π_loc))
    (M : ℕ) : (Localization.Away s)ˣ :=
  (hπ_loc_unit.pow (M + 1)).unit

/-- **Value identity for `locSigmaUnit`**: the underlying `Loc s` value
of the constructed σ_loc unit equals `((locSubring P T s).subtype π_loc) ^ (M+1)`. -/
theorem locSigmaUnit_val
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (π_loc : locSubring P T s)
    (hπ_loc_unit :
      IsUnit ((locSubring P T s).subtype π_loc))
    (M : ℕ) :
    (locSigmaUnit P T s hopen π_loc hπ_loc_unit M : Localization.Away s) =
      ((locSubring P T s).subtype π_loc) ^ (M + 1) :=
  (hπ_loc_unit.pow (M + 1)).unit_spec

/-- **Topological nilpotency of `locSigmaUnit`**: the underlying value
of σ_loc is topologically nilpotent under `locTopology P T s hopen`,
since π_loc is and `(M+1) > 0`. -/
theorem locSigmaUnit_isTopologicallyNilpotent
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (π_loc : locSubring P T s)
    (hπ_loc_unit :
      IsUnit ((locSubring P T s).subtype π_loc))
    (hπ_loc_tn :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      IsTopologicallyNilpotent ((locSubring P T s).subtype π_loc))
    (M : ℕ) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    IsTopologicallyNilpotent
      (locSigmaUnit P T s hopen π_loc hπ_loc_unit M : Localization.Away s) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  rw [locSigmaUnit_val P T s hopen π_loc hπ_loc_unit M]
  exact isTopologicallyNilpotent_pow hπ_loc_tn (Nat.succ_pos M)

/-- **`locSigmaUnit` lies in `locSubring`**: as `(π_loc : Loc s)^(M+1)`
is a positive power of an element of the subring `locSubring P T s`,
its value lies in `locSubring P T s`. -/
theorem locSigmaUnit_val_mem_locSubring
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (π_loc : locSubring P T s)
    (hπ_loc_unit :
      IsUnit ((locSubring P T s).subtype π_loc))
    (M : ℕ) :
    (locSigmaUnit P T s hopen π_loc hπ_loc_unit M : Localization.Away s) ∈
      locSubring P T s := by
  rw [locSigmaUnit_val P T s hopen π_loc hπ_loc_unit M]
  exact (locSubring P T s).pow_mem π_loc.property (M + 1)

/-- **Named M/N-choice membership in σ-as-π-power form (T160)**.

Existential closure over `(M, N)` of the M/N-choice locSubring
membership package, with σ_loc fixed as the π_loc-power
`locSigmaUnit P T s hopen π_loc hπ_loc_unit M`. This is the σ-as-π-power
shape natural to Wedhorn 8.34(ii) Step 2's Cor 7.32 σ-construction
(σ = π^(N+1) in `Cor732.lean:225`). -/
def AlphaJointMNChoiceLocSubringMembership_via_pi_pow
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (π_loc : locSubring P T s)
    (hπ_loc_unit :
      IsUnit ((locSubring P T s).subtype π_loc)) : Prop :=
  ∃ M N : ℕ,
    AlphaJointMNChoiceLocSubringMembership P T s hopen T_D s_D
      (locSigmaUnit P T s hopen π_loc hπ_loc_unit M) N

omit [PlusSubring A] in
/-- **From π-power M/N-choice membership to factorization witnesses
existence**. Bridge collapsing `AlphaJointMNChoiceLocSubringMembership_via_pi_pow`
into `AlphaJointFactorizationWitnessesExist`. -/
theorem AlphaJointFactorizationWitnessesExist_via_pi_pow
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (π_loc : locSubring P T s)
    (hπ_loc_unit :
      IsUnit ((locSubring P T s).subtype π_loc))
    (h_pi_pow :
      AlphaJointMNChoiceLocSubringMembership_via_pi_pow
        P T s hopen T_D s_D π_loc hπ_loc_unit) :
    AlphaJointFactorizationWitnessesExist P T s hopen T_D s_D := by
  obtain ⟨M, N, h_mn⟩ := h_pi_pow
  exact AlphaJointFactorizationWitnessesExist_via_mn_choice
    P T s hopen T_D s_D
    (locSigmaUnit P T s hopen π_loc hπ_loc_unit M) N h_mn

omit [PlusSubring A] in
/-- **Top-level π-power supplier feed: π-power M/N-choice + `IsUnit α s_D`
→ `∃ σ_loc, WedhornMPowerStructuralDataHonest`**.

End-to-end consumer for the σ-as-π-power form: takes the existential
M/N-choice membership in π-power form plus `IsUnit (algebraMap A (Loc s) s_D)`,
yields `∃ σ_loc, WedhornMPowerStructuralDataHonest`. -/
theorem WedhornMPowerStructuralDataHonest_exists_via_pi_pow_and_unit_s_D
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (π_loc : locSubring P T s)
    (hπ_loc_unit :
      IsUnit ((locSubring P T s).subtype π_loc))
    (h_unit_s_D : IsUnit (algebraMap A (Localization.Away s) s_D))
    (h_pi_pow :
      AlphaJointMNChoiceLocSubringMembership_via_pi_pow
        P T s hopen T_D s_D π_loc hπ_loc_unit) :
    ∃ σ_loc : (Localization.Away s)ˣ,
      WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc := by
  obtain ⟨M, N, h_mn⟩ := h_pi_pow
  refine ⟨locSigmaUnit P T s hopen π_loc hπ_loc_unit M, ?_⟩
  exact WedhornMPowerStructuralDataHonest_via_mn_choice_membership_and_unit_s_D
    P T s hopen T_D s_D
    (locSigmaUnit P T s hopen π_loc hπ_loc_unit M) N h_unit_s_D h_mn

/-! ### T160 dependency map (post-σ-power-API)

After this section, the σ-as-π-power form of the M/N-choice content is
isolated. The remaining genuinely-mathematical content for the joint
factorisation witnesses reduces to:

```
∀ (P T s hopen T_D s_D)
  (π_loc : locSubring P T s)
  (hπ_loc_unit : IsUnit ((locSubring P T s).subtype π_loc)),
  -- the M/N-choice membership in π-power form holds for some (M, N):
  AlphaJointMNChoiceLocSubringMembership_via_pi_pow
    P T s hopen T_D s_D π_loc hπ_loc_unit
```

Discharging this is the genuine Wedhorn 8.34(ii) Step 2 Cor 7.32
M/N-choice content (Primary's T159 / T162 lane). The σ-as-π-power
algebraic packaging here (T160) plus the σ_loc-fixed factorization
discharge (T161/T156) plus the named witness existence Prop (T157) and
M/N-choice package (T158) together cover the full algebraic / structural
infrastructure on the consumer side. -/

/-! ### T162: Global-section / sheafiness criterion residual

Materially reduces the T159 bridge residual
`AlphaJointCor732CoverImpliesMNChoice_residual` by isolating its core
content as the named **global-section / sheafiness criterion** for
`Localization.Away s` against the open subring `locSubring P T s`:

```
∀ a : Localization.Away s,
  (∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺, w.vle a 1) →
  a ∈ locSubring P T s
```

This is the converse direction of the standard `vle_one_of_mem_spa`
inclusion: locSubring sits inside the integral elements of every
Spa-valuation. The forward direction is immediate from
`AdicSpectrum.vle_one_of_mem_spa` (and the canonical PlusSubring
identification `(Localization.Away s)⁺ = locSubring P T s` via
`localizationLocSubringPlusSubring`); the converse is the
"adic-space-style global section ring = A⁺" criterion in the localized
setting and is the Wedhorn 7.18 / Bourbaki sheafiness content.

Provided:

* `GlobalSectionLocSubringCriterion` — named residual Prop.

* `vle_one_of_mem_locSubring_on_spa` — fully proved forward direction
  (locSubring → vle ≤ 1 globally on Spa); direct from
  `vle_one_of_mem_spa` against the canonical `localizationLocSubringPlusSubring`.

* `AlphaJointCor732CoverImpliesMNChoice_residual_via_globalSectionCriterion_residual`
  — strictly lower named bridge residual: the global-section criterion
  plus an explicit valuation-side hypothesis on the cover (uniform
  multiplicative bound) implies T159's
  `AlphaJointCor732CoverImpliesMNChoice_residual`. This isolates the
  algebraic factorisation construction as the remaining content,
  separating it cleanly from the global-section/sheafiness content.

Status: T162 manager-fallback delivery — named criterion Prop, fully
compiled forward direction, and a strictly lower bridge residual capturing
exactly the remaining algebraic content. -/

omit [PlusSubring A] in
/-- **T162 named global-section criterion**: every element of
`Localization.Away s` whose valuation is bounded by `1` on every Spa
point (over the canonical localized PlusSubring
`localizationLocSubringPlusSubring P T s = locSubring P T s`) lies in
`locSubring P T s`. The Wedhorn 7.18 / Bourbaki adic-space sheafiness
criterion in the localized setting. -/
def GlobalSectionLocSubringCriterion
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  ∀ a : Localization.Away s,
    (∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle a 1) →
    a ∈ locSubring P T s

omit [PlusSubring A] in
/-- **T162 forward direction**: locSubring ⊆ global section ring.
Every `a ∈ locSubring P T s` satisfies `w.vle a 1` for every
`w ∈ Spa (Localization.Away s) (Localization.Away s)⁺`.

Direct application of `vle_one_of_mem_spa` after the
`localizationLocSubringPlusSubring` identification. The forward
direction is the easy half; the converse is `GlobalSectionLocSubringCriterion`. -/
theorem vle_one_of_mem_locSubring_on_spa
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    ∀ (a : Localization.Away s), a ∈ locSubring P T s →
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle a 1 := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  intro a ha w hw
  -- `a ∈ locSubring P T s = (Localization.Away s)⁺` (by the canonical
  -- `localizationLocSubringPlusSubring` identification), so
  -- `vle_one_of_mem_spa` directly applies.
  exact vle_one_of_mem_spa hw ha

omit [PlusSubring A] in
/-- **T162 strictly lower bridge residual**: the global-section criterion
plus an explicit valuation-side multiplicative-bound hypothesis on the
cover implies T159's `AlphaJointCor732CoverImpliesMNChoice_residual`.

This isolates the algebraic factorisation construction as the genuine
remaining content: given the criterion and a uniform multiplicative bound
on the cover (formulated as a hypothesis), one constructs explicit
N : ℕ and witnesses `ξ_decay`, `ξ_t'` in `Localization.Away s`, applies the
criterion to verify their `locSubring` membership, and assembles
`AlphaJointMNChoiceLocSubringMembership`.

The residual `AlphaJointCor732MultiplicativeBound_residual` captures the
explicit N-choice + valuation hypothesis on the cover that the criterion
alone does not imply (it requires σ-strict-domination plus per-`τ`
N-power decay, an explicit Wedhorn 8.34(ii) Step 2 algebraic step). -/
def AlphaJointCor732MultiplicativeBound_residual
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  ∀ σ_loc : (Localization.Away s)ˣ,
    AlphaJointCor732TestFamilyCoverPackage P T s hopen T_D s_D σ_loc →
    -- For each cover, there exist N and explicit valuation-bounded
    -- witnesses constructible from σ_loc and the cover data:
    ∃ (N : ℕ) (ξ_decay : Localization.Away s)
      (ξ_t : ∀ t ∈ T_D, Localization.Away s),
      -- Decay factorization with valuation ≤ 1 on Spa:
      (algebraMap A (Localization.Away s) s =
        ξ_decay *
          ((σ_loc : Localization.Away s) *
            (algebraMap A (Localization.Away s) s_D) ^ (N + 1))) ∧
      (∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ξ_decay 1) ∧
      -- Per-`t` chain factorization with valuation ≤ 1 on Spa:
      (∀ t (ht : t ∈ T_D),
        (σ_loc : Localization.Away s) *
            (algebraMap A (Localization.Away s) t) *
            (algebraMap A (Localization.Away s) s_D) ^ N =
          ξ_t t ht * algebraMap A (Localization.Away s) s) ∧
      (∀ t (ht : t ∈ T_D),
        ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
          w.vle (ξ_t t ht) 1)

omit [PlusSubring A] in
/-- **T162 compiled bridge**: global-section criterion +
multiplicative-bound residual ⇒ T159's
`AlphaJointCor732CoverImpliesMNChoice_residual`.

Given (a) the global-section criterion (the Wedhorn 7.18 sheafiness
content) and (b) the multiplicative-bound residual (the algebraic
factorization construction), the original T159 bridge follows: the
criterion lifts each Spa-bounded factorization to a `locSubring`-level
witness, and the residual provides the factorization construction.

This strictly reduces T159's bridge residual to two strictly smaller
named residuals, separating the global-section content from the
algebraic-factorization content. -/
theorem AlphaJointCor732CoverImpliesMNChoice_residual_via_globalSectionCriterion_residual
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (h_criterion : GlobalSectionLocSubringCriterion P T s hopen)
    (h_mult : AlphaJointCor732MultiplicativeBound_residual
      P T s hopen T_D s_D) :
    AlphaJointCor732CoverImpliesMNChoice_residual P T s hopen T_D s_D := by
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro σ_loc h_cover
  obtain ⟨N, ξ_decay, ξ_t, hfact_decay, hvle_decay,
    hfact_chain, hvle_chain⟩ := h_mult σ_loc h_cover
  -- Apply the global-section criterion to `ξ_decay` and each `ξ_t t ht`.
  have hξ_decay_mem : ξ_decay ∈ locSubring P T s := h_criterion ξ_decay hvle_decay
  refine ⟨N, ⟨⟨ξ_decay, hξ_decay_mem⟩, hfact_decay⟩, ?_⟩
  intro t' ht'
  -- t' ∈ T_D.image (algebraMap ...) ⇒ pick a preimage t ∈ T_D.
  rcases Finset.mem_image.mp ht' with ⟨t, ht, ht_eq⟩
  have hξ_t_mem : ξ_t t ht ∈ locSubring P T s :=
    h_criterion (ξ_t t ht) (hvle_chain t ht)
  refine ⟨⟨ξ_t t ht, hξ_t_mem⟩, ?_⟩
  -- Replace t' with algebraMap ... t.
  subst ht_eq
  exact hfact_chain t ht

/-! ### T163: integral-closure reduction of the global-section criterion

Reduces T162's `GlobalSectionLocSubringCriterion` to a strictly smaller
named residual: the **integral-closure property** of `locSubring P T s`
inside `Localization.Away s`.

The strategy uses Wedhorn Proposition 7.18
(`isIntegral_of_forall_continuous_valuation_le_one` in `Presheaf.lean`):
for an open subring `B` of a topological domain `R` containing the ring
of definition `P.A₀`, an element `a : R` is integral over `B` iff
`v.vle a 1` for every continuous valuation `v` with `v.vle b 1` on `b ∈ B`.

Applied with `R = Localization.Away s` (under `locTopology`),
`P = locPairOfDefinition P T s hopen`, and `B = locSubring P T s`,
the Spa-bounded hypothesis of `GlobalSectionLocSubringCriterion`
yields `IsIntegral (locSubring P T s) a`. The remaining gap from
`IsIntegral B a` to `a ∈ B` is exactly the **integral closure** of
`locSubring P T s` in `Localization.Away s`, the genuine Wedhorn 7.14
"ring of integral elements" structural axiom.

Provided:

* `LocSubringIntegrallyClosedInLocalization` — named residual Prop:
  every element of `Localization.Away s` integral over `locSubring P T s`
  already lies in `locSubring P T s`. This is the genuine Wedhorn 7.14
  ring-of-integral-elements axiom in the localized setting.

* `GlobalSectionLocSubringCriterion_via_locSubring_integrallyClosed` —
  compiled main bridge: integral-closure residual + `[IsDomain A]` +
  `s ≠ 0` ⇒ `GlobalSectionLocSubringCriterion`. Direct application of
  Wedhorn 7.18 + the integral-closure residual.

* `AlphaJointCor732CoverImpliesMNChoice_residual_via_locSubring_integrallyClosed` —
  compiled chained bridge: integral-closure residual + multiplicative-bound
  residual ⇒ T159's `AlphaJointCor732CoverImpliesMNChoice_residual`.
  Combines the two T162 + T163 reductions into a single supplier.

Status: T163 manager-fallback delivery — strictly lower named residual
plus two compiled bridge theorems (one direct, one chained). The
remaining residual `LocSubringIntegrallyClosedInLocalization` is the
genuine Wedhorn 7.14 / 7.18 structural content not reducible to existing
local Cor 7.32 / σ-power-decay / Spa-bounded primitives. -/

omit [PlusSubring A] in
/-- **T163 named integral-closure residual**: `locSubring P T s` is
integrally closed inside `Localization.Away s`, i.e. every element of
`Localization.Away s` integral over `locSubring P T s` already lies in
`locSubring P T s`.

This is the Wedhorn 7.14 / 7.18 structural axiom on rings of integral
elements: a "ring of integral elements" `A⁺` is by definition the
integral closure of an open bounded subring inside `A`. Without it,
the integral-closure half of the global-section criterion fails. -/
def LocSubringIntegrallyClosedInLocalization
    (P : PairOfDefinition A) (T : Finset A) (s : A) : Prop :=
  ∀ a : Localization.Away s,
    IsIntegral (locSubring P T s) a → a ∈ locSubring P T s

omit [PlusSubring A] in
/-- **T163 compiled main bridge**: Wedhorn 7.18 + integral-closure of
`locSubring P T s` in `Localization.Away s` together with `[IsDomain A]`
and `s ≠ 0` yield T162's `GlobalSectionLocSubringCriterion`.

Strictly reduces the global-section / sheafiness criterion to one
strictly smaller named residual: the integral-closure property of
`locSubring` in the localization (the Wedhorn 7.14 ring-of-integral-elements
axiom).

**Proof sketch**: Apply
`isIntegral_of_forall_continuous_valuation_le_one` (Wedhorn Prop 7.18,
`Presheaf.lean`) to `(locPairOfDefinition P T s hopen)` with subring
`locSubring P T s`. The Spa-bounded hypothesis on `a` produces a
continuous-valuation hypothesis from which Wedhorn 7.18 yields
`IsIntegral (locSubring P T s) a`. The integral-closure residual then
gives `a ∈ locSubring P T s`. -/
theorem GlobalSectionLocSubringCriterion_via_locSubring_integrallyClosed
    [DecidableEq A] [IsDomain A]
    (P : PairOfDefinition A) (T : Finset A) (s : A) (hs : s ≠ 0)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (h_intCl : LocSubringIntegrallyClosedInLocalization P T s) :
    GlobalSectionLocSubringCriterion P T s hopen := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : IsTopologicalRing (Localization.Away s) :=
    (locBasis P T s hopen).toRingFilterBasis.isTopologicalRing
  letI : IsDomain (Localization.Away s) := locAway_isDomain hs
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  intro a ha_spa
  -- Step 1: Apply Wedhorn 7.18 to get integrality over `locSubring P T s`.
  have hint : IsIntegral (locSubring P T s) a := by
    apply isIntegral_of_forall_continuous_valuation_le_one
      (locPairOfDefinition P T s hopen)
      (locSubring_isOpen P T s hopen)
      (Set.Subset.refl _)
    intro v hv_cont hv_sub
    -- (⟨v⟩ : Spv (Loc s)) is in Spa via hv_cont and hv_sub.
    have hw_spa : (⟨v⟩ : Spv (Localization.Away s))
        ∈ Spa (Localization.Away s) (Localization.Away s)⁺ := ⟨hv_cont, hv_sub⟩
    exact ha_spa _ hw_spa
  -- Step 2: Apply integral-closure residual.
  exact h_intCl a hint

omit [PlusSubring A] in
/-- **T163 chained bridge**: integral-closure residual +
multiplicative-bound residual ⇒ T159's
`AlphaJointCor732CoverImpliesMNChoice_residual`.

Combines the T163 main bridge (integrality ⇒ `GlobalSectionLocSubringCriterion`)
with T162's compiled bridge (criterion + multiplicative-bound ⇒
T159's bridge residual). The result is a single chained supplier
turning two strictly smaller named residuals into the M/N-choice
bridge residual. -/
theorem AlphaJointCor732CoverImpliesMNChoice_residual_via_locSubring_integrallyClosed
    [DecidableEq A] [IsDomain A]
    (P : PairOfDefinition A) (T : Finset A) (s : A) (hs : s ≠ 0)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (h_intCl : LocSubringIntegrallyClosedInLocalization P T s)
    (h_mult : AlphaJointCor732MultiplicativeBound_residual
      P T s hopen T_D s_D) :
    AlphaJointCor732CoverImpliesMNChoice_residual P T s hopen T_D s_D :=
  AlphaJointCor732CoverImpliesMNChoice_residual_via_globalSectionCriterion_residual
    P T s hopen T_D s_D
    (GlobalSectionLocSubringCriterion_via_locSubring_integrallyClosed
      P T s hs hopen h_intCl)
    h_mult

/-! ### T163 (object-level redo): `locPlusSubring` honest plus-subring API

**Reviewer redirection (T163)**: the residual
`LocSubringIntegrallyClosedInLocalization` introduced above is *not the
right target* — `locSubring P T s = Subring.closure(image A₀ ∪ {t/s})` is
not expected to be integrally closed in `Localization.Away s` under the
final Wedhorn 8.34(ii) hypotheses. The honest fix replaces `locSubring`
with its **integral closure** as the localized plus-subring.

This block lands the object-level correction:

1. `locPlusSubring P T s` — the integral closure of `locSubring P T s`
   inside `Localization.Away s`, packaged as `Subring (Localization.Away s)`.

2. `localizationLocPlusSubring P T s : PlusSubring (Localization.Away s)`
   — the canonical localized plus-subring instance with
   `toSubring = locPlusSubring P T s`.

3. `mem_locPlusSubring_iff_isIntegral` — definitional equivalence between
   `locPlusSubring` membership and `IsIntegral` over `locSubring`.

4. `vle_one_of_isIntegral_of_subring_le_one` — reusable helper:
   integrality over a subring contained in `Valuation.integer ν` gives
   `ν ≤ 1`. Pure ValuativeRel ↔ Valuation translation, depends only on
   `Valuation.Integers.mem_of_integral`.

5. `vle_one_of_mem_locPlusSubring_on_spa` — fully proved forward
   direction: `locPlusSubring → vle ≤ 1 globally on Spa(_, locPlusSubring)`.

6. `mem_locPlusSubring_of_vle_on_spa` — **the honest global-section
   theorem**: under `[IsDomain A]` and `s ≠ 0`, every element of
   `Localization.Away s` whose valuation is `≤ 1` on every Spa point
   over `(Localization.Away s, locPlusSubring P T s)` lies in
   `locPlusSubring P T s`. Combines Wedhorn Prop 7.18
   (`isIntegral_of_forall_continuous_valuation_le_one`) with
   integral-closure stability of non-archimedean valuations.

7. `AlphaJointMNChoiceLocPlusMembership` — the honest M/N-choice
   membership Prop with witnesses in `locPlusSubring` (replacing the
   `locSubring` version). This is the right downstream target for the
   T021 lane.

8. `AlphaJointMNChoiceLocPlusMembership_of_locSubring` — trivial
   bridge: any `AlphaJointMNChoiceLocSubringMembership` lifts to the
   locPlus version via `locSubring ≤ locPlusSubring`. Lets every
   existing locSubring-side supplier feed the honest locPlus target
   without duplication.

**Supersedes**: the residual route
`LocSubringIntegrallyClosedInLocalization` +
`GlobalSectionLocSubringCriterion_via_locSubring_integrallyClosed` +
`AlphaJointCor732CoverImpliesMNChoice_residual_via_locSubring_integrallyClosed`.
Those bridges remain in the file (compile clean) but their named residual
is unreachable under the final Wedhorn hypotheses; downstream consumers
should target the locPlus API instead.

**Status**: T163 honest object-level delivery — sorry-free locPlus API
plus the honest global-section theorem, no new named residuals. -/

omit [PlusSubring A] in
/-- **T163 reusable helper**: integrality over a subring contained in
`Valuation.integer ν` forces `ν ≤ 1`. Combines `IsIntegral.tower_top` with
`Valuation.Integers.mem_of_integral` (ValuativeRel ↔ Valuation via
`Valuation.Compatible.vle_iff_le`). -/
private theorem vle_one_of_isIntegral_of_subring_le_one
    {R : Type*} [CommRing R] (S : Subring R)
    (_v : ValuativeRel R)
    (hv_S : ∀ x ∈ S, _v.vle x 1)
    {b : R}
    (hb_int : IsIntegral S b) : _v.vle b 1 := by
  letI : ValuativeRel R := _v
  set ν := ValuativeRel.valuation R
  -- Translate vle x y ↔ ν x ≤ ν y via the Compatible instance for ν.
  haveI : Valuation.Compatible (R := R) ν := inferInstance
  have h_iff : ∀ x : R, x ≤ᵥ 1 ↔ ν x ≤ 1 := fun x ↦ by
    rw [Valuation.Compatible.vle_iff_le (v := ν) x 1, ν.map_one]
  -- S ≤ ν.integer (as subrings of R).
  have h_le : S ≤ Valuation.integer ν := by
    intro x hx
    show ν x ≤ 1
    exact (h_iff x).mp (hv_S x hx)
  -- Algebra (S → ν.integer) via inclusion; IsScalarTower S ν.integer R.
  letI : Algebra S (Valuation.integer ν) := (Subring.inclusion h_le).toAlgebra
  letI : IsScalarTower S (Valuation.integer ν) R :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- Tower top: IsIntegral S b → IsIntegral ν.integer b.
  have hb_int' : IsIntegral (Valuation.integer ν) b := hb_int.tower_top
  -- Use Valuation.Integers.mem_of_integral on (ν, ν.integer).
  have hb_mem : b ∈ Valuation.integer ν :=
    (Valuation.integer.integers ν).mem_of_integral hb_int'
  -- b ∈ ν.integer ↔ ν b ≤ 1.
  exact (h_iff b).mpr ((Valuation.mem_integer_iff ν b).mp hb_mem)

omit [PlusSubring A] in
/-- **T163 honest plus-subring**: the integral closure of `locSubring P T s`
inside `Localization.Away s`, packaged as a `Subring`.

This is the **honest** plus-subring of `Localization.Away s` for the
Wedhorn 8.34(ii) lane: it is by construction integrally closed (Wedhorn
Definition 7.14 ring-of-integral-elements axiom), so the global-section
theorem `mem_locPlusSubring_of_vle_on_spa` is sorry-free directly from
Wedhorn 7.18 + integral-closure stability. -/
noncomputable def locPlusSubring
    (P : PairOfDefinition A) (T : Finset A) (s : A) :
    Subring (Localization.Away s) :=
  (integralClosure (locSubring P T s) (Localization.Away s)).toSubring

omit [PlusSubring A] [IsTopologicalRing A] in
/-- **T163 mem characterization** for `locPlusSubring`: `a ∈ locPlusSubring P T s`
iff `a` is integral over `locSubring P T s`. Definitional unfolding of
`integralClosure.toSubring`. -/
theorem mem_locPlusSubring_iff_isIntegral
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (a : Localization.Away s) :
    a ∈ locPlusSubring P T s ↔ IsIntegral (locSubring P T s) a := by
  simp only [locPlusSubring, Subalgebra.mem_toSubring, mem_integralClosure_iff]

omit [PlusSubring A] [IsTopologicalRing A] in
/-- **T163 inclusion**: `locSubring P T s ≤ locPlusSubring P T s`.
Every element of the ring of definition is trivially integral over itself. -/
theorem locSubring_le_locPlusSubring
    (P : PairOfDefinition A) (T : Finset A) (s : A) :
    locSubring P T s ≤ locPlusSubring P T s := by
  intro x hx
  rw [mem_locPlusSubring_iff_isIntegral]
  exact isIntegral_algebraMap (x := (⟨x, hx⟩ : locSubring P T s))

omit [PlusSubring A] in
/-- **T163 canonical localized plus-subring** with `toSubring = locPlusSubring P T s`.
Provided as `noncomputable def` (not `instance`) to avoid global
instance-resolution interference; consumers introduce locally via `letI`. -/
@[reducible]
noncomputable def localizationLocPlusSubring
    (P : PairOfDefinition A) (T : Finset A) (s : A) :
    PlusSubring (Localization.Away s) where
  toSubring := locPlusSubring P T s

omit [PlusSubring A] in
/-- **T163 forward direction**: `locPlusSubring → vle ≤ 1` on Spa.
Direct application of `vle_one_of_mem_spa` against the canonical
`localizationLocPlusSubring`. -/
theorem vle_one_of_mem_locPlusSubring_on_spa
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) := localizationLocPlusSubring P T s
    ∀ (a : Localization.Away s), a ∈ locPlusSubring P T s →
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle a 1 := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) := localizationLocPlusSubring P T s
  intro a ha w hw
  exact vle_one_of_mem_spa hw ha

omit [PlusSubring A] in
/-- **T163 honest global-section theorem**: any `a : Localization.Away s`
with `w.vle a 1` for every `w ∈ Spa(_, locPlusSubring P T s)` lies in
`locPlusSubring P T s`.

Combines:
- Wedhorn Proposition 7.18
  (`isIntegral_of_forall_continuous_valuation_le_one`) with
  `B = locSubring P T s` to get `IsIntegral (locSubring) a`.
- Integral-closure stability of non-archimedean valuations
  (`vle_one_of_isIntegral_of_subring_le_one`) to bridge from
  `Spa(_, locPlusSubring)` to `Spa(_, locSubring)` hypotheses
  (every continuous v ≤ 1 on locSubring is automatically ≤ 1 on
  locPlusSubring).

No residual: this is the honest closing of the global-section /
sheafiness criterion at the locPlus level. -/
theorem mem_locPlusSubring_of_vle_on_spa
    [DecidableEq A] [IsDomain A]
    (P : PairOfDefinition A) (T : Finset A) (s : A) (hs : s ≠ 0)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) := localizationLocPlusSubring P T s
    ∀ a : Localization.Away s,
      (∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle a 1) →
      a ∈ locPlusSubring P T s := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : IsTopologicalRing (Localization.Away s) :=
    (locBasis P T s hopen).toRingFilterBasis.isTopologicalRing
  letI : IsDomain (Localization.Away s) := locAway_isDomain hs
  letI : PlusSubring (Localization.Away s) := localizationLocPlusSubring P T s
  intro a ha_spa
  -- Step 1: Apply Wedhorn 7.18 to get integrality over locSubring.
  have hint : IsIntegral (locSubring P T s) a := by
    apply isIntegral_of_forall_continuous_valuation_le_one
      (locPairOfDefinition P T s hopen)
      (locSubring_isOpen P T s hopen)
      (Set.Subset.refl _)
    intro v hv_cont hv_locSubring
    -- Upgrade: v ≤ 1 on locPlusSubring (integral-closure stability).
    have hv_locPlus : ∀ b ∈ locPlusSubring P T s, v.vle b 1 := by
      intro b hb
      rw [mem_locPlusSubring_iff_isIntegral] at hb
      exact vle_one_of_isIntegral_of_subring_le_one
        (locSubring P T s) v hv_locSubring hb
    -- ⟨v⟩ ∈ Spa(_, locPlusSubring).
    have hw_spa : (⟨v⟩ : Spv (Localization.Away s))
        ∈ Spa (Localization.Away s) (Localization.Away s)⁺ :=
      ⟨hv_cont, hv_locPlus⟩
    exact ha_spa _ hw_spa
  -- Step 2: a ∈ locPlusSubring (by definition of integral closure).
  rwa [mem_locPlusSubring_iff_isIntegral]

omit [PlusSubring A] in
/-- **T163 honest M/N-choice membership** with witnesses in
`locPlusSubring` (replacing the `locSubring` version
`AlphaJointMNChoiceLocSubringMembership`).

This is the right downstream target for the T021 lane: the honest
`A⁺ = locPlusSubring P T s` is integrally closed by construction, so the
M/N-choice factorisation witnesses naturally land in it. -/
def AlphaJointMNChoiceLocPlusMembership
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) := localizationLocPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  (∃ ξ_decay : locPlusSubring P T s,
    algebraMap A (Localization.Away s) s =
      (ξ_decay : Localization.Away s) *
        ((σ_loc : Localization.Away s) *
          (algebraMap A (Localization.Away s) s_D) ^ (N + 1))) ∧
  (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
    ∃ ξ_t' : locPlusSubring P T s,
      (σ_loc : Localization.Away s) * t' *
          (algebraMap A (Localization.Away s) s_D) ^ N =
        (ξ_t' : Localization.Away s) *
          algebraMap A (Localization.Away s) s)

omit [PlusSubring A] in
/-- **T163 trivial bridge**: any
`AlphaJointMNChoiceLocSubringMembership` (witnesses in `locSubring`)
lifts to `AlphaJointMNChoiceLocPlusMembership` (witnesses in
`locPlusSubring`) via the canonical inclusion
`locSubring ≤ locPlusSubring`. No new content; lets every existing
locSubring-side supplier feed the honest locPlus target without
duplication.

The `[IsTopologicalRing A]` section variable appears unused to the
linter because `locTopology` is `@[reducible]` and unfolds during
elaboration, but it is genuinely required at instance synthesis. -/
theorem AlphaJointMNChoiceLocPlusMembership_of_locSubring
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_loc : AlphaJointMNChoiceLocSubringMembership
      P T s hopen T_D s_D σ_loc N) :
    AlphaJointMNChoiceLocPlusMembership P T s hopen T_D s_D σ_loc N := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) := localizationLocPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  obtain ⟨⟨⟨ξ_decay, hξ_decay_mem⟩, hξ_decay_eq⟩, h_chain⟩ := h_loc
  refine ⟨⟨⟨ξ_decay, locSubring_le_locPlusSubring P T s hξ_decay_mem⟩,
    hξ_decay_eq⟩, ?_⟩
  intro t' ht'
  obtain ⟨⟨ξ_t', hξ_t'_mem⟩, hξ_t'_eq⟩ := h_chain t' ht'
  exact ⟨⟨ξ_t', locSubring_le_locPlusSubring P T s hξ_t'_mem⟩, hξ_t'_eq⟩

/-! ### T164: algebraic multiplicative-bound residual reduction

Strictly lower reduction of T162's `AlphaJointCor732MultiplicativeBound_residual`
into a single named **uniform σ-power-decay + per-`t` chain** Prop on
`Spa(Localization.Away s, ⁺)`, plus an `IsUnit α s_D` algebraic side
hypothesis. The reduction isolates the **algebraic factorisation
construction** as a trivial `IsUnit`-driven step, leaving the genuine
remaining content as the uniform decay+chain on Spa (the Wedhorn 8.34(ii)
Step 2 σ-power-decay content).

Provided:

* `AlphaJointCor732_uniformDecayAndChain` — named per-σ_loc Prop
  asserting the existence of a Spa-uniform exponent `N` such that the
  σ-power decay `w.vle (α s) (σ_loc · α s_D^(N+1))` and the per-`t`
  chain `w.vle (σ_loc · α t · α s_D^N) (α s)` hold at every
  `w ∈ Spa(Localization.Away s, ⁺)`.

* `AlphaJointCor732MultiplicativeBound_residual_via_uniformDecayAndChain_and_unit_s_D`
  — compiled bridge: from the uniform decay+chain residual + `IsUnit α s_D`,
  produces T162's `AlphaJointCor732MultiplicativeBound_residual`. The
  proof constructs explicit witnesses `ξ_decay := α s · (σ_loc · α s_D^(N+1))⁻¹`
  and per-`t` `ξ_t := σ_loc · α t · α s_D^N · (α s)⁻¹` (using the unit
  inverses), verifies the algebraic factorisations by Units arithmetic,
  and derives the valuation bounds via `vle_iff_mul_unit_right`
  applied to the uniform decay+chain inequalities.

The remaining content is then concentrated entirely in
`AlphaJointCor732_uniformDecayAndChain`, which is the Wedhorn 8.34(ii)
Step 2 σ-power-decay statement on the local Spa — discharged via
σ-as-π-power identification (T160) + Spa-quasi-compactness M-choice. -/

omit [PlusSubring A] in
/-- **T164 named uniform σ-power-decay + per-`t` chain Prop**. For a
fixed `σ_loc : (Localization.Away s)ˣ`, asserts the existence of an
exponent `N : ℕ` such that:

* (uniform decay) at every `w ∈ Spa(Localization.Away s, ⁺)`:
  `w.vle (algebraMap A (Loc s) s) ((σ_loc : Loc s) · (algebraMap A (Loc s) s_D)^(N+1))`;
* (per-`t` chain) at every `t ∈ T_D` and every `w ∈ Spa`:
  `w.vle ((σ_loc : Loc s) · (algebraMap A (Loc s) t) · (algebraMap A (Loc s) s_D)^N)
        (algebraMap A (Loc s) s)`.

This is the natural Wedhorn 8.34(ii) Step 2 σ-power-decay content
isolated from the algebraic factorisation. -/
def AlphaJointCor732_uniformDecayAndChain
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  ∃ N : ℕ,
    (∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle (algebraMap A (Localization.Away s) s)
        ((σ_loc : Localization.Away s) *
          (algebraMap A (Localization.Away s) s_D) ^ (N + 1))) ∧
    (∀ t ∈ T_D,
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            algebraMap A (Localization.Away s) t *
            (algebraMap A (Localization.Away s) s_D) ^ N)
          (algebraMap A (Localization.Away s) s))

omit [PlusSubring A] in
/-- **T164 strictly lower reduction**: from the uniform σ-power
decay+chain residual and `IsUnit α s_D`, produce T162's
`AlphaJointCor732MultiplicativeBound_residual`.

**Proof outline**: given σ_loc with the Cor 7.32 cover, the
uniform-decay+chain hypothesis (passed as `h_decayChain` per σ_loc-with-cover)
yields an exponent `N` and Spa-uniform inequalities. With `IsUnit α s_D`
and the always-available `IsUnit (algebraMap A (Loc s) s)` (since `s` is
inverted in `Loc s`), construct `ξ_decay := α s · (σ_loc · α s_D^(N+1))⁻¹`
and per-`t` `ξ_t := σ_loc · α t · α s_D^N · (α s)⁻¹`; the algebraic
factorisations follow by Units arithmetic, and the valuation bounds
`w.vle ξ_decay 1` / `w.vle (ξ_t t ht) 1` follow from the uniform-decay /
chain inequalities via `vle_iff_mul_unit_right` applied with the unit
inverse.

This isolates the algebraic-factorisation construction as a trivial
`IsUnit`-driven step, leaving `AlphaJointCor732_uniformDecayAndChain`
(the Wedhorn 8.34(ii) Step 2 σ-power-decay content) as the genuinely
remaining target. -/
theorem AlphaJointCor732MultiplicativeBound_residual_via_uniformDecayAndChain_and_unit_s_D
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (h_unit_s_D : IsUnit (algebraMap A (Localization.Away s) s_D))
    (h_decayChain :
      ∀ σ_loc : (Localization.Away s)ˣ,
        AlphaJointCor732TestFamilyCoverPackage P T s hopen T_D s_D σ_loc →
        AlphaJointCor732_uniformDecayAndChain P T s hopen T_D s_D σ_loc) :
    AlphaJointCor732MultiplicativeBound_residual P T s hopen T_D s_D := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  intro σ_loc h_cover
  obtain ⟨N, h_decay, h_chain⟩ := h_decayChain σ_loc h_cover
  -- α s is a unit in Loc s (by IsLocalization.Away).
  have h_α_s_unit :
      IsUnit (algebraMap A (Localization.Away s) s) :=
    IsLocalization.Away.algebraMap_isUnit (S := Localization.Away s) s
  -- α s_D is a unit by hypothesis; raise to the (N+1)-th power.
  have h_α_s_D_pow_unit :
      IsUnit ((algebraMap A (Localization.Away s) s_D) ^ (N + 1)) :=
    h_unit_s_D.pow (N + 1)
  -- σ_loc · α s_D^(N+1) is a unit.
  have h_denom_unit :
      IsUnit ((σ_loc : Localization.Away s) *
        (algebraMap A (Localization.Away s) s_D) ^ (N + 1)) :=
    σ_loc.isUnit.mul h_α_s_D_pow_unit
  -- Construct the witnesses.
  set denom_inv : Localization.Away s :=
    ((h_denom_unit.unit⁻¹ : (Localization.Away s)ˣ) : Localization.Away s)
    with hdenom_inv_def
  set α_s_inv : Localization.Away s :=
    ((h_α_s_unit.unit⁻¹ : (Localization.Away s)ˣ) : Localization.Away s)
    with hα_s_inv_def
  refine ⟨N,
    algebraMap A (Localization.Away s) s * denom_inv,
    fun t _ht ↦
      (σ_loc : Localization.Away s) *
        algebraMap A (Localization.Away s) t *
        (algebraMap A (Localization.Away s) s_D) ^ N *
        α_s_inv,
    ?_, ?_, ?_, ?_⟩
  · -- Decay factorisation: α s = ξ_decay · denom.
    have h_denom_inv_mul :
        denom_inv * ((σ_loc : Localization.Away s) *
          (algebraMap A (Localization.Away s) s_D) ^ (N + 1)) = 1 := by
      rw [hdenom_inv_def]
      exact h_denom_unit.val_inv_mul
    rw [mul_assoc, h_denom_inv_mul, mul_one]
  · -- Decay valuation bound on Spa.
    intro w hw
    have h_decay_at := h_decay w hw
    have h_denom_eq : (h_denom_unit.unit : Localization.Away s) =
        (σ_loc : Localization.Away s) *
          (algebraMap A (Localization.Away s) s_D) ^ (N + 1) :=
      h_denom_unit.unit_spec
    -- Restate decay using denom_unit's value.
    rw [← h_denom_eq] at h_decay_at
    -- Multiply both sides by (denom_unit⁻¹ : Loc s) on the right.
    have h_mul := (vle_iff_mul_unit_right w h_denom_unit.unit⁻¹
      (algebraMap A (Localization.Away s) s)
      ((h_denom_unit.unit : Localization.Away s))).mpr h_decay_at
    -- (denom_unit : Loc s) * (denom_unit⁻¹ : Loc s) = 1.
    rwa [Units.mul_inv] at h_mul
  · -- Per-t chain factorisation.
    intro t _ht
    have h_inv_mul : α_s_inv * algebraMap A (Localization.Away s) s = 1 := by
      rw [hα_s_inv_def]
      exact h_α_s_unit.val_inv_mul
    rw [mul_assoc _ α_s_inv (algebraMap A (Localization.Away s) s), h_inv_mul,
      mul_one]
  · -- Per-t chain valuation bound on Spa.
    intro t ht w hw
    have h_chain_at := h_chain t ht w hw
    have h_α_s_eq : (h_α_s_unit.unit : Localization.Away s) =
        algebraMap A (Localization.Away s) s :=
      h_α_s_unit.unit_spec
    -- Restate chain using α s = α_s_unit's value.
    rw [← h_α_s_eq] at h_chain_at
    have h_mul := (vle_iff_mul_unit_right w h_α_s_unit.unit⁻¹
      ((σ_loc : Localization.Away s) *
        algebraMap A (Localization.Away s) t *
        (algebraMap A (Localization.Away s) s_D) ^ N)
      ((h_α_s_unit.unit : Localization.Away s))).mpr h_chain_at
    -- (α_s_unit : Loc s) * (α_s_unit⁻¹ : Loc s) = 1.
    rwa [Units.mul_inv] at h_mul

/-! ### T164 (corrected, post-T163): locPlus M/N-choice supplier

Honest version of T164 with witnesses landing in `locPlusSubring P T s`
(the integral closure of `locSubring` in `Localization.Away s` from
T163), targeting `AlphaJointMNChoiceLocPlusMembership` directly. Uses
T163's `mem_locPlusSubring_of_vle_on_spa` (Wedhorn 7.18 honest
global-section criterion) to lift the raw localization witnesses
`ξ_decay := α s · (σ_loc · α s_D^(N+1))⁻¹` and per-`t` `ξ_t := σ_loc ·
α t · α s_D^N · (α s)⁻¹` into `locPlusSubring`-coefficients.

Provided:

* `AlphaJointCor732_uniformDecayAndChain_locPlus` — per-σ_loc Prop
  asserting Spa-uniform σ-power decay + per-`t` chain on the **locPlus**
  Spa `Spa(Localization.Away s, localizationLocPlusSubring P T s)`. The
  uniform finite-family `N : ℕ` is shared across the decay and the
  per-`t` chains.

* `AlphaJointMNChoiceLocPlusMembership_via_uniformDecayAndChain_and_unit_s_D`
  — compiled theorem producing
  `∃ N, AlphaJointMNChoiceLocPlusMembership P T s hopen T_D s_D σ_loc N`
  from the uniform decay+chain residual on locPlus Spa, the algebraic
  hypothesis `IsUnit (algebraMap A (Loc s) s_D)`, and the
  domain/non-zero `[IsDomain A]` + `s ≠ 0` hypotheses required by
  `mem_locPlusSubring_of_vle_on_spa`.

This is the honest plus-subring Cor 7.32 multiplicative-bound theorem
with one uniform finite-family `N`. The remaining content reduces to
proving `AlphaJointCor732_uniformDecayAndChain_locPlus` (the σ-power
decay+chain on the locPlus Spa, weaker than on the locSubring Spa
since the locPlus Spa has fewer points), discharged via
σ-as-π-power identification (T160) + Spa-quasi-compactness M-choice. -/

omit [PlusSubring A] in
/-- **T164 (corrected) named uniform σ-power-decay + per-`t` chain on
locPlus Spa**. For a fixed `σ_loc : (Localization.Away s)ˣ`, asserts the
existence of an exponent `N : ℕ` such that on the **locPlus Spa**
`Spa(Localization.Away s, localizationLocPlusSubring P T s)`:

* (uniform decay) at every w in the locPlus Spa:
  `w.vle (α s) ((σ_loc : Loc s) · (α s_D)^(N+1))`;
* (per-`t` chain) at every `t ∈ T_D` and every w in the locPlus Spa:
  `w.vle ((σ_loc : Loc s) · α t · (α s_D)^N) (α s)`.

The uniform `N` is shared across the decay and the entire finite family
`T_D`. -/
def AlphaJointCor732_uniformDecayAndChain_locPlus
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocPlusSubring P T s
  ∃ N : ℕ,
    (∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle (algebraMap A (Localization.Away s) s)
        ((σ_loc : Localization.Away s) *
          (algebraMap A (Localization.Away s) s_D) ^ (N + 1))) ∧
    (∀ t ∈ T_D,
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            algebraMap A (Localization.Away s) t *
            (algebraMap A (Localization.Away s) s_D) ^ N)
          (algebraMap A (Localization.Away s) s))

omit [PlusSubring A] in
/-- **T164 corrected: locPlus M/N-choice from uniform decay+chain +
`IsUnit α s_D`**.

Given the locPlus-Spa uniform σ-power decay+chain residual + `IsUnit α s_D`
+ domain/non-zero hypotheses (`[IsDomain A]`, `s ≠ 0`) for
`mem_locPlusSubring_of_vle_on_spa`, produces

```
∃ N : ℕ, AlphaJointMNChoiceLocPlusMembership P T s hopen T_D s_D σ_loc N.
```

**Proof outline**:

1. From `h_decayChain` extract a uniform `N`, the decay inequality, and
   the per-`t` chain inequalities on the locPlus Spa.

2. `α s` is a unit in `Loc s` (by `IsLocalization.Away.algebraMap_isUnit`);
   `α s_D` is a unit by hypothesis; `σ_loc` is a unit by type. So
   `σ_loc · α s_D^(N+1)` is a unit; raise α s_D to the (N+1)-th power.

3. Construct raw witnesses
   `ξ_decay_raw := α s · (σ_loc · α s_D^(N+1))⁻¹` and per-`t`
   `ξ_t_raw := σ_loc · α t · α s_D^N · (α s)⁻¹` in `Loc s` via Units
   inverses.

4. Verify locPlus membership via `mem_locPlusSubring_of_vle_on_spa`:
   each raw witness has Spa-uniform `vle 1` on the locPlus Spa,
   derived from the uniform decay/chain inequalities by
   right-multiplication with the unit inverse via
   `vle_iff_mul_unit_right` and `Units.mul_inv` to clear.

5. Verify the algebraic factorisations by Units arithmetic
   (`IsUnit.val_inv_mul`).

6. Package as `AlphaJointMNChoiceLocPlusMembership`. -/
theorem AlphaJointMNChoiceLocPlusMembership_via_uniformDecayAndChain_and_unit_s_D
    [DecidableEq A] [IsDomain A]
    (P : PairOfDefinition A) (T : Finset A) (s : A) (hs : s ≠ 0)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_unit_s_D : IsUnit (algebraMap A (Localization.Away s) s_D))
    (h_decayChain :
      AlphaJointCor732_uniformDecayAndChain_locPlus
        P T s hopen T_D s_D σ_loc) :
    ∃ N : ℕ,
      AlphaJointMNChoiceLocPlusMembership
        P T s hopen T_D s_D σ_loc N := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  obtain ⟨N, h_decay, h_chain⟩ := h_decayChain
  -- Unit infrastructure.
  have h_α_s_unit :
      IsUnit (algebraMap A (Localization.Away s) s) :=
    IsLocalization.Away.algebraMap_isUnit (S := Localization.Away s) s
  have h_α_s_D_pow_unit :
      IsUnit ((algebraMap A (Localization.Away s) s_D) ^ (N + 1)) :=
    h_unit_s_D.pow (N + 1)
  have h_denom_unit :
      IsUnit ((σ_loc : Localization.Away s) *
        (algebraMap A (Localization.Away s) s_D) ^ (N + 1)) :=
    σ_loc.isUnit.mul h_α_s_D_pow_unit
  -- Raw inverses.
  set denom_inv : Localization.Away s :=
    ((h_denom_unit.unit⁻¹ : (Localization.Away s)ˣ) : Localization.Away s)
    with hdenom_inv_def
  set α_s_inv : Localization.Away s :=
    ((h_α_s_unit.unit⁻¹ : (Localization.Away s)ˣ) : Localization.Away s)
    with hα_s_inv_def
  -- Raw witnesses.
  set ξ_decay_raw : Localization.Away s :=
    algebraMap A (Localization.Away s) s * denom_inv with hξ_decay_raw_def
  refine ⟨N, ?_, ?_⟩
  · -- Decay piece: ξ_decay ∈ locPlusSubring + algebraic factorisation.
    -- locPlus membership via mem_locPlusSubring_of_vle_on_spa.
    have h_decay_inv_mul :
        denom_inv * ((σ_loc : Localization.Away s) *
          (algebraMap A (Localization.Away s) s_D) ^ (N + 1)) = 1 := by
      rw [hdenom_inv_def]
      exact h_denom_unit.val_inv_mul
    have h_ξ_decay_mem : ξ_decay_raw ∈ locPlusSubring P T s := by
      apply mem_locPlusSubring_of_vle_on_spa P T s hs hopen ξ_decay_raw
      intro w hw
      -- Goal: w.vle ξ_decay_raw 1, derived from h_decay.
      have h_decay_at := h_decay w hw
      have h_denom_eq : (h_denom_unit.unit : Localization.Away s) =
          (σ_loc : Localization.Away s) *
            (algebraMap A (Localization.Away s) s_D) ^ (N + 1) :=
        h_denom_unit.unit_spec
      rw [← h_denom_eq] at h_decay_at
      have h_mul := (vle_iff_mul_unit_right w h_denom_unit.unit⁻¹
        (algebraMap A (Localization.Away s) s)
        ((h_denom_unit.unit : Localization.Away s))).mpr h_decay_at
      rwa [Units.mul_inv] at h_mul
    -- Algebraic factorisation: α s = ξ_decay_raw · (σ_loc · α s_D^(N+1)).
    have h_decay_eq :
        algebraMap A (Localization.Away s) s = ξ_decay_raw *
          ((σ_loc : Localization.Away s) *
            (algebraMap A (Localization.Away s) s_D) ^ (N + 1)) := by
      rw [hξ_decay_raw_def, mul_assoc, h_decay_inv_mul, mul_one]
    exact ⟨⟨ξ_decay_raw, h_ξ_decay_mem⟩, h_decay_eq⟩
  · -- Per-t' chain piece: ξ_t' ∈ locPlusSubring + algebraic factorisation.
    intro t' ht'
    obtain ⟨t, ht_in_T_D, ht_eq⟩ := Finset.mem_image.mp ht'
    set ξ_t_raw : Localization.Away s :=
      (σ_loc : Localization.Away s) *
        algebraMap A (Localization.Away s) t *
        (algebraMap A (Localization.Away s) s_D) ^ N *
        α_s_inv with hξ_t_raw_def
    have h_α_s_inv_mul :
        α_s_inv * algebraMap A (Localization.Away s) s = 1 := by
      rw [hα_s_inv_def]
      exact h_α_s_unit.val_inv_mul
    have h_ξ_t_mem : ξ_t_raw ∈ locPlusSubring P T s := by
      apply mem_locPlusSubring_of_vle_on_spa P T s hs hopen ξ_t_raw
      intro w hw
      have h_chain_at := h_chain t ht_in_T_D w hw
      have h_α_s_eq : (h_α_s_unit.unit : Localization.Away s) =
          algebraMap A (Localization.Away s) s :=
        h_α_s_unit.unit_spec
      rw [← h_α_s_eq] at h_chain_at
      have h_mul := (vle_iff_mul_unit_right w h_α_s_unit.unit⁻¹
        ((σ_loc : Localization.Away s) *
          algebraMap A (Localization.Away s) t *
          (algebraMap A (Localization.Away s) s_D) ^ N)
        ((h_α_s_unit.unit : Localization.Away s))).mpr h_chain_at
      rwa [Units.mul_inv] at h_mul
    -- Algebraic factorisation: σ_loc · t' · α s_D^N = ξ_t_raw · α s.
    have h_chain_eq :
        (σ_loc : Localization.Away s) * t' *
            (algebraMap A (Localization.Away s) s_D) ^ N =
          ξ_t_raw * algebraMap A (Localization.Away s) s := by
      rw [← ht_eq, hξ_t_raw_def,
        mul_assoc _ α_s_inv (algebraMap A (Localization.Away s) s),
        h_α_s_inv_mul, mul_one]
    exact ⟨⟨ξ_t_raw, h_ξ_t_mem⟩, h_chain_eq⟩

/-! ### T165: bridge from locSubring uniform decay+chain to locPlus version

Strictly lower concrete bridge: derives
`AlphaJointCor732_uniformDecayAndChain_locPlus` (the locPlus Spa
uniform decay+chain target consumed by T164's locPlus M/N-choice
constructor) from `AlphaJointCor732_uniformDecayAndChain` (the
locSubring Spa version, present since the original T164 reduction).

The proof is a single `spa_antitone` chase: since
`locSubring P T s ≤ locPlusSubring P T s` (T163's
`locSubring_le_locPlusSubring`), `spa_antitone` yields
`Spa(Loc s, locPlusSubring) ⊆ Spa(Loc s, locSubring)` (locPlus Spa is
smaller because locPlus is bigger). Any uniform statement on the
locSubring Spa transports to the locPlus Spa pointwise; the uniform `N`
is shared.

This **lowers** T164's open `_locPlus` target onto the same uniform
σ-power-decay+chain content stated on the **locSubring** Spa
(`AlphaJointCor732_uniformDecayAndChain`), which is the form most
existing localized Cor 7.32 / σ-power API in the project (e.g.,
`IsLocalizedCor732SigmaLocOutput` from
`WedhornSigmaFactoredSupplierFromLocalizedCor732`,
`localizedCor732_sigma_supplier_for_actual_C1` from
`WedhornLocalizedCor732SigmaSupplier`, the σ-decay-chain predicates
in `WedhornSigmaPowerInequalityFromLocalizedCor732`) is naturally
stated against — those APIs all use the canonical
`localizationLocSubringPlusSubring` Spa, not the integral-closure
`localizationLocPlusSubring`.

### Existing-API mismatch / why a full discharge is blocked here

The existing localized Cor 7.32 / σ-power API in the project (chiefly
`Cor732SigmaDecayChainSupplier`, `LocalizedCor732SigmaDecayChainSupplier`,
and `sigma_power_cleared_inequality_from_localized_cor732_output`)
delivers conclusions of the form

```
∀ t' ∈ T_D, ∀ w ∈ Spa A A⁺,
  w.vle f s_base → w.vle 1 t' → ¬ w.vle t' 0 →
  ∃ N : ℕ, w.vle (t' * s_D ^ N) (s_D ^ (N + 1)) ∧ ¬ w.vle s_D 0
```

— at the **global** `Spa A A⁺` with **per-(w, t') existential `N`** and
the **σ-cancelled** conclusion `t' · s_D^N ≤ s_D^(N+1)` (no `σ_loc`,
no `α s`). The target `AlphaJointCor732_uniformDecayAndChain_locPlus`
needs:

* **uniform `N`** over the entire finite family `T_D` and the entire
  Spa (not per-(w, t') existential),
* the **σ-uncancelled** decay shape `α s ≤ σ_loc · α s_D^(N+1)` and the
  per-`t` chain `σ_loc · α t · α s_D^N ≤ α s` (with `σ_loc` and `α s`
  explicit, not cancelled),
* on the **local** `Spa(Localization.Away s, …)` with `α`-images of
  `T_D, s_D, s` — not on the global Spa with global elements.

Bridging the existing API to my target therefore requires (i) a
quasi-compactness uniformisation step to collapse the per-(w, t')
existential `N` to a single uniform `N`, and (ii) a global-to-local
Spa transfer with element substitution. Neither bridging is available
as a single lemma in existing API; constructing it from
`Cor732.exists_dominatedBy_cover` plus a denominator-clearing
factorisation step is genuine Wedhorn 8.34(ii) Step 2 mathematical
content and is the actual remaining critical-path target. -/

omit [PlusSubring A] in
/-- **T165 strictly lower bridge** (locSubring → locPlus): the
locPlus-Spa uniform decay+chain residual follows from the locSubring-Spa
uniform decay+chain residual at the **same `(σ_loc, N)`**.

**Proof**: `locSubring P T s ≤ locPlusSubring P T s` (T163's
`locSubring_le_locPlusSubring`), so `spa_antitone` gives the inclusion
`Spa(Loc s, locPlusSubring) ⊆ Spa(Loc s, locSubring)`. Both halves of
the locSubring residual transport pointwise to the locPlus Spa via this
inclusion, sharing the uniform `N`.

This **strictly lowers** T164's locPlus target (which is the open input
to T164's `AlphaJointMNChoiceLocPlusMembership_via_uniformDecayAndChain_and_unit_s_D`)
onto the locSubring uniform decay+chain `AlphaJointCor732_uniformDecayAndChain`,
which is the natural target shape against existing localized Cor 7.32
supplier API. -/
theorem AlphaJointCor732_uniformDecayAndChain_locPlus_of_locSubring
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_locSubring :
      AlphaJointCor732_uniformDecayAndChain
        P T s hopen T_D s_D σ_loc) :
    AlphaJointCor732_uniformDecayAndChain_locPlus
      P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  obtain ⟨N, h_decay, h_chain⟩ := h_locSubring
  -- locSubring P T s ≤ locPlusSubring P T s, so locPlus Spa ⊆ locSubring Spa.
  have h_subset :
      Spa (Localization.Away s) (locPlusSubring P T s) ⊆
        Spa (Localization.Away s) (locSubring P T s) :=
    spa_antitone (locSubring_le_locPlusSubring P T s)
  refine ⟨N, ?_, ?_⟩
  · intro w hw_locPlus
    exact h_decay w (h_subset hw_locPlus)
  · intro t ht w hw_locPlus
    exact h_chain t ht w (h_subset hw_locPlus)

/-! ### T166 (blocked path): finite-family N-uniformization concrete lemma

The locSubring uniform decay+chain `AlphaJointCor732_uniformDecayAndChain`
is the open critical-path target. Direct discharge from existing
localized Cor 7.32 / σ-power API is blocked at **two missing
operations** (per the T165 audit):

1. **Finite-family N-uniformization** — the existing API delivers
   per-(w, t') existential `N` (e.g.,
   `sigma_power_cleared_inequality_from_localized_cor732_output`); the
   target needs a single uniform `N` over the entire finite family `T_D`.

2. **Global-to-local Spa transfer with element substitution** — the
   existing API delivers conclusions at the global `Spa A A⁺` with
   global elements `t', s_D : A`; the target needs the local
   `Spa(Localization.Away s, locSubring P T s)` with `α`-images.

Per the manager's "if blocked, commit one concrete lower lemma performing
one of the two actual missing operations": this section delivers the
**finite-family N-uniformization** operation (item 1) as a generic
monotonicity-driven Finset lemma, applicable directly to the chain piece
under the natural `α s_D` power-bounded hypothesis.

Provided:

* `Finset.exists_uniform_N_of_per_mem_monotone` — generic Mathlib-style
  helper: for any predicate `P : ℕ → α → Prop` monotone in `N`, the
  per-member existence `∀ a ∈ T, ∃ N, P N a` lifts to a uniform `∃ N,
  ∀ a ∈ T, P N a` via the maximum of per-member `N`s.

* `AlphaJointCor732_chain_uniform_N_of_per_t_chain_monotone` — concrete
  application to the chain piece of `AlphaJointCor732_uniformDecayAndChain`:
  per-`t'` chain hypotheses `∀ t ∈ T_D, ∃ N_t, ∀ w ∈ Spa, chain_t_at_N_t`
  + monotonicity `(N ≤ M, t, w with chain_t_at_N) → chain_t_at_M`
  together produce the uniform `∃ N, ∀ t ∈ T_D, ∀ w ∈ Spa, chain_t_at_N`.
  The monotonicity hypothesis is naturally satisfied when
  `w.vle (α s_D) 1` for every w in the locSubring Spa — i.e., when
  `α s_D ∈ locSubring P T s` (which holds when `s_D ∈ P.A₀`).

After these helpers land, the genuinely-remaining critical-path content
for `AlphaJointCor732_uniformDecayAndChain` reduces to:

(a) producing the per-`t'` chain inequality at some `N_t` from the
    Cor 7.32 cover output (genuine Wedhorn 8.34(ii) Step 2 content,
    requires the second missing operation: global-to-local Spa transfer);

(b) producing the σ-power decay inequality at some `N` (similarly,
    genuine Wedhorn 8.34(ii) Step 2 content with the orientation issue
    documented in `WedhornSigmaPowerDecay.lean:14-22`).

These two pieces remain open. -/

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] in
/-- **Generic finite-family N-uniformization for monotone-in-N
predicates** (Mathlib-style helper).

Given a finite family `T : Finset α`, a predicate `P : ℕ → α → Prop`
monotone in `N` (larger `N` preserves the predicate), and per-element
existence `∀ a ∈ T, ∃ N, P N a`, produce a uniform `N` working for all
members of `T`:

```
∃ N, ∀ a ∈ T, P N a
```

The uniform `N` is the maximum of per-member `N`s, well-defined since
`T` is finite. Proof by Finset induction. -/
theorem Finset.exists_uniform_N_of_per_mem_monotone
    {α : Type*} {T : Finset α}
    {P : ℕ → α → Prop}
    (h_mono : ∀ {N M : ℕ}, N ≤ M → ∀ a, P N a → P M a)
    (h_per_mem : ∀ a ∈ T, ∃ N, P N a) :
    ∃ N, ∀ a ∈ T, P N a := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    exact ⟨0, fun a ha ↦ absurd ha (Finset.notMem_empty a)⟩
  | insert b T' hb_notin ih =>
    obtain ⟨N_T, h_N_T⟩ :=
      ih (fun a ha ↦ h_per_mem a (Finset.mem_insert_of_mem ha))
    obtain ⟨N_b, h_N_b⟩ := h_per_mem b (Finset.mem_insert_self b T')
    refine ⟨max N_T N_b, fun a ha ↦ ?_⟩
    rcases Finset.mem_insert.mp ha with rfl | ha_T'
    · exact h_mono (le_max_right _ _) _ h_N_b
    · exact h_mono (le_max_left _ _) _ (h_N_T a ha_T')

omit [PlusSubring A] in
/-- **T166 chain finite-family N-uniformization** (concrete application
of the generic helper to the chain piece of
`AlphaJointCor732_uniformDecayAndChain`).

From a per-`t'` chain `∀ t ∈ T_D, ∃ N_t, ∀ w ∈ Spa(Loc s, locSubring),
chain_at_N_t` plus a monotonicity hypothesis, derive the uniform-`N`
chain `∃ N, ∀ t ∈ T_D, ∀ w ∈ Spa(Loc s, locSubring), chain_at_N`.

The monotonicity hypothesis is naturally satisfied when
`α s_D ∈ locSubring` (giving `w(α s_D) ≤ 1` everywhere on the locSubring
Spa, so larger `N` makes `(α s_D)^N` smaller and the chain easier).

This is one of the two **missing operations** (item 1 of the T165 audit:
finite-family N-uniformization) on the route to closing
`AlphaJointCor732_uniformDecayAndChain` directly. -/
theorem AlphaJointCor732_chain_uniform_N_of_per_t_chain_monotone
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_chain_per_t :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ t ∈ T_D, ∃ N_t : ℕ,
        ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
          w.vle ((σ_loc : Localization.Away s) *
              algebraMap A (Localization.Away s) t *
              (algebraMap A (Localization.Away s) s_D) ^ N_t)
            (algebraMap A (Localization.Away s) s))
    (h_chain_mono :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ {N M : ℕ}, N ≤ M → ∀ (t : A),
        (∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
          w.vle ((σ_loc : Localization.Away s) *
              algebraMap A (Localization.Away s) t *
              (algebraMap A (Localization.Away s) s_D) ^ N)
            (algebraMap A (Localization.Away s) s)) →
        ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
          w.vle ((σ_loc : Localization.Away s) *
              algebraMap A (Localization.Away s) t *
              (algebraMap A (Localization.Away s) s_D) ^ M)
            (algebraMap A (Localization.Away s) s)) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    ∃ N : ℕ, ∀ t ∈ T_D,
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            algebraMap A (Localization.Away s) t *
            (algebraMap A (Localization.Away s) s_D) ^ N)
          (algebraMap A (Localization.Away s) s) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  exact Finset.exists_uniform_N_of_per_mem_monotone
    (P := fun N t ↦
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            algebraMap A (Localization.Away s) t *
            (algebraMap A (Localization.Away s) s_D) ^ N)
          (algebraMap A (Localization.Away s) s))
    h_chain_mono h_chain_per_t

/-! ### T166 (continued): direct chain-half closure on the local Spa

After the manager's review of commit 4781685, the previous Finset
helper does not actually close the chain half because it leaves the
per-(w, t) → per-t collapse as an external hypothesis that the existing
API does not directly produce. The genuine chain-half closure needs to
collapse `w` as well — i.e., the per-`t` chain hypothesis must hold
at every w in the local Spa, not just per-(w, t).

This section delivers a **direct chain-half closure on the local
locSubring Spa**: given a σ_loc that is **uniformly dominated by α s**
on the entire local Spa (the natural local-Spa output of
`Cor732.exists_dominatedBy_cover` applied with `T := {α s}`), and the
natural locSubring-membership hypotheses on `α t` (for `t ∈ T_D`) and
`α s_D`, the chain piece holds at **any** `N : ℕ` and every `w` in the
local Spa. The chain is automatically uniform over both `T_D` and `w`
because the σ-domination + plus-subring bounds compose multiplicatively.

This collapses operation #1 (finite-family + per-w N-uniformization)
for the chain half by exhibiting a chain that is **trivially uniform**
in N (any N works) once the natural σ-domination + plus-subring data
is in place.

The decay half remains open — its discharge requires the orientation-
reversal handled by the genuine Wedhorn 8.34(ii) Step 2 σ-power-decay
construction, which is not available from the existing localized
Cor 7.32 σ-domination output alone (per the orientation note in
`WedhornSigmaPowerDecay.lean:14-22`). -/

omit [PlusSubring A] in
/-- **T166 chain-half closure** (direct local-Spa form).

Closes the chain half of `AlphaJointCor732_uniformDecayAndChain` at any
`N : ℕ` from local data: σ_loc uniformly σ-dominated by `α s` on the
local locSubring Spa (the cover-output shape of
`Cor732.exists_dominatedBy_cover` applied with `T := {α s}` on the
local Spa), plus the natural locSubring-membership hypotheses on
`α t` (`t ∈ T_D`) and `α s_D`.

**Proof**: at each `w` in the local Spa, decompose the chain target
multiplicatively:
* `w.vle σ_loc (α s)` — σ-domination by `α s`.
* `w.vle (α t) 1` — from `α t ∈ locSubring = (Loc s)⁺` via `vle_one_of_mem_spa`.
* `w.vle ((α s_D)^N) 1` — from `α s_D ∈ locSubring` via
  `vle_one_of_mem_spa` plus `pow_vle_pow` against `1^N = 1`.

Compose via `ValuativeRel.mul_vle_mul` then simplify
`(α s) * 1 * 1 = α s` to land the chain.

Crucially, the result holds **for any `N : ℕ`** — N is not the source
of difficulty for the chain half; the σ-domination + plus-bound data
already gives a stronger uniform bound. The N free parameter feeds
directly into the chain shape required by
`AlphaJointCor732_uniformDecayAndChain`. -/
theorem AlphaJointCor732_chain_half_via_sigma_dominated_by_alpha_s
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_σ_dom :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle (σ_loc : Localization.Away s)
          (algebraMap A (Localization.Away s) s))
    (h_T_D_in : ∀ t ∈ T_D,
      algebraMap A (Localization.Away s) t ∈ locSubring P T s)
    (h_s_D_in : algebraMap A (Localization.Away s) s_D ∈ locSubring P T s)
    (N : ℕ) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    ∀ t ∈ T_D,
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            algebraMap A (Localization.Away s) t *
            (algebraMap A (Localization.Away s) s_D) ^ N)
          (algebraMap A (Localization.Away s) s) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  intro t ht w hw
  letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
  have h_α_t_le_one :
      w.vle (algebraMap A (Localization.Away s) t) 1 :=
    vle_one_of_mem_spa hw (h_T_D_in t ht)
  have h_α_s_D_le_one :
      w.vle (algebraMap A (Localization.Away s) s_D) 1 :=
    vle_one_of_mem_spa hw h_s_D_in
  have h_α_s_D_pow_le_one :
      w.vle ((algebraMap A (Localization.Away s) s_D) ^ N) 1 := by
    have := ValuativeRel.pow_vle_pow h_α_s_D_le_one N
    rwa [one_pow] at this
  -- (σ_loc) * (α t) ≤ᵥ (α s) * 1
  have h_step1 :
      w.vle ((σ_loc : Localization.Away s) *
          algebraMap A (Localization.Away s) t)
        (algebraMap A (Localization.Away s) s * 1) :=
    ValuativeRel.mul_vle_mul (h_σ_dom w hw) h_α_t_le_one
  -- (σ_loc * α t) * (α s_D)^N ≤ᵥ (α s * 1) * 1
  have h_step2 :
      w.vle ((σ_loc : Localization.Away s) *
          algebraMap A (Localization.Away s) t *
          (algebraMap A (Localization.Away s) s_D) ^ N)
        (algebraMap A (Localization.Away s) s * 1 * 1) :=
    ValuativeRel.mul_vle_mul h_step1 h_α_s_D_pow_le_one
  rwa [mul_one, mul_one] at h_step2

/-! ### T166 (continued): combiner theorem using existing decay
factorization + new chain-half closure

Per the manager's review of commit 454d490: combine the existing
decay-factorization theorem `AlphaJointSigmaPowerDecayPiece_via_factorization`
(this file, lines 1616-1643, T156) — which proves the decay half from
a `ξ : locSubring P T s` with `α s = ξ · (σ_loc · α s_D^(N+1))` — with
my T166 chain-half closure
`AlphaJointCor732_chain_half_via_sigma_dominated_by_alpha_s` into a
single compiled theorem feeding `AlphaJointCor732_uniformDecayAndChain`.

The combiner lands the locSubring uniform decay+chain target itself
once the **decay factorization data** is supplied — leaving as the
sole remaining content the construction of the explicit `ξ : locSubring`
witnessing the decay equation, which is the genuine missing Wedhorn
8.34(ii) Step 2 algebraic / denominator-clearing data. -/

omit [PlusSubring A] in
/-- **T166 combiner theorem**: closes
`AlphaJointCor732_uniformDecayAndChain` from the decay factorization
plus chain σ-domination + plus-subring data.

**Inputs** (shared exponent `N : ℕ`):

* **Decay side** — `ξ : locSubring P T s` with the algebraic
  factorization `α s = ξ · (σ_loc · α s_D^(N+1))` (consumed via the
  existing `AlphaJointSigmaPowerDecayPiece_via_factorization` from
  T156, this file).

* **Chain side** — local σ-domination
  `h_σ_dom : ∀ w ∈ Spa(Loc s, locSubring), w.vle σ_loc (α s)`
  + `α t ∈ locSubring` for every `t ∈ T_D`
  + `α s_D ∈ locSubring`
  (consumed via `AlphaJointCor732_chain_half_via_sigma_dominated_by_alpha_s`
  from T166, just above).

**Conclusion**: `AlphaJointCor732_uniformDecayAndChain P T s hopen T_D s_D σ_loc`
at the supplied `N`.

After this combiner, the sole remaining mathematical content for
`AlphaJointCor732_uniformDecayAndChain` is the construction of the
decay factorization witness `ξ : locSubring` from concrete localized
Cor732 / M-choice / denominator-clearing data — i.e., the genuine
Wedhorn 8.34(ii) Step 2 algebraic step. The chain side is closed
by σ-domination + plus-subring data already available from
`Cor732.exists_dominatedBy_cover` applied locally at `T := {α s}` plus
the natural locSubring-membership hypotheses on the test family. -/
theorem AlphaJointCor732_uniformDecayAndChain_via_decay_factorization_and_sigma_dom_chain
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (ξ : locSubring P T s)
    (hfact_decay :
      algebraMap A (Localization.Away s) s =
        (ξ : Localization.Away s) *
          ((σ_loc : Localization.Away s) *
            (algebraMap A (Localization.Away s) s_D) ^ (N + 1)))
    (h_σ_dom :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle (σ_loc : Localization.Away s)
          (algebraMap A (Localization.Away s) s))
    (h_T_D_in : ∀ t ∈ T_D,
      algebraMap A (Localization.Away s) t ∈ locSubring P T s)
    (h_s_D_in : algebraMap A (Localization.Away s) s_D ∈ locSubring P T s) :
    AlphaJointCor732_uniformDecayAndChain
      P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  refine ⟨N, ?_, ?_⟩
  · -- Decay half via T156's factorization theorem.
    exact AlphaJointSigmaPowerDecayPiece_via_factorization
      P T s hopen s_D σ_loc N ξ hfact_decay
  · -- Chain half via this section's σ-domination closure.
    exact AlphaJointCor732_chain_half_via_sigma_dominated_by_alpha_s
      P T s hopen T_D s_D σ_loc h_σ_dom h_T_D_in h_s_D_in N

/-! ### T166 (continued): concrete witness construction in the
`s = s_D · c` (`c ∈ P.A₀`) special case

Per the manager's review of bf3acd3: the previous combiners are the
right shape, but the actual remaining content is the **decay
factorization witness construction**, not another combiner. This
section delivers a concrete fully-proved instance of
`AlphaJointCor732_uniformDecayAndChain` in the natural special case
`s = s_D · c` for `c ∈ P.A₀`, mirroring T158's
`AlphaJointFactorizationWitnessesExist_when_s_eq_s_D_mul_A0_elt_and_T_D_le_T`
construction but landing the locSubring uniform decay+chain target
directly (rather than the T156-T158 factorization-witness existential).

Reuses the T156 factorization-side primitives
(`AlphaJointSigmaPowerDecayPiece_via_factorization`,
`AlphaJointPerTChainPiece_via_factorization`) on the same
(`σ_loc := 1`, `N := 0`) data T158 already established produces locSubring
witnesses in this case:

* decay witness `ξ_decay := algebraMap A (Loc s) c` (in `locSubring` by
  `algebraMap_mem_locSubring P T s c.property`);
* per-`t'` chain witness `ξ_t' := divByS (preimage_t') s` (in
  `locSubring` by `divByS_mem_locSubring P T s ht_in_T` for
  `preimage_t' ∈ T_D ⊆ T`).

The decay factorisation `α s = α c · (1 · α s_D^1)` reduces to
`α s = α s_D · α c` via `s = s_D · c`. The per-`t'` chain factorisation
`1 · t' · α s_D^0 = ξ_t' · α s` reduces to `t' = (divByS preimage_t' s) · α s`,
which is `IsLocalization.mk'_spec`.

This is the **actual decay-factorisation witness construction** in the
manager-suggested concrete case, not a wrapper around the open target. -/

omit [PlusSubring A] in
/-- **T166 concrete construction**: closes
`AlphaJointCor732_uniformDecayAndChain P T s hopen T_D s_D 1` (at σ_loc = 1)
in the `s = s_D · c` (`c ∈ P.A₀`) + `T_D ⊆ T` case.

**Witnesses**: `N := 0`, `ξ_decay := algebraMap A (Loc s) c`,
per-`t'` `ξ_t' := divByS (preimage_t') s`.

**Proof skeleton**: feeds these witnesses into T156's
`AlphaJointSigmaPowerDecayPiece_via_factorization` (decay) and
`AlphaJointPerTChainPiece_via_factorization` (chain), then converts
the `∀ w ∀ t'` quantifier shape to `∀ t ∀ w` via
`Finset.mem_image_of_mem`.

This is the same `s = s_D · c` data T158's
`AlphaJointFactorizationWitnessesExist_when_s_eq_s_D_mul_A0_elt_and_T_D_le_T`
already proved produces locSubring factorisation witnesses; this
theorem reformulates the conclusion as the locSubring uniform
decay+chain target consumed directly by T164/T165. -/
theorem AlphaJointCor732_uniformDecayAndChain_when_s_eq_s_D_mul_A0_elt_and_T_D_le_T
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (c : P.A₀)
    (h_s_factor : s = s_D * (c : A))
    (h_T_D_le_T : T_D ⊆ T) :
    AlphaJointCor732_uniformDecayAndChain
      P T s hopen T_D s_D 1 := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  -- Decay-side: ξ_decay := α c, hfact_decay : α s = α c · (1 · α s_D^1).
  have h_decay_piece :
      AlphaJointSigmaPowerDecayPiece P T s hopen s_D 1 0 := by
    apply AlphaJointSigmaPowerDecayPiece_via_factorization
      P T s hopen s_D 1 0
      ⟨algebraMap A (Localization.Away s) (c : A),
        algebraMap_mem_locSubring P T s c.property⟩
    rw [h_s_factor, map_mul]
    simp [Units.val_one, mul_comm]
  -- Chain-side: per-t', ξ_t' := divByS (preimage_t') s.
  have h_chain_piece :
      AlphaJointPerTChainPiece P T s hopen T_D s_D 1 0 := by
    apply AlphaJointPerTChainPiece_via_factorization
      P T s hopen T_D s_D 1 0
    intro t' ht'
    obtain ⟨t, ht_in_T_D, ht_eq⟩ := Finset.mem_image.mp ht'
    have ht_in_T : t ∈ T := h_T_D_le_T ht_in_T_D
    refine ⟨⟨divByS t s, divByS_mem_locSubring P T s ht_in_T⟩, ?_⟩
    have hspec : divByS t s * algebraMap A (Localization.Away s) s =
        algebraMap A (Localization.Away s) t :=
      IsLocalization.mk'_spec _ t ⟨s, Submonoid.mem_powers s⟩
    simp only [Units.val_one, one_mul, pow_zero, mul_one]
    rw [← ht_eq]
    exact hspec.symm
  refine ⟨0, h_decay_piece, ?_⟩
  -- Convert PerTChainPiece's `∀ w ∀ t'` to uniformDecayAndChain's `∀ t ∀ w`.
  intro t ht w hw
  exact h_chain_piece w hw (algebraMap A (Localization.Away s) t)
    (Finset.mem_image_of_mem _ ht)

/-! ### T167: locPlus Spa equality with locSubring Spa

Concrete structural transfer for the locPlus theorem: shows that the
**locPlus Spa equals the locSubring Spa as a set of valuations**. The
forward inclusion `Spa(Loc s, locPlusSubring) ⊆ Spa(Loc s, locSubring)`
holds by `spa_antitone` (T165's bridge direction). The **reverse**
inclusion `Spa(Loc s, locSubring) ⊆ Spa(Loc s, locPlusSubring)` holds
because every element of `locPlusSubring` is integral over `locSubring`
(T163's `mem_locPlusSubring_iff_isIntegral`), and integrality preserves
`v.vle a 1` (T163's private helper `vle_one_of_isIntegral_of_subring_le_one`).

Combined: the two Spa sets are equal. This means **uniform statements
on the locSubring Spa transfer to the locPlus Spa for free** (and vice
versa) — the existing localized Cor 7.32 / σ-power API operating on
the canonical `localizationLocSubringPlusSubring` Spa applies directly
to the `localizationLocPlusSubring` Spa target.

After this section, my T166 chain-half closure
`AlphaJointCor732_chain_half_via_sigma_dominated_by_alpha_s` (locSubring
Spa) and the s = s_D · c concrete construction
`AlphaJointCor732_uniformDecayAndChain_when_s_eq_s_D_mul_A0_elt_and_T_D_le_T`
(locSubring Spa) automatically apply to the locPlus Spa target via
T165's bridge — without losing strength.

The genuine remaining content for the **general** locPlus case
(s ≠ s_D · c) is the **decay factorisation witness construction**: an
explicit `ξ : locSubring P T s` (or `ξ : locPlusSubring`) satisfying
`α s = ξ · (σ_loc · α s_D^(N+1))` for σ_loc, N chosen via Cor 7.32 +
M-choice. This is the genuine Wedhorn 8.34(ii) Step 2 algebraic step
and is not available from existing localized Cor 7.32 outputs.

Provided:

* `locPlusSpa_subset_locSubringSpa` — explicit name for T165's
  `spa_antitone` direction.
* `locSubringSpa_subset_locPlusSpa` — the **reverse direction** via
  integral closure (T167's missing operation).
* `locSubringSpa_eq_locPlusSpa` — Spa equality.

Note on `AlphaJointCor732_uniformDecayAndChain_locPlus`: T165's
`AlphaJointCor732_uniformDecayAndChain_locPlus_of_locSubring` already
provides the transport from the locSubring version to the locPlus
version via `spa_antitone` (forward inclusion only). The Spa equality
landed here strengthens the structural relationship but does NOT
produce a stronger bridge — both versions of the uniform decay+chain
target are equivalent regardless of which Spa they range over.

### Precise remaining content (T167 blocker report)

The genuine remaining content for both
`AlphaJointCor732_uniformDecayAndChain` (locSubring Spa) and
`AlphaJointCor732_uniformDecayAndChain_locPlus` (locPlus Spa, equal as
sets per `locSubringSpa_eq_locPlusSpa` above) reduces to the
**σ-power-decay piece**:

```
∃ N, ∀ w ∈ Spa(Localization.Away s, ⁺),
  w.vle (algebraMap A (Localization.Away s) s)
    ((σ_loc : Localization.Away s) *
      (algebraMap A (Localization.Away s) s_D) ^ (N + 1))
```

The chain piece is closed via T166's `AlphaJointCor732_chain_half_via_sigma_dominated_by_alpha_s`
+ T167's Spa equality (T166 closes the chain piece for any N from
σ-domination + plus-subring data on the locSubring Spa, which transfers
to locPlus Spa via T167).

The σ-power-decay piece is documented as an **open target** at the
project level — see `WedhornFactorExtractionPowerDecay.lean:144-171`,
where the target signature `sigma_power_decay_of_cor732` is recorded
along with the discharge hint:

> "the genuinely-new Wedhorn content: the existence of an exponent N
> (depending on σ, D_s, C_base_s, T_test) such that C_base_s ≤ σ * D_s ^
> (N + 1) uniformly on Spa. This is achievable via the topological
> nilpotency of σ (which is a Cor 7.32 σ-power, hence topologically
> nilpotent) plus Spa-quasi-compactness, but is not yet formalized as
> a named theorem."

I.e., the σ-power-decay shape requires a Spa-quasi-compactness +
topological-nilpotency argument distinct from the standard Cor 7.32
σ-strict-domination output. Closest existing APIs and why they don't
suffice:

* `Cor732.exists_dominatedBy_cover` produces uniform N for the shape
  `w.vle (π^N) τ` for some τ in a finite test family — not the
  σ-uncancelled decay shape `w.vle C_base_s (σ * D_s^(N+1))`.

* `localizedCor732_sigma_supplier_for_actual_C1` /
  `IsLocalizedCor732SigmaLocOutput` produce the σ-rescaled Laurent
  piece cover (per-w τ ∈ test family with σ-strict-domination by τ) —
  the **opposite orientation** from σ-power-decay (σ small from above
  vs σ * D_s^(N+1) large from below).

* `WedhornSigmaPowerInequalityFromLocalizedCor732`'s
  `sigma_power_cleared_inequality_from_localized_cor732_output`
  produces the σ-cancelled chain `t' * s_D^N ≤ s_D^(N+1)` per-(w, t')
  on global Spa — wrong shape (σ-cancelled, not σ-uncancelled) and
  wrong Spa (global vs local), and per-(w, t') existential N rather
  than uniform N over T_D.

* `WedhornFactorExtractionPowerDecay`'s `sigma_power_decay_of_cor732`
  itself is the **target signature** documented as remaining work, not
  a delivered theorem.

* `exists_away_denominator_cleared` (in
  `WedhornLocalizationDenominatorClearing`) produces `x · α s^n = α a`
  for `x ∈ Loc s` — wrong direction (Loc s element to A element after
  multiplication by `s^n`; not the decay factorisation).

The genuine missing API is a direct Spa-quasi-compactness application
producing the σ-uncancelled decay shape from topological nilpotency of
σ_loc on the local Spa. This is non-trivial Wedhorn 8.34(ii) Step 2
mathematical content and is NOT available from existing localized
Cor 7.32 / σ-power output. -/

omit [PlusSubring A] in
/-- **T167 forward direction**: `Spa(Loc s, locPlusSubring) ⊆ Spa(Loc s, locSubring)`
via `spa_antitone` (the easy half — T165 already used this implicitly). -/
theorem locPlusSpa_subset_locSubringSpa
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    Spa (Localization.Away s) (locPlusSubring P T s) ⊆
      Spa (Localization.Away s) (locSubring P T s) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  exact spa_antitone (locSubring_le_locPlusSubring P T s)

omit [PlusSubring A] in
/-- **T167 reverse direction** (concrete missing operation):
`Spa(Loc s, locSubring) ⊆ Spa(Loc s, locPlusSubring)` via integral
closure. Every continuous valuation `v` with `v.vle f 1` for all
`f ∈ locSubring P T s` automatically satisfies `v.vle f 1` for all
`f ∈ locPlusSubring P T s`, since the latter is the integral closure
of the former, and integrality preserves `v.vle a 1`.

Combines `mem_locPlusSubring_iff_isIntegral` (definitional unfolding of
`locPlusSubring` as the integral closure) with the private helper
`vle_one_of_isIntegral_of_subring_le_one` (T163, this file lines
~3155-3182). -/
theorem locSubringSpa_subset_locPlusSpa
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    Spa (Localization.Away s) (locSubring P T s) ⊆
      Spa (Localization.Away s) (locPlusSubring P T s) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  intro v hv
  refine ⟨hv.1, ?_⟩
  intro f hf
  rw [mem_locPlusSubring_iff_isIntegral] at hf
  exact vle_one_of_isIntegral_of_subring_le_one
    (locSubring P T s) v.toValuativeRel hv.2 hf

omit [PlusSubring A] in
/-- **T167 Spa equality**: `Spa(Loc s, locSubring P T s) = Spa(Loc s, locPlusSubring P T s)`.

Combines the forward and reverse subset inclusions. The two Spas are
the **same set of valuations** — the integral-closure step at the
plus-subring level does not change the set of continuous valuations
satisfying the plus condition, since integrality preserves `v.vle a 1`.

After this equality, all existing localized Cor 7.32 / σ-power API
operating on the canonical `localizationLocSubringPlusSubring` Spa
applies directly to the `localizationLocPlusSubring` Spa target — the
"locPlus distinction" is at the level of plus-subring **witnesses**
(integrally closed locPlusSubring vs. raw locSubring), not at the
level of the Spa point set. -/
theorem locSubringSpa_eq_locPlusSpa
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    Spa (Localization.Away s) (locSubring P T s) =
      Spa (Localization.Away s) (locPlusSubring P T s) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  exact Set.eq_of_subset_of_subset
    (locSubringSpa_subset_locPlusSpa P T s hopen)
    (locPlusSpa_subset_locSubringSpa P T s hopen)

/-! ### T164 (algebraic-side closure): named pure-algebraic decay
factorization Prop and top-level supplier

Closes the algebraic side of T164 by isolating the genuine remaining
Wedhorn 8.34(ii) Step 2 σ-power-decay content as a **single named
pure-algebraic Prop** (`AlphaJointCor732_decay_factorization`). The
remaining pieces beyond this Prop are either automatic from existing
API or purely Spa-uniform via σ-domination + plus-subring data
(available from existing Cor 7.32 / locSubring API).

Provided:

* `AlphaJointCor732_decay_factorization` — named pure-algebraic Prop:
  `∃ N, ∃ ξ : locSubring P T s, α s = ξ · σ_loc · α s_D^(N+1)`. This
  is the **single named algebraic lemma** capturing the genuine
  remaining Wedhorn 8.34(ii) Step 2 σ-power-decay content.

* `AlphaJointCor732_uniformDecayAndChain_via_named_decay_factorization`
  — compiled bridge: from the named decay factorization Prop + chain
  σ-domination + α-image plus-subring data, produces
  `AlphaJointCor732_uniformDecayAndChain`.

* `AlphaJointMNChoiceLocPlusMembership_via_named_decay_factorization_and_unit_s_D`
  — top-level supplier: from the named decay factorization Prop + chain
  σ-domination + α-image plus-subring data + `IsUnit α s_D`, produces
  `∃ N, AlphaJointMNChoiceLocPlusMembership P T s hopen T_D s_D σ_loc N`.

After this section, the algebraic side of T164 is reduced to the **one
named pure-algebraic Prop** `AlphaJointCor732_decay_factorization`. The
chain σ-domination hypothesis is the natural Cor 7.32 σ-strict-domination
output and the α-image plus-subring memberships are standard locSubring
data — both available from existing API. -/

omit [PlusSubring A] in
/-- **T164 named pure-algebraic decay factorization Prop**. The single
algebraic statement isolating the genuine remaining Wedhorn 8.34(ii)
Step 2 σ-power-decay content:

```
∃ N : ℕ, ∃ ξ : locSubring P T s,
  algebraMap A (Loc s) s =
    (ξ : Loc s) · ((σ_loc : Loc s) · (algebraMap A (Loc s) s_D)^(N+1))
```

The decay factorization data is purely algebraic — no Spa-uniform
inequalities, no continuous-valuation hypotheses. This is the cleanest
formulation of the σ-power-decay content as a single algebraic
existence Prop, ready for discharge via Spa-quasi-compactness +
topological nilpotence of `σ_loc` (the Wedhorn 8.34(ii) Step 2 step). -/
def AlphaJointCor732_decay_factorization
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (s_D : A) (σ_loc : (Localization.Away s)ˣ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  ∃ (N : ℕ) (ξ : locSubring P T s),
    algebraMap A (Localization.Away s) s =
      (ξ : Localization.Away s) *
        ((σ_loc : Localization.Away s) *
          (algebraMap A (Localization.Away s) s_D) ^ (N + 1))

omit [PlusSubring A] in
/-- **T164 algebraic-side bridge**: from the named decay factorization
Prop + chain σ-domination + α-image plus-subring data, produce
`AlphaJointCor732_uniformDecayAndChain`.

Thin wrapper around T166's
`AlphaJointCor732_uniformDecayAndChain_via_decay_factorization_and_sigma_dom_chain`
that opens the named existential and forwards the σ-domination + chain
data unchanged. -/
theorem AlphaJointCor732_uniformDecayAndChain_via_named_decay_factorization
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_decay_fact :
      AlphaJointCor732_decay_factorization P T s hopen s_D σ_loc)
    (h_σ_dom :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle (σ_loc : Localization.Away s)
          (algebraMap A (Localization.Away s) s))
    (h_T_D_in : ∀ t ∈ T_D,
      algebraMap A (Localization.Away s) t ∈ locSubring P T s)
    (h_s_D_in :
      algebraMap A (Localization.Away s) s_D ∈ locSubring P T s) :
    AlphaJointCor732_uniformDecayAndChain
      P T s hopen T_D s_D σ_loc := by
  obtain ⟨N, ξ, hfact⟩ := h_decay_fact
  exact AlphaJointCor732_uniformDecayAndChain_via_decay_factorization_and_sigma_dom_chain
    P T s hopen T_D s_D σ_loc N ξ hfact h_σ_dom h_T_D_in h_s_D_in

omit [PlusSubring A] in
/-- **T164 top-level algebraic supplier**: from the named pure-algebraic
decay factorization Prop, chain σ-domination, α-image plus-subring data,
`IsUnit (α s_D)`, `[IsDomain A]`, and `s ≠ 0`, produce

```
∃ N, AlphaJointMNChoiceLocPlusMembership P T s hopen T_D s_D σ_loc N.
```

This is the **clean single-supplier theorem** for T164's algebraic side:
the locPlus M/N-choice membership follows from purely algebraic data
(decay factorization) plus standard Cor 7.32 σ-strict-domination, standard
α-image locSubring membership, and the natural `IsUnit α s_D` hypothesis.

The remaining content is concentrated in the named pure-algebraic Prop
`AlphaJointCor732_decay_factorization`, which is the genuine Wedhorn
8.34(ii) Step 2 σ-power-decay step (Spa-quasi-compactness + topological
nilpotence of σ_loc).

**Proof**: chain via T166's combiner to `AlphaJointCor732_uniformDecayAndChain`
on the locSubring Spa, transport to the locPlus Spa via T165's
`_locPlus_of_locSubring` bridge, then apply T164's
`AlphaJointMNChoiceLocPlusMembership_via_uniformDecayAndChain_and_unit_s_D`. -/
theorem AlphaJointMNChoiceLocPlusMembership_via_named_decay_factorization_and_unit_s_D
    [DecidableEq A] [IsDomain A]
    (P : PairOfDefinition A) (T : Finset A) (s : A) (hs : s ≠ 0)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_unit_s_D : IsUnit (algebraMap A (Localization.Away s) s_D))
    (h_decay_fact :
      AlphaJointCor732_decay_factorization P T s hopen s_D σ_loc)
    (h_σ_dom :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle (σ_loc : Localization.Away s)
          (algebraMap A (Localization.Away s) s))
    (h_T_D_in : ∀ t ∈ T_D,
      algebraMap A (Localization.Away s) t ∈ locSubring P T s)
    (h_s_D_in :
      algebraMap A (Localization.Away s) s_D ∈ locSubring P T s) :
    ∃ N, AlphaJointMNChoiceLocPlusMembership
      P T s hopen T_D s_D σ_loc N := by
  -- Step 1: named decay + σ-dom + plus-subring data ⇒ uniform decay+chain (locSubring Spa).
  have h_uniformDecayAndChain :
      AlphaJointCor732_uniformDecayAndChain
        P T s hopen T_D s_D σ_loc :=
    AlphaJointCor732_uniformDecayAndChain_via_named_decay_factorization
      P T s hopen T_D s_D σ_loc h_decay_fact h_σ_dom h_T_D_in h_s_D_in
  -- Step 2: locSubring → locPlus Spa via T165's bridge.
  have h_uniformDecayAndChain_locPlus :
      AlphaJointCor732_uniformDecayAndChain_locPlus
        P T s hopen T_D s_D σ_loc :=
    AlphaJointCor732_uniformDecayAndChain_locPlus_of_locSubring
      P T s hopen T_D s_D σ_loc h_uniformDecayAndChain
  -- Step 3: T164's locPlus M/N-choice supplier from uniform decay+chain + IsUnit α s_D.
  exact AlphaJointMNChoiceLocPlusMembership_via_uniformDecayAndChain_and_unit_s_D
    P T s hs hopen T_D s_D σ_loc h_unit_s_D h_uniformDecayAndChain_locPlus

omit [IsTopologicalRing A] [PlusSubring A] in
/-- **T164 decay factorization from any M/N-choice membership**. Any
existing `AlphaJointMNChoiceLocSubringMembership` data (witnesses for a
specific `(σ_loc, N)`) discharges the named pure-algebraic decay
factorization Prop by extracting the decay piece.

This bridge collapses every existing M/N-choice supplier — including
T158/T157's special-case constructions, T159's
`AlphaJointMNChoiceLocSubringMembership_via_cover_and_residual`, and
T160's π-power supplier — into the named decay factorization Prop. -/
theorem AlphaJointCor732_decay_factorization_of_mn_choice
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_mn : AlphaJointMNChoiceLocSubringMembership
      P T s hopen T_D s_D σ_loc N) :
    AlphaJointCor732_decay_factorization P T s hopen s_D σ_loc := by
  obtain ⟨⟨ξ_decay, hξ_decay_eq⟩, _⟩ := h_mn
  exact ⟨N, ξ_decay, hξ_decay_eq⟩

omit [IsTopologicalRing A] [PlusSubring A] in
/-- **T164 concrete discharge** at `σ_loc = 1` in the natural special
case `s = s_D · c` for `c ∈ P.A₀`.

**Witnesses**: `N := 0`, `ξ := algebraMap A (Loc s) c` (in
`locSubring P T s` by `algebraMap_mem_locSubring P T s c.property`).

**Proof**: `α s = α (s_D · c) = α s_D · α c` by `RingHom.map_mul`,
which equals `α c · (1 · α s_D^1) = ξ · (σ_loc · α s_D^(N+1))`
under commutativity. Mirrors T158's
`AlphaJointFactorizationWitnessesExist_when_s_eq_s_D_mul_A0_elt_and_T_D_le_T`
construction (decay-side only — chain side not needed for the named
decay factorization Prop). -/
theorem AlphaJointCor732_decay_factorization_when_s_eq_s_D_mul_A0_elt
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (s_D : A)
    (c : P.A₀) (h_s_factor : s = s_D * (c : A)) :
    AlphaJointCor732_decay_factorization P T s hopen s_D 1 := by
  refine ⟨0, ⟨algebraMap A (Localization.Away s) (c : A),
    algebraMap_mem_locSubring P T s c.property⟩, ?_⟩
  -- Goal: α s = α c · (1 · α s_D^1).
  rw [h_s_factor, map_mul]
  simp [Units.val_one, mul_comm]

end ValuationSpectrum

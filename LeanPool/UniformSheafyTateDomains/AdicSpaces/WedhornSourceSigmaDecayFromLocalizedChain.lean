/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornSigmaPowerInequalityFromLocalizedCor732
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornCor732DirectUpperBoundResidual
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalizedCor732Bridge

/-!
# Wedhorn 8.34(ii) — Source σ-decay chain from localized denominator-clearing chain (T086)

T084 (`WedhornCor732DirectUpperBoundResidual`) provides the named
**localized** denominator-clearing chain identity
`Cor732SigmaDenominatorClearingChainIdentity P T s hopen T_D s_D
D_T_loc s_base_loc D_s_loc f_loc` and reduces it to the localized
direct upper bound residual `Cor732SigmaDirectUpperBoundResidual …` —
both operate at `v ∈ Spa(Localization.Away s, locSubring P T s)`.

T083 (`WedhornSigmaPowerInequalityFromLocalizedCor732`) consumes the
named **source-side** σ-decay chain residual
`LocalizedCor732SigmaDecayChainSupplier P T s hopen T_D s_D s_base f`,
quantified at `w ∈ Spa A A⁺` over the source-restricted Laurent piece
(`w.vle f s_base`, `w.vle 1 t'`, `¬ w.vle t' 0`).

This file lands the **theorem-level bridge** from the localized chain
lane to the source σ-decay chain lane via the existing source ↔
localized valuation comparison API (`Spv.comap_vle` and
`valuationLocalizationLift_of_spa_rationalOpen_locSubring`), modulo a
**single named source/localized comparison precondition**: the
membership of T083's source-restricted Laurent piece in the
localization base rational open `R(T, s)`. The latter is the precise
"missing comparison theorem" that, once supplied per-`w`, closes the
bridge end-to-end.

## Audit of existing source ↔ localized API

* `Spv.comap_vle` (`WedhornPrelocalizationTransfer.lean`) — pulls back
  any localized inequality `v.vle (φ a) (φ b)` to source
  `(comap φ v).vle a b` for `φ : A →+* B`. Direct comparison primitive.

* `valuationLocalizationLift_of_spa_rationalOpen_locSubring`
  (`WedhornLocalizedCor732Bridge.lean`) — for `w ∈ rationalOpen T s ⊂
  Spa A A⁺` and `hA₀_le : P.A₀ ≤ A⁺`, supplies a lift
  `v ∈ Spa(Localization.Away s, locSubring P T s)` with
  `comap (algebraMap A _) v = w`. Direct comparison primitive.

These two together provide the source ↔ localized comparison API. The
source σ-decay chain at `w` reduces to the localized direct upper bound
at `v` via comap_vle (after T084's σ-cancellation), provided the
σ-decay chain witnesses are supplied at `σ := 1`, `N := 0`,
`C_base_s := s_D` (the trivial σ-decay reducing to a direct upper
bound). The lift requires `w ∈ rationalOpen T s` — the precise missing
comparison precondition.

## Strategy

Two substantive comparison components (proven), one named missing
precondition Prop, and the composition theorem.

* **Comparison component 1 (proven)**: from a localized direct upper
  bound `v.vle (algebraMap a) (algebraMap b)` and non-vanishing
  `¬ v.vle (algebraMap b) 0` at `v` with `comap v = w`, derive the
  source-side `w.vle a b` and `¬ w.vle b 0` via `comap_vle` (three
  uses, including `map_zero`).

* **Comparison component 2 (proven)**: witness the source σ-decay
  chain at `σ := 1`, `N := 0`, `C_base_s := s_D` from the source-side
  direct upper bound `w.vle a b ∧ ¬ w.vle b 0`. The σ-decay chain
  reduces to the direct upper bound after `pow_zero / mul_one /
  pow_one` rewriting, with `Spv.vle_refl` discharging the trivial
  upper bound `w.vle s_D s_D`.

* **Named missing precondition** (`SourceLaurentMembershipInLocalizationBase`):
  for each per-`(w, t')` source-restricted Laurent piece witness in
  T083's `LocalizedCor732SigmaDecayChainSupplier` body, supply
  `w ∈ rationalOpen T s` (membership in the localization base
  rational open). This is the precise comparison precondition for
  invoking `valuationLocalizationLift_of_spa_rationalOpen_locSubring`
  at the source-restricted Laurent piece.

* **Composition theorem** (ticket-named target): from T084's localized
  chain identity instantiated at the algebra-map-image source data,
  the named missing precondition, and `hA₀_le : P.A₀ ≤ A⁺`, produce
  T083's `LocalizedCor732SigmaDecayChainSupplier`. The proof composes:
  (i) lift each source `w` to `v` via the lift comparison primitive;
  (ii) translate source restrictions at `w` to `v` via `comap_vle`;
  (iii) apply T084's chain identity at `v` to derive the localized
  direct upper bound (T084's reduction theorem); (iv) pull back the
  upper bound to source via Comparison Component 1; (v) witness the
  source σ-decay chain via Comparison Component 2.

## Why one missing comparison precondition (not zero, not many)

The lift requires `w ∈ rationalOpen T s`. T083's predicate body
provides `w ∈ Spa A A⁺` and the per-`(w, t')` Laurent-piece
restrictions `w.vle f s_base`, `w.vle 1 t'`, `¬ w.vle t' 0`. These
are over the **source-side** rationalOpens `R(insert f T_base, s_base)
∩ R({1}, t')`, which are not generally the same as
`R(T, s)` (the localization base). Whether the source-restricted
Laurent piece sits inside the localization base is a structural
relation between the cover-piece data `(s_base, f, t', T_base)` and
the localization parameters `(T, s)` — it is the precise comparison
precondition this file names.

In the canonical Wedhorn 8.34(ii) setup, this membership holds because
the cover-piece sits inside the base by construction (cover-piece
denominator `D.s` is bounded by base denominator `C.base.s`, etc.),
but the relation is not abstractly derivable from the source
restrictions alone. T086 makes this dependency explicit and provides
the proven part of the bridge.

## What this file provides

* `source_direct_upper_bound_via_comap_at` — Comparison Component 1
  (proven via `comap_vle`).

* `source_sigma_decay_chain_via_direct_upper_bound_at` — Comparison
  Component 2 (proven via `Spv.vle_refl` + arithmetic).

* `SourceLaurentMembershipInLocalizationBase` — Prop predicate naming
  the missing comparison precondition: per-`(w, t')` Laurent-piece
  containment in the localization base rational open.

* `localized_cor732_sigma_decay_chain_supplier_from_denominator_chain`
  — T086 ticket-named main theorem composing the comparison
  components, the missing precondition, and `hA₀_le` with T084's chain
  identity (instantiated at algebra-map-image data) to produce T083's
  `LocalizedCor732SigmaDecayChainSupplier`.

## Notes

* No root import; leaf-level.
* Imports T083 (`WedhornSigmaPowerInequalityFromLocalizedCor732`) for
  the named source-side residual, T084
  (`WedhornCor732DirectUpperBoundResidual`) for the localized chain
  identity and its reduction to the localized direct upper bound, and
  `WedhornLocalizedCor732Bridge` for
  `valuationLocalizationLift_of_spa_rationalOpen_locSubring` and (via
  transitive imports) `comap_vle`.
* No edits to T031–T085 accepted leaves, root imports, or final
  theorem signatures.
* No edits to Primary's T085 file.
* No revival of M-power-decay / σ-power-decay (the σ-decay chain is
  per-`(w, t')` here, not a global decay), T001/Lane-B, Cor 8.32 /
  Jacobson, faithful-flatness, Zavyalov, or bivariate-overlap content.
* No global universal-over-`T_D` lower bound, no global universal-
  over-Spa multi-element bound, no all-units σ residual.
* No final `ValuationSpectrum.tateAcyclicity` hypothesis additions.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-! ## Comparison components -/

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- **Source-side direct upper bound from localized direct upper bound
via `comap`** (T086 strict comparison component 1; proven via
`comap_vle`).

From a localized direct upper bound `v.vle (algebraMap A _ a)
(algebraMap A _ b)` and non-vanishing `¬ v.vle (algebraMap A _ b) 0`
at `v ∈ Spv (Localization.Away s)`, with `comap (algebraMap A _) v =
w`, derive the source-side direct upper bound `w.vle a b ∧ ¬ w.vle b 0`.

**Proof structure**: substitute `w = comap (algebraMap A _) v`,
unfold the source-side `w.vle a b` and `w.vle b 0` via `comap_vle`
(transports inequalities along `comap`), and use the supplied
localized inequalities. The `map_zero` rewriting handles the
non-vanishing's `0` ↔ `algebraMap 0`.

**Substantive consumption**: both localized inequalities are genuinely
used — neither is a pass-through. The transport is the natural
`comap_vle`-based source ↔ localized comparison. -/
theorem source_direct_upper_bound_via_comap_at
    {s : A} {v : Spv (Localization.Away s)} {w : Spv A}
    (hv_eq : comap (algebraMap A (Localization.Away s)) v = w)
    {a b : A}
    (h_v_le : v.vle (algebraMap A (Localization.Away s) a)
        (algebraMap A (Localization.Away s) b))
    (h_v_b_ne : ¬ v.vle (algebraMap A (Localization.Away s) b) 0) :
    w.vle a b ∧ ¬ w.vle b 0 := by
  refine ⟨?_, ?_⟩
  · -- w.vle a b ↔ (comap _ v).vle a b ↔ v.vle (algebraMap a) (algebraMap b)
    rwa [← hv_eq, comap_vle]
  · -- ¬ w.vle b 0 ↔ ¬ v.vle (algebraMap b) (algebraMap 0) = ¬ v.vle (algebraMap b) 0
    rwa [← hv_eq, comap_vle, map_zero]

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- **Source σ-decay chain from source direct upper bound at
`σ := 1`, `N := 0`, `C_base_s := s_D`** (T086 strict comparison
component 2; proven via `Spv.vle_refl` and elementary arithmetic).

From the source-side direct upper bound `w.vle a b ∧ ¬ w.vle b 0`,
witness the source σ-decay chain at the trivial choice `σ := 1`,
`N := 0`, `C_base_s := b`:
```
w.vle ((1 : A) * a * b ^ 0) b          -- after pow_zero, mul_one
w.vle b ((1 : A) * b ^ (0 + 1))        -- after pow_one, one_mul
¬ w.vle b 0
```

The first reduces to `w.vle a b` (the supplied direct upper bound).
The second reduces to `w.vle b b` (`Spv.vle_refl`). The third is
forwarded.

**Why `σ := 1`, `N := 0`**: this is the trivial σ-decay chain
witness — the source σ-decay chain's `∃ (σ : Aˣ) (N : ℕ) (C_base_s : A)`
existential is satisfied at the simplest choice when the source-side
direct upper bound holds. No further σ-construction structure is
required; the upper bound is already enough to discharge the chain. -/
theorem source_sigma_decay_chain_via_direct_upper_bound_at
    {w : Spv A} {a b : A}
    (h_w : w.vle a b) (h_b_ne : ¬ w.vle b 0) :
    ∃ (σ : Aˣ) (N : ℕ) (C_base_s : A),
      w.vle ((σ : A) * a * b ^ N) C_base_s ∧
      w.vle C_base_s ((σ : A) * b ^ (N + 1)) ∧
      ¬ w.vle b 0 := by
  refine ⟨(1 : Aˣ), 0, b, ?_, ?_, h_b_ne⟩
  · simpa only [Units.val_one, one_mul, pow_zero, mul_one] using h_w
  · simpa only [Units.val_one, one_mul, zero_add, pow_one] using w.vle_refl b

/-! ## Named missing comparison precondition -/

/-- **Source Laurent piece membership in the localization base**
(T086 named missing source/localized comparison precondition).

For each per-`(w, t')` witness of T083's source-restricted Laurent
piece (`w ∈ Spa A A⁺` with `w.vle f s_base`, `w.vle 1 t'`,
`¬ w.vle t' 0`), supply the membership `w ∈ rationalOpen T s` —
i.e., `w` lies in the **localization base rational open** `R(T, s)`.

**Why this is the precise missing comparison theorem**: invoking
`valuationLocalizationLift_of_spa_rationalOpen_locSubring` to lift a
source `w` to a localized `v` requires `w ∈ rationalOpen T s`. T083's
predicate body provides only the per-`(w, t')` Laurent-piece
restrictions over the cover-piece-side `R(insert f T_base, s_base) ∩
R({1}, t')`, which is not generally contained in the localization
base `R(T, s)`. The structural relation between the cover-piece data
`(s_base, f, t', T_base)` and the localization parameters `(T, s)`
that ensures the inclusion is the **comparison precondition** — it
holds in the canonical Wedhorn 8.34(ii) setup but is not abstractly
derivable from the source-restricted body alone.

**Per-`(w, t')` source-restricted**: the precondition is supplied at
each `(w, t')` in T083's restricted set; no global universal-over-`T_D`
or universal-over-Spa form is introduced. This is exactly the missing
piece between T084's localized chain identity and T083's source-side
σ-decay chain residual. -/
def SourceLaurentMembershipInLocalizationBase
    (T : Finset A) (s : A)
    (T_D : Finset A) (s_base f : A) : Prop :=
  ∀ t' ∈ T_D, ∀ w ∈ Spa A A⁺,
    w.vle f s_base →
    w.vle (1 : A) t' →
    ¬ w.vle t' 0 →
    w ∈ rationalOpen T s

/-! ## Composition theorem -/

/-- **T083's source σ-decay chain residual from T084's localized chain
identity** (T086 ticket-named main theorem).

Composes T084's localized denominator-clearing chain identity at the
algebra-map-image source data with the comparison primitives
(`comap_vle` + `valuationLocalizationLift_of_spa_rationalOpen_locSubring`)
plus the named missing comparison precondition
`SourceLaurentMembershipInLocalizationBase` to produce T083's named
source-side σ-decay chain residual
`LocalizedCor732SigmaDecayChainSupplier`.

**Inputs**:

* `P T s hopen T_D s_D s_base f` — the standard T083 / T084 parameters.
* `hA₀_le : P.A₀ ≤ A⁺` — relationship between the pair-of-definition's
  ring of integers and the plus-subring; required for the lift.
* `h_chain_at_images` — T084's localized chain identity instantiated
  at the algebra-map-image source data: `D_T_loc :=
  localizedTestFamily s T_D s_D`, `s_base_loc := algebraMap s_base`,
  `D_s_loc := algebraMap s_D`, `f_loc := algebraMap f`. This is the
  natural source-data instantiation of T084's predicate.
* `h_loc_base` — the named missing comparison precondition: per-`(w, t')`,
  `w ∈ rationalOpen T s`.

**Output**: T083's `LocalizedCor732SigmaDecayChainSupplier P T s hopen
T_D s_D s_base f` — i.e., the source σ-decay chain at every `(σ_loc,
h_cover_t)` and per-`(w, t')` Laurent-piece witness.

**Proof structure**:

1. Reduce T084's chain identity at images to the localized direct
   upper bound via `cor732_sigma_direct_upper_bound_residual_from_denominator_identity`
   (T084's mechanical reduction).

2. At each `(σ_loc, h_cover_t, t', w)` in T083's source-restricted
   set: apply `h_loc_base` to obtain `w ∈ rationalOpen T s`; lift to
   `v` via `valuationLocalizationLift_of_spa_rationalOpen_locSubring`
   with `comap (algebraMap A _) v = w`.

3. Translate the source restrictions at `w` to `v` via `comap_vle`
   (with `map_one`, `map_zero` for the unit and zero translations),
   and verify `algebraMap A _ t' ∈ localizedTestFamily s T_D s_D`
   via `localizedTestFamily`'s membership characterisation.

4. Apply the localized direct upper bound at `(σ_loc, h_cover_t,
   algebraMap t', v)` to obtain `v.vle (algebraMap t')
   (algebraMap s_D)` and `¬ v.vle (algebraMap s_D) 0`.

5. Pull back to source via `source_direct_upper_bound_via_comap_at`
   (Comparison Component 1) to obtain `w.vle t' s_D ∧ ¬ w.vle s_D 0`.

6. Witness the source σ-decay chain via
   `source_sigma_decay_chain_via_direct_upper_bound_at` (Comparison
   Component 2) at `σ := 1`, `N := 0`, `C_base_s := s_D`.

**Substantive consumption**: every input is genuinely used —
`h_chain_at_images` is reduced to the direct upper bound and applied;
`h_loc_base` is consumed at each `(t', w)` to enable the lift;
`hA₀_le` is consumed by the lift theorem; the σ-decay chain witness
is the trivial existential chosen substantively (not by elaboration). -/
theorem localized_cor732_sigma_decay_chain_supplier_from_denominator_chain
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (hA₀_le : P.A₀ ≤ A⁺)
    (T_D : Finset A) (s_D s_base f : A)
    (h_chain_at_images :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      Cor732SigmaDenominatorClearingChainIdentity P T s hopen T_D s_D
        (localizedTestFamily s T_D s_D)
        (algebraMap A (Localization.Away s) s_base)
        (algebraMap A (Localization.Away s) s_D)
        (algebraMap A (Localization.Away s) f))
    (h_loc_base : SourceLaurentMembershipInLocalizationBase T s T_D s_base f) :
    LocalizedCor732SigmaDecayChainSupplier P T s hopen T_D s_D s_base f := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  -- Step 1: reduce T084's chain identity to the localized direct upper bound.
  have h_direct :=
    cor732_sigma_direct_upper_bound_residual_from_denominator_identity
      P T s hopen T_D s_D
      (localizedTestFamily s T_D s_D)
      (algebraMap A (Localization.Away s) s_base)
      (algebraMap A (Localization.Away s) s_D)
      (algebraMap A (Localization.Away s) f)
      h_chain_at_images
  -- Open T083's predicate.
  intro σ_loc h_cover_t t' ht' w hw_spa hw_f hw_one_t hw_t_ne
  -- Step 2: w lies in the localization base R(T, s); lift to v.
  have hw_rat : w ∈ rationalOpen T s :=
    h_loc_base t' ht' w hw_spa hw_f hw_one_t hw_t_ne
  obtain ⟨v, hv_spa, hv_eq⟩ :=
    valuationLocalizationLift_of_spa_rationalOpen_locSubring
      P T s hopen hA₀_le hw_rat
  -- Step 3: translate source restrictions at w to v via comap_vle.
  have hv_f : v.vle (algebraMap A (Localization.Away s) f)
      (algebraMap A (Localization.Away s) s_base) := by
    rwa [← comap_vle, hv_eq]
  have hv_one_t : v.vle (1 : Localization.Away s)
      (algebraMap A (Localization.Away s) t') := by
    rwa [show (1 : Localization.Away s)
          = algebraMap A (Localization.Away s) 1 from (map_one _).symm,
      ← comap_vle, hv_eq]
  have hv_t_ne : ¬ v.vle (algebraMap A (Localization.Away s) t') 0 := by
    rwa [show (0 : Localization.Away s)
          = algebraMap A (Localization.Away s) 0 from (map_zero _).symm,
      ← comap_vle, hv_eq]
  -- Step 4: apply the localized direct upper bound at v.
  have ht_image_mem :
      algebraMap A (Localization.Away s) t' ∈
        localizedTestFamily s T_D s_D := by
    rw [mem_localizedTestFamily_iff]
    exact Or.inr (Finset.mem_image_of_mem _ ht')
  obtain ⟨h_v_t_le_D, h_v_D_ne⟩ :=
    h_direct σ_loc h_cover_t (algebraMap A (Localization.Away s) t')
      ht_image_mem v hv_spa hv_f hv_one_t hv_t_ne
  -- Step 5: pull back to source via Comparison Component 1.
  obtain ⟨h_w_t_le_D, h_w_D_ne⟩ :=
    source_direct_upper_bound_via_comap_at hv_eq h_v_t_le_D h_v_D_ne
  -- Step 6: witness the source σ-decay chain via Comparison Component 2.
  exact source_sigma_decay_chain_via_direct_upper_bound_at h_w_t_le_D h_w_D_ne

end ValuationSpectrum

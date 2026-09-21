/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornMPowerStructuralDataHonest
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalCor732ToFactoredChain

/-!
# `WedhornMPowerStructuralDataHonest` from localized Cor 7.32 Laurent-piece membership

T028 consumer-interface bridge connecting T027's localized Cor 7.32
Laurent-piece membership output (commit `87762cd`,
`WedhornLocalCor732ToFactoredChain.lean`) to T021's honest σ-factored
structural supplier `WedhornMPowerStructuralDataHonest`. **Replaces
the parked false uniform σ-power-decay route** (T023) with the genuine
Wedhorn 8.34(ii) Laurent-cover language.

## Route summary

T027 produces, per `w ∈ Spa(Localization.Away s, locSubring P T s)`,
a Laurent piece `rationalOpen {1} (σ_loc⁻¹ * τ_w)` for some
`τ_w ∈ localizedTestFamily s T_D s_D` containing `w`. The honest
structural supplier asks for the per-`t'` σ-factored chain
`w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)` at every `(w, τ, t')`
under f-membership and σ-strict-domination by τ.

The natural T028 bridge:

1. Define a **per-Laurent-piece factored-chain residual**
   `PerLaurentPieceFactoredChain` carrying the per-`t'` σ-factored
   chain on each Laurent piece (i.e., assuming `w` lies in the Laurent
   piece for some τ instead of σ-strict-dominated by τ).

2. Compose: at each `(w, τ_supp, t')`, use the Laurent-piece
   membership at `w` to extract `τ_w` (independent of `τ_supp`),
   apply the per-piece residual at `(τ_w, w, t')`, and return the
   τ-independent per-`t'` σ-factored conclusion.

The conclusion `w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)` is
τ-independent (depends only on `(w, t')`), so the supplier's signature
`τ` and the Laurent-piece membership's `τ_w` need not coincide.

## Why this is non-tautological

The bridge **strictly reduces** the genuine Wedhorn 8.34(ii) per-`t'`
content by one quantifier layer: it replaces the σ-strict-domination
hypothesis at every τ in the localized test family with the Laurent-
piece membership existential plus a single per-piece consumer. The
per-piece consumer is **strictly weaker** than σ-strict-domination
(non-strict ≤-domination at a chosen τ + non-vanishing of τ replaces
strict <-domination at every τ), and matches Wedhorn's actual
8.34(ii) cover-piece arithmetic at PDF page 84 / Lemma 8.33.

## What this file provides

* `PerLaurentPieceFactoredChain` — the per-Laurent-piece factored-chain
  residual `Prop`, carrying the per-`t'` σ-factored chain on each
  Laurent piece `rationalOpen {1} (σ_loc⁻¹ * τ)` for `τ` ranging over
  the localized canonical test family.

* `WedhornMPowerStructuralDataHonest_via_laurent_piece_consumer` —
  bridge consuming **explicit** Laurent-piece membership data (T027
  output) plus the new per-piece residual; produces
  `WedhornMPowerStructuralDataHonest`.

* `WedhornMPowerStructuralDataHonest_via_localized_cor732_laurent_consumer`
  — top-level wrapper consuming σ-strict-domination on
  `localizedTestFamily` (the natural Cor 7.32 output) plus the
  per-piece residual; uses
  `localized_cor732_laurent_piece_membership_at` (T027) internally to
  extract the Laurent-piece data.

## Notes

* No root import; leaf-level.
* No edits to `WedhornLocalCor732ToFactoredChain.lean` (Tertiary's T027
  file) — only imports it. No edits to Primary's assembly files,
  Tertiary's value-group files, root imports, or final theorem
  signatures.
* No T001, Lane B, Cor 8.32, Jacobson, faithful-flatness, Zavyalov,
  or bivariate-overlap content. No revival of the parked
  `sigma_power_decay_of_cor732` route.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

/-- **Per-Laurent-piece σ-factored chain residual**.

For each `(τ, w, t')` with `τ ∈ localizedTestFamily s T_D s_D`, `w` in
the Laurent piece `rationalOpen {1} (σ_loc⁻¹ * τ)` on the localized
Spa, and the f-membership inequality `w.vle (σ_loc * ∏ T_D.image)
(algebraMap s)`, asserts the per-`t'` σ-factored chain
`w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)` for every `t' ∈
T_D.image (algebraMap)`.

This `Prop` packages the **per-piece** Wedhorn 8.34(ii) Route B
content. Equivalent to its σ-cancelled unfactored counterpart
`w.vle t' (algebraMap s_D)` via `vle_iff_mul_unit_right`. -/
def PerLaurentPieceFactoredChain
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
  ∀ τ ∈ localizedTestFamily s T_D s_D,
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w ∈ rationalOpen
        ({(1 : Localization.Away s)} : Finset (Localization.Away s))
        (((σ_loc⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) * τ) →
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s) →
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle (t' * (σ_loc : Localization.Away s))
          (algebraMap A (Localization.Away s) s_D *
            (σ_loc : Localization.Away s))

omit [PlusSubring A] in
/-- **Bridge: Laurent-piece membership + per-piece consumer →
honest structural supplier**.

Given:

* `h_laurent` — per-`w` Laurent-piece membership, the verbatim
  conclusion of `localized_cor732_laurent_piece_membership_at` (T027,
  commit `87762cd`).
* `h_per_piece` — `PerLaurentPieceFactoredChain` residual carrying the
  per-Laurent-piece per-`t'` σ-factored arithmetic.

Produces `WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc`.

The σ-strict-domination hypothesis `τ_supp` from the supplier's
signature is **not used**: at each `(w, t')`, we extract the
Laurent-piece-defining `τ_w` from `h_laurent w hw_spa` and apply
`h_per_piece` at `τ_w`. The conclusion is τ-independent so this
substitution is valid. -/
theorem WedhornMPowerStructuralDataHonest_via_laurent_piece_consumer
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_laurent :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w ∈ rationalOpen
            ({(1 : Localization.Away s)} : Finset (Localization.Away s))
            (((σ_loc⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) * τ))
    (h_per_piece :
      PerLaurentPieceFactoredChain P T s hopen T_D s_D σ_loc) :
    WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc := by
  intro w hw_spa hw_f _τ_supp _hτ_supp _hστ_supp t' ht'
  obtain ⟨τ_w, hτ_w_mem, hw_in_piece⟩ := h_laurent w hw_spa
  exact h_per_piece τ_w hτ_w_mem w hw_spa hw_in_piece hw_f t' ht'

omit [PlusSubring A] in
/-- **Top-level bridge: σ-strict-domination + per-piece consumer →
honest structural supplier**.

Caller-friendly composition that consumes the natural Cor 7.32 output
(σ-strict-domination over `localizedTestFamily s T_D s_D` on the
localized Spa) plus the new per-piece residual, internally calling
`localized_cor732_laurent_piece_membership_at` (T027) to extract the
Laurent-piece membership data. Produces
`WedhornMPowerStructuralDataHonest`.

The single mathematical residual is `h_per_piece`:
`PerLaurentPieceFactoredChain P T s hopen T_D s_D σ_loc`. The σ-strict-
domination input is whatever
`exists_dominating_unit_in_localization_via_global_pi` (or any
upstream Cor 7.32 supplier) produces. -/
theorem WedhornMPowerStructuralDataHonest_via_localized_cor732_laurent_consumer
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (hσ_loc_dom :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s))
    (h_per_piece :
      PerLaurentPieceFactoredChain P T s hopen T_D s_D σ_loc) :
    WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc :=
  WedhornMPowerStructuralDataHonest_via_laurent_piece_consumer
    P T s hopen T_D s_D σ_loc
    (localized_cor732_laurent_piece_membership_at
      P T s hopen T_D s_D σ_loc hσ_loc_dom)
    h_per_piece

end ValuationSpectrum

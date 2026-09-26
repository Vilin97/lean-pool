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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornC1PerCallSupplyHonestAssembly
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornMPowerStructuralDataHonestFromLaurentPiece

/-!
# T032 — Wedhorn 8.34(ii) C1 supplier assembly via the localized Laurent chain

Top-level consumer-facing interface theorem for the Wedhorn 8.34(ii)
supplier route: composes the existing localized Laurent honest-data
chain (T027–T030) with T020's honest per-call assembly to produce
`C1SupplierStrong_local C` from a per-call function whose only
non-mechanical residual is `PerLaurentPieceFactoredChain` — the
per-Laurent-piece factored-chain residual delegated to T031's full
`V_K` branch decomposition.

## Composition pipeline

```
PerLaurentPieceFactoredChain                              ← T031 (V_K branch)
  ↓ (via WedhornMPowerStructuralDataHonest_via_localized_cor732_laurent_consumer
     under σ-strict-domination from Cor 7.32)
WedhornMPowerStructuralDataHonest                         ← T028 output
  ↓ (one of the seven honest per-call components consumed by T020)
WedhornC1PerCallSupplyHonest                              ← T020 packaging
  ↓ (via C1SupplierStrong_local_via_honest_per_call_assembly)
C1SupplierStrong_local C                                  ← consumed by Wedhorn834SupplierAssembly
```

`WedhornMPowerStructuralDataHonest_via_localized_cor732_laurent_consumer`
(T028, commit landed) already wires the lower part of the chain.
`C1SupplierStrong_local_via_honest_per_call_assembly` (T020, commit
`635a2c5` chain) wires the upper part. This file connects them at the
per-call level by replacing the T020 input slot for
`WedhornMPowerStructuralDataHonest` with the T028 derivation from
`PerLaurentPieceFactoredChain` + the σ-strict-domination clause already
present in the per-call data.

## Single explicit residual

The per-call function consumed by this assembly carries
`PerLaurentPieceFactoredChain P C.base.T C.base.s hopen_base D.T D.s σ_loc`
as its only non-routine component. Discharging this for every per-call
`(D, v, t, σ_loc)` is the **T031 full Laurent `V_K` branch decomposition
deliverable**; T030 already discharges the lower-half (V_∅) special
case at the α_s_D branch.

## What this file provides

* `C1SupplierStrong_local_via_laurent_piece_per_call_assembly` — the
  top-level assembly. Inputs:
  - Standard Wedhorn supplier hypotheses (`P, hA₀_le, C, hopen_base`).
  - A per-call function delivering, for every
    `(D ∈ C.covers, v ∈ rationalOpen D.T D.s, t ∈ D.T,
     v.vle t D.s, ¬ v.vle D.s 0)`, the seven components:
    `σ_loc, f, h_alg, h_dom, h_per_piece, hv_in_plus, hvf_nz`,
    where `h_per_piece : PerLaurentPieceFactoredChain ...` is the
    T031 residual at this call.
  Output: `C1SupplierStrong_local C`. Sorry-free, axiom-clean.

* The per-call shape exposes `PerLaurentPieceFactoredChain` as a clean
  named slot so that, when T031 lands, callers replace one explicit
  hypothesis and the rest of the chain composes automatically.

## Notes

* No root import; leaf-level.
* No edits to T031's `WedhornFullLaurentVKBranchDecomposition.lean`
  (does not yet exist, but reserved for Tertiary).
* No edits to Tertiary's localized-Laurent files
  (`WedhornLocalCor732ToFactoredChain.lean`,
  `WedhornLaurentPieceFactoredChain.lean`,
  `WedhornFullLaurentLowerBranchBound.lean`),
  Secondary's `WedhornC1PerCallSupplyHonestAssembly.lean`, Primary's
  `Wedhorn834C1SupplierLocalInterface.lean`, root imports, or final
  theorem signatures.
* No T001, Lane B, Cor 8.32, Jacobson, faithful-flatness, Zavyalov,
  bivariate-overlap, or σ-power-decay content.
* Axioms (verified post-build): only `propext`, `Classical.choice`,
  `Quot.sound`. -/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **T032 top-level assembly: `C1SupplierStrong_local C` via the
localized Laurent honest-data chain**.

Composes T028's localized Laurent honest-data bridge
(`WedhornMPowerStructuralDataHonest_via_localized_cor732_laurent_consumer`)
with T020's honest per-call assembly
(`C1SupplierStrong_local_via_honest_per_call_assembly`) into a single
caller-facing theorem.

The per-call function delivers, at every
`(D ∈ C.covers, v ∈ rationalOpen D.T D.s, t ∈ D.T)`, the seven
components needed by the assembly chain. Six of these (σ_loc, f,
h_alg, h_dom, hv_in_plus, hvf_nz) are routine Cor 7.32 / denominator-
clearing / base-side data. The seventh, `h_per_piece`, is the
**T031 residual** `PerLaurentPieceFactoredChain` carrying the
per-Laurent-piece per-`t'` σ-factored chain over the localized
canonical test family.

Internally:
1. `WedhornMPowerStructuralDataHonest_via_localized_cor732_laurent_consumer`
   converts `(h_dom, h_per_piece)` to
   `WedhornMPowerStructuralDataHonest`.
2. `C1SupplierStrong_local_via_honest_per_call_assembly` packages
   the seven honest components (with `WedhornMPowerStructuralDataHonest`
   replacing the `h_per_piece` slot) into `C1SupplierStrong_local C`.

The σ-strict-domination clause `h_dom` is consumed by both T028's
bridge (to produce `WedhornMPowerStructuralDataHonest`) and T020's
assembly (as one of the seven per-call components). The same
`h_dom` term is reused; no duplication.

Sorry-free; everything composes from already-landed bridges. -/
theorem C1SupplierStrong_local_via_laurent_piece_per_call_assembly
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (h_per_call_components_with_laurent_piece :
      letI : TopologicalSpace (Localization.Away C.base.s) :=
        locTopology P C.base.T C.base.s hopen_base
      letI : PlusSubring (Localization.Away C.base.s) :=
        localizationLocSubringPlusSubring P C.base.T C.base.s
      letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
      ∃ (σ_loc : (Localization.Away C.base.s)ˣ) (f : A),
        algebraMap A (Localization.Away C.base.s) f =
          (σ_loc : Localization.Away C.base.s) *
            (∏ τ ∈ D.T.image (algebraMap A (Localization.Away C.base.s)), τ) ∧
        (∀ w ∈ Spa (Localization.Away C.base.s)
            (Localization.Away C.base.s)⁺,
          ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
            w.vle (σ_loc : Localization.Away C.base.s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away C.base.s)) ∧
        PerLaurentPieceFactoredChain P C.base.T C.base.s hopen_base
          D.T D.s σ_loc ∧
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
        ¬ v.vle f 0) :
    C1SupplierStrong_local C := by
  letI : TopologicalSpace (Localization.Away C.base.s) :=
    locTopology P C.base.T C.base.s hopen_base
  letI : PlusSubring (Localization.Away C.base.s) :=
    localizationLocSubringPlusSubring P C.base.T C.base.s
  letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
  refine C1SupplierStrong_local_via_honest_per_call_assembly P hA₀_le C
    hopen_base ?_
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨σ_loc, f, h_alg, h_dom, h_per_piece, hv_in_plus, hvf_nz⟩ :=
    h_per_call_components_with_laurent_piece D hD v hv t ht hvt hvD_s
  -- Convert per-Laurent-piece residual to honest structural supplier via T028.
  have h_honest :
      WedhornMPowerStructuralDataHonest P C.base.T C.base.s hopen_base
        D.T D.s σ_loc :=
    WedhornMPowerStructuralDataHonest_via_localized_cor732_laurent_consumer
      P C.base.T C.base.s hopen_base D.T D.s σ_loc h_dom h_per_piece
  exact ⟨σ_loc, f, h_alg, h_dom, h_honest, hv_in_plus, hvf_nz⟩

end ValuationSpectrum

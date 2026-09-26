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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornStrengthenedC1
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalCor732ToFactoredChain

/-!
# Wedhorn 8.34(ii) — Top-Level C1 Supplier Local Interface

The cleanest caller theorem for producing `C1SupplierStrong_local C`
(consumed by the `Wedhorn834SupplierAssembly` skeleton at commit
`20f27a4`). Composes the existing M-power-decay bridge
(`WedhornLocalCor732ToFactoredChain.rationalOpen_subset_base_via_M_power_decay`)
with a per-(D, v, t) supplier predicate that bundles the **two real
supplier residuals**:

* **Secondary's M-power-decay residual**
  (`WedhornLocalCor732ToFactoredChain.M_power_decay_target`).
* **Tertiary's value-group / MulArchimedean localization transfer
  residual**
  (`WedhornLocalizedArchimedeanTransfer.mulArchimedean_localization_comap_via_strictMono_hom`),
  consumed inside `exists_dominating_unit_in_localization_via_global_pi`
  to produce the σ-strict-domination clause carried by this interface
  predicate.

Together with the routine algebraic packaging (denominator clearing,
plus-piece membership, and σ-unit non-degeneracy), the predicate
captures *all* per-call data the Wedhorn 8.34(ii) ratio construction
must produce, leaving the two named residuals as the sole external
contributions.

## What this file provides

* `WedhornC1PerCallSupply` — `Prop` predicate bundling the per-(D, v)
  data produced by the Wedhorn 8.34(ii) ratio construction. Six
  components packaged in a single existential:
  1. `σ_loc` — Cor 7.32 dominating unit inside
     `Localization.Away C.base.s`.
  2. `f` — the cleared base candidate in `A`.
  3. `h_alg` — denominator-clearing identity
     `algebraMap f = σ_loc * ∏ T_D`.
  4. `h_dom` — σ-strict-domination on local Spa (Cor 7.32 conclusion;
     consumes Tertiary's MulArchimedean transfer residual).
  5. `h_M_power_decay` — Secondary's M-power-decay structural residual
     (verbatim shape from `WedhornLocalCor732ToFactoredChain`).
  6. `hv_in_plus`, `hvf_nz` — clauses 1 and 3 of the C1 conclusion.

* `C1SupplierStrong_local_via_named_residuals` — the caller theorem.
  Given the per-call supply for every `(D, v, t)`, produces
  `C1SupplierStrong_local C` by threading
  `rationalOpen_subset_base_via_M_power_decay` for clause 2 and the
  bundled clauses 1, 3 for the rest. Sorry-free, axiom-clean.

## Residual list (post-this-interface)

Once an upstream caller discharges `WedhornC1PerCallSupply` for every
`(D, v, t)` triple under the standard Tate setup,
`C1SupplierStrong_local C` is mechanical. The discharge of
`WedhornC1PerCallSupply` reduces to:

* **R₁ — Secondary's M-power-decay** (component 5 of the predicate):
  documented at `WedhornLocalCor732ToFactoredChain.lean:224`
  (`M_power_decay_target`). The genuinely new Wedhorn 8.34(ii) Route B
  content. Currently `WEDHORN-DOMINATING-UNIT-INEQUALITY-CORE` lane.

* **R₂ — Tertiary's MulArchimedean transfer** (consumed inside
  component 4): documented at `WedhornLocalizedArchimedeanTransfer.lean:100`
  (`mulArchimedean_localization_comap_transfer`). Strict-mono-hom-based
  reduction landed at
  `WedhornLocalizedArchimedeanTransfer.mulArchimedean_localization_comap_via_strictMono_hom`;
  the strictMono hom construction itself is the
  `WEDHORN-EXTEND-VALUATION-LOC-TOPOLOGY-CONTINUITY` lane.

* Routine algebraic packaging (components 1–3, 6):
  `exists_unit_away_denominator_cleared` (in
  `WedhornLocalizationDenominatorClearing.lean`) for components 1–3;
  `valuationLocalizationLift_via_continuity` (in
  `WedhornValuationLocalizationLift.lean`) plus σ-unit reasoning for
  component 6. These are all already-landed bridges that compose
  mechanically once R₁ and R₂ are discharged.

## Notes

* No root import; leaf-level file.
* No edits to `WedhornLocalCor732ToFactoredChain.lean` (Secondary's
  M-power-decay file) or `WedhornLocalizedArchimedeanTransfer.lean`
  (Tertiary's value-group file).
* No final-acyclicity signature changes, no T001 / Lane B / Cor832 /
  Jacobson / faithful-flatness / non-open-prime content.
* Axioms (verified post-build): only `propext`, `Classical.choice`,
  `Quot.sound`. -/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Per-call Wedhorn 8.34(ii) supply predicate** (the bundle of data
the ratio construction must produce at each `(D, v)`).

The localization-side typeclass instances (`TopologicalSpace`,
`PlusSubring`, `DecidableEq` on `Localization.Away C.base.s`) are
provided up-front via `letI` so the per-call existential body
type-checks uniformly against the M-power-decay residual signature
(verbatim shape from `WedhornLocalCor732ToFactoredChain`).

Components 4 (`h_dom` σ-strict-domination) and 5 (`h_M_power_decay`)
together carry the only non-mechanical content; the rest is routine
algebraic packaging that composes mechanically from already-landed
bridges. -/
def WedhornC1PerCallSupply
    [DecidableEq A]
    (P : PairOfDefinition A)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (D : RationalLocData A) (v : Spv A) : Prop :=
  letI : TopologicalSpace (Localization.Away C.base.s) :=
    locTopology P C.base.T C.base.s hopen_base
  letI : PlusSubring (Localization.Away C.base.s) :=
    localizationLocSubringPlusSubring P C.base.T C.base.s
  letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
  ∃ (σ_loc : (Localization.Away C.base.s)ˣ) (f : A),
    -- (1)–(3) Denominator-clearing identity.
    (algebraMap A (Localization.Away C.base.s) f =
      (σ_loc : Localization.Away C.base.s) *
        (∏ τ ∈ D.T.image (algebraMap A (Localization.Away C.base.s)), τ)) ∧
    -- (4) σ-strict-domination on local Spa (Cor 7.32 output;
    -- consumes Tertiary's MulArchimedean transfer R₂ via
    -- `exists_dominating_unit_in_localization_via_global_pi`).
    (∀ w ∈ Spa (Localization.Away C.base.s) (Localization.Away C.base.s)⁺,
        ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
          w.vle (σ_loc : Localization.Away C.base.s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away C.base.s)) ∧
    -- (5) Secondary's M-power-decay structural residual R₁.
    (∀ w ∈ Spa (Localization.Away C.base.s) (Localization.Away C.base.s)⁺,
        w.vle ((σ_loc : Localization.Away C.base.s) *
            (∏ τ ∈ D.T.image (algebraMap A (Localization.Away C.base.s)), τ))
          (algebraMap A (Localization.Away C.base.s) C.base.s) →
        ∀ τ ∈ localizedTestFamily C.base.s D.T D.s,
          w.vle (σ_loc : Localization.Away C.base.s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away C.base.s) →
          (∀ t' ∈ D.T.image (algebraMap A (Localization.Away C.base.s)),
              w.vle (algebraMap A (Localization.Away C.base.s) C.base.s)
                (algebraMap A (Localization.Away C.base.s) D.s *
                  (σ_loc : Localization.Away C.base.s) *
                  (∏ τ ∈ (D.T.image
                    (algebraMap A (Localization.Away C.base.s))).erase t', τ))) ∧
          (∀ t'' ∈ D.T.image (algebraMap A (Localization.Away C.base.s)),
              ¬ w.vle t'' 0) ∧
          ¬ w.vle (algebraMap A (Localization.Away C.base.s) D.s) 0) ∧
    -- (6a) Clause 1 of C1: v ∈ R(insert f C.base.T, C.base.s).
    v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
    -- (6b) Clause 3 of C1: ¬ v.vle f 0.
    ¬ v.vle f 0

/-- **Top-level C1 supplier interface theorem**.

Given:
* the standard Tate setup (`P, hA₀_le`),
* the localization-topology openness data on the cover base
  (`hopen_base`), and
* a per-call Wedhorn 8.34(ii) supply for every `(D, v, t)` (the
  `WedhornC1PerCallSupply` predicate, which bundles Secondary's
  M-power-decay residual R₁ and the σ-domination output that consumes
  Tertiary's MulArchimedean transfer R₂),

produces the abstract strong supplier `C1SupplierStrong_local C`
required by `Wedhorn834SupplierAssembly` at the next composition
layer.

The proof composes Secondary's
`rationalOpen_subset_base_via_M_power_decay` for clause 2 of the C1
conclusion and reads clauses 1 and 3 directly from the supply
predicate. -/
theorem C1SupplierStrong_local_via_named_residuals
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (h_per_call_supply :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        WedhornC1PerCallSupply P C hopen_base D v) :
    C1SupplierStrong_local C := by
  intro D hD v hv t ht hvt hvD_s
  have h_supply := h_per_call_supply D hD v hv t ht hvt hvD_s
  -- Unfold WedhornC1PerCallSupply to extract the six components.
  obtain ⟨σ_loc, f, h_alg, h_dom, h_M, hv_in_plus, hvf_nz⟩ := h_supply
  refine ⟨f, hv_in_plus, ?_, hvf_nz⟩
  exact rationalOpen_subset_base_via_M_power_decay
    P C.base.T C.base.s hopen_base hA₀_le C.base.T D.T D.s
    (Finset.Subset.refl _) f σ_loc h_alg h_dom h_M

end ValuationSpectrum

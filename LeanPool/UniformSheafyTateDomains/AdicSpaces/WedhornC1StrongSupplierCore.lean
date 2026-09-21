/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornStandardCoverRefinement

/-!
# Strong analogues of the C1 supplier core helpers

The strong supplier `C1SupplierStrong_local` (defined in
`WedhornStrengthenedC1.lean`) augments the C1 supplier conclusion with
the **third clause** `¬ v.vle f 0`. This file lands the strong
analogues of the two algebraically-clean C1 supplier helpers from
`WedhornStandardCoverRefinement.lean`:

1. `exists_single_f_refinement_at_t_strong_of_standardShape` —
   standard-shape branch with explicit witness non-degeneracy.
2. `exists_single_f_refinement_at_t_strong_of_singleton_unit_rescaled`
   — singleton + unit-rescaled-denominator branch with explicit test
   non-degeneracy.

Plus the underlying valuation arithmetic helper:

* `not_vle_zero_of_isUnit_mul` — the smallest non-degeneracy
  building block: a unit times a non-degenerate element is
  non-degenerate.

## Why these are core supplier pieces

These two strong analogues directly cover the two algebraically-clean
subcases of the strong supplier (`C1SupplierStrong_local C`):
* Standard-shape: when `D` is already presented as
  `R(insert f₀ C.base.T, C.base.s)`.
* Singleton + unit-rescaled: when `D.T = {t}` and there is a unit
  `σ : Aˣ` with `(σ : A) * D.s = C.base.s`.

The truly general non-standard case (`|D.T| ≥ 1` with `D.s` not unit-
rescalable to `C.base.s`) requires the full Wedhorn 8.34(ii) σ-
construction — recorded as the documented residual in the trailing
docblock with the precise missing target signature.

## Why the additional non-degeneracy hypotheses

In the strong supplier, the `¬ v.vle f 0` clause does NOT follow
automatically from `v ∈ rationalOpen D.T D.s` plus `v.vle t D.s` plus
`¬ v.vle D.s 0`: the test element `t` could lie in `supp(v)` (i.e.,
`v.vle t 0`), making `v(t) = 0` — and then `f := σ * t` would have
`v(f) = 0` regardless of `σ` being a unit. So:
* Standard-shape strong: requires `¬ v.vle f₀ 0` (witness non-degenerate).
* Singleton + unit-rescaled strong: requires `¬ v.vle t 0` (test element
  non-degenerate).

In typical Wedhorn applications (where the consumer threads
`t := D.s` after `insertDenom` normalization), these auxiliary
hypotheses become `¬ v.vle D.s 0` — which IS automatic from the input
hypothesis `_hvD_s` of the strong supplier signature. So in practice the
auxiliary hypotheses are discharged for free at the typical callsite.

## Notes

* No root import; leaf-level file.
* No edits to `WedhornStandardCoverRefinement.lean` or any other file.
* No Lane B / Cor 8.32 / Jacobson / T001 / faithful-flatness /
  final-acyclicity content. -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] in
/-- **Smallest non-degeneracy building block**: a unit times a
non-degenerate element is non-degenerate.

`v((σ : A) * a) = v(σ) · v(a)`, with `v(σ) > 0` (σ unit) and `v(a) > 0`
(by hypothesis), so `v((σ : A) * a) > 0`.

Proof: `ValuativeRel.zero_vlt_mul` applied to `0 <ᵥ σ` (from
`not_vle_zero_of_isUnit`) and `0 <ᵥ a` (from `¬ v.vle a 0`). -/
lemma not_vle_zero_of_isUnit_mul
    {v : Spv A} (σ : Aˣ) {a : A} (ha : ¬ v.vle a 0) :
    ¬ v.vle ((σ : A) * a) 0 := by
  letI : ValuativeRel A := v.toValuativeRel
  have hσ_pos : (0 : A) <ᵥ (σ : A) := not_vle_zero_of_isUnit σ.isUnit v
  have ha_pos : (0 : A) <ᵥ a := ha
  exact ValuativeRel.zero_vlt_mul hσ_pos ha_pos

/-- **Strong analogue of `exists_single_f_refinement_at_t_of_standardShape`**.

Same statement as the non-strong version, with the additional
**third conclusion clause** `¬ v.vle f 0`. The proof uses `f := f₀`
(same as non-strong); the strong clause discharges via the explicit
witness non-degeneracy hypothesis `hvf₀_nz`.

**Hypothesis discharge in the typical insertDenom callsite**: when the
consumer normalizes by `insertDenom` and chooses `t := D.s`, the
witness `f₀` for the standard-shape `D = R(insert f₀ C.base.T,
C.base.s)` satisfies `v(f₀) ≤ v(C.base.s)`. The non-degeneracy
`¬ v.vle f₀ 0` is supplied externally (often automatic when `f₀ = D.s`
and `D.s` is the cover-piece denominator). -/
theorem exists_single_f_refinement_at_t_strong_of_standardShape
    [DecidableEq A] (C : RationalCoveringData A) (D : RationalLocData A)
    (f₀ : A)
    (hD_shape : rationalOpen D.T D.s =
      rationalOpen (insert f₀ C.base.T) C.base.s)
    {v : Spv A} (hv : v ∈ rationalOpen D.T D.s)
    (hvf₀_nz : ¬ v.vle f₀ 0)
    (t : A) (_ht : t ∈ D.T) :
    ∃ f : A,
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s ∧
      ¬ v.vle f 0 :=
  ⟨f₀, hD_shape ▸ hv, hD_shape.ge, hvf₀_nz⟩

/-- **Strong analogue of `exists_single_f_refinement_at_t_of_singleton_unit_rescaled`**.

Same statement as the non-strong version, with the additional
**third conclusion clause** `¬ v.vle f 0`. The proof uses
`f := (σ : A) * t` (same as non-strong); the strong clause discharges
via the explicit test-element non-degeneracy hypothesis `hvt_nz` plus
`not_vle_zero_of_isUnit_mul` at the unit `σ`.

**Hypothesis discharge in the typical insertDenom callsite**: when the
consumer threads `t := D.s` after `insertDenom` normalization, `hvt_nz`
becomes `¬ v.vle D.s 0`, which IS automatic from the strong supplier's
input hypothesis `_hvD_s`. So the strong clause is free at the typical
callsite.

**Why the proof inlines the non-strong helper**: the existing
`exists_single_f_refinement_at_t_of_singleton_unit_rescaled` returns `f`
via an existential witness `⟨(σ : A) * t, ...⟩`, hiding the f-shape
behind `Exists.intro`. To derive the third strong clause from the
specific f-shape, we re-derive the f-construction directly. -/
theorem exists_single_f_refinement_at_t_strong_of_singleton_unit_rescaled
    [DecidableEq A] (C : RationalCoveringData A) (D : RationalLocData A)
    (hD_sub : rationalOpen D.T D.s ⊆ rationalOpen C.base.T C.base.s)
    (t : A) (hT : D.T = {t})
    (σ : Aˣ) (hσ : (σ : A) * D.s = C.base.s)
    {v : Spv A} (hv : v ∈ rationalOpen D.T D.s)
    (hvt_nz : ¬ v.vle t 0) :
    ∃ f : A,
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s ∧
      ¬ v.vle f 0 := by
  obtain ⟨f, h_in, h_sub⟩ :=
    exists_single_f_refinement_at_t_of_singleton_unit_rescaled
      C D hD_sub t hT σ hσ hv
  -- The non-strong proof uses `f := (σ : A) * t`. We re-prove the strong
  -- version with this explicit f-shape so the third clause is in scope.
  refine ⟨(σ : A) * t, ?_, ?_, not_vle_zero_of_isUnit_mul σ hvt_nz⟩
  · -- v ∈ rationalOpen (insert ((σ : A) * t) C.base.T) C.base.s — re-derive.
    have hvCbase := hD_sub hv
    obtain ⟨hv_spa, hvD, _hvDs⟩ := hv
    obtain ⟨_, hvT, hvCs⟩ := hvCbase
    have hvt : v.vle t D.s := hvD t (hT ▸ Finset.mem_singleton_self t)
    refine ⟨hv_spa, fun b hb ↦ ?_, hvCs⟩
    rcases Finset.mem_insert.mp hb with rfl | hb_base
    · have h1 : v.vle (t * (σ : A)) (D.s * (σ : A)) :=
        v.mul_vle_mul_left hvt (σ : A)
      have h2 : v.vle ((σ : A) * t) ((σ : A) * D.s) := by
        rw [mul_comm (σ : A) t, mul_comm (σ : A) D.s]; exact h1
      rw [hσ] at h2; exact h2
    · exact hvT b hb_base
  · -- subset: re-derive via cancellation at σ unit.
    intro w hw
    obtain ⟨hw_spa, hwIns, hwCs⟩ := hw
    have hw_σt : w.vle ((σ : A) * t) C.base.s :=
      hwIns ((σ : A) * t) (Finset.mem_insert_self _ _)
    have hwσ_ne : ¬ w.vle (σ : A) 0 := not_vle_zero_of_isUnit σ.isUnit w
    have hw_t : w.vle t D.s := by
      have h := hw_σt
      rw [← hσ, mul_comm (σ : A) t, mul_comm (σ : A) D.s] at h
      exact w.vle_mul_cancel hwσ_ne h
    have hwDs : ¬ w.vle D.s 0 := by
      intro hwDs0
      have h := w.mul_vle_mul_left hwDs0 (σ : A)
      rw [zero_mul, mul_comm D.s (σ : A), hσ] at h
      exact hwCs h
    refine ⟨hw_spa, fun t' ht' ↦ ?_, hwDs⟩
    rw [hT, Finset.mem_singleton] at ht'
    subst ht'
    exact hw_t

/-! ## Documented residual: the truly general non-standard strong case

The strong analogue of `exists_single_f_refinement_at_t_via_dominating_unit`
(`WedhornStandardCoverRefinement.lean:255` target signature) is the next
core supplier obligation. The exact missing target signature:

```
theorem exists_single_f_refinement_at_t_strong_via_dominating_unit
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCoveringData A) (D : RationalLocData A) (hD : D ∈ C.covers)
    (v : Spv A) (hv : v ∈ rationalOpen D.T D.s)
    (t : A) (ht : t ∈ D.T)
    (_hvt : v.vle t D.s) (_hvD_s : ¬ v.vle D.s 0)
    -- Localization-topology openness data:
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s) :
    ∃ f : A,
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s ∧
      ¬ v.vle f 0
```

### Canonical proof path

1. Lift `v` to `w ∈ Spa(A_loc, A_loc⁺_image)` via the
   `localizationAwayPlusSubring` (this lift is a major missing piece —
   no `valuationLocalizationLift` lemma exists in the codebase yet).
2. Apply `Cor732.exists_dominating_unit` inside `Spa(A_loc, A_loc⁺_image)`
   to extract `σ_loc : (A_loc)ˣ`.
3. Clear denominators: `σ_loc * (algebraMap C.base.s)^M = algebraMap σ_A`
   for some `σ_A : A` and `M : ℕ`.
4. Set `f := σ_A * D.s ^ N` (when `t = D.s` after normalization) for
   suitable `N`. This avoids using `t` directly in the f-construction,
   so the strong clause `¬ v.vle f 0 = v(σ_A) · v(D.s)^N ≠ 0` follows
   from `σ_A` being a unit times a unit power and `¬ v.vle D.s 0`.
5. Verify `v ∈ R(insert f C.base.T, C.base.s)` and
   `R(insert f C.base.T, C.base.s) ⊆ R(D.T, D.s)` via
   `rationalOpen_transfer_via_localization`
   (`Adic spaces/WedhornLocalizationTransferConsumer.lean`).

### Smallest single missing Lean lemma toward this

The single biggest missing piece is the **valuation-lift to
localization**:

```
theorem valuationLocalizationLift
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] (s : A) {v : Spv A} (hv : v ∈ Spa A A⁺)
    (hvs : ¬ v.vle s 0) :
    letI : PlusSubring (Localization.Away s) := localizationAwayPlusSubring s
    ∃ w : Spv (Localization.Away s),
      w ∈ Spa (Localization.Away s) (Localization.Away s)⁺ ∧
      comap (algebraMap A (Localization.Away s)) w = v
```

This is the v→w bridge. It requires constructing a Spv on
`Localization.Away s` from a Spv on `A` (with `v(s) ≠ 0`), and
verifying the Spa-membership on the localized side.

No further work in this file; the core supplier task continues with
the v→w lift as the next concrete sub-target. -/

end ValuationSpectrum

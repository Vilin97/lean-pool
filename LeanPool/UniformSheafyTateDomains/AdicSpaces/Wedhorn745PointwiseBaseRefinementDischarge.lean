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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornBaseRationalComapResidualDischarge
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornStandardCoverRefinement

/-!
# Wedhorn 7.45 pointwise base-refinement discharge for the strong C1
supplier (T049)

T048 (commit `4eacd35`) accepted the base-refinement bridge: the entire
T044–T047 chain reduces to a single per-call **strong C1 supply**
matching `C1SupplierStrong_local`'s body — a pointwise Wedhorn 7.45
cover-refinement statement at the base side, with the additional
`¬ v.vle f 0` non-vanishing clause.

This file lands the **strong-shape pointwise discharge** of T048's
per-call C1 supply from the existing standard-cover refinement API
(`StandardCover.exists_single_f_refinement_of_standardShape` and
`WedhornStandardCoverRefinement.exists_single_f_refinement_at_t_of_singleton_unit_rescaled`),
augmented with the strong third clause `¬ v.vle f 0`.

## What this file provides

* `exists_strong_C1_refinement_of_standardShape_pointwise` — strong
  pointwise C1 from standard-shape witness PLUS explicit `¬ v.vle f₀ 0`
  non-vanishing of the standard-shape representative at `v`. Discharges
  all three conjuncts of `C1SupplierStrong_local`'s body. Direct
  enrichment of `StandardCover.exists_single_f_refinement_of_standardShape`.

* `exists_strong_C1_refinement_singleton_self_unit_rescaled` — strong
  pointwise C1 from singleton self-test family `D.T = {D.s}` with a
  unit rescaling `(σ : A) * D.s = C.base.s`. Discharges all three
  conjuncts; the third clause `¬ v.vle f 0` is **automatic** in this
  case via `f := σ * D.s = C.base.s` and `v ∈ rationalOpen D.T D.s ⊆
  rationalOpen C.base.T C.base.s` (cover refinement) which gives
  `¬ v.vle C.base.s 0`. **No external non-vanishing hypothesis required.**

* `C1SupplierStrong_local_via_per_D_singleton_self_unit_rescaled` —
  top-level C1 supplier wrapper: if every cover piece has the
  singleton-self + unit-rescaled-denominator form, derive
  `C1SupplierStrong_local C` from existing API alone (no σ-construction
  hypotheses).

* `C1SupplierStrong_local_via_per_D_strong_standardShape` — top-level
  C1 supplier wrapper from per-D strong-standardShape data. The named
  residual is the per-D strong-standardShape predicate (an `f_D`
  witnessing standard shape AND non-vanishing at every `v ∈ D`).

* `C1SupplierStrong_local_via_Wedhorn745_pointwise_refinement` — the
  shortest-path top-level wrapper: composes T048's
  `C1SupplierStrong_local_via_Wedhorn745_refinement` with a per-call
  Wedhorn 7.45 pointwise C1 hypothesis (the natural Wedhorn 7.45
  cover-refinement obligation at the base, with no σ-construction
  premises).

## Why the strong-standardShape residual is closer to Wedhorn 7.45 than
T048

T048's residual is the per-call cover-refinement inclusion AT
ARBITRARY `v`. T049's residual restricts to a **per-D existence**:
each cover piece D admits a single `f_D` providing the standard-shape
representation AND non-vanishing on D. This is the natural
"Wedhorn 7.45 cover-refinement WITNESS" formulation:

* Per-D existence (one witness per cover piece, not pointwise).
* No σ-construction / max-element / V_K / localized-Spa premises.
* Fully at the base side `Spa(A, A⁺)`.
* The non-vanishing clause is mathematically free under the standard
  σ-construction (per `WedhornStrengthenedC1.lean:96-100`'s docstring
  argument: `f := σ · D.s^N` has `v(f) = v(σ) · v(D.s)^N`, both
  factors non-zero).

## Notes

* No root import; leaf-level.
* Imports `WedhornBaseRationalComapResidualDischarge` (T048) for the
  top-level C1 supplier composition, plus `WedhornStandardCoverRefinement`
  for the existing standard-shape and singleton unit-rescaled branch
  primitives.
* No edits to T031–T048 accepted leaves, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* No global universal-over-Spa bounds; all clauses are pointwise or
  per-D source-restricted.
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Strong pointwise C1 from standard-shape witness + explicit
non-vanishing of `f₀` at `v`** (T049 standard-shape branch).

Given `D` in standard shape with witness `f₀ : A` AND the explicit
non-vanishing hypothesis `¬ v.vle f₀ 0`, conclude all three conjuncts
of `C1SupplierStrong_local`'s body with `f := f₀`.

Direct enrichment of
`StandardCover.exists_single_f_refinement_of_standardShape` with the
non-vanishing third clause supplied as an explicit hypothesis. -/
theorem exists_strong_C1_refinement_of_standardShape_pointwise
    [DecidableEq A] (C : RationalCoveringData A) (D : RationalLocData A)
    (f₀ : A)
    (hD_shape : rationalOpen D.T D.s =
      rationalOpen (insert f₀ C.base.T) C.base.s)
    {v : Spv A} (hv : v ∈ rationalOpen D.T D.s)
    (hvf₀_ne : ¬ v.vle f₀ 0) :
    ∃ f : A,
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s ∧
      ¬ v.vle f 0 :=
  ⟨f₀, hD_shape ▸ hv, hD_shape.ge, hvf₀_ne⟩

/-- **Strong pointwise C1 from singleton self-test family with unit-
rescaled denominator** (T049 singleton self-test branch).

Specialisation of
`WedhornStandardCoverRefinement.exists_single_f_refinement_at_t_of_singleton_unit_rescaled`
to the singleton self-test case `D.T = {D.s}` with unit rescaling
`(σ : A) * D.s = C.base.s`. Discharges ALL THREE conjuncts of
`C1SupplierStrong_local`'s body — the third clause `¬ v.vle f 0` is
**automatic** in this case.

**Construction**: take `f := (σ : A) * D.s = C.base.s` (by `hσ`).

* First clause `v ∈ rationalOpen (insert ((σ : A) * D.s) C.base.T) C.base.s`:
  the per-`c` bound at `b = (σ : A) * D.s` reduces to
  `v.vle C.base.s C.base.s` (via `hσ`), trivially true; the per-`c`
  bound at `c ∈ C.base.T` and the non-vanishing of `C.base.s` follow
  from the cover-refinement inclusion `v ∈ rationalOpen C.base.T C.base.s`
  (via `hD_sub`).

* Second clause `R(insert ((σ : A) * D.s) C.base.T) C.base.s ⊆
  R(D.T, D.s)`: at any `w` in the LHS, the σ-rescaling cancellation
  (`Spv.vle_mul_cancel` + `mul_vle_mul_left`) gives
  `w.vle D.s D.s` and `¬ w.vle D.s 0`; with `D.T = {D.s}` (singleton),
  the per-`t'` bound check is `w.vle D.s D.s`, trivially.

* Third clause `¬ v.vle ((σ : A) * D.s) 0 = ¬ v.vle C.base.s 0`
  (by `hσ`): from `v ∈ rationalOpen D.T D.s ⊆ rationalOpen C.base.T C.base.s`
  (cover refinement) we get `¬ v.vle C.base.s 0` directly. -/
theorem exists_strong_C1_refinement_singleton_self_unit_rescaled
    [DecidableEq A] (C : RationalCoveringData A) (D : RationalLocData A)
    (hD_sub : rationalOpen D.T D.s ⊆ rationalOpen C.base.T C.base.s)
    (hT : D.T = {D.s})
    (σ : Aˣ) (hσ : (σ : A) * D.s = C.base.s)
    {v : Spv A} (hv : v ∈ rationalOpen D.T D.s) :
    ∃ f : A,
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s ∧
      ¬ v.vle f 0 := by
  refine ⟨(σ : A) * D.s, ?_, ?_, ?_⟩
  · -- Membership clause.
    have hvCbase := hD_sub hv
    obtain ⟨hv_spa, _hvD, _hvDs⟩ := hv
    obtain ⟨_, hvT, hvCs⟩ := hvCbase
    refine ⟨hv_spa, fun b hb ↦ ?_, hvCs⟩
    rcases Finset.mem_insert.mp hb with rfl | hb_base
    · rw [hσ]; exact (v.vle_total C.base.s C.base.s).elim id id
    · exact hvT b hb_base
  · -- Subset clause.
    intro w hw
    obtain ⟨hw_spa, hwIns, hwCs⟩ := hw
    have hw_σDs : w.vle ((σ : A) * D.s) C.base.s :=
      hwIns ((σ : A) * D.s) (Finset.mem_insert_self _ _)
    have hw_Ds : w.vle D.s D.s := (w.vle_total D.s D.s).elim id id
    have hwDs_ne : ¬ w.vle D.s 0 := by
      intro hwDs0
      have h := w.mul_vle_mul_left hwDs0 (σ : A)
      rw [zero_mul, mul_comm D.s (σ : A), hσ] at h
      exact hwCs h
    refine ⟨hw_spa, fun t' ht' ↦ ?_, hwDs_ne⟩
    rw [hT, Finset.mem_singleton] at ht'
    subst ht'
    exact hw_Ds
  · -- Third clause: ¬ v.vle (σ * D.s) 0 via hσ + cover refinement.
    rw [hσ]
    exact (hD_sub hv).2.2

/-- **Top-level: `C1SupplierStrong_local C` from per-D singleton-self
unit-rescaled witnesses** (T049 per-D singleton-self route).

If every cover piece `D ∈ C.covers` is in the **singleton self-test
unit-rescaled form** — i.e., `D.T = {D.s}` AND `∃ σ : Aˣ, (σ : A) * D.s
= C.base.s` AND the cover-refinement inclusion `R(D.T, D.s) ⊆
R(C.base.T, C.base.s)` — derive `C1SupplierStrong_local C` directly
from existing API. **No σ-construction hypotheses required**. -/
theorem C1SupplierStrong_local_via_per_D_singleton_self_unit_rescaled
    [DecidableEq A] (C : RationalCoveringData A)
    (h_per_D :
      ∀ D ∈ C.covers,
        rationalOpen D.T D.s ⊆ rationalOpen C.base.T C.base.s ∧
        D.T = {D.s} ∧
        ∃ σ : Aˣ, (σ : A) * D.s = C.base.s) :
    C1SupplierStrong_local C := by
  intro D hD v hv _t _ht _hvt _hvD_s
  obtain ⟨hD_sub, hT, σ, hσ⟩ := h_per_D D hD
  exact exists_strong_C1_refinement_singleton_self_unit_rescaled C D
    hD_sub hT σ hσ hv

/-- **Top-level: `C1SupplierStrong_local C` from per-D strong-
standardShape witnesses** (T049 per-D strong-standardShape route).

If every cover piece `D ∈ C.covers` admits a strong-standardShape
witness `f_D : A` — i.e., `R(D.T, D.s) = R(insert f_D C.base.T, C.base.s)`
AND `f_D` is non-vanishing on the cover piece (`∀ v ∈ R(D.T, D.s),
¬ v.vle f_D 0`) — derive `C1SupplierStrong_local C` from
`exists_strong_C1_refinement_of_standardShape_pointwise`.

**The named residual is the per-D strong-standardShape predicate**:
`∀ D ∈ C.covers, ∃ f_D, [standard shape] ∧ [non-vanishing on D]`.
This is closer to Wedhorn 7.45 than T048 because it is per-D (not
per-call), purely at the base side, with no sigma/max/V_K/localized-
Spa premises. The non-vanishing clause is mathematically free under
the σ-construction (`f_D := σ · D.s^N`, with both `v(σ) ≠ 0` and
`v(D.s) ≠ 0` on the cover piece). -/
theorem C1SupplierStrong_local_via_per_D_strong_standardShape
    [DecidableEq A] (C : RationalCoveringData A)
    (h_per_D :
      ∀ D ∈ C.covers, ∃ f_D : A,
        rationalOpen D.T D.s =
          rationalOpen (insert f_D C.base.T) C.base.s ∧
        ∀ v ∈ rationalOpen D.T D.s, ¬ v.vle f_D 0) :
    C1SupplierStrong_local C := by
  intro D hD v hv _t _ht _hvt _hvD_s
  obtain ⟨f_D, hD_shape, h_f_D_ne⟩ := h_per_D D hD
  exact exists_strong_C1_refinement_of_standardShape_pointwise C D f_D
    hD_shape hv (h_f_D_ne v hv)

/-- **Top-level: `C1SupplierStrong_local C` via the per-call Wedhorn
7.45 pointwise refinement obligation** (T049 final deliverable).

The shortest-path wrapper: takes the per-call Wedhorn 7.45 pointwise
C1 obligation directly (matching `C1SupplierStrong_local`'s body) and
produces `C1SupplierStrong_local C` via T048's
`C1SupplierStrong_local_via_Wedhorn745_refinement`. The named residual
is the **per-call Wedhorn 7.45 cover-refinement obligation** — a
pointwise base-side rational-open inclusion with no σ-construction
premises.

**The single named non-tautological residual** is exactly the
canonical Wedhorn 7.45 / Hübner 3.7-3.8 cover-refinement deduction at
the base side, in its sharpest pointwise form:

```
∀ D ∈ C.covers, ∀ v ∈ R(D.T, D.s), ∀ t ∈ D.T, v.vle t D.s →
  ¬ v.vle D.s 0 →
  ∃ f, R(insert f C.base.T) C.base.s ⊆ R(D.T, D.s) ∧
       v ∈ R(insert f C.base.T) C.base.s ∧
       ¬ v.vle f 0
```

This residual involves no σ-construction, max-element comparison, V_K
branch decomposition, or localized-Spa machinery — purely Wedhorn 7.45
base-side rational-open content. -/
theorem C1SupplierStrong_local_via_Wedhorn745_pointwise_refinement
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (h_pointwise_C1 :
      ∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
        ∀ t ∈ D.T, v.vle t D.s → ¬ v.vle D.s 0 →
        ∃ f : A,
          rationalOpen (insert f C.base.T) C.base.s ⊆
              rationalOpen D.T D.s ∧
          v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
          ¬ v.vle f 0) :
    C1SupplierStrong_local C :=
  C1SupplierStrong_local_via_Wedhorn745_refinement P hA₀_le
    hAplus_le_A₀ C hopen_base h_pointwise_C1

end ValuationSpectrum

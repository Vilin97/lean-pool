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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.StandardCover
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornMultiDominatingUnit

/-!
# Wedhorn Standard-Cover Refinement: single-`t` C1 helpers

Wedhorn §8.34(ii) refinement step (the C1 component documented in
`StandardCover.lean:306-429`): for `D ∈ C.covers` and a single point
`v ∈ rationalOpen D.T D.s`, produce `f : A` such that

* `v ∈ rationalOpen (insert f C.base.T) C.base.s`, and
* `rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s`.

This file lands the standard-shape branch and the **σ-equipped
unit-rescaled-denominator branch** of the single-`f` helper, plus a
companion **multi-`F` unit-rescaled algebraic identity** that establishes
the rational-open transfer law underlying the σ-equipped reduction.
The truly general non-standard branch — where `D.s` is **not** a unit
multiple of `C.base.s` — requires the full Cor 7.32 σ-domination
construction over a multi-element test family and is recorded as the
precise missing API; see the docblock at the end of this file.

## What this file provides

1. `exists_single_f_refinement_at_t_of_standardShape` — extends
   `StandardCover.exists_single_f_refinement_of_standardShape`
   (`StandardCover.lean:519`) with an explicit `t : A` and
   `ht : t ∈ D.T`. Proof: takes `f := f₀` from the standard-shape
   witness; the explicit `t` is a no-op marker for downstream callers.

2. `rationalOpen_image_union_base_eq_of_unit_rescaled` — algebraic
   identity: when `(σ : A) * D.s = C.base.s` for a unit `σ : Aˣ` and
   `D ⊆ C.base`, the rational open `R(σ • D.T ∪ C.base.T, C.base.s)`
   equals `R(D.T, D.s)` exactly. This is the *denominator-equalisation*
   identity underlying the σ-equipped C1 reduction.

3. `exists_single_f_refinement_at_t_of_singleton_unit_rescaled` — the
   **strongest single-`f` non-standard-shape C1 conclusion** provable
   from existing rational-open algebra: when `D.T = {t}` and there is a
   unit `σ : Aˣ` with `(σ : A) * D.s = C.base.s`, the single-`f`
   conclusion discharges with `f := (σ : A) * t`.

4. Precise blocker docblock (`exists_single_f_refinement_at_t_via_dominating_unit`)
   for the truly general non-standard branch, where `D.s` and `C.base.s`
   generate distinct principal ideals (no unit rescaling) AND/OR `D.T`
   has multiple elements (single `f` cannot encode multiple constraints).
   This is the Wedhorn / Cor 7.32 σ-domination content, with explicit
   pointers to the missing valuation-inequality API.

## Wedhorn ingredients used

* `StandardCover.exists_single_f_refinement_of_standardShape`
  (`StandardCover.lean:519`) — standard-shape branch dispatch.
* `Spv.mul_vle_mul_left`, `Spv.vle_mul_cancel`
  (`ValuationSpectrum.lean:63-65`) — valuation cancellation at units.
* `not_vle_zero_of_isUnit` (`ValuationSpectrum.lean:224`) — units are
  non-zero in valuation.
* `Cor732.exists_dominating_unit` (`Cor732.lean:206`) — referenced in the
  missing-API docblock for the truly general residual.

No Lane B / Cor 8.32 / Jacobson / faithful-flatness / T001 content.
No new final acyclicity hypotheses.
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

/-- **Wedhorn standard-cover refinement at an explicit `t ∈ D.T`,
standard-shape branch**.

Given `D` already in the form `R(insert f₀ C.base.T, C.base.s)` for some
`f₀ : A` (the witnessed standard-shape form), the single-`t` helper
discharges by `f := f₀`; the explicit `t ∈ D.T` is a downstream
bookkeeping witness not used in the standard-shape proof.

Mirror of `StandardCover.exists_single_f_refinement_of_standardShape`
(`StandardCover.lean:519`) with the additional explicit `t` parameter
documenting the manager-target shape. -/
theorem exists_single_f_refinement_at_t_of_standardShape
    [DecidableEq A] (C : RationalCoveringData A) (D : RationalLocData A)
    (f₀ : A)
    (hD_shape : rationalOpen D.T D.s =
      rationalOpen (insert f₀ C.base.T) C.base.s)
    {v : Spv A} (hv : v ∈ rationalOpen D.T D.s)
    (t : A) (_ht : t ∈ D.T) :
    ∃ f : A,
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s :=
  exists_single_f_refinement_of_standardShape C D f₀ hD_shape hv

/-- **Multi-`F` rational-open identity at unit-rescaled denominator
(Wedhorn 8.34(ii) algebraic core)**.

When the cover-piece `D` is contained in the base
(`R(D.T, D.s) ⊆ R(C.base.T, C.base.s)`) AND there is a unit `σ : Aˣ`
rescaling `D.s` to `C.base.s` (`(σ : A) * D.s = C.base.s`), the rational
open at the **σ-rescaled test family** unioned with `C.base.T` and
denominator `C.base.s` equals `R(D.T, D.s)` exactly:

```
R(σ • D.T ∪ C.base.T, C.base.s) = R(D.T, D.s)
```

where `σ • D.T = D.T.image ((σ : A) * ·)`.

**Proof core**: `Spv.mul_vle_mul_left` lifts the per-`t` inequality
`v.vle t D.s ↔ v.vle ((σ : A) * t) C.base.s` (using `(σ : A) * D.s =
C.base.s`); `Spv.vle_mul_cancel` at the unit `σ` provides the inverse
direction. The non-zero clause `¬ v.vle D.s 0 ↔ ¬ v.vle C.base.s 0` is
the `mul_vle_mul_left` of `D.s ↦ 0` against `σ`, again using `hσ`.

**Specialisations**:
* `σ := 1` (with `D.s = C.base.s`) gives the same-denominator multi-`F`
  identity `R(D.T ∪ C.base.T, C.base.s) = R(D.T, D.s)`.
* `D.T = {t}` (with arbitrary unit-rescaled `σ`) feeds into the
  single-`f` consumer
  `exists_single_f_refinement_at_t_of_singleton_unit_rescaled` below. -/
theorem rationalOpen_image_union_base_eq_of_unit_rescaled
    [DecidableEq A] (C : RationalCoveringData A) (D : RationalLocData A)
    (hD_sub : rationalOpen D.T D.s ⊆ rationalOpen C.base.T C.base.s)
    (σ : Aˣ) (hσ : (σ : A) * D.s = C.base.s) :
    rationalOpen (D.T.image ((σ : A) * ·) ∪ C.base.T) C.base.s =
      rationalOpen D.T D.s := by
  ext v
  constructor
  · rintro ⟨hv_spa, hvFT, hvCs⟩
    refine ⟨hv_spa, fun t ht => ?_, ?_⟩
    · have h : v.vle ((σ : A) * t) C.base.s :=
        hvFT _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t, ht, rfl⟩))
      rw [← hσ, mul_comm (σ : A) t, mul_comm (σ : A) D.s] at h
      exact v.vle_mul_cancel (not_vle_zero_of_isUnit σ.isUnit v) h
    · intro hvDs0
      have h := v.mul_vle_mul_left hvDs0 (σ : A)
      rw [zero_mul, mul_comm D.s (σ : A), hσ] at h
      exact hvCs h
  · intro hv
    have hvCbase := hD_sub hv
    obtain ⟨hv_spa, hvD, _hvDs⟩ := hv
    obtain ⟨_, hvT, hvCs⟩ := hvCbase
    refine ⟨hv_spa, fun b hb => ?_, hvCs⟩
    rcases Finset.mem_union.mp hb with hF | hT_mem
    · obtain ⟨t, htD, rfl⟩ := Finset.mem_image.mp hF
      have h2 : v.vle ((σ : A) * t) ((σ : A) * D.s) := by
        rw [mul_comm (σ : A) t, mul_comm (σ : A) D.s]
        exact v.mul_vle_mul_left (hvD t htD) (σ : A)
      rwa [hσ] at h2
    · exact hvT b hT_mem

/-- **Single-`t` C1 helper for singleton cover piece with unit-rescaled
denominator**.

The strongest **single-`f`** non-standard-shape C1 conclusion provable
from existing rational-open algebra without invoking the full Cor 7.32
σ-domination construction. Hypotheses:

* the cover piece `D` has a singleton test family `D.T = {t}`;
* there is a unit `σ : Aˣ` rescaling the denominator: `(σ : A) * D.s =
  C.base.s` (equivalently, `D.s` and `C.base.s` generate the same
  principal ideal);
* the cover piece is contained in the base
  (`hD_sub : R(D.T, D.s) ⊆ R(C.base.T, C.base.s)`; this is exactly
  `C.hsubset` for `D ∈ C.covers`).

Conclusion: the C1 single-`f` conclusion at any `v ∈ R(D.T, D.s)`
discharges with `f := (σ : A) * t`.

**Why singleton + unit-rescaled**: a single inserted `f` can encode at
most ONE valuation inequality in the new rational open. When `D.T` has
multiple elements, multiple constraints must hold simultaneously on the
plus-piece-at-`f`, which a single `f` cannot enforce algebraically
without the σ-domination over a multi-element test family. When `D.s`
is not a unit multiple of `C.base.s`, the denominator transfer
`v.vle t D.s ↔ v.vle (?) C.base.s` cannot be inverted via simple
multiplication by a unit. The full Wedhorn 8.34(ii) construction
addresses both via Cor 7.32; see the missing-API docblock below.

**Proof**: take `f := (σ : A) * t`. Both clauses reduce to the
multi-`F`-style cancellation `v.vle ((σ : A) * t) C.base.s ↔ v.vle t D.s`
(via `mul_vle_mul_left` and `vle_mul_cancel` at the unit `σ`), with
`(σ : A) * D.s` rewritten as `C.base.s` via `hσ`. Specialisation of
`rationalOpen_image_union_base_eq_of_unit_rescaled` to `D.T = {t}`. -/
theorem exists_single_f_refinement_at_t_of_singleton_unit_rescaled
    [DecidableEq A] (C : RationalCoveringData A) (D : RationalLocData A)
    (hD_sub : rationalOpen D.T D.s ⊆ rationalOpen C.base.T C.base.s)
    (t : A) (hT : D.T = {t})
    (σ : Aˣ) (hσ : (σ : A) * D.s = C.base.s)
    {v : Spv A} (hv : v ∈ rationalOpen D.T D.s) :
    ∃ f : A,
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s := by
  refine ⟨(σ : A) * t, ?_, ?_⟩
  · have hvCbase := hD_sub hv
    obtain ⟨hv_spa, hvD, _hvDs⟩ := hv
    obtain ⟨_, hvT, hvCs⟩ := hvCbase
    refine ⟨hv_spa, fun b hb => ?_, hvCs⟩
    rcases Finset.mem_insert.mp hb with rfl | hb_base
    · have h2 : v.vle ((σ : A) * t) ((σ : A) * D.s) := by
        rw [mul_comm (σ : A) t, mul_comm (σ : A) D.s]
        exact v.mul_vle_mul_left (hvD t (hT ▸ Finset.mem_singleton_self t)) (σ : A)
      rwa [hσ] at h2
    · exact hvT b hb_base
  · intro w hw
    obtain ⟨hw_spa, hwIns, hwCs⟩ := hw
    have hw_t : w.vle t D.s := by
      have h := hwIns ((σ : A) * t) (Finset.mem_insert_self _ _)
      rw [← hσ, mul_comm (σ : A) t, mul_comm (σ : A) D.s] at h
      exact w.vle_mul_cancel (not_vle_zero_of_isUnit σ.isUnit w) h
    have hwDs : ¬ w.vle D.s 0 := by
      intro hwDs0
      have h := w.mul_vle_mul_left hwDs0 (σ : A)
      rw [zero_mul, mul_comm D.s (σ : A), hσ] at h
      exact hwCs h
    refine ⟨hw_spa, fun t' ht' => ?_, hwDs⟩
    rw [hT, Finset.mem_singleton] at ht'
    subst ht'
    exact hw_t

/-! ## Wedhorn 8.34(ii) Laurent cover σ-inversion primitives

Wedhorn 8.34(ii) (PDF page 84) refines a rational cover into a Laurent
cover via `Cor732.exists_dominating_unit`: from σ-strict-domination over
a generating family `T = {f_0, ..., f_n}`, form the Laurent cover
generated by the σ-rescaled elements `{σ⁻¹ * f_1, …, σ⁻¹ * f_r}`. At
each `w ∈ Spa A A⁺`, some `t_w ∈ T` has `w(σ⁻¹ * t_w) ≥ 1` (i.e., `w`
is in the Laurent piece where this rescaled element is a unit).

The two lemmas below provide the **per-`w` algebraic core** of this
Laurent refinement: σ-strict-domination at `w` lifts to an
`σ⁻¹`-rescaled "valuation ≥ 1" inequality, whose pointwise existential
form is the Laurent piece membership.

These primitives are the **corrected route** (after T023's blocker on
the false uniform σ-power-decay shape and T024's blocker on the false
direct `vle_of_dominating_unit_multi` signature): instead of trying to
extract a per-`t'` rational-subset bound from σ-strict-dom + f-membership
alone (which is mathematically impossible per the T023/T024 counter-
examples), Wedhorn's actual proof builds a Laurent cover and uses cover-
level acyclicity (Lemma 8.33) to conclude. -/

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] in
/-- **σ-inversion at strict domination**. From σ-strict-domination
`w.vle (σ : A) τ` (which is the conclusion of `Cor732.exists_dominating_unit`
at a given `w`), deduce that the σ-rescaled element `σ⁻¹ * τ` has
valuation at least 1 at `w`: `w.vle 1 (((σ⁻¹ : Aˣ) : A) * τ)`.

This is the **algebraic core** of Wedhorn 8.34(ii)'s Laurent cover
refinement (PDF page 84): the Laurent cover generated by
`{σ⁻¹ * t | t ∈ T}` is exactly the cover where each `σ⁻¹ * t` becomes
a unit on its respective Laurent piece, and at every `w` some `σ⁻¹ * t_w`
indeed satisfies `w(σ⁻¹ * t_w) ≥ 1`.

Proof: multiply both sides of `w.vle (σ : A) τ` by `((σ⁻¹ : Aˣ) : A)`
on the LEFT via `ValuativeRel.mul_vle_mul_right`; the LHS becomes
`((σ⁻¹ : Aˣ) : A) * (σ : A) = 1` by `Units.inv_mul`. -/
theorem one_vle_inv_unit_mul_of_strict_dom_at
    (w : Spv A) {σ : Aˣ} {τ : A} (hστ : w.vle (σ : A) τ) :
    w.vle (1 : A) (((σ⁻¹ : Aˣ) : A) * τ) := by
  letI : ValuativeRel A := w.toValuativeRel
  have h_mul := ValuativeRel.mul_vle_mul_right hστ ((σ⁻¹ : Aˣ) : A)
  rwa [Units.inv_mul] at h_mul

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] in
/-- **Per-`w` Laurent-piece membership from Cor 7.32 σ-strict-domination
existential**.

Combines `one_vle_inv_unit_mul_of_strict_dom_at` with the existential
σ-strict-domination supplier from `Cor732.exists_dominating_unit`: at
each `w`, given `∃ τ ∈ T, w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A)`
(the per-`w` slice of the Cor 7.32 output), there exists `τ ∈ T` such
that:

* `w.vle 1 (((σ⁻¹ : Aˣ) : A) * τ)` — the σ-rescaled element has
  valuation at least 1 at `w` (so `w` is in the Laurent piece where
  `σ⁻¹ * τ` is a unit), and
* `¬ w.vle τ 0` — `τ` is non-vanishing at `w`.

The collection `{V_τ := {w | w.vle 1 (σ⁻¹ * τ)} | τ ∈ T}` thus forms a
**Laurent cover** of `Spa A A⁺`: at each `w`, some τ wins. This is the
foundational per-`w` step for Wedhorn 8.34(ii)'s Laurent cover
refinement (PDF page 84, second paragraph of the proof of Lemma 8.34
part (ii)). -/
theorem exists_one_vle_inv_unit_mul_at_of_cor732_strict_dom
    {w : Spv A} {σ : Aˣ} {T : Finset A}
    (hστ : ∃ τ ∈ T, w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A)) :
    ∃ τ ∈ T,
      w.vle (1 : A) (((σ⁻¹ : Aˣ) : A) * τ) ∧ ¬ w.vle τ 0 := by
  letI : ValuativeRel A := w.toValuativeRel
  obtain ⟨τ, hτ, hστ_left, hστ_right⟩ := hστ
  refine ⟨τ, hτ, one_vle_inv_unit_mul_of_strict_dom_at w hστ_left, ?_⟩
  intro h_τ_zero
  exact hστ_right (w.vle_trans h_τ_zero (ValuativeRel.zero_vle (σ : A)))

/-! ### Cor 7.32-based Laurent cover formation (T026)

Bridges T025's σ-inversion primitives to the existing `rationalOpen` /
Wedhorn rational-subset API: at every `w ∈ Spa A A⁺` with Cor 7.32
σ-strict-domination over a finite generating family `T`, the σ-rescaled
Laurent piece `rationalOpen ({(1 : A)} : Finset A) ((σ⁻¹ : Aˣ) * τ)`
contains `w` for some `τ ∈ T`. The collection
`{rationalOpen {1} (σ⁻¹ * τ) | τ ∈ T}` is a Laurent cover of
`Spa A A⁺` matching Wedhorn 8.34(ii)'s actual proof on PDF page 84:
the rescaled elements `σ⁻¹ * τ` become units on their respective
Laurent pieces, and the cover `{V_τ}` is the natural target of
Wedhorn's Lemma 8.33 (binary Laurent cover acyclicity) for cover-level
acyclicity.

These bridges intentionally avoid the **full `RationalCoveringData`
packaging**: each per-piece `RationalLocData A` would require a
non-trivial `hopen` verification (the localization at `σ⁻¹ * τ` having
the right openness data — which depends on whether `τ` is a unit,
generally NOT the case for arbitrary `τ ∈ T` in Wedhorn 8.34(ii)).
The lighter cover-membership theorem suffices for downstream
acyclicity arguments. -/

omit [IsTopologicalRing A] in
/-- **Cor 7.32 Laurent piece membership at `w`** (σ-rescaled form).

At any `w ∈ Spa A A⁺`, given Cor 7.32 σ-strict-domination over a
finite family `T` (the existential output of
`Cor732.exists_dominating_unit`), there exists `τ ∈ T` such that `w`
lies in the σ-rescaled Laurent piece
`rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ)`.

This Laurent piece corresponds to the "≥ 1" half-space
`{v ∈ Spa A A⁺ | v.vle 1 (σ⁻¹ * τ) ∧ ¬ v.vle (σ⁻¹ * τ) 0}` for the
single rescaled element `σ⁻¹ * τ`. It is exactly the Laurent piece
where `σ⁻¹ * τ` is a "valuation-≥-1" element (and hence becomes a
unit on the localized adic spectrum on this piece). Wedhorn 8.34(ii)
(PDF page 84) uses precisely this piece structure for the Laurent
cover refinement.

Proof: T025's `exists_one_vle_inv_unit_mul_at_of_cor732_strict_dom`
provides `τ ∈ T` with `w.vle 1 (σ⁻¹ * τ)` and `¬ w.vle τ 0`. We then
verify the `rationalOpen` membership: the singleton `{1}` membership
condition unfolds to the first inequality, and the non-vanishing of
`σ⁻¹ * τ` follows from `¬ w.vle τ 0` by left-multiplying by `σ` (which
maps the hypothetical `w.vle (σ⁻¹ * τ) 0` to `w.vle τ 0`). -/
theorem cor732_laurent_piece_membership_at
    {σ : Aˣ} {T : Finset A}
    (hσ_dom :
      ∀ v ∈ Spa A A⁺, ∃ τ ∈ T, v.vle (σ : A) τ ∧ ¬ v.vle τ (σ : A))
    {w : Spv A} (hw : w ∈ Spa A A⁺) :
    ∃ τ ∈ T,
      w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) := by
  letI : ValuativeRel A := w.toValuativeRel
  obtain ⟨τ, hτ, h_one_le, h_τ_ne⟩ :=
    exists_one_vle_inv_unit_mul_at_of_cor732_strict_dom (hσ_dom w hw)
  refine ⟨τ, hτ, hw, ?_, ?_⟩
  · intro t ht
    rw [Finset.mem_singleton] at ht
    exact ht ▸ h_one_le
  · intro h_inv_τ_zero
    apply h_τ_ne
    have h_mul := ValuativeRel.mul_vle_mul_right h_inv_τ_zero (σ : A)
    rwa [← mul_assoc, Units.mul_inv, one_mul, mul_zero] at h_mul

omit [IsTopologicalRing A] in
/-- **Spa is covered by the Cor 7.32 σ-rescaled Laurent pieces**
(set-level cover statement).

Existential per-`w` form of `cor732_laurent_piece_membership_at`,
phrased as a set-level cover-membership: every `w ∈ Spa A A⁺` lies in
some σ-rescaled Laurent piece `rationalOpen {1} (σ⁻¹ * τ)` for `τ ∈ T`.

The set-level statement
`Spa A A⁺ ⊆ ⋃ τ ∈ T, rationalOpen {1} (σ⁻¹ * τ)` follows from this by
`Set.subset_def` + `Set.mem_iUnion₂` unfolding (no extra content). -/
theorem cor732_laurent_cover_covers_spa
    {σ : Aˣ} {T : Finset A}
    (hσ_dom :
      ∀ v ∈ Spa A A⁺, ∃ τ ∈ T, v.vle (σ : A) τ ∧ ¬ v.vle τ (σ : A)) :
    ∀ w ∈ Spa A A⁺, ∃ τ ∈ T,
      w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) :=
  fun _ hw => cor732_laurent_piece_membership_at hσ_dom hw

/-! ## Precise missing API for the truly general non-standard branch

The `_of_singleton_unit_rescaled` helper above covers the **two
algebraically clean** subcases of the non-standard branch:
1. `σ := 1` with `D.s = C.base.s` and `D.T = {t}` (same-denominator
   singleton).
2. Arbitrary unit `σ : Aˣ` with `(σ : A) * D.s = C.base.s` and
   `D.T = {t}` (unit-rescaled-denominator singleton).

The truly general residual case — `|D.T| ≥ 2` AND/OR `D.s` not a unit
multiple of `C.base.s` — requires the explicit Wedhorn / Zavyalov §2.3
**multi-element σ-domination** construction. The exact missing target
signature is documented below.

### Target signature (general non-standard residual)

```
theorem exists_single_f_refinement_at_t_via_dominating_unit
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
    (_hvt : v.vle t D.s) (_hvD_s : ¬ v.vle D.s 0) :
    ∃ f : A,
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s
```

### Proof sketch (Wedhorn 8.34(ii) / not implemented here)

1. Apply `Cor732.exists_dominating_unit` (`Cor732.lean:206`) to a
   carefully chosen finite test family `T_test ⊆ A` (containing
   appropriate combinations of `D.T`, `D.s`, `C.base.T`, `C.base.s`).
   This yields a unit `σ : Aˣ` with `∀ w ∈ Spa A A⁺, ∃ τ ∈ T_test,
   w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A)` (strict domination).

2. Set `f := (σ : A) * t * D.s ^ (N - 1)` for an exponent `N` chosen
   large enough that `σ`'s domination of `T_test` clears the
   denominator across all `w ∈ Spa(A, A⁺)`.

3. Verify membership: `v.vle f C.base.s` from the chain
   `v(f) = v(σ) * v(t) * v(D.s)^(N-1) ≤ v(C.base.s)` using `_hvt`,
   `_hvD_s`, and σ's domination at `v`.

4. Verify subset: `R(insert f C.base.T, C.base.s) ⊆ R(D.T, D.s)`. For
   arbitrary `w` in the plus-piece-at-`f`, σ-domination transfers
   `w(f) ≤ w(C.base.s)` into `w(t') ≤ w(D.s)` for **every**
   `t' ∈ D.T` (multi-element transfer; singleton case is the
   `_of_singleton_unit_rescaled` helper above) and `w(D.s) ≠ 0`.

### Precise missing valuation-inequality API

The proof step 4 requires a **multi-element σ-clearing lemma** with
target signature

```
lemma vle_of_dominating_unit_multi
    {σ : Aˣ} {f s D_s : A} (T_D : Finset A) (N : ℕ)
    (hf : f = (σ : A) * (T_D.prod id) * D_s ^ N)
    (hσ_dom : ∀ w ∈ Spa A A⁺, ∃ τ ∈ T_D ∪ {D_s},
      w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A))
    {w : Spv A} (hw : w ∈ Spa A A⁺) (hw_f : w.vle f s) :
    (∀ t' ∈ T_D, w.vle t' D_s) ∧ ¬ w.vle D_s 0
```

Closest existing API:
* `Cor732.exists_dominating_unit` (`Cor732.lean:206`) — produces `σ`
  with the per-Spa-point domination, but does NOT supply the multi-`t'`
  conclusion at a single `w`.
* `RationalSubsets.rationalOpen_inter` (`RationalSubsets.lean:72`) —
  algebraic intersection of two rational opens; useful for the
  multi-element case but does not handle the σ-power product
  `D.s^(N-1)`.
* `ValuativeRel.mul_vle_mul`, `Spv.mul_vle_mul_left`,
  `Spv.vle_mul_cancel` — single-multiplication cancellation at units;
  the multi-element / power-product case requires iterating these along
  with the σ-domination per `t' ∈ D.T`.

### Why this is genuinely Wedhorn-content (not new)

Step 4's transfer is precisely Wedhorn's "dominating unit clears the
denominator" lemma (Wedhorn 8.34(ii) / Hübner 3.7). It is NOT a
faithful-flatness or Cor 8.32 argument; it is purely a valuation-
inequality manipulation using σ's `Cor732`-supplied domination plus
finite-element bookkeeping for the test family.

### Where it slots in

After the truly general non-standard helper lands,
`StandardCover.exists_single_f_refining_point_in_D` (target signature
documented at `StandardCover.lean:365-372`) follows by varying `t` over
the (necessarily finite, in the Spa-quasi-compact sense) family of
inequalities that hold at `v` for some `t ∈ D.T`. Combined with
`SpaCompact.isCompact_preimage_rationalOpen_of_tate_pseudouniformizer`
finite-extraction (C2) and `StandardCover.spanTop_iff_noCommonZero_spa`
(C3) this completes `StandardCover.exists_zavyalov_candidate_family`
(target signature documented at `StandardCover.lean:1043`).

### Repository status

This file currently provides the standard-shape branch and the
σ-equipped unit-rescaled-denominator singleton branch (the two
algebraically clean reductions of the non-standard form), plus the
multi-`F` rational-open identity underlying both. The truly general
non-standard branch — multi-element `D.T` and/or non-unit-rescalable
`D.s` — is the next concrete formalisation target along the Wedhorn
8.34(ii) chain; this file's docblock isolates its precise Lean
signature and the precise valuation-inequality API needed to land it. -/

/-! ### T199: Step-2 factor-carrying refinement API

The T197/T198 blocker analysis identified the genuinely missing
upstream piece for T192/T195's `h_struct` per-call provider as the
**per-`(D, t)` algebraic factorization in `A`** plus the **uniform
source f-bound** at every `v ∈ rationalOpen D.T D.s`:

* `C.base.s = D.s * (σ * t * D.s ^ N)` — algebraic factorization;
* `∀ v ∈ rationalOpen D.T D.s, ¬ v.vle D.s 0 → v.vle t D.s →
   v.vle (σ * t * D.s ^ N) C.base.s` — uniform f-bound on the cover
  piece.

T199 packages this content as a **structure**
`WedhornStep2RefinementCarryingFactor` with explicit factorization +
Tate + uniform-bound fields. The bridge
`wedhorn_834_h_struct_via_step2_factor_carrying` shows how a per-
`(D, t)` provider of this structure produces T192/T195's `h_struct`.

The genuinely missing upstream theorem — **the constructor** producing
the factor-carrying refinement from concrete Tate /
pseudouniformizer / cover data — is named precisely as
`wedhorn_834_step2_factor_carrying_constructor_target` (Prop-valued
target signature; not a residual Prop equal to `h_struct`).

The Wedhorn 8.34(ii) Step-2 construction in the literature picks
`f := σ · t · D.s^(N-1)` for σ from Cor 7.32 + N from Spa-quasi-
compactness. The factorization `C.base.s = D.s · σ · t · D.s^(N-1) ·
(rest)` is enforced by the **choice of `f` to lie inside a specific
cover-refinement piece of the rational covering**, NOT by standard
denominator clearing. -/

/-- **T199: Wedhorn 8.34(ii) Step-2 factor-carrying refinement
structure**.

Packages the per-`(C, D, t)` data needed by T192/T195's `h_struct`:

* `σ : A` and `N : ℕ` — the Wedhorn 8.34(ii) `f := σ · t · D.s^(N-1)`
  parameters;
* `h_factor : C.base.s = D.s * (σ * t * D.s ^ N)` — the algebraic
  factorization in `A` (the genuinely missing upstream content per
  T197/T198);
* `h_T_D_in_plus : ∀ t' ∈ D.T, t' ∈ A⁺` — the natural Tate condition
  on `D.T`;
* `h_v_bound` — uniform source f-bound at every `v ∈ rationalOpen
  D.T D.s` satisfying the standard cover-piece preconditions.

The structure binds `(C, D, t)` and lets `(σ, N)` depend on the choice;
the v-bound holds uniformly over the cover piece (not per-v). This
matches Wedhorn's σ-strict-dom + N-choice pattern where `(σ, N)`
depend on the cover but the bound is uniform across Spa points in the
piece. -/
structure WedhornStep2RefinementCarryingFactor (A : Type*)
    [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A]
    (C : RationalCoveringData A) (D : RationalLocData A) (t : A) where
  /-- The Wedhorn σ parameter (`f := σ · t · D.s^(N-1)`). -/
  σ : A
  /-- The Spa-quasi-compactness N-choice exponent. -/
  N : ℕ
  /-- The algebraic factorization in `A` for the chosen `(σ, N)`. -/
  h_factor : C.base.s = D.s * (σ * t * D.s ^ N)
  /-- The natural Tate condition `D.T ⊆ A⁺`. -/
  h_T_D_in_plus : ∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)
  /-- Uniform source f-bound at every `v ∈ rationalOpen D.T D.s`
  with the standard cover-piece preconditions. -/
  h_v_bound :
    ∀ v ∈ rationalOpen D.T D.s,
      v.vle t D.s → ¬ v.vle D.s 0 →
      v.vle (σ * t * D.s ^ N) C.base.s

/-- **T199 factor-carrying provider Prop**.

Per-`(D, t)` Nonempty `WedhornStep2RefinementCarryingFactor`. This is
the natural per-cover provider shape; its discharge from concrete Tate
/ cover data is the missing upstream constructor (named precisely
below as `wedhorn_834_step2_factor_carrying_constructor_target`). -/
def WedhornStep2FactorCarryingProvider {A : Type*}
    [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A]
    (C : RationalCoveringData A) : Prop :=
  ∀ (D : RationalLocData A), D ∈ C.covers →
  ∀ (t : A), t ∈ D.T →
    Nonempty (WedhornStep2RefinementCarryingFactor A C D t)

/-- **T199 bridge: factor-carrying provider produces T192/T195
`h_struct` shape**.

From a per-`(D, t)` `WedhornStep2FactorCarryingProvider`, produces the
exact `h_struct` shape consumed by
`hZavyalov_per_E_via_single_t_structural_data_of_base_eq_Spa` (T192)
and
`tateAcyclicity_Part2_via_single_t_structural_data_and_integrated_laneB`
(T195).

This bridge **isolates the genuinely Wedhorn-content boundary**: the
caller supplies the factor-carrying provider (a per-`(D, t)` data
package satisfying the Wedhorn 8.34(ii) Step-2 algebraic factorization
+ Tate condition + uniform v-bound), and the bridge mechanically
unpacks it to feed the per-call existential of T195's `h_struct`. -/
theorem wedhorn_834_h_struct_via_step2_factor_carrying {A : Type*}
    [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A]
    (C : RationalCoveringData A)
    (h_provider : WedhornStep2FactorCarryingProvider C) :
    ∀ (D : RationalLocData A), D ∈ C.covers →
    ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
    ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
      ∃ (σ : A) (N : ℕ),
        C.base.s = D.s * (σ * t * D.s ^ N) ∧
        (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
        v.vle (σ * t * D.s ^ N) C.base.s := by
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨carry⟩ := h_provider D hD t ht
  exact ⟨carry.σ, carry.N, carry.h_factor, carry.h_T_D_in_plus,
    carry.h_v_bound v hv hvt hvD_s⟩

/-- **T199 missing constructor target signature** (the genuinely
remaining Wedhorn 8.34(ii) Step-2 content).

Precise Lean type of the next theorem-level ticket: the constructor
producing `WedhornStep2FactorCarryingProvider C` from concrete Tate /
pseudouniformizer / cover data.

The intended discharge follows Wedhorn 8.34(ii) Step-2:
1. Apply Cor 7.32 (`exists_dominating_unit`) inside a localization or
   directly on `Spa A A⁺` (depending on the Wedhorn variant) to obtain
   a unit σ with σ-strict-domination over a test family that includes
   `D.s` and the elements of `D.T`.
2. Apply Spa-quasi-compactness + topological nilpotence of σ-as-π-power
   to choose `N : ℕ` large enough that `f := σ · t · D.s^(N-1)`
   satisfies `v.vle f C.base.s` uniformly on `rationalOpen D.T D.s`.
3. Verify the algebraic factorization `C.base.s = D.s · σ · t · D.s^N`
   in `A` — this is enforced by the cover-refinement choice of the
   factor.
4. Verify the Tate condition `D.T ⊆ A⁺` — typically a structural
   property of the cover-refinement family.

The natural cover families to discharge this on:
* the per-`E` localized cover `C.per_E_local_covering`;
* the σ-rescaled Laurent cover `cor732_laurent_cover_covers_spa`;
* explicit Wedhorn 8.34(ii) cover-refinement constructions.

This Prop's discharge is the **next critical-path theorem-level work**
after T199's structural API. It is NOT a residual Prop equal to
`h_struct`: the constructor produces a specific structural data
package, which then mechanically feeds `h_struct` via the bridge above. -/
def wedhorn_834_step2_factor_carrying_constructor_target {A : Type*}
    [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A]
    (C : RationalCoveringData A) : Prop :=
  WedhornStep2FactorCarryingProvider C

/-! ### T200: per-call data → factor-carrying provider lower bridge

T199 isolated the genuinely missing upstream content as the per-`(D, t)`
factor-carrying refinement structure. Constructing this structure for a
non-trivial cover-refinement family from concrete Cor 7.32 / Spa-
quasi-compactness data is genuine Wedhorn 8.34(ii) Step-2 content (the
proof sketch above lines 442-460 outlines the four sub-steps).

T200 provides:

1. A **compiled lower bridge** `WedhornStep2FactorCarryingProvider_of_per_call_carrying`
   that takes per-`(D, t)` Prop-form factor data — the existential of
   the Step-2 carrying-factor structure's fields — and produces the
   `WedhornStep2FactorCarryingProvider C` shape consumed by T199's
   `wedhorn_834_h_struct_via_step2_factor_carrying`. This packaging is
   useful because the Prop existential form is the **natural way to
   discharge per-`(D, t)` carrying-factor data** (it matches the shape
   of `h_struct` itself, but per-`(D, t)` rather than per-`(D, v, t)`,
   and crucially the `(σ, N)` pick is inside the existential rather
   than depending on `v`).

2. A **precise compiled boundary** for the next concrete cover-
   refinement family on which to discharge the per-call data — naming
   the four sub-inputs (Cor 7.32 σ-choice, Spa-quasi-compact N-choice,
   algebraic factorization verification, Tate condition + uniform
   v-bound verification) — distinct from the parked false lanes.

The lower bridge does NOT discharge the missing constructor itself; it
isolates the per-`(D, t)` Prop-form discharge as the next theorem-level
work, ready to be filled in for any concrete cover candidate. -/

/-- **T200 lower bridge**: per-`(D, t)` Prop-form factor data produces
the `WedhornStep2FactorCarryingProvider C`.

The hypothesis `h_carrying` is the **per-`(D, t)` existential** of
`WedhornStep2RefinementCarryingFactor`'s fields:

* `σ : A` and `N : ℕ` chosen for this `(D, t)`;
* `C.base.s = D.s * (σ * t * D.s ^ N)` — algebraic factorization;
* `∀ t' ∈ D.T, t' ∈ A⁺` — Tate condition;
* uniform v-bound on `rationalOpen D.T D.s`.

The conclusion is the provider Prop, which then feeds `h_struct` via
`wedhorn_834_h_struct_via_step2_factor_carrying` (T199 bridge). The
proof is mechanical: extract the existential, pack into the structure
constructor, wrap as `Nonempty`.

**Useful for next theorem-level work**: discharging the
`WedhornStep2FactorCarryingProvider C` for a non-trivial cover family
reduces to discharging the per-`(D, t)` Prop existential, which is the
natural per-call shape of Wedhorn 8.34(ii) Step-2 data. The four sub-
inputs (Cor 7.32 σ, Spa-quasi-compact N, algebraic identity, v-bound)
can be discharged independently inside the existential. -/
theorem WedhornStep2FactorCarryingProvider_of_per_call_carrying
    (C : RationalCoveringData A)
    (h_carrying : ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (t : A), t ∈ D.T →
        ∃ (σ : A) (N : ℕ),
          C.base.s = D.s * (σ * t * D.s ^ N) ∧
          (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
          (∀ v ∈ rationalOpen D.T D.s,
            v.vle t D.s → ¬ v.vle D.s 0 →
            v.vle (σ * t * D.s ^ N) C.base.s)) :
    WedhornStep2FactorCarryingProvider C := by
  intro D hD t ht
  obtain ⟨σ, N, h_factor, h_T_D_in_plus, h_v_bound⟩ := h_carrying D hD t ht
  exact ⟨⟨σ, N, h_factor, h_T_D_in_plus, h_v_bound⟩⟩

/-! ### T200: precise compiled boundary for a concrete cover candidate

The natural concrete cover candidate beyond T198's trivial whole-Spa
construction is one carrying explicit Cor 7.32 σ + N data tied to the
cover-refinement element `f := σ * t * D.s ^ (N - 1)` (Wedhorn
8.34(ii) Step-2 literature recipe). For any such cover candidate, the
per-`(D, t)` data needed by
`WedhornStep2FactorCarryingProvider_of_per_call_carrying` decomposes
into four sub-inputs:

* **(I-σ) Cor 7.32 σ-choice**:
  ```
  ∃ σ : A, σ-strict-domination over a test family containing
    `t` and `D.s` and the elements of `D.T`
  ```

* **(I-N) Spa-quasi-compact N-choice**:
  ```
  ∃ N : ℕ, the σ-power-decay `σ · D.s^(N-1)` clears the denominator
    `C.base.s` uniformly on `rationalOpen D.T D.s`
  ```

* **(I-f) Algebraic factorization verification**:
  ```
  C.base.s = D.s * (σ * t * D.s ^ N)
  ```
  This is the **genuinely missing per-cover content**: the cover-
  refinement piece `D` must be constructed so that its denominator
  divides `C.base.s` with the explicit multiplicative chain
  `D.s · σ · t · D.s ^ N`. None of the existing constructions
  (`laurentPlusDatum`, `laurentMinusDatum`, `per_E_local_covering`,
  `cor732_laurent_cover_covers_spa`'s pieces) supply this identity in
  `A`; the existing `_via_dominating_unit` target (line 422 above)
  supplies only the rationalOpen subset relation, NOT the algebraic
  identity.

* **(I-v) Uniform v-bound verification + Tate condition**:
  ```
  ∀ t' ∈ D.T, t' ∈ A⁺
  ∀ v ∈ rationalOpen D.T D.s, v.vle t D.s → ¬ v.vle D.s 0 →
    v.vle (σ * t * D.s ^ N) C.base.s
  ```
  The Tate condition is structural for the chosen cover family.
  The v-bound follows from (I-σ) σ-strict-domination + (I-N)
  N-choice + transitivity once `(σ, N)` are fixed.

**The first missing theorem signature** for a concrete cover-refinement
family is:

```
theorem exists_per_call_carrying_factor_for_<cover_family>
    [<Tate hypothesis bundle>]
    (P : PairOfDefinition A) (...) (C : RationalCoveringData A)
    (h_cover_shape : <cover-family-specific structural hypotheses>) :
    ∀ (D : RationalLocData A), D ∈ C.covers →
    ∀ (t : A), t ∈ D.T →
      ∃ (σ : A) (N : ℕ),
        C.base.s = D.s * (σ * t * D.s ^ N) ∧
        (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
        (∀ v ∈ rationalOpen D.T D.s,
          v.vle t D.s → ¬ v.vle D.s 0 →
          v.vle (σ * t * D.s ^ N) C.base.s)
```

This signature is the precise next theorem-level work. Discharging it
for a concrete cover family requires:

1. A specific `<cover_family>` whose pieces' denominators `D.s` carry
   an explicit factorization with `C.base.s` (so (I-f) holds by
   construction). Existing candidates DO NOT satisfy this; the missing
   construction is a **factor-carrying refinement** whose pieces are
   built specifically to make (I-f) algebraically.

2. Cor 7.32 + Spa-quasi-compactness for (I-σ) and (I-N) — already
   available via `Cor732.exists_dominating_unit` + `SpaCompact`.

3. Tate condition (I-T_D) — structural property of the cover family.

4. v-bound (I-v) — derived from (I-σ) + (I-N) + (I-f) by the standard
   `vle_of_dominating_unit_multi`-style argument.

**Routing through T199 provider**: once the per-call carrying-factor
existential is discharged for a concrete cover family,
`WedhornStep2FactorCarryingProvider_of_per_call_carrying` packages it
into the provider, and `wedhorn_834_h_struct_via_step2_factor_carrying`
(T199 bridge) packages the provider into T192/T195's `h_struct`. The
end-to-end pipeline becomes:

```
exists_per_call_carrying_factor_for_<cover_family>  [missing, T200's
                                                     blocker]
  ↓  (WedhornStep2FactorCarryingProvider_of_per_call_carrying, T200)
WedhornStep2FactorCarryingProvider C                 [T199 def]
  ↓  (wedhorn_834_h_struct_via_step2_factor_carrying, T199 bridge)
h_struct C                                           [T192/T195 input]
  ↓  (T192/T195 wrappers)
hZavyalov_per_E / Tate acyclicity Part 2
```

**Why this avoids the parked false lanes**:

* The per-call existential is per-`(D, t)`, not Spa-uniform: NO
  σ-power-decay or M-power-decay shape.
* The existential gives concrete `(σ, N) : A × ℕ`: NO locSubring
  integrally-closed or denominator-clearing `n = 0` content.
* The factorization is single-`t` and per-call: NO multi-product
  exact `h_alg`.
* The v-bound's σ-strict-domination is a **per-cover** input, not a
  clause-2 path.

The lower bridge above is **purely additive structural packaging**;
no Wedhorn content is hidden inside it. -/

/-! ### T201: strengthened single-f Step-2 target + compiled bridges

The documented `exists_single_f_refinement_at_t_via_dominating_unit`
target signature (line 422 above) supplies, for `D ∈ C.covers` and
`t ∈ D.T`, an element `f : A` with:

* `v ∈ rationalOpen (insert f C.base.T) C.base.s` (source plus-piece
  membership at `v`);
* `rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s`
  (rationalOpen subset).

This is **NOT enough** to feed T199's `WedhornStep2RefinementCarryingFactor`:
we additionally need the algebraic identity
`C.base.s = D.s * (σ * t * D.s ^ N)` in `A`, the Tate condition
`∀ t' ∈ D.T, t' ∈ A⁺`, and the uniform v-bound on
`rationalOpen D.T D.s`.

T201 strengthens the documented target by carrying these extra fields,
and compiles bridges from the strengthened target to T199's structure
and T199's provider via T200's lower bridge.

The strengthened target's discharge is the **next missing theorem**;
the bridges compile mechanically and route the discharge into the
T192/T195 `h_struct` pipeline.

What this section provides:

* `exists_single_f_factor_carrying_refinement_at_t_target` — the
  per-`(D, t)` strengthened-single-f Prop with explicit `(σ, N, f)`
  fields plus algebraic identity, rationalOpen subset, Tate, and
  uniform v-bound.

* `WedhornStep2RefinementCarryingFactor_of_strengthened_single_f` —
  per-`(D, t)` bridge: from the strengthened Prop, build the T199
  carrying-factor structure.

* `WedhornStep2FactorCarryingProvider_of_strengthened_single_f` —
  per-cover bridge: from the per-`(D, t)` strengthened Prop, produce
  the T199 provider via T200's lower bridge.

* `wedhorn_834_h_struct_via_strengthened_single_f` — full end-to-end
  bridge composing T201 + T200 + T199 to produce T192/T195's
  `h_struct` from the per-`(D, t)` strengthened single-f Prop directly.

The pipeline once the strengthened single-f target is discharged for a
concrete cover-refinement family:

```
exists_single_f_factor_carrying_refinement_at_t_target  [T201's blocker]
  ↓ (WedhornStep2RefinementCarryingFactor_of_strengthened_single_f, T201)
Nonempty (WedhornStep2RefinementCarryingFactor A C D t)  [T199 structure]
  ↓ (Nonempty.intro packaged in
     WedhornStep2FactorCarryingProvider_of_per_call_carrying, T200)
WedhornStep2FactorCarryingProvider C                     [T199 def]
  ↓ (wedhorn_834_h_struct_via_step2_factor_carrying, T199 bridge)
h_struct C                                               [T192/T195 input]
```

The strengthened target adds **only the algebraic identity** (`C.base.s =
D.s * f`) plus the Tate condition and the uniform v-bound; it does
NOT change the source-side (`v ∈ rationalOpen ...`) or σ-strict-
domination shape of the original `_via_dominating_unit` target. The
genuine Wedhorn 8.34(ii) Step-2 content needed for the discharge is
the same as before, with the algebraic identity carried alongside the
rationalOpen subset relation. -/

omit [PlusSubring A] in
/-- **T201 strengthened single-f Step-2 target** (per-`(D, t)`).

Strengthens the documented `exists_single_f_refinement_at_t_via_dominating_unit`
target by carrying:

* `f := σ * t * D.s ^ N` for explicit `(σ, N) : A × ℕ` (the Wedhorn
  Step-2 element shape);
* `C.base.s = D.s * f` — the **algebraic identity in `A`** (the
  central missing content per T197/T198/T199);
* `rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s`
  — the rationalOpen subset relation (already in the documented
  target);
* `∀ t' ∈ D.T, t' ∈ A⁺` — the Tate condition on `D.T`;
* `∀ v ∈ rationalOpen D.T D.s, v.vle t D.s → ¬ v.vle D.s 0 →
  v.vle f C.base.s` — the uniform source f-bound on the cover piece.

Discharging this Prop for a concrete cover-refinement family is the
**next critical-path theorem-level work**. The discharge follows the
same proof sketch as the documented `_via_dominating_unit` target
(Cor 7.32 σ + Spa-quasi-compact N + transitivity), with the algebraic
identity carried alongside the rationalOpen-side conclusion. -/
def exists_single_f_factor_carrying_refinement_at_t_target
    {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A] [DecidableEq A]
    (C : RationalCoveringData A) (D : RationalLocData A) (t : A) : Prop :=
  ∃ (σ : A) (N : ℕ) (f : A),
    f = σ * t * D.s ^ N ∧
    C.base.s = D.s * f ∧
    rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s ∧
    (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
    (∀ v ∈ rationalOpen D.T D.s,
      v.vle t D.s → ¬ v.vle D.s 0 →
      v.vle f C.base.s)

/-- **T201 per-`(D, t)` bridge: strengthened single-f → T199 structure**.

From the strengthened single-f target, build the T199 carrying-factor
structure `WedhornStep2RefinementCarryingFactor A C D t` (wrapped in
`Nonempty`).

Proof: extract the existential witnesses `(σ, N, f)`, rewrite
`σ * t * D.s ^ N = f` via `hf_eq`, and use `h_factor`, `h_T_D_in_plus`,
`h_v_bound` directly as the structure's fields. The rationalOpen
subset is unused in the structure (it is needed only for downstream
rationalOpen consumers, not for the carrying-factor data itself). -/
theorem WedhornStep2RefinementCarryingFactor_of_strengthened_single_f
    {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A] [DecidableEq A]
    (C : RationalCoveringData A) (D : RationalLocData A) (t : A)
    (h_target : exists_single_f_factor_carrying_refinement_at_t_target C D t) :
    Nonempty (WedhornStep2RefinementCarryingFactor A C D t) := by
  obtain ⟨σ, N, f, rfl, h_factor, _h_subset, h_T_D_in_plus, h_v_bound⟩ :=
    h_target
  exact ⟨σ, N, h_factor, h_T_D_in_plus, h_v_bound⟩

/-- **T201 per-cover bridge: strengthened single-f → T199 provider**.

From the per-`(D, t)` strengthened single-f target, produce the T199
`WedhornStep2FactorCarryingProvider C` shape consumed by
`wedhorn_834_h_struct_via_step2_factor_carrying`.

Routes through T200's `WedhornStep2FactorCarryingProvider_of_per_call_carrying`
indirectly via the per-`(D, t)` carrying-factor structure. -/
theorem WedhornStep2FactorCarryingProvider_of_strengthened_single_f
    {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A] [DecidableEq A]
    (C : RationalCoveringData A)
    (h_target : ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (t : A), t ∈ D.T →
        exists_single_f_factor_carrying_refinement_at_t_target C D t) :
    WedhornStep2FactorCarryingProvider C := by
  intro D hD t ht
  exact WedhornStep2RefinementCarryingFactor_of_strengthened_single_f C D t
    (h_target D hD t ht)

/-- **T201 end-to-end bridge: strengthened single-f → `h_struct` shape**.

Composes T201's per-cover bridge with T199's
`wedhorn_834_h_struct_via_step2_factor_carrying` to produce T192/T195's
`h_struct` shape directly from the per-`(D, t)` strengthened single-f
target. -/
theorem wedhorn_834_h_struct_via_strengthened_single_f
    {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A] [DecidableEq A]
    (C : RationalCoveringData A)
    (h_target : ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (t : A), t ∈ D.T →
        exists_single_f_factor_carrying_refinement_at_t_target C D t) :
    ∀ (D : RationalLocData A), D ∈ C.covers →
    ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
    ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
      ∃ (σ : A) (N : ℕ),
        C.base.s = D.s * (σ * t * D.s ^ N) ∧
        (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
        v.vle (σ * t * D.s ^ N) C.base.s :=
  wedhorn_834_h_struct_via_step2_factor_carrying C
    (WedhornStep2FactorCarryingProvider_of_strengthened_single_f C h_target)

/-! ### T204: integrate localisation transfer into strengthened Step-2 target

T201 introduced `exists_single_f_factor_carrying_refinement_at_t_target`
and the bridges to `h_struct`. T202/T203
(`WedhornMultiDominatingUnit.lean`) provided the bidirectional
comap/localisation pair for `rationalOpen T s` and
`Spa(Localization.Away s)`. T204 integrates the two: it discharges the
T201 strengthened target's per-`v` `h_v_bound` clause from a **localised
f-bound** on `Spa(Localization.Away D.s, ⁺)` by:

1. Lifting `v ∈ rationalOpen D.T D.s` to
   `w ∈ Spa(Localization.Away D.s, ⁺)` via T203
   (`exists_localization_lift_of_rationalOpen`), with `comap w = v`.
2. Applying the localised f-bound at `w`:
   `w.vle (algebraMap f) (algebraMap C.base.s)`.
3. Transferring the bound back to `v.vle f C.base.s` via
   `comap_vle` and the fact that `comap w = v`.

This is the standard Wedhorn 8.34(ii) Step-2 σ-clearing route:
pre-localise at `D.s`, run σ-construction inside the localised Spa,
transfer back via comap.

The compiled bridge below packages this routing as a per-`(C, D, t)`
constructor for the T201 strengthened target, taking the **localised
f-bound** as a hypothesis. The localised f-bound is the natural
output of `Cor732.exists_dominating_unit` (or its localised variant)
applied inside `Spa(Localization.Away D.s, ⁺)`; discharging it for a
specific cover-refinement family is the next theorem-level work.

The bridge does NOT discharge the localised f-bound itself; it isolates
it as the **last remaining input** for the T201 strengthened target.
The h_factor algebraic identity, h_subset rationalOpen subset,
h_T_D_in_plus Tate condition, and the `(σ, N, f)` parameters are
taken as inputs alongside the localised bound. -/

/-- **T204 localisation-transfer bridge**: discharges T201's
`exists_single_f_factor_carrying_refinement_at_t_target` from a
localised f-bound on `Spa(Localization.Away D.s, ⁺)`.

**Inputs**:
* `(σ, N, f, hf_eq)` — Wedhorn Step-2 element parameters;
* `h_factor` — algebraic identity in `A`: `C.base.s = D.s * f`;
* `h_subset` — rationalOpen subset relation:
  `R(insert f C.base.T, C.base.s) ⊆ R(D.T, D.s)`;
* `h_T_D_in_plus` — Tate condition: `D.T ⊆ A⁺`;
* `hA₀_le` — standard pair-of-definition direction `D.P.A₀ ≤ A⁺`;
* `h_loc_bound` — **localised f-bound**: at every
  `w ∈ Spa(Localization.Away D.s, ⁺)`,
  `w.vle (algebraMap f) (algebraMap C.base.s)`.

**Output**: `exists_single_f_factor_carrying_refinement_at_t_target C D t`
— the T201 strengthened target with the per-`v` `h_v_bound` discharged
from the localised f-bound via T203 (lift) + comap transfer.

**Proof**: extract Spa-membership and non-vanishing from `hv`, lift `v`
to `w ∈ Spa(Loc D.s, ⁺)` via `exists_localization_lift_of_rationalOpen`
(T203), apply `h_loc_bound` at `w`, rewrite via `comap_vle` and
`hw_comap` to recover `v.vle f C.base.s`. -/
theorem exists_single_f_factor_carrying_refinement_at_t_via_localisation_transfer
    {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A] [DecidableEq A]
    (C : RationalCoveringData A) (D : RationalLocData A) (t : A)
    (hA₀_le : D.P.A₀ ≤ A⁺)
    (σ : A) (N : ℕ) (f : A)
    (hf_eq : f = σ * t * D.s ^ N)
    (h_factor : C.base.s = D.s * f)
    (h_subset : rationalOpen (insert f C.base.T) C.base.s ⊆
      rationalOpen D.T D.s)
    (h_T_D_in_plus : ∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A))
    (h_loc_bound :
      letI : TopologicalSpace (Localization.Away D.s) :=
        locTopology D.P D.T D.s D.hopen
      letI : PlusSubring (Localization.Away D.s) :=
        localizationAwayPlusSubring D.s
      ∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
        w.vle (algebraMap A (Localization.Away D.s) f)
              (algebraMap A (Localization.Away D.s) C.base.s)) :
    exists_single_f_factor_carrying_refinement_at_t_target C D t := by
  refine ⟨σ, N, f, hf_eq, h_factor, h_subset, h_T_D_in_plus, ?_⟩
  intro v hv _hvt _hvD_s
  letI : TopologicalSpace (Localization.Away D.s) :=
    locTopology D.P D.T D.s D.hopen
  letI : PlusSubring (Localization.Away D.s) :=
    localizationAwayPlusSubring D.s
  obtain ⟨w, hw_spa, hw_comap⟩ :=
    exists_localization_lift_of_rationalOpen D.P D.T D.s D.hopen hA₀_le hv
  rw [← hw_comap, comap_vle]
  exact h_loc_bound w hw_spa

/-! ### T207: specialise T205 localised σ-clearing reducer to T204 f-bound

T204 (`exists_single_f_factor_carrying_refinement_at_t_via_localisation_transfer`)
takes a **single-`f` localised f-bound** of shape

```
∀ w ∈ Spa(Loc D.s, ⁺),
  w.vle (algMap f) (algMap C.base.s)
```

T205 (`WedhornMultiDominatingUnit.localised_sigma_clearing_bounds_for_localisation_transfer`,
commit 437f993) supplies a more general `(T', s')` two-conjunct shape
from a localised σ-strict-domination + per-`τ` algebraic bridge. T207
**specialises** T205 at `T' := {f}, s' := C.base.s` and extracts the
singleton bound, producing exactly T204's `h_loc_bound` input.

The composition T207 + T204 + T201 + T199 produces T192/T195's
`h_struct` shape, with **only mathematical input** the per-`τ`
algebraic σ-clearing bridge `h_per_τ_bound` and the black-box
σ-strict-domination `h_sigma_loc`. The black-box `h_sigma_loc` will
be discharged by T206 (Tertiary) when it lands. -/

/-- **T207 specialised localised σ-clearing reducer: single-`f` bound**.

Specialises T205 (`localised_sigma_clearing_bounds_for_localisation_transfer`)
at `T' := {f}, s' := C.base.s`, producing exactly T204's
`h_loc_bound` input from a localised σ-strict-domination
`h_sigma_loc` plus a per-`τ` algebraic bridge `h_per_τ_bound`.

**Inputs**:
* `(σ, N, f, hf_eq)` — Wedhorn Step-2 element parameters (passed
  through to keep the signature compatible with T204).
* `(T_test_loc, σ_loc)` — finite test family + unit on `Loc D.s`.
* `h_sigma_loc` — Cor 7.32-shape σ-strict-domination on
  `Spa(Loc D.s, ⁺)` (T206 will eventually discharge this).
* `h_per_τ_bound` — per-`τ` algebraic bridge **at T' = {f}**: at
  every `τ ∈ T_test_loc` and every `w ∈ Spa(Loc D.s, ⁺)` with
  σ-strict-dom witness `τ`, the singleton-product bound
  `w.vle (algMap f) (algMap C.base.s)` plus the non-vanishing of
  `algMap C.base.s` at `w`.

**Output**: T204's exact `h_loc_bound` input shape:
`∀ w ∈ Spa(Loc D.s, ⁺), w.vle (algMap f) (algMap C.base.s)`.

**Proof**: apply T205 at `T' := {f}, s' := C.base.s`; extract the
singleton bound via `Finset.mem_singleton_self`. -/
theorem localised_sigma_reducer_to_single_f_bound_for_step2
    {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A] [DecidableEq A]
    (C : RationalCoveringData A) (D : RationalLocData A) (t : A)
    (σ : A) (N : ℕ) (f : A) (_hf_eq : f = σ * t * D.s ^ N)
    (T_test_loc : Finset (Localization.Away D.s))
    (σ_loc : (Localization.Away D.s)ˣ)
    (h_sigma_loc :
      letI : TopologicalSpace (Localization.Away D.s) :=
        locTopology D.P D.T D.s D.hopen
      letI : PlusSubring (Localization.Away D.s) :=
        localizationAwayPlusSubring D.s
      ∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
        ∃ τ ∈ T_test_loc,
          w.vle (σ_loc : Localization.Away D.s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away D.s))
    (h_per_τ_bound :
      letI : TopologicalSpace (Localization.Away D.s) :=
        locTopology D.P D.T D.s D.hopen
      letI : PlusSubring (Localization.Away D.s) :=
        localizationAwayPlusSubring D.s
      ∀ τ ∈ T_test_loc,
        ∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
          (w.vle (σ_loc : Localization.Away D.s) τ ∧
           ¬ w.vle τ (σ_loc : Localization.Away D.s)) →
          (∀ t' ∈ ({f} : Finset A),
            w.vle (algebraMap A (Localization.Away D.s) t')
                  (algebraMap A (Localization.Away D.s) C.base.s)) ∧
          ¬ w.vle (algebraMap A (Localization.Away D.s) C.base.s) 0) :
    letI : TopologicalSpace (Localization.Away D.s) :=
      locTopology D.P D.T D.s D.hopen
    letI : PlusSubring (Localization.Away D.s) :=
      localizationAwayPlusSubring D.s
    ∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
      w.vle (algebraMap A (Localization.Away D.s) f)
            (algebraMap A (Localization.Away D.s) C.base.s) := by
  letI : TopologicalSpace (Localization.Away D.s) :=
    locTopology D.P D.T D.s D.hopen
  letI : PlusSubring (Localization.Away D.s) :=
    localizationAwayPlusSubring D.s
  intro w hw
  exact (localised_sigma_clearing_bounds_for_localisation_transfer
    D.P D.T D.s D.hopen ({f} : Finset A) C.base.s T_test_loc σ_loc
    h_sigma_loc h_per_τ_bound w hw).1 f (Finset.mem_singleton_self f)

/-- **T207 composed bridge: localised σ-data → strengthened target**.

Composes T207's specialised localised σ-clearing reducer (above) with
T204's `exists_single_f_factor_carrying_refinement_at_t_via_localisation_transfer`
to produce T201's strengthened single-f target directly from the
**localised σ-strict-domination** + **per-`τ` algebraic bridge**
inputs (plus the standard T201 fields).

This is the **strongest currently-compilable bridge** along the T204
path: only mathematical inputs are `h_sigma_loc` (T206's eventual
output) and `h_per_τ_bound` (the per-`τ` algebraic σ-clearing bridge,
genuine Wedhorn 8.34(ii) Step-2 content). -/
theorem exists_single_f_factor_carrying_refinement_at_t_via_localised_sigma
    {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A] [DecidableEq A]
    (C : RationalCoveringData A) (D : RationalLocData A) (t : A)
    (hA₀_le : D.P.A₀ ≤ A⁺)
    (σ : A) (N : ℕ) (f : A)
    (hf_eq : f = σ * t * D.s ^ N)
    (h_factor : C.base.s = D.s * f)
    (h_subset : rationalOpen (insert f C.base.T) C.base.s ⊆
      rationalOpen D.T D.s)
    (h_T_D_in_plus : ∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A))
    (T_test_loc : Finset (Localization.Away D.s))
    (σ_loc : (Localization.Away D.s)ˣ)
    (h_sigma_loc :
      letI : TopologicalSpace (Localization.Away D.s) :=
        locTopology D.P D.T D.s D.hopen
      letI : PlusSubring (Localization.Away D.s) :=
        localizationAwayPlusSubring D.s
      ∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
        ∃ τ ∈ T_test_loc,
          w.vle (σ_loc : Localization.Away D.s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away D.s))
    (h_per_τ_bound :
      letI : TopologicalSpace (Localization.Away D.s) :=
        locTopology D.P D.T D.s D.hopen
      letI : PlusSubring (Localization.Away D.s) :=
        localizationAwayPlusSubring D.s
      ∀ τ ∈ T_test_loc,
        ∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
          (w.vle (σ_loc : Localization.Away D.s) τ ∧
           ¬ w.vle τ (σ_loc : Localization.Away D.s)) →
          (∀ t' ∈ ({f} : Finset A),
            w.vle (algebraMap A (Localization.Away D.s) t')
                  (algebraMap A (Localization.Away D.s) C.base.s)) ∧
          ¬ w.vle (algebraMap A (Localization.Away D.s) C.base.s) 0) :
    exists_single_f_factor_carrying_refinement_at_t_target C D t :=
  exists_single_f_factor_carrying_refinement_at_t_via_localisation_transfer
    C D t hA₀_le σ N f hf_eq h_factor h_subset h_T_D_in_plus
    (localised_sigma_reducer_to_single_f_bound_for_step2 C D t σ N f hf_eq
      T_test_loc σ_loc h_sigma_loc h_per_τ_bound)

/-- **T207 end-to-end bridge: localised σ-data → `h_struct`**.

Composes the T207 strengthened-target bridge with T201's
`wedhorn_834_h_struct_via_strengthened_single_f` to produce T192/T195's
`h_struct` shape directly from per-`(D, t)` localised σ-data
(σ-strict-domination + per-`τ` algebraic bridge) plus the standard
T201 fields. -/
theorem wedhorn_834_h_struct_via_localised_sigma
    {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A] [DecidableEq A]
    (C : RationalCoveringData A)
    (h_per_call :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (t : A), t ∈ D.T →
      ∃ (_hA₀_le : D.P.A₀ ≤ A⁺) (σ : A) (N : ℕ) (f : A)
        (_hf_eq : f = σ * t * D.s ^ N)
        (_h_factor : C.base.s = D.s * f)
        (_h_subset : rationalOpen (insert f C.base.T) C.base.s ⊆
          rationalOpen D.T D.s)
        (_h_T_D_in_plus : ∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A))
        (_T_test_loc : Finset (Localization.Away D.s))
        (_σ_loc : (Localization.Away D.s)ˣ),
        letI : TopologicalSpace (Localization.Away D.s) :=
          locTopology D.P D.T D.s D.hopen
        letI : PlusSubring (Localization.Away D.s) :=
          localizationAwayPlusSubring D.s
        (∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
          ∃ τ ∈ _T_test_loc,
            w.vle (_σ_loc : Localization.Away D.s) τ ∧
            ¬ w.vle τ (_σ_loc : Localization.Away D.s)) ∧
        (∀ τ ∈ _T_test_loc,
          ∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
            (w.vle (_σ_loc : Localization.Away D.s) τ ∧
             ¬ w.vle τ (_σ_loc : Localization.Away D.s)) →
            (∀ t' ∈ ({f} : Finset A),
              w.vle (algebraMap A (Localization.Away D.s) t')
                    (algebraMap A (Localization.Away D.s) C.base.s)) ∧
            ¬ w.vle (algebraMap A (Localization.Away D.s) C.base.s) 0)) :
    ∀ (D : RationalLocData A), D ∈ C.covers →
    ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
    ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
      ∃ (σ : A) (N : ℕ),
        C.base.s = D.s * (σ * t * D.s ^ N) ∧
        (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
        v.vle (σ * t * D.s ^ N) C.base.s :=
  wedhorn_834_h_struct_via_strengthened_single_f C
    (fun D hD t ht => by
      obtain ⟨hA₀_le, σ, N, f, hf_eq, h_factor, h_subset, h_T_D_in_plus,
        T_test_loc, σ_loc, h_sigma_loc, h_per_τ_bound⟩ :=
          h_per_call D hD t ht
      exact exists_single_f_factor_carrying_refinement_at_t_via_localised_sigma
        C D t hA₀_le σ N f hf_eq h_factor h_subset h_T_D_in_plus
        T_test_loc σ_loc h_sigma_loc h_per_τ_bound)

/-- **T204 end-to-end bridge: localisation-transfer → `h_struct`**.

Composes the T204 localisation-transfer bridge above with T201's
`wedhorn_834_h_struct_via_strengthened_single_f` to produce T192/T195's
`h_struct` shape directly from per-`(D, t)` localised f-bound +
algebraic identity + Tate condition + rationalOpen subset.

Pipeline:
```
per-(D, t) [σ, N, f, hf_eq, h_factor, h_subset, h_T_D_in_plus,
            hA₀_le, h_loc_bound]
  ↓ (T204 exists_single_f_factor_carrying_refinement_at_t_via_localisation_transfer)
exists_single_f_factor_carrying_refinement_at_t_target C D t  [T201]
  ↓ (T201 wedhorn_834_h_struct_via_strengthened_single_f)
h_struct C  [T192/T195 input]
```

The localised f-bound `h_loc_bound` is the natural output of
`Cor732.exists_dominating_unit` applied inside `Spa(Loc D.s, ⁺)` (with
`σ_loc` chosen via Cor 7.32 + N via Spa-quasi-compactness). Discharging
it for a concrete cover-refinement family is the **next theorem-level
work after T204**. -/
theorem wedhorn_834_h_struct_via_localisation_transfer
    {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A] [DecidableEq A]
    (C : RationalCoveringData A)
    (h_per_call :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (t : A), t ∈ D.T →
      ∃ (_hA₀_le : D.P.A₀ ≤ A⁺) (σ : A) (N : ℕ) (f : A)
        (_hf_eq : f = σ * t * D.s ^ N)
        (_h_factor : C.base.s = D.s * f)
        (_h_subset : rationalOpen (insert f C.base.T) C.base.s ⊆
          rationalOpen D.T D.s)
        (_h_T_D_in_plus : ∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)),
        letI : TopologicalSpace (Localization.Away D.s) :=
          locTopology D.P D.T D.s D.hopen
        letI : PlusSubring (Localization.Away D.s) :=
          localizationAwayPlusSubring D.s
        ∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
          w.vle (algebraMap A (Localization.Away D.s) f)
                (algebraMap A (Localization.Away D.s) C.base.s)) :
    ∀ (D : RationalLocData A), D ∈ C.covers →
    ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
    ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
      ∃ (σ : A) (N : ℕ),
        C.base.s = D.s * (σ * t * D.s ^ N) ∧
        (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
        v.vle (σ * t * D.s ^ N) C.base.s :=
  wedhorn_834_h_struct_via_strengthened_single_f C
    (fun D hD t ht => by
      obtain ⟨hA₀_le, σ, N, f, hf_eq, h_factor, h_subset, h_T_D_in_plus,
        h_loc_bound⟩ := h_per_call D hD t ht
      exact exists_single_f_factor_carrying_refinement_at_t_via_localisation_transfer
        C D t hA₀_le σ N f hf_eq h_factor h_subset h_T_D_in_plus h_loc_bound)

/-- **T209: per-`τ` algebraic σ-clearing bridge for the single-`f` bound**.

Algebraic transitivity bridge for the Wedhorn 8.34(ii) Step-2 σ-clearing
setup. Given fixed per-`(C, D, t)` Step-2 data `σ N f` with
`f = σ * t * D.s ^ N` and the algebraic identity `C.base.s = D.s * f`,
plus a per-`(τ, w)` supplier of `w.vle 1 (algebraMap D.s)` and a
per-`(τ, w)` supplier of `¬ w.vle (algebraMap f) 0`, this theorem
produces T207's `h_per_τ_bound` shape:

* singleton bound `w.vle (algebraMap f) (algebraMap C.base.s)` —
  derived from `w.vle 1 (algebraMap D.s)` via `mul_vle_mul_left` on
  the algebraic identity `algebraMap C.base.s = algebraMap D.s *
  algebraMap f`;
* non-vanishing `¬ w.vle (algebraMap C.base.s) 0` — derived from
  `algebraMap D.s` being a unit in `Localization.Away D.s` (free, by
  `IsLocalization.map_units`) plus `¬ w.vle (algebraMap f) 0` (the
  supplier), via the prime-support argument on the prime ideal
  `w.supp`.

The σ-strict-domination witness `(w.vle σ_loc τ ∧ ¬ w.vle τ σ_loc)`
is consumed as the antecedent and forwarded to the two suppliers; the
genuine "what σ-clearing delivers" content is encapsulated in those
two suppliers. They are the precise next missing valuation/algebra
inputs along the T207 → `h_per_τ_bound` path. -/
theorem per_tau_algebraic_sigma_clearing_bridge_for_single_f_bound
    {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A] [DecidableEq A]
    (C : RationalCoveringData A) (D : RationalLocData A) (t : A)
    (σ : A) (N : ℕ) (f : A) (_hf_eq : f = σ * t * D.s ^ N)
    (h_factor : C.base.s = D.s * f)
    (T_test_loc : Finset (Localization.Away D.s))
    (σ_loc : (Localization.Away D.s)ˣ)
    (h_v_le_one_D_s :
      letI : TopologicalSpace (Localization.Away D.s) :=
        locTopology D.P D.T D.s D.hopen
      letI : PlusSubring (Localization.Away D.s) :=
        localizationAwayPlusSubring D.s
      ∀ τ ∈ T_test_loc,
        ∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
          (w.vle (σ_loc : Localization.Away D.s) τ ∧
           ¬ w.vle τ (σ_loc : Localization.Away D.s)) →
          w.vle (1 : Localization.Away D.s)
                (algebraMap A (Localization.Away D.s) D.s))
    (h_f_ne_zero :
      letI : TopologicalSpace (Localization.Away D.s) :=
        locTopology D.P D.T D.s D.hopen
      letI : PlusSubring (Localization.Away D.s) :=
        localizationAwayPlusSubring D.s
      ∀ τ ∈ T_test_loc,
        ∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
          (w.vle (σ_loc : Localization.Away D.s) τ ∧
           ¬ w.vle τ (σ_loc : Localization.Away D.s)) →
          ¬ w.vle (algebraMap A (Localization.Away D.s) f) 0) :
    letI : TopologicalSpace (Localization.Away D.s) :=
      locTopology D.P D.T D.s D.hopen
    letI : PlusSubring (Localization.Away D.s) :=
      localizationAwayPlusSubring D.s
    ∀ τ ∈ T_test_loc,
      ∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
        (w.vle (σ_loc : Localization.Away D.s) τ ∧
         ¬ w.vle τ (σ_loc : Localization.Away D.s)) →
        (∀ t' ∈ ({f} : Finset A),
          w.vle (algebraMap A (Localization.Away D.s) t')
                (algebraMap A (Localization.Away D.s) C.base.s)) ∧
        ¬ w.vle (algebraMap A (Localization.Away D.s) C.base.s) 0 := by
  letI : TopologicalSpace (Localization.Away D.s) :=
    locTopology D.P D.T D.s D.hopen
  letI : PlusSubring (Localization.Away D.s) :=
    localizationAwayPlusSubring D.s
  intro τ hτ w hw hστ
  have h_alg : algebraMap A (Localization.Away D.s) C.base.s =
      algebraMap A (Localization.Away D.s) D.s *
        algebraMap A (Localization.Away D.s) f := by
    rw [h_factor, map_mul]
  have h_D_s_unit : IsUnit (algebraMap A (Localization.Away D.s) D.s) :=
    IsLocalization.map_units (Localization.Away D.s)
      ⟨D.s, Submonoid.mem_powers D.s⟩
  refine ⟨?_, ?_⟩
  · intro t' ht'
    rw [Finset.mem_singleton] at ht'
    rw [ht', h_alg]
    have hmul := w.mul_vle_mul_left (h_v_le_one_D_s τ hτ w hw hστ)
      (algebraMap A (Localization.Away D.s) f)
    rwa [one_mul] at hmul
  · rw [h_alg]
    intro hC0
    rcases (inferInstance : w.supp.IsPrime).mem_or_mem
      ((w.mem_supp_iff _).mpr hC0) with hD | hf
    · exact not_vle_zero_of_isUnit h_D_s_unit w ((w.mem_supp_iff _).mp hD)
    · exact h_f_ne_zero τ hτ w hw hστ ((w.mem_supp_iff _).mp hf)

/-- **T209 composed bridge: per-`τ` algebraic suppliers → strengthened
single-`f` Step-2 target**.

Composes T209's per-`τ` algebraic σ-clearing bridge with T207's
`exists_single_f_factor_carrying_refinement_at_t_via_localised_sigma`
to produce T201's strengthened single-`f` target directly from the
σ-strict-domination data plus the two genuine algebraic suppliers
(`w.vle 1 (algMap D.s)` and `¬ w.vle (algMap f) 0`), bypassing
T207's compound `h_per_τ_bound`. -/
theorem exists_single_f_factor_carrying_refinement_at_t_via_per_tau_algebraic
    {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A] [DecidableEq A]
    (C : RationalCoveringData A) (D : RationalLocData A) (t : A)
    (hA₀_le : D.P.A₀ ≤ A⁺)
    (σ : A) (N : ℕ) (f : A)
    (hf_eq : f = σ * t * D.s ^ N)
    (h_factor : C.base.s = D.s * f)
    (h_subset : rationalOpen (insert f C.base.T) C.base.s ⊆
      rationalOpen D.T D.s)
    (h_T_D_in_plus : ∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A))
    (T_test_loc : Finset (Localization.Away D.s))
    (σ_loc : (Localization.Away D.s)ˣ)
    (h_sigma_loc :
      letI : TopologicalSpace (Localization.Away D.s) :=
        locTopology D.P D.T D.s D.hopen
      letI : PlusSubring (Localization.Away D.s) :=
        localizationAwayPlusSubring D.s
      ∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
        ∃ τ ∈ T_test_loc,
          w.vle (σ_loc : Localization.Away D.s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away D.s))
    (h_v_le_one_D_s :
      letI : TopologicalSpace (Localization.Away D.s) :=
        locTopology D.P D.T D.s D.hopen
      letI : PlusSubring (Localization.Away D.s) :=
        localizationAwayPlusSubring D.s
      ∀ τ ∈ T_test_loc,
        ∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
          (w.vle (σ_loc : Localization.Away D.s) τ ∧
           ¬ w.vle τ (σ_loc : Localization.Away D.s)) →
          w.vle (1 : Localization.Away D.s)
                (algebraMap A (Localization.Away D.s) D.s))
    (h_f_ne_zero :
      letI : TopologicalSpace (Localization.Away D.s) :=
        locTopology D.P D.T D.s D.hopen
      letI : PlusSubring (Localization.Away D.s) :=
        localizationAwayPlusSubring D.s
      ∀ τ ∈ T_test_loc,
        ∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
          (w.vle (σ_loc : Localization.Away D.s) τ ∧
           ¬ w.vle τ (σ_loc : Localization.Away D.s)) →
          ¬ w.vle (algebraMap A (Localization.Away D.s) f) 0) :
    exists_single_f_factor_carrying_refinement_at_t_target C D t :=
  exists_single_f_factor_carrying_refinement_at_t_via_localised_sigma
    C D t hA₀_le σ N f hf_eq h_factor h_subset h_T_D_in_plus
    T_test_loc σ_loc h_sigma_loc
    (per_tau_algebraic_sigma_clearing_bridge_for_single_f_bound
      C D t σ N f hf_eq h_factor T_test_loc σ_loc
      h_v_le_one_D_s h_f_ne_zero)

/-- **T209 end-to-end bridge: per-`τ` algebraic suppliers → `h_struct`**.

Composes the T209 strengthened-target bridge with T201's
`wedhorn_834_h_struct_via_strengthened_single_f` to produce T192/T195's
`h_struct` shape directly from per-`(D, t)` σ-strict-domination data
plus the two genuine algebraic suppliers (`w.vle 1 (algMap D.s)` and
`¬ w.vle (algMap f) 0`). -/
theorem wedhorn_834_h_struct_via_per_tau_algebraic
    {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A] [DecidableEq A]
    (C : RationalCoveringData A)
    (h_per_call :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (t : A), t ∈ D.T →
      ∃ (_hA₀_le : D.P.A₀ ≤ A⁺) (σ : A) (N : ℕ) (f : A)
        (_hf_eq : f = σ * t * D.s ^ N)
        (_h_factor : C.base.s = D.s * f)
        (_h_subset : rationalOpen (insert f C.base.T) C.base.s ⊆
          rationalOpen D.T D.s)
        (_h_T_D_in_plus : ∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A))
        (_T_test_loc : Finset (Localization.Away D.s))
        (_σ_loc : (Localization.Away D.s)ˣ),
        letI : TopologicalSpace (Localization.Away D.s) :=
          locTopology D.P D.T D.s D.hopen
        letI : PlusSubring (Localization.Away D.s) :=
          localizationAwayPlusSubring D.s
        (∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
          ∃ τ ∈ _T_test_loc,
            w.vle (_σ_loc : Localization.Away D.s) τ ∧
            ¬ w.vle τ (_σ_loc : Localization.Away D.s)) ∧
        (∀ τ ∈ _T_test_loc,
          ∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
            (w.vle (_σ_loc : Localization.Away D.s) τ ∧
             ¬ w.vle τ (_σ_loc : Localization.Away D.s)) →
            w.vle (1 : Localization.Away D.s)
                  (algebraMap A (Localization.Away D.s) D.s)) ∧
        (∀ τ ∈ _T_test_loc,
          ∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
            (w.vle (_σ_loc : Localization.Away D.s) τ ∧
             ¬ w.vle τ (_σ_loc : Localization.Away D.s)) →
            ¬ w.vle (algebraMap A (Localization.Away D.s) f) 0)) :
    ∀ (D : RationalLocData A), D ∈ C.covers →
    ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
    ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
      ∃ (σ : A) (N : ℕ),
        C.base.s = D.s * (σ * t * D.s ^ N) ∧
        (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
        v.vle (σ * t * D.s ^ N) C.base.s :=
  wedhorn_834_h_struct_via_strengthened_single_f C
    (fun D hD t ht => by
      obtain ⟨hA₀_le, σ, N, f, hf_eq, h_factor, h_subset, h_T_D_in_plus,
        T_test_loc, σ_loc, h_sigma_loc, h_v_le_one_D_s, h_f_ne_zero⟩ :=
          h_per_call D hD t ht
      exact exists_single_f_factor_carrying_refinement_at_t_via_per_tau_algebraic
        C D t hA₀_le σ N f hf_eq h_factor h_subset h_T_D_in_plus
        T_test_loc σ_loc h_sigma_loc h_v_le_one_D_s h_f_ne_zero)

/-! ## T212: post-T209 supplier audit for the per-`τ` algebraic bridge

Two suppliers were exposed by T209's
`per_tau_algebraic_sigma_clearing_bridge_for_single_f_bound`:

* `h_v_le_one_D_s` — per-`(τ, w)` supplier of
  `w.vle 1 (algebraMap A (Localization.Away D.s) D.s)`;
* `h_f_ne_zero` — per-`(τ, w)` supplier of
  `¬ w.vle (algebraMap A (Localization.Away D.s) f) 0` for
  `f = σ * t * D.s ^ N`.

T212 audits both. The conclusions are:

1. **`h_f_ne_zero` is reducible to nonvanishing of the two finite-input
   factors `σ` and `t`**, modulo the free unitness of `algebraMap D.s`
   in `Localization.Away D.s`. The reducer
   `post_T209_supplier_f_ne_zero_via_factors` discharges this from
   `¬ w.vle (algebraMap σ) 0` and `¬ w.vle (algebraMap t) 0` directly.

2. **`h_v_le_one_D_s` requires structural input not derivable from
   `localizationAwayPlusSubring D.s = image(A⁺)` alone**: under that
   placeholder plus subring, `w.vle 1 (algMap D.s)` is equivalent to
   `(algMap D.s)⁻¹ ∈ ((Loc D.s)⁺)`, i.e., to the existence of a
   plus-subring element `y` with `y * algMap D.s = 1`. The interface
   lemma `post_T209_supplier_v_le_one_D_s_via_inverse_in_plus`
   exposes this exact hypothesis. Under the current image-only plus
   subring, that hypothesis amounts to `∃ a ∈ A⁺, algMap a *
   algMap D.s = 1`, which (for a non-zero-divisor `D.s`) forces
   `D.s` to be a unit in `A` with inverse in `A⁺` — strong but
   precise. Genuinely deriving `w.vle 1 (algMap D.s)` from a Wedhorn
   8.34(ii) σ-strict-domination witness alone is the next theorem-level
   work; see the docblock above the interface lemma. -/

/-- **T212 supplier for `h_f_ne_zero` via prime-support factor decomposition**.

Given fixed `σ t : A`, `N : ℕ`, and `f : A` with `f = σ * t * D.s ^ N`,
the per-`w` non-vanishing `¬ w.vle (algebraMap A (Loc D.s) f) 0` reduces
to non-vanishing of the two scalar factors `algebraMap σ` and
`algebraMap t`, since `(algebraMap D.s) ^ N` is a unit in
`Localization.Away D.s` (free, by `IsLocalization.map_units`) and the
support of `w` is a prime ideal closed under the multiplicative
expansion of `algebraMap (σ * t * D.s ^ N) = algebraMap σ * algebraMap t
* (algebraMap D.s) ^ N`.

This produces `h_f_ne_zero` for the T209 callsite from the two minimal
non-vanishing assumptions on `σ` and `t`, leaving only those two to be
discharged by the upstream σ-clearing data.

**Reusable scope**: this is a pure prime-support / unit-power reduction
on `Loc D.s`; it does not depend on the specific `localTopology` or
plus subring. -/
theorem post_T209_supplier_f_ne_zero_via_factors
    {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A]
    (D : RationalLocData A) (σ t : A) (N : ℕ) (f : A)
    (hf_eq : f = σ * t * D.s ^ N) :
    letI : TopologicalSpace (Localization.Away D.s) :=
      locTopology D.P D.T D.s D.hopen
    letI : PlusSubring (Localization.Away D.s) :=
      localizationAwayPlusSubring D.s
    ∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
      ¬ w.vle (algebraMap A (Localization.Away D.s) σ) 0 →
      ¬ w.vle (algebraMap A (Localization.Away D.s) t) 0 →
      ¬ w.vle (algebraMap A (Localization.Away D.s) f) 0 := by
  letI : TopologicalSpace (Localization.Away D.s) :=
    locTopology D.P D.T D.s D.hopen
  letI : PlusSubring (Localization.Away D.s) :=
    localizationAwayPlusSubring D.s
  intro w _hw hσ_ne ht_ne
  letI : ValuativeRel (Localization.Away D.s) := w.toValuativeRel
  rw [hf_eq, map_mul, map_mul, map_pow]
  have h_D_s_unit : IsUnit (algebraMap A (Localization.Away D.s) D.s) :=
    IsLocalization.map_units (Localization.Away D.s)
      ⟨D.s, Submonoid.mem_powers D.s⟩
  exact ValuativeRel.zero_vlt_mul (ValuativeRel.zero_vlt_mul hσ_ne ht_ne)
    (not_vle_zero_of_isUnit (h_D_s_unit.pow N) w)

/-- **T212 per-`τ` wrapper of the `h_f_ne_zero` factor reducer**.

Specialises `post_T209_supplier_f_ne_zero_via_factors` to the per-`τ`
shape consumed by T209: every σ-strict-domination witness produces
`¬ w.vle (algebraMap A (Loc D.s) f) 0`, given non-vanishing at the two
factors `σ` and `t`. The σ-strict-domination witness is forwarded
through; the conclusion does not depend on it. -/
theorem post_T209_supplier_f_ne_zero_per_tau_via_factors
    {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A]
    (D : RationalLocData A) (σ t : A) (N : ℕ) (f : A)
    (hf_eq : f = σ * t * D.s ^ N)
    (T_test_loc : Finset (Localization.Away D.s))
    (σ_loc : (Localization.Away D.s)ˣ)
    (h_σ_ne :
      letI : TopologicalSpace (Localization.Away D.s) :=
        locTopology D.P D.T D.s D.hopen
      letI : PlusSubring (Localization.Away D.s) :=
        localizationAwayPlusSubring D.s
      ∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
        ¬ w.vle (algebraMap A (Localization.Away D.s) σ) 0)
    (h_t_ne :
      letI : TopologicalSpace (Localization.Away D.s) :=
        locTopology D.P D.T D.s D.hopen
      letI : PlusSubring (Localization.Away D.s) :=
        localizationAwayPlusSubring D.s
      ∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
        ¬ w.vle (algebraMap A (Localization.Away D.s) t) 0) :
    letI : TopologicalSpace (Localization.Away D.s) :=
      locTopology D.P D.T D.s D.hopen
    letI : PlusSubring (Localization.Away D.s) :=
      localizationAwayPlusSubring D.s
    ∀ τ ∈ T_test_loc,
      ∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
        (w.vle (σ_loc : Localization.Away D.s) τ ∧
         ¬ w.vle τ (σ_loc : Localization.Away D.s)) →
        ¬ w.vle (algebraMap A (Localization.Away D.s) f) 0 := by
  letI : TopologicalSpace (Localization.Away D.s) :=
    locTopology D.P D.T D.s D.hopen
  letI : PlusSubring (Localization.Away D.s) :=
    localizationAwayPlusSubring D.s
  intro _τ _hτ w hw _hστ
  exact post_T209_supplier_f_ne_zero_via_factors D σ t N f hf_eq w hw
    (h_σ_ne w hw) (h_t_ne w hw)

/-- **T212 interface lemma for `h_v_le_one_D_s` via inverse-in-plus**.

Characterizes `w.vle 1 (algebraMap A (Loc D.s) D.s)` for
`w ∈ Spa(Loc D.s, ⁺)`: it is implied by the existence of a plus-subring
element `y` in `(Loc D.s)⁺` with `y * algebraMap D.s = 1`, i.e., by
`(algebraMap D.s)⁻¹ ∈ (Loc D.s)⁺`.

**Math**: for `w ∈ Spa(Loc D.s, ⁺)` and `y ∈ ⁺`, we have
`w.vle y 1` (`v(y) ≤ 1`) by `vle_one_of_mem_spa`. Multiplying through by
`algebraMap D.s` via `mul_vle_mul_left`:

  `v(y * algebraMap D.s) ≤ v(1 * algebraMap D.s) = v(algebraMap D.s)`,

and `y * algebraMap D.s = 1` rewrites the LHS to `v(1)`. Hence
`v(1) ≤ v(algebraMap D.s)`, i.e., `w.vle 1 (algebraMap D.s)`.

**Status of the hypothesis**: under the current placeholder plus
subring `localizationAwayPlusSubring D.s = image (A⁺)`, the existence
of `y ∈ image(A⁺)` with `y * algebraMap D.s = 1` is equivalent (for a
non-zero-divisor `D.s`) to the existence of `a ∈ A⁺` with
`a * D.s = 1` in `A`, i.e., `D.s` is a unit in `A` with inverse in
`A⁺`. **In the typical Wedhorn 8.34(ii) Step-2 setting, this fails:
`D.s` is a denominator of a rational subset `R(D.T, D.s)` and is
generally not a unit in `A⁺` (much less in `A`).**

Therefore, deriving `h_v_le_one_D_s` from σ-strict-domination data on
`Spa(Loc D.s, ⁺)` requires either:

* **A finer plus subring** on `Loc D.s` than the image of `A⁺`
  (e.g., `localizationLocSubringPlusSubring`, the integral closure of
  `A⁺[D.T / D.s]` in `Loc D.s`), under which `(algMap D.s)⁻¹ ∈ ⁺`
  becomes natural; OR

* **A different valuation-arithmetic route** that bypasses
  `w.vle 1 (algMap D.s)` and derives `w.vle (algMap f) (algMap C.base.s)`
  directly from σ-strict-domination on `f` (e.g., via an explicit
  factorization using both σ-strict-dom and the rational-open
  condition `v(t) ≤ v(D.s)` for `v ∈ R(D.T, D.s)`).

Either route is theorem-level Wedhorn content. This interface lemma
makes the structural premise explicit so the consumer can supply it
once the appropriate plus subring or factorization has been built. -/
theorem post_T209_supplier_v_le_one_D_s_via_inverse_in_plus
    {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A]
    (D : RationalLocData A)
    (h_inv_mem :
      letI : TopologicalSpace (Localization.Away D.s) :=
        locTopology D.P D.T D.s D.hopen
      letI : PlusSubring (Localization.Away D.s) :=
        localizationAwayPlusSubring D.s
      ∃ y ∈ ((Localization.Away D.s)⁺ : Subring (Localization.Away D.s)),
        y * algebraMap A (Localization.Away D.s) D.s = 1) :
    letI : TopologicalSpace (Localization.Away D.s) :=
      locTopology D.P D.T D.s D.hopen
    letI : PlusSubring (Localization.Away D.s) :=
      localizationAwayPlusSubring D.s
    ∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
      w.vle (1 : Localization.Away D.s)
            (algebraMap A (Localization.Away D.s) D.s) := by
  letI : TopologicalSpace (Localization.Away D.s) :=
    locTopology D.P D.T D.s D.hopen
  letI : PlusSubring (Localization.Away D.s) :=
    localizationAwayPlusSubring D.s
  intro w hw
  obtain ⟨y, hy_plus, hy_inv⟩ := h_inv_mem
  have h := w.mul_vle_mul_left (vle_one_of_mem_spa hw hy_plus)
    (algebraMap A (Localization.Away D.s) D.s)
  rwa [hy_inv, one_mul] at h

/-- **T212 per-`τ` wrapper of the `h_v_le_one_D_s` interface lemma**.

Specialises `post_T209_supplier_v_le_one_D_s_via_inverse_in_plus` to
the per-`τ` shape consumed by T209. The σ-strict-domination witness is
forwarded through; the conclusion does not depend on it. -/
theorem post_T209_supplier_v_le_one_D_s_per_tau_via_inverse_in_plus
    {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A]
    (D : RationalLocData A)
    (T_test_loc : Finset (Localization.Away D.s))
    (σ_loc : (Localization.Away D.s)ˣ)
    (h_inv_mem :
      letI : TopologicalSpace (Localization.Away D.s) :=
        locTopology D.P D.T D.s D.hopen
      letI : PlusSubring (Localization.Away D.s) :=
        localizationAwayPlusSubring D.s
      ∃ y ∈ ((Localization.Away D.s)⁺ : Subring (Localization.Away D.s)),
        y * algebraMap A (Localization.Away D.s) D.s = 1) :
    letI : TopologicalSpace (Localization.Away D.s) :=
      locTopology D.P D.T D.s D.hopen
    letI : PlusSubring (Localization.Away D.s) :=
      localizationAwayPlusSubring D.s
    ∀ τ ∈ T_test_loc,
      ∀ w ∈ Spa (Localization.Away D.s) (Localization.Away D.s)⁺,
        (w.vle (σ_loc : Localization.Away D.s) τ ∧
         ¬ w.vle τ (σ_loc : Localization.Away D.s)) →
        w.vle (1 : Localization.Away D.s)
              (algebraMap A (Localization.Away D.s) D.s) := by
  letI : TopologicalSpace (Localization.Away D.s) :=
    locTopology D.P D.T D.s D.hopen
  letI : PlusSubring (Localization.Away D.s) :=
    localizationAwayPlusSubring D.s
  intro _τ _hτ w hw _hστ
  exact post_T209_supplier_v_le_one_D_s_via_inverse_in_plus D h_inv_mem w hw

end ValuationSpectrum

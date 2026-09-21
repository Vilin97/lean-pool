/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Cor732
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Presheaf
import LeanPool.UniformSheafyTateDomains.AdicSpaces.RationalSubsets
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalizationTransferConsumer
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornSpaRationalOpenLiftWrapper

/-!
# Wedhorn multi-element dominating-unit step (smallest reusable lemmas)

Building blocks toward the **multi-element σ-clearing lemma** identified
as the residual blocker of `WedhornStandardCoverRefinement.lean`'s
`exists_single_f_refinement_at_t_via_dominating_unit` target signature.

## API audit (state of the repository as of this file)

### Cor 7.32 output shape (the σ supplier)

```
ValuationSpectrum.exists_dominating_unit
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, ...)
    (T : Finset A)
    (hT : ∀ v ∈ Spa A A⁺, ∃ t ∈ T, ¬ v.vle t 0) :
    ∃ s : Aˣ, ∀ v ∈ Spa A A⁺, ∃ t ∈ T,
      v.vle (s : A) t ∧ ¬ v.vle t (s : A)
```
(`Adic spaces/Cor732.lean:206`).

The **strict-dominance pair** `v.vle (s : A) t ∧ ¬ v.vle t (s : A)` is
the key per-Spa-point output to be transferred into the multi-`t'`
inequality at every plus-piece point.

### Available valuation-inequality API

* `Spv.mul_vle_mul_left`, `Spv.vle_mul_cancel`
  (`Adic spaces/ValuationSpectrum.lean:63-65`) — single-multiplication
  cancellation at units.
* `ValuativeRel.mul_vle_mul` — bilinear product propagation
  `(x ≤ᵥ y → x' ≤ᵥ y' → x*x' ≤ᵥ y*y')` (Mathlib).
* `ValuativeRel.mul_vle_mul_iff_left` — iff form of cancellation at a
  non-zero element (Mathlib).
* `ValuativeRel.pow_vle_pow` — power propagation
  `(a ≤ᵥ b → ∀ n, a^n ≤ᵥ b^n)` (Mathlib).
* `ValuativeRel.not_vle_zero_of_isUnit` — units are non-zero in
  valuation (Mathlib via `Adic spaces/ValuationSpectrum.lean:224`).

### Missing (this file lands the first piece)

* **Finset.prod propagation in Spv form** — landed below as
  `Spv.vle_prod_of_pointwise`. This is the smallest reusable building
  block needed to package multi-element products `∏ t ∈ T, x t` under
  pointwise `vle`-bounds, which the Wedhorn σ-clearing uses to bound
  `w(∏ t ∈ D.T, t) ≤ w(D.s ^ |D.T|)` from per-`t` bounds
  `w.vle t D.s`.

* **Strict σ-dominance + finite-product transfer** — the genuinely
  new content. Documented as the missing target signature
  `rationalOpen_subset_via_strict_sigma_domination` at the end of this
  file; the proof requires a non-trivial case analysis on which
  `τ ∈ T_test` wins σ-domination at each `w` and is the next concrete
  formalisation target.

## What this file provides

1. `Spv.vle_prod_of_pointwise` — pointwise-`vle` to product-`vle` for
   any indexed family over a `Finset`. Proved by `Finset.induction_on`
   using `ValuativeRel.mul_vle_mul`. Generic / reusable.

2. Documented target signature
   (`rationalOpen_subset_via_strict_sigma_domination`) for the
   full multi-element σ-clearing lemma — the next missing layer
   above `Spv.vle_prod_of_pointwise`.

No Lane B / Cor 8.32 / Jacobson / faithful-flatness / T001 content.
No new final acyclicity hypotheses. Strict adherence to the Wedhorn
8.34(ii) σ-domination route. -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-- **Finset.prod monotonicity for valuations (Spv form)**.

For any indexed family `x, y : α → A` and a finite index set `T`, if
`v.vle (x t) (y t)` holds pointwise for every `t ∈ T`, then the product
inequality `v.vle (∏ t ∈ T, x t) (∏ t ∈ T, y t)` holds.

**Use case**: in the Wedhorn σ-clearing argument, this lemma packages
per-`t` valuation bounds `w.vle t D.s` (for `t ∈ D.T`) into the global
product bound `w.vle (∏ t ∈ D.T, t) (∏ t ∈ D.T, D.s) = w.vle (∏ t,
t) (D.s ^ |D.T|)` (after rewriting the constant product by power), which
is one half of the algebraic core of the multi-element σ-clearing step.

**Proof**: `Finset.induction_on` using `ValuativeRel.mul_vle_mul`
(bilinear propagation) and `vle_total 1 1` for the empty base case. -/
lemma Spv.vle_prod_of_pointwise
    {α : Type*} (v : Spv A) (T : Finset α) {x y : α → A}
    (h : ∀ t ∈ T, v.vle (x t) (y t)) :
    v.vle (∏ t ∈ T, x t) (∏ t ∈ T, y t) := by
  classical
  letI : ValuativeRel A := v.toValuativeRel
  induction T using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty] using (v.vle_total 1 1).elim id id
  | insert a T' ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact ValuativeRel.mul_vle_mul (h a (Finset.mem_insert_self a T'))
      (ih (fun t ht => h t (Finset.mem_insert_of_mem ht)))

/-- **Logical reducer: rational-open containment from `T_test`-compatibility
of σ-strict-domination**.

This is the **callsite shape** of the multi-element σ-clearing step: it
takes Cor 7.32-style σ-domination of a test family `T_test` plus an
**explicit τ-case-analysis hypothesis** `hT_test_compat` and produces
the rational-open subset conclusion

```
R(insert ((σ : A) * (∏ t ∈ D.T, t)) C.base.T, C.base.s) ⊆ R(D.T, D.s)
```

for arbitrary finite `D.T`. The reducer itself contains no genuinely
new Wedhorn content: it is purely the logical step from the per-Spa-point
existential `hσ` plus the per-τ algebraic transfer `hT_test_compat` to
the membership-of-rational-open conclusion at every `w` in the LHS
plus-piece.

**The genuine Wedhorn 8.34(ii) content** is now isolated as the
discharge of `hT_test_compat` for a specific test family `T_test`. The
canonical Wedhorn choice — `T_test := D.T.image (· * C.base.s) ∪ {D.s}`
with the power-product f-shape `(σ : A) * (∏ t ∈ D.T, t) * D.s ^ N` —
is the next concrete formalisation target; the present reducer fixes
the callsite shape so that the τ-case-analysis discharge can be
attempted in isolation. Detailed obligation pinned in the docblock at
the end of this file.

**Proof**: pointwise on the LHS plus-piece: extract the `f`-membership
inequality from the `insert`-clause, apply `hσ` at `w` to pick a
witness `τ`, then apply `hT_test_compat` at `τ` to extract the per-`t'`
inequalities and non-degeneracy clause comprising the RHS rational-open
membership. -/
theorem rationalOpen_subset_via_strict_sigma_domination
    [DecidableEq A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] (C : RationalCoveringData A) (D : RationalLocData A)
    (σ : Aˣ) (T_test : Finset A)
    (hσ : ∀ w ∈ Spa A A⁺, ∃ τ ∈ T_test,
      w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A))
    (hT_test_compat : ∀ τ ∈ T_test, ∀ w ∈ Spa A A⁺,
      w.vle ((σ : A) * (∏ t ∈ D.T, t)) C.base.s →
      (w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A)) →
        (∀ t' ∈ D.T, w.vle t' D.s) ∧ ¬ w.vle D.s 0) :
    rationalOpen (insert ((σ : A) * (∏ t ∈ D.T, t)) C.base.T) C.base.s ⊆
      rationalOpen D.T D.s := by
  intro w hw
  obtain ⟨hw_spa, hwIns, _hwCs⟩ := hw
  -- Extract f-membership at w from the `insert`-clause.
  have hw_f : w.vle ((σ : A) * (∏ t ∈ D.T, t)) C.base.s :=
    hwIns _ (Finset.mem_insert_self _ _)
  -- Apply σ-domination at w to pick the witnessing τ.
  obtain ⟨τ, hτ_mem, hστ⟩ := hσ w hw_spa
  -- Apply the τ-case-analysis hypothesis to extract D.T inequalities + non-degeneracy.
  exact ⟨hw_spa, hT_test_compat τ hτ_mem w hw_spa hw_f hστ⟩

/-- **Strict-domination forces non-degeneracy** (smallest valuation
arithmetic helper toward multi-element σ-clearing).

For any `w : Spv A` and any `x, y : A`, if `w` strictly dominates
`x` by `y` (i.e., `¬ w.vle x y`), then `x` is non-degenerate at `w`
(`¬ w.vle x 0`).

**Proof (contrapositive)**: if `w.vle x 0`, then by `≤ᵥ` transitivity
against the always-true `0 ≤ᵥ y` (i.e., `ValuativeRel.zero_vle`), we
get `w.vle x y`, contradicting the strict hypothesis.

**Use case in σ-clearing**: Cor 7.32's σ-strict-domination output
`w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A)` produces `¬ w.vle τ (σ : A)`,
which by this lemma yields `¬ w.vle τ 0` — i.e., `τ` is non-degenerate
at `w`. With `τ := D.s` (when `D.s ∈ T_test` is the σ-witness at `w`),
this discharges the **non-degeneracy half** of the multi-element
σ-clearing conjunction `(∀ t' ∈ D.T, w.vle t' D.s) ∧ ¬ w.vle D.s 0`. -/
lemma not_vle_zero_of_strict_dominator
    {w : Spv A} {x y : A} (h_strict : ¬ w.vle x y) :
    ¬ w.vle x 0 :=
  fun hw_x0 => h_strict (w.vle_trans hw_x0 (w.zero_vle y))

/-- **Discharge of `hT_test_compat` for the empty `D.T` case** with
`T_test := {D.s}`.

The `D.T = ∅` case is the simplest non-trivial cover-piece shape: it
captures basic-open-at-`D.s` cover pieces `D` with no test elements.
The conjunction `(∀ t' ∈ ∅, ...) ∧ ¬ w.vle D.s 0` reduces to just
`¬ w.vle D.s 0`, which is discharged by `not_vle_zero_of_strict_dominator`
applied to the σ-strict-domination by `D.s`.

**Plug-in callsite**: feed this into `rationalOpen_subset_via_strict_sigma_domination`
with `T_test := {D.s}` to obtain
```
rationalOpen (insert (σ : A) C.base.T) C.base.s ⊆ rationalOpen ∅ D.s
```
(noting `(σ : A) * (∏ t ∈ ∅, t) = (σ : A)` after `Finset.prod_empty`).

The σ supplier is `Cor732.exists_dominating_unit` applied to
`T := {D.s}`, requiring the no-common-zero hypothesis
`∀ v ∈ Spa A A⁺, ¬ v.vle D.s 0` (a non-degeneracy precondition on the
cover-piece denominator that holds when the cover is non-trivially
contained in the basic open at `D.s`). -/
lemma hT_test_compat_of_empty_D_T
    [DecidableEq A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] (C : RationalCoveringData A) (D : RationalLocData A)
    (hD_empty : D.T = ∅) (σ : Aˣ) :
    ∀ τ ∈ ({D.s} : Finset A), ∀ w ∈ Spa A A⁺,
      w.vle ((σ : A) * (∏ t ∈ D.T, t)) C.base.s →
      (w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A)) →
        (∀ t' ∈ D.T, w.vle t' D.s) ∧ ¬ w.vle D.s 0 := by
  intro τ hτ w _hw_spa _hw_f hστ
  obtain rfl := Finset.mem_singleton.mp hτ
  exact ⟨fun t' ht' => absurd (hD_empty ▸ ht') (Finset.notMem_empty t'),
    not_vle_zero_of_strict_dominator hστ.2⟩

/-! ## Remaining obligation: per-`t'` inequalities for arbitrary `D.T`

### Status of the canonical T_test choice (CORRECTED)

The earlier docblock proposed `T_test := D.T.image (· * C.base.s) ∪
{D.s * C.base.s}` as a "canonical choice" that would discharge
`hT_test_compat` uniformly. **This choice does not work** for the
per-`t'` half of the conjunction:

* In the case `τ = t₀ * C.base.s` for `t₀ ∈ D.T`, σ-strict-domination
  gives only `w(σ) ≤ w(t₀) * w(C.base.s)` — i.e., information about a
  single `t₀`, not all `t' ∈ D.T`. There is no algebraic route from
  this single-`t₀` bound and the f-membership to the uniform per-`t'`
  conclusion `∀ t' ∈ D.T, w.vle t' D.s`.

* In the case `τ = D.s * C.base.s`, σ-strict-domination gives
  `w(σ) ≤ w(D.s) * w(C.base.s)`. Combined with the f-membership
  `w(σ) * (∏ t ∈ D.T, w(t)) ≤ w(C.base.s)`, one cannot derive
  `w(t') ≤ w(D.s)` without additional information about
  `w(C.base.s) / (w(σ) * ∏_{t ≠ t'} w(t))` versus `w(D.s)`.

The genuine Wedhorn 8.34(ii) approach almost certainly requires
**pre-localisation at `C.base.s`** (treating `R(C.base.T, C.base.s)`
as a Spa over a localised ring `A_loc`) so that the σ-construction
operates on the localised space rather than `Spa A A⁺` directly. This
is structural, not a simple test-family-choice question.

### What this file currently provides

* `not_vle_zero_of_strict_dominator` — generic helper extracting
  non-degeneracy from a strict `≤ᵥ` inequality. Single-line proof via
  `vle_trans` against `zero_vle`.

* `hT_test_compat_of_empty_D_T` — concrete discharge of `hT_test_compat`
  in the trivial `D.T = ∅` case (basic-open-at-`D.s` cover pieces),
  using `T_test := {D.s}`. Plugged into
  `rationalOpen_subset_via_strict_sigma_domination`, this discharges
  the C1 single-`f` containment for the `D.T = ∅` subcase.

### Smallest missing valuation arithmetic lemma

The remaining obligation — the per-`t'` inequality discharge for
`|D.T| ≥ 1` — admits TWO possible routes; both are open:

**Route A (direct, valuation arithmetic only)**: identify a test family
`T_test` and an f-shape `f := σ * (something involving D.T, D.s,
C.base.s, exponents)` such that, at every `w ∈ Spa A A⁺`, the
combination of f-membership and σ-strict-domination by some `τ ∈ T_test`
forces `w.vle t' D.s` for every `t' ∈ D.T`. **This appears to fail**
under the natural canonical choices (see analysis above) and likely
requires a non-uniform (per-`w`) argument outside the scope of the
present `hT_test_compat` shape.

**Route B (structural / pre-localisation)**: pre-localise `A` at
`C.base.s` to obtain `A_loc`, then apply Cor 7.32 / σ-construction
inside `Spa(A_loc, A_loc⁺)`. The standard Wedhorn 8.34(ii) proof
follows this route. The smallest missing lemma is then a **transfer
lemma** `rationalOpen_subset_localisation_transfer` between
rational opens of `A` and `A_loc` along the localisation map; its
precise signature involves the `Localization.Away C.base.s` ring
structure plus the comap behaviour of Spa-points across this map.

### Status

* The reducer `rationalOpen_subset_via_strict_sigma_domination` provides
  the right **callsite shape** for either route.
* The `D.T = ∅` discharge above is a concrete sanity-check that the
  reducer integrates correctly with the σ-strict-domination output.
* The `|D.T| ≥ 1` per-`t'` discharge remains the genuine Wedhorn
  content; the present file does not claim a "canonical choice" without
  a verified discharge.

### Why this is still Wedhorn-route

No faithful-flatness / Cor 8.32 / Jacobson / T001 content is invoked
anywhere in this file. The framework is purely Wedhorn 8.34(ii) /
Cor 7.32 σ-domination. -/

/-! ### T202: rational-open subset-form localisation transfer

Route B support: a subset-style transfer along
`comap (algebraMap A (Localization.Away C.base.s))` that takes
**uniform bounds on the localised Spa** and produces **per-`v`
membership in the original `rationalOpen T' s'` on `Spa A A⁺`** via
comap.

This is the natural Step-2 entry point for the pre-localisation
σ-clearing route: produce σ-data on `Spa(Localization.Away s, ⁺)`
(where `s = C.base.s` is invertible, so the test family choice is
unconstrained), then transfer back to `Spa A A⁺` via comap.

**API used**: `rationalOpen_transfer_via_localization` (in
`WedhornLocalizationTransferConsumer.lean`). The new T202 lemma is the
**one-direction subset packaging** of the existing iff: from per-`w`
boundedness on Loc-Spa, produce per-`comap-w` membership on A-Spa.

Limitations: this transfers conditions FROM `Spa(Loc s, ⁺)` to the
**comap-image** in `Spa A A⁺`. The converse direction (lifting
`v ∈ rationalOpen T s` on A-Spa to `w ∈ Spa(Loc, ⁺)` with
`comap w = v`) is the **Spa-point lift**, a separate genuine missing
API; documented at the end of this section. -/

/-- **T202 rational-open subset-form localisation transfer**.

From per-`w` bounded behavior on `Spa(Localization.Away s, ⁺)`,
produces per-`comap-w` membership in `rationalOpen T' s'` on
`Spa A A⁺`.

**Inputs**:
* `(P, T, s, hopen)` — the standard `locTopology` / `locSubring` data.
* `(T', s')` — the target rational-open's data (typically `T_D` and
  `D.s` for the Step-2 `D ∈ C.covers` case).
* `h_loc_bound` — per-`w` boundedness on `Spa(Loc s, ⁺)`: at every
  `w` in the localised Spa, the per-`t ∈ T'` inequality
  `w.vle (algebraMap t) (algebraMap s')` and denominator
  non-vanishing `¬ w.vle (algebraMap s') 0` hold.

**Output**: per-`w`, the comap `comap (algebraMap A (Loc s)) w` lies
in `rationalOpen T' s'` on `Spa A A⁺`.

**Proof**: direct application of
`rationalOpen_transfer_via_localization`'s `.mpr` direction, fed by
`h_loc_bound`.

**Use case**: Step-2 σ-clearing route. After producing σ-strict-dom
output on `Spa(Loc s, ⁺)` via Cor 7.32, transfer the resulting per-`t'`
bounds back to `Spa A A⁺` via comap, yielding the per-`t'` inequalities
needed to discharge `hT_test_compat`. -/
theorem rationalOpen_subset_localisation_transfer
    [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T' : Finset A) (s' : A)
    (h_loc_bound :
      letI : TopologicalSpace (Localization.Away s) :=
        locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationAwayPlusSubring s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        (∀ t ∈ T', w.vle (algebraMap A (Localization.Away s) t)
          (algebraMap A (Localization.Away s) s')) ∧
        ¬ w.vle (algebraMap A (Localization.Away s) s') 0) :
    letI : TopologicalSpace (Localization.Away s) :=
      locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationAwayPlusSubring s
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      comap (algebraMap A (Localization.Away s)) w ∈
        rationalOpen T' s' := by
  letI : TopologicalSpace (Localization.Away s) :=
    locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationAwayPlusSubring s
  intro w hw
  exact (rationalOpen_transfer_via_localization P T s hopen T' s' hw).mpr
    (h_loc_bound w hw)

/-! ### T203: Spa-point lift across `algebraMap A (Localization.Away s)`

The converse direction of T202: from `v ∈ rationalOpen T s` on
`Spa A A⁺`, construct `w ∈ Spa(Localization.Away s, (Loc s)⁺)` with
`comap (algebraMap A _) w = v`.

**Mathematical content**: at `v` with `¬ v.vle s 0`, the valuation `v`
extends uniquely to `Localization.Away s` by `w(a/s^n) := v(a)/v(s)^n`,
which is well-defined since `v(s) ≠ 0`. The continuity + plus-bound
conditions for `w ∈ Spa(Loc s, ⁺)` follow from the `locTopology` and
`localizationAwayPlusSubring` constructions.

**Discharge**: the supporting layers
* `Spv.localizationLift` + `Spv.comap_localizationLift`
  (`Adic spaces/ValuationSpectrum.lean`) — the Spv-level lift and
  comap identity.
* `extendToLocalization_le_one_of_locSubring`
  (`WedhornExtendValuationContinuity.lean:85`) — plus-bound on the
  extended valuation.
* `localizationLift_isContinuous_locTopology_of_bounded`
  (`WedhornLocalizationLiftContinuityBounded.lean:92`) — continuity.
* `valuationLocalizationLift_of_bounded`
  (`WedhornLocalizationLiftContinuityBounded.lean:149`) — packaged lift
  + comap identity from the three boundedness conditions
  `(hν_A₀, hv_T, hvs)`.
* `valuationLocalizationLift_of_spa_rationalOpen`
  (`WedhornSpaRationalOpenLiftWrapper.lean:68`) — discharges
  `(hν_A₀, hv_T, hvs)` from a single `v ∈ rationalOpen T s` together
  with the standard direction `hA₀_le : P.A₀ ≤ A⁺`.

T203 below is the **callsite-shaped exit form**: it threads the
existing wrapper through and re-presents the conclusion under the
canonical `localizationAwayPlusSubring s` `PlusSubring` instance, so
downstream consumers can use the `(Localization.Away s)⁺` notation.

The T203 lift composes with `rationalOpen_subset_localisation_transfer`
(T202, backward at the σ-clearing conclusion) to give the standard
Wedhorn 8.34(ii) Step-2 σ-clearing route:
1. start at `v ∈ rationalOpen` on `Spa A A⁺`,
2. T203 lifts `v` to `w ∈ Spa(Loc s, ⁺)`,
3. run Cor 7.32 / σ-construction inside `Spa(Loc s, ⁺)`,
4. T202 transfers the σ-clearing output back to `Spa A A⁺`. -/

/-- **T203 Spa-point lift**: every `v ∈ rationalOpen T s` lifts to a
`w ∈ Spa(Localization.Away s, (Localization.Away s)⁺)` with
`comap (algebraMap A _) w = v`.

**Inputs**:
* `(P, T, s, hopen)` — the standard `locTopology` / `locSubring` data.
* `hA₀_le : P.A₀ ≤ A⁺` — the standard pair-of-definition direction
  (used to bound `v` on `P.A₀` via `vle_one_of_mem_spa`).
* `hv : v ∈ rationalOpen T s` — Spa-membership in the rational open;
  unpacks to `(v ∈ Spa A A⁺) ∧ (∀ t ∈ T, v.vle t s) ∧ ¬ v.vle s 0`.

**Output**: existence of `w ∈ Spa(Localization.Away s, (Loc s)⁺)`
under the canonical `localizationAwayPlusSubring s` plus-subring with
`comap (algebraMap A _) w = v`.

**Proof**: direct application of
`valuationLocalizationLift_of_spa_rationalOpen` from
`WedhornSpaRationalOpenLiftWrapper.lean`. -/
theorem exists_localization_lift_of_rationalOpen
    [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (hA₀_le : P.A₀ ≤ A⁺)
    {v : Spv A} (hv : v ∈ rationalOpen T s) :
    letI : TopologicalSpace (Localization.Away s) :=
      locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationAwayPlusSubring s
    ∃ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      comap (algebraMap A (Localization.Away s)) w = v := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) := localizationAwayPlusSubring s
  exact valuationLocalizationLift_of_spa_rationalOpen P T s hopen hA₀_le hv

/-! ### T205: localised σ-clearing support for T202 `h_loc_bound`

T202 (`rationalOpen_subset_localisation_transfer`) requires
`h_loc_bound`: a per-`w` boundedness hypothesis on
`Spa(Localization.Away s, ⁺)` of shape

```
∀ w ∈ Spa (Loc s) (Loc s)⁺,
  (∀ t ∈ T', w.vle (algebraMap A (Loc s) t) (algebraMap A (Loc s) s')) ∧
  ¬ w.vle (algebraMap A (Loc s) s') 0
```

The natural Wedhorn 8.34(ii) Step-2 supplier of `h_loc_bound` is a
**localised Cor 7.32-style σ-strict-domination output** on
`Spa(Loc s, ⁺)`:

```
∃ σ_loc : (Loc s)ˣ, ∀ w ∈ Spa(Loc s, ⁺), ∃ τ ∈ T_test_loc,
  w.vle (σ_loc : Loc s) τ ∧ ¬ w.vle τ (σ_loc : Loc s)
```

plus a **per-`τ` algebraic bridge** that converts the strict-dom
witness at each `w` to the algebraMap-image bounds for the target
rational-open data `(T', s')` on `A`.

T205 below packages the smallest reducer that **composes** these two
hypotheses to produce `h_loc_bound` directly. The reducer is a clean
∃-elim composition; the genuine Wedhorn σ-clearing math sits in the
discharge of the per-`τ` bridge, which is the Step-2 integration
target owned by T204 (`Adic spaces/WedhornStandardCoverRefinement.lean`).

**Missing-input signature** (the localised Cor 7.32 supplier):

```
ValuationSpectrum.exists_dominating_unit_localised
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    [...localised PairOfDefinition + π + Archimedean data on Loc s...]
    (T_test_loc : Finset (Localization.Away s))
    (h_no_zero_loc :
      letI : TopologicalSpace (Localization.Away s) :=
        locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationAwayPlusSubring s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ T_test_loc, ¬ w.vle τ 0) :
    letI : TopologicalSpace (Localization.Away s) :=
      locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationAwayPlusSubring s
    ∃ σ_loc : (Localization.Away s)ˣ,
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ T_test_loc,
          w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s)
```

This is the **localised analogue of `Cor732.exists_dominating_unit`**
(`Adic spaces/Cor732.lean:206`) and is the precise missing input that
would feed T205's `h_sigma_loc` from algebraic data on `A`. Producing
it requires either:
* a localised PairOfDefinition + Archimedean data on `Loc s` (allowing
  direct application of `Cor732.exists_dominating_unit` to `Loc s`), or
* a transfer construction lifting `Cor732`'s output on `Spa A A⁺` to
  `Spa(Loc s, ⁺)` along the comap.

T205 below treats the σ-strict-dom on `Spa(Loc s, ⁺)` as a black-box
hypothesis, leaving the supplier construction to a downstream ticket. -/

/-- **T205 localised σ-clearing reducer to T202 `h_loc_bound`**.

Composes a localised Cor 7.32-style σ-strict-domination output on
`Spa(Localization.Away s, ⁺)` with a per-`τ` algebraic bridge to
produce the `h_loc_bound` per-`w` boundedness shape required as input
to T202's `rationalOpen_subset_localisation_transfer`.

**Inputs**:
* `(P, T, s, hopen)` — the standard `locTopology` / `locSubring` data.
* `(T', s')` — the target rational-open's data on `A`.
* `(T_test_loc, σ_loc)` — finite test family on `Localization.Away s`
  and a unit `σ_loc : (Loc s)ˣ`.
* `h_sigma_loc` — Cor 7.32-shape σ-strict-domination on
  `Spa(Loc s, ⁺)`: at every `w`, some `τ ∈ T_test_loc` satisfies
  `w.vle σ_loc τ ∧ ¬ w.vle τ σ_loc`. (See section docstring above for
  the precise signature of the supplier; this is the
  `exists_dominating_unit_localised` missing input.)
* `h_per_τ_bound` — per-`τ` algebraic transfer: at every `w` with
  σ-strict-dom witness `τ`, the algebraMap-image bounds for `(T', s')`
  hold. (This is the genuine Wedhorn 8.34(ii) σ-clearing math, owned
  by T204 in `WedhornStandardCoverRefinement.lean`.)

**Output**: exactly T202's `h_loc_bound` per-`w` boundedness shape for
`(T', s')` on `Spa(Loc s, ⁺)`.

**Proof**: per-`w`, ∃-elim on `h_sigma_loc` to obtain a witnessing
`τ ∈ T_test_loc`, then apply `h_per_τ_bound`.

**Use in Step-2 (T204 integration)**: after lifting `v ∈ rationalOpen
T s` to `w ∈ Spa(Loc s, ⁺)` via T203, the σ-clearing argument runs on
`Spa(Loc s, ⁺)`. T205 packages its output as `h_loc_bound`, and T202
transfers the resulting `(T', s')` membership back to `Spa A A⁺` along
the comap. -/
theorem localised_sigma_clearing_bounds_for_localisation_transfer
    [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T' : Finset A) (s' : A)
    (T_test_loc : Finset (Localization.Away s))
    (σ_loc : (Localization.Away s)ˣ)
    (h_sigma_loc :
      letI : TopologicalSpace (Localization.Away s) :=
        locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationAwayPlusSubring s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ T_test_loc,
          w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s))
    (h_per_τ_bound :
      letI : TopologicalSpace (Localization.Away s) :=
        locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationAwayPlusSubring s
      ∀ τ ∈ T_test_loc,
        ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
          (w.vle (σ_loc : Localization.Away s) τ ∧
           ¬ w.vle τ (σ_loc : Localization.Away s)) →
          (∀ t ∈ T', w.vle (algebraMap A (Localization.Away s) t)
            (algebraMap A (Localization.Away s) s')) ∧
          ¬ w.vle (algebraMap A (Localization.Away s) s') 0) :
    letI : TopologicalSpace (Localization.Away s) :=
      locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationAwayPlusSubring s
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      (∀ t ∈ T', w.vle (algebraMap A (Localization.Away s) t)
        (algebraMap A (Localization.Away s) s')) ∧
      ¬ w.vle (algebraMap A (Localization.Away s) s') 0 := by
  letI : TopologicalSpace (Localization.Away s) :=
    locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationAwayPlusSubring s
  intro w hw
  obtain ⟨τ, hτ_mem, hστ⟩ := h_sigma_loc w hw
  exact h_per_τ_bound τ hτ_mem w hw hστ

/-! ### T206: localised Cor 7.32 dominating-unit supplier

T205 (above) consumes a localised σ-strict-domination output as a
black-box hypothesis. T206 below is the **supplier** of that output:
a thin wrapper that applies `Cor732.exists_dominating_unit` to
`Localization.Away s` under `locTopology P T s hopen` and
`localizationAwayPlusSubring s`, given the localised analogues of
Cor 7.32's algebraic preconditions on `Loc s`.

**Strategy — direct application of the abstract Cor 7.32**:

`ValuationSpectrum.exists_dominating_unit`
(`Adic spaces/Cor732.lean:206`) is stated abstractly for any ring
`A` with `[CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
[PlusSubring A]` (`[IsLinearTopology A A]` is omitted in the theorem
statement). Substituting `A := Localization.Away s`:

* `[CommRing (Localization.Away s)]` — Mathlib's `Localization`
  instance.
* `[TopologicalSpace (Localization.Away s)]` — supplied by `letI :=
  locTopology P T s hopen`.
* `[IsTopologicalRing (Localization.Away s)]` — derived from
  `(locBasis P T s hopen).toRingFilterBasis.isTopologicalRing` (the
  same pattern used throughout `Presheaf.lean`,
  `WedhornLocalizationContinuity.lean`, etc.).
* `[PlusSubring (Localization.Away s)]` — supplied by `letI :=
  localizationAwayPlusSubring s`.

T206 takes the eight per-Loc inputs as named hypotheses and applies
`exists_dominating_unit` directly. This delivers the **acceptable
fallback** of the ticket's spec: "compile the strongest reducer and
report the exact first missing localised PairOfDefinition / Archimedean
/ no-zero input signature needed to apply Cor732 on Localization.Away
s." Each input is named below.

**Missing-input signatures** (the eight per-Loc preconditions, in
order):

1. `P_loc : PairOfDefinition (Localization.Away s)` — a
   pair-of-definition for the localised ring under `locTopology`. The
   genuine Wedhorn-route construction would build `P_loc.A₀` as the
   image of `P.A₀` under `algebraMap A (Loc s)` (the locSubring
   restricted to `algebraMap`-image), with `P_loc.I` derived from
   `P.I`. **This is the first non-trivial missing input.**

2. `hA₀_le_loc : P_loc.A₀ ≤ (Loc s)⁺` — direction
   `P_loc.A₀ ⊆ localizationAwayPlusSubring s`; should follow once
   `P_loc.A₀` is constructed as a sub-locSubring (since
   `locSubring P T s ⊆ localizationAwayPlusSubring s` by the
   definition of the localised plus-subring).

3. `π_loc : P_loc.A₀` — pseudo-uniformizer in the localised ring,
   typically `algebraMap (P.I-generator)` if `P.I` is principal.

4. `hI_loc : P_loc.I = Ideal.span {π_loc}` — principal ideal data.

5. `hπ_loc_tn : IsTopologicallyNilpotent (P_loc.A₀.subtype π_loc)` —
   topological nilpotency in `(Loc s, locTopology)`. Should follow
   from the original `IsTopologicallyNilpotent` on `(A, top A)` plus
   continuity of `algebraMap A (Loc s)` under `locTopology`.

6. `hπ_loc_unit : IsUnit (P_loc.A₀.subtype π_loc)` — unit-ness
   preserved by `algebraMap`.

7. `hArch_loc : ∀ w : Spv (Loc s), MulArchimedean ...` — Archimedean
   value groups condition; this is a generic abstract hypothesis on
   Spv (Loc s) and is preserved under any ring extension.

8. `T_test_loc, hT_loc` — finite test family on `Loc s` with
   no-common-zero on `Spa(Loc s, ⁺)`.

The **first** non-trivial missing input (item 1, `P_loc`) is the
genuine algebraic content; items 2–8 are derivable from item 1 plus
the existing data on `(A, P, T, s, hopen)` and `Spa A A⁺`. -/

/-- **T206 localised Cor 7.32 dominating-unit supplier**.

Direct application of `Cor732.exists_dominating_unit` to
`Localization.Away s` under `locTopology P T s hopen` and
`localizationAwayPlusSubring s`, given the localised algebraic data.

**Inputs**:
* `(P, T, s, hopen)` — the standard `locTopology` / `locSubring` data.
* `P_loc, hA₀_le_loc, π_loc, hI_loc, hπ_loc_tn, hπ_loc_unit,
  hArch_loc` — the localised pair-of-definition and Tate data on
  `(Loc s, locTopology, localizationAwayPlusSubring)`.
* `T_test_loc, hT_loc` — finite test family on `Loc s` with no-common
  -zero on `Spa(Loc s, ⁺)`.

**Output**: `σ_loc : (Loc s)ˣ` and the strict-domination witness shape
required as input to T205's `h_sigma_loc`.

**Proof**: derive `[IsTopologicalRing (Loc s)]` from `locBasis`, then
apply `Cor732.exists_dominating_unit`. -/
theorem exists_dominating_unit_localised
    [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (P_loc :
      letI : TopologicalSpace (Localization.Away s) :=
        locTopology P T s hopen
      PairOfDefinition (Localization.Away s))
    (hA₀_le_loc :
      letI : TopologicalSpace (Localization.Away s) :=
        locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationAwayPlusSubring s
      P_loc.A₀ ≤ (Localization.Away s)⁺)
    (π_loc :
      letI : TopologicalSpace (Localization.Away s) :=
        locTopology P T s hopen
      P_loc.A₀)
    (hI_loc :
      letI : TopologicalSpace (Localization.Away s) :=
        locTopology P T s hopen
      P_loc.I = Ideal.span {π_loc})
    (hπ_loc_tn :
      letI : TopologicalSpace (Localization.Away s) :=
        locTopology P T s hopen
      IsTopologicallyNilpotent (P_loc.A₀.subtype π_loc))
    (hπ_loc_unit :
      letI : TopologicalSpace (Localization.Away s) :=
        locTopology P T s hopen
      IsUnit (P_loc.A₀.subtype π_loc))
    (hArch_loc :
      ∀ w : Spv (Localization.Away s),
        letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero (Localization.Away s)))
    (T_test_loc : Finset (Localization.Away s))
    (hT_loc :
      letI : TopologicalSpace (Localization.Away s) :=
        locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationAwayPlusSubring s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ T_test_loc, ¬ w.vle τ 0) :
    letI : TopologicalSpace (Localization.Away s) :=
      locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationAwayPlusSubring s
    ∃ σ_loc : (Localization.Away s)ˣ,
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ T_test_loc,
          w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) := localizationAwayPlusSubring s
  haveI : IsTopologicalRing (Localization.Away s) :=
    (locBasis P T s hopen).toRingFilterBasis.isTopologicalRing
  exact exists_dominating_unit P_loc hA₀_le_loc π_loc hI_loc hπ_loc_tn
    hπ_loc_unit hArch_loc T_test_loc hT_loc

/-! ### T208: localised PairOfDefinition supplier on `Localization.Away s`

T206's first non-trivial missing input (item 1 of its docstring's eight
per-Loc preconditions) is
`P_loc : PairOfDefinition (Localization.Away s)` under `locTopology P
T s hopen`. The construction already exists in
`Adic spaces/Prop752.lean` (lines 87–100) as `locPairOfDefinition`
(Wedhorn §8.1):

* `A₀ := locSubring P T s` — the ring of definition
  `D = A₀[t₁/s, …, tₙ/s]`.
* `I := locIdeal P T s` — the ideal of definition `J = I · D`.
* `isOpen := locSubring_isOpen P T s hopen`
  (`Adic spaces/Prop752.lean:37`).
* `fg := locIdeal_fg P T s`
  (`Adic spaces/LocalizationTopology.lean:92`).
* `isAdic := locSubring_isAdic P T s hopen`
  (`Adic spaces/Prop752.lean:53`).

This file is transitively connected to `Prop752.lean` via
`Presheaf.lean`, so `locPairOfDefinition` is already callable from
T206.

T208 below re-exports the existing `locPairOfDefinition` under the
name requested at the T206 supplier callsite, providing a stable entry
point and surfacing the construction on the WedhornMultiDominatingUnit
file ladder. The result is `@[reducible]` so callers of T206 can
substitute `localizationAway_pairOfDefinition P T s hopen` directly
into the `P_loc` argument without unfolding.

**Note on T206's `hA₀_le_loc` (item 2)**: with this `P_loc`, item 2 of
T206's input list specialises to
`locSubring P T s ≤ (localizationAwayPlusSubring s).toSubring`, which
asks whether the algebraMap-image of `P.A₀` plus the `divByS t s`
generators all lie in `algebraMap '' A⁺`. The first part follows from
`P.A₀ ≤ A⁺`; the second part requires `divByS t s ∈ algebraMap '' A⁺`,
which is **NOT generally true** under the trivial
`localizationAwayPlusSubring` choice (`Subring.map (algebraMap A _)
A⁺`). A Wedhorn-faithful refinement of the plus subring on `Loc s`
(integrally closed and containing `locSubring`) is the future-work
gap noted in `WedhornLocalizationPlus.lean:103-106`. This is
**orthogonal** to T208's PairOfDefinition construction and is the
genuine remaining downstream gap for the full `exists_dominating_unit_localised`
chain. -/

/-- **T208 localised PairOfDefinition supplier**.

Re-exports `locPairOfDefinition` (`Adic spaces/Prop752.lean:90`) under
the name expected at the T206 `P_loc` callsite. The localised pair of
definition `(D, J)` on `Localization.Away s` under `locTopology P T s
hopen`:

* ring of definition `D = locSubring P T s = A₀[t₁/s, …, tₙ/s]`,
* ideal of definition `J = locIdeal P T s = I · D`,
* with `D` open in `Localization.Away s` and the subspace topology on
  `D` equal to the `J`-adic topology.

`@[reducible]` so callers of `exists_dominating_unit_localised` (T206)
can substitute `localizationAway_pairOfDefinition P T s hopen`
directly into the `P_loc` argument. -/
@[reducible] noncomputable def localizationAway_pairOfDefinition
    [TopologicalSpace A] [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    letI : TopologicalSpace (Localization.Away s) :=
      locTopology P T s hopen
    PairOfDefinition (Localization.Away s) :=
  locPairOfDefinition P T s hopen

/-! ### T210: algebraMap-image inclusion into `localizationAwayPlusSubring`

For the trivial plus-subring choice
`localizationAwayPlusSubring s := Subring.map (algebraMap A (Loc s)) A⁺`
(`Adic spaces/WedhornLocalizationPlus.lean:108`), the **algebraMap
image of `A⁺`** is by construction the `(Loc s)⁺`-subring itself. T210
below packages this safe pointwise / set-level inclusion fact in a
clean form for downstream consumers — typically used to discharge the
`algebraMap '' P.A₀ ⊆ (Loc s)⁺` half of T206's item-2 input, given
`P.A₀ ≤ A⁺`.

**Limitation re-emphasised** (matching T208 docstring's downstream
note): `divByS t s` (for `t ∈ T`) is **NOT** generally in `(Loc s)⁺`
under this trivial plus-subring choice. T210 makes **no claim** about
`divByS t s`; the full discharge of T206's `hA₀_le_loc` (i.e.,
`locSubring P T s ≤ (Loc s)⁺` under the current trivial plus-subring)
does **not** hold and would require a Wedhorn-faithful refinement of
the plus-subring on `Loc s` (future work, explicitly excluded by the
T210 ticket scope).

The lemmas below are reusable Mathlib-style API parameterised only by
`s : A` and (for the set-level form) the standard `(P, hA₀_le)` data;
they do **not** depend on `T`, `hopen`, or the localisation topology. -/

omit [CommRing A] in
/-- **T210 pointwise algebraMap-image plus membership**.

For `a ∈ A⁺` and any `s : A`, the algebraMap-image
`algebraMap A (Loc s) a` lies in the canonical
`localizationAwayPlusSubring s` plus-subring.

**Proof**: by definition `(Loc s)⁺ = Subring.map (algebraMap A (Loc
s)) A⁺`, so the image membership is the canonical `Subring.mem_map`
witness `⟨a, ha, rfl⟩`. -/
theorem algebraMap_mem_localizationAwayPlusSubring_of_mem_plus
    [CommRing A] [PlusSubring A] (s : A) {a : A} (ha : a ∈ A⁺) :
    letI : PlusSubring (Localization.Away s) := localizationAwayPlusSubring s
    algebraMap A (Localization.Away s) a ∈ (Localization.Away s)⁺ :=
  Subring.mem_map.mpr ⟨a, ha, rfl⟩

/-- **T210 set-level algebraMap-image inclusion**.

If `P.A₀ ≤ A⁺` (the standard `Cor732`/`SpaCompact` precondition), the
algebraMap-image of `P.A₀` (as a `Set`) is contained in
`localizationAwayPlusSubring s`. -/
theorem algebraMap_image_A₀_subset_localizationAwayPlusSubring
    [TopologicalSpace A] [PlusSubring A]
    (P : PairOfDefinition A) (s : A) (hA₀_le : P.A₀ ≤ A⁺) :
    letI : PlusSubring (Localization.Away s) := localizationAwayPlusSubring s
    (algebraMap A (Localization.Away s)) '' (P.A₀ : Set A) ⊆
      ((Localization.Away s)⁺ : Set (Localization.Away s)) := by
  letI : PlusSubring (Localization.Away s) := localizationAwayPlusSubring s
  rintro x ⟨a, ha, rfl⟩
  exact algebraMap_mem_localizationAwayPlusSubring_of_mem_plus s (hA₀_le ha)

/-- **T210 Subring-level algebraMap-image inclusion**.

The Subring-level packaging of the set-level inclusion: the image
subring `Subring.map (algebraMap A (Loc s)) P.A₀` is contained in
`(Loc s)⁺` whenever `P.A₀ ≤ A⁺`. -/
theorem algebraMap_map_A₀_le_localizationAwayPlusSubring
    [TopologicalSpace A] [PlusSubring A]
    (P : PairOfDefinition A) (s : A) (hA₀_le : P.A₀ ≤ A⁺) :
    letI : PlusSubring (Localization.Away s) := localizationAwayPlusSubring s
    Subring.map (algebraMap A (Localization.Away s)) P.A₀ ≤
      ((Localization.Away s)⁺ : Subring (Localization.Away s)) := by
  letI : PlusSubring (Localization.Away s) := localizationAwayPlusSubring s
  rintro x ⟨a, ha, rfl⟩
  exact algebraMap_mem_localizationAwayPlusSubring_of_mem_plus s (hA₀_le ha)

end ValuationSpectrum

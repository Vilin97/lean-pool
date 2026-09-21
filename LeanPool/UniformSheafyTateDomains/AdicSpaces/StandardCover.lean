/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.LaurentRefinement
import LeanPool.UniformSheafyTateDomains.AdicSpaces.StructureSheaf
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Cor732

/-!
# Standard-Cover Reduction (R1 of 2026-04-14 acyclicity plan)

This file scaffolds the **standard-cover reduction** of Wedhorn / Zavyalov
(the revised Q1 route in `docs/plans/2026-04-14-acyclicity-completion.md`).

## Mathematical content

A *standard cover* of a commutative ring `A` is a finite set
`{f₀, …, fₙ} ⊂ A` whose generated ideal is the unit ideal,
`Ideal.span {f₀, …, fₙ} = ⊤`. Geometrically the associated family
`{ R(insert fᵢ C.base.T / C.base.s) }ᵢ` covers `R(C.base.T / C.base.s)` —
this is the "plus-type" Laurent piece for each `fᵢ` inside the base `D₀`
(cf. `laurentPlusDatum` in `LaurentRefinement.lean`).

Wedhorn's Theorem 8.28(b) is proved by the following reduction chain:

1. **Standard-cover reduction** (this file, `refines_by_standard_cover`):
   Any `RationalCoveringData A` admits a refinement by a standard cover. The
   refinement replaces the arbitrary rational pieces `Dᵢ` by plus-type
   pieces at elements `fⱼ ∈ A` whose ideal generates the unit ideal.

2. **Laurent-cover induction** (uses `laurentCover_gluing_presheaf` already
   available in `LaurentRefinement.lean`): once the cover is standard,
   acyclicity follows by induction on the size of the standard cover,
   with each induction step the 2-element Laurent cover of Wedhorn Lemma 8.33.

3. **Transfer** (Proposition A.3 of Wedhorn, scaffolded in `RationalRefinement`
   as `separation_of_finer_rational`): acyclicity for the refinement
   transfers back to the original covering.

The standard-cover reduction replaces the (much harder) Wedhorn Lemma 8.34 /
Phase 5a faithful-flatness route, which required a Spa-point construction at
non-open primes and depended on Bourbaki CA III §2.8 formalization (not in
Mathlib). The standard-cover route **aims** to bypass that blocker; in practice
the Nullstellensatz helper (`exists_nullstellensatz_refinement`) still
requires the non-open-prime Spa-point construction in at least some sub-cases,
so the R1 workaround is incremental rather than a clean cut-off. See
`docs/plans/2026-04-14-acyclicity-completion.md` §"2026-04-15 reviewer-guided
plan revision" (Q1 directive) for details.

## Status (2026-04-20, post-T-NULL-PER-E singleton supplier + per-E strengthening)

* **`RationalCoveringData.refines_by_standard_cover`** — proved sorry-free
  modulo the explicit `hZavyalov` hypothesis (weak-form existence).
  Zero-ring branch fully discharged using `S.elts = ∅`; the nontrivial
  branch dispatches on rational-open nonemptiness and consumes
  `hZavyalov` in the nontrivial case.

* **`RationalCoveringData.refines_by_standard_cover_per_E`** — STRENGTHENED
  variant (2026-04-19): takes `hZavyalov_per_E` (the per-E existence
  shape) and outputs `refines_cover_per_E C S ∧ refines_contain C S`.
  This is the upstream supplier for the S-GEOM-ASM direct per-E
  assembly route (`GeometricReduction.tateAcyclicity_Part2_direct_per_E`).

* **T-NULL-PER-E singleton supplier** (2026-04-20):
  `exists_nullstellensatz_refinement_per_E_of_singleton_cover` derives
  `hZavyalov_per_E` from the weaker `hZavyalov` in the
  single-cover-piece case, bypassing the unformalised Prop 7.14
  candidate-family construction. Paired with
  `refines_cover_per_E_of_singleton_cover` (the underlying predicate
  derivation), this provides a concrete hZavyalov_per_E discharge for
  callers with trivial coverings.

* **`tateAcyclicity_via_standard_cover`** — delegates to
  `tateAcyclicity` in `LaurentRefinement.lean` (the two statements are
  identical bit-for-bit). No independent sorry; the upstream sorry in
  `tateAcyclicity` Part 2 (partition-of-unity gluing) is carried over.

**Infrastructure from 2026-04-16** (Cor 7.32 + Lemma 7.45 interface):

* **`exists_dominating_unit_from_covering`** — wraps Cor 7.32
  (`ValuationSpectrum.exists_dominating_unit`) for use with a
  `RationalCoveringData`: given a finite test family `T ⊆ A` with no common
  zero on `Spa(A, A⁺)`, produces a unit `σ ∈ Aˣ` strictly dominating
  some `t ∈ T` at every Spa point.

* **`exists_spa_point_with_supp_ge_of_prime`** — dispatches on openness
  of a prime `p`:
  * Open case: `exists_spa_point_in_rationalOpen_of_isOpen_prime`
    (trivial valuation at `p`).
  * Non-open case: `exists_mem_spa_supp_ge_of_nonOpen_prime` (Lemma
    7.45). Produces `v ∈ Spa(A, A⁺)` with `p ≤ supp(v)` unconditionally.

* **`spanTop_iff_noCommonZero_spa`** — the conversion lemma: for a
  `PairOfDefinition P` with `[IsAdicComplete P.I P.A₀]`, a finite
  family `T ⊂ A` generates the unit ideal iff `T` has no common zero
  on `Spa(A, A⁺)`. This is the equivalence that connects the
  ideal-theoretic `refines_span_top` clause with the Cor 7.32 hypothesis.

**Remaining blockers**:

1. **T-NULL-PER-E general case** — the Wedhorn Prop 7.14 + Zavyalov
   §2.3 construction for multi-piece covers. Specific missing content:
   the candidate-family construction producing f's that target each
   `Dⱼ ∈ C.covers` SPECIFICALLY (per-E assignment). Cor 7.32 provides
   the dominating-unit step (proved in `Cor732.lean`), Lemma 7.45
   provides the Spa-point step (proved), but Prop 7.14 is unformalised.
   Singleton case above is the narrow-scope workaround.
2. `tateAcyclicity` Part 2 gluing — partition-of-unity via the geometric
   reduction. The S-GEOM-ASM direct per-E route in
   `GeometricReduction.lean` closes this modulo Lane A (T-OV-1) and
   Lane B (T-IDEAL-2 per-E Cor 8.32).

## References

* Zavyalov, *Quasicoherent sheaves on rigid-analytic spaces*, §2 —
  standard-cover refinement argument.
* Wedhorn, *Adic Spaces*, Theorem 8.28(b) and Lemma 8.34.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Theorem 8.28(b), Lemma 8.34.
* `docs/plans/2026-04-14-acyclicity-completion.md` (R1 ticket).
-/

noncomputable section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-! ### Standard covers -/

/-- A **standard cover** of `A` is a finite set of elements whose generated
ideal is the unit ideal.

Geometrically, a standard cover `{f₀, …, fₙ}` of `A` gives rise to the
"plus-type" rational cover of any base `D₀` whose pieces are
`rationalOpen (insert fᵢ D₀.T) D₀.s` (cf. `laurentPlusDatum` in
`LaurentRefinement.lean`). Whenever `Ideal.span {fᵢ} = ⊤`, these pieces
cover `rationalOpen D₀.T D₀.s`: any continuous valuation `v` on the base
sees `v(1) ≤ max_i v(fᵢ)` (since `∑ aᵢ fᵢ = 1` for some `aᵢ`), and the
valuation trichotomy then places `v` in one of the plus-pieces. -/
structure StandardCover (A : Type*) [CommRing A] where
  /-- The finite family of elements generating the unit ideal. -/
  elts : Finset A
  /-- The ideal they generate is all of `A`. -/
  span_eq_top : Ideal.span (elts : Set A) = ⊤

namespace StandardCover

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- A standard cover is nonempty: the unit ideal cannot be generated by the
empty set unless `A` is the zero ring, in which case any singleton works. -/
theorem nonempty_of_nontrivial [Nontrivial A] (S : StandardCover A) : S.elts.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have : Ideal.span ((∅ : Finset A) : Set A) = ⊤ := h ▸ S.span_eq_top
  rw [Finset.coe_empty, Ideal.span_empty] at this
  exact (bot_ne_top this).elim

end StandardCover

/-! ### The three refinement clauses, named as predicates

Rather than repeating the three-clause conjunction, we record each clause as a
named predicate on `S : Finset A` relative to a `RationalCoveringData C`. This
makes the structure of the Nullstellensatz refinement more transparent and
lets downstream work attack each clause independently. -/

/-- **Clause 1 (covering)**: Every point of the base rational open is contained
in the plus-type piece at some element of `S`. -/
def refines_cover [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) : Prop :=
  ∀ v ∈ rationalOpen C.base.T C.base.s,
    ∃ f ∈ S, v ∈ rationalOpen (insert f C.base.T) C.base.s

/-- **Clause 2 (containment)**: Each plus-type piece at an element of `S` is
contained in some piece of the original cover. This captures the *genuinely
new* Nullstellensatz ingredient (Zavyalov §2.3). -/
def refines_contain [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) : Prop :=
  ∀ f ∈ S, ∃ D ∈ C.covers,
    rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s

/-- **Clause 3 (unit ideal)**: The elements of `S` generate the unit ideal in `A`. -/
def refines_span_top (S : Finset A) : Prop :=
  Ideal.span (S : Set A) = ⊤

/-- **Per-E precise covering** (strengthened joint form of Clauses 1+2):
for each `E ∈ C.covers`, every `v` in `E`'s rational open is witnessed by
some `f ∈ S` whose plus-piece both contains `v` *and* is contained in `E`
(not merely in some unspecified cover piece).

This captures the precise per-`f`-to-per-`E` assignment produced by the
Wedhorn/Hübner 8.34 Nullstellensatz-refinement construction (where each
`f` is designed to target a specific cover piece `D = E`). It is strictly
stronger than `refines_cover C S` alone (since it specifies the target
`E` for each covering witness) and combined with `refines_contain C S`
it carries the full precise-refinement information needed downstream for
S-GEOM-ASM Lane B's per-E local covering construction
(`GeometricReduction.RationalCoveringData.per_E_local_covering`). -/
def refines_cover_per_E [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) : Prop :=
  ∀ E ∈ C.covers, ∀ v ∈ rationalOpen E.T E.s,
    ∃ f ∈ S,
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen E.T E.s

/-- **Weakening**: `refines_cover_per_E` implies `refines_cover` via
`C.hcover` (for each `v` in `C.base`'s rational open, `C.hcover` produces
the target `E ∈ C.covers`; then apply the per-E witness). -/
theorem refines_cover_of_refines_cover_per_E [DecidableEq A]
    (C : RationalCoveringData A) (S : Finset A)
    (h : refines_cover_per_E C S) :
    refines_cover C S := by
  intro v hv
  obtain ⟨D, hD, hv_in_D⟩ := C.hcover v hv
  obtain ⟨f, hf, hv_in_plus, _⟩ := h D hD v hv_in_D
  exact ⟨f, hf, hv_in_plus⟩

/-- **Weakening**: `refines_cover_per_E` is strictly stronger than the
existing `refines_contain` provided every `f ∈ S` is actually used as a
per-E witness (which holds for the Wedhorn construction since redundant
f's can always be pruned). We do NOT prove `refines_contain` from
`refines_cover_per_E` here because the two predicates quantify
differently: `refines_contain` quantifies over every `f ∈ S` (including
potentially unused ones), whereas `refines_cover_per_E` only asserts
existence of witnessing `f` for each `(E, v)`. Callers needing both
pass them as independent hypotheses. -/
example [DecidableEq A] (C : RationalCoveringData A) (S : Finset A)
    (_h : refines_cover_per_E C S) : True := trivial

/-! ### T-NULL-PER-E decomposition: per-D construction → global `refines_cover_per_E`

The Wedhorn/Zavyalov construction produces, for each `D ∈ C.covers`,
a local family `S_D ⊂ A` whose plus-pieces (at `C.base`) cover `D`
and land inside `D`. Wedhorn 8.34 (Zavyalov §2.3) then unions these
to form the global `S := ⋃ S_D`.

The **decomposition lemma below** captures this assembly step
cleanly: given per-D local families with the right local containment
and coverage properties, plus a span-top witness on the combined
family, produce the global `refines_cover_per_E C S ∧ refines_contain
C S ∧ refines_span_top S`. This reduces the T-NULL-PER-E general
case to the **per-D construction** (the actual Zavyalov §2.3 /
Prop 7.14-using content that remains external). -/

/-- **T-NULL-PER-E decomposition**: from per-D refining families to
global `hZavyalov_per_E` shape. If for each `D ∈ C.covers` we have a
`Finset A` of refining elements satisfying local containment (`plus-
piece-at-f ⊆ D`) and local coverage (`plus-pieces-at-f-for-f-in-S_D`
cover `D`), and the combined family spans `⊤`, then the union
`S := C.covers.biUnion S_D` satisfies `refines_cover_per_E C S`,
`refines_contain C S`, and `refines_span_top S`.

This lemma encapsulates the **assembly step** of the
Wedhorn/Zavyalov refinement construction (Lemma 8.34 / §2.3). The
per-D family construction itself (the actual Zavyalov §2.3 /
Prop 7.14 content — constructing `mk_S_D` for each `D`) remains
external; this lemma makes that residual boundary explicit and
reusable.

Given a supplier of `mk_S_D` and its properties, this lemma
discharges the `hZavyalov_per_E`-shaped hypothesis consumed by
`RationalCoveringData.refines_by_standard_cover_per_E`. -/
theorem exists_refines_cover_per_E_of_per_D_construction
    [DecidableEq A] (C : RationalCoveringData A)
    (mk_S_D : RationalLocData A → Finset A)
    (h_in_D : ∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s)
    (h_cover_D : ∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
      ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s)
    (h_span : Ideal.span ((C.covers.biUnion mk_S_D : Finset A) : Set A) = ⊤) :
    ∃ S : Finset A,
      refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S := by
  refine ⟨C.covers.biUnion mk_S_D, ?_, ?_, h_span⟩
  · -- refines_cover_per_E: for each E and v ∈ E, find f ∈ mk_S_D E via h_cover_D.
    intro E hE v hv
    obtain ⟨f, hf_in_SE, hv_f⟩ := h_cover_D E hE v hv
    refine ⟨f, Finset.mem_biUnion.mpr ⟨E, hE, hf_in_SE⟩, hv_f,
      h_in_D E hE f hf_in_SE⟩
  · -- refines_contain: for each f ∈ biUnion, extract its D-source and use h_in_D.
    intro f hf
    obtain ⟨D, hD, hf_in_SD⟩ := Finset.mem_biUnion.mp hf
    exact ⟨D, hD, h_in_D D hD f hf_in_SD⟩

/-- **`hZavyalov_per_E` supplier via per-D construction**. Packages
`exists_refines_cover_per_E_of_per_D_construction` into the
`rationalOpen C.base.T C.base.s ≠ ∅ → ∃ S, ...` shape consumed by
`RationalCoveringData.refines_by_standard_cover_per_E`. The
`rationalOpen ≠ ∅` hypothesis is unused since the decomposition is
unconditional — callers supplying per-D data don't need the nonempty
precondition. -/
theorem hZavyalov_per_E_of_per_D_construction
    [DecidableEq A] (C : RationalCoveringData A)
    (mk_S_D : RationalLocData A → Finset A)
    (h_in_D : ∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s)
    (h_cover_D : ∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
      ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s)
    (h_span : Ideal.span ((C.covers.biUnion mk_S_D : Finset A) : Set A) = ⊤) :
    rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S :=
  fun _ ↦ exists_refines_cover_per_E_of_per_D_construction C mk_S_D
    h_in_D h_cover_D h_span

/-! ### T-NULL-PER-E remaining content — reviewer's C1/C2/C3 decomposition

With the `exists_refines_cover_per_E_of_per_D_construction` decomposition
above, T-NULL-PER-E reduces to supplying the per-D function `mk_S_D`.
The **reviewer's further decomposition** splits this per-D construction
into three sequential sub-lemmas:

**C1 (local standard neighborhood)** — for each `D ∈ C.covers` and each
`v ∈ rationalOpen D.T D.s`, produce a single `f ∈ A` such that:
* `v ∈ rationalOpen (insert f C.base.T) C.base.s` (plus-piece-at-f at
  `C.base` contains v).
* `rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s`
  (the plus-piece-at-f is contained in D).

This IS the Wedhorn §8.34 / Zavyalov §2.3 content at the point level.
**Note on difficulty**: the single-`f`-insert shape demands f encode
all of `D.T`'s constraints simultaneously inside the `C.base.s`-
denominator-only plus-piece. Algebraically this requires a
ratio-and-clear-denominators construction using Cor 7.32's
dominating unit to pull `t ∈ D.T` and `D.s` back into `A`.

**C2 (finite extraction via quasi-compactness)** — ✅ **LANDED
2026-04-18** in `SpaCompact.lean`.

**Correction**: an earlier version of this note claimed C2 follows
from `basicOpen_isClopen` + compactness of `Spa`. That is WRONG: the
SpaCompact preamble notes `{v | v.vle a 1} = basicOpen a 1` is
**open, not closed** in `Spv A`. Rational opens are quasi-compact
opens in a spectral space, not clopen.

**Correct route (landed)**: via the Bool Huber embedding
`ιSpvBool : Spv A → (A × A → Bool)`. In the discrete Bool product,
each cylinder `{r | r(t, s) = true}` IS clopen, and
`v ∈ basicOpen t s ↔ ιSpvBool v (t, s) = true`. The theorems
`image_ιSpv_bool_rationalOpen`, `isCompact_rationalOpen_of_isClosed_image`,
`isCompact_preimage_rationalOpen_of_isClosed_image` (all in
`SpaCompact.lean`, all axiom-clean) give the quasi-compactness.
Concrete suppliers:
- `isCompact_preimage_rationalOpen_of_tate_pseudouniformizer` for the
  Tate consumer (the T-NULL-PER-E consumer).
- `isCompact_preimage_rationalOpen_of_discreteTopology` for the
  discrete case.

Consumers needing finite sub-cover extraction: `IsCompact.elim_finite_subcover`
plus C1's per-point covering gives the finite refining family.

**C3 (span-top from no-common-zero)** — given the finite refining
family (union of C1-families from C2-extractions per D, across all
D ∈ C.covers), verify the span-top property via
`spanTop_iff_noCommonZero_spa` (already proved, `StandardCover.lean`).
The no-common-zero hypothesis follows from the C1+C2 cover: every
valuation lies in some D ∈ C.covers's rational open, hence in some
C1-extracted plus-piece-at-f, so `v(f) ≤ v(C.base.s) ≠ 0`, so `v(f)
≠ 0` at least at that f. **Available in project**: ✅ `spanTop_iff_noCommonZero_spa`.

**Exact external question** (Lean target for C1 escalation):

```
-- C1: single-f refinement at each v ∈ D
theorem exists_single_f_refining_point_in_D
    [IsTateRing A] [IsNoetherianRing A] ...
    (C : RationalCoveringData A) (D : RationalLocData A) (hD : D ∈ C.covers)
    (v : Spv A) (hv : v ∈ rationalOpen D.T D.s) :
    ∃ f : A,
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s
```

**Rational-opens-as-basis content (C2)**: ✅ LANDED (see above).
Available for callers as
`isCompact_preimage_rationalOpen_of_tate_pseudouniformizer` and
`isCompact_preimage_rationalOpen_of_discreteTopology` in
`SpaCompact.lean`. Does NOT rely on `rationalOpen_isClosed` or
`basicOpen_isClopen`; uses Bool-cylinder route instead.

**Alternative C1 reduction** (if single-f form is intractable): allow
multiple-f insertion, i.e., `rationalOpen (F ∪ C.base.T) C.base.s`
for a Finset F. This still fails generally (denominator mismatch:
C.base.s vs D.s), but may admit easier formulation via
`rationalOpen_inter`.

**Original external question (global form, now decomposed above)**:

```
∀ (A : Type*) [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A] [IsHuberRing A] [HasLocLiftPowerBounded A]
  [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
  [DecidableEq A] (C : RationalCoveringData A),
  ∃ (mk_S_D : RationalLocData A → Finset A),
    (∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s) ∧
    (∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
      ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s) ∧
    Ideal.span ((C.covers.biUnion mk_S_D : Finset A) : Set A) = ⊤
```

**Available Lean APIs** that can contribute:
* `spanTop_iff_noCommonZero_spa` (`StandardCover.lean`, line ~460) —
  ✅ PROVED: Prop 7.14's forward direction (ideal-to-Spa-cover
  equivalence) is already available.
* `exists_dominating_unit_from_covering` (line ~379) — ✅ Cor 7.32
  dominating-unit extraction.
* `exists_spa_point_with_supp_ge_of_prime` (line ~410) — ✅ Lemma 7.45
  non-open-prime Spa-point lift + open-prime trivial-valuation
  construction.
* `refines_span_top_image_unit_mul` (line ~435) — ✅ unit-rescaled
  family preserves span-top.

**Missing content (Zavyalov §2.3 candidate-family construction)**:
1. For each `D ∈ C.covers`, the test family `D.T ∪ {D.s}` has no
   common zero on `D`'s rational open (trivially).
2. But the candidate elements need to be in `A`, not in the
   localization. Zavyalov's trick: multiply by a dominating unit
   (from Cor 7.32) to get elements of `A` whose plus-pieces contain
   `D` within `D`.
3. The span-top property on the union follows from combining per-D
   no-common-zero witnesses (via Prop 7.14 `spanTop_iff_noCommonZero_spa`).

**Ticket log entry** — see `.mathlib-quality/tickets.md` T-NULL-PER-E:
the decomposition lemma reduces the general case to the per-D
construction. The per-D construction requires the explicit Zavyalov
§2.3 computation (unit-rescaling of test families + span-top via
Cor 7.32 + Prop 7.14); this is the next formalisation target and
is outside the scope of the geometric lane's decomposition helper. -/

/-! ### T-NULL-PER-E: discharging `refines_cover_per_E` in special cases

The full Wedhorn Prop 7.14 / Hübner 3.7-3.8 construction that produces
`refines_cover_per_E` from abstract cover data remains unformalised.
However, in **special cases** — e.g., when the covering has a single
piece, or when the refinement is tautological — `refines_cover_per_E`
can be derived unconditionally from `refines_cover` + `refines_contain`.
We land the singleton-cover derivation here; it provides a concrete
`hZavyalov_per_E` discharge route for callers whose `C.covers` happens
to be a single piece, and documents the exact shape of the general
residual. -/

/-- **Singleton-cover case**: if `C.covers` has at most one piece
(`∀ D₁ D₂ ∈ C.covers, D₁ = D₂`), then `refines_cover C S` and
`refines_contain C S` together imply `refines_cover_per_E C S`.

**Proof**: the `D'` returned by `refines_contain` for any `f ∈ S` is
FORCED to equal `E ∈ C.covers` (since all cover pieces are equal), so
the per-E assignment is automatic. -/
theorem refines_cover_per_E_of_singleton_cover
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A)
    (hC_singleton : ∀ D₁ D₂, D₁ ∈ C.covers → D₂ ∈ C.covers → D₁ = D₂)
    (hS_cover : refines_cover C S)
    (hS_contain : refines_contain C S) :
    refines_cover_per_E C S := by
  intro E hE v hv
  -- v ∈ rationalOpen E.T E.s ⊆ rationalOpen C.base.T C.base.s via C.hsubset.
  have hv_base : v ∈ rationalOpen C.base.T C.base.s := C.hsubset E hE hv
  -- refines_cover gives f ∈ S with v ∈ plus-piece-at-f.
  obtain ⟨f, hf_S, hv_plus⟩ := hS_cover v hv_base
  -- refines_contain gives D' ∈ C.covers with plus-piece-at-f ⊆ D'.
  obtain ⟨D', hD'_mem, hD'_sub⟩ := hS_contain f hf_S
  -- In the singleton case, D' = E.
  have hD'_eq : D' = E := hC_singleton D' E hD'_mem hE
  exact ⟨f, hf_S, hv_plus, hD'_eq ▸ hD'_sub⟩

/-- **`hZavyalov_per_E` discharge in the singleton-cover case**. Takes
the weaker `hZavyalov` existence and a singleton-cover witness, produces
the strengthened `hZavyalov_per_E` existence shape consumed by
`refines_by_standard_cover_per_E`. Useful for callers whose rational
covering has a single piece. -/
theorem exists_nullstellensatz_refinement_per_E_of_singleton_cover
    [DecidableEq A] (C : RationalCoveringData A)
    (hC_singleton : ∀ D₁ D₂, D₁ ∈ C.covers → D₂ ∈ C.covers → D₁ = D₂)
    (hZavyalov : ∃ S : Finset A,
      refines_cover C S ∧ refines_contain C S ∧ refines_span_top S) :
    ∃ S : Finset A,
      refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S := by
  obtain ⟨S, hS_cover, hS_contain, hS_span⟩ := hZavyalov
  exact ⟨S,
    refines_cover_per_E_of_singleton_cover C S hC_singleton hS_cover hS_contain,
    hS_contain, hS_span⟩

/-- **`hZavyalov_per_E` supplier via singleton-cover reduction**. Packages
`exists_nullstellensatz_refinement_per_E_of_singleton_cover` into the
`rationalOpen C.base.T C.base.s ≠ ∅ → ∃ S, ...` shape consumed by
`RationalCoveringData.refines_by_standard_cover_per_E`. Companion of
`hZavyalov_per_E_of_per_D_construction` for the singleton-cover branch:
the caller supplies the plain `hZavyalov` existence together with a
singleton-cover witness, and `hZavyalov_per_E` follows unconditionally
(the `rationalOpen ≠ ∅` premise is unused). -/
theorem hZavyalov_per_E_of_singleton_cover
    [DecidableEq A] (C : RationalCoveringData A)
    (hC_singleton : ∀ D₁ D₂, D₁ ∈ C.covers → D₂ ∈ C.covers → D₁ = D₂)
    (hZavyalov : ∃ S : Finset A,
      refines_cover C S ∧ refines_contain C S ∧ refines_span_top S) :
    rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S :=
  fun _ ↦ exists_nullstellensatz_refinement_per_E_of_singleton_cover
    C hC_singleton hZavyalov

/-! ### C1 special case: standard-shape `D`

When `D ∈ C.covers` already has the standard plus-piece shape
`rationalOpen D.T D.s = rationalOpen (insert f₀ C.base.T) C.base.s`
for some `f₀ : A`, the C1 single-`f` refinement is trivial: take `f = f₀`.
This is the **base case** of the Wedhorn §8.34 reduction: once an
arbitrary cover is refined to a standard cover (via Zavyalov §2.3), each
piece has this shape and C1 discharges automatically.

Landing this helper documents the single-`f`-refinement obligation in
its most common consumed form and lets callers immediately discharge C1
after they have performed the Zavyalov refinement. -/

/-- **C1 discharge for standard-shape D**: if `D` is already of the
form `R(insert f₀ base.T, base.s)` for some `f₀ : A`, then the single-
`f` refinement at every `v ∈ D` is simply `f := f₀`. -/
theorem exists_single_f_refinement_of_standardShape
    [DecidableEq A] (C : RationalCoveringData A) (D : RationalLocData A)
    (f₀ : A)
    (hD_shape : rationalOpen D.T D.s =
      rationalOpen (insert f₀ C.base.T) C.base.s)
    {v : Spv A} (hv : v ∈ rationalOpen D.T D.s) :
    ∃ f : A,
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s :=
  ⟨f₀, hD_shape ▸ hv, hD_shape.ge⟩

omit [IsTopologicalRing A] in
/-- **Multi-`F` decomposition**: for any `F, T : Finset A` and `s : A`,
the rational open at `F ∪ T` equals the intersection of the plus-pieces
at each `f ∈ F` (with base `T`) with the rational open at `T`:
`R(F ∪ T, s) = (⋂ f ∈ F, R(insert f T, s)) ∩ R(T, s)`.

**Usage**: this structural identity records that a "D in multi-F shape"
(`R(D.T, D.s) = R(F ∪ C.base.T, C.base.s)`) is exactly the joint
intersection of plus-pieces over F. It is WEAKER than `refines_cover_per_E`
— the individual plus-piece at `f ∈ F` is NOT generally contained in `D`,
only the joint intersection is. For the single-`f`-per-point form
consumed by `refines_cover_per_E`, the per-point `f` depends on `v` and
requires the full Zavyalov §2.3 construction (documented below). -/
theorem rationalOpen_eq_biInter_insert_union
    [DecidableEq A] (F : Finset A) (T : Finset A) (s : A) :
    rationalOpen (F ∪ T) s =
      (⋂ f ∈ F, rationalOpen (insert f T) s) ∩ rationalOpen T s := by
  ext v
  constructor
  · rintro ⟨hv_spa, hvFT, hvs⟩
    refine ⟨?_, hv_spa, fun t ht ↦ hvFT t (Finset.mem_union_right F ht), hvs⟩
    simp only [Set.mem_iInter]
    intro f hf
    refine ⟨hv_spa, fun t ht ↦ ?_, hvs⟩
    rcases Finset.mem_insert.mp ht with rfl | ht'
    · exact hvFT t (Finset.mem_union_left T hf)
    · exact hvFT t (Finset.mem_union_right F ht')
  · rintro ⟨hfam, hv_spa, hvT, hvs⟩
    refine ⟨hv_spa, fun t ht ↦ ?_, hvs⟩
    rcases Finset.mem_union.mp ht with hF | hT_mem
    · have hmem : v ∈ rationalOpen (insert t T) s := by
        simp only [Set.mem_iInter] at hfam
        exact hfam t hF
      exact hmem.2.1 t (Finset.mem_insert_self t T)
    · exact hvT t hT_mem

/-! ### C1 full discharge when every cover piece has standard shape

When the user has already reduced the cover to a "standard" rational
cover — i.e., each `D ∈ C.covers` is of the form
`R(insert f_D C.base.T, C.base.s)` for some `f_D : A` — the per-D
C1 construction `mk_S_D D := {f_D}` provides `h_in_D` and `h_cover_D`
immediately, leaving only the span-top hypothesis for the caller. This
matches the Wedhorn §8.34 strategy: reduce to standard cover first,
then everything after is syntactic.

The Zavyalov §2.3 content that is **still external** is the *reduction*
itself (arbitrary cover → standard cover). Consumers who supply the
`f_D : A` witness per piece can discharge C1 without Prop 7.14. -/

/-- **Per-D C1 data from standard-shape witnesses**: if for each
`D ∈ C.covers` the user supplies a `f_D : A` with
`R(D.T, D.s) = R(insert f_D C.base.T, C.base.s)`, then the per-D
refining family `mk_S_D D := {f_D}` satisfies both `h_in_D` (each
plus-piece at `f_D` lies inside `D`) and `h_cover_D` (each `v ∈ D` is
in the plus-piece at `f_D`). The remaining `h_span` (unit-ideal span
of the combined family) is the only external obligation. -/
theorem per_D_construction_of_standardShape
    [DecidableEq A] (C : RationalCoveringData A)
    (f_D : RationalLocData A → A)
    (h_shape : ∀ D ∈ C.covers,
      rationalOpen D.T D.s =
        rationalOpen (insert (f_D D) C.base.T) C.base.s) :
    let mk_S_D : RationalLocData A → Finset A := fun D ↦ {f_D D}
    (∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s) ∧
    (∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
      ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s) := by
  refine ⟨?_, ?_⟩
  · intro D hD f hf
    rw [Finset.mem_singleton] at hf
    rw [hf, ← h_shape D hD]
  · intro D hD v hv
    refine ⟨f_D D, Finset.mem_singleton.mpr rfl, ?_⟩
    rw [← h_shape D hD]
    exact hv

/-- **hZavyalov_per_E discharge from standard-shape refinement and
span-top witness.** If every `D ∈ C.covers` has the standard shape
`R(insert f_D C.base.T, C.base.s)` for user-supplied `f_D`, and the
combined family spans the unit ideal, then `hZavyalov_per_E` holds
(using `exists_refines_cover_per_E_of_per_D_construction`).

**What this bypasses**: the full Wedhorn §8.34 / Zavyalov §2.3 reduction
(arbitrary cover → standard cover). Callers with pre-standardised
covers can discharge C1+C3 entirely; C2 remains handled by
`SpaCompact.isCompact_preimage_rationalOpen_of_tate_pseudouniformizer`. -/
theorem exists_refines_cover_per_E_of_standardShape
    [DecidableEq A] (C : RationalCoveringData A)
    (f_D : RationalLocData A → A)
    (h_shape : ∀ D ∈ C.covers,
      rationalOpen D.T D.s =
        rationalOpen (insert (f_D D) C.base.T) C.base.s)
    (h_span :
      Ideal.span ((C.covers.image f_D : Finset A) : Set A) = ⊤) :
    ∃ S : Finset A,
      refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S := by
  -- Let `mk_S_D D := {f_D D}`; its `biUnion` equals `C.covers.image f_D`.
  have hbiUnion : (C.covers.biUnion (fun D ↦ ({f_D D} : Finset A)) : Finset A) =
      C.covers.image f_D := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_singleton, Finset.mem_image, eq_comm]
  obtain ⟨h_in_D, h_cover_D⟩ :=
    per_D_construction_of_standardShape C f_D h_shape
  refine exists_refines_cover_per_E_of_per_D_construction C
    (fun D ↦ {f_D D}) h_in_D h_cover_D ?_
  rw [hbiUnion]; exact h_span

/-- **`hZavyalov_per_E` supplier via standard-shape per-piece witnesses**.
Packages `exists_refines_cover_per_E_of_standardShape` into the
`rationalOpen C.base.T C.base.s ≠ ∅ → ∃ S, ...` shape consumed by
`RationalCoveringData.refines_by_standard_cover_per_E`. Companion of
`hZavyalov_per_E_of_per_D_construction` for the standard-shape branch:
the caller supplies a per-piece single-generator witness `f_D` with
`R(D.T, D.s) = R(insert (f_D D) C.base.T, C.base.s)` together with a
global span-top for the collected family `C.covers.image f_D`. The
`rationalOpen ≠ ∅` premise is unused; this wrapper just adapts the shape
for direct substitution into `tateAcyclicity_Part2_*_via_primary_*`
callsites that expect the `hZavyalov_per_E` implication form. -/
theorem hZavyalov_per_E_of_standardShape
    [DecidableEq A] (C : RationalCoveringData A)
    (f_D : RationalLocData A → A)
    (h_shape : ∀ D ∈ C.covers,
      rationalOpen D.T D.s =
        rationalOpen (insert (f_D D) C.base.T) C.base.s)
    (h_span :
      Ideal.span ((C.covers.image f_D : Finset A) : Set A) = ⊤) :
    rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S :=
  fun _ ↦ exists_refines_cover_per_E_of_standardShape C f_D h_shape h_span

/-! ### General case: exact minimal missing lemma

The general `refines_cover_per_E` discharge — for covers with multiple
pieces — requires the Wedhorn Prop 7.14 / Hübner 3.7-3.8 Nullstellensatz
construction. Specifically, the missing ingredient is a **per-E
candidate family construction**:

**Missing lemma (T-NULL-PER-E-general)**: given `C : RationalCoveringData A`
and the Tate-ring hypotheses, produce a Finset `S ⊂ A` such that for
EACH `E ∈ C.covers` and each `v` in `E`'s rational open, SOME `f ∈ S`
has plus-piece-at-f targeting `E` specifically (not just some `D`).

The Wedhorn proof constructs `S` per-`D ∈ C.covers`: for each `D`, a
finite sub-family of ratios `tⱼ / D.s` (for `tⱼ ∈ D.T`) combined with
the Prop 7.14 adic Nullstellensatz to clear denominators. The result
is tracked as a per-E assignment by construction. The formal statement:

```
theorem refines_by_standard_cover_per_E_unconditional
    [IsTateRing A] [IsNoetherianRing A] ...
    (C : RationalCoveringData A) (hne : C.covers.Nonempty) :
    ∃ S : Finset A,
      refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S
```

**Dependencies for formalisation**:
1. Cor 7.32 (`Cor732.lean`) — dominating-unit extraction. ✓ PROVED.
2. Lemma 7.45 (`Lemma745.exists_mem_spa_supp_ge_of_nonOpen_prime`) —
   Spa-point construction at non-open primes. ✓ PROVED.
3. **Prop 7.14 adic Nullstellensatz** — UNFORMALISED (this is the
   blocker). Specifically, the strong Nullstellensatz giving that a
   finite family `T ⊂ A` with no common zero on `Spa(A, A⁺)`
   generates the unit ideal.
4. **Zavyalov §2.3 candidate-family construction** — UNFORMALISED.
   Uses Prop 7.14 + Cor 7.32 to construct the specific ratios
   `tⱼ / Dⱼ.s`.

Without items (3) and (4), the general `refines_cover_per_E` discharge
is blocked. The singleton case above (`refines_cover_per_E_of_singleton_cover`)
bypasses items (3)-(4) by observing that the D-target is forced.

**Status per T-NULL-7 ticket**: full Prop 7.14 not needed for Route B
Tate-acyclicity closure — the `hZavyalov_per_E` can be supplied as an
explicit hypothesis via `refines_by_standard_cover_per_E`. The
singleton case here is a concrete supplier for the degenerate covering;
the general case remains as an external Wedhorn-Hübner formalisation
obligation. -/

/-! ### Internal helpers from Cor 7.32 and Lemma 7.45

The Zavyalov §2.3 construction (Wedhorn Lemma 8.34(ii)) decomposes into three
ingredients:

1. A **Spa-points witness**: for every prime `p` of `A` with `C.base.s ∉ p`,
   produce `v ∈ rationalOpen C.base.T C.base.s` with `p ≤ v.supp`.
   This dispatches on openness of `p`:
   * **Open `p`**: use `exists_spa_point_in_rationalOpen_of_isOpen_prime`.
   * **Non-open `p`**: use `exists_mem_spa_supp_ge_of_nonOpen_prime` (Lemma
     7.45). This gives a Spa point with support containing `p`, but not
     automatically in the rational open — the containment in
     `rationalOpen C.base.T C.base.s` requires an additional
     specialization-theoretic argument (Wedhorn Prop 7.41 / Remark 7.58).

2. A **dominating-unit extraction** (Cor 7.32): given a finite test family
   `T ⊆ A` with no common zero on `Spa A A⁺`, produce a unit `s ∈ Aˣ` with
   `v(s) < v(t)` (strictly) for some `t ∈ T`, at every `v ∈ Spa`.

3. A **candidate-family construction** (Zavyalov §2.3): given (1) and (2)
   plus the adic Nullstellensatz (Wedhorn Prop 7.14), produce the refining
   family `S`.

The `hZavyalov` hypothesis below packages ingredient (3). Ingredients
(1)–(2) are available via `exists_spa_point_in_rationalOpen_of_isOpen_prime`,
`exists_mem_spa_supp_ge_of_nonOpen_prime`, and `exists_dominating_unit`.

The present file demonstrates the invocation pattern via
`exists_dominating_unit_from_covering` below, which extracts a dominating
unit from a rational covering under the typeclass assumptions of Cor 7.32.
This is a stepping stone toward a full internal discharge of `hZavyalov`;
the remaining obstruction is constructing a Spa-level no-common-zero family
from the cover condition (requires the adic Nullstellensatz Prop 7.14). -/

/-- **Cor 7.32 invocation for rational coverings.** Given a rational
covering `C` and a finite test family `T ⊆ A` with no common zero on
`Spa(A, A⁺)`, Cor 7.32 produces a unit `σ ∈ Aˣ` with `v(σ) < v(t)` for
some `t ∈ T`, at every Spa point `v`.

This demonstrates the interface between `RationalCoveringData` data and
`ValuationSpectrum.exists_dominating_unit` (Cor 7.32). It is a
building block for the Zavyalov §2.3 candidate-family construction
referenced by `hZavyalov`; the remaining obstruction is producing the
no-common-zero hypothesis `hT` from the cover condition (requires the
adic Nullstellensatz Prop 7.14 and the Spa-points witness from
`Lemma 7.45` — see the `exists_nullstellensatz_refinement_of_rationalOpen_nonempty`
docstring below for the full analysis). -/
theorem exists_dominating_unit_from_covering
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A,
      letI : ValuativeRel A := v.toValuativeRel
      MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (_C : RationalCoveringData A) (T : Finset A)
    (hT : ∀ v ∈ Spa A A⁺, ∃ t ∈ T, ¬ v.vle t 0) :
    ∃ σ : Aˣ, ∀ v ∈ Spa A A⁺, ∃ t ∈ T,
      v.vle (σ : A) t ∧ ¬ v.vle t (σ : A) :=
  exists_dominating_unit P hA₀_le π hI hπ_tn hπ_unit hArch T hT

/-- **Spa-point producer for arbitrary primes** (combining open + non-open
cases). For a prime `p` of `A` with `s ∉ p`:

* If `p` is open, the trivial-valuation-at-`p` construction
  (`exists_spa_point_in_rationalOpen_of_isOpen_prime`) gives
  `v ∈ rationalOpen T s` with `p ≤ v.supp`.
* If `p` is non-open, `Lemma 7.45`
  (`exists_mem_spa_supp_ge_of_nonOpen_prime`) gives a Spa point with
  `p ≤ v.supp`.

The open-prime output lands *in the rational open*; the non-open output
only lands *in Spa*. Matching these into a single "Spa-point witness in
the rational open" is the residual obligation that distinguishes the
discrete-case proof in `TateAcyclicity.lean:475` from the general Tate
case: the Tate case needs an additional specialization-theoretic step
(Wedhorn Prop 7.41) to move the non-open-prime Spa point into the
rational open. -/
theorem exists_spa_point_with_supp_ge_of_prime
    [IsTopologicalRing A] [IsHuberRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺ : Subring A)]
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    {p : Ideal A} [p.IsPrime] :
    ∃ v ∈ Spa A A⁺, p ≤ v.supp := by
  by_cases hp_open : IsOpen (p : Set A)
  · -- Open prime: use the open-prime Spa-point construction.
    -- Take `T = ∅`, `s = 1`; the rational open is then `Spa A A⁺`.
    have h1_notin : (1 : A) ∉ p := by
      intro h
      exact (Ideal.IsPrime.ne_top inferInstance) (Ideal.eq_top_iff_one p |>.mpr h)
    have key := ValuationSpectrum.exists_spa_point_in_rationalOpen_of_isOpen_prime
      (A := A) (∅ : Finset A) (1 : A) p hp_open h1_notin
    obtain ⟨v, hv_rat, hv_supp⟩ := key
    exact ⟨v, hv_rat.1, hv_supp⟩
  · -- Non-open prime: FAITHFUL pair-free (Wedhorn 7.45 + 7.41 +
    -- `IsRingOfIntegralElements.subset_powerBounded`): the non-open prime has a continuous
    -- analytic Spa-point bounded on all of `A°`, which lies in `Spa(A, A⁺)` since `A⁺ ⊆ A°`.
    obtain ⟨v, hv_cont, hv_supp, hv_bd⟩ :=
      exists_cont_supp_ge_powerBounded_of_nonOpen_prime (A := A) P hp_open
    exact ⟨v, ⟨hv_cont, fun f hf => hv_bd f
      (IsRingOfIntegralElements.subset_powerBounded (B := (A⁺ : Subring A)) hf)⟩, hv_supp⟩

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- **Unit-rescaled family keeps unit-ideal span.** Multiplying a finite family
by a fixed unit does not change the ideal it generates, so the rescaled family
spans the unit ideal iff the original does. This is the `refines_span_top`
clause under the Zavyalov construction `S := T.image (σ⁻¹ * ·)`. -/
theorem refines_span_top_image_unit_mul [DecidableEq A]
    (σ : Aˣ) {T : Finset A} (hT : Ideal.span (T : Set A) = ⊤) :
    Ideal.span ((T.image (fun t ↦ (σ.inv : A) * t) : Finset A) : Set A) = ⊤ := by
  rw [eq_top_iff, ← hT, Ideal.span_le]
  intro t ht
  -- Write `t = σ * (σ.inv * t)`; since `σ.inv * t ∈ image`, `t` lies in the span.
  have h_eq : t = (σ : A) * ((σ.inv : A) * t) := by
    rw [← mul_assoc]
    have : (σ : A) * (σ.inv : A) = 1 := σ.val_inv
    rw [this, one_mul]
  rw [h_eq]
  refine Ideal.mul_mem_left _ (σ : A) (Ideal.subset_span ?_)
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨t, ht, rfl⟩)

/-- **Span-top ⟺ no-common-zero on Spa.** Given `exists_spa_point_with_supp_ge_of_prime`
(which lifts every prime `p` of `A` to a Spa point `v` with `p ≤ supp(v)`), the
two conditions are equivalent:

* `Ideal.span (T : Set A) = ⊤` in `A`.
* For every `v ∈ Spa(A, A⁺)`, some `t ∈ T` satisfies `v(t) ≠ 0`
  (equivalently, `¬ v.vle t 0`).

This equivalence is what converts between the ideal-theoretic formulation
(required for `refines_span_top`) and the Spa-cover-condition formulation
(required for `exists_dominating_unit` Cor 7.32). -/
theorem spanTop_iff_noCommonZero_spa
    [IsTopologicalRing A] [IsHuberRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺ : Subring A)]
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    (T : Finset A) :
    Ideal.span (T : Set A) = ⊤ ↔
      ∀ v ∈ Spa A A⁺, ∃ t ∈ T, ¬ v.vle t 0 := by
  constructor
  · intro h_span v hv
    -- If `span T = ⊤`, then `1 ∈ span T`, so writing `1 = ∑ a_i t_i` we cannot
    -- have `v(t) = 0` for all `t ∈ T`, else `v(1) = 0`. Since v is a valuation
    -- with `v(1) ≠ 0`, some `v(t) ≠ 0`.
    by_contra h_all
    push Not at h_all
    -- `h_all : ∀ t ∈ T, v.vle t 0`. So `T ⊆ v.supp`.
    have hT_le_supp : (T : Set A) ⊆ (v.supp : Set A) := by
      intro t ht
      exact (v.mem_supp_iff t).mpr (h_all t ht)
    -- Then `span T ⊆ v.supp`.
    have hspan_le : Ideal.span (T : Set A) ≤ v.supp :=
      Ideal.span_le.mpr hT_le_supp
    -- But `span T = ⊤` gives `⊤ ≤ v.supp`, so `v.supp = ⊤` — contradicting `v.supp.IsPrime`.
    rw [h_span] at hspan_le
    exact (instIsPrimeSupp v).ne_top (top_le_iff.mp hspan_le)
  · intro h_spa
    -- If `span T ≠ ⊤`, there's a prime `p` containing `span T`, hence `T ⊆ p`.
    -- By `exists_spa_point_with_supp_ge_of_prime`, there's `v ∈ Spa` with `p ≤ supp(v)`.
    -- Then `T ⊆ p ⊆ supp(v)`, so `v.vle t 0` for all `t ∈ T`, contradicting `h_spa`.
    by_contra h_ne
    obtain ⟨q, hq_max, hq_le⟩ := Ideal.exists_le_maximal _ h_ne
    haveI : q.IsPrime := hq_max.isPrime
    obtain ⟨v, hv_spa, hv_supp⟩ := exists_spa_point_with_supp_ge_of_prime (A := A) P
      (p := q)
    obtain ⟨t, htT, htne⟩ := h_spa v hv_spa
    apply htne
    refine (v.mem_supp_iff t).mp ?_
    exact hv_supp (hq_le (Ideal.subset_span htT))

/-! ### Zavyalov §2.3 candidate-family — sorry-free wrappers + missing-sublemma signature

The user's target (`ZAVYALOV-CANDIDATE-FAMILY` ticket) is the existential

```
∃ mk_S_D : RationalLocData A → Finset A,
  (∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
    rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s) ∧
  (∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
    ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s) ∧
  Ideal.span ((C.covers.biUnion mk_S_D : Finset A) : Set A) = ⊤
```

under the bare class context `[IsTateRing A] [IsNoetherianRing A] [T2Space A]
[NonarchimedeanRing A] [DecidableEq A]`. Two distinct obstructions block an
unconditional discharge of this target inside the project as it stands today:

**(O1) Hypothesis gap.** Both `spanTop_iff_noCommonZero_spa` (Prop 7.14, line
~838) and `exists_dominating_unit_from_covering` (Cor 7.32, line ~757)
require a concrete `(P : PairOfDefinition A)` together with
* `[IsAdicComplete P.I P.A₀]`,
* `(hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)` (Prop 7.14 / Lemma 7.45 side),
* `(hA₀_le : P.A₀ ≤ A⁺)`, `π / hI / hπ_tn / hπ_unit` (principal generator), and
* `(hArch : ∀ v : Spv A, MulArchimedean (ValuativeRel.ValueGroupWithZero A))`
  (Cor 7.32 side).

`IsTateRing.principalPair` (`HuberRings.lean:545`) supplies `P + π + hI + hπ_tn
+ hπ_unit`, but not `IsAdicComplete`, `hAplus_le_A₀`, `hA₀_le`, or `hArch` — and
in particular `hAplus_le_A₀ ∧ hA₀_le` together force `P.A₀ = A⁺`, a uniformity
condition not derivable from `[IsTateRing A]`.

**(O2) Construction gap.** Even with all hypotheses in (O1), the **candidate
family itself** is missing. `spanTop_iff_noCommonZero_spa` checks span-top
from a Spa-level no-common-zero witness, and `exists_dominating_unit_from_covering`
extracts a dominating unit from such a witness — but neither produces
`mk_S_D : RationalLocData A → Finset A` satisfying `h_in_D` (per-D plus-piece
containment) and `h_cover_D` (per-D plus-piece coverage). That construction is
the actual Zavyalov §2.3 / Wedhorn 8.34(ii) content (ratios `t/D.s` cleared via
Cor 7.32's dominating unit). It remains UNFORMALISED.

**Shipped contribution.** Three thin sorry-free wrappers below capture the
*exact* boundary between "what the project provides" and "what §2.3 still
owes":

* `zavyalov_candidate_family_h_span_from_no_common_zero` — bridges a
  Spa-level no-common-zero witness on `C.covers.biUnion mk_S_D` to the
  ideal-theoretic span-top conclusion via `spanTop_iff_noCommonZero_spa`.
  Sorry-free; uses Prop 7.14 directly.
* `zavyalov_candidate_family_per_D_from_construction` — repackages the
  per-D combinatorial witness `(mk_S_D, h_in_D, h_cover_D)` together with
  the no-common-zero witness into the user's target existential form.
  Sorry-free; one-line composition.
* `hZavyalov_per_E_from_candidate_family_construction` — composes the
  above with `hZavyalov_per_E_of_per_D_construction` (line ~292) to
  produce a clean `hZavyalov_per_E` discharge route for callers who can
  supply the §2.3 data. Sorry-free.

**Precise minimal missing sublemma.** The single piece needed to upgrade the
shipped wrappers to the user's bare-class unconditional target is documented
below as `exists_zavyalov_candidate_family` (NOT proved here — listed only as
a target signature). It bundles (O1) and (O2): given the PoD + completeness +
plus-subring compatibility + Archimedean hypotheses, produce `mk_S_D` with
`h_in_D ∧ h_cover_D ∧ (Spa-level no-common-zero)`. Once that lemma lands, the
user's unconditional target follows by composing it with
`zavyalov_candidate_family_h_span_from_no_common_zero`. -/

/-- **Zavyalov §2.3 — span-top from no-common-zero family** (Prop 7.14
direct invocation). Given a per-D candidate family `mk_S_D` together with
the Spa-level no-common-zero witness on the union family
`C.covers.biUnion mk_S_D`, the unit-ideal-span follows from
`spanTop_iff_noCommonZero_spa`.

This is the core sorry-free bridge: it exposes that the *only* ingredient
external to the project is the Zavyalov §2.3 candidate-family
CONSTRUCTION (which produces both the per-D combinatorial data and the
Spa-level no-common-zero witness simultaneously). -/
theorem zavyalov_candidate_family_h_span_from_no_common_zero
    [DecidableEq A] [IsHuberRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺ : Subring A)] (P : PairOfDefinition A)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (C : RationalCoveringData A)
    (mk_S_D : RationalLocData A → Finset A)
    (h_no_common_zero : ∀ v ∈ Spa A A⁺,
      ∃ f ∈ C.covers.biUnion mk_S_D, ¬ v.vle f 0) :
    Ideal.span ((C.covers.biUnion mk_S_D : Finset A) : Set A) = ⊤ :=
  (spanTop_iff_noCommonZero_spa P _).mpr h_no_common_zero

/-- **Zavyalov §2.3 — per-D existential from a candidate-family
construction** (the user's target signature, in conditional form).

Given the per-D combinatorial witness `(mk_S_D, h_in_D, h_cover_D)` and a
Spa-level no-common-zero witness on the union family, this produces the
existential form

```
∃ mk_S_D, h_in_D ∧ h_cover_D ∧ (span = ⊤)
```

required by `exists_refines_cover_per_E_of_per_D_construction`.

**External obligation.** The four inputs `(mk_S_D, h_in_D, h_cover_D,
h_no_common_zero)` are exactly the Zavyalov §2.3 output that remains
UNFORMALISED. This wrapper merely repackages the combinatorial witness
into the existential form expected downstream; the actual content
(constructing `mk_S_D` from a `RationalCoveringData` under `[IsTateRing A]
∧ [IsNoetherianRing A]`) is recorded as the target signature
`exists_zavyalov_candidate_family` in the docstring above. -/
theorem zavyalov_candidate_family_per_D_from_construction
    [DecidableEq A] [IsHuberRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺ : Subring A)] (P : PairOfDefinition A)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (C : RationalCoveringData A)
    (mk_S_D : RationalLocData A → Finset A)
    (h_in_D : ∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s)
    (h_cover_D : ∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
      ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s)
    (h_no_common_zero : ∀ v ∈ Spa A A⁺,
      ∃ f ∈ C.covers.biUnion mk_S_D, ¬ v.vle f 0) :
    ∃ mk_S_D' : RationalLocData A → Finset A,
      (∀ D ∈ C.covers, ∀ f ∈ mk_S_D' D,
        rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s) ∧
      (∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
        ∃ f ∈ mk_S_D' D, v ∈ rationalOpen (insert f C.base.T) C.base.s) ∧
      Ideal.span ((C.covers.biUnion mk_S_D' : Finset A) : Set A) = ⊤ :=
  ⟨mk_S_D, h_in_D, h_cover_D,
    zavyalov_candidate_family_h_span_from_no_common_zero P hAplus_le_A₀ C mk_S_D
      h_no_common_zero⟩

/-- **`hZavyalov_per_E` discharge from candidate-family construction +
no-common-zero**. Composes
`zavyalov_candidate_family_per_D_from_construction` with
`hZavyalov_per_E_of_per_D_construction` (line ~292) to produce the
`rationalOpen ≠ ∅ → ∃ S, refines_cover_per_E ∧ refines_contain ∧
refines_span_top` shape consumed by
`RationalCoveringData.refines_by_standard_cover_per_E` and the direct per-E
Tate-acyclicity assembly.

This is the **end-to-end consumer-ready wrapper**: callers who can
supply the Zavyalov §2.3 data (`mk_S_D`, `h_in_D`, `h_cover_D`) plus the
Spa-level no-common-zero witness obtain `hZavyalov_per_E` directly.
Sorry-free; one-line composition of two existing lemmas. -/
theorem hZavyalov_per_E_from_candidate_family_construction
    [DecidableEq A] [IsHuberRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺ : Subring A)] (P : PairOfDefinition A)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (C : RationalCoveringData A)
    (mk_S_D : RationalLocData A → Finset A)
    (h_in_D : ∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s)
    (h_cover_D : ∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
      ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s)
    (h_no_common_zero : ∀ v ∈ Spa A A⁺,
      ∃ f ∈ C.covers.biUnion mk_S_D, ¬ v.vle f 0) :
    rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S :=
  hZavyalov_per_E_of_per_D_construction C mk_S_D h_in_D h_cover_D
    (zavyalov_candidate_family_h_span_from_no_common_zero P hAplus_le_A₀ C mk_S_D
      h_no_common_zero)

/-! ### Precise missing sublemma: `exists_zavyalov_candidate_family`

**Target signature (NOT PROVED — recorded as the precise external
obligation).** With the hypothesis-gap (O1) explicitly listed, the
unconditional Zavyalov §2.3 output is:

```
theorem exists_zavyalov_candidate_family
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A] (P : PairOfDefinition A)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A,
      letI : ValuativeRel A := v.toValuativeRel
      MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCoveringData A) (hne : C.covers.Nonempty) :
    ∃ mk_S_D : RationalLocData A → Finset A,
      (∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
        rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s) ∧
      (∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
        ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s) ∧
      ∀ v ∈ Spa A A⁺,
        ∃ f ∈ C.covers.biUnion mk_S_D, ¬ v.vle f 0
```

**Mathematical content (Zavyalov §2.3 / Wedhorn 8.34(ii)).** For each
`D ∈ C.covers` and each `t ∈ D.T`, the ratio `t / D.s` lives in the
localization `Localization.Away D.s` but not in `A`. The construction
multiplies by a power of the dominating unit `σ` from Cor 7.32 (applied
to a suitable test family with no common zero on `Spa`) to clear the
denominator: `f_{D, t} := σ^{-N} · t · D.s^{N-1}` for an appropriate
exponent `N`. The plus-piece-at-`f_{D,t}` is then designed to land in
`rationalOpen D.T D.s` (h_in_D), and varying `t ∈ D.T` covers
`rationalOpen D.T D.s` (h_cover_D). The Spa-level no-common-zero
follows from the dominating unit's strict-domination property.

**Where it slots in** (after a successful proof):

```
theorem zavyalov_candidate_family_per_D
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A] (P : PairOfDefinition A)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A,
      letI : ValuativeRel A := v.toValuativeRel
      MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCoveringData A) (hne : C.covers.Nonempty) :
    ∃ mk_S_D : RationalLocData A → Finset A,
      (∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
        rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s) ∧
      (∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
        ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s) ∧
      Ideal.span ((C.covers.biUnion mk_S_D : Finset A) : Set A) = ⊤ := by
  obtain ⟨mk_S_D, h_in_D, h_cover_D, h_no_common_zero⟩ :=
    exists_zavyalov_candidate_family P hAplus_le_A₀ hA₀_le π hI hπ_tn hπ_unit hArch C hne
  exact zavyalov_candidate_family_per_D_from_construction P hAplus_le_A₀ C mk_S_D
    h_in_D h_cover_D h_no_common_zero
```

**Dependencies once `exists_zavyalov_candidate_family` lands**:
* `Cor732.exists_dominating_unit` (Cor 7.32, `Cor732.lean:206`) — already
  PROVED. Provides the dominating unit `σ`.
* `Lemma745.exists_mem_spa_supp_ge_of_nonOpen_prime` (Lemma 7.45,
  `Lemma745.lean:691`) — already PROVED. Provides Spa points at non-open
  primes (used inside `spanTop_iff_noCommonZero_spa`).
* `spanTop_iff_noCommonZero_spa` (Prop 7.14, line ~838) — already PROVED.
  Used by the wrappers above.
* The §2.3 ratio construction itself — UNFORMALISED. This is the only
  remaining mathematical content. -/

/-! ### Standard-cover reduction -/

/-! ### Structural factoring of the Nullstellensatz refinement (R1 refactor)

The Nullstellensatz refinement theorem decomposes into three cases on the
structure of `C`:

* **`exists_nullstellensatz_refinement_of_rationalOpen_empty`** — provable:
  when `rationalOpen C.base.T C.base.s = ∅` and `C.covers` is nonempty,
  take `S = {1}`. Clauses 1 and 2 are vacuous; Clause 3 holds by
  `Ideal.span {1} = ⊤`.

* **`exists_nullstellensatz_refinement_of_empty_covers`** — pathological
  edge case: `C.covers = ∅` with `[Nontrivial A]`. Forces
  `rationalOpen C.base.T C.base.s = ∅` via `C.hcover`, but then any nonempty
  `S` fails Clause 2 (needs `D ∈ ∅`) and `S = ∅` fails Clause 3
  (`Ideal.span ∅ = ⊥ ≠ ⊤`). Genuine `sorry` for this edge case.

* **`exists_nullstellensatz_refinement_of_rationalOpen_nonempty`** — the
  *only* mathematically-substantive sorry (Zavyalov §2.3 / Wedhorn
  Prop 7.14 + Lemma 7.44).

The assembly theorem `exists_nullstellensatz_refinement` dispatches on
`C.covers.Nonempty` and then on `rationalOpen = ∅`. -/

/-- **Degenerate branch.** When the base rational open is empty (e.g., when
`C.base.s = 0`) and `C.covers` is nonempty, Clauses 1 and 2 are vacuous, and
any `D ∈ C.covers` suffices to witness Clause 2 for `S = {1}` (which satisfies
Clause 3 by `Ideal.span {1} = ⊤`). -/
private theorem exists_nullstellensatz_refinement_of_rationalOpen_empty
    [DecidableEq A] (C : RationalCoveringData A)
    (hne : C.covers.Nonempty)
    (hempty : rationalOpen C.base.T C.base.s = ∅) :
    ∃ S : Finset A, refines_cover C S ∧ refines_contain C S ∧ refines_span_top S := by
  refine ⟨{1}, ?_, ?_, ?_⟩
  · -- Covering: vacuous, the base rational open is empty.
    intro v hv
    rw [hempty] at hv
    exact absurd hv (Set.notMem_empty _)
  · -- Containment: pick any `D ∈ C.covers`; the plus-piece at any `f` is
    -- contained in `rationalOpen C.base.T C.base.s = ∅ ⊆ rationalOpen D.T D.s`.
    intro f _
    obtain ⟨D, hD⟩ := hne
    refine ⟨D, hD, ?_⟩
    intro v hv
    have hle : rationalOpen (insert f C.base.T) C.base.s ⊆
        rationalOpen C.base.T C.base.s := by
      intro w ⟨hwspa, hwT, hws⟩
      exact ⟨hwspa, fun t ht ↦ hwT t (Finset.mem_insert_of_mem ht), hws⟩
    exact absurd (hle hv) (hempty ▸ Set.notMem_empty v)
  · -- Unit ideal: span {1} = ⊤.
    change Ideal.span (({1} : Finset A) : Set A) = ⊤
    rw [Finset.coe_singleton, Ideal.span_singleton_one]

/-- **Pathological edge case eliminated**: `C.covers = ∅` together with
`[Nontrivial A]` and `hne : C.covers.Nonempty` gives an immediate
contradiction. Retained as a private helper so the main dispatcher
`exists_nullstellensatz_refinement` can use it uniformly. -/
private theorem exists_nullstellensatz_refinement_of_empty_covers
    [DecidableEq A] [Nontrivial A]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty) (hcov : C.covers = ∅) :
    ∃ S : Finset A, refines_cover C S ∧ refines_contain C S ∧ refines_span_top S := by
  exfalso
  obtain ⟨D, hD⟩ := hne
  rw [hcov] at hD
  exact Finset.notMem_empty D hD

/-- **The genuine Nullstellensatz obligation**: the *nonempty-rational-open*
case of `exists_nullstellensatz_refinement`, with `C.covers` nonempty. This
isolates the Zavyalov §2.3 + Wedhorn Prop 7.14/Lemma 7.44 construction from
the degenerate empty-rational-open case and the pathological empty-covers
edge case.

**Proof strategy (Wedhorn Lemma 8.34(ii) via Cor 7.32).**

The core mathematical content is split into two pieces:

1. **Cor 7.32 (`ValuationSpectrum.exists_dominating_unit` in
   `Cor732.lean`, proved 2026-04-16):** Given a finite family `T ⊂ A`
   with no common zero on `Spa A A⁺`, produce a unit `s ∈ Aˣ` such that
   for each `v ∈ Spa`, some `t ∈ T` satisfies `v(s) < v(t)` strictly.
   This is the *dominating-unit extraction*.

2. **Zavyalov §2.3 candidate family:** Given the dominating unit `s`, the
   refinement family `S := {s⁻¹ · t : t ∈ T}` satisfies the three
   clauses — conditional on the adic Nullstellensatz (Wedhorn
   Prop 7.14) providing a suitable ingredient `T ⊂ A` whose elements
   simultaneously (a) have no common zero on `Spa`, (b) correspond to
   ratios `tⱼ/Dⱼ.s` for each cover piece `Dⱼ`, and (c) generate the
   unit ideal in `A`.

**Why Cor 7.32 alone does not suffice.** The obstruction lies in step 2
above: Cor 7.32 needs a *Spa-level* no-common-zero family, but the
natural candidates `⋃ Dⱼ.T`, `{Dⱼ.s}`, `{C.base.s} ∪ ⋃ Dⱼ.T` have no
common zero only on `rationalOpen C.base.T C.base.s`, not on all of
`Spa`. Closing this gap requires either

  (i) the non-open-prime Spa-point construction
      (`Lemma745.exists_mem_spa_supp_ge_of_nonOpen_prime`, reachable
      here via `Presheaf → Prop752 → Lemma745`), combined with the
      open-prime route
      `StructureSheaf.exists_spa_point_in_rationalOpen_of_isOpen_prime`;

  (ii) or a direct localization argument on `Localization.Away C.base.s`
       where the analogous span-top statement is provable (see
       `TateAcyclicity.lean:475` for the discrete specialization).

**Current formalization (Option B per the 2026-04-16 plan).** The
present statement takes as an extra hypothesis `hZavyalov` the output
of the Zavyalov §2.3 construction — namely, the existence of the
refining family `S`. This makes explicit the two missing ingredients
that reduce the obligation to Cor 7.32 alone:

* The `hSpa_nozero` hypothesis asserts the existence of a *Spa-level*
  no-common-zero finite family (the "extended test family"), obtained
  from the cover condition via the adic Nullstellensatz and the
  Spa-point constructions (i) and (ii) above. This is the
  *non-trivially-hard* missing step.

* Given `hSpa_nozero`, the dominating unit `s` from Cor 7.32 together
  with the Zavyalov ratio construction produces `S`, and this is the
  content `hZavyalov` captures.

Future work: replace `hZavyalov` with an inlined construction once
Lemma 7.45 / Prop 7.14 landing yields the `hSpa_nozero` ingredient
unconditionally.

**2026-04-14 analysis of candidate families.** Three natural candidate
sets were evaluated; all fail at least one clause:

* `S := C.covers.image (·.s)` — succeeds in the *discrete* case (see
  `TateAcyclicity.lean:475`) but fails **Clause 2** in the Tate case:
  `rationalOpen (insert D.s C.base.T) C.base.s ⊆ rationalOpen D.T D.s`
  is **false in general** — the plus-piece at `D.s` in the *base*
  needs not land in the cover piece `D`.

* `S := {C.base.s}` — trivially satisfies **Clause 1** (by
  `rationalOpen_insert_s`) but fails **Clause 3** unless
  `C.base.s` is a unit, and fails **Clause 2** unless
  `C.base ∈ C.covers`.

* `S := {1}` — trivially satisfies **Clause 3** but fails
  **Clause 1**: requires `v(1) = 1 ≤ v(C.base.s)`, i.e.
  `v(C.base.s) ≥ 1`, which can fail (e.g. when `C.base.s`
  is a topological nilpotent).

The correct candidate is built by Zavyalov §2.3 from products
`tⱼ/Dⱼ.s` (via the adic Nullstellensatz, Prop 7.14) so that the
plus-piece at each `fᵢ` is *designed* to land in a specific
cover piece `Dⱼ`.

**Caller obligation.** The `hne_rat` hypothesis exposes that the meaningful
work happens only when the base rational open is nonempty; callers in the
empty case should use
`exists_nullstellensatz_refinement_of_rationalOpen_empty`.

The `hZavyalov` hypothesis bundles the existence of the refining
family `S` produced by the Zavyalov §2.3 construction (Cor 7.32
dominating-unit + Prop 7.14 adic Nullstellensatz). Downstream callers
(`RationalCoveringData.refines_by_standard_cover`) thread the same
hypothesis, exposing the remaining obligation explicitly. -/
private theorem exists_nullstellensatz_refinement_of_rationalOpen_nonempty
    [DecidableEq A]
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [Nontrivial A]
    (C : RationalCoveringData A) (_hne : C.covers.Nonempty)
    (_hne_rat : rationalOpen C.base.T C.base.s ≠ ∅)
    -- Zavyalov §2.3 existence hypothesis: the output of Wedhorn Lemma 8.34(ii),
    -- combining Cor 7.32's dominating-unit extraction with the adic
    -- Nullstellensatz (Prop 7.14). Callers obtain this from the compactness
    -- infrastructure and the Spa-point constructions; see the docstring above
    -- for the mathematical content and the obstruction preventing a direct
    -- Cor 7.32-only proof.
    (hZavyalov : ∃ S : Finset A,
      refines_cover C S ∧ refines_contain C S ∧ refines_span_top S) :
    ∃ S : Finset A, refines_cover C S ∧ refines_contain C S ∧ refines_span_top S :=
  hZavyalov

/-- **Key Nullstellensatz claim** (Wedhorn Prop 7.14 / Lemma 7.44):
for a rational cover of a strongly noetherian Tate ring, there exists a
finite family `S ⊂ A` satisfying **all three clauses** of the
standard-cover reduction (see `refines_cover`, `refines_contain`,
`refines_span_top`).

**Mathematical content.** This is the adic Nullstellensatz applied to
the cover condition. Zavyalov §2.3 builds `S` from ratios `tⱼ/Dⱼ.s`
pulled back to `A` via the Nullstellensatz; the resulting family has all
three properties simultaneously.

**Status (2026-04-16, Option B).** This theorem is an assembly of two
sub-lemmas dispatched on `rationalOpen C.base.T C.base.s = ∅`:

* Empty branch: closed via `..._of_rationalOpen_empty` (uses `S = {1}`,
  clauses 1 and 2 vacuous).
* Nonempty branch: closed via `..._of_rationalOpen_nonempty` given the
  `hZavyalov` hypothesis, which bundles the Wedhorn Lemma 8.34(ii)
  construction (Cor 7.32 dominating-unit + adic Nullstellensatz
  Prop 7.14). See that theorem's docstring for the obstruction
  preventing a direct Cor 7.32-only proof.

The pathological `C.covers = ∅` branch is excluded by the `hne`
hypothesis.

**Closely-related proven result.** `TateAcyclicity.lean:475` contains the
analogous span-top argument at `Localization.Away C.base.s` (producing
`Ideal.span {algebraMap D.s | D ∈ C.covers} = ⊤` there). That proof is
discrete-specific because it uses `isOpen_discrete _` to satisfy the
continuity condition of the trivial-valuation construction (the
discrete-topology lets every valuation be continuous). For the Tate case,
the analogous step requires `exists_spa_point_in_rationalOpen_of_nonOpen_prime`
(per Wedhorn Lemma 7.45, currently tracked by the
`project_T001_completion_route` memory and blocked on Bourbaki CA III §2.8).
The OPEN prime sub-case is already available via
`exists_spa_point_in_rationalOpen_of_isOpen_prime`.

**Pieces of the helper that ARE available.**
- **Clause 3** (span-top in `Localization.Away C.base.s`) for the candidate
  set `S := C.covers.image (·.s)` is mostly provable from the OPEN-prime
  Spa-point construction; the non-open prime case needs Lemma 7.45.
- **Clause 1** (cover): follows from `C.hcover v` composed with a "plus-piece
  at `D.s` contains `rationalOpen D.T D.s` inside the base" lemma. The
  precise form depends on the normalization and is not yet factored out.
- **Clause 2** (containment): the hard direction — requires the plus-piece
  `rationalOpen (insert D.s C.base.T) C.base.s` to be inside `rationalOpen
  D.T D.s`. This is NOT automatic — it requires a Nullstellensatz-style
  argument (Zavyalov §2.3) producing the `fᵢ` specifically so that the
  plus-piece at `fᵢ` is exactly (or inside) some `Dⱼ` piece. This is the
  genuinely new ingredient.

**Nontriviality hypothesis.** The `[Nontrivial A]` hypothesis is cosmetic:
when `A` is subsingleton, the main theorem is handled by a separate branch
using `S.elts = ∅`. Keeping the hypothesis here simplifies the nontrivial
branch of the main proof. -/
private theorem exists_nullstellensatz_refinement
    [DecidableEq A]
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [Nontrivial A]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    -- Zavyalov §2.3 existence hypothesis for the nonempty-rational-open branch.
    -- See `exists_nullstellensatz_refinement_of_rationalOpen_nonempty` for the
    -- mathematical content.
    (hZavyalov : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A, refines_cover C S ∧ refines_contain C S ∧ refines_span_top S) :
    ∃ S : Finset A, refines_cover C S ∧ refines_contain C S ∧ refines_span_top S := by
  -- `hne` eliminates the pathological empty-covers branch; remaining dispatch is
  -- on whether the base rational open is empty.
  by_cases hempty : rationalOpen C.base.T C.base.s = ∅
  · exact exists_nullstellensatz_refinement_of_rationalOpen_empty C hne hempty
  · -- Meaningful case: `rationalOpen C.base.T C.base.s` is nonempty.
    -- This is the genuine Nullstellensatz obligation (Zavyalov §2.3 /
    -- Wedhorn Prop 7.14 + Lemma 7.44), supplied via `hZavyalov`.
    exact exists_nullstellensatz_refinement_of_rationalOpen_nonempty C hne hempty
      (hZavyalov hempty)

/-- **Wedhorn / Zavyalov standard-cover reduction** (Theorem 8.28(b) step,
ticket R1 of the 2026-04-14 plan).

Any rational covering of the base `C.base` admits a refinement by a
*standard cover* `S = {f₀, …, fₙ}` in the following sense:

* `Ideal.span (S.elts : Set A) = ⊤` (unit ideal);
* the plus-type pieces `rationalOpen (insert fᵢ C.base.T) C.base.s` cover
  `rationalOpen C.base.T C.base.s` (by valuation trichotomy, using
  `∑ aᵢ fᵢ = 1`);
* each plus-piece `rationalOpen (insert fᵢ C.base.T) C.base.s` is contained
  in some piece `Dⱼ ∈ C.covers` of the original covering.

This reduces Tate acyclicity for arbitrary rational coverings to the case
of standard covers, where Laurent-cover induction applies.

**Proof strategy** (see Zavyalov §2 / Wedhorn Lemma 8.34):

1. For each `v ∈ rationalOpen C.base.T C.base.s`, the covering property
   `C.hcover v` produces some `Dⱼ ∈ C.covers` containing `v`.
2. The finite family `{Dⱼ}` has enough "test elements" from the `Dⱼ.T`
   data to build candidate `fᵢ`. Concretely, one takes a finite family of
   ratios `t/Dⱼ.s` (for `t ∈ Dⱼ.T`) along with units produced by
   Wedhorn's adic Nullstellensatz (Prop 7.14) to extract an `fᵢ` such that
   each `v` is covered by `insert fᵢ C.base.T / C.base.s` inside `Dⱼ`.
3. Strong Nullstellensatz (Wedhorn 7.14) then gives `Ideal.span S.elts = ⊤`.
4. The containment of each plus-piece in some `Dⱼ` comes from the
   construction in step 2. -/
theorem RationalCoveringData.refines_by_standard_cover
    [DecidableEq A]
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    -- Zavyalov §2.3 existence hypothesis for the nonempty-rational-open branch.
    -- See `exists_nullstellensatz_refinement_of_rationalOpen_nonempty` for
    -- the mathematical content. Downstream callers obtain this from Cor 7.32
    -- combined with the adic Nullstellensatz (Wedhorn Prop 7.14 / Lemma 7.44).
    (hZavyalov : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A, refines_cover C S ∧ refines_contain C S ∧ refines_span_top S) :
    ∃ S : StandardCover A,
      -- The plus-type pieces at elements of `S` cover the base rational open.
      (∀ v ∈ rationalOpen C.base.T C.base.s,
        ∃ f ∈ S.elts, v ∈ rationalOpen (insert f C.base.T) C.base.s) ∧
      -- Each plus-type piece is contained in some piece of the original cover.
      (∀ f ∈ S.elts, ∃ D ∈ C.covers,
        rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s) := by
  -- Dispatch on whether `A` is subsingleton (zero ring).
  by_cases hA : Subsingleton A
  · -- In the zero ring, the unit ideal equals the zero ideal, so the empty set
    -- spans `⊤`. Both the covering and containment conditions are vacuous.
    refine ⟨⟨∅, ?_⟩, ?_, ?_⟩
    · -- `Ideal.span (∅ : Set A) = ⊤` because in a subsingleton ring `⊥ = ⊤`.
      rw [Finset.coe_empty, Ideal.span_empty]
      exact Subsingleton.elim _ _
    · -- Covering: vacuous because we'd need a `v` satisfying `v.vle s 0` being
      -- false, but `s = 0` in the zero ring.
      intro v hv
      -- `v ∈ rationalOpen _ s` requires `¬ v.vle s 0`, but `s = 0`, so
      -- `v.vle 0 0` holds (reflexivity). Contradiction.
      exfalso
      have : C.base.s = 0 := Subsingleton.elim _ _
      exact hv.2.2 (this ▸ v.vle_refl 0)
    · -- Containment: vacuous because `S.elts = ∅`.
      intro f hf
      simp at hf
  · -- Nontrivial `A`. Apply the Nullstellensatz refinement helper directly.
    haveI hNT : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
    obtain ⟨S, hS_cover, hS_contain, hS_span⟩ :=
      exists_nullstellensatz_refinement C hne hZavyalov
    exact ⟨⟨S, hS_span⟩, hS_cover, hS_contain⟩

/-! ### Strengthened refinement chain: per-E precise standard-cover

For the S-GEOM-ASM Lane B pipeline (`GeometricReduction.lean`'s
`per_E_local_covering`), we need the per-E precise assignment
`refines_cover_per_E C S` rather than just the weakest-form
`refines_cover C S` + `refines_contain C S`. The Wedhorn/Hübner
construction inherently produces the per-E assignment (each `f` is
designed to target a specific `D = E`), but
`refines_by_standard_cover` above packages this under the weaker
hypothesis `hZavyalov`.

We therefore provide a **parallel private helper chain** mirroring
`exists_nullstellensatz_refinement{_of_rationalOpen_empty,_of_rationalOpen_nonempty}`,
but with the strengthened hypothesis and output. The nonempty-branch
helper is a passthrough of `hZavyalov_per_E` (the existing Wedhorn
construction is a black box that the caller supplies); the empty-branch
helper is a direct `S = {1}` witness that trivially satisfies per-E
covering (since every `E ⊆ base = ∅`). The public
`refines_by_standard_cover_per_E` dispatches via the chain just like
`refines_by_standard_cover` dispatches via the unstrengthened chain. -/

/-- **Per-E variant**: empty-rational-open branch. When the base
rational open is empty, every `E ∈ C.covers` has
`rationalOpen E.T E.s ⊆ rationalOpen C.base.T C.base.s = ∅` (via
`C.hsubset`), so the per-E covering condition is vacuous. `S = {1}`
witnesses all three clauses. -/
private theorem exists_nullstellensatz_refinement_per_E_of_rationalOpen_empty
    [DecidableEq A] (C : RationalCoveringData A)
    (hne : C.covers.Nonempty)
    (hempty : rationalOpen C.base.T C.base.s = ∅) :
    ∃ S : Finset A,
      refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S := by
  refine ⟨{1}, ?_, ?_, ?_⟩
  · -- Per-E covering: vacuous, `E.1 ⊆ base ⊆ ∅`.
    intro E hE v hv
    have hv_base : v ∈ rationalOpen C.base.T C.base.s := C.hsubset E hE hv
    exact absurd (hempty ▸ hv_base) (Set.notMem_empty v)
  · -- Containment: pick any `D`; plus-piece-at-1 ⊆ base = ∅ ⊆ D.
    intro f _hf
    obtain ⟨D, hD⟩ := hne
    refine ⟨D, hD, ?_⟩
    intro v hv_in_plus
    have hv_base : v ∈ rationalOpen C.base.T C.base.s := by
      obtain ⟨hvspa, hv_T, hv_s⟩ := hv_in_plus
      exact ⟨hvspa, fun t ht ↦ hv_T t (Finset.mem_insert_of_mem ht), hv_s⟩
    exact absurd (hempty ▸ hv_base) (Set.notMem_empty v)
  · -- Span-top: `Ideal.span {1} = ⊤`.
    change Ideal.span (({1} : Finset A) : Set A) = ⊤
    rw [Finset.coe_singleton, Ideal.span_singleton_one]

/-- **Per-E variant**: nonempty-rational-open branch. Passthrough of
the strengthened `hZavyalov_per_E` hypothesis. The Wedhorn/Hübner
construction of the refining family naturally produces the per-E
assignment (each `f` is built targeting a specific `D = E`);
`hZavyalov_per_E` packages this existence. -/
private theorem exists_nullstellensatz_refinement_per_E_of_rationalOpen_nonempty
    [DecidableEq A]
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [Nontrivial A]
    (C : RationalCoveringData A) (_hne : C.covers.Nonempty)
    (_hne_rat : rationalOpen C.base.T C.base.s ≠ ∅)
    (hZavyalov_per_E : ∃ S : Finset A,
      refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S) :
    ∃ S : Finset A,
      refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S :=
  hZavyalov_per_E

/-- **Per-E variant**: dispatcher over empty/nonempty rational open.
Mirrors `exists_nullstellensatz_refinement` with the strengthened
`refines_cover_per_E` output. The pathological `C.covers = ∅` branch
is eliminated by `hne`. -/
private theorem exists_nullstellensatz_refinement_per_E
    [DecidableEq A]
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [Nontrivial A]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S) :
    ∃ S : Finset A,
      refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S := by
  by_cases hempty : rationalOpen C.base.T C.base.s = ∅
  · exact exists_nullstellensatz_refinement_per_E_of_rationalOpen_empty C hne hempty
  · exact exists_nullstellensatz_refinement_per_E_of_rationalOpen_nonempty C hne hempty
      (hZavyalov_per_E hempty)

/-- **Strengthened variant of `refines_by_standard_cover`** with per-E
precise covering.

Takes a strengthened Zavyalov-existence hypothesis `hZavyalov_per_E`
bundling the per-E assignment. Produces a `StandardCover A` together
with `refines_cover_per_E C S.elts` and `refines_contain C S.elts`.

This is the input shape expected by
`GeometricReduction.per_E_local_covering` — the per-E covering gives,
for each `E ∈ C.covers` and each `v` in `E`'s rational open, a specific
`f ∈ S.elts` whose plus-piece-at-f is contained in that same `E`.

**Architectural note**: the proof dispatches on zero-ring vs nontrivial,
then threads through `exists_nullstellensatz_refinement_per_E` —
mirroring the existing `refines_by_standard_cover` chain with the
strengthened predicate. -/
theorem RationalCoveringData.refines_by_standard_cover_per_E
    [DecidableEq A]
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S) :
    ∃ S : StandardCover A,
      refines_cover_per_E C S.elts ∧
      refines_contain C S.elts := by
  by_cases hA : Subsingleton A
  · -- Zero-ring branch: `S.elts = ∅` satisfies everything vacuously.
    refine ⟨⟨∅, ?_⟩, ?_, ?_⟩
    · rw [Finset.coe_empty, Ideal.span_empty]
      exact Subsingleton.elim _ _
    · intro E _hE v hv
      exfalso
      have : E.s = 0 := Subsingleton.elim _ _
      exact hv.2.2 (this ▸ v.vle_refl 0)
    · intro f hf
      simp at hf
  · -- Nontrivial `A`: dispatch via the strengthened refinement helper chain.
    haveI hNT : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
    obtain ⟨S, hS_per_E, hS_contain, hS_span⟩ :=
      exists_nullstellensatz_refinement_per_E C hne hZavyalov_per_E
    exact ⟨⟨S, hS_span⟩, hS_per_E, hS_contain⟩

/-! ### Acyclicity via standard covers -/

/-- **Acyclicity via standard-cover reduction** (ticket R1 of the 2026-04-14
plan).

Once a rational covering is refined to a standard cover (via
`RationalCoveringData.refines_by_standard_cover`), the Tate acyclicity
(separation + gluing) transfers from the Laurent-cover induction to the
original covering.

This is the scaffold for the replacement of `tateAcyclicity` in
`LaurentRefinement.lean:801`. The statement shape mirrors that of
`tateAcyclicity`, differing only in the proof route: it goes through the
standard-cover reduction (R1), avoiding the Spa-point-at-non-open-prime
route (original Phase 1/5a) which was blocked on Bourbaki CA III §2.8.

**Proof strategy**:

1. Apply `RationalCoveringData.refines_by_standard_cover` to produce `S : StandardCover A`.
2. Perform induction on `S.elts.card`:
   * base case `n = 1`: `{f}` with `Ideal.span {f} = ⊤` means `f` is a
     unit, so the plus-piece at `f` is the whole base and acyclicity is
     trivial;
   * inductive step `n + 1`: pick an `f ∈ S.elts` and apply the 2-element
     Laurent cover gluing `laurentCover_gluing_presheaf` at `f` to reduce
     to the acyclicity of the smaller standard cover on each Laurent half.
3. Transfer the acyclicity back to `C` via Proposition A.3 of Wedhorn
   (scaffolded as `separation_of_finer_rational` in `RationalRefinement.lean`). -/
theorem tateAcyclicity_via_standard_cover
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    [HasLocLiftPowerBounded A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty) :
    -- Part 1: Separation (zero kernel).
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    -- Part 2: Gluing.
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) :=
  -- The statement of `tateAcyclicity_via_standard_cover` matches that of
  -- `tateAcyclicity` (LaurentRefinement.lean:801) bit-for-bit; it is named
  -- separately only to document the INTENDED proof route (refinement by a
  -- standard cover, followed by Laurent-cover induction), which the R1 ticket
  -- is meant to carry out. Until the standard-cover reduction is complete
  -- (see `RationalCoveringData.refines_by_standard_cover` above), this theorem is
  -- implemented by delegating to `tateAcyclicity` — carrying over the single
  -- upstream sorry in `tateAcyclicity` Part 2 (gluing via partition-of-unity)
  -- rather than introducing a second independent one.
  tateAcyclicity P C hne

end ValuationSpectrum

end

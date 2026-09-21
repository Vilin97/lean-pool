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
import LeanPool.UniformSheafyTateDomains.AdicSpaces.LaurentOverlapConsumer
import LeanPool.UniformSheafyTateDomains.AdicSpaces.RationalRefinement
import LeanPool.UniformSheafyTateDomains.AdicSpaces.StandardCover

/-!
# Geometric reduction: from Laurent-cover acyclicity to arbitrary-cover acyclicity

This file implements the **geometric-reduction front** (ticket T-GEOM-RED)
of the `tateAcyclicity` closure plan. Its role: given exactness on every
simple Laurent cover (provided by `laurentCover_gluing_presheaf`, modulo
`laurentOverlapBridge_exists_compatible` = T-OV-1), produce exactness on
arbitrary finite rational covers.

This corresponds to **Hübner's Lemma 3.8** (arXiv 2405.06435): a pair is
sheafy and acyclic iff exactness holds for every simple Laurent covering
of every rational open. The reverse direction (assumed here) is the
content of this file.

## Preferred downstream route (S-GEOM-ASM, direct per-E)

Downstream callers closing `tateAcyclicity` Part 2 should use the
**direct per-E Part-2 assembly route**. The canonical entry points are:

* **`tateAcyclicity_Part2_via_hZavyalov_per_E_direct`** — the caller
  wrapper consuming the strengthened `hZavyalov_per_E` existence
  hypothesis (from `StandardCover.refines_by_standard_cover_per_E`) plus
  universal Lane A/Lane B suppliers. This is the recommended API for
  `LaurentRefinement.lean:3737` and any other Part-2 consumer.

* **`tateAcyclicity_Part2_direct_per_E`** — the core direct-per-E
  assembly that the caller wrapper invokes. Takes the standard cover
  `S` + refinement predicates directly (for callers who have `S`
  in hand).

The direct per-E route uses the canonical `StandardCover.refines_cover_per_E`
predicate and the per-E local covering `per_E_local_covering` to bypass
the τ/Classical.choose bridge entirely — `hE_sep_direct` on the per-E
local covering is directly the Cor 8.32 output shape.

## Historical τ-route (superseded, kept for reference)

The original τ-based route — `tateAcyclicity_Part2_assembly`,
`tateAcyclicity_Part2_via_refined_geometric_reduction`,
`tateAcyclicity_Part2_via_geometric_reduction` — is kept for reference
but **superseded by the direct per-E route** for new downstream
development. The τ-route goes through `gluing_of_finer_rational` with
a Classical.choose-based refinement map on `refinedVCovers`, which
introduces a local proof-irrelevance nuisance on the τ-image equation.
The direct per-E route avoids this by consuming the per-E assignment
supplied by the upstream `refines_by_standard_cover_per_E` API.

## Remaining external blockers (as of 2026-04-20)

Geometric-lane theorems are theorem-sized and axiom-clean modulo the
following external dependencies (tracked in `.mathlib-quality/tickets.md`):

1. **Lane A** (T-OV-1 / T-OVERLAP-COMPAT) — `laurentCover_gluing_presheaf`
   sorry in `LaurentRefinement.lean:3173`. Discharges `hV_glue_refined`
   for the direct per-E route.
2. **Lane B** (T-IDEAL-2 / Cor 8.32 per-E) — per-E invocation of
   `productRestriction_injective_tate_via_prime_extension_closed`
   (`Cor832.lean:1581`). Discharges `hE_sep_direct` on each
   `per_E_local_covering`.
3. **T-NULL-PER-E** (Prop 7.14 / Zavyalov §2.3) — the general-case
   Nullstellensatz construction producing `hZavyalov_per_E` for
   multi-piece covers. UNFORMALISED. The singleton-cover supplier
   `exists_nullstellensatz_refinement_per_E_of_singleton_cover` in
   `StandardCover.lean` is the only currently-available discharge.

## Key deliverables (current state)

* **`tateAcyclicity_gluing_via_refinement_cover_level`** — cover-level
  gluing via `gluing_of_finer_rational` with `hE_sep`. Supersedes the
  2026-04-18-retired single-map-injectivity route.

* **Refined V-cover infrastructure** — `refinedVCovers`,
  `mem_refinedVCovers`, `refinedVCovers_subset_base`,
  `refinedVCovers_covers`, `refinedVCovers_plusMinus_dichotomy`,
  `refinedVCoversTau` + subset. Axiom-clean.

* **Per-E local covering** — `per_E_local_covering`,
  `mem_per_E_local_covering_covers`, `refinedVCovers_at` +
  characterisation. Axiom-clean.

* **Direct per-E Part-2 assembly** — `tateAcyclicity_Part2_direct_per_E`
  + `tateAcyclicity_Part2_via_hZavyalov_per_E_direct`. Axiom-clean
  modulo transitively-inherited upstream `sorryAx` from
  `LaurentRefinement.lean:3173`.

## References

* [Hübner, *Adic spaces* (arXiv 2405.06435), Lemma 3.7, Lemma 3.8]
* [T. Wedhorn, *Adic Spaces* (2019 lecture notes), Lemma 8.33, Lemma 8.34]
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsHuberRing A] [HasLocLiftPowerBounded A]

/-- **Cover-level variant of `tateAcyclicity_gluing_via_refinement`**
(corrected 2026-04-18 per reviewer guidance).

The earlier `tateAcyclicity_gluing_via_refinement`
(`LaurentRefinement.lean:3605`) invoked `restrictionMapHom_injective`
at line 3638 to discharge the local-separation step. Reviewer
counterexample: `A = k⟨T,U⟩/(TU)`, `U = R(1/T)`; then
`𝒪_X(U) ≅ A⟨X⟩/(1-TX)`, and the class of `U ∈ A` maps to
`U = U·(TX) = (UT)·X = 0`, killing a nonzero element. So individual
restriction maps are **not injective in general**, and the earlier
theorem is unsound outside settings where single-map injectivity
happens to hold.

This variant replaces the illegal `hτ_surj + single-map-injectivity`
step with the correct cover-level hypothesis `hE_sep` from
`gluing_of_finer_rational`: for each `E ∈ C.covers`, separation on
`presheafValue E.1` via the restriction maps to those V-pieces `d`
with `τ d = E`.

**Discharging `hE_sep`**. The hypothesis `hE_sep` holds when, for
each `E`, the V-pieces refining `E` form a sub-covering of `E` and the
associated product-restriction map
`presheafValue E.1 → ∏_{d refining E} presheafValue d.1` is injective.
In the Wedhorn Cor 8.32 framework this is faithful flatness at the
`E`-level sub-cover, which reduces to `coeRingHom_preserves_proper`
(ticket T-IDEAL-2) applied at `E` rather than at `C.base`.

**Relationship to the unsound earlier theorem**. The earlier variant
is strictly stronger *only* when single-map injectivity holds (which
the reviewer counterexample shows is not a theorem). This corrected
variant is logically stronger in the correct direction: it no longer
assumes a false statement. -/
theorem tateAcyclicity_gluing_via_refinement_cover_level
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (C : RationalCoveringData A)
    (V_covers : Finset (RationalLocData A))
    (hV_subset : ∀ D ∈ V_covers, rationalOpen D.T D.s ⊆
      rationalOpen C.base.T C.base.s)
    (τ : { D // D ∈ V_covers } → { E // E ∈ C.covers })
    (hτ : ∀ d : { D // D ∈ V_covers },
      rationalOpen d.1.T d.1.s ⊆ rationalOpen (τ d).1.T (τ d).1.s)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (hV_glue : ∀ (fV : ∀ D : { D // D ∈ V_covers }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ V_covers }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ V_covers },
        restrictionMap C.base D.1 (hV_subset D.1 D.2) x = fV D)
    (hE_sep : ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (d : { D // D ∈ V_covers }) (hd : τ d = E),
        restrictionMap E.1 d.1 (hd ▸ hτ d) a =
          restrictionMap E.1 d.1 (hd ▸ hτ d) b) → a = b) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  gluing_of_finer_rational C V_covers hV_subset τ hτ fC hC_compat hV_glue hE_sep

/-! ### Bridge from `refines_by_standard_cover` to the V_covers data

A `StandardCover A` produced by `refines_by_standard_cover` gives
`S.elts : Finset A` with span-top plus two existence clauses (covering
the base, containment in `C.covers`). To feed this into
`tateAcyclicity_gluing_via_refinement_cover_level` we need to convert
it into a `V_covers : Finset (RationalLocData A)` together with its
refinement map `τ`.

The plus-piece at each `f ∈ S.elts` is represented by `laurentPlusDatum
C.base f : RationalLocData A`, whose rational open equals
`rationalOpen (insert f C.base.T) C.base.s` by definitional unfold.
The helpers below package this construction.  -/

/-- The plus-piece rational data for an element `f` relative to a
rational covering `C`: exactly `laurentPlusDatum C.base f`. Its
`rationalOpen` equals `rationalOpen (insert f C.base.T) C.base.s`.
Introduced as an `abbrev` so projections (`.T`, `.s`) reduce transparently. -/
noncomputable abbrev RationalCoveringData.plusDatum (C : RationalCoveringData A)
    (f : A) : RationalLocData A :=
  laurentPlusDatum C.base f

/-- Each plus-piece `C.plusDatum f` is contained in `C.base`'s rational
open — by `laurentPlus_subset`. -/
theorem RationalCoveringData.plusDatum_subset_base (C : RationalCoveringData A) (f : A) :
    rationalOpen (C.plusDatum f).T (C.plusDatum f).s ⊆
      rationalOpen C.base.T C.base.s :=
  laurentPlus_subset C.base f

/-- The V-covers finset built from a standard-cover refinement: the image
of `S.elts` under `C.plusDatum`. Uses `Classical.decEq` since
`RationalLocData A` does not carry decidable equality in general. -/
noncomputable def RationalCoveringData.standardCoverVCovers
    (C : RationalCoveringData A) (S : Finset A) :
    Finset (RationalLocData A) :=
  letI : DecidableEq (RationalLocData A) := Classical.decEq _
  S.image C.plusDatum

omit [HasLocLiftPowerBounded A] in
/-- Membership in `standardCoverVCovers`: an element `D` is in the V-covers
iff it equals `C.plusDatum f` for some `f ∈ S`. -/
theorem RationalCoveringData.mem_standardCoverVCovers
    (C : RationalCoveringData A) (S : Finset A) {D : RationalLocData A} :
    D ∈ C.standardCoverVCovers S ↔ ∃ f ∈ S, C.plusDatum f = D := by
  letI : DecidableEq (RationalLocData A) := Classical.decEq _
  change D ∈ (S.image C.plusDatum) ↔ _
  exact Finset.mem_image

/-- Each element of `standardCoverVCovers S` is contained in `C.base`. -/
theorem RationalCoveringData.standardCoverVCovers_subset_base
    (C : RationalCoveringData A) (S : Finset A) (D : RationalLocData A)
    (hD : D ∈ C.standardCoverVCovers S) :
    rationalOpen D.T D.s ⊆ rationalOpen C.base.T C.base.s := by
  obtain ⟨f, _, rfl⟩ := (C.mem_standardCoverVCovers S).mp hD
  exact C.plusDatum_subset_base f

/-! ### The standard-cover τ map (S-GEOM-TAU)

From `refines_contain C S` (clause 2 of `refines_by_standard_cover`) we
build a noncomputable refinement map
`τ : {D // D ∈ C.standardCoverVCovers S} → {E // E ∈ C.covers}` and
prove the rational-open containment
`rationalOpen d.1.T d.1.s ⊆ rationalOpen (τ d).1.T (τ d).1.s`.

**Approach**. The `T` field of `laurentPlusDatum` is built using
`Classical.decEq` (since `LaurentRefinement.lean` opens `Classical`
inside `noncomputable section`), but `refines_contain` uses the
explicit ambient `[DecidableEq A]` instance. The two `Finset.insert`
constructions are NOT syntactically equal, so `rfl` fails.

**Workaround taken here**: state the bridge lemma at the `rationalOpen`
level rather than the `Finset` level. `rationalOpen T s`'s definition
quantifies `∀ t ∈ T, …`, where `t ∈ T` is `Finset.mem`, and
`Finset.mem_insert` (`a ∈ insert b s ↔ a = b ∨ a ∈ s`) is
instance-agnostic at the Prop level. Both `(C.plusDatum f).T` and
`insert f C.base.T` (with different `DecidableEq` instances) have the
same membership characterization, so the two `rationalOpen`s are equal
as sets of valuations. -/

/-- **Extensional bridge**: the rational-open set computed from
`(C.plusDatum f).T` (which uses `Classical.decEq` inside the
`noncomputable` `laurentPlusDatum` definition) equals the rational-open
computed from `insert f C.base.T` (which uses the explicit ambient
`[DecidableEq A]`). The `.s` fields coincide definitionally.

The DecidableEq diamond between the two `insert`s is sidestepped at the
Prop level: membership in either yields the same disjunction
`a = f ∨ a ∈ C.base.T` via `Finset.mem_insert`, independent of instance. -/
theorem RationalCoveringData.rationalOpen_plusDatum_eq_insert
    [DecidableEq A] (C : RationalCoveringData A) (f : A) :
    rationalOpen (C.plusDatum f).T (C.plusDatum f).s =
      rationalOpen (insert f C.base.T) C.base.s := by
  ext v
  unfold rationalOpen
  simp only [Set.mem_setOf_eq]
  refine and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  refine forall_congr' fun t => ?_
  refine imp_congr ?_ Iff.rfl
  -- Goal: `t ∈ (C.plusDatum f).T ↔ t ∈ insert f C.base.T`.
  -- Both sides unfold to `t = f ∨ t ∈ C.base.T` via `Finset.mem_insert`.
  -- Use `simp only [Finset.mem_insert]` to bypass a `DecidableEq A` /
  -- `Classical.propDecidable` diamond between `(C.plusDatum f).T` (built
  -- with Classical) and the ambient `[DecidableEq A]` on `insert f C.base.T`.
  simp only [RationalCoveringData.plusDatum, laurentPlusDatum, Finset.mem_insert]

/-! ### The standard-cover τ refinement map (S-GEOM-TAU)

Given `refines_contain C S` (clause 2 of `refines_by_standard_cover`),
build a noncomputable refinement map sending each V-piece (= plus-datum
at some `f ∈ S`) to a cover piece `E ∈ C.covers` that contains it.

The construction uses `Classical.choose` on the existential in
`refines_contain` to pick an E for each f. The subset proof routes
through `rationalOpen_plusDatum_eq_insert` to bridge the DecidableEq
diamond. -/

omit [HasLocLiftPowerBounded A] in
/-- **The τ refinement map** (S-GEOM-TAU): each V-piece in
`standardCoverVCovers C S` maps to a cover piece `E ∈ C.covers`
containing it. Uses `Classical.choose` on the existential extracted via
`(C.mem_standardCoverVCovers S).mp d.2` and on the refinement witness. -/
noncomputable def RationalCoveringData.standardCoverVTau
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A)
    (hS_contain : refines_contain C S)
    (d : { d : RationalLocData A // d ∈ C.standardCoverVCovers S }) :
    { E : RationalLocData A // E ∈ C.covers } :=
  let h := ((C.mem_standardCoverVCovers S).mp d.2)
  let f := h.choose
  let hf := h.choose_spec.1
  ⟨(hS_contain f hf).choose, (hS_contain f hf).choose_spec.1⟩

/-- **τ subset property** (S-GEOM-TAU): each V-piece is contained in its
τ-target cover piece (as rational opens). The proof bridges the
`DecidableEq` diamond between `(C.plusDatum f).T` (built with
`Classical.decEq`) and `insert f C.base.T` (using ambient
`[DecidableEq A]`) via `rationalOpen_plusDatum_eq_insert`. -/
theorem RationalCoveringData.standardCoverVTau_subset
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A)
    (hS_contain : refines_contain C S)
    (d : { d : RationalLocData A // d ∈ C.standardCoverVCovers S }) :
    rationalOpen d.1.T d.1.s ⊆
      rationalOpen (C.standardCoverVTau S hS_contain d).1.T
                   (C.standardCoverVTau S hS_contain d).1.s := by
  -- Extract the same f ∈ S used inside standardCoverVTau (via `let h := ...; let f := h.choose`).
  intro v hv
  set h := (C.mem_standardCoverVCovers S).mp d.2 with hh_def
  let f := h.choose
  let hf := h.choose_spec.1
  have hf_eq : C.plusDatum f = d.1 := h.choose_spec.2
  -- Translate: v ∈ rationalOpen d.1.T d.1.s → v ∈ rationalOpen (insert f C.base.T) C.base.s
  -- via hf_eq + rationalOpen_plusDatum_eq_insert.
  have hv_insert : v ∈ rationalOpen (insert f C.base.T) C.base.s := by
    rw [← C.rationalOpen_plusDatum_eq_insert f, hf_eq]; exact hv
  -- standardCoverVTau d unfolds to ⟨(hS_contain f hf).choose, _⟩ via the SAME f, hf.
  exact (hS_contain f hf).choose_spec.2 hv_insert

/-! ### Iterated Laurent-plus swap

For the outer induction on `|S|`, the recursion at each Laurent split
point `f₀ ∈ S` produces V-pieces in two different iterated-plus
orderings:

* Outer V-piece at `g ∈ S` restricted to plus-half at `f₀`:
  `laurentPlusDatum (laurentPlusDatum D g) f` — g-then-f order.
* Inner recursive V-piece on plus-half covering at `g ∈ S.erase f₀`:
  `laurentPlusDatum (laurentPlusDatum D f) g` — f-then-g order.

These two iterations produce the same `.s` (= `D.s`) and the same `.T`
**as sets of valuations** — `insert g (insert f D.T)` vs
`insert f (insert g D.T)`, equal by `Finset.insert_comm`. However, the
corresponding `RationalLocData` values differ structurally (different
`DecidableEq` instance orderings internally), so the transport between
them must go through the rational-open equality stated below.

The rational-open swap combined with
`restrictionMap_bijective_of_rationalOpen_eq` gives a presheaf-value
bijection that can be used to transport `fV`-type data between the two
iteration orders in the outer induction's fV transport step. -/

/-- **Iterated Laurent-plus rational-open swap**. The rational open of
`laurentPlusDatum (laurentPlusDatum D f) g` equals that of
`laurentPlusDatum (laurentPlusDatum D g) f`.

Reason: both iterations have `.s = D.s` and `.T = insert _ (insert _
D.T)` with equal membership (up to `insert_comm`). Stated at the
rational-open level (as `Set (Spv A)`) to bypass any `DecidableEq A`
instance diamond between the two iterated-insert constructions. -/
theorem iteratedLaurentPlus_swap_rationalOpen
    [DecidableEq A] (D : RationalLocData A) (f g : A) :
    rationalOpen (laurentPlusDatum (laurentPlusDatum D f) g).T
                 (laurentPlusDatum (laurentPlusDatum D f) g).s =
    rationalOpen (laurentPlusDatum (laurentPlusDatum D g) f).T
                 (laurentPlusDatum (laurentPlusDatum D g) f).s := by
  ext v
  unfold rationalOpen
  simp only [Set.mem_setOf_eq]
  refine and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  refine forall_congr' fun t => ?_
  refine imp_congr ?_ Iff.rfl
  -- Goal: `t ∈ (laurentPlusDatum (laurentPlusDatum D f) g).T ↔
  --        t ∈ (laurentPlusDatum (laurentPlusDatum D g) f).T`.
  -- Both unfold via `laurentPlusDatum` to nested inserts; `Finset.mem_insert`
  -- translates each to `t = _ ∨ _` and `tauto` closes the or-permutation.
  simp only [laurentPlusDatum, Finset.mem_insert]
  tauto


/-! ### Pre-placed for forward-reference resolution (Move A + Move B)

The block below was originally located later in the file and has been
moved up to resolve forward references from Lane-C theorems. Content
unchanged — relocated only. -/

/-- **Rational-open equality under `v.vle f s`**. Adding an element `f` to
the generating family `T` does not change the rational open `R(T/s)`
precisely when every valuation in `R(T/s)` already satisfies `v.vle f s`. -/
theorem rationalOpen_insert_of_vle [DecidableEq A]
    (T : Finset A) (s f : A)
    (hvle : ∀ v ∈ rationalOpen T s, v.vle f s) :
    rationalOpen (insert f T) s = rationalOpen T s := by
  apply Set.Subset.antisymm
  · -- adding `f` adds a constraint: `rationalOpen (insert f T) s ⊆ rationalOpen T s`.
    rintro v ⟨hv_spa, hv_T, hv_s⟩
    exact ⟨hv_spa, fun t ht => hv_T t (Finset.mem_insert_of_mem ht), hv_s⟩
  · -- under `hvle`, the constraint on `f` is already satisfied.
    intro v hv
    -- Keep `hv` intact for feeding to `hvle`; destructure only locally.
    obtain ⟨hv_spa, hv_T, hv_s⟩ := hv
    refine ⟨hv_spa, fun t ht => ?_, hv_s⟩
    rcases Finset.mem_insert.mp ht with rfl | ht'
    · exact hvle v ⟨hv_spa, hv_T, hv_s⟩
    · exact hv_T t ht'

/-- **Bijectivity of restriction under rational-open equality**. If two
rational data `D, D'` have equal rational opens as sets of valuations, the
forward and reverse restriction maps are mutual inverses, so the forward
restriction is a bijection.

Both restrictions exist because the set equality gives both containment
directions. Their compositions equal `restrictionMap D D _` and
`restrictionMap D' D' _`, respectively, both identities by
`restrictionMap_id` (up to `Prop`-level proof irrelevance on the
reflexive `⊆` witness). -/
theorem restrictionMap_bijective_of_rationalOpen_eq
    (D D' : RationalLocData A)
    (h_eq : rationalOpen D.T D.s = rationalOpen D'.T D'.s) :
    Function.Bijective (restrictionMap D D' h_eq.symm.le) := by
  have hcomp1 :
      (restrictionMap D' D h_eq.le) ∘ (restrictionMap D D' h_eq.symm.le) = id := by
    rw [restrictionMap_comp D D' D h_eq.symm.le h_eq.le]
    exact restrictionMap_id D
  have hcomp2 :
      (restrictionMap D D' h_eq.symm.le) ∘ (restrictionMap D' D h_eq.le) = id := by
    rw [restrictionMap_comp D' D D' h_eq.le h_eq.symm.le]
    exact restrictionMap_id D'
  have hli : Function.LeftInverse (restrictionMap D' D h_eq.le)
             (restrictionMap D D' h_eq.symm.le) := congr_fun hcomp1
  have hri : Function.RightInverse (restrictionMap D' D h_eq.le)
             (restrictionMap D D' h_eq.symm.le) := congr_fun hcomp2
  exact ⟨hli.injective, hri.surjective⟩

/-- **Surjectivity corollary**: `restrictionMap D D'` is surjective when the
two rational opens agree. Unfolds the bijectivity proof. -/
theorem restrictionMap_surjective_of_rationalOpen_eq
    (D D' : RationalLocData A)
    (h_eq : rationalOpen D.T D.s = rationalOpen D'.T D'.s) :
    Function.Surjective (restrictionMap D D' h_eq.symm.le) :=
  (restrictionMap_bijective_of_rationalOpen_eq D D' h_eq).2

/-- **Laurent-plus half of a rational covering**. Given `C` and a split
point `f₀`, and explicit hypotheses certifying that the Laurent-plus of
each cover piece lands in the Laurent-plus base (`hContain`) and that
every valuation in the half's rational open is covered by some such
piece (`hCov`), builds a `RationalCoveringData` of `laurentPlusDatum C.base f₀`
whose covers are `{laurentPlusDatum E f₀ : E ∈ C.covers}`. -/
noncomputable def RationalCoveringData.plusLaurentCovering
    [DecidableEq A] (C : RationalCoveringData A) (f₀ : A)
    (hContain : ∀ E ∈ C.covers,
      rationalOpen (laurentPlusDatum E f₀).T (laurentPlusDatum E f₀).s ⊆
        rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
    (hCov : ∀ v ∈ rationalOpen (laurentPlusDatum C.base f₀).T
                              (laurentPlusDatum C.base f₀).s,
      ∃ E ∈ C.covers,
        v ∈ rationalOpen (laurentPlusDatum E f₀).T (laurentPlusDatum E f₀).s) :
    RationalCoveringData A :=
  letI : DecidableEq (RationalLocData A) := Classical.decEq _
  { base := laurentPlusDatum C.base f₀
    covers := C.covers.image (fun E => laurentPlusDatum E f₀)
    hsubset := by
      intro D hD
      obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hD
      exact hContain E hE
    hcover := by
      intro v hv
      obtain ⟨E, hE, hvE⟩ := hCov v hv
      exact ⟨laurentPlusDatum E f₀, Finset.mem_image.mpr ⟨E, hE, rfl⟩, hvE⟩ }

/-- **`hContain` automatic discharge for standard-cover V-covers**. When
`C.covers = C.standardCoverVCovers S`, each cover piece `E` is
`C.plusDatum f` with `E.s = C.base.s`, so the Laurent-plus-at-`f₀`
containment reduces to a pure Finset-membership argument: adding `f₀` to
both the original V-piece's T and the base's T preserves the containment
direction. -/
theorem RationalCoveringData.plusLaurentCovering_hContain_of_standardCoverVCovers
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A) :
    ∀ E ∈ C.standardCoverVCovers S,
      rationalOpen (laurentPlusDatum E f₀).T (laurentPlusDatum E f₀).s ⊆
        rationalOpen (laurentPlusDatum C.base f₀).T
                     (laurentPlusDatum C.base f₀).s := by
  intro E hE v hv
  obtain ⟨f, _hf_mem, hf_eq⟩ := (C.mem_standardCoverVCovers S).mp hE
  -- Substitute `E := C.plusDatum f` throughout; `E.s = C.base.s` and
  -- `E.T = insert f C.base.T` become rfl-reducible via `plusDatum`'s abbrev
  -- and `laurentPlusDatum`'s structure projections.
  subst hf_eq
  obtain ⟨hv_spa, hv_T, hv_s⟩ := hv
  refine ⟨hv_spa, fun t ht => ?_, hv_s⟩
  apply hv_T
  -- Goal: `t ∈ (laurentPlusDatum (C.plusDatum f) f₀).T`. Use `simp only
  -- [Finset.mem_insert]` on both `ht` and the goal to bypass the
  -- `[DecidableEq A]` / `Classical.propDecidable` instance diamond that
  -- shows up inside `laurentPlusDatum`'s internal `insert`.
  simp only [laurentPlusDatum, RationalCoveringData.plusDatum, Finset.mem_insert] at ht ⊢
  rcases ht with rfl | ht'
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ht')

/-- **`hCov` automatic discharge for standard-cover V-covers**. Under
`refines_cover C S` (every valuation in the base's rational open lands in
some plus-piece `insert f C.base.T / C.base.s`), combined with being in
the Laurent-plus-`f₀` half, every valuation in the Laurent-plus base is
covered by the corresponding iterated Laurent-plus V-piece. -/
theorem RationalCoveringData.plusLaurentCovering_hCov_of_refines_cover
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hS_cover : refines_cover C S) :
    ∀ v ∈ rationalOpen (laurentPlusDatum C.base f₀).T
                       (laurentPlusDatum C.base f₀).s,
      ∃ E ∈ C.standardCoverVCovers S,
        v ∈ rationalOpen (laurentPlusDatum E f₀).T (laurentPlusDatum E f₀).s := by
  intro v hv
  -- From v in laurent-plus-base: v ∈ rationalOpen C.base.T C.base.s AND v.vle f₀ C.base.s.
  have hv_base : v ∈ rationalOpen C.base.T C.base.s := laurentPlus_subset C.base f₀ hv
  -- `hv.2.1 f₀ _` gives `v.vle f₀ (laurentPlusDatum C.base f₀).s = v.vle f₀ C.base.s`.
  -- The membership `f₀ ∈ (laurentPlusDatum C.base f₀).T = insert f₀ C.base.T` is
  -- produced via simp through `laurentPlusDatum` and `Finset.mem_insert` to
  -- sidestep the `DecidableEq A` / `Classical.propDecidable` instance diamond.
  have hv_f₀ : v.vle f₀ C.base.s := hv.2.1 f₀ (by simp [laurentPlusDatum])
  -- Apply refines_cover to find f ∈ S with v ∈ plus-piece at f.
  obtain ⟨f, hf, hv_f⟩ := hS_cover v hv_base
  refine ⟨C.plusDatum f, (C.mem_standardCoverVCovers S).mpr ⟨f, hf, rfl⟩, ?_⟩
  obtain ⟨hv_spa, hv_f_T, hv_s⟩ := hv_f
  refine ⟨hv_spa, fun t ht => ?_, hv_s⟩
  -- Decompose `t ∈ (laurentPlusDatum (C.plusDatum f) f₀).T` = `insert f₀ (insert f C.base.T)`
  -- via `simp only [Finset.mem_insert]` to bypass the instance diamond.
  simp only [laurentPlusDatum, RationalCoveringData.plusDatum, Finset.mem_insert] at ht
  rcases ht with h_t_f₀ | h_t_f | ht'
  · rw [h_t_f₀]; exact hv_f₀
  · rw [h_t_f]; exact hv_f_T f (Finset.mem_insert_self _ _)
  · exact hv_f_T t (Finset.mem_insert_of_mem ht')

/-- **Laurent-plus covering for standard-cover V-covers**. Specialises
`plusLaurentCovering` to the case `C.covers = C.standardCoverVCovers S`
(the scenario of the outer induction), automatically discharging both
`hContain` and `hCov` from the preceding two theorems.

Takes the `refines_cover` hypothesis (Wedhorn-normalised standard-cover
condition on `S`) and produces a `RationalCoveringData` of
`laurentPlusDatum C.base f₀` with iterated-plus-pieces as covers. -/
noncomputable def RationalCoveringData.plusLaurentCovering_of_standardCoverVCovers
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hS_cover : refines_cover C S) :
    RationalCoveringData A :=
  -- Build a RationalCoveringData whose `covers = standardCoverVCovers S`, then split.
  let C_std : RationalCoveringData A :=
    { base := C.base
      covers := C.standardCoverVCovers S
      hsubset := C.standardCoverVCovers_subset_base S
      hcover := fun v hv => by
        obtain ⟨f, hf, hvf⟩ := hS_cover v hv
        refine ⟨C.plusDatum f, (C.mem_standardCoverVCovers S).mpr ⟨f, hf, rfl⟩, ?_⟩
        -- `hvf : v ∈ rationalOpen (insert f C.base.T) C.base.s`; convert to
        -- `v ∈ rationalOpen (C.plusDatum f).T (C.plusDatum f).s` via the
        -- rational-open equality theorem (which sidesteps the DecidableEq
        -- diamond between ambient and Classical).
        exact (C.rationalOpen_plusDatum_eq_insert f).symm ▸ hvf }
  C_std.plusLaurentCovering f₀
    (C_std.plusLaurentCovering_hContain_of_standardCoverVCovers S f₀)
    (C_std.plusLaurentCovering_hCov_of_refines_cover S f₀ hS_cover)

/-- **Iterated Laurent-plus presheaf-value bijection**. Combining
`iteratedLaurentPlus_swap_rationalOpen` with
`restrictionMap_bijective_of_rationalOpen_eq` gives a bijection
between the presheaf values of the two iteration orderings — this is
the fV-transport bridge for the outer induction's recursion step. -/
theorem iteratedLaurentPlus_swap_bijective
    [DecidableEq A] (D : RationalLocData A) (f g : A) :
    Function.Bijective
      (restrictionMap
        (laurentPlusDatum (laurentPlusDatum D f) g)
        (laurentPlusDatum (laurentPlusDatum D g) f)
        (iteratedLaurentPlus_swap_rationalOpen D f g).symm.le) :=
  restrictionMap_bijective_of_rationalOpen_eq _ _
    (iteratedLaurentPlus_swap_rationalOpen D f g)

/-! ### fV transport across the iterated-Laurent-plus swap (item 2)

Outer induction's recursive call on the plus half needs `fV_plus` indexed
by the INNER V-cover `plusC.standardCoverVCovers (S.erase f₀) =
{laurentPlusDatum (laurentPlusDatum C.base f₀) g | g ∈ S.erase f₀}`
(f-then-g iteration). The OUTER `fV` gives values at
`C.plusDatum g = laurentPlusDatum C.base g` for each `g ∈ S` — so the
transport is a 2-step composition:

1. **Restrict** outer `fV D` (on `laurentPlusDatum C.base g`) to the
   plus half at `f₀`, producing a value on
   `laurentPlusDatum (laurentPlusDatum C.base g) f₀` (g-then-f).
2. **Swap** iteration order via
   `iteratedLaurentPlus_swap_rationalOpen`, producing a value on
   `laurentPlusDatum (laurentPlusDatum C.base f₀) g` (f-then-g) —
   exactly the type the inner IH expects.

The transport below packages this as a single reusable `def`. -/

/-- **Plus-half presheaf-value transport**. Composes restriction to
the plus half at `f₀` with the iterated-Laurent-plus swap, mapping
`presheafValue (C.plusDatum g)` (outer V-piece at g) to
`presheafValue (laurentPlusDatum (laurentPlusDatum C.base f₀) g)`
(inner V-piece at g in the plus-half V-cover). -/
noncomputable def RationalCoveringData.plusHalf_presheaf_transport
    [DecidableEq A] (C : RationalCoveringData A) (f₀ g : A)
    (u : presheafValue (C.plusDatum g)) :
    presheafValue (laurentPlusDatum (laurentPlusDatum C.base f₀) g) :=
  restrictionMap
    (laurentPlusDatum (C.plusDatum g) f₀)
    (laurentPlusDatum (laurentPlusDatum C.base f₀) g)
    (iteratedLaurentPlus_swap_rationalOpen C.base f₀ g).le
    (restrictionMap (C.plusDatum g) (laurentPlusDatum (C.plusDatum g) f₀)
      (laurentPlus_subset (C.plusDatum g) f₀) u)

/-- **Plus-half transport factors through single-level `restrictionMap`**.
The two-step transport equals a single composite `restrictionMap` from
`C.plusDatum g` to `laurentPlusDatum (laurentPlusDatum C.base f₀) g`.
This is the key identity enabling item-3 compatibility transfer:
`fV_plus D'` is structurally a single restriction of the outer `fV D`,
so restrictionMap chains on `fV_plus` reduce to chains on `fV`. -/
theorem RationalCoveringData.plusHalf_presheaf_transport_eq_single
    [DecidableEq A] (C : RationalCoveringData A) (f₀ g : A)
    (u : presheafValue (C.plusDatum g)) :
    C.plusHalf_presheaf_transport f₀ g u =
      restrictionMap (C.plusDatum g)
        (laurentPlusDatum (laurentPlusDatum C.base f₀) g)
        ((iteratedLaurentPlus_swap_rationalOpen C.base f₀ g).le.trans
          (laurentPlus_subset (C.plusDatum g) f₀)) u := by
  unfold RationalCoveringData.plusHalf_presheaf_transport
  exact congr_fun (restrictionMap_comp (C.plusDatum g)
    (laurentPlusDatum (C.plusDatum g) f₀)
    (laurentPlusDatum (laurentPlusDatum C.base f₀) g)
    (laurentPlus_subset (C.plusDatum g) f₀)
    (iteratedLaurentPlus_swap_rationalOpen C.base f₀ g).le) u

/-! ### Restriction-property transfer at the recursion boundary (item 3)

For the outer recursion's `plus_section fV hV_compat := ⟨u_plus, proof⟩`
to have `restrictionMap ... u_plus = fV D` for each outer V-piece `D`
in the plus half, we need the inner IH's restriction property
(on inner V-pieces) to compose cleanly with the transport to give
the outer restriction property. The helper below provides this
chain via `plusHalf_presheaf_transport_eq_single` +
`restrictionMap_comp`: given an inner-IH restriction property on the
transported family, produce the outer restriction property after
re-transport. -/

/-- **Transport-compatible restriction identity**. For any outer V-piece
`D = C.plusDatum g` contained in the plus half, the plus-half transport
of `fV D` restricted to any smaller `D₃` equals the direct restriction
of `fV D` to `D₃`. In the outer induction, this identifies
`restrictionMap plusC.base D.1 _ u_plus` (for outer D in plus half)
with `restrictionMap (laurentPlusDatum (...) g) D.1 _ (transport ...)`
composed across the transport. -/
theorem RationalCoveringData.plusHalf_transport_restrictionMap_eq
    [DecidableEq A] (C : RationalCoveringData A) (f₀ g : A)
    (D₃ : RationalLocData A)
    (h₃ : rationalOpen D₃.T D₃.s ⊆
      rationalOpen (laurentPlusDatum (laurentPlusDatum C.base f₀) g).T
                   (laurentPlusDatum (laurentPlusDatum C.base f₀) g).s)
    (u : presheafValue (C.plusDatum g)) :
    restrictionMap (laurentPlusDatum (laurentPlusDatum C.base f₀) g) D₃ h₃
        (C.plusHalf_presheaf_transport f₀ g u) =
      restrictionMap (C.plusDatum g) D₃
        (h₃.trans ((iteratedLaurentPlus_swap_rationalOpen C.base f₀ g).le.trans
          (laurentPlus_subset (C.plusDatum g) f₀))) u := by
  rw [C.plusHalf_presheaf_transport_eq_single f₀ g u]
  exact congr_fun (restrictionMap_comp (C.plusDatum g)
    (laurentPlusDatum (laurentPlusDatum C.base f₀) g) D₃
    ((iteratedLaurentPlus_swap_rationalOpen C.base f₀ g).le.trans
      (laurentPlus_subset (C.plusDatum g) f₀))
    h₃) u

/-! ### Plus-half `fV` transport at each `g ∈ S.erase f₀`

Wraps `plusHalf_presheaf_transport` in a form that takes outer `fV`
(indexed by `C.standardCoverVCovers S`) plus an explicit `g ∈ S.erase
f₀` and produces a presheaf value at the inner V-piece
`laurentPlusDatum (laurentPlusDatum C.base f₀) g` (the f-then-g
iteration order used by the recursive IH on the plus half). -/

/-- **Plus-half `fV` transport (parametric on `g`)**. Given outer `fV`
and an explicit `g ∈ S.erase f₀`, produces the value at the inner
V-piece shape expected by the recursive IH on
`plusLaurentCovering_of_standardCoverVCovers C S f₀ hS_cover`. -/
noncomputable def RationalCoveringData.plusHalf_fV_transport_at_g
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ g : A)
    (hg_mem : g ∈ S.erase f₀)
    (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S }, presheafValue D.1) :
    presheafValue (laurentPlusDatum (laurentPlusDatum C.base f₀) g) :=
  C.plusHalf_presheaf_transport f₀ g
    (fV ⟨C.plusDatum g,
      (C.mem_standardCoverVCovers S).mpr
        ⟨g, Finset.mem_of_mem_erase hg_mem, rfl⟩⟩)

/-- **Restriction identity for `plusHalf_fV_transport_at_g`**. For any
`D₃` contained in the inner V-piece, restricting the transported value
to `D₃` equals restricting the outer `fV` directly to `D₃` (chaining
through the swap and plus-half subset). -/
theorem RationalCoveringData.plusHalf_fV_transport_at_g_restrictionMap_eq
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ g : A)
    (hg_mem : g ∈ S.erase f₀)
    (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S }, presheafValue D.1)
    (D₃ : RationalLocData A)
    (h₃ : rationalOpen D₃.T D₃.s ⊆
      rationalOpen (laurentPlusDatum (laurentPlusDatum C.base f₀) g).T
                   (laurentPlusDatum (laurentPlusDatum C.base f₀) g).s) :
    restrictionMap (laurentPlusDatum (laurentPlusDatum C.base f₀) g) D₃ h₃
        (C.plusHalf_fV_transport_at_g S f₀ g hg_mem fV) =
      restrictionMap (C.plusDatum g) D₃
        (h₃.trans ((iteratedLaurentPlus_swap_rationalOpen C.base f₀ g).le.trans
          (laurentPlus_subset (C.plusDatum g) f₀)))
        (fV ⟨C.plusDatum g,
          (C.mem_standardCoverVCovers S).mpr
            ⟨g, Finset.mem_of_mem_erase hg_mem, rfl⟩⟩) :=
  C.plusHalf_transport_restrictionMap_eq f₀ g D₃ h₃ _

/-- **Per-`g` plus-half transported compat** (sorry-free derivation from
outer `hV_compat` without `Classical.choose`). At specific
`g₁, g₂ ∈ S.erase f₀`, the transported values
`plusHalf_fV_transport_at_g ... g₁ fV` and `... g₂ fV` satisfy the
compatibility expected by the recursive IH: their restrictions to any
common `D₃` agree.

Proof: rewrite both sides via
`plusHalf_fV_transport_at_g_restrictionMap_eq` (reducing to
restrictions of outer `fV` at `C.plusDatum gᵢ`), then apply outer
`hV_compat`.

**Usage**: a caller deriving the `plus_compat_fn` hypothesis of
`tateAcyclicity_augmentedCech_from_plusIH_and_minusBundle` can reduce
the `Classical.choose`-extracted statement to this per-`g` form by
destructuring the V-piece subtype and applying `subst`. This helper
absorbs the per-`g` restriction-compose + `hV_compat` chain into one
named theorem, so downstream derivations of the full `plus_compat_fn`
only need to handle the `Classical.choose` / `▸` substitution layer. -/
theorem RationalCoveringData.plusHalf_transported_compat_at_g
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (g₁ g₂ : A) (hg₁ : g₁ ∈ S.erase f₀) (hg₂ : g₂ ∈ S.erase f₀)
    (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S }, presheafValue D.1)
    (hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
      (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂))
    (D₃ : RationalLocData A)
    (h₃₁ : rationalOpen D₃.T D₃.s ⊆
      rationalOpen (laurentPlusDatum (laurentPlusDatum C.base f₀) g₁).T
                   (laurentPlusDatum (laurentPlusDatum C.base f₀) g₁).s)
    (h₃₂ : rationalOpen D₃.T D₃.s ⊆
      rationalOpen (laurentPlusDatum (laurentPlusDatum C.base f₀) g₂).T
                   (laurentPlusDatum (laurentPlusDatum C.base f₀) g₂).s) :
    restrictionMap (laurentPlusDatum (laurentPlusDatum C.base f₀) g₁) D₃ h₃₁
        (C.plusHalf_fV_transport_at_g S f₀ g₁ hg₁ fV) =
      restrictionMap (laurentPlusDatum (laurentPlusDatum C.base f₀) g₂) D₃ h₃₂
        (C.plusHalf_fV_transport_at_g S f₀ g₂ hg₂ fV) := by
  rw [C.plusHalf_fV_transport_at_g_restrictionMap_eq S f₀ g₁ hg₁ fV D₃ h₃₁,
      C.plusHalf_fV_transport_at_g_restrictionMap_eq S f₀ g₂ hg₂ fV D₃ h₃₂]
  exact hV_compat
    ⟨C.plusDatum g₁, (C.mem_standardCoverVCovers S).mpr
      ⟨g₁, Finset.mem_of_mem_erase hg₁, rfl⟩⟩
    ⟨C.plusDatum g₂, (C.mem_standardCoverVCovers S).mpr
      ⟨g₂, Finset.mem_of_mem_erase hg₂, rfl⟩⟩
    D₃ _ _

/-! ### Minus-half: natural restriction and iteration-asymmetry note

**No symmetric swap for minus**: unlike the plus half, the two iteration
orders for the minus case produce DIFFERENT rational opens as sets:

* **Plus-then-minus**: `laurentMinusDatum (C.plusDatum g) f₀` — the
  OUTER restriction of V-piece at `g` to minus-half at `f₀`. Its
  rational open is `{v ∈ minus-half | v(g) ≤ v(C.base.s)}`.
* **Minus-then-plus**: `laurentPlusDatum (laurentMinusDatum C.base f₀) g`
  = `minusC.plusDatum g` — the INNER V-piece on the minus-half covering
  at `g`. Its rational open is
  `{v ∈ minus-half | v(g) ≤ v(C.base.s * f₀)}`
  = `{v ∈ minus-half | v(g) ≤ v(C.base.s) · v(f₀)}`.

Under `v(f₀) ≥ v(C.base.s) > 0` (holds on minus half), the two
conditions differ: plus-then-minus is strictly STRONGER than
minus-then-plus in general (the outer restriction's condition
`v(g) ≤ v(C.base.s)` is tighter than `v(g) ≤ v(C.base.s) · v(f₀)`
when `v(f₀) ≥ 1`, but the reverse can hold when `v(f₀) < 1`). The
two rational opens are NOT set-equal.

**Consequence for the outer induction**: there is no direct
`restrictionMap`-based transport from an outer-natural restriction
(plus-then-minus) to an inner-IH-expected shape (minus-then-plus). The
outer induction architecture as currently designed cannot recurse on
`minusLaurentCovering_of_standardCoverVCovers C S f₀ hS_cover` with
`S.erase f₀` on the minus half without either:

1. **Architectural change**: use a different inner V-cover shape on the
   minus half (e.g., `minusC.covers = {laurentMinusDatum (C.plusDatum g)
   f₀ | g ∈ S}` directly, NOT `minusC.standardCoverVCovers (S.erase f₀)`).
   This loses the clean well-founded cardinality recursion on `|S|`.
2. **Additional hypotheses**: caller supplies the minus-half `fV_minus`
   and recursion witness directly, taking `hBase_vle_minus` +
   analogous transport data as explicit top-level parameters.
3. **Abandon `standardCoverVCovers` as V-cover**: switch the outer
   induction to use `refinedVCovers S f₀` (where plus/minus refined
   pieces are built in). This is a larger refactor.

**This session's minus-half landing**: we provide the NATURAL
restriction at plus-then-minus shape
(`minusHalf_fV_restriction_at_g`) — useful when the caller takes route
(2) above and supplies additional machinery. The minus-then-plus
recursive shape remains as documented-explicit future work. -/

/-- **Minus-half natural restriction at `g ∈ S.erase f₀`**. Given
outer `fV` and explicit `g ∈ S.erase f₀`, produces the natural
restriction of `fV ⟨C.plusDatum g, ...⟩` to the minus half at `f₀` —
a value at `laurentMinusDatum (C.plusDatum g) f₀` (plus-then-minus
iteration).

**Type mismatch warning**: this produces the plus-then-minus shape,
NOT the minus-then-plus shape `minusC.plusDatum g = laurentPlusDatum
(laurentMinusDatum C.base f₀) g` expected by a naive recursive IH. See
the doc block above. For callers using explicit minus-side hypotheses,
this natural restriction is the cleanest starting point. -/
noncomputable def RationalCoveringData.minusHalf_fV_restriction_at_g
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ g : A)
    (hg_mem : g ∈ S.erase f₀)
    (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S }, presheafValue D.1) :
    presheafValue (laurentMinusDatum (C.plusDatum g) f₀) :=
  restrictionMap (C.plusDatum g) (laurentMinusDatum (C.plusDatum g) f₀)
    (laurentMinus_subset (C.plusDatum g) f₀)
    (fV ⟨C.plusDatum g,
      (C.mem_standardCoverVCovers S).mpr
        ⟨g, Finset.mem_of_mem_erase hg_mem, rfl⟩⟩)

/-- **Restriction identity for `minusHalf_fV_restriction_at_g`**. For
any `D₃` contained in the plus-then-minus shape, restricting the
natural restriction to `D₃` equals restricting the outer `fV` directly
to `D₃` via `laurentMinus_subset` + the subset proof. Symmetric
single-step version of the plus-half restriction identity. -/
theorem RationalCoveringData.minusHalf_fV_restriction_at_g_restrictionMap_eq
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ g : A)
    (hg_mem : g ∈ S.erase f₀)
    (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S }, presheafValue D.1)
    (D₃ : RationalLocData A)
    (h₃ : rationalOpen D₃.T D₃.s ⊆
      rationalOpen (laurentMinusDatum (C.plusDatum g) f₀).T
                   (laurentMinusDatum (C.plusDatum g) f₀).s) :
    restrictionMap (laurentMinusDatum (C.plusDatum g) f₀) D₃ h₃
        (C.minusHalf_fV_restriction_at_g S f₀ g hg_mem fV) =
      restrictionMap (C.plusDatum g) D₃
        (h₃.trans (laurentMinus_subset (C.plusDatum g) f₀))
        (fV ⟨C.plusDatum g,
          (C.mem_standardCoverVCovers S).mpr
            ⟨g, Finset.mem_of_mem_erase hg_mem, rfl⟩⟩) := by
  unfold RationalCoveringData.minusHalf_fV_restriction_at_g
  exact congr_fun (restrictionMap_comp (C.plusDatum g)
    (laurentMinusDatum (C.plusDatum g) f₀) D₃
    (laurentMinus_subset (C.plusDatum g) f₀) h₃) _

/-! ### Outer-vs-inner `plusDatum` equality under `hD_plus`

When an outer V-piece `D = C.plusDatum g` is contained in the plus
half at `f₀` (i.e., `hD_plus` holds), the rational open of `D` equals
the rational open of the inner V-piece `laurentPlusDatum
(laurentPlusDatum C.base f₀) g`. This lets us identify outer and
inner V-pieces as SAME adic subsets at Prop level, so restrictions of
presheaf values on one match the restrictions on the other. This is
the final bridge enabling outer-V-piece restriction properties from
inner-IH restriction properties. -/

/-- **Outer plus-piece at `g` equals inner iterated plus when outer ⊆ plus half**.
Given `hD_plus : rationalOpen (C.plusDatum g) ⊆ rationalOpen plus-half`,
the rational open of `C.plusDatum g` equals that of
`laurentPlusDatum (laurentPlusDatum C.base f₀) g` as sets. This uses
`hD_plus` to "add back" the implicit `v.vle f₀ C.base.s` constraint
that distinguishes the inner iteration from the outer. -/
theorem RationalCoveringData.outer_plusDatum_eq_inner_when_subset_plusHalf
    [DecidableEq A] (C : RationalCoveringData A) (f₀ g : A)
    (hD_plus : rationalOpen (C.plusDatum g).T (C.plusDatum g).s ⊆
      rationalOpen (laurentPlusDatum C.base f₀).T
                   (laurentPlusDatum C.base f₀).s) :
    rationalOpen (C.plusDatum g).T (C.plusDatum g).s =
    rationalOpen (laurentPlusDatum (laurentPlusDatum C.base f₀) g).T
                 (laurentPlusDatum (laurentPlusDatum C.base f₀) g).s := by
  apply Set.Subset.antisymm
  · -- Outer ⊆ Inner: use hD_plus to discharge the extra `v.vle f₀ C.base.s`.
    intro v hv
    have h_plus := hD_plus hv
    obtain ⟨hv_spa, hv_T, hv_s⟩ := hv
    refine ⟨hv_spa, fun t ht => ?_, hv_s⟩
    simp only [laurentPlusDatum, Finset.mem_insert] at ht
    rcases ht with h_eq | h_eq | ht'
    · -- t = g
      rw [h_eq]
      apply hv_T
      simp [RationalCoveringData.plusDatum, laurentPlusDatum]
    · -- t = f₀
      rw [h_eq]
      apply h_plus.2.1
      simp [laurentPlusDatum]
    · -- t ∈ C.base.T
      apply hv_T
      simp only [RationalCoveringData.plusDatum, laurentPlusDatum, Finset.mem_insert]
      exact Or.inr ht'
  · -- Inner ⊆ Outer: drop the f₀ constraint.
    intro v hv
    obtain ⟨hv_spa, hv_T, hv_s⟩ := hv
    refine ⟨hv_spa, fun t ht => ?_, hv_s⟩
    apply hv_T
    simp only [RationalCoveringData.plusDatum, laurentPlusDatum, Finset.mem_insert] at ht ⊢
    rcases ht with h_eq | ht'
    · exact Or.inl h_eq
    · exact Or.inr (Or.inr ht')

/-! ### `hV_glue` assembly from plus-half IH and explicit minus-half bundle

The culminating theorem of this session: given
* plus-half inner IH `plus_hV_glue` (shape of `hV_glue` applied to
  `plusLaurentCovering_of_standardCoverVCovers` at `S.erase f₀`),
* an EXPLICIT minus-half section builder `minus_section`,
* standard plumbing (`hrefine`, `hLaurentGlue`, `hoverlap`, `hBase_vle`,
  `hAplus`),
we produce an `hV_glue`-shaped output for the outer `(C, S)` by:

1. Using `plusHalf_fV_transport_at_g` to transport outer `fV` into an
   `fV_plus` on the plus-half V-cover `(plusC).standardCoverVCovers
   (S.erase f₀)`.
2. Applying the `plus_hV_glue` IH to get `u_plus`.
3. Verifying the restriction property on outer plus V-pieces via
   `plusHalf_fV_transport_at_g_restrictionMap_eq` +
   `outer_plusDatum_eq_inner_when_subset_plusHalf`.
4. Consuming `minus_section` for the minus half.
5. Assembling via `hV_glue_step_from_laurent_halves` (which itself
   uses `standardCover_gluing_induction_step` + the Laurent gluing).

Strategy: since the full theorem has ~30 hypothesis components and the
body is deep restrictionMap-chain reasoning, we DO NOT attempt to prove
it in one go. Instead we state the precise boundary as a sorry-free
THEOREM that chains `hV_glue_step_from_laurent_halves` with the
explicit `plus_section` builder derived from the IH. The plus_section's
restriction-property proof (requiring the combination of `plus_hV_glue`
output + transport restriction identity + outer-vs-inner equality) is
split into a separate helper that can be proved mechanically in a
follow-up session.

For this session, we land the **plus_section builder** up to the
restriction-property obligation, which is stated as an explicit
hypothesis of the builder (matching the shape the caller would have to
discharge anyway). The result: a sorry-free builder producing
plus_section, with the remaining restriction-property boundary
precisely stated. -/

/-- **Plus-half `plus_section` builder**. Given the plus-half inner IH
`plus_hV_glue` and outer `fV, hV_compat`, produces the `plus_section`
Subtype value expected by `standardCover_hV_glue_induction_via_vle`'s
step_witness. The u_plus is obtained from `plus_hV_glue` applied to
the transported family `plusHalf_fV_transport_at_g`; the restriction
property on outer V-pieces in the plus half is taken as an EXPLICIT
hypothesis `h_restriction_prop` (provable by combining `plus_hV_glue`'s
own restriction property with `plusHalf_fV_transport_at_g_restrictionMap_eq`
and `outer_plusDatum_eq_inner_when_subset_plusHalf`, but deferred here
to keep the builder a single clean application). -/
noncomputable def RationalCoveringData.plus_section_of_plus_hV_glue
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hS_cover : refines_cover C S)
    (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S }, presheafValue D.1)
    (_hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
      (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂))
    -- Plus-half IH: given fV_plus on plus-half V-cover + plus-compat, produce u_plus.
    (plus_hV_glue :
      ∀ (fV_plus : ∀ D' : { D' // D' ∈ (C.plusLaurentCovering_of_standardCoverVCovers
          S f₀ hS_cover).standardCoverVCovers (S.erase f₀) },
          presheafValue D'.1),
        (∀ (D₁' D₂' : { D' // D' ∈ (C.plusLaurentCovering_of_standardCoverVCovers
            S f₀ hS_cover).standardCoverVCovers (S.erase f₀) })
          (D₃ : RationalLocData A)
          (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁'.1.T D₁'.1.s)
          (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂'.1.T D₂'.1.s),
          restrictionMap D₁'.1 D₃ h₃₁ (fV_plus D₁') =
            restrictionMap D₂'.1 D₃ h₃₂ (fV_plus D₂')) →
        ∃ u_plus : presheafValue (laurentPlusDatum C.base f₀),
          ∀ (D' : { D' // D' ∈ (C.plusLaurentCovering_of_standardCoverVCovers
              S f₀ hS_cover).standardCoverVCovers (S.erase f₀) })
            (hD' : rationalOpen D'.1.T D'.1.s ⊆
              rationalOpen (laurentPlusDatum C.base f₀).T
                           (laurentPlusDatum C.base f₀).s),
            restrictionMap (laurentPlusDatum C.base f₀) D'.1 hD' u_plus = fV_plus D')
    -- Plus-compat of the transported family. Auto-derivable from outer
    -- `hV_compat` via `plus_compat_fn_from_outer_hV_compat` (landed after
    -- this definition; callers should use `plus_section_of_plus_hV_glue_auto`
    -- for automatic discharge).
    (plus_compat :
      ∀ (D₁' D₂' : { D' // D' ∈ (C.plusLaurentCovering_of_standardCoverVCovers
          S f₀ hS_cover).standardCoverVCovers (S.erase f₀) })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁'.1.T D₁'.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂'.1.T D₂'.1.s),
        restrictionMap D₁'.1 D₃ h₃₁
            (let h_exists :=
               ((C.plusLaurentCovering_of_standardCoverVCovers S f₀
                 hS_cover).mem_standardCoverVCovers
                 (S.erase f₀)).mp D₁'.2
             let g := Classical.choose h_exists
             let hg_spec := Classical.choose_spec h_exists
             hg_spec.2 ▸ C.plusHalf_fV_transport_at_g S f₀ g hg_spec.1 fV) =
          restrictionMap D₂'.1 D₃ h₃₂
            (let h_exists :=
               ((C.plusLaurentCovering_of_standardCoverVCovers S f₀
                 hS_cover).mem_standardCoverVCovers
                 (S.erase f₀)).mp D₂'.2
             let g := Classical.choose h_exists
             let hg_spec := Classical.choose_spec h_exists
             hg_spec.2 ▸ C.plusHalf_fV_transport_at_g S f₀ g hg_spec.1 fV))
    -- Restriction property on outer plus V-pieces (explicit; see
    -- `outer_plusDatum_eq_inner_when_subset_plusHalf` for the bridge).
    (h_restriction_prop :
      ∀ (u_plus : presheafValue (laurentPlusDatum C.base f₀)),
        (∀ (D' : { D' // D' ∈ (C.plusLaurentCovering_of_standardCoverVCovers
            S f₀ hS_cover).standardCoverVCovers (S.erase f₀) })
          (hD' : rationalOpen D'.1.T D'.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T
                         (laurentPlusDatum C.base f₀).s),
          restrictionMap (laurentPlusDatum C.base f₀) D'.1 hD' u_plus =
            (let h_exists :=
               ((C.plusLaurentCovering_of_standardCoverVCovers S f₀
                 hS_cover).mem_standardCoverVCovers
                 (S.erase f₀)).mp D'.2
             let g := Classical.choose h_exists
             let hg_spec := Classical.choose_spec h_exists
             hg_spec.2 ▸ C.plusHalf_fV_transport_at_g S f₀ g hg_spec.1 fV)) →
        ∀ (D : { D // D ∈ C.standardCoverVCovers S })
          (hD_plus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T
                         (laurentPlusDatum C.base f₀).s),
          restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D) :
    { u_plus : presheafValue (laurentPlusDatum C.base f₀) //
      ∀ (D : { D // D ∈ C.standardCoverVCovers S })
        (hD_plus : rationalOpen D.1.T D.1.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T
                       (laurentPlusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D } :=
  let fV_plus :
    ∀ D' : { D' // D' ∈ (C.plusLaurentCovering_of_standardCoverVCovers
        S f₀ hS_cover).standardCoverVCovers (S.erase f₀) }, presheafValue D'.1 :=
    fun D' =>
      let h_exists :=
        ((C.plusLaurentCovering_of_standardCoverVCovers S f₀ hS_cover).mem_standardCoverVCovers
          (S.erase f₀)).mp D'.2
      let g := Classical.choose h_exists
      let hg_spec := Classical.choose_spec h_exists
      hg_spec.2 ▸ C.plusHalf_fV_transport_at_g S f₀ g hg_spec.1 fV
  let hIH := plus_hV_glue fV_plus plus_compat
  ⟨Classical.choose hIH, h_restriction_prop (Classical.choose hIH) (Classical.choose_spec hIH)⟩

/-- **`plus_compat` derivation from outer `hV_compat`**. Supplies the
`plus_compat` hypothesis of `plus_section_of_plus_hV_glue` directly
from outer `hV_compat`. Strategy: destructure each V-piece subtype,
then destructure the EXISTENTIAL (via `obtain` on the bi-conditional
membership, NOT `Classical.choose_spec`) to get FRESH `(g_i, hg_i_mem,
hg_i_eq)` that don't contain `D_i'_val` in their terms. Subst
`hg_i_eq` to replace `D_i'_val` with `plusC.plusDatum g_i`; the inner
`Classical.choose`-let in the goal still references `D_i'_prop` (now
with updated type), and its `▸` cast becomes a cast along an equation
that holds by `rfl` (both sides `plusC.plusDatum (Classical.choose ⋯)`).

The `restrictionMap` of the cast value equals the outer `fV`
restriction via `plusHalf_fV_transport_at_g_restrictionMap_eq`;
`hV_compat` closes the matching of both sides. -/
theorem RationalCoveringData.plus_compat_fn_from_outer_hV_compat
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hS_cover : refines_cover C S)
    (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S }, presheafValue D.1)
    (hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
      (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) :
    ∀ (D₁' D₂' : { D' // D' ∈ (C.plusLaurentCovering_of_standardCoverVCovers
        S f₀ hS_cover).standardCoverVCovers (S.erase f₀) })
      (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁'.1.T D₁'.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂'.1.T D₂'.1.s),
      restrictionMap D₁'.1 D₃ h₃₁
          (let h_exists :=
             ((C.plusLaurentCovering_of_standardCoverVCovers S f₀ hS_cover).mem_standardCoverVCovers
               (S.erase f₀)).mp D₁'.2
           let g := Classical.choose h_exists
           let hg_spec := Classical.choose_spec h_exists
           hg_spec.2 ▸ C.plusHalf_fV_transport_at_g S f₀ g hg_spec.1 fV) =
        restrictionMap D₂'.1 D₃ h₃₂
          (let h_exists :=
             ((C.plusLaurentCovering_of_standardCoverVCovers S f₀ hS_cover).mem_standardCoverVCovers
               (S.erase f₀)).mp D₂'.2
           let g := Classical.choose h_exists
           let hg_spec := Classical.choose_spec h_exists
           hg_spec.2 ▸ C.plusHalf_fV_transport_at_g S f₀ g hg_spec.1 fV) := by
  -- Transport helper: restrictionMap commutes with ▸ cast on the source.
  have restrictionMap_mpr_eq : ∀ {D D' : RationalLocData A} (h : D = D')
      (D₃ : RationalLocData A) (h₃ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D'.T D'.s)
      (v : presheafValue D),
      restrictionMap D' D₃ h₃ (h ▸ v) = restrictionMap D D₃ (h.symm ▸ h₃) v := by
    intro D D' h D₃ h₃ v
    subst h
    rfl
  rintro ⟨D₁'_val, D₁'_prop⟩ ⟨D₂'_val, D₂'_prop⟩ D₃ h₃₁ h₃₂
  -- Extract the existentials. These give FRESH g₁, g₂ (not Classical.choose).
  obtain ⟨g₁, hg₁_mem, hg₁_eq⟩ :=
    ((C.plusLaurentCovering_of_standardCoverVCovers S f₀ hS_cover).mem_standardCoverVCovers
      (S.erase f₀)).mp D₁'_prop
  obtain ⟨g₂, hg₂_mem, hg₂_eq⟩ :=
    ((C.plusLaurentCovering_of_standardCoverVCovers S f₀ hS_cover).mem_standardCoverVCovers
      (S.erase f₀)).mp D₂'_prop
  -- Subst replaces D_i'_val with plusC.plusDatum g_i. g_i are fresh, so subst works.
  subst hg₁_eq
  subst hg₂_eq
  -- Extract Classical.choose-derived witnesses g₁', g₂' (may differ from g₁, g₂).
  set h_ex_1 := ((C.plusLaurentCovering_of_standardCoverVCovers S f₀
      hS_cover).mem_standardCoverVCovers
      (S.erase f₀)).mp D₁'_prop with hE1
  set h_ex_2 := ((C.plusLaurentCovering_of_standardCoverVCovers S f₀
      hS_cover).mem_standardCoverVCovers
      (S.erase f₀)).mp D₂'_prop with hE2
  obtain ⟨hg₁'_mem, hg₁'_eq⟩ := Classical.choose_spec h_ex_1
  obtain ⟨hg₂'_mem, hg₂'_eq⟩ := Classical.choose_spec h_ex_2
  -- Now goal:
  -- restrictionMap (plusC.plusDatum g₁) D₃ h₃₁
  --   (hg₁'_eq ▸ plusHalf_fV_transport_at_g S f₀ g₁' hg₁'_mem fV)
  -- = restrictionMap (plusC.plusDatum g₂) D₃ h₃₂
  --   (hg₂'_eq ▸ plusHalf_fV_transport_at_g S f₀ g₂' hg₂'_mem fV)
  -- where g_i' := Classical.choose h_ex_i,
  --       hg_i'_eq : plusC.plusDatum g_i' = plusC.plusDatum g_i.
  -- Apply restrictionMap_mpr_eq to push the ▸ onto the subset witness.
  rw [restrictionMap_mpr_eq hg₁'_eq D₃ h₃₁
        (C.plusHalf_fV_transport_at_g S f₀ (Classical.choose h_ex_1) hg₁'_mem fV),
      restrictionMap_mpr_eq hg₂'_eq D₃ h₃₂
        (C.plusHalf_fV_transport_at_g S f₀ (Classical.choose h_ex_2) hg₂'_mem fV)]
  -- Apply plusHalf_transported_compat_at_g at g₁' := Classical.choose h_ex_i.
  exact C.plusHalf_transported_compat_at_g S f₀ (Classical.choose h_ex_1) (Classical.choose h_ex_2)
    hg₁'_mem hg₂'_mem fV hV_compat D₃ _ _

/-- **Auto-discharge wrapper for `plus_section_of_plus_hV_glue`**. Drops the
explicit `plus_compat` hypothesis, auto-deriving it from outer `hV_compat`
via `plus_compat_fn_from_outer_hV_compat`. Callers now only supply
`plus_hV_glue` (the inner IH) and `h_restriction_prop` (the outer
V-piece bridge). -/
noncomputable def RationalCoveringData.plus_section_of_plus_hV_glue_auto
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hS_cover : refines_cover C S)
    (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S }, presheafValue D.1)
    (hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
      (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂))
    (plus_hV_glue :
      ∀ (fV_plus : ∀ D' : { D' // D' ∈ (C.plusLaurentCovering_of_standardCoverVCovers
          S f₀ hS_cover).standardCoverVCovers (S.erase f₀) },
          presheafValue D'.1),
        (∀ (D₁' D₂' : { D' // D' ∈ (C.plusLaurentCovering_of_standardCoverVCovers
            S f₀ hS_cover).standardCoverVCovers (S.erase f₀) })
          (D₃ : RationalLocData A)
          (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁'.1.T D₁'.1.s)
          (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂'.1.T D₂'.1.s),
          restrictionMap D₁'.1 D₃ h₃₁ (fV_plus D₁') =
            restrictionMap D₂'.1 D₃ h₃₂ (fV_plus D₂')) →
        ∃ u_plus : presheafValue (laurentPlusDatum C.base f₀),
          ∀ (D' : { D' // D' ∈ (C.plusLaurentCovering_of_standardCoverVCovers
              S f₀ hS_cover).standardCoverVCovers (S.erase f₀) })
            (hD' : rationalOpen D'.1.T D'.1.s ⊆
              rationalOpen (laurentPlusDatum C.base f₀).T
                           (laurentPlusDatum C.base f₀).s),
            restrictionMap (laurentPlusDatum C.base f₀) D'.1 hD' u_plus = fV_plus D')
    (h_restriction_prop :
      ∀ (u_plus : presheafValue (laurentPlusDatum C.base f₀)),
        (∀ (D' : { D' // D' ∈ (C.plusLaurentCovering_of_standardCoverVCovers
            S f₀ hS_cover).standardCoverVCovers (S.erase f₀) })
          (hD' : rationalOpen D'.1.T D'.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T
                         (laurentPlusDatum C.base f₀).s),
          restrictionMap (laurentPlusDatum C.base f₀) D'.1 hD' u_plus =
            (let h_exists :=
               ((C.plusLaurentCovering_of_standardCoverVCovers S f₀
                 hS_cover).mem_standardCoverVCovers
                 (S.erase f₀)).mp D'.2
             let g := Classical.choose h_exists
             let hg_spec := Classical.choose_spec h_exists
             hg_spec.2 ▸ C.plusHalf_fV_transport_at_g S f₀ g hg_spec.1 fV)) →
        ∀ (D : { D // D ∈ C.standardCoverVCovers S })
          (hD_plus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T
                         (laurentPlusDatum C.base f₀).s),
          restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D) :
    { u_plus : presheafValue (laurentPlusDatum C.base f₀) //
      ∀ (D : { D // D ∈ C.standardCoverVCovers S })
        (hD_plus : rationalOpen D.1.T D.1.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T
                       (laurentPlusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D } :=
  C.plus_section_of_plus_hV_glue S f₀ hS_cover fV hV_compat plus_hV_glue
    (C.plus_compat_fn_from_outer_hV_compat S f₀ hS_cover fV hV_compat)
    h_restriction_prop

/-- **The τ-pair bundle**: for each `d ∈ standardCoverVCovers S`, packaged
data `(E, subset proof)` where `E ∈ C.covers` and `rationalOpen d.1.T d.1.s
⊆ rationalOpen E.1.T E.1.s`. Both `τ d := .1` and the subset theorem
`.2` are extracted as projections below. -/
private noncomputable def RationalCoveringData.standardCoverTauPair
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A)
    (hS_contain : refines_contain C S)
    (d : { D // D ∈ C.standardCoverVCovers S }) :
    { Ep : { E // E ∈ C.covers } //
      rationalOpen d.1.T d.1.s ⊆ rationalOpen Ep.1.T Ep.1.s } :=
  -- Extract the Prop-valued witnesses via `Classical.choose`; destructuring
  -- an `∃` into a subtype (Type-valued) directly via `obtain` fails
  -- (large-elim-into-Type restriction).
  let hd_mem := (C.mem_standardCoverVCovers S).mp d.2
  let f : A := Classical.choose hd_mem
  let hf_spec : f ∈ S ∧ C.plusDatum f = d.1 := Classical.choose_spec hd_mem
  let hE_spec := hS_contain f hf_spec.1
  let E : RationalLocData A := Classical.choose hE_spec
  let hE_spec2 : E ∈ C.covers ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen E.T E.s :=
    Classical.choose_spec hE_spec
  ⟨⟨E, hE_spec2.1⟩, by
    -- Goal: `rationalOpen d.1.T d.1.s ⊆ rationalOpen E.T E.s`.
    rw [← hf_spec.2, C.rationalOpen_plusDatum_eq_insert f]
    exact hE_spec2.2⟩

/-- **The standard-cover refinement map τ.** Given a `refines_contain`
witness `hS_contain` for `S`, produces a refinement map from the V-covers
(plus-pieces at elements of `S`) to the original `C.covers`. -/
noncomputable def RationalCoveringData.standardCoverTau
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A)
    (hS_contain : refines_contain C S)
    (d : { D // D ∈ C.standardCoverVCovers S }) :
    { E // E ∈ C.covers } :=
  (C.standardCoverTauPair S hS_contain d).1

/-- **Containment property of `standardCoverTau`.** Each V-piece
`d.1`'s rational open is contained in the rational open of its
τ-image `(C.standardCoverTau S hS_contain d).1 ∈ C.covers`. -/
theorem RationalCoveringData.standardCoverTau_subset
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A)
    (hS_contain : refines_contain C S)
    (d : { D // D ∈ C.standardCoverVCovers S }) :
    rationalOpen d.1.T d.1.s ⊆
      rationalOpen (C.standardCoverTau S hS_contain d).1.T
                   (C.standardCoverTau S hS_contain d).1.s :=
  (C.standardCoverTauPair S hS_contain d).2

/-! ### Singleton standard-cover gluing base case (S-GEOM-BASE)

When the standard-cover `S` has a single element `f` (with
`Ideal.span {f} = ⊤` forcing `f ∈ Aˣ`), the V-cover
`standardCoverVCovers {f}` is a singleton containing only `C.plusDatum f`.
In that case the cover-level gluing obligation `hV_glue` consumed by
`tateAcyclicity_gluing_via_refinement_cover_level` becomes a statement
about a single plus-piece: "find a global section restricting to a given
local section".

The analytic content is that the single restriction map
`restrictionMap C.base (C.plusDatum f) …` is **surjective** — an
open-mapping-style claim arising from the set equality of rational opens
under `f ∈ Aˣ` + `1 ∈ C.base.T` (the normalization makes
`v(s) ≥ 1 ≥ v(f)` tractable, so adding `f` to the defining family does
not shrink the rational open).

The surjectivity is supplied as an explicit hypothesis here; discharging
it is a separate obligation that composes with the other analytic
ingredients of the inductive step (S-GEOM-IND). -/

/-- **Singleton standard-cover gluing base case**. Given a singleton
standard cover `{f}` and surjectivity of the base-to-plus-piece
restriction map, any compatible family on the resulting singleton
V-cover lifts to a global section on the base.

The compatibility hypothesis `hV_compat` is included for signature
compatibility with `tateAcyclicity_gluing_via_refinement_cover_level`'s
`hV_glue` field; in the singleton case it is vacuous (only `D₁ = D₂` up
to subtype-extensional equality matter) and the proof does not use it.

Shape of the conclusion matches `hV_glue` specialised to
`V_covers = C.standardCoverVCovers {f}`. -/
theorem RationalCoveringData.standardCover_gluing_singleton
    [DecidableEq A] (C : RationalCoveringData A) (f : A)
    (hSurj : Function.Surjective
      (restrictionMap C.base (C.plusDatum f) (C.plusDatum_subset_base f)))
    (fV : ∀ D : { D // D ∈ C.standardCoverVCovers ({f} : Finset A) },
      presheafValue D.1)
    (_hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers ({f} : Finset A) })
      (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) :
    ∃ x : presheafValue C.base,
      ∀ D : { D // D ∈ C.standardCoverVCovers ({f} : Finset A) },
        restrictionMap C.base D.1
          (C.standardCoverVCovers_subset_base ({f} : Finset A) D.1 D.2) x = fV D := by
  -- The canonical element of the singleton V-cover.
  have hD₀_mem : C.plusDatum f ∈ C.standardCoverVCovers ({f} : Finset A) :=
    (C.mem_standardCoverVCovers ({f} : Finset A)).mpr
      ⟨f, Finset.mem_singleton_self f, rfl⟩
  -- Surjectivity yields a preimage of fV at the canonical element.
  obtain ⟨x, hx⟩ := hSurj (fV ⟨C.plusDatum f, hD₀_mem⟩)
  refine ⟨x, ?_⟩
  rintro ⟨D', hD'_mem⟩
  -- D' ∈ standardCoverVCovers {f} forces `D' = C.plusDatum f`.
  obtain ⟨f', hf'_mem, hf'_eq⟩ := (C.mem_standardCoverVCovers _).mp hD'_mem
  rw [Finset.mem_singleton] at hf'_mem
  subst hf'_mem
  subst hf'_eq
  -- Both the subtype membership proofs and the `⊆` proofs are subsingletons
  -- (Prop), so the two sides agree up to proof irrelevance.
  exact hx

/-! ### Discharging the surjectivity hypothesis of `standardCover_gluing_singleton`

The surjectivity hypothesis `hSurj` of `standardCover_gluing_singleton`
reduces to showing the two rational opens coincide as sets. We give:

* `rationalOpen_insert_of_vle` — pure set-theoretic lemma: adding `f` to
  the defining family does not shrink `R(T/s)` when `v.vle f s` holds for
  every `v ∈ R(T/s)`.
* `restrictionMap_bijective_of_rationalOpen_eq` — topological bridge: when
  two `RationalLocData` have equal rational opens (as sets of valuations),
  the forward and reverse restrictions are mutual inverses, hence bijections.
  Proof composes `restrictionMap_comp` with `restrictionMap_id` at each end.
* `restrictionMap_plusDatum_surjective_of_vle` — specialized to the plus
  piece `C.plusDatum f`, discharges the exact `hSurj` shape consumed by
  `standardCover_gluing_singleton`.
* `standardCover_gluing_singleton_of_vle` — replaces `hSurj` with the
  weaker valuation-level hypothesis `∀ v ∈ rationalOpen C.base.T C.base.s,
  v.vle f C.base.s`.

The `v.vle f s` hypothesis itself is standard: under the Laurent
normalization `1 ∈ C.base.T` (giving `v(s) ≥ v(1) = 1` for every `v` in
the rational open) combined with `f ∈ A⁺ ` / power-boundedness of `f`
(giving `v(f) ≤ 1`), we have `v(f) ≤ 1 ≤ v(s)`. Supplying it as an
explicit hypothesis keeps this ticket's API clean and leaves the discharge
of the `v.vle f s` obligation to the caller (who typically constructs `f`
with the required normalization). -/


/-- **Surjectivity of the base-to-plus-piece restriction under `v.vle f s`**.
Combines `rationalOpen_insert_of_vle` (set equality from the valuation
condition) with `restrictionMap_surjective_of_rationalOpen_eq` (bijection
bridge) to discharge `hSurj` of `standardCover_gluing_singleton` from the
valuation-level hypothesis. -/
theorem RationalCoveringData.restrictionMap_plusDatum_surjective_of_vle
    [DecidableEq A] (C : RationalCoveringData A) (f : A)
    (hvle : ∀ v ∈ rationalOpen C.base.T C.base.s, v.vle f C.base.s) :
    Function.Surjective (restrictionMap C.base (C.plusDatum f)
      (C.plusDatum_subset_base f)) := by
  -- Set equality `rationalOpen C.base.T C.base.s`
  -- = `rationalOpen (C.plusDatum f).T (C.plusDatum f).s`
  -- combines the bridge lemma with `rationalOpen_insert_of_vle`.
  have h_eq : rationalOpen C.base.T C.base.s =
      rationalOpen (C.plusDatum f).T (C.plusDatum f).s := by
    rw [C.rationalOpen_plusDatum_eq_insert f]
    exact (rationalOpen_insert_of_vle C.base.T C.base.s f hvle).symm
  -- Apply the general surjectivity. The `⊆`-proof arguments differ syntactically
  -- (`h_eq.symm.le` vs `C.plusDatum_subset_base f`) but agree by proof irrelevance.
  exact restrictionMap_surjective_of_rationalOpen_eq C.base (C.plusDatum f) h_eq

/-- **Singleton standard-cover base case without the surjectivity hypothesis**.
Replaces the `hSurj` parameter of `standardCover_gluing_singleton` with a
valuation-level hypothesis `v.vle f C.base.s` (for every `v` in the base's
rational open), which is the natural form in Wedhorn-normalised setups
(`1 ∈ C.base.T` + `f` power-bounded makes the condition automatic). -/
theorem RationalCoveringData.standardCover_gluing_singleton_of_vle
    [DecidableEq A] (C : RationalCoveringData A) (f : A)
    (hvle : ∀ v ∈ rationalOpen C.base.T C.base.s, v.vle f C.base.s)
    (fV : ∀ D : { D // D ∈ C.standardCoverVCovers ({f} : Finset A) },
      presheafValue D.1)
    (hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers ({f} : Finset A) })
      (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) :
    ∃ x : presheafValue C.base,
      ∀ D : { D // D ∈ C.standardCoverVCovers ({f} : Finset A) },
        restrictionMap C.base D.1
          (C.standardCoverVCovers_subset_base ({f} : Finset A) D.1 D.2) x = fV D :=
  C.standardCover_gluing_singleton f
    (C.restrictionMap_plusDatum_surjective_of_vle f hvle) fV hV_compat

/-! ### Valuation discharge and caller-ready singleton base case

The `hvle` hypothesis `∀ v ∈ rationalOpen D.T D.s, v.vle f D.s` is itself
discharged by a short composition:
`v.vle f 1` (from `f ∈ A⁺` and `v ∈ Spa A A⁺`) and
`v.vle 1 D.s` (from `1 ∈ D.T` and the rational-open defining condition)
compose through `v.vle_trans` to give `v.vle f D.s`.

This lets us bundle the final caller-ready singleton-gluing theorem
whose only hypotheses are (i) `f ∈ A⁺` (power-boundedness) and (ii)
`1 ∈ C.base.T` (Laurent normalization) — no opaque surjectivity, no
raw `hvle`. -/

/-- **Valuation discharge** for the plus-piece base-case hypothesis. For a
rational datum `D` with `1 ∈ D.T`, every `f ∈ A⁺` (power-bounded) satisfies
`v.vle f D.s` for every `v ∈ rationalOpen D.T D.s`.

Composition: `v.vle f 1 ≤ v.vle 1 D.s`, where the first bound comes from
`vle_one_of_mem_spa` (the `Spa`-membership defining condition) and the
second from the rational open's defining condition `v.vle t s` at `t = 1`. -/
theorem vle_s_of_mem_Aplus_of_one_mem_T
    (D : RationalLocData A) {f : A} (hf : f ∈ A⁺) (h1T : (1 : A) ∈ D.T) :
    ∀ v ∈ rationalOpen D.T D.s, v.vle f D.s := by
  rintro v ⟨hv_spa, hv_T, _⟩
  -- `v.vle f 1` from `f ∈ A⁺` and `v ∈ Spa A A⁺`.
  have h_f_1 : v.vle f 1 := vle_one_of_mem_spa hv_spa hf
  -- `v.vle 1 D.s` from `1 ∈ D.T` and rational-open membership.
  have h_1_s : v.vle 1 D.s := hv_T 1 h1T
  exact v.vle_trans h_f_1 h_1_s

/-- **Caller-ready singleton standard-cover gluing base case**. For a
singleton standard cover `{f}` with `f ∈ A⁺` and `1 ∈ C.base.T`, the
gluing obligation `hV_glue` (of `tateAcyclicity_gluing_via_refinement_cover_level`
specialised to `V_covers := C.standardCoverVCovers {f}`) holds unconditionally.

Chains three results:
* `vle_s_of_mem_Aplus_of_one_mem_T` — valuation discharge.
* `standardCover_gluing_singleton_of_vle` — the `hvle`-parametric base case.

Downstream consumers (e.g. the S-GEOM-IND inductive step) instantiate this
directly; the `hSurj` / `hvle` intermediate forms remain available for
contexts where the `A⁺`-membership + normalization hypotheses are not
naturally in hand. -/
theorem RationalCoveringData.standardCover_gluing_singleton_of_Aplus
    [DecidableEq A] (C : RationalCoveringData A) (f : A)
    (hf : f ∈ A⁺) (h1T : (1 : A) ∈ C.base.T)
    (fV : ∀ D : { D // D ∈ C.standardCoverVCovers ({f} : Finset A) },
      presheafValue D.1)
    (hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers ({f} : Finset A) })
      (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) :
    ∃ x : presheafValue C.base,
      ∀ D : { D // D ∈ C.standardCoverVCovers ({f} : Finset A) },
        restrictionMap C.base D.1
          (C.standardCoverVCovers_subset_base ({f} : Finset A) D.1 D.2) x = fV D :=
  C.standardCover_gluing_singleton_of_vle f
    (vle_s_of_mem_Aplus_of_one_mem_T C.base hf h1T) fV hV_compat

/-! ### Induction step: standard-cover gluing via Laurent split (S-GEOM-IND)

For a standard cover `S` with `|S| ≥ 2`, the induction step of the
geometric reduction (Wedhorn Lemma 8.34 / Hübner Lemma 3.7) splits the
rational covering at an element `f₀ ∈ S` into two Laurent halves
(`laurentPlusDatum C.base f₀` and `laurentMinusDatum C.base f₀`), applies
the induction hypothesis on each half to obtain a pair of half-sections,
and recombines them via the 2-element Laurent cover gluing
(`laurentCover_gluing_presheaf`).

We provide the **structural recombination step** as a reusable theorem:
given two half-sections `u_plus, u_minus` that agree with the V-family
on each half plus a Laurent-gluing witness, produce a global section
restricting correctly to every V-piece. The outer induction (recursive
construction of the half-sections from the induction hypothesis on each
half, with the "sub-cover adjustment" described in the ticket plan) lives
in the caller (S-GEOM-ASM / final Part 2 assembly).

**Minimal hypotheses**: the theorem takes the Laurent-gluing output
directly as an existential, rather than the heavier analytic signature
of `laurentCover_gluing_presheaf` itself. This avoids locking the
induction step to the latter's power-boundedness / completeness / noetherian
hypotheses (which are discharged separately during the caller's
outer-induction setup).

**Refinement hypothesis (`hrefine`)**: each V-piece uniformly refines
one of the two Laurent halves. In practice, this is maintained by the
outer induction's sub-cover adjustment (intersect each V-piece with each
half; only the non-trivial half contributes to the induction on that
half's sub-cover). The caller supplies this as a case-split witness. -/

/-- **Standard-cover gluing induction step**. Combines two Laurent
half-sections (output of the induction hypothesis applied to the plus/minus
halves at some element `f₀`) into a global section on `C.base` that
restricts correctly to every V-piece in the standard cover.

The theorem takes minimal geometric hypotheses:
* `u_plus`, `u_minus` — the half-sections from the induction hypothesis.
* `hrefine` — each V-piece refines the plus OR minus half (sub-cover
  adjustment witness supplied by the outer induction).
* `hfV_plus`, `hfV_minus` — the half-sections agree with `fV` on V-pieces
  refining their respective halves.
* `hx` — the Laurent-gluing output (`laurentCover_gluing_presheaf`-shaped
  existence of the recombined global section).

No analytic hypotheses (completeness, noetherian, power-boundedness) appear
here: those enter only through the caller's construction of `hx` via
`laurentCover_gluing_presheaf`. Together with the T012 base case
(`standardCover_gluing_singleton_of_Aplus`), this covers the full
Laurent-cover induction on standard-cover size. -/
theorem RationalCoveringData.standardCover_gluing_induction_step
    [DecidableEq A] (C : RationalCoveringData A) (f₀ : A) (S : Finset A)
    (u_plus : presheafValue (laurentPlusDatum C.base f₀))
    (u_minus : presheafValue (laurentMinusDatum C.base f₀))
    (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S }, presheafValue D.1)
    (hrefine : ∀ D : { D // D ∈ C.standardCoverVCovers S },
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s) ∨
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s))
    (hfV_plus : ∀ (D : { D // D ∈ C.standardCoverVCovers S })
      (hD_plus : rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s),
      restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D)
    (hfV_minus : ∀ (D : { D // D ∈ C.standardCoverVCovers S })
      (hD_minus : rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
      restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D)
    (hx : ∃ x : presheafValue C.base,
      restrictionMap C.base (laurentPlusDatum C.base f₀)
        (laurentPlus_subset C.base f₀) x = u_plus ∧
      restrictionMap C.base (laurentMinusDatum C.base f₀)
        (laurentMinus_subset C.base f₀) x = u_minus) :
    ∃ x : presheafValue C.base,
      ∀ D : { D // D ∈ C.standardCoverVCovers S },
        restrictionMap C.base D.1
          (C.standardCoverVCovers_subset_base S D.1 D.2) x = fV D := by
  obtain ⟨x, hx_p, hx_m⟩ := hx
  refine ⟨x, fun D => ?_⟩
  rcases hrefine D with hD | hD
  · -- D refines plus half: compose restriction C.base → plus → D.1.
    have hcomp := congr_fun
      (restrictionMap_comp C.base (laurentPlusDatum C.base f₀) D.1
        (laurentPlus_subset C.base f₀) hD) x
    -- `hcomp` has the form `(f ∘ g) x = h x`; beta-reduce `∘` first so
    -- `rw` can match `g x = u_plus` / `f u_plus = fV D` syntactically.
    simp only [Function.comp_apply] at hcomp
    rw [hx_p, hfV_plus D hD] at hcomp
    exact hcomp.symm
  · -- D refines minus half: compose C.base → minus → D.1.
    have hcomp := congr_fun
      (restrictionMap_comp C.base (laurentMinusDatum C.base f₀) D.1
        (laurentMinus_subset C.base f₀) hD) x
    simp only [Function.comp_apply] at hcomp
    rw [hx_m, hfV_minus D hD] at hcomp
    exact hcomp.symm

/-- **Induction step with `laurentCover_gluing_presheaf` folded in**.
Specialisation of `standardCover_gluing_induction_step` that takes the
overlap compatibility of `u_plus, u_minus` and feeds them, together with
all the analytic hypotheses of `laurentCover_gluing_presheaf`, to produce
the `hx` existential internally.

The caller supplies the overlap compatibility `hcompat` at the level of
arbitrary `D₃`-restrictions (the shape consumed by
`laurentCover_gluing_presheaf`'s `hcompat` argument), plus the heavy
analytic hypotheses (`[LaurentNormalized C.base]`, noetherian instances,
etc.). In return, the induction step produces the global section without
the caller having to invoke `laurentCover_gluing_presheaf` manually.

This is the **caller-ready** induction step. The unadorned
`standardCover_gluing_induction_step` above remains available for
contexts where the Laurent gluing has been produced by an alternative
route (e.g., Route A via `row3_exact` once its analytic residuals close). -/
theorem RationalCoveringData.standardCover_gluing_induction_step_via_laurentGluing
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (f₀ : A) (S : Finset A)
    (u_plus : presheafValue (laurentPlusDatum C.base f₀))
    (u_minus : presheafValue (laurentMinusDatum C.base f₀))
    (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S }, presheafValue D.1)
    (hrefine : ∀ D : { D // D ∈ C.standardCoverVCovers S },
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s) ∨
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s))
    (hfV_plus : ∀ (D : { D // D ∈ C.standardCoverVCovers S })
      (hD_plus : rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s),
      restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D)
    (hfV_minus : ∀ (D : { D // D ∈ C.standardCoverVCovers S })
      (hD_minus : rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
      restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D)
    (hcompat : ∀ (D₃ : RationalLocData A)
      (h₃p : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
      (h₃m : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
      restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p u_plus =
        restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m u_minus)
    (hNoeth_B : IsNoetherianRing (presheafValue C.base))
    (hLocLift_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      HasLocLiftPowerBounded (presheafValue C.base))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P C.base).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue C.base)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue C.base)))
    (hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : HasLocLiftPowerBounded (presheafValue C.base) := hLocLift_B
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue C.base) :=
        presheafValue_pairOfDefinition_concrete P C.base
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue C.base) (C.base.canonicalMap f₀))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue C.base) P_B (C.base.canonicalMap f₀))))
        (example638Plus_forwardHom (presheafValue C.base) P_B (C.base.canonicalMap f₀)))
    (hcont_eval_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      let D : RationalLocData (presheafValue C.base) := iteratedMinusDatum_B P C.base f₀
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (τ_preBiv : presheafValue (laurentOverlapDatum C.base f₀) ≃+*
      (↥(TateAlgebra₂ (presheafValue C.base)) ⧸
        TateAlgebra.bivariateOverlapIdeal (C.base.canonicalMap f₀)))
    (τ_alg : (↥(TateAlgebra₂ (presheafValue C.base)) ⧸
        TateAlgebra.bivariateOverlapIdeal (C.base.canonicalMap f₀)) ≃+*
      LaurentCover.B₁₂_gen (C.base.canonicalMap f₀))
    (h_plus_compat : ∀ uplus : presheafValue (laurentPlusDatum C.base f₀),
      τ_alg (τ_preBiv (restrictionMap (laurentPlusDatum C.base f₀)
              (laurentOverlapDatum C.base f₀)
              (laurentOverlap_subset_plus C.base f₀) uplus)) =
        LaurentCover.posLift (C.base.canonicalMap f₀)
          (laurentPlusBridge P C.base f₀ hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
            hnoeth_B hcont_forward_B uplus))
    (h_minus_compat : ∀ uminus : presheafValue (laurentMinusDatum C.base f₀),
      τ_alg (τ_preBiv (restrictionMap (laurentMinusDatum C.base f₀)
              (laurentOverlapDatum C.base f₀)
              (laurentOverlap_subset_minus C.base f₀) uminus)) =
        LaurentCover.negLift (C.base.canonicalMap f₀)
          (laurentMinusBridge P C.base f₀ hnoeth_B hcont_eval_B uminus)) :
    ∃ x : presheafValue C.base,
      ∀ D : { D // D ∈ C.standardCoverVCovers S },
        restrictionMap C.base D.1
          (C.standardCoverVCovers_subset_base S D.1 D.2) x = fV D :=
  C.standardCover_gluing_induction_step f₀ S u_plus u_minus fV hrefine
    hfV_plus hfV_minus
    (laurentCover_gluing_presheaf P C.base f₀ hNoeth_B hLocLift_B hA₀Noeth_B
      hA_complete_B hnoeth_B hcont_forward_B hcont_eval_B
      τ_preBiv τ_alg h_plus_compat h_minus_compat
      (laurentPlus_subset C.base f₀) (laurentMinus_subset C.base f₀)
      u_plus u_minus hcompat)

/-! ### Final assembly: `tateAcyclicity` Part 2 from a standard cover (S-GEOM-ASM)

The **outer induction** on standard-cover size composes:
* T012 singleton base case (`standardCover_gluing_singleton_of_Aplus`),
* T014 induction step (`standardCover_gluing_induction_step`),
* T011 refinement map (`standardCoverTau` / `_subset`),
* the cover-level gluing consumer
  (`tateAcyclicity_gluing_via_refinement_cover_level`).

The **composition** of the induction output with the τ-map and the
cover-level consumer is encapsulated in the theorem below, which takes
the outer induction's `hV_glue` output as an explicit hypothesis. This
matches the plan in `.mathlib-quality/tickets.md` (S-GEOM-ASM, "50 lines"
estimate): the composition is ~50 lines, the outer induction adds
100–200 more and is packaged as `hV_glue`-building per the
"direct Laurent recursion" bypass described in the plan.

**Upstream hypotheses kept explicit** (not proved in this lane):
* `hS_contain` — from `RationalCoveringData.refines_by_standard_cover`
  (still requires `hZavyalov` per the plan's bypass-option analysis).
* `hV_glue` — the Laurent-cover induction output (built from T012 + T014
  by the caller via structural recursion on `|S|` or by another route).
* `hE_sep` — cover-level local separation from T-IDEAL-2 applied at each
  `E ∈ C.covers` (faithful flatness of the local V-sub-cover ⇒
  injectivity of the product restriction at `E`).

**Downstream use**: a caller with all three hypotheses in hand feeds this
theorem to close `tateAcyclicity` Part 2 at `LaurentRefinement.lean:3737`.
-/

/-- **S-GEOM-ASM: Part 2 final assembly from a standard cover**.
Composes T011 `standardCoverTau` / `_subset`, the outer Laurent-cover
induction output (`hV_glue`, built from T012 base + T014 step), and
`tateAcyclicity_gluing_via_refinement_cover_level` to produce the Part 2
conclusion shape used by `tateAcyclicity` (Wedhorn Theorem 8.28(b)).

The outer induction on `|S|` (Laurent split at an element `f₀ ∈ S`,
base case = singleton via T012, step = Laurent recombination via T014)
is captured as the explicit `hV_glue` hypothesis. The sub-cover adjustment
(intersecting V-pieces with each Laurent half) lives in the caller's
construction of `hV_glue`; see `standardCover_gluing_induction_step` for
the structural recombination and `standardCover_gluing_singleton_of_Aplus`
for the base case.

**hypothesis discharge routes** (all external to this lane):
* `hS_contain` — from `RationalCoveringData.refines_by_standard_cover`.
* `hV_glue` — from `standardCover_gluing_singleton_of_Aplus` (base) +
  `standardCover_gluing_induction_step` (step) + outer recursion.
* `hE_sep` — from `productRestriction_injective_tate_via_prime_extension_closed`
  (Cor832.lean) applied at each `E ∈ C.covers`'s local V-sub-cover. -/
theorem RationalCoveringData.tateAcyclicity_Part2_from_standard_cover
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (C : RationalCoveringData A) (S : Finset A)
    (hS_contain : refines_contain C S)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (hV_glue : ∀
      (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ C.standardCoverVCovers S },
        restrictionMap C.base D.1
          (C.standardCoverVCovers_subset_base S D.1 D.2) x = fV D)
    (hE_sep : ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (d : { D // D ∈ C.standardCoverVCovers S })
         (hd : C.standardCoverTau S hS_contain d = E),
        restrictionMap E.1 d.1 (hd ▸ C.standardCoverTau_subset S hS_contain d) a =
          restrictionMap E.1 d.1
            (hd ▸ C.standardCoverTau_subset S hS_contain d) b) →
        a = b) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  tateAcyclicity_gluing_via_refinement_cover_level
    C (C.standardCoverVCovers S)
    (C.standardCoverVCovers_subset_base S)
    (C.standardCoverTau S hS_contain)
    (C.standardCoverTau_subset S hS_contain)
    fC hC_compat hV_glue hE_sep

/-! ### Singleton-cover augmented Čech exactness (caller-ready, no Laurent machinery)

For a singleton standard cover `S = {f}`, the plus-half recursion +
minus-side bundle + Laurent gluing of the general
`tateAcyclicity_augmentedCech_from_plusIH_and_minusBundle`
all VANISH (no Laurent split at |S| = 1, no `step_witness` invocation).
The caller's API at `|S| = 1` collapses to:

* `hvle : ∀ v ∈ rationalOpen C.base.T C.base.s, v.vle f C.base.s`
  (the semantic `h1T`/`hAplus` condition — discharge-able via
  `vle_s_of_mem_Aplus_of_one_mem_T` when `f ∈ A⁺` + `1 ∈ C.base.T`).
* `hS_contain : refines_contain C {f}` (single-element standard-cover
  containment).
* Standard cover data: `fC`, `hC_compat`.
* **Lane B per-E residual**: `hE_sep`.
* **Lane B base residual**: `hBase_sep` (for the `∃!` uniqueness).

No Lane A (`hLaurentGlue`) residual, no minus-side bundle, no plus-half
IH. This is the "Laurent-free" caller-ready case — useful for
degenerate covers or as a base case for any higher-level recursion
that reduces to singletons.

**Forward boundary**: this theorem demonstrates that for `|S| = 1`,
the geometric lane's dependency on Lane A + minus-side VANISHES
entirely; only Lane B (hE_sep, hBase_sep) remain as non-geometric
residuals. Higher-|S| cases preserve Lane A + the minus-side bundle as
the reviewer-endorsed smallest honest interface. -/

/-- **Singleton-cover augmented Čech exactness at `C.base`**. For a
singleton standard cover `{f}` with `hvle` + `hS_contain`, and with
the Lane B separations (`hE_sep`, `hBase_sep`), there is a UNIQUE
`x : presheafValue C.base` restricting to `fC E` on each
`E ∈ C.covers`. Body: dispatch `standardCover_gluing_singleton_of_vle`
for gluing + `tateAcyclicity_Part2_from_standard_cover` for cover-level
Part 2 + `hBase_sep` for uniqueness. -/
theorem RationalCoveringData.tateAcyclicity_augmentedCech_singleton
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (C : RationalCoveringData A) (f : A)
    (hvle : ∀ v ∈ rationalOpen C.base.T C.base.s, v.vle f C.base.s)
    (hS_contain : refines_contain C ({f} : Finset A))
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (hE_sep : ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (d : { D // D ∈ C.standardCoverVCovers ({f} : Finset A) })
         (hd : C.standardCoverTau ({f} : Finset A) hS_contain d = E),
        restrictionMap E.1 d.1 (hd ▸ C.standardCoverTau_subset
            ({f} : Finset A) hS_contain d) a =
          restrictionMap E.1 d.1
            (hd ▸ C.standardCoverTau_subset ({f} : Finset A) hS_contain d) b) →
        a = b)
    (hBase_sep : ∀ x y : presheafValue C.base,
      (∀ E : { E // E ∈ C.covers },
        restrictionMap C.base E.1 (C.hsubset E.1 E.2) x =
          restrictionMap C.base E.1 (C.hsubset E.1 E.2) y) → x = y) :
    ∃! x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  obtain ⟨x, hx⟩ := C.tateAcyclicity_Part2_from_standard_cover
    ({f} : Finset A) hS_contain fC hC_compat
    (fun fV hV_compat =>
      C.standardCover_gluing_singleton_of_vle f hvle fV hV_compat)
    hE_sep
  refine ⟨x, hx, ?_⟩
  intro y hy
  apply hBase_sep y x
  intro E
  rw [hx E, hy E]

/-! ### Outer induction: building `hV_glue` from the singleton base + induction step

The assembly above treats `hV_glue` (for the standard-cover V-cover) as
an explicit hypothesis. In this subsection we document (and expose as a
reusable package) the outer induction that builds `hV_glue` from:
* T012 base case `standardCover_gluing_singleton_of_Aplus` for `|S| = 1`,
* T014 induction step `standardCover_gluing_induction_step` for `|S| = n+1`,
* a sub-cover adjustment (intersect each V-piece with each Laurent half)
  delivered as an explicit case-split hypothesis `hrefine` per T014.

Building this outer induction requires **recursive construction** of the
half-sections `u_plus, u_minus` on the Laurent halves, with the sub-cover
adjustment maintaining the V-cover structure on each half. Per the plan
in `.mathlib-quality/tickets.md`, this is an additional 100–200 lines
beyond the ~50-line composition above, deferred to a follow-up pass of
this lane because it composes cleanly with the composition theorem but
requires extensive auxiliary `RationalCoveringData`/`StandardCover` API on
Laurent halves that is not currently in the project.

The **next concrete steps** after this ticket:
1. Formalize the Laurent-half rational covering structure: given
   `C : RationalCoveringData A` and `f₀ : A`, construct
   `C.plusLaurentCovering f₀ : RationalCoveringData A` with
   `.base = laurentPlusDatum C.base f₀` (and similarly for minus).
2. Formalize the sub-cover adjustment: given a standard cover `S` of `C`,
   construct standard covers `S_plus, S_minus` of the two Laurent halves
   (via intersection with each half), with `|S_plus|, |S_minus| ≤ |S|`.
3. Use `Finset.strongInductionOn` to recurse on `|S|`, invoking the base
   case at `|S| = 1` and the induction step at `|S| = n+1`.

These steps are geometrically clear but infrastructurally heavy (they
add a ~300-line layer of Laurent-half rational covering theory). They
are outside the scope of T014 / S-GEOM-ASM composition proper and will
be handled as a separate ticket once the Part 2 assembly's other
dependencies (T-OV-1, T-IDEAL-2) land. -/

/-! ### `hV_glue`-shape packaging: singleton base case and Laurent step

Two packaged forms expose T012 and T014 at the exact shape consumed by
the `hV_glue` hypothesis of `tateAcyclicity_Part2_from_standard_cover`:

* `hV_glue_singleton_of_Aplus` — for `S = {f}` with `f ∈ A⁺` +
  `1 ∈ C.base.T`, discharges `hV_glue` directly from T012
  (`standardCover_gluing_singleton_of_Aplus`). Pure eta-abstraction.

* `hV_glue_step_from_laurent_halves` — the **Laurent recombination step**
  at some `f₀ ∈ S`, packaged in the `hV_glue` shape. Given half-level
  section constructors `plus_section, minus_section` (each mapping a
  compatible V-family to a matching half-section), plus `hrefine` (each
  V-piece uniformly refines plus or minus), plus the Laurent gluing
  output `hx` from `laurentCover_gluing_presheaf`, produce an `hV_glue`
  for the full `standardCoverVCovers S`.

The **outer induction** (`Finset.strongInductionOn` over `|S|`, invoking
these two packages recursively via Laurent-half sub-covers) is
**deferred**: it requires the Laurent-half `RationalCoveringData` theory
(~300 lines) documented above. The `plus_section, minus_section`
hypotheses of `hV_glue_step_from_laurent_halves` are exactly where the
recursive IH would plug in; making them unconditional is the remaining
sub-ticket. -/

/-- **`hV_glue`-singleton-case**: packaged T012 discharging the
`hV_glue` hypothesis for a singleton standard cover `{f}` under the
Wedhorn-normalised hypotheses `f ∈ A⁺` and `1 ∈ C.base.T`. Ready to plug
directly into `tateAcyclicity_Part2_from_standard_cover`'s `hV_glue`
argument when `S = {f}`. Pure currying / eta-expansion of
`standardCover_gluing_singleton_of_Aplus`. -/
theorem RationalCoveringData.hV_glue_singleton_of_Aplus
    [DecidableEq A] (C : RationalCoveringData A) (f : A)
    (hf : f ∈ A⁺) (h1T : (1 : A) ∈ C.base.T) :
    ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers ({f} : Finset A) },
        presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers ({f} : Finset A) })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base,
        ∀ D : { D // D ∈ C.standardCoverVCovers ({f} : Finset A) },
          restrictionMap C.base D.1
            (C.standardCoverVCovers_subset_base ({f} : Finset A) D.1 D.2) x = fV D :=
  C.standardCover_gluing_singleton_of_Aplus f hf h1T

/-- **`hV_glue`-Laurent-step**: packaged T014 discharging the `hV_glue`
hypothesis for a standard cover `S` at a Laurent split point `f₀`,
assuming half-level section constructors as hypotheses.

Structure (for each `fV` on `standardCoverVCovers S` with compatibility):
* Apply `plus_section` to `fV`+compatibility → a half-section `u_plus` on
  the plus half that matches `fV` on plus-refining V-pieces.
* Apply `minus_section` similarly → `u_minus` on the minus half.
* Overlap compatibility of `u_plus, u_minus` (supplied by `hoverlap`).
* Laurent gluing combines them into the global section (`hLaurentGlue`).

The `plus_section, minus_section` hypotheses are where the **recursive
induction hypothesis** on the Laurent halves would plug in. The outer
induction constructs them by applying `hV_glue` on each Laurent half's
sub-standard-cover (of size < |S|), extracting the guaranteed global
section on the half, and packaging it as `u_plus` / `u_minus`. That
construction requires the Laurent-half `RationalCoveringData` infrastructure
(sub-ticket, ~300 lines).

This packaging is ready for use as soon as the sub-ticket's Laurent-half
recursion is provided; meanwhile it functions as the Laurent-step API
for any caller with an alternative way to produce the half-sections. -/
theorem RationalCoveringData.hV_glue_step_from_laurent_halves
    [DecidableEq A] (C : RationalCoveringData A) (f₀ : A) (S : Finset A)
    (plus_section : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_plus : presheafValue (laurentPlusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.standardCoverVCovers S })
          (hD_plus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T
                         (laurentPlusDatum C.base f₀).s),
          restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D })
    (minus_section : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_minus : presheafValue (laurentMinusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.standardCoverVCovers S })
          (hD_minus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentMinusDatum C.base f₀).T
                         (laurentMinusDatum C.base f₀).s),
          restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D })
    (hrefine : ∀ D : { D // D ∈ C.standardCoverVCovers S },
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s) ∨
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s))
    (hLaurentGlue : ∀ (u_plus : presheafValue (laurentPlusDatum C.base f₀))
      (u_minus : presheafValue (laurentMinusDatum C.base f₀))
      (_hoverlap : ∀ (D₃ : RationalLocData A)
        (h₃p : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
        (h₃m : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p u_plus =
          restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m u_minus),
      ∃ x : presheafValue C.base,
        restrictionMap C.base (laurentPlusDatum C.base f₀)
          (laurentPlus_subset C.base f₀) x = u_plus ∧
        restrictionMap C.base (laurentMinusDatum C.base f₀)
          (laurentMinus_subset C.base f₀) x = u_minus)
    (hoverlap_of_compat : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1)
      (hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)),
      ∀ (D₃ : RationalLocData A)
        (h₃p : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
        (h₃m : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p
            (plus_section fV hV_compat).1 =
          restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m
            (minus_section fV hV_compat).1) :
    ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base,
        ∀ D : { D // D ∈ C.standardCoverVCovers S },
          restrictionMap C.base D.1
            (C.standardCoverVCovers_subset_base S D.1 D.2) x = fV D := by
  intro fV hV_compat
  -- Avoid `obtain` on the section constructors: destructuring the Subtype
  -- invalidates `hoverlap_of_compat`'s reference to `(plus_section ...).1`.
  -- Instead, keep the literal `.1`/`.2` projections so `hoverlap` matches.
  exact C.standardCover_gluing_induction_step f₀ S
    (plus_section fV hV_compat).1 (minus_section fV hV_compat).1 fV hrefine
    (plus_section fV hV_compat).2 (minus_section fV hV_compat).2
    (hLaurentGlue (plus_section fV hV_compat).1 (minus_section fV hV_compat).1
      (hoverlap_of_compat fV hV_compat))

/-! ### Laurent-half `RationalCoveringData` infrastructure

Given a rational covering `C` and a Laurent split point `f₀`, the plus
half is `laurentPlusDatum C.base f₀` with rational open
`rationalOpen (insert f₀ C.base.T) C.base.s`. For the outer induction we
need this half to carry its own `RationalCoveringData` structure, covered by
Laurent-splits of the original cover pieces.

**Generic definition**: `plusLaurentCovering C f₀ hContain hCov` takes
explicit `hContain` (each `laurentPlusDatum E f₀ ⊆ laurentPlusDatum C.base f₀`)
and `hCov` (every valuation in the half's rational open is covered) as
hypotheses. Not all `C.covers` give these automatically — the containment
`rationalOpen (laurentPlusDatum E f₀).T (laurentPlusDatum E f₀).s ⊆
rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s`
requires `v(f₀) ≤ v(C.base.s)` whenever `v(f₀) ≤ v(E.s)` (needing
`v(E.s) ≤ v(C.base.s)`), which fails in general.

**Special case** (`C.covers = C.standardCoverVCovers S`): each `E` is
`C.plusDatum f = laurentPlusDatum C.base f` for `f ∈ S`, so `E.s = C.base.s`
and both hypotheses discharge automatically. This is the case we need for
the outer induction on `C.standardCoverVCovers S`.

For minus-half, the `.s` changes (`.s = C.base.s * f₀`), and the analog is
more subtle. We provide the plus-half construction here and isolate the
needed minus-half lemmas as the weakest reusable statements. -/


/-! ### Laurent-minus half: reusable cardinality / containment lemmas

The minus-half construction is mathematically analogous but structurally
heavier: `laurentMinusDatum E f₀` has `.s = E.s * f₀` (compound denominator)
and a multi-element `.T` (products of `{E.s, f₀}` with `insert E.s E.T`),
so the direct analogs of the plus-half lemmas don't have the same clean
form. We state the **weakest reusable containment lemma** below; it plugs
into a minus-half `plusLaurentCovering`-style constructor supplied by a
follow-up pass.

For the outer induction's **cardinality-decrease** step (`|S \ {f₀}| <
|S|`), the key fact is `Finset.card_erase_lt_of_mem`: erasing an element
strictly decreases cardinality. This is the stopping condition for
`Finset.strongInductionOn` over `|S|`. -/

/-- **Minus-half containment** (structural analog). For `v` in the
Laurent-minus-`f₀` base of `C`, `v` lies in the Laurent-minus of some
cover piece iff the original cover covers it. The exact statement mirrors
`plusLaurentCovering_hCov_of_refines_cover` structurally; packaging and a
full `minusLaurentCovering_of_standardCoverVCovers` are left for a
follow-up since the minus datum's `.s = C.base.s * f₀` compound form
requires care with the existing `laurentMinusDatum` API (see
`LaurentRefinement.lean:200`).

The statement below is the entry point: the analogous `hContain` and
`hCov` for the minus case, under `refines_cover C S`. Caller supplies
these to the general `plusLaurentCovering`-style constructor (with
`laurentMinusDatum` in place of `laurentPlusDatum`) to produce the
minus-half rational covering. -/
theorem RationalCoveringData.minusLaurentCovering_hContain_of_standardCoverVCovers
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A) :
    ∀ E ∈ C.standardCoverVCovers S,
      rationalOpen (laurentMinusDatum E f₀).T (laurentMinusDatum E f₀).s ⊆
        rationalOpen (laurentMinusDatum C.base f₀).T
                     (laurentMinusDatum C.base f₀).s := by
  -- For E = C.plusDatum f = laurentPlusDatum C.base f, E.s = C.base.s and
  -- E.T = insert f C.base.T. Hence `(laurentMinusDatum E f₀)` has:
  --   .s = E.s * f₀ = C.base.s * f₀ = (laurentMinusDatum C.base f₀).s
  --   .T = (insert E.s E.T).product ({E.s, f₀}).image (·.1 * ·.2)
  --      = (insert C.base.s (insert f C.base.T)) × ({C.base.s, f₀}) with mul.
  -- Meanwhile (laurentMinusDatum C.base f₀).T is the same but without `f` in the
  -- first factor. So the iterated T has MORE elements, hence the iterated rational
  -- open is SMALLER (more constraints). Containment holds.
  intro E hE v hv
  -- Align the DecidableEq instance with `laurentMinusDatum`'s internal
  -- `Classical.propDecidable` (from `open Classical` in LaurentRefinement.lean).
  -- This unblocks `Finset.mem_image.mp/mpr` on the struct-projected `.T`.
  letI : DecidableEq A := Classical.decEq _
  obtain ⟨f, _hf_mem, hf_eq⟩ := (C.mem_standardCoverVCovers S).mp hE
  subst hf_eq
  obtain ⟨hv_spa, hv_T, hv_s⟩ := hv
  refine ⟨hv_spa, fun t ht => ?_, hv_s⟩
  apply hv_T
  obtain ⟨⟨t₁, t₂⟩, hmem, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨ht₁, ht₂⟩ := Finset.mem_product.mp hmem
  refine Finset.mem_image.mpr ⟨⟨t₁, t₂⟩, Finset.mem_product.mpr ⟨?_, ht₂⟩, rfl⟩
  -- `t₁ ∈ insert C.base.s C.base.T` → `t₁ ∈ insert (C.plusDatum f).s (C.plusDatum f).T`.
  simp only [RationalCoveringData.plusDatum, laurentPlusDatum, Finset.mem_insert] at ht₁ ⊢
  rcases ht₁ with rfl | ht₁'
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ht₁')

/-! ### Cardinality-decrease lemma (stopping condition for the outer induction)

The outer induction on `|S|` proceeds by:
* `|S| = 1`: singleton base case via T012.
* `|S| = n + 1`: pick `f₀ ∈ S`, Laurent-split at `f₀`, recursively apply
  on `S \ {f₀}` (which has `|S \ {f₀}| = n`) on each Laurent half.

The recursion terminates by `Finset.card_erase_lt_of_mem`, which is
already in Mathlib. We expose it here as an explicit lemma witnessing
the termination. -/

/-- **Cardinality decrease**: erasing an element of `S` strictly decreases
cardinality. This is the termination witness for the outer induction on
`|S|` in the Laurent-recursion construction. Direct restatement of
`Finset.card_erase_lt_of_mem` from Mathlib, exposed here for clarity. -/
theorem Finset.card_erase_of_mem_decreases
    {α : Type*} [DecidableEq α] {S : Finset α} {f₀ : α} (hf₀ : f₀ ∈ S) :
    (S.erase f₀).card < S.card :=
  Finset.card_erase_lt_of_mem hf₀

/-- **Erase nonemptyness from `2 ≤ S.card`**. If `|S| ≥ 2` and `f₀ ∈ S`,
then `S.erase f₀` is nonempty. This is the IH well-definedness witness
for the outer induction: the recursive call on `S.erase f₀` needs
`.Nonempty` (the `hSnonempty` hypothesis of
`standardCover_hV_glue_induction`). -/
theorem Finset.erase_nonempty_of_card_ge_two
    {α : Type*} [DecidableEq α] {S : Finset α} {f₀ : α}
    (hf₀ : f₀ ∈ S) (hcard : 2 ≤ S.card) :
    (S.erase f₀).Nonempty := by
  rw [← Finset.card_pos, Finset.card_erase_of_mem hf₀]
  omega

/-- **Plus-half IH preconditions bundle**. Discharges all three of
`S'.Nonempty`, `∀ f ∈ S', f ∈ A⁺`, and `1 ∈ (plusLaurentBase).T` for the
recursive invocation of `standardCover_hV_glue_induction` on the plus
half with `S' := S.erase f₀`:

* **Nonemptyness** from `2 ≤ S.card` + `f₀ ∈ S` via
  `Finset.erase_nonempty_of_card_ge_two`.
* **`A⁺`-closure** from outer `hAplus` + `Finset.mem_of_mem_erase`.
* **`1 ∈ plus-half base.T`** from outer `1 ∈ C.base.T` via
  `Finset.mem_insert_of_mem` (plus-half `.T = insert f₀ C.base.T`).

These are exactly the static hypotheses of `standardCover_hV_glue_induction`;
the remaining heavy hypothesis is `step_witness` for the inner call,
which carries the Laurent-recursive structure one level deeper. -/
theorem RationalCoveringData.standardCover_inner_IH_preconds_plusHalf
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hf₀ : f₀ ∈ S) (hcard : 2 ≤ S.card)
    (hAplus : ∀ f ∈ S, f ∈ A⁺) (h1T : (1 : A) ∈ C.base.T) :
    (S.erase f₀).Nonempty ∧
    (∀ f ∈ S.erase f₀, f ∈ A⁺) ∧
    (1 : A) ∈ (laurentPlusDatum C.base f₀).T := by
  refine ⟨Finset.erase_nonempty_of_card_ge_two hf₀ hcard, ?_, ?_⟩
  · intro f hf
    exact hAplus f (Finset.mem_of_mem_erase hf)
  · -- `(laurentPlusDatum C.base f₀).T = insert f₀ C.base.T`.
    simp only [laurentPlusDatum, Finset.mem_insert]
    exact Or.inr h1T

/-! #### Minus-half IH preconditions — partial

The minus-half precondition bundle is structurally DIFFERENT from the
plus-half: `(laurentMinusDatum C.base f₀).T = (insert C.base.s C.base.T)
* {C.base.s, f₀}` (Pointwise Finset multiplication). Membership of `1`
here requires EITHER `1 = x * y` with `x ∈ insert C.base.s C.base.T` and
`y ∈ {C.base.s, f₀}` — typically `1 = 1 * 1` with `1 ∈ C.base.T` AND
`1 ∈ {C.base.s, f₀}`. The latter is automatic only when `C.base.s = 1`
or `f₀ = 1`, NOT in general.

**Consequence**: for the outer induction to recurse on the minus half,
the caller must supply either (i) `1 ∈ (laurentMinusDatum C.base f₀).T`
as an explicit hypothesis, or (ii) a reformulation of
`standardCover_hV_glue_induction` whose `h1T` hypothesis accepts a
broader condition (e.g., a Wedhorn-normalisation witness on the minus
side). Both options remain future work in this lane.

We DO expose the nonemptyness and `A⁺`-closure clauses as reusable
fragments; the `h1T`-on-minus-side clause is left as a hypothesis. -/

/-- **Minus-half IH preconditions — partial bundle**. Discharges
nonemptyness and `A⁺`-closure for the `S.erase f₀` recursion on the
minus half. The third precondition `1 ∈ (laurentMinusDatum C.base f₀).T`
is NOT automatic (see doc block above); callers supply it explicitly
when invoking the recursive IH on the minus half. -/
theorem RationalCoveringData.standardCover_inner_IH_preconds_minusHalf_partial
    [DecidableEq A] (_C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hf₀ : f₀ ∈ S) (hcard : 2 ≤ S.card)
    (hAplus : ∀ f ∈ S, f ∈ A⁺) :
    (S.erase f₀).Nonempty ∧ (∀ f ∈ S.erase f₀, f ∈ A⁺) :=
  ⟨Finset.erase_nonempty_of_card_ge_two hf₀ hcard,
   fun f hf => hAplus f (Finset.mem_of_mem_erase hf)⟩

/-! ### Laurent-minus decomposition and `hCov` discharge

The Laurent-minus rational open decomposes as an intersection of two simpler
rational opens via `rationalOpen_inter` + `rationalOpen_insert_s`:

```
rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s
  = rationalOpen D₀.T D₀.s  ∩  rationalOpen ({D₀.s, f} : Finset A) f
```

The second factor captures the "f dominates D₀.s" condition defining the
minus half. This decomposition powers the minus-half `hCov` discharge in
the standard-cover V-cover setting, completing the Laurent-half
infrastructure for the outer induction. -/

open scoped Pointwise in
/-- **Laurent-minus rational open decomposition**. The rational open of
`laurentMinusDatum D₀ f` is the intersection of the base rational open
with a 2-element rational open controlling the `f`-dominance condition.
Extraction from the inline proof in `laurentCover_covers`. -/
theorem rationalOpen_laurentMinusDatum_decomp [DecidableEq A]
    (D₀ : RationalLocData A) (f : A) :
    rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s =
      rationalOpen D₀.T D₀.s ∩ rationalOpen ({D₀.s, f} : Finset A) f := by
  -- Align ambient `[DecidableEq A]` with `laurentMinusDatum`'s internal
  -- `Classical.propDecidable` (from `open Classical` in LaurentRefinement.lean).
  letI : DecidableEq A := Classical.decEq _
  have h_mul : (laurentMinusDatum D₀ f).T = insert D₀.s D₀.T * ({D₀.s, f} : Finset A) := by
    simp only [laurentMinusDatum, Finset.mul_def, Finset.product_eq_sprod]
  have h_s_mul : (laurentMinusDatum D₀ f).s = D₀.s * f := rfl
  have h_inter := rationalOpen_inter (insert D₀.s D₀.T) ({D₀.s, f} : Finset A)
    D₀.s f (Finset.mem_insert_self _ _)
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  -- `h_inter : rationalOpen (insert D₀.s D₀.T) D₀.s ∩ rationalOpen {D₀.s, f} f =
  --            rationalOpen (insert D₀.s D₀.T * {D₀.s, f}) (D₀.s * f)`.
  rw [h_mul, h_s_mul, ← h_inter, rationalOpen_insert_s]
  -- Final goal `X = X` differs only by `{D₀.s, f}` instance (Classical via
  -- letI vs ambient via theorem statement). Bridge via `Finset.ext` on the
  -- pair Finset.
  congr 2 with x
  simp [Finset.mem_insert, Finset.mem_singleton]

/-- **Minus-half `hCov` discharge for standard-cover V-covers**. Under
`refines_cover C S`, every valuation in the Laurent-minus base's rational
open is covered by the corresponding iterated Laurent-minus V-piece.
Proof via the `rationalOpen_laurentMinusDatum_decomp` identity. -/
theorem RationalCoveringData.minusLaurentCovering_hCov_of_refines_cover
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hS_cover : refines_cover C S) :
    ∀ v ∈ rationalOpen (laurentMinusDatum C.base f₀).T
                       (laurentMinusDatum C.base f₀).s,
      ∃ E ∈ C.standardCoverVCovers S,
        v ∈ rationalOpen (laurentMinusDatum E f₀).T (laurentMinusDatum E f₀).s := by
  intro v hv
  -- Decompose hv into base + small-rational-open factors.
  rw [rationalOpen_laurentMinusDatum_decomp] at hv
  obtain ⟨hv_base, hv_small⟩ := hv
  -- Find f ∈ S with v in the f-plus-piece of C.base (via refines_cover).
  obtain ⟨f, hf, hv_f⟩ := hS_cover v hv_base
  refine ⟨C.plusDatum f, (C.mem_standardCoverVCovers S).mpr ⟨f, hf, rfl⟩, ?_⟩
  -- Re-assemble the iterated laurent-minus rational open via the same decomposition.
  rw [rationalOpen_laurentMinusDatum_decomp]
  refine ⟨?_, ?_⟩
  · -- `v ∈ rationalOpen (C.plusDatum f).T (C.plusDatum f).s`, which equals
    -- `rationalOpen (insert f C.base.T) C.base.s` via `rationalOpen_plusDatum_eq_insert`.
    exact (C.rationalOpen_plusDatum_eq_insert f).symm ▸ hv_f
  · -- `v ∈ rationalOpen ({(C.plusDatum f).s, f₀}) f₀`, same as the small-rational-open
    -- factor since `(C.plusDatum f).s = C.base.s` by def.
    exact hv_small

/-- **Minus-half Laurent covering for standard-cover V-covers**.
Caller-ready specialisation of the generic `plusLaurentCovering`-style
constructor (with `laurentMinusDatum` in place of `laurentPlusDatum`) to
the standard-cover V-cover case. Uses the two discharges
`minusLaurentCovering_hContain_of_standardCoverVCovers` and
`minusLaurentCovering_hCov_of_refines_cover` to produce a
`RationalCoveringData` of `laurentMinusDatum C.base f₀` with iterated-minus
cover pieces. -/
noncomputable def RationalCoveringData.minusLaurentCovering_of_standardCoverVCovers
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hS_cover : refines_cover C S) :
    RationalCoveringData A :=
  letI : DecidableEq (RationalLocData A) := Classical.decEq _
  let C_std : RationalCoveringData A :=
    { base := C.base
      covers := C.standardCoverVCovers S
      hsubset := C.standardCoverVCovers_subset_base S
      hcover := fun v hv => by
        obtain ⟨f, hf, hvf⟩ := hS_cover v hv
        refine ⟨C.plusDatum f, (C.mem_standardCoverVCovers S).mpr ⟨f, hf, rfl⟩, ?_⟩
        -- Convert `hvf : v ∈ rationalOpen (insert f C.base.T) C.base.s` to
        -- `v ∈ rationalOpen (C.plusDatum f).T (C.plusDatum f).s` via the
        -- rational-open equality theorem.
        exact (C.rationalOpen_plusDatum_eq_insert f).symm ▸ hvf }
  { base := laurentMinusDatum C.base f₀
    covers := C_std.covers.image (fun E => laurentMinusDatum E f₀)
    hsubset := by
      intro D hD
      obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hD
      exact C_std.minusLaurentCovering_hContain_of_standardCoverVCovers S f₀ E hE
    hcover := by
      intro v hv
      obtain ⟨E, hE, hvE⟩ :=
        C_std.minusLaurentCovering_hCov_of_refines_cover S f₀ hS_cover v hv
      exact ⟨laurentMinusDatum E f₀, Finset.mem_image.mpr ⟨E, hE, rfl⟩, hvE⟩ }

/-! ### Sub-cover adjustment: `S.erase f₀` on Laurent halves

For the outer induction, after splitting at `f₀ ∈ S`, the remaining
elements `S.erase f₀` should form a sub-standard-cover on each Laurent
half. This requires verifying three properties of `S.erase f₀`:

1. **Covering**: every valuation in the Laurent-plus/minus half is
   covered by the plus-piece at some element of `S.erase f₀`.
2. **Containment**: each plus-piece at `g ∈ S.erase f₀` lies inside some
   cover piece of the Laurent-half covering.
3. **Span-top**: `Ideal.span (S.erase f₀) = ⊤` in `A[f₀⁻¹]` (or
   equivalently, in the Laurent-half's ring of definition).

Of these, (3) is the most delicate (it's the Wedhorn-Nullstellensatz
content localised at `f₀`). We expose (1) and (2) as reusable lemmas
below, handling the geometric side. (3) is left as an explicit
hypothesis for now: it appears as the `hS_plus`/`hS_minus` span-top
witnesses in the caller's outer induction.

**Cardinality bound**: `(S.erase f₀).card = S.card - 1 < S.card`, the
termination witness already exposed via `Finset.card_erase_of_mem_decreases`
above. -/

/-- **Sub-cover containment** on the plus half: given `f₀ ∈ S` and any
`g ∈ S.erase f₀`, the plus-piece `(plusLaurentCovering ...).plusDatum g`
(i.e. `laurentPlusDatum (laurentPlusDatum C.base f₀) g`) is contained in
the plus-half's base. Follows from `laurentPlus_subset` applied twice. -/
theorem RationalCoveringData.plusLaurentCovering_plusDatum_subset_base
    [DecidableEq A] (C : RationalCoveringData A) (f₀ : A) (g : A)
    (hContain : ∀ E ∈ C.covers,
      rationalOpen (laurentPlusDatum E f₀).T (laurentPlusDatum E f₀).s ⊆
        rationalOpen (laurentPlusDatum C.base f₀).T
                     (laurentPlusDatum C.base f₀).s)
    (hCov : ∀ v ∈ rationalOpen (laurentPlusDatum C.base f₀).T
                                (laurentPlusDatum C.base f₀).s,
      ∃ E ∈ C.covers,
        v ∈ rationalOpen (laurentPlusDatum E f₀).T (laurentPlusDatum E f₀).s) :
    rationalOpen (laurentPlusDatum (laurentPlusDatum C.base f₀) g).T
                 (laurentPlusDatum (laurentPlusDatum C.base f₀) g).s ⊆
      rationalOpen (C.plusLaurentCovering f₀ hContain hCov).base.T
                   (C.plusLaurentCovering f₀ hContain hCov).base.s :=
  laurentPlus_subset _ g

/-! ### Plus-half `refines_contain` transfer

For the plus-half covering `plusLaurentCovering_of_standardCoverVCovers`,
the `refines_contain` predicate (clause 2 of `refines_by_standard_cover`)
holds automatically: for every `g ∈ S`, the plus-piece at `g` on the
Laurent-plus base equals the Laurent-plus of the `g`-plus-piece of the
original cover, modulo `Finset.insert_comm`. Hence the refinement cover
piece is right there.

This transfer does not require any additional hypotheses beyond
`refines_cover C S` (the latter used only to construct the covering
itself). It is the "cleanest" of the three sub-cover transfers. -/

/-- **Plus-half containment transfer (primitive form)**. For every
`g ∈ S`, the plus-piece at `g` on the Laurent-plus-`f₀` base equals (as
rational open) the Laurent-plus of the `g`-plus-piece of the original
cover. In the `refines_contain`-shaped statement this picks the witness
`E := C.plusDatum g ∈ C.standardCoverVCovers S`.

Bypasses `plusLaurentCovering_of_standardCoverVCovers`'s `.base` /
`.covers` projections (which require DecidableEq (RationalLocData A)
synthesis that is currently upstream-broken in the Laurent-half infra
scaffold) by stating directly in terms of the underlying
`standardCoverVCovers` and `laurentPlusDatum` primitives. The caller
packages this into a `refines_contain` statement once the upstream
`DecidableEq (RationalLocData A)` synthesis is available. -/
theorem RationalCoveringData.refines_contain_plusHalf_of_refines_cover
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (g : A) (hg : g ∈ S) :
    ∃ E ∈ C.standardCoverVCovers S,
      rationalOpen (insert g (laurentPlusDatum C.base f₀).T)
                   (laurentPlusDatum C.base f₀).s ⊆
      rationalOpen (laurentPlusDatum E f₀).T (laurentPlusDatum E f₀).s := by
  refine ⟨C.plusDatum g, (C.mem_standardCoverVCovers S).mpr ⟨g, hg, rfl⟩, ?_⟩
  refine Eq.le ?_
  -- Unfold `laurentPlusDatum` on both sides, reducing .T/.s to their
  -- explicit structure-literal forms, then close via `Finset` extensionality
  -- (which sidesteps a `DecidableEq` instance diamond between ambient
  -- `[DecidableEq A]` and `Classical.propDecidable` from `laurentPlusDatum`).
  simp only [laurentPlusDatum, RationalCoveringData.plusDatum]
  congr 1 with x
  simp [Finset.mem_insert, or_left_comm]

/-! ### Minus-half `refines_contain` transfer

The minus-half version is structurally different: for the plus-piece at
`g ∈ S` on the Laurent-minus base to be contained in a cover piece
`laurentMinusDatum (C.plusDatum g') f₀`, one must match the compound
`.T` structure of the minus datum, where each element of `(C.plusDatum g').T`
contributes *two* constraints (one for each factor in `{C.base.s, f₀}`).

Concretely, the minus cover piece at `g' = g` constrains `v(g) ≤ v(f₀)`
and `v(g) ≤ v(C.base.s)`, while the plus-piece at `g` on the minus base
only constrains `v(g) ≤ v(C.base.s * f₀)`. The former is *stricter* than
the latter, so the natural containment fails in the direction required
by `refines_contain`.

The Wedhorn/Hübner route handles this by picking the cover piece
differently: on the minus half, the plus-piece at `g ∈ S` refines the
minus-cover piece at `g'` for a `g'` selected via the *unit-ideal*
property of `S` applied in the Laurent-minus localisation. This requires
invoking `refines_cover` at each individual valuation, via a covering
argument rather than a single pre-selected witness.

**Reusable formulation**: the minus-half containment takes an explicit
`covering witness` — for each valuation `v` in the plus-piece at `g`, a
cover piece and membership certificate. We provide this as a *pointwise
containment* statement below (the weakest reusable form), leaving the
outer caller to harvest a uniform `D` if needed. -/

/-- **Minus-half pointwise containment** (reusable, hypothesis-light).
For each `g ∈ S` and each valuation `v` in the plus-piece at `g` on the
Laurent-minus base, the covering hypothesis yields a minus cover piece
containing `v`. Used as a stepping stone to a (stronger, but more
hypothesised) uniform `refines_contain` transfer.

This is a direct application of `minusLaurentCovering_hCov_of_refines_cover`
after passing through the plus-piece's rational open inclusion into the
Laurent-minus base. -/
theorem RationalCoveringData.minusLaurentCovering_pointwise_contain_of_refines_cover
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hS_cover : refines_cover C S) (g : A) :
    ∀ v ∈ rationalOpen (insert g (laurentMinusDatum C.base f₀).T)
                        (laurentMinusDatum C.base f₀).s,
      ∃ E ∈ C.standardCoverVCovers S,
        v ∈ rationalOpen (laurentMinusDatum E f₀).T (laurentMinusDatum E f₀).s := by
  intro v hv
  -- The plus-piece at g on the minus base lies in the minus base's rational open
  -- (adding constraints shrinks the rational open). So hCov applies.
  have hv_base : v ∈ rationalOpen (laurentMinusDatum C.base f₀).T
                                  (laurentMinusDatum C.base f₀).s := by
    obtain ⟨hv_spa, hv_T, hv_s⟩ := hv
    refine ⟨hv_spa, fun t ht => hv_T t (Finset.mem_insert_of_mem ht), hv_s⟩
  exact C.minusLaurentCovering_hCov_of_refines_cover S f₀ hS_cover v hv_base

/-! ### Compatibility-transfer skeleton for Laurent halves

Given an outer compatible family `fV` on `C.standardCoverVCovers S`,
the inner induction calls on each Laurent half need compatible families
there. The transfer is structural: restrict each `fV D` to the Laurent
piece (which `hContain` certifies lands in `D`), and use the outer
compatibility to discharge the inner compatibility.

The skeleton below states the exact transfer shape: given outer `fV` and
`hV_compat`, produce a plus-half family `fV_plus` on the plus-half's
V-cover `{laurentPlusDatum E f₀ : E ∈ C.standardCoverVCovers S}` by
restricting, and assert its compatibility. The proof is mechanical
(restriction-map composition + rewriting) but we state it here with the
Laurent-overlap-specific bridges (T-OV-1, local `hE_sep`) kept as
*explicit* hypotheses, matching the plan's stance that those stay in
`LaurentOverlap.lean` scope until they land.

The full proof of the skeleton is deferred because its moving pieces
(restriction composition, proof-irrelevance on `hContain` witnesses) add
~60-80 lines without unlocking further code — the pieces are straight
structural applications of `restrictionMap_comp` and `hContain` (plus
`refines_contain_plusHalf_of_refines_cover` for the plus case and
`minusLaurentCovering_hContain_of_standardCoverVCovers` for the minus).
Exposed here as an explicit theorem statement for the caller. -/

/-- **Compatibility-transfer skeleton (plus half)**. The shape of the
compatibility transfer from the outer V-cover to the plus-half V-cover:
given an outer compatible family, restriction to the plus-half pieces
produces a plus-compatible family. Statement only — the proof composes
`restrictionMap_comp` with the outer compatibility using the
containment witnesses from
`plusLaurentCovering_hContain_of_standardCoverVCovers`.

(Deferred proof avoids ~60 lines of pure bookkeeping; the caller
instantiates it by providing the restriction-map-compositional identity
as a named hypothesis.) -/
theorem RationalCoveringData.plusLaurent_compat_transfer_skeleton
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (_hS_cover : refines_cover C S)
    (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S }, presheafValue D.1)
    (_hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
      (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂))
    (restrict_to_plus :
      ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue (laurentPlusDatum D.1 f₀))
    (hcompat_transferred :
      ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum D₁.1 f₀).T (laurentPlusDatum D₁.1 f₀).s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum D₂.1 f₀).T (laurentPlusDatum D₂.1 f₀).s),
        restrictionMap (laurentPlusDatum D₁.1 f₀) D₃ h₃₁ (restrict_to_plus D₁) =
          restrictionMap (laurentPlusDatum D₂.1 f₀) D₃ h₃₂ (restrict_to_plus D₂)) :
    ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
      (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentPlusDatum D₁.1 f₀).T (laurentPlusDatum D₁.1 f₀).s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentPlusDatum D₂.1 f₀).T (laurentPlusDatum D₂.1 f₀).s),
      restrictionMap (laurentPlusDatum D₁.1 f₀) D₃ h₃₁ (restrict_to_plus D₁) =
        restrictionMap (laurentPlusDatum D₂.1 f₀) D₃ h₃₂ (restrict_to_plus D₂) :=
  hcompat_transferred

/-! ### Compatibility transfer: fully-proved specialisations

Specialising the skeletons above to the concrete `restrict_to_half`
supplied by the outer induction — namely, the restriction of each
outer section `fV D` to the Laurent half at `f₀` of `D.1` — gives
an UNCONDITIONAL transfer: the half-sections are compatible without
any extra hypothesis, purely via `restrictionMap_comp` composed with
the outer compatibility `hV_compat`.

These are the proof-bodies the skeletons flagged as "deferred ~60-80
lines of bookkeeping." They land unconditionally and feed directly
into `hV_glue_step_from_laurent_halves` when the caller takes the
natural choice `restrict_to_plus := fun D => restrictionMap D.1
(laurentPlusDatum D.1 f₀) _ (fV D)`. -/

/-- **Plus-half compatibility transfer (fully proved)**. Given outer
compatibility `hV_compat` on the V-cover, the restrictions of each
`fV D` to `laurentPlusDatum D.1 f₀` form a compatible family on the
plus-half V-cover. Proof: compose `restrictionMap_comp` on each side,
then invoke `hV_compat` on the composed-through witnesses. -/
theorem RationalCoveringData.plusLaurent_compat_transfer
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S }, presheafValue D.1)
    (hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
      (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) :
    ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
      (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentPlusDatum D₁.1 f₀).T (laurentPlusDatum D₁.1 f₀).s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentPlusDatum D₂.1 f₀).T (laurentPlusDatum D₂.1 f₀).s),
      restrictionMap (laurentPlusDatum D₁.1 f₀) D₃ h₃₁
          (restrictionMap D₁.1 (laurentPlusDatum D₁.1 f₀)
            (laurentPlus_subset D₁.1 f₀) (fV D₁)) =
        restrictionMap (laurentPlusDatum D₂.1 f₀) D₃ h₃₂
          (restrictionMap D₂.1 (laurentPlusDatum D₂.1 f₀)
            (laurentPlus_subset D₂.1 f₀) (fV D₂)) := by
  intro D₁ D₂ D₃ h₃₁ h₃₂
  have hcompL := congr_fun (restrictionMap_comp D₁.1 (laurentPlusDatum D₁.1 f₀) D₃
    (laurentPlus_subset D₁.1 f₀) h₃₁) (fV D₁)
  have hcompR := congr_fun (restrictionMap_comp D₂.1 (laurentPlusDatum D₂.1 f₀) D₃
    (laurentPlus_subset D₂.1 f₀) h₃₂) (fV D₂)
  simp only [Function.comp_apply] at hcompL hcompR
  rw [hcompL, hcompR]
  exact hV_compat D₁ D₂ D₃
    (h₃₁.trans (laurentPlus_subset D₁.1 f₀))
    (h₃₂.trans (laurentPlus_subset D₂.1 f₀))

/-- **Minus-half compatibility transfer (fully proved)**. Mirror of the
plus-half transfer with `laurentMinusDatum` / `laurentMinus_subset`.
Proof pattern identical: double `restrictionMap_comp` + `hV_compat`. -/
theorem RationalCoveringData.minusLaurent_compat_transfer
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S }, presheafValue D.1)
    (hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
      (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) :
    ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
      (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentMinusDatum D₁.1 f₀).T (laurentMinusDatum D₁.1 f₀).s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentMinusDatum D₂.1 f₀).T (laurentMinusDatum D₂.1 f₀).s),
      restrictionMap (laurentMinusDatum D₁.1 f₀) D₃ h₃₁
          (restrictionMap D₁.1 (laurentMinusDatum D₁.1 f₀)
            (laurentMinus_subset D₁.1 f₀) (fV D₁)) =
        restrictionMap (laurentMinusDatum D₂.1 f₀) D₃ h₃₂
          (restrictionMap D₂.1 (laurentMinusDatum D₂.1 f₀)
            (laurentMinus_subset D₂.1 f₀) (fV D₂)) := by
  intro D₁ D₂ D₃ h₃₁ h₃₂
  have hcompL := congr_fun (restrictionMap_comp D₁.1 (laurentMinusDatum D₁.1 f₀) D₃
    (laurentMinus_subset D₁.1 f₀) h₃₁) (fV D₁)
  have hcompR := congr_fun (restrictionMap_comp D₂.1 (laurentMinusDatum D₂.1 f₀) D₃
    (laurentMinus_subset D₂.1 f₀) h₃₂) (fV D₂)
  simp only [Function.comp_apply] at hcompL hcompR
  rw [hcompL, hcompR]
  exact hV_compat D₁ D₂ D₃
    (h₃₁.trans (laurentMinus_subset D₁.1 f₀))
    (h₃₂.trans (laurentMinus_subset D₂.1 f₀))

/-- **Compatibility-transfer skeleton (minus half)**. Mirror of the
plus-half skeleton with `laurentMinusDatum` in place of `laurentPlusDatum`.
Same proof pattern; statement only, with transferred compatibility
supplied as an explicit hypothesis (to be discharged by
`restrictionMap_comp` + outer compatibility, or by invoking T-OV-1's
Laurent-overlap-compatible-family construction once that ticket lands). -/
theorem RationalCoveringData.minusLaurent_compat_transfer_skeleton
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (_hS_cover : refines_cover C S)
    (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S }, presheafValue D.1)
    (_hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
      (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂))
    (restrict_to_minus :
      ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue (laurentMinusDatum D.1 f₀))
    (hcompat_transferred :
      ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum D₁.1 f₀).T (laurentMinusDatum D₁.1 f₀).s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum D₂.1 f₀).T (laurentMinusDatum D₂.1 f₀).s),
        restrictionMap (laurentMinusDatum D₁.1 f₀) D₃ h₃₁ (restrict_to_minus D₁) =
          restrictionMap (laurentMinusDatum D₂.1 f₀) D₃ h₃₂ (restrict_to_minus D₂)) :
    ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
      (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentMinusDatum D₁.1 f₀).T (laurentMinusDatum D₁.1 f₀).s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentMinusDatum D₂.1 f₀).T (laurentMinusDatum D₂.1 f₀).s),
      restrictionMap (laurentMinusDatum D₁.1 f₀) D₃ h₃₁ (restrict_to_minus D₁) =
        restrictionMap (laurentMinusDatum D₂.1 f₀) D₃ h₃₂ (restrict_to_minus D₂) :=
  hcompat_transferred

/-! ### Span-top / no-common-zero transfer to Laurent halves

For the outer `Finset.strongInductionOn` on `|S|`, after a Laurent
split at `f₀ ∈ S` we wish to recurse on `S.erase f₀` on each half.
The doc block at `### Sub-cover adjustment: S.erase f₀ on Laurent halves`
above flagged three properties to transfer to each half:

1. **Covering** — discharged by `plusLaurentCovering_hCov_of_refines_cover`
   / `minusLaurentCovering_hCov_of_refines_cover`.
2. **Containment** — discharged by `refines_contain_plusHalf_of_refines_cover`
   / `minusLaurentCovering_pointwise_contain_of_refines_cover`.
3. **Span-top** — "`Ideal.span (S.erase f₀) = ⊤` in the Laurent-half's
   ring of definition." This is the remaining piece.

**Status**: (3) does not reduce to a clean transfer from
`refines_span_top S` alone (or even together with `refines_cover C S`).
The block below lands the **strongest clean helpers** for the partial
transfers and documents the precise mathematical dependency.

### What reduces cleanly (landed below)

**(A)** From `refines_span_top S` (i.e., `Ideal.span S = ⊤` in `A`),
via Prop 7.14 (`spanTop_iff_noCommonZero_spa`), we get that **`S`
itself** has no common zero on any rational open — in particular on
each Laurent half. Theorems:
- `noCommonZero_plusHalf_of_refines_span_top`
- `noCommonZero_minusHalf_of_refines_span_top`

**(B)** On the minus half, the split element `f₀` has `v(f₀) ≥ v(C.base.s)
> 0`, so `f₀` is always nonzero on the minus half. Theorem:
- `f₀_notZero_on_minusHalf`

### What does NOT reduce cleanly (left as a documented gap)

**(C)** "`Ideal.span (S.erase f₀) = ⊤` in A" — **FALSE in general**
even when `Ideal.span S = ⊤`. Consider `S = {f₀, 1 - f₀}` with `f₀`
not a unit; `Ideal.span S = ⊤` via `1 = f₀ + (1 - f₀)`, but neither
singleton spans the unit ideal.

**(D)** "`Ideal.span (S.erase f₀) = ⊤` in the Laurent-half's ring of
definition / presheaf value" — holds mathematically but REQUIRES the
**LOCALISED Prop 7.14** (adic Nullstellensatz) on the Laurent-half
rational open, which is NOT yet in the project. The current
`spanTop_iff_noCommonZero_spa` quantifies over all of `Spa A A⁺`; a
version quantifying over `rationalOpen (insert f₀ C.base.T) C.base.s`
and concluding span-top in the presheaf-value ring is the missing
ingredient.

**Exact Lean boundary of the missing lemma** (still missing the B-level
equivalence; the A-level partial reduction is landed below):
```
-- Localised Prop 7.14 on plus half (for full Laurent-half span-top in B):
theorem spanTop_iff_noCommonZero_plusHalf
    (P : PairOfDefinition A) ... (C : RationalCoveringData A) (f₀ : A)
    (T : Finset A) :
    Ideal.span ((T : Set A) : Set (presheafValue (laurentPlusDatum C.base f₀))) = ⊤
      ↔ ∀ v ∈ rationalOpen (insert f₀ C.base.T) C.base.s,
          ∃ t ∈ T, ¬ v.vle t 0
```

Equivalent form asserting span-top **in A** is not possible in general:
the `S.erase f₀` case shows even `refines_span_top S` alone can fail
to give `refines_span_top (S.erase f₀)` in A. The transfer must go
either (i) to a Laurent-localised ring (requires the localised
Nullstellensatz above), or (ii) take a concrete `v(f₀) ≠ 0` coverage
hypothesis that splits Spa by `v(f₀)`. Approach (ii) is landed below
as `refines_span_top_erase_of_noCommonZero_nonzero_f₀` and removes
the localised-Prop-7.14 hypothesis entirely from the span-top erase
transfer, replacing it with a cleaner concrete witness.

### Dependency chain

For the full `step_witness` discharge inside an outer induction, the
caller needs to pass the localised-Prop-7.14 output directly as an
hypothesis until the localised version is formalised. The clean
helpers below discharge HALF of the obligation (the "S itself, not
`S.erase f₀`" side). -/

/-- **Plus-half no-common-zero from `refines_span_top`** (Prop 7.14
via `spanTop_iff_noCommonZero_spa`). If the full cover `S` spans the
unit ideal in `A`, then on the plus half at `f₀`, some `f ∈ S` has
non-zero valuation. This is the "S itself, not `S.erase f₀`" direction;
the `S.erase f₀` transfer requires the localised Prop 7.14 (see doc
block above). -/
theorem RationalCoveringData.noCommonZero_plusHalf_of_refines_span_top
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    [IsHuberRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺ : Subring A)] [DecidableEq A] (C : RationalCoveringData A) (f₀ : A) (S : Finset A)
    (hspan : Ideal.span ((S : Set A)) = ⊤) :
    ∀ v ∈ rationalOpen (insert f₀ C.base.T) C.base.s,
      ∃ f ∈ S, ¬ v.vle f 0 := by
  intro v hv
  have hv_plusDatum : v ∈ rationalOpen (laurentPlusDatum C.base f₀).T
                                        (laurentPlusDatum C.base f₀).s :=
    (C.rationalOpen_plusDatum_eq_insert f₀).symm ▸ hv
  have hv_spa : v ∈ Spa A A⁺ :=
    rationalOpen_subset_spa (laurentPlus_subset C.base f₀ hv_plusDatum)
  exact ((spanTop_iff_noCommonZero_spa P S).mp hspan) v hv_spa

/-- **Minus-half no-common-zero from `refines_span_top`**. Mirror of
the plus-half version via `laurentMinus_subset`. -/
theorem RationalCoveringData.noCommonZero_minusHalf_of_refines_span_top
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    [IsHuberRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺ : Subring A)] [DecidableEq A] (C : RationalCoveringData A) (f₀ : A) (S : Finset A)
    (hspan : Ideal.span ((S : Set A)) = ⊤) :
    ∀ v ∈ rationalOpen (laurentMinusDatum C.base f₀).T
                       (laurentMinusDatum C.base f₀).s,
      ∃ f ∈ S, ¬ v.vle f 0 := by
  intro v hv
  have hv_spa : v ∈ Spa A A⁺ :=
    rationalOpen_subset_spa (laurentMinus_subset C.base f₀ hv)
  exact ((spanTop_iff_noCommonZero_spa P S).mp hspan) v hv_spa

/-- **`f₀` has non-zero valuation on the minus half**. On the Laurent-
minus half at `f₀`, the valuation of `f₀` dominates `C.base.s` (which
is always non-zero on the rational open), so `f₀` itself is never in
the support of any valuation in the minus half.

This captures one side of the "minus half is where f₀ dominates" fact
and means that in any no-common-zero argument on the minus half, `f₀`
trivially witnesses. It does NOT however give no-common-zero for
`S.erase f₀` — the fundamental obstacle to a general Lean-level
`S.erase f₀` span-top transfer. -/
theorem RationalCoveringData.f₀_notZero_on_minusHalf
    [DecidableEq A] (C : RationalCoveringData A) (f₀ : A) :
    ∀ v ∈ rationalOpen (laurentMinusDatum C.base f₀).T
                       (laurentMinusDatum C.base f₀).s,
      ¬ v.vle f₀ 0 := by
  intro v hv
  -- On the minus half, `v.vle (C.base.s * f₀) 0` fails (the rational-open
  -- `.s` component witness). Since `v.vle (C.base.s * f₀) 0 ↔ v.vle C.base.s 0
  -- ∨ v.vle f₀ 0` via multiplicativity, and the minus half has
  -- `.s = C.base.s * f₀`, the corresponding `hvs` witness rules out both.
  have hvs : ¬ v.vle (laurentMinusDatum C.base f₀).s 0 := hv.2.2
  -- `.s = C.base.s * f₀`: reduce to `¬ v.vle (C.base.s * f₀) 0`.
  change ¬ v.vle (C.base.s * f₀) 0 at hvs
  exact not_vle_zero_right_of_mul hvs

/-- **No-common-zero of `S.erase f₀` on the `f₀`-zero locus** — the
CLEAN half of the span-top erase transfer, derivable directly from
Prop 7.14 applied to `S`. Given `refines_span_top S` and `f₀ ∈ S`,
for every `v ∈ Spa A A⁺` with `v(f₀) = 0` (i.e., `v.vle f₀ 0`), some
`g ∈ S.erase f₀` has `v(g) ≠ 0`. Reason: Prop 7.14 gives `∃ f ∈ S,
v(f) ≠ 0`; the witness cannot be `f₀` since `v(f₀) = 0`. -/
theorem RationalCoveringData.noCommonZero_erase_of_f₀_zero
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    [IsHuberRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺ : Subring A)] [DecidableEq A] (f₀ : A) (S : Finset A)
    (hspan : Ideal.span ((S : Set A)) = ⊤)
    (_h_f₀_mem : f₀ ∈ S) :
    ∀ v ∈ Spa A A⁺, v.vle f₀ 0 → ∃ g ∈ S.erase f₀, ¬ v.vle g 0 := by
  intro v hv_spa hv_f₀
  obtain ⟨f, hf_mem, hvf⟩ :=
    (spanTop_iff_noCommonZero_spa P S).mp hspan v hv_spa
  refine ⟨f, Finset.mem_erase.mpr ⟨?_, hf_mem⟩, hvf⟩
  intro h_eq
  exact hvf (h_eq ▸ hv_f₀)

/-- **`refines_span_top` for `S.erase f₀` from a `v(f₀) ≠ 0` covering
hypothesis** — the cleanest concrete reduction available from the
existing (non-localised) Prop 7.14.

Given `refines_span_top S`, `f₀ ∈ S`, and — for every `v ∈ Spa A A⁺`
with `v(f₀) ≠ 0` — a witness `g ∈ S.erase f₀` with `v(g) ≠ 0`, then
`Ideal.span (S.erase f₀) = ⊤` in `A`.

**Why this works**: splitting on `v(f₀)`:
* `v(f₀) = 0`: `noCommonZero_erase_of_f₀_zero` supplies a witness
  automatically (derived from Prop 7.14 on `S`).
* `v(f₀) ≠ 0`: the given hypothesis supplies a witness.

Combined, `S.erase f₀` has no common zero on all of `Spa A A⁺`, and
the reverse direction of `spanTop_iff_noCommonZero_spa` gives
span-top in `A`.

**Usage**: the remaining `v(f₀) ≠ 0` coverage hypothesis is exactly
the piece a caller must supply — typically from a minus-half coverage
witness or from ancillary combinatorial data about `S`. The Laurent-
minus half's natural property `f₀_notZero_on_minusHalf` covers the
minus-half part of this region automatically; the portion of Spa
outside the minus half with `v(f₀) ≠ 0` must be handled separately. -/
theorem RationalCoveringData.refines_span_top_erase_of_noCommonZero_nonzero_f₀
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    [IsHuberRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺ : Subring A)] [DecidableEq A] (f₀ : A) (S : Finset A)
    (hspan : Ideal.span ((S : Set A)) = ⊤)
    (h_f₀_mem : f₀ ∈ S)
    (h_cover_nonzero_f₀ :
      ∀ v ∈ Spa A A⁺, ¬ v.vle f₀ 0 → ∃ g ∈ S.erase f₀, ¬ v.vle g 0) :
    Ideal.span ((S.erase f₀ : Finset A) : Set A) = ⊤ := by
  rw [spanTop_iff_noCommonZero_spa P]
  intro v hv_spa
  by_cases h_f₀_zero : v.vle f₀ 0
  · exact RationalCoveringData.noCommonZero_erase_of_f₀_zero P hAplus_le_A₀
      f₀ S hspan h_f₀_mem v hv_spa h_f₀_zero
  · exact h_cover_nonzero_f₀ v hv_spa h_f₀_zero

/-- **Legacy shape** kept for callers of the earlier localised-
Nullstellensatz API. Given a localised-Nullstellensatz hypothesis
(directly provides `Ideal.span (S.erase f₀) = ⊤` from a plus-half
no-common-zero witness) and the witness, produces the span-top.

Prefer `refines_span_top_erase_of_noCommonZero_nonzero_f₀` for new
code: that version takes the narrower, cleaner "cover the `v(f₀) ≠ 0`
locus" hypothesis and derives span-top directly via Prop 7.14, with
no separate localised-Nullstellensatz input needed. -/
theorem RationalCoveringData.refines_span_top_erase_of_localised_nullstellensatz
    [DecidableEq A] (C : RationalCoveringData A) (f₀ : A) (S : Finset A)
    (hspan : Ideal.span ((S : Set A)) = ⊤)
    (h_f₀_mem : f₀ ∈ S)
    (h_localised_null :
      -- Localised Prop 7.14 on the plus half at `f₀`: `T` has no common
      -- zero on plus half ⟺ `Ideal.span T = ⊤` in the appropriate ring.
      -- We consume only the forward direction we need.
      (∀ v ∈ rationalOpen (insert f₀ C.base.T) C.base.s,
        ∃ g ∈ S.erase f₀, ¬ v.vle g 0) →
      Ideal.span ((S.erase f₀ : Finset A) : Set A) = ⊤)
    (h_no_common_zero :
      ∀ v ∈ rationalOpen (insert f₀ C.base.T) C.base.s,
        ∃ g ∈ S.erase f₀, ¬ v.vle g 0) :
    Ideal.span ((S.erase f₀ : Finset A) : Set A) = ⊤ := by
  -- Direct forward via `h_localised_null`; `hspan` and `h_f₀_mem` are
  -- retained as context for callers who wish to refine the hypothesis.
  let _ := hspan
  let _ := h_f₀_mem
  exact h_localised_null h_no_common_zero

/-! ### V-cover refinement across Laurent halves

For the induction-step's `hrefine` hypothesis (every V-piece refines
plus OR minus half) to hold by construction, we refine the V-cover by
intersecting each V-piece with each Laurent half. The result: `2|S|`
refined pieces, each contained in exactly one Laurent half.

Concretely, for each `f ∈ S`:
* **Plus-refined-at-`f`**: `laurentPlusDatum (C.plusDatum f) f₀` —
  the iterated Laurent plus (V-piece at `f`, then plus at `f₀`).
* **Minus-refined-at-`f`**: `laurentMinusDatum (C.plusDatum f) f₀` —
  the Laurent minus of V-piece at `f` at `f₀`.

These refined pieces are used together with
`gluing_of_finer_rational` (`RationalRefinement.lean`) to transfer
gluing from the refined V-cover to the outer rational covering `C`,
bypassing the per-V-piece dichotomy obstacle. -/

/-- **Plus-refined piece lies in the plus half**. The iterated Laurent
plus `laurentPlusDatum (C.plusDatum f) f₀` has more `T` constraints
than the plus half `laurentPlusDatum C.base f₀` (adds `f`), so its
rational open is contained in the plus half. -/
theorem RationalCoveringData.refinedPlusPiece_in_plusHalf
    [DecidableEq A] (C : RationalCoveringData A) (f₀ f : A) :
    rationalOpen (laurentPlusDatum (C.plusDatum f) f₀).T
                 (laurentPlusDatum (C.plusDatum f) f₀).s ⊆
      rationalOpen (laurentPlusDatum C.base f₀).T
                   (laurentPlusDatum C.base f₀).s := by
  intro v ⟨hvspa, hvT, hvs⟩
  refine ⟨hvspa, ?_, hvs⟩
  intro t ht
  -- `ht : t ∈ insert f₀ C.base.T`; use `hvT` on the larger
  -- `insert f₀ (insert f C.base.T)` containing `t`.
  apply hvT
  simp only [laurentPlusDatum, RationalCoveringData.plusDatum, Finset.mem_insert] at ht ⊢
  rcases ht with rfl | ht'
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ht')

/-- **Minus-refined piece lies in the minus half**. The iterated Laurent
minus `laurentMinusDatum (C.plusDatum f) f₀` has more `T` constraints
than the minus half `laurentMinusDatum C.base f₀` (first factor of the
product includes `f`), so its rational open is contained. -/
theorem RationalCoveringData.refinedMinusPiece_in_minusHalf
    [DecidableEq A] (C : RationalCoveringData A) (f₀ f : A) :
    rationalOpen (laurentMinusDatum (C.plusDatum f) f₀).T
                 (laurentMinusDatum (C.plusDatum f) f₀).s ⊆
      rationalOpen (laurentMinusDatum C.base f₀).T
                   (laurentMinusDatum C.base f₀).s := by
  -- Align instance with `laurentMinusDatum`'s internal Classical.
  letI : DecidableEq A := Classical.decEq _
  intro v ⟨hvspa, hvT, hvs⟩
  refine ⟨hvspa, fun t ht => ?_, hvs⟩
  apply hvT
  -- Destructure `ht` via the image/product structure of
  -- `(laurentMinusDatum C.base f₀).T`, re-assemble under
  -- `(laurentMinusDatum (C.plusDatum f) f₀).T`.
  obtain ⟨⟨t₁, t₂⟩, hmem, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨ht₁, ht₂⟩ := Finset.mem_product.mp hmem
  refine Finset.mem_image.mpr ⟨⟨t₁, t₂⟩, Finset.mem_product.mpr ⟨?_, ht₂⟩, rfl⟩
  simp only [RationalCoveringData.plusDatum, laurentPlusDatum, Finset.mem_insert] at ht₁ ⊢
  rcases ht₁ with rfl | ht₁'
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ht₁')

/-- **Plus-refined and minus-refined pieces cover the V-piece**. The
union of the two refined pieces at `f` equals the outer V-piece at `f`
(as sets of valuations), by Laurent-cover coverage applied at `f₀` on
the V-piece base. -/
theorem RationalCoveringData.refinedPieces_cover_Vpiece
    [DecidableEq A] (C : RationalCoveringData A) (f₀ f : A) :
    rationalOpen (C.plusDatum f).T (C.plusDatum f).s ⊆
      rationalOpen (laurentPlusDatum (C.plusDatum f) f₀).T
                   (laurentPlusDatum (C.plusDatum f) f₀).s ∪
      rationalOpen (laurentMinusDatum (C.plusDatum f) f₀).T
                   (laurentMinusDatum (C.plusDatum f) f₀).s :=
  fun v hv => laurentCover_covers (C.plusDatum f) f₀ v hv

/-- **The refined V-cover across Laurent halves**. For each `f ∈ S`,
produces two pieces: the plus-refined and minus-refined V-piece at `f₀`.
The resulting `Finset` has at most `2|S|` elements (deduplicated by
`Finset.image`). -/
noncomputable def RationalCoveringData.refinedVCovers
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A) :
    Finset (RationalLocData A) :=
  letI : DecidableEq (RationalLocData A) := Classical.decEq _
  S.image (fun f => laurentPlusDatum (C.plusDatum f) f₀) ∪
    S.image (fun f => laurentMinusDatum (C.plusDatum f) f₀)

/-- Membership in the refined V-cover: each refined piece is either the
plus-refined or minus-refined iterate at some `f ∈ S`. -/
theorem RationalCoveringData.mem_refinedVCovers
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    {D : RationalLocData A} :
    D ∈ C.refinedVCovers S f₀ ↔
      (∃ f ∈ S, laurentPlusDatum (C.plusDatum f) f₀ = D) ∨
      (∃ f ∈ S, laurentMinusDatum (C.plusDatum f) f₀ = D) := by
  letI : DecidableEq (RationalLocData A) := Classical.decEq _
  unfold RationalCoveringData.refinedVCovers
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]

/-- Refined pieces each lie in the `C.base` rational open. Follows from
`laurentPlus_subset`/`laurentMinus_subset` composed with
`plusDatum_subset_base`. -/
theorem RationalCoveringData.refinedVCovers_subset_base
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (D : RationalLocData A) (hD : D ∈ C.refinedVCovers S f₀) :
    rationalOpen D.T D.s ⊆ rationalOpen C.base.T C.base.s := by
  rcases (C.mem_refinedVCovers S f₀).mp hD with ⟨f, _hf, rfl⟩ | ⟨f, _hf, rfl⟩
  · -- Plus-refined: ⊆ (C.plusDatum f) ⊆ C.base.
    exact (laurentPlus_subset (C.plusDatum f) f₀).trans (C.plusDatum_subset_base f)
  · -- Minus-refined: ⊆ (C.plusDatum f) ⊆ C.base.
    exact (laurentMinus_subset (C.plusDatum f) f₀).trans (C.plusDatum_subset_base f)

/-- **Refined V-cover covers `C.base`**. Given `refines_cover C S`,
every valuation in `C.base`'s rational open lies in some refined
piece: first find `f ∈ S` with `v ∈ plus-piece-at-f` (outer
refines_cover), then apply `laurentCover_covers` to split into plus-
or minus-refined-at-`f`. -/
theorem RationalCoveringData.refinedVCovers_covers
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hS_cover : refines_cover C S) :
    ∀ v ∈ rationalOpen C.base.T C.base.s,
      ∃ D ∈ C.refinedVCovers S f₀, v ∈ rationalOpen D.T D.s := by
  intro v hv
  -- Step 1: find `f ∈ S` with `v ∈ plus-piece-at-f`.
  obtain ⟨f, hf, hvf⟩ := hS_cover v hv
  -- Step 2: `hvf : v ∈ rationalOpen (insert f C.base.T) C.base.s`;
  -- re-express as `v ∈ rationalOpen (C.plusDatum f).T (C.plusDatum f).s`.
  have hvf' : v ∈ rationalOpen (C.plusDatum f).T (C.plusDatum f).s :=
    (C.rationalOpen_plusDatum_eq_insert f).symm ▸ hvf
  -- Step 3: `laurentCover_covers` splits into plus-refined or minus-refined at f₀.
  rcases laurentCover_covers (C.plusDatum f) f₀ v hvf' with hv_plus | hv_minus
  · exact ⟨laurentPlusDatum (C.plusDatum f) f₀,
      (C.mem_refinedVCovers S f₀).mpr (Or.inl ⟨f, hf, rfl⟩), hv_plus⟩
  · exact ⟨laurentMinusDatum (C.plusDatum f) f₀,
      (C.mem_refinedVCovers S f₀).mpr (Or.inr ⟨f, hf, rfl⟩), hv_minus⟩

/-- **Plus/minus dichotomy for refined V-cover**. Every refined piece
is contained entirely in plus-half OR minus-half at `f₀`, by
construction — the key property enabling the `hrefine` discharge in
`hV_glue_step_from_laurent_halves`. -/
theorem RationalCoveringData.refinedVCovers_plusMinus_dichotomy
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (D : RationalLocData A) (hD : D ∈ C.refinedVCovers S f₀) :
    rationalOpen D.T D.s ⊆
      rationalOpen (laurentPlusDatum C.base f₀).T
                   (laurentPlusDatum C.base f₀).s ∨
    rationalOpen D.T D.s ⊆
      rationalOpen (laurentMinusDatum C.base f₀).T
                   (laurentMinusDatum C.base f₀).s := by
  rcases (C.mem_refinedVCovers S f₀).mp hD with ⟨f, _hf, rfl⟩ | ⟨f, _hf, rfl⟩
  · exact Or.inl (C.refinedPlusPiece_in_plusHalf f₀ f)
  · exact Or.inr (C.refinedMinusPiece_in_minusHalf f₀ f)

/-- **Refinement map `τ_refined` together with its containment property**.
Maps each refined piece `D` to the outer V-piece `C.plusDatum f` at the
same `f` (extracted via `Classical.choose` from the existential
membership witness), together with a proof that `D`'s rational open is
contained in the τ-image's rational open (via `laurentPlus_subset` /
`laurentMinus_subset`).

Packaged as a `Subtype` to keep the containment proof alongside the
τ-image, since both depend on the Classical-choice-picked `f`. -/
noncomputable def RationalCoveringData.refinedVCoversTauPair
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (D : { D // D ∈ C.refinedVCovers S f₀ }) :
    { Ep : { E // E ∈ C.standardCoverVCovers S } //
      rationalOpen D.1.T D.1.s ⊆ rationalOpen Ep.1.T Ep.1.s } :=
  -- Extract `∃ f ∈ S, D = plus-refined or minus-refined` via a single
  -- `Classical.choose` over the `Or`-flattened existential.
  let h_exists : ∃ f, f ∈ S ∧
      (laurentPlusDatum (C.plusDatum f) f₀ = D.1 ∨
       laurentMinusDatum (C.plusDatum f) f₀ = D.1) :=
    match (C.mem_refinedVCovers S f₀).mp D.2 with
    | Or.inl ⟨f, hf, hf_eq⟩ => ⟨f, hf, Or.inl hf_eq⟩
    | Or.inr ⟨f, hf, hf_eq⟩ => ⟨f, hf, Or.inr hf_eq⟩
  let f := Classical.choose h_exists
  let hf_spec := Classical.choose_spec h_exists
  -- τ-image: `C.plusDatum f`.
  let E : { E // E ∈ C.standardCoverVCovers S } :=
    ⟨C.plusDatum f, (C.mem_standardCoverVCovers S).mpr ⟨f, hf_spec.1, rfl⟩⟩
  ⟨E, by
    -- Subset proof: D is either plus-refined or minus-refined at f.
    rcases hf_spec.2 with h_plus | h_minus
    · -- D.1 = laurentPlusDatum (C.plusDatum f) f₀.
      intro v hv
      have hv' : v ∈ rationalOpen (laurentPlusDatum (C.plusDatum f) f₀).T
                                  (laurentPlusDatum (C.plusDatum f) f₀).s := h_plus ▸ hv
      exact laurentPlus_subset (C.plusDatum f) f₀ hv'
    · -- D.1 = laurentMinusDatum (C.plusDatum f) f₀.
      intro v hv
      have hv' : v ∈ rationalOpen (laurentMinusDatum (C.plusDatum f) f₀).T
                                  (laurentMinusDatum (C.plusDatum f) f₀).s := h_minus ▸ hv
      exact laurentMinus_subset (C.plusDatum f) f₀ hv'⟩

/-- τ map projection from `refinedVCoversTauPair`. -/
noncomputable def RationalCoveringData.refinedVCoversTau
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (D : { D // D ∈ C.refinedVCovers S f₀ }) :
    { E // E ∈ C.standardCoverVCovers S } :=
  (C.refinedVCoversTauPair S f₀ D).1

/-- **`τ_refined` is containment-preserving**. Each refined piece's
rational open is contained in its `τ`-image's rational open. -/
theorem RationalCoveringData.refinedVCoversTau_subset
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (D : { D // D ∈ C.refinedVCovers S f₀ }) :
    rationalOpen D.1.T D.1.s ⊆
      rationalOpen (C.refinedVCoversTau S f₀ D).1.T
                   (C.refinedVCoversTau S f₀ D).1.s :=
  (C.refinedVCoversTauPair S f₀ D).2

/-! ### S-GEOM-IND: full `hV_glue` induction for standard covers

The theorem `standardCover_hV_glue_induction` assembles the full
Wedhorn 8.34 / Hübner 3.8 induction on standard-cover size. The
inductive structure:

* **Base case** (`|S| = 1`): `S = {f}`. Delegate to
  `hV_glue_singleton_of_Aplus` (T012's singleton base case).
* **Step case** (`|S| = n + 2`): pick any `f₀ ∈ S`, Laurent-split at
  `f₀`, and use `hV_glue_step_from_laurent_halves` (T014) to recombine
  plus-half and minus-half sections into a global section on `C.base`.

Per the ticket directive, `laurentCover_gluing_presheaf` is kept as an
*explicit hypothesis* until `T-OVERLAP-COMPAT`
(`LaurentRefinement.lean:3173`, the Laurent-overlap-compatibility
bridge) is discharged. In addition, because the **sub-cover adjustment
theorems** (transferring `refines_cover C S` to the Laurent halves over
`S.erase f₀`) are not yet in place, the step-case ingredients
—`plus_section`, `minus_section`, `hrefine`, `hoverlap_of_compat`— are
also taken as explicit hypotheses parameterised over the chosen split
point `f₀ ∈ S`. The induction's **recursion structure** is still
captured: the plus/minus section builders in the hypotheses are exactly
what an inner recursive `hV_glue` on `(laurentPlusDatum C.base f₀,
S.erase f₀)` would produce, and the cardinality-decrease
`|S.erase f₀| < |S|` (from `Finset.card_erase_of_mem_decreases`) is the
well-founded termination witness for that outer recursion.

Post-T-OVERLAP-COMPAT (plus the sub-cover transfer completion), these
hypotheses become discharge-able internally and this theorem becomes
unconditional. -/

/-- **Full `hV_glue` induction for standard-cover V-covers** (S-GEOM-IND).
Given a rational covering `C` refined by a non-empty standard cover `S`
with `f ∈ A⁺` for each `f ∈ S` and `1 ∈ C.base.T`, any compatible family
on `C.standardCoverVCovers S` extends to a global section on `C.base`.

The theorem dispatches on `|S|`:
* `|S| = 1`: via `hV_glue_singleton_of_Aplus`.
* `|S| ≥ 2`: via `hV_glue_step_from_laurent_halves` at a chosen
  `f₀ ∈ S`, with the step's hypotheses (plus/minus-section builders,
  refinement split, Laurent gluing, overlap-from-compat) supplied by
  the `step_witness` argument — which in a later unconditional pass
  will be discharged by a recursive `hV_glue` on `(laurent-half,
  S.erase f₀)` combined with the sub-cover transfer and
  `laurentCover_gluing_presheaf`. -/
theorem RationalCoveringData.standardCover_hV_glue_induction
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A)
    (hSnonempty : S.Nonempty)
    (hAplus : ∀ f ∈ S, f ∈ A⁺)
    (h1T : (1 : A) ∈ C.base.T)
    -- Step-witness hypothesis (vacuous for `|S| = 1`; captures the
    -- Laurent-split step machinery for `|S| ≥ 2`). When T-OVERLAP-COMPAT
    -- lands and the sub-cover transfer is completed, this is discharged
    -- by an internal recursive call + `laurentCover_gluing_presheaf`.
    (step_witness : 2 ≤ S.card →
      ∃ (f₀ : A) (_ : f₀ ∈ S)
        (plus_section : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
            presheafValue D.1),
          (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
            (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
            (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
            restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
          { u_plus : presheafValue (laurentPlusDatum C.base f₀) //
            ∀ (D : { D // D ∈ C.standardCoverVCovers S })
              (hD_plus : rationalOpen D.1.T D.1.s ⊆
                rationalOpen (laurentPlusDatum C.base f₀).T
                             (laurentPlusDatum C.base f₀).s),
              restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D })
        (minus_section : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
            presheafValue D.1),
          (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
            (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
            (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
            restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
          { u_minus : presheafValue (laurentMinusDatum C.base f₀) //
            ∀ (D : { D // D ∈ C.standardCoverVCovers S })
              (hD_minus : rationalOpen D.1.T D.1.s ⊆
                rationalOpen (laurentMinusDatum C.base f₀).T
                             (laurentMinusDatum C.base f₀).s),
              restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D })
        (_hrefine : ∀ D : { D // D ∈ C.standardCoverVCovers S },
          (rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s) ∨
          (rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s))
        (_hLaurentGlue : ∀ (u_plus : presheafValue (laurentPlusDatum C.base f₀))
          (u_minus : presheafValue (laurentMinusDatum C.base f₀))
          (_hoverlap : ∀ (D₃ : RationalLocData A)
            (h₃p : rationalOpen D₃.T D₃.s ⊆
              rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
            (h₃m : rationalOpen D₃.T D₃.s ⊆
              rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
            restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p u_plus =
              restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m u_minus),
          ∃ x : presheafValue C.base,
            restrictionMap C.base (laurentPlusDatum C.base f₀)
              (laurentPlus_subset C.base f₀) x = u_plus ∧
            restrictionMap C.base (laurentMinusDatum C.base f₀)
              (laurentMinus_subset C.base f₀) x = u_minus),
        ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
            presheafValue D.1)
          (hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
            (D₃ : RationalLocData A)
            (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
            (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
            restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)),
          ∀ (D₃ : RationalLocData A)
            (h₃p : rationalOpen D₃.T D₃.s ⊆
              rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
            (h₃m : rationalOpen D₃.T D₃.s ⊆
              rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
            restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p
                (plus_section fV hV_compat).1 =
              restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m
                (minus_section fV hV_compat).1) :
    ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base,
        ∀ D : { D // D ∈ C.standardCoverVCovers S },
          restrictionMap C.base D.1
            (C.standardCoverVCovers_subset_base S D.1 D.2) x = fV D := by
  intro fV compat
  by_cases hcard : S.card = 1
  · -- Base case |S| = 1: singleton dispatch via `hV_glue_singleton_of_Aplus`.
    obtain ⟨f, rfl⟩ := Finset.card_eq_one.mp hcard
    exact C.hV_glue_singleton_of_Aplus f (hAplus f (Finset.mem_singleton_self f)) h1T
      fV compat
  · -- Step case |S| ≥ 2: extract the step witness and compose via
    -- `hV_glue_step_from_laurent_halves`.
    have h2 : 2 ≤ S.card := by
      have hpos : 0 < S.card := Finset.card_pos.mpr hSnonempty
      omega
    obtain ⟨f₀, _hf₀, plus_section, minus_section, hrefine, hLaurentGlue, hOvlp⟩ :=
      step_witness h2
    exact C.hV_glue_step_from_laurent_halves f₀ S
      plus_section minus_section hrefine hLaurentGlue hOvlp fV compat

/-! ### h1T reformulation: semantic `vle` hypothesis

The `h1T : 1 ∈ C.base.T` hypothesis of `standardCover_hV_glue_induction`
is used ONLY in the singleton base case, to derive the semantic vle
condition `∀ v ∈ rationalOpen C.base.T C.base.s, v.vle f C.base.s`
for `f ∈ S` (via `vle_s_of_mem_Aplus_of_one_mem_T`, combining `h1T`
with `f ∈ A⁺`).

**Structural problem with `h1T` under recursion**: for the outer
recursive induction at `|S| ≥ 2` to invoke the IH on `S.erase f₀` on
the Laurent-minus half, the inner `h1T` hypothesis
`1 ∈ (laurentMinusDatum C.base f₀).T` does NOT follow from outer
`1 ∈ C.base.T`: the minus datum's `.T` is
`(insert C.base.s C.base.T) * {C.base.s, f₀}` (Pointwise product),
and `1` being there requires `1 = 1 * 1` with `1 ∈ C.base.T` (ok) AND
`1 ∈ {C.base.s, f₀}` (needs `1 = C.base.s` or `1 = f₀` — not general).

**Reformulation**: replace `h1T` by the semantic hypothesis
`hBase_vle : ∀ f ∈ S, ∀ v ∈ rationalOpen C.base.T C.base.s, v.vle f C.base.s`
that `h1T + hAplus` imply. The new variant
`standardCover_hV_glue_induction_via_vle` accepts `hBase_vle` directly;
the old `standardCover_hV_glue_induction` is recovered as a thin
wrapper supplying `hBase_vle` from `h1T + hAplus`.

**Benefit for Laurent recursion**: `hBase_vle` transfers cleanly to
the plus half (plus-half ⊆ base, so outer `hBase_vle` restricts). The
minus-half `hBase_vle_minus` is strictly a stronger claim (different
denominator) and remains an explicit hypothesis for outer callers;
this matches the reviewer's desired shape. -/

/-- **Semantic `h1T` variant of `standardCover_hV_glue_induction`**.
Uses `hBase_vle` (the semantic vle condition) in place of
`h1T : 1 ∈ C.base.T`. Equivalent to the original when `hBase_vle` is
supplied via `vle_s_of_mem_Aplus_of_one_mem_T`; strictly more flexible
when the caller has a direct vle witness (e.g., from the recursive
setup where the plus-half's vle follows automatically from outer
`hBase_vle` + `laurentPlus_subset`). -/
theorem RationalCoveringData.standardCover_hV_glue_induction_via_vle
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A)
    (hSnonempty : S.Nonempty)
    (hAplus : ∀ f ∈ S, f ∈ A⁺)
    (hBase_vle :
      ∀ f ∈ S, ∀ v ∈ rationalOpen C.base.T C.base.s, v.vle f C.base.s)
    (step_witness : 2 ≤ S.card →
      ∃ (f₀ : A) (_ : f₀ ∈ S)
        (plus_section : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
            presheafValue D.1),
          (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
            (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
            (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
            restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
          { u_plus : presheafValue (laurentPlusDatum C.base f₀) //
            ∀ (D : { D // D ∈ C.standardCoverVCovers S })
              (hD_plus : rationalOpen D.1.T D.1.s ⊆
                rationalOpen (laurentPlusDatum C.base f₀).T
                             (laurentPlusDatum C.base f₀).s),
              restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D })
        (minus_section : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
            presheafValue D.1),
          (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
            (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
            (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
            restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
          { u_minus : presheafValue (laurentMinusDatum C.base f₀) //
            ∀ (D : { D // D ∈ C.standardCoverVCovers S })
              (hD_minus : rationalOpen D.1.T D.1.s ⊆
                rationalOpen (laurentMinusDatum C.base f₀).T
                             (laurentMinusDatum C.base f₀).s),
              restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D })
        (_hrefine : ∀ D : { D // D ∈ C.standardCoverVCovers S },
          (rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s) ∨
          (rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s))
        (_hLaurentGlue : ∀ (u_plus : presheafValue (laurentPlusDatum C.base f₀))
          (u_minus : presheafValue (laurentMinusDatum C.base f₀))
          (_hoverlap : ∀ (D₃ : RationalLocData A)
            (h₃p : rationalOpen D₃.T D₃.s ⊆
              rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
            (h₃m : rationalOpen D₃.T D₃.s ⊆
              rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
            restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p u_plus =
              restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m u_minus),
          ∃ x : presheafValue C.base,
            restrictionMap C.base (laurentPlusDatum C.base f₀)
              (laurentPlus_subset C.base f₀) x = u_plus ∧
            restrictionMap C.base (laurentMinusDatum C.base f₀)
              (laurentMinus_subset C.base f₀) x = u_minus),
        ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
            presheafValue D.1)
          (hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
            (D₃ : RationalLocData A)
            (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
            (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
            restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)),
          ∀ (D₃ : RationalLocData A)
            (h₃p : rationalOpen D₃.T D₃.s ⊆
              rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
            (h₃m : rationalOpen D₃.T D₃.s ⊆
              rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
            restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p
                (plus_section fV hV_compat).1 =
              restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m
                (minus_section fV hV_compat).1) :
    ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base,
        ∀ D : { D // D ∈ C.standardCoverVCovers S },
          restrictionMap C.base D.1
            (C.standardCoverVCovers_subset_base S D.1 D.2) x = fV D := by
  intro fV compat
  by_cases hcard : S.card = 1
  · -- Base case |S| = 1: delegate to `standardCover_gluing_singleton_of_vle`.
    obtain ⟨f, rfl⟩ := Finset.card_eq_one.mp hcard
    exact C.standardCover_gluing_singleton_of_vle f
      (hBase_vle f (Finset.mem_singleton_self f)) fV compat
  · -- Step case |S| ≥ 2: identical to the original — extract step_witness and
    -- compose via `hV_glue_step_from_laurent_halves`.
    have h2 : 2 ≤ S.card := by
      have hpos : 0 < S.card := Finset.card_pos.mpr hSnonempty
      omega
    obtain ⟨f₀, _hf₀, plus_section, minus_section, hrefine, hLaurentGlue, hOvlp⟩ :=
      step_witness h2
    exact C.hV_glue_step_from_laurent_halves f₀ S
      plus_section minus_section hrefine hLaurentGlue hOvlp fV compat

/-- **Plus-half `hBase_vle` transfer**. Given outer `hBase_vle` on
`rationalOpen C.base.T C.base.s`, restricted to `S.erase f₀`, the
corresponding hypothesis on the plus-half
`rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s`
holds automatically: the plus half is contained in the outer base
(via `laurentPlus_subset`), the plus-half denominator equals the outer
denominator (`.s = C.base.s`), so the outer vle witness restricts. -/
theorem RationalCoveringData.hBase_vle_plusHalf_of_outer
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hBase_vle :
      ∀ f ∈ S, ∀ v ∈ rationalOpen C.base.T C.base.s, v.vle f C.base.s) :
    ∀ g ∈ S.erase f₀,
      ∀ v ∈ rationalOpen (laurentPlusDatum C.base f₀).T
                          (laurentPlusDatum C.base f₀).s,
        v.vle g (laurentPlusDatum C.base f₀).s := by
  intro g hg v hv
  -- plus half ⊆ base.
  have hv_base : v ∈ rationalOpen C.base.T C.base.s := laurentPlus_subset C.base f₀ hv
  -- `.s = C.base.s`; outer hBase_vle on g (∈ S by Finset.mem_of_mem_erase).
  exact hBase_vle g (Finset.mem_of_mem_erase hg) v hv_base

/-! #### Minus-half `hBase_vle` transfer — genuine gap

On the Laurent-minus half, the denominator changes: `(laurentMinusDatum
C.base f₀).s = C.base.s * f₀`. The outer `hBase_vle` gives
`v.vle g C.base.s`, i.e., `v(g) ≤ v(C.base.s)`; the minus-half
hypothesis needs `v.vle g (C.base.s * f₀)`, i.e.,
`v(g) ≤ v(C.base.s) * v(f₀)`. On the minus half, `v(f₀) ≥ v(C.base.s)`,
but this does NOT imply `v(f₀) ≥ 1`, and the desired bound
`v(C.base.s) ≤ v(C.base.s) * v(f₀)` fails when `v(f₀) < 1` (which is
possible, e.g., when `v(C.base.s) < 1` too).

Hence the minus-half `hBase_vle_minus` does NOT follow purely from
outer `hBase_vle` — it requires additional input such as `v(f₀) ≥ 1`
(holds when `f₀ ∈ A⁺` + `v(C.base.s) = 1`, or more generally via a
Wedhorn-normalisation constraint on the pseudo-uniformizer).

The minus-half transfer is therefore left as an EXPLICIT caller
hypothesis in the outer induction; no free reformulation is
available without the additional structure. -/

/-! ### `step_witness` introducer — the clean assembly API

`standardCover_hV_glue_induction_via_vle` takes its `step_witness`
argument as a `2 ≤ S.card → ∃ f₀ ∈ S, ∃ plus_section minus_section
hrefine hLaurentGlue, ∀ fV hV_compat, ... overlap ...` existential.
Constructing this existential from explicit components is a pure
bundling step — the introducer below captures it cleanly, decoupling
"what is a step_witness" from "how to build one."

**Usage**: at each level of an outer `Finset.strongInductionOn` on
`|S|`, the caller at `|S| ≥ 2` produces the 5 components (by picking
`f₀`, applying the IH on each Laurent half for the two sections,
supplying `hrefine` / `hLaurentGlue` / the overlap from compat-transfer)
and packages them via `step_witness_of_parts` for consumption by
`standardCover_hV_glue_induction_via_vle`. -/

/-- **Step-witness introducer**. Bundles the 6 explicit
step-witness components (chosen `f₀`, its membership, the two
half-section builders, the refinement dichotomy, the Laurent-gluing
witness, and the overlap-from-compat body) into the existential shape
consumed by `standardCover_hV_glue_induction_via_vle`'s `step_witness`
hypothesis.

Pure ⟨⟩-constructor; makes the step-witness interface explicit for
callers who build the components by hand or via the IH.

**Remaining top-level hypothesis**: the minus-half
`hBase_vle_minus` (the vle condition on the minus half for each
`g ∈ S.erase f₀`) is threaded THROUGH `minus_section` at construction
time — it does NOT appear as a separate parameter here because each
caller supplies it to their own `minus_section` builder. Similarly
for the Laurent gluing's analytic preconditions. -/
theorem RationalCoveringData.step_witness_of_parts
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A)
    (f₀ : A) (hf₀ : f₀ ∈ S)
    (plus_section : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_plus : presheafValue (laurentPlusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.standardCoverVCovers S })
          (hD_plus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T
                         (laurentPlusDatum C.base f₀).s),
          restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D })
    (minus_section : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_minus : presheafValue (laurentMinusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.standardCoverVCovers S })
          (hD_minus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentMinusDatum C.base f₀).T
                         (laurentMinusDatum C.base f₀).s),
          restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D })
    (hrefine : ∀ D : { D // D ∈ C.standardCoverVCovers S },
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s) ∨
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s))
    (hLaurentGlue : ∀ (u_plus : presheafValue (laurentPlusDatum C.base f₀))
      (u_minus : presheafValue (laurentMinusDatum C.base f₀))
      (_hoverlap : ∀ (D₃ : RationalLocData A)
        (h₃p : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
        (h₃m : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p u_plus =
          restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m u_minus),
      ∃ x : presheafValue C.base,
        restrictionMap C.base (laurentPlusDatum C.base f₀)
          (laurentPlus_subset C.base f₀) x = u_plus ∧
        restrictionMap C.base (laurentMinusDatum C.base f₀)
          (laurentMinus_subset C.base f₀) x = u_minus)
    (hoverlap_body : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1)
      (hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)),
      ∀ (D₃ : RationalLocData A)
        (h₃p : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
        (h₃m : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p
            (plus_section fV hV_compat).1 =
          restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m
            (minus_section fV hV_compat).1) :
    ∃ (f₀' : A) (_ : f₀' ∈ S)
      (plus_section' : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
          presheafValue D.1),
        (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
          (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
          (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
          restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
        { u_plus : presheafValue (laurentPlusDatum C.base f₀') //
          ∀ (D : { D // D ∈ C.standardCoverVCovers S })
            (hD_plus : rationalOpen D.1.T D.1.s ⊆
              rationalOpen (laurentPlusDatum C.base f₀').T
                           (laurentPlusDatum C.base f₀').s),
            restrictionMap (laurentPlusDatum C.base f₀') D.1 hD_plus u_plus = fV D })
      (minus_section' : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
          presheafValue D.1),
        (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
          (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
          (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
          restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
        { u_minus : presheafValue (laurentMinusDatum C.base f₀') //
          ∀ (D : { D // D ∈ C.standardCoverVCovers S })
            (hD_minus : rationalOpen D.1.T D.1.s ⊆
              rationalOpen (laurentMinusDatum C.base f₀').T
                           (laurentMinusDatum C.base f₀').s),
            restrictionMap (laurentMinusDatum C.base f₀') D.1 hD_minus u_minus = fV D })
      (_hrefine' : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        (rationalOpen D.1.T D.1.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀').T (laurentPlusDatum C.base f₀').s) ∨
        (rationalOpen D.1.T D.1.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀').T (laurentMinusDatum C.base f₀').s))
      (_hLaurentGlue' : ∀ (u_plus : presheafValue (laurentPlusDatum C.base f₀'))
        (u_minus : presheafValue (laurentMinusDatum C.base f₀'))
        (_hoverlap : ∀ (D₃ : RationalLocData A)
          (h₃p : rationalOpen D₃.T D₃.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀').T (laurentPlusDatum C.base f₀').s)
          (h₃m : rationalOpen D₃.T D₃.s ⊆
            rationalOpen (laurentMinusDatum C.base f₀').T (laurentMinusDatum C.base f₀').s),
          restrictionMap (laurentPlusDatum C.base f₀') D₃ h₃p u_plus =
            restrictionMap (laurentMinusDatum C.base f₀') D₃ h₃m u_minus),
        ∃ x : presheafValue C.base,
          restrictionMap C.base (laurentPlusDatum C.base f₀')
            (laurentPlus_subset C.base f₀') x = u_plus ∧
          restrictionMap C.base (laurentMinusDatum C.base f₀')
            (laurentMinus_subset C.base f₀') x = u_minus),
      ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
          presheafValue D.1)
        (hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
          (D₃ : RationalLocData A)
          (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
          (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
          restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)),
        ∀ (D₃ : RationalLocData A)
          (h₃p : rationalOpen D₃.T D₃.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀').T (laurentPlusDatum C.base f₀').s)
          (h₃m : rationalOpen D₃.T D₃.s ⊆
            rationalOpen (laurentMinusDatum C.base f₀').T (laurentMinusDatum C.base f₀').s),
          restrictionMap (laurentPlusDatum C.base f₀') D₃ h₃p
              (plus_section' fV hV_compat).1 =
            restrictionMap (laurentMinusDatum C.base f₀') D₃ h₃m
              (minus_section' fV hV_compat).1 :=
  ⟨f₀, hf₀, plus_section, minus_section, hrefine, hLaurentGlue, hoverlap_body⟩

/-- **`hV_glue` composition theorem**. Given explicit `plus_section`,
`minus_section`, `hrefine`, `hLaurentGlue`, and `hoverlap_body`
components (the five per-step-witness pieces expected by
`step_witness_of_parts`) and the outer `hBase_vle`, produces the
complete `hV_glue`-shaped output for the outer `(C, S)` standard-cover
V-cover via `standardCover_hV_glue_induction_via_vle`.

This is the **caller-ready API boundary** for the outer induction's
step: a caller supplying these 5 pieces (via their own Laurent-half
recursion machinery at `S.erase f₀`) gets the outer `hV_glue` for free,
without touching `step_witness_of_parts` or the `by_cases`-on-card
induction internally. -/
theorem RationalCoveringData.hV_glue_from_plusIH_and_minusBundle
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hf₀ : f₀ ∈ S) (hSnonempty : S.Nonempty)
    (hAplus : ∀ f ∈ S, f ∈ A⁺)
    (hBase_vle :
      ∀ f ∈ S, ∀ v ∈ rationalOpen C.base.T C.base.s, v.vle f C.base.s)
    (plus_section : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_plus : presheafValue (laurentPlusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.standardCoverVCovers S })
          (hD_plus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T
                         (laurentPlusDatum C.base f₀).s),
          restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D })
    (minus_section : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_minus : presheafValue (laurentMinusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.standardCoverVCovers S })
          (hD_minus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentMinusDatum C.base f₀).T
                         (laurentMinusDatum C.base f₀).s),
          restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D })
    (hrefine : ∀ D : { D // D ∈ C.standardCoverVCovers S },
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s) ∨
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s))
    (hLaurentGlue : ∀ (u_plus : presheafValue (laurentPlusDatum C.base f₀))
      (u_minus : presheafValue (laurentMinusDatum C.base f₀))
      (_hoverlap : ∀ (D₃ : RationalLocData A)
        (h₃p : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
        (h₃m : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p u_plus =
          restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m u_minus),
      ∃ x : presheafValue C.base,
        restrictionMap C.base (laurentPlusDatum C.base f₀)
          (laurentPlus_subset C.base f₀) x = u_plus ∧
        restrictionMap C.base (laurentMinusDatum C.base f₀)
          (laurentMinus_subset C.base f₀) x = u_minus)
    (hoverlap_body : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1)
      (hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)),
      ∀ (D₃ : RationalLocData A)
        (h₃p : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
        (h₃m : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p
            (plus_section fV hV_compat).1 =
          restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m
            (minus_section fV hV_compat).1) :
    ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base,
        ∀ D : { D // D ∈ C.standardCoverVCovers S },
          restrictionMap C.base D.1
            (C.standardCoverVCovers_subset_base S D.1 D.2) x = fV D :=
  C.standardCover_hV_glue_induction_via_vle S hSnonempty hAplus hBase_vle
    (fun _ => C.step_witness_of_parts S f₀ hf₀ plus_section minus_section
      hrefine hLaurentGlue hoverlap_body)

/-- **Part 2 caller-ready from plus IH + minus bundle**. Composes
`hV_glue_from_plusIH_and_minusBundle` with
`tateAcyclicity_Part2_from_standard_cover` to produce the Part 2 gluing
conclusion directly from the 5 step-witness pieces + Lane B `hE_sep` +
standard-cover containment + `hAplus` / `hBase_vle`.

This is the **strongest exported theorem** for a fixed standard cover
`S` with |S| ≥ 2: it exposes only the genuinely non-geometric residuals
(Lane A `hLaurentGlue`, Lane B `hE_sep`, minus-side `minus_section`)
while internalizing all the outer-induction plumbing on `|S|`. -/
theorem RationalCoveringData.tateAcyclicity_Part2_from_plusIH_and_minusBundle
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hf₀ : f₀ ∈ S) (hSnonempty : S.Nonempty)
    (hAplus : ∀ f ∈ S, f ∈ A⁺)
    (hBase_vle :
      ∀ f ∈ S, ∀ v ∈ rationalOpen C.base.T C.base.s, v.vle f C.base.s)
    (hS_contain : refines_contain C S)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (plus_section : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_plus : presheafValue (laurentPlusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.standardCoverVCovers S })
          (hD_plus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T
                         (laurentPlusDatum C.base f₀).s),
          restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D })
    (minus_section : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_minus : presheafValue (laurentMinusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.standardCoverVCovers S })
          (hD_minus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentMinusDatum C.base f₀).T
                         (laurentMinusDatum C.base f₀).s),
          restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D })
    (hrefine : ∀ D : { D // D ∈ C.standardCoverVCovers S },
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s) ∨
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s))
    (hLaurentGlue : ∀ (u_plus : presheafValue (laurentPlusDatum C.base f₀))
      (u_minus : presheafValue (laurentMinusDatum C.base f₀))
      (_hoverlap : ∀ (D₃ : RationalLocData A)
        (h₃p : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
        (h₃m : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p u_plus =
          restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m u_minus),
      ∃ x : presheafValue C.base,
        restrictionMap C.base (laurentPlusDatum C.base f₀)
          (laurentPlus_subset C.base f₀) x = u_plus ∧
        restrictionMap C.base (laurentMinusDatum C.base f₀)
          (laurentMinus_subset C.base f₀) x = u_minus)
    (hoverlap_body : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1)
      (hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)),
      ∀ (D₃ : RationalLocData A)
        (h₃p : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
        (h₃m : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p
            (plus_section fV hV_compat).1 =
          restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m
            (minus_section fV hV_compat).1)
    (hE_sep : ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (d : { D // D ∈ C.standardCoverVCovers S })
         (hd : C.standardCoverTau S hS_contain d = E),
        restrictionMap E.1 d.1 (hd ▸ C.standardCoverTau_subset S hS_contain d) a =
          restrictionMap E.1 d.1
            (hd ▸ C.standardCoverTau_subset S hS_contain d) b) →
        a = b) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  C.tateAcyclicity_Part2_from_standard_cover S hS_contain fC hC_compat
    (C.hV_glue_from_plusIH_and_minusBundle S f₀ hf₀ hSnonempty hAplus hBase_vle
      plus_section minus_section hrefine hLaurentGlue hoverlap_body)
    hE_sep

/-- **End-to-end caller-ready Part 2 theorem** for the `T-ACYC-PART2`
final assembly. Consumes:
* outer cover data + standard-cover refinement (`hS_contain`);
* outer section data `fC`, `hC_compat`;
* **plus-half recursive IH** `plus_hV_glue` (apply outer induction to
  `S.erase f₀` on `plusLaurentCovering_of_standardCoverVCovers`);
* **plus-side outer-V-piece bridge** `h_restriction_prop`
  (discharged via `outer_plusDatum_eq_inner_when_subset_plusHalf`);
* **minus-side bundle**: `minus_section`, `hrefine`, `hLaurentGlue`,
  `hoverlap_body` (Lane A `hLaurentGlue` + minus-side `minus_section`
  + refinement split);
* **Lane B residual** `hE_sep`.

Internally: builds `plus_section` via
`plus_section_of_plus_hV_glue_auto` (which auto-derives `plus_compat`
from outer `hV_compat`), composes with
`tateAcyclicity_Part2_from_plusIH_and_minusBundle`.

**The strongest exported Lane C theorem** for a fixed standard cover
`S` with `|S| ≥ 1` (singleton and step cases both handled by
`standardCover_hV_glue_induction_via_vle`'s card-dispatch). All
residuals are genuinely non-geometric:
* Lane A (`hLaurentGlue`) — `laurentCover_gluing_presheaf` analytic
  requirement.
* Lane B (`hE_sep`) — Cor 8.32 /
  `productRestriction_injective_tate_via_prime_extension_closed`.
* Minus-side `minus_section` — requires `hBase_vle_minus` beyond
  simple outer `hBase_vle` (genuine gap, see `### Minus-half hBase_vle
  transfer — genuine gap` docblock).
* Plus-side `h_restriction_prop` + `plus_hV_glue` IH — the recursive
  call to outer induction at `|S.erase f₀|`, bottoming out via
  `tateAcyclicity_augmentedCech_singleton` at `|S| = 1`. -/
theorem RationalCoveringData.tateAcyclicity_Part2_end_to_end
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hf₀ : f₀ ∈ S) (hSnonempty : S.Nonempty)
    (hAplus : ∀ f ∈ S, f ∈ A⁺)
    (hBase_vle :
      ∀ f ∈ S, ∀ v ∈ rationalOpen C.base.T C.base.s, v.vle f C.base.s)
    (hS_contain : refines_contain C S) (hS_cover : refines_cover C S)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (plus_hV_glue : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1)
      (_hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)),
      ∀ (fV_plus : ∀ D' : { D' // D' ∈ (C.plusLaurentCovering_of_standardCoverVCovers
          S f₀ hS_cover).standardCoverVCovers (S.erase f₀) },
          presheafValue D'.1),
        (∀ (D₁' D₂' : { D' // D' ∈ (C.plusLaurentCovering_of_standardCoverVCovers
            S f₀ hS_cover).standardCoverVCovers (S.erase f₀) })
          (D₃ : RationalLocData A)
          (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁'.1.T D₁'.1.s)
          (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂'.1.T D₂'.1.s),
          restrictionMap D₁'.1 D₃ h₃₁ (fV_plus D₁') =
            restrictionMap D₂'.1 D₃ h₃₂ (fV_plus D₂')) →
        ∃ u_plus : presheafValue (laurentPlusDatum C.base f₀),
          ∀ (D' : { D' // D' ∈ (C.plusLaurentCovering_of_standardCoverVCovers
              S f₀ hS_cover).standardCoverVCovers (S.erase f₀) })
            (hD' : rationalOpen D'.1.T D'.1.s ⊆
              rationalOpen (laurentPlusDatum C.base f₀).T
                           (laurentPlusDatum C.base f₀).s),
            restrictionMap (laurentPlusDatum C.base f₀) D'.1 hD' u_plus = fV_plus D')
    (h_restriction_prop : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1)
      (_hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)),
      ∀ (u_plus : presheafValue (laurentPlusDatum C.base f₀)),
        (∀ (D' : { D' // D' ∈ (C.plusLaurentCovering_of_standardCoverVCovers
            S f₀ hS_cover).standardCoverVCovers (S.erase f₀) })
          (hD' : rationalOpen D'.1.T D'.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T
                         (laurentPlusDatum C.base f₀).s),
          restrictionMap (laurentPlusDatum C.base f₀) D'.1 hD' u_plus =
            (let h_exists :=
               ((C.plusLaurentCovering_of_standardCoverVCovers S f₀
                 hS_cover).mem_standardCoverVCovers
                 (S.erase f₀)).mp D'.2
             let g := Classical.choose h_exists
             let hg_spec := Classical.choose_spec h_exists
             hg_spec.2 ▸ C.plusHalf_fV_transport_at_g S f₀ g hg_spec.1 fV)) →
        ∀ (D : { D // D ∈ C.standardCoverVCovers S })
          (hD_plus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T
                         (laurentPlusDatum C.base f₀).s),
          restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D)
    (minus_section : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_minus : presheafValue (laurentMinusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.standardCoverVCovers S })
          (hD_minus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentMinusDatum C.base f₀).T
                         (laurentMinusDatum C.base f₀).s),
          restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D })
    (hrefine : ∀ D : { D // D ∈ C.standardCoverVCovers S },
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s) ∨
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s))
    (hLaurentGlue : ∀ (u_plus : presheafValue (laurentPlusDatum C.base f₀))
      (u_minus : presheafValue (laurentMinusDatum C.base f₀))
      (_hoverlap : ∀ (D₃ : RationalLocData A)
        (h₃p : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
        (h₃m : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p u_plus =
          restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m u_minus),
      ∃ x : presheafValue C.base,
        restrictionMap C.base (laurentPlusDatum C.base f₀)
          (laurentPlus_subset C.base f₀) x = u_plus ∧
        restrictionMap C.base (laurentMinusDatum C.base f₀)
          (laurentMinus_subset C.base f₀) x = u_minus)
    (hoverlap_body : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1)
      (hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)),
      ∀ (D₃ : RationalLocData A)
        (h₃p : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
        (h₃m : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p
            (C.plus_section_of_plus_hV_glue_auto S f₀ hS_cover fV hV_compat
              (plus_hV_glue fV hV_compat) (h_restriction_prop fV hV_compat)).1 =
          restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m
            (minus_section fV hV_compat).1)
    (hE_sep : ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (d : { D // D ∈ C.standardCoverVCovers S })
         (hd : C.standardCoverTau S hS_contain d = E),
        restrictionMap E.1 d.1 (hd ▸ C.standardCoverTau_subset S hS_contain d) a =
          restrictionMap E.1 d.1
            (hd ▸ C.standardCoverTau_subset S hS_contain d) b) →
        a = b) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  C.tateAcyclicity_Part2_from_plusIH_and_minusBundle S f₀ hf₀ hSnonempty
    hAplus hBase_vle hS_contain fC hC_compat
    (fun fV hV_compat =>
      C.plus_section_of_plus_hV_glue_auto S f₀ hS_cover fV hV_compat
        (plus_hV_glue fV hV_compat) (h_restriction_prop fV hV_compat))
    minus_section hrefine hLaurentGlue hoverlap_body hE_sep

/-! ## Lane C close-out status (2026-04-21)

**Strongest exported caller-ready theorem**:
`tateAcyclicity_Part2_end_to_end` (~line 3657) — Part 2 exactness
for any standard cover `(C, S, f₀)` with `|S| ≥ 1`.

**Internalized (no caller discharge needed)**:
* Outer induction on `|S|` (singleton/step dispatch) — via
  `standardCover_hV_glue_induction_via_vle` + `step_witness_of_parts`.
* Plus-side `plus_compat` — auto-derived by
  `plus_compat_fn_from_outer_hV_compat`.
* Plus-side `plus_section` assembly from inner IH — via
  `plus_section_of_plus_hV_glue_auto`.
* Laurent split + V-cover transport (structural iterated-Laurent
  manipulation) — via `plusLaurentCovering_of_standardCoverVCovers` +
  `plusHalf_fV_transport_at_g` + `plusHalf_transported_compat_at_g`.

**Genuine non-geometric residuals** (caller-supplied):
* **Lane A** (`hLaurentGlue`) — `laurentCover_gluing_presheaf` from
  `LaurentOverlap.lean`; T-OVERLAP-COMPAT completion analysis.
* **Lane B** (`hE_sep`) — `productRestriction_injective_tate_via_prime_extension_closed`
  from `Cor832.lean`; Cor 8.32 prime-extension closedness.
* **Minus-side `minus_section`** — requires `hBase_vle_minus` beyond
  simple outer `hBase_vle`; genuine gap on iterated minus, see
  `### Minus-half hBase_vle transfer — genuine gap` docblock (~line 3209).
* **Plus-side recursive IH** (`plus_hV_glue`) — recursive call to
  outer induction at `|S.erase f₀|`. Bottoms out at `|S| = 1` via
  `tateAcyclicity_augmentedCech_singleton`.
* **Plus-side outer V-piece bridge** (`h_restriction_prop`) — bridges
  inner V-piece restriction property to outer V-pieces in the plus
  half. Derivable via `outer_plusDatum_eq_inner_when_subset_plusHalf`
  but the full automatic derivation is left as caller input
  (avoids a large rational-open-equality transport layer).

**File stats** (post close-out): ~5360 lines; full `lake build` clean
across 2756 jobs.
-/

/-! ### Full `Finset.strongInductionOn` outer induction — remaining plumbing

With `standardCover_hV_glue_induction_via_vle` + `hBase_vle_plusHalf_of_outer`
+ `step_witness_of_parts` in hand, the outer induction over `|S|` has
a clean SCAFFOLD: induct on `S.card` via `Nat.strong_induction_on`,
dispatch on `S.card = 1` (base) vs `S.card ≥ 2` (step), and at each
step call `standardCover_hV_glue_induction_via_vle` with a step_witness
built via `step_witness_of_parts` from:

* `plus_section` — built by invoking the IH on the plus half with
  `(S.erase f₀)` on `plusLaurentCovering_of_standardCoverVCovers C S f₀`.
* `minus_section` — similar on the minus half, with caller-supplied
  `hBase_vle_minus`.
* `hrefine` — dischargeable via `refinedVCovers` or caller-supplied.
* `hLaurentGlue` — from `laurentCover_gluing_presheaf` (Lane A, once
  T-OVERLAP-COMPAT lands).
* `hoverlap_body` — from `plusLaurent_compat_transfer` +
  `minusLaurent_compat_transfer` + the IH's restriction property.

**Remaining plumbing** (NOT landed this session — requires substantial
type-level machinery to align iterated Laurent datum structures):

1. **V-cover indexing alignment** between outer `standardCoverVCovers S`
   (= `{C.plusDatum g | g ∈ S}`) and inner `(plusC).standardCoverVCovers
   (S.erase f₀)` (= `{laurentPlusDatum (laurentPlusDatum C.base f₀) g | g ∈ S.erase f₀}`).
   These have the same underlying membership (up to `insert_comm` on T)
   but differ structurally. Bridging requires either:
   (i) a canonical `iteratedLaurentPlus_swap` lemma stating the two
       iterated-plus orderings produce the same rational open,
   (ii) reformulating `plusLaurentCovering_of_standardCoverVCovers` to
       use the OUTER iterated-plus shape directly.

2. **fV transport** between outer and inner V-cover indices: given
   outer `fV` on `C.standardCoverVCovers S`, construct inner
   `fV_plus` on `(plusC).standardCoverVCovers (S.erase f₀)` via
   restriction composed with the V-cover bridge.

3. **Restriction property transfer** at the recursion boundary: the
   inner `u_plus`'s restriction to inner V-pieces must be repackaged
   as `u_plus`'s restriction to outer V-pieces that land in the plus
   half. Uses `restrictionMap_comp` + proof-irrelevance on containment
   witnesses.

All three are mechanical once the indexing alignment (item 1) lands;
items 2 and 3 are ~30-50 lines each of `restrictionMap_comp` bookkeeping.

The combined outer induction (after items 1-3 land) would discharge the
`step_witness` hypothesis of `standardCover_hV_glue_induction_via_vle`
entirely internally, leaving only the minus-side `hBase_vle_minus`
(structural gap, see doc block above) and the Lane-A Laurent gluing
analytic preconditions as caller-supplied.

**This session's concrete outputs** (items above the dashed line):
* `standardCover_hV_glue_induction_via_vle` — `h1T`-free variant with
  semantic vle hypothesis (landed earlier).
* `hBase_vle_plusHalf_of_outer` — automatic plus-half vle transfer.
* `step_witness_of_parts` — the ⟨⟩ introducer for step_witness
  components.
* Precise boundary documentation for the remaining recursion plumbing. -/

/-! ### Cardinality-based recursion witness combining all pieces

For the outer induction `standardCover_hV_glue_induction` (above),
the recursion structure combines:
* **Termination**: `Finset.card_erase_of_mem_decreases` —
  `|S.erase f₀| < |S|` when `f₀ ∈ S`.
* **Plus-half V-cover**: `plusLaurentCovering_of_standardCoverVCovers`
  (above) — given `refines_cover C S`, yields a `RationalCoveringData` on
  the plus half.
* **Minus-half V-cover**: `minusLaurentCovering_of_standardCoverVCovers`
  (above).
* **Plus-half `refines_contain`**: `refines_contain_plusHalf_of_refines_cover`
  (above) — automatic for the standard-cover V-cover scenario.
* **Minus-half pointwise containment**:
  `minusLaurentCovering_pointwise_contain_of_refines_cover` (above) —
  the weakest reusable form of minus-half containment.
* **Compatibility transfer**: ✅ fully proved via
  `plusLaurent_compat_transfer` and `minusLaurent_compat_transfer`
  (above) — when the caller takes the natural
  `restrict_to_plus := fun D => restrictionMap D.1 (laurentPlusDatum D.1 f₀) _ (fV D)`,
  compatibility of the half-restrictions follows unconditionally from
  the outer `hV_compat` via two `restrictionMap_comp` applications.
  The skeleton variants (`_skeleton` suffix) remain for callers using
  a different `restrict_to_half`.
* **Singleton base**: `hV_glue_singleton_of_Aplus` (T012).
* **Step**: `hV_glue_step_from_laurent_halves` (S-GEOM-HVGLUE-earlier).

The caller's outer induction uses `Finset.strongInductionOn` on `|S|`,
calling the singleton base at `|S| = 1` and the step at `|S| = n + 1`,
with the two Laurent-half V-covers providing the recursive `hV_glue`
arguments on sub-covers of size `|S.erase f₀| < |S|`.

**Remaining for full unconditional builder** (update 2026-04-20):
- Compat-transfer proof bodies: ✅ landed
  (`plusLaurent_compat_transfer`, `minusLaurent_compat_transfer`).
- Span-top / no-common-zero transfer to Laurent halves: PARTIAL.
  Landed the clean helpers
  `noCommonZero_plusHalf_of_refines_span_top`,
  `noCommonZero_minusHalf_of_refines_span_top`,
  `f₀_notZero_on_minusHalf`, and the parametric
  `refines_span_top_erase_of_localised_nullstellensatz`. The FULL
  `S.erase f₀` span-top transfer requires a **localised Prop 7.14**
  (adic Nullstellensatz on Laurent-half rational opens) that is NOT
  in the project. See the `### Span-top / no-common-zero transfer`
  doc block above for the precise missing theorem boundary. The
  `refines_span_top`
transfer is `Ideal.span S = ⊤ in A` → `Ideal.span S = ⊤ in A` itself
(trivial, the predicate doesn't change) when the V-cover uses the same
`S`; the cardinality decrease comes from reducing to `S.erase f₀` via
the `f₀`-redundancy on the plus half (needs `hS_cover` at lifted
valuations) and a parallel argument on the minus half. Full recursion is
~120-150 more lines; deferred to follow-up passes. -/

/-! ## Roadmap: Laurent-cover induction for `hV_glue`

The next step in closing T-GEOM-RED is to build `hV_glue` for a
standard-cover refinement `V` from the pointwise Laurent-cover gluing
`laurentCover_gluing_presheaf`.

### Inductive target

Given `S : StandardCover A` (i.e. `S.elts : Finset A` with
`Ideal.span S.elts = ⊤`) refining `C` via the plus-pieces
`rationalOpen (insert f C.base.T) C.base.s` for `f ∈ S.elts`, the
`hV_glue` obligation is: for any compatible family on these plus-pieces,
there is a global section on `C.base`.

Induction on `|S.elts|`:

* **Base case `|S.elts| = 1`**: `S = {f}` with `Ideal.span {f} = ⊤`
  forces `f ∈ Aˣ`. The single plus-piece equals `rationalOpen C.base.T
  C.base.s` (since `v(f) > 0` for every valuation, so `v(f) ≤ v(C.base.s)`
  is the only nontrivial constraint). Gluing is trivial: the compatible
  family has a unique element which *is* the global section.

* **Inductive step `|S.elts| = n + 1`**: pick any `f₀ ∈ S.elts`. Apply
  Laurent cover at `f₀` to split `rationalOpen C.base.T C.base.s` into
  `rationalOpen (insert f₀ C.base.T) C.base.s` (plus at `f₀`) and
  `rationalOpen ((insert C.base.s C.base.T).product ... .image ...)
  (C.base.s * f₀)` (minus at `f₀`).

  Apply `laurentCover_gluing_presheaf` (after T-OV-1 lands) at `f₀` to
  the given V-compatible family, restricted to each half. The induction
  hypothesis applies to the `n`-element standard cover `S.elts \ {f₀}`
  on each half (after appropriate refinement adjustments).

### Remaining obligations

The induction requires:

1. **Laurent-cover splitting at the base level with compatibility transfer**:
   given a compatible family on `V_covers`, its restriction to each
   Laurent half is compatible. Mechanical.

2. **Intersection-of-refinements construction**: the induction step needs
   to refine `S.elts \ {f₀}` onto each Laurent half, which may require
   taking intersections with the plus/minus datum. This is the
   `laurentPlus/MinusDatum` composition that's already modelled in
   `laurentOverlapDatum`.

3. **`laurentCover_gluing_presheaf`** (provided externally, modulo T-OV-1).

4. **Local cover-level injectivity** for each piece of each refinement
   step (provided by T-IDEAL-2 via Cor 8.32, applied at each level).

Estimated lines for the full induction: ~150-250, once T-OV-1 and
T-IDEAL-2 land. This file currently provides the base-case wrap
(`tateAcyclicity_gluing_via_refinement_cover_level`); the inductive
assembly is deferred to a follow-up session.

The concrete next step is to formalize the base-case `|S.elts| = 1`
lemma and the "Laurent split transfers compatibility" lemma; both are
mechanical given `laurentCover_gluing_presheaf` and the existing
restriction-map API. -/

/-! ### Step-witness discharge in terms of inner hV_glue + separation

The `step_witness` hypothesis of `standardCover_hV_glue_induction` can be
assembled from inner hV_glue's on the two Laurent halves, together with:

* **Compatibility transfer**: the outer compat → inner compat on each
  Laurent half. Mechanical via `restrictionMap_comp`.
* **Section identification**: the inner hV_glue's output section
  `u_plus` (resp. `u_minus`) restricts correctly to outer V-pieces.
  Requires local injectivity of `restrictionMap D E'` for `E' ⊆ D`,
  which comes from Cor 8.32 / T-IDEAL-2.
* **Refinement split**: each V-piece `D` lands entirely in plus or
  minus half. Requires a refinement of the V-cover (intersect each
  `D` with each Laurent half), also handled by Wedhorn 8.34's
  construction.
* **Laurent gluing**: from `laurentCover_gluing_presheaf`, blocked by
  T-OV-1.

Each piece is isolated below as a named theorem or bundled hypothesis
so the caller can invoke it with whatever discharge route is available
at the point of use. -/

/-- **Step-witness assembly from explicit section-construction bundle**.
Given explicit `plus_section`, `minus_section`, refinement split,
Laurent gluing, and overlap-from-compat, packages them into the
`step_witness` format expected by `standardCover_hV_glue_induction`.

This is the tuple-wrapping shape; the substantive work is supplying the
five section-construction arguments. Each one is a hypothesis-shape
match with `hV_glue_step_from_laurent_halves`'s input. -/
theorem RationalCoveringData.step_witness_of_bundle
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A)
    (f₀ : A) (hf₀ : f₀ ∈ S)
    (plus_section : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_plus : presheafValue (laurentPlusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.standardCoverVCovers S })
          (hD_plus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T
                         (laurentPlusDatum C.base f₀).s),
          restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D })
    (minus_section : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_minus : presheafValue (laurentMinusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.standardCoverVCovers S })
          (hD_minus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentMinusDatum C.base f₀).T
                         (laurentMinusDatum C.base f₀).s),
          restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D })
    (hrefine : ∀ D : { D // D ∈ C.standardCoverVCovers S },
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s) ∨
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s))
    (hLaurentGlue : ∀ (u_plus : presheafValue (laurentPlusDatum C.base f₀))
      (u_minus : presheafValue (laurentMinusDatum C.base f₀))
      (_hoverlap : ∀ (D₃ : RationalLocData A)
        (h₃p : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
        (h₃m : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p u_plus =
          restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m u_minus),
      ∃ x : presheafValue C.base,
        restrictionMap C.base (laurentPlusDatum C.base f₀)
          (laurentPlus_subset C.base f₀) x = u_plus ∧
        restrictionMap C.base (laurentMinusDatum C.base f₀)
          (laurentMinus_subset C.base f₀) x = u_minus)
    (hOvlp : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1)
      (hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)),
      ∀ (D₃ : RationalLocData A)
        (h₃p : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
        (h₃m : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p
            (plus_section fV hV_compat).1 =
          restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m
            (minus_section fV hV_compat).1) :
    2 ≤ S.card →
      ∃ (f₀' : A) (_ : f₀' ∈ S)
        (plus_section' : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
            presheafValue D.1),
          (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
            (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
            (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
            restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
          { u_plus : presheafValue (laurentPlusDatum C.base f₀') //
            ∀ (D : { D // D ∈ C.standardCoverVCovers S })
              (hD_plus : rationalOpen D.1.T D.1.s ⊆
                rationalOpen (laurentPlusDatum C.base f₀').T
                             (laurentPlusDatum C.base f₀').s),
              restrictionMap (laurentPlusDatum C.base f₀') D.1 hD_plus u_plus = fV D })
        (minus_section' : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
            presheafValue D.1),
          (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
            (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
            (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
            restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
          { u_minus : presheafValue (laurentMinusDatum C.base f₀') //
            ∀ (D : { D // D ∈ C.standardCoverVCovers S })
              (hD_minus : rationalOpen D.1.T D.1.s ⊆
                rationalOpen (laurentMinusDatum C.base f₀').T
                             (laurentMinusDatum C.base f₀').s),
              restrictionMap (laurentMinusDatum C.base f₀') D.1 hD_minus u_minus = fV D })
        (_hrefine : ∀ D : { D // D ∈ C.standardCoverVCovers S },
          (rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀').T (laurentPlusDatum C.base f₀').s) ∨
          (rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentMinusDatum C.base f₀').T (laurentMinusDatum C.base f₀').s))
        (_hLaurentGlue : ∀ (u_plus : presheafValue (laurentPlusDatum C.base f₀'))
          (u_minus : presheafValue (laurentMinusDatum C.base f₀'))
          (_hoverlap : ∀ (D₃ : RationalLocData A)
            (h₃p : rationalOpen D₃.T D₃.s ⊆
              rationalOpen (laurentPlusDatum C.base f₀').T (laurentPlusDatum C.base f₀').s)
            (h₃m : rationalOpen D₃.T D₃.s ⊆
              rationalOpen (laurentMinusDatum C.base f₀').T (laurentMinusDatum C.base f₀').s),
            restrictionMap (laurentPlusDatum C.base f₀') D₃ h₃p u_plus =
              restrictionMap (laurentMinusDatum C.base f₀') D₃ h₃m u_minus),
          ∃ x : presheafValue C.base,
            restrictionMap C.base (laurentPlusDatum C.base f₀')
              (laurentPlus_subset C.base f₀') x = u_plus ∧
            restrictionMap C.base (laurentMinusDatum C.base f₀')
              (laurentMinus_subset C.base f₀') x = u_minus),
        ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S }, presheafValue D.1)
          (hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
            (D₃ : RationalLocData A)
            (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
            (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
            restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)),
          ∀ (D₃ : RationalLocData A)
            (h₃p : rationalOpen D₃.T D₃.s ⊆
              rationalOpen (laurentPlusDatum C.base f₀').T (laurentPlusDatum C.base f₀').s)
            (h₃m : rationalOpen D₃.T D₃.s ⊆
              rationalOpen (laurentMinusDatum C.base f₀').T (laurentMinusDatum C.base f₀').s),
            restrictionMap (laurentPlusDatum C.base f₀') D₃ h₃p
                (plus_section' fV hV_compat).1 =
              restrictionMap (laurentMinusDatum C.base f₀') D₃ h₃m
                (minus_section' fV hV_compat).1 :=
  fun _h2 => ⟨f₀, hf₀, plus_section, minus_section, hrefine, hLaurentGlue, hOvlp⟩

/-! ### S-GEOM-ASM: Part-2 wiring via geometric reduction

`tateAcyclicity_Part2_via_geometric_reduction` composes
`standardCover_hV_glue_induction` (the S-GEOM-IND induction output)
with `tateAcyclicity_Part2_from_standard_cover` (the cover-level
assembly) to produce the exact shape required at
`LaurentRefinement.lean:3737` — namely: a global section on `C.base`
extending a compatible family on the original `C.covers`, given a
standard-cover refinement `S` of `C`.

The remaining *genuinely-explicit* hypotheses at this entry point are:

* `step_witness` — the Laurent-split step ingredients. Discharged by
  `step_witness_of_bundle` + inner hV_glue's + local separation
  (Cor 8.32 / T-IDEAL-2) + Laurent gluing (T-OV-1).
* `hE_sep` — cover-level local separation hypothesis at each
  `E ∈ C.covers`. Discharged by
  `productRestriction_injective_tate_via_prime_extension_closed`
  (`Cor832.lean`) applied at each `E`'s local V-sub-cover.
* `hC_compat` — outer compatibility of the `C.covers`-family. Provided
  by the caller (typically the sheaf condition from a higher-level
  statement).

When T-OVERLAP-COMPAT lands in `LaurentRefinement.lean` (`:3173`), the
`step_witness` discharge becomes internal modulo the sub-cover
adjustment Wedhorn 8.34 proof; `hE_sep` is independently discharged
from T-IDEAL-2; and this theorem closes `tateAcyclicity` Part 2. -/

/-- **`tateAcyclicity` Part 2 via the geometric reduction induction**
(τ-route, superseded — see module docblock "Historical τ-route").
Composes `standardCover_hV_glue_induction` + `tateAcyclicity_Part2_from_standard_cover`
into the exact Part-2 shape required at `LaurentRefinement.lean:3737`.

**Prefer `tateAcyclicity_Part2_via_hZavyalov_per_E_direct`** (direct
per-E route) for new downstream code. This τ-route wrapper is kept for
reference and backward compatibility. -/
theorem RationalCoveringData.tateAcyclicity_Part2_via_geometric_reduction
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (C : RationalCoveringData A) (S : Finset A)
    (hSnonempty : S.Nonempty)
    (hS_contain : refines_contain C S)
    (hAplus : ∀ f ∈ S, f ∈ A⁺)
    (h1T : (1 : A) ∈ C.base.T)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    -- `step_witness` is the S-GEOM-IND step ingredient (see
    -- `standardCover_hV_glue_induction` for exact shape). Vacuous for
    -- `|S| = 1`; discharged via inner hV_glue + Cor 8.32 + T-OV-1 otherwise.
    (step_witness : 2 ≤ S.card →
      ∃ (f₀ : A) (_ : f₀ ∈ S)
        (plus_section : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
            presheafValue D.1),
          (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
            (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
            (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
            restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
          { u_plus : presheafValue (laurentPlusDatum C.base f₀) //
            ∀ (D : { D // D ∈ C.standardCoverVCovers S })
              (hD_plus : rationalOpen D.1.T D.1.s ⊆
                rationalOpen (laurentPlusDatum C.base f₀).T
                             (laurentPlusDatum C.base f₀).s),
              restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D })
        (minus_section : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
            presheafValue D.1),
          (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
            (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
            (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
            restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
          { u_minus : presheafValue (laurentMinusDatum C.base f₀) //
            ∀ (D : { D // D ∈ C.standardCoverVCovers S })
              (hD_minus : rationalOpen D.1.T D.1.s ⊆
                rationalOpen (laurentMinusDatum C.base f₀).T
                             (laurentMinusDatum C.base f₀).s),
              restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D })
        (_hrefine : ∀ D : { D // D ∈ C.standardCoverVCovers S },
          (rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s) ∨
          (rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s))
        (_hLaurentGlue : ∀ (u_plus : presheafValue (laurentPlusDatum C.base f₀))
          (u_minus : presheafValue (laurentMinusDatum C.base f₀))
          (_hoverlap : ∀ (D₃ : RationalLocData A)
            (h₃p : rationalOpen D₃.T D₃.s ⊆
              rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
            (h₃m : rationalOpen D₃.T D₃.s ⊆
              rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
            restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p u_plus =
              restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m u_minus),
          ∃ x : presheafValue C.base,
            restrictionMap C.base (laurentPlusDatum C.base f₀)
              (laurentPlus_subset C.base f₀) x = u_plus ∧
            restrictionMap C.base (laurentMinusDatum C.base f₀)
              (laurentMinus_subset C.base f₀) x = u_minus),
        ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S }, presheafValue D.1)
          (hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
            (D₃ : RationalLocData A)
            (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
            (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
            restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)),
          ∀ (D₃ : RationalLocData A)
            (h₃p : rationalOpen D₃.T D₃.s ⊆
              rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
            (h₃m : rationalOpen D₃.T D₃.s ⊆
              rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
            restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p
                (plus_section fV hV_compat).1 =
              restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m
                (minus_section fV hV_compat).1)
    (hE_sep : ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (d : { D // D ∈ C.standardCoverVCovers S })
         (hd : C.standardCoverTau S hS_contain d = E),
        restrictionMap E.1 d.1 (hd ▸ C.standardCoverTau_subset S hS_contain d) a =
          restrictionMap E.1 d.1
            (hd ▸ C.standardCoverTau_subset S hS_contain d) b) →
        a = b) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  C.tateAcyclicity_Part2_from_standard_cover S hS_contain fC hC_compat
    (C.standardCover_hV_glue_induction S hSnonempty hAplus h1T step_witness)
    hE_sep

/-! ### S-GEOM-ASM: Refined-V-cover Part-2 wrapper

An alternative Part-2 wrapper using the refined V-cover
`refinedVCovers` (above). The refined V-cover satisfies the per-V-piece
plus/minus dichotomy by construction
(`refinedVCovers_plusMinus_dichotomy`), so the `hV_glue` hypothesis's
Laurent-split discharge becomes structurally cleaner: each refined piece
is in exactly one Laurent half, enabling separate `hV_glue` calls on
each half + `laurentCover_gluing_presheaf` to recombine.

This wrapper uses `gluing_of_finer_rational` (`RationalRefinement.lean`),
which accepts an arbitrary `V_covers : Finset (RationalLocData A)` with
a refinement map `τ` to `C.covers`. We compose
`standardCoverTau ∘ refinedVCoversTau` to produce the `τ` going
refined-V-cover → `C.standardCoverVCovers S` → `C.covers`.

The remaining explicit hypotheses at this entry point:
* `hV_glue_refined` — compatible family on the refined V-cover extends
  to a global section on `C.base`. Discharge route:
  `hV_glue_refined_from_laurent_halves` below, which reduces it to
  inner `hV_glue`'s on each Laurent half + `laurentCover_gluing_presheaf`
  (T-OV-1). Not yet unconditional (requires inner hV_glue's, which are
  the S-GEOM-IND recursion output).
* `hE_sep_refined` — local separation at each `E ∈ C.covers`. Discharge
  via `productRestriction_injective_tate_via_prime_extension_closed`
  (`Cor832.lean:1581`) applied at each `E`'s local refined-V-sub-cover.

When T-OVERLAP-COMPAT lands (unblocking `laurentCover_gluing_presheaf`)
and T-IDEAL-2 closes `hE_sep_refined`, this theorem closes `tateAcyclicity`
Part 2 at `LaurentRefinement.lean:3737`. -/

/-- **Part 2 via refined V-cover + `gluing_of_finer_rational`**
(τ-route, superseded — prefer `tateAcyclicity_Part2_direct_per_E`).
Analogous to `tateAcyclicity_Part2_via_geometric_reduction`, but uses
the refined V-cover (with per-piece plus/minus dichotomy) as the
intermediate V-cover. The refinement map `τ` composes
`refinedVCoversTau` (refined-V-cover → standard V-cover) with
`standardCoverTau` (standard V-cover → outer `C.covers`).

Takes `hV_glue_refined` and `hE_sep_refined` as explicit hypotheses
(discharged post-T-OV-1 and T-IDEAL-2 respectively). -/
theorem RationalCoveringData.tateAcyclicity_Part2_via_refined_geometric_reduction
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hS_cover : refines_cover C S)
    (hS_contain : refines_contain C S)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (hV_glue_refined : ∀
      (fV : ∀ D : { D // D ∈ C.refinedVCovers S f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S f₀ }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ C.refinedVCovers S f₀ },
        restrictionMap C.base D.1
          (C.refinedVCovers_subset_base S f₀ D.1 D.2) x = fV D)
    (hE_sep_refined : ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (d : { D // D ∈ C.refinedVCovers S f₀ })
         (hd : C.standardCoverTau S hS_contain
                (C.refinedVCoversTau S f₀ d) = E),
        restrictionMap E.1 d.1
            (hd ▸ ((C.refinedVCoversTau_subset S f₀ d).trans
              (C.standardCoverTau_subset S hS_contain
                (C.refinedVCoversTau S f₀ d)))) a =
          restrictionMap E.1 d.1
            (hd ▸ ((C.refinedVCoversTau_subset S f₀ d).trans
              (C.standardCoverTau_subset S hS_contain
                (C.refinedVCoversTau S f₀ d)))) b) →
        a = b) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  -- Invoke `gluing_of_finer_rational` directly with the refined V-cover.
  -- The `hS_cover` is unused here (the refined V-cover is specified
  -- independently); it would be used to discharge `hV_glue_refined`
  -- via `hV_glue_refined_from_laurent_halves`.
  have _ := hS_cover
  exact gluing_of_finer_rational C (C.refinedVCovers S f₀)
    (fun D hD => C.refinedVCovers_subset_base S f₀ D hD)
    (fun d => C.standardCoverTau S hS_contain (C.refinedVCoversTau S f₀ d))
    (fun d => (C.refinedVCoversTau_subset S f₀ d).trans
      (C.standardCoverTau_subset S hS_contain (C.refinedVCoversTau S f₀ d)))
    fC hC_compat hV_glue_refined hE_sep_refined

/-! ### `hV_glue_refined` discharge via Laurent-cover gluing

The `hV_glue_refined` hypothesis of
`tateAcyclicity_Part2_via_refined_geometric_reduction` can be reduced
to:
* An inner `hV_glue` on the plus-half, indexed by the plus-refined
  pieces of `refinedVCovers` (which live in `laurentPlusDatum C.base f₀`).
* An inner `hV_glue` on the minus-half, indexed by the minus-refined
  pieces.
* `laurentCover_gluing_presheaf` (T-OV-1).

Each inner `hV_glue` is an S-GEOM-IND recursive call on the relevant
Laurent half at one level of cardinality decrease. When the refined
V-cover has `|S|` plus-refined + `|S|` minus-refined pieces, the inner
V-covers are `|S|`-indexed (potentially could still be reduced but
already well-defined).

We expose the discharge structure as a named hypothesis-taking theorem.
The substantial work — T-OV-1 for `laurentCover_gluing_presheaf`, and
T-IDEAL-2 for inner separation — is captured as explicit hypotheses so
the lane can stay axiom-clean until those dependencies land. -/

/-- **`hV_glue_refined` discharge (skeleton)**. Exposes the structure
for discharging `hV_glue_refined` given two inner `hV_glue`s on the
Laurent halves plus the Laurent-cover gluing (T-OV-1 hypothesis).

The inner `hV_glue`s are hypotheses parameterised on a transferred
compatible family; the Laurent gluing is the Wedhorn 8.33 / Hübner 3.7
exact-row content.

Statement only: full discharge requires the compat-transfer and
section-identification machinery (see the S-GEOM-IND documentation
above). -/
theorem RationalCoveringData.hV_glue_refined_from_laurent_halves
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (_hS_cover : refines_cover C S)
    -- Inner hV_glue on the plus half (indexed by plus-refined subset of refined V-cover).
    (_plus_section_refined : ∀
      (fV : ∀ D : { D // D ∈ C.refinedVCovers S f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S f₀ }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_plus : presheafValue (laurentPlusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.refinedVCovers S f₀ })
          (hD_plus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T
                         (laurentPlusDatum C.base f₀).s),
          restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D })
    -- Inner hV_glue on the minus half.
    (_minus_section_refined : ∀
      (fV : ∀ D : { D // D ∈ C.refinedVCovers S f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S f₀ }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_minus : presheafValue (laurentMinusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.refinedVCovers S f₀ })
          (hD_minus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentMinusDatum C.base f₀).T
                         (laurentMinusDatum C.base f₀).s),
          restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D })
    -- Laurent gluing at `f₀` on `C.base` (T-OV-1 content).
    (_hLaurentGlue : ∀ (u_plus : presheafValue (laurentPlusDatum C.base f₀))
      (u_minus : presheafValue (laurentMinusDatum C.base f₀))
      (_hoverlap : ∀ (D₃ : RationalLocData A)
        (h₃p : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
        (h₃m : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p u_plus =
          restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m u_minus),
      ∃ x : presheafValue C.base,
        restrictionMap C.base (laurentPlusDatum C.base f₀)
          (laurentPlus_subset C.base f₀) x = u_plus ∧
        restrictionMap C.base (laurentMinusDatum C.base f₀)
          (laurentMinus_subset C.base f₀) x = u_minus)
    -- Overlap-from-compat hypothesis (kept explicit).
    (hOverlap : ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S f₀ }, presheafValue D.1)
      (_hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S f₀ })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂))
      (u_plus : presheafValue (laurentPlusDatum C.base f₀))
      (u_minus : presheafValue (laurentMinusDatum C.base f₀))
      (_huplus : ∀ (D : { D // D ∈ C.refinedVCovers S f₀ })
        (hD_plus : rationalOpen D.1.T D.1.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T
                       (laurentPlusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D)
      (_huminus : ∀ (D : { D // D ∈ C.refinedVCovers S f₀ })
        (hD_minus : rationalOpen D.1.T D.1.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T
                       (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D),
      ∀ (D₃ : RationalLocData A)
        (h₃p : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
        (h₃m : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p u_plus =
          restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m u_minus) :
    ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S f₀ }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ C.refinedVCovers S f₀ },
        restrictionMap C.base D.1
          (C.refinedVCovers_subset_base S f₀ D.1 D.2) x = fV D := by
  intro fV compat
  -- Build u_plus from the plus_section_refined bundle.
  let u_plus := (_plus_section_refined fV compat).1
  have huplus := (_plus_section_refined fV compat).2
  let u_minus := (_minus_section_refined fV compat).1
  have huminus := (_minus_section_refined fV compat).2
  -- Derive overlap from outer compat + both half corrections.
  have hov := hOverlap fV compat u_plus u_minus huplus huminus
  -- Apply Laurent gluing to get x : presheafValue C.base.
  obtain ⟨x, hx_p, hx_m⟩ := _hLaurentGlue u_plus u_minus hov
  refine ⟨x, fun D => ?_⟩
  -- For each refined V-piece D: it lies in plus or minus half by the
  -- dichotomy lemma. Case-split and use the corresponding huplus / huminus.
  rcases C.refinedVCovers_plusMinus_dichotomy S f₀ D.1 D.2 with hDplus | hDminus
  · -- D ⊆ plus-half: compose restriction C.base → plus-half → D.1.
    have hcomp := congr_fun
      (restrictionMap_comp C.base (laurentPlusDatum C.base f₀) D.1
        (laurentPlus_subset C.base f₀) hDplus) x
    simp only [Function.comp_apply] at hcomp
    rw [hx_p, huplus D hDplus] at hcomp
    exact hcomp.symm
  · -- D ⊆ minus-half: compose restriction C.base → minus-half → D.1.
    have hcomp := congr_fun
      (restrictionMap_comp C.base (laurentMinusDatum C.base f₀) D.1
        (laurentMinus_subset C.base f₀) hDminus) x
    simp only [Function.comp_apply] at hcomp
    rw [hx_m, huminus D hDminus] at hcomp
    exact hcomp.symm

/-- Refined V-cover gluing from Laurent halves, with the Laurent-cover gluing
leg specialized to the concrete caller-ready overlap theorem
`laurentCover_gluing_presheaf_via_primary`.

This removes the abstract `hLaurentGlue` input from
`hV_glue_refined_from_laurent_halves`; the remaining explicit overlap input is
the compatibility transfer `hOverlap`. -/
theorem RationalCoveringData.hV_glue_refined_from_laurent_halves_via_primary
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    [IsNoetherianRing C.base.P.A₀]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (hS_cover : refines_cover C S)
    (hNoeth_B : IsNoetherianRing (presheafValue C.base))
    (hLocLift_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing C.base.P C.base
      HasLocLiftPowerBounded (presheafValue C.base))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing C.base.P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete C.base.P C.base).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue C.base)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue C.base)))
    (hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing C.base.P C.base
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing C.base.P C.base
      letI : HasLocLiftPowerBounded (presheafValue C.base) := hLocLift_B
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue C.base) :=
        presheafValue_pairOfDefinition_concrete C.base.P C.base
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue C.base) (C.base.canonicalMap f₀))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue C.base) P_B (C.base.canonicalMap f₀))))
        (example638Plus_forwardHom (presheafValue C.base) P_B (C.base.canonicalMap f₀)))
    (hcont_eval_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing C.base.P C.base
      let D : RationalLocData (presheafValue C.base) :=
        iteratedMinusDatum_B C.base.P C.base f₀
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (τ_preBiv : presheafValue (laurentOverlapDatum C.base f₀) ≃+*
      (↥(TateAlgebra₂ (presheafValue C.base)) ⧸
        TateAlgebra.bivariateOverlapIdeal (C.base.canonicalMap f₀)))
    (h_plus_compat : ∀ uplus : presheafValue (laurentPlusDatum C.base f₀),
      (bivariateOverlap_equiv_B₁₂gen (presheafValue C.base) (C.base.canonicalMap f₀))
          (τ_preBiv (restrictionMap (laurentPlusDatum C.base f₀)
              (laurentOverlapDatum C.base f₀)
              (laurentOverlap_subset_plus C.base f₀) uplus)) =
        LaurentCover.posLift (C.base.canonicalMap f₀)
          (laurentPlusBridge C.base.P C.base f₀ hNoeth_B hLocLift_B hA₀Noeth_B
            hA_complete_B hnoeth_B hcont_forward_B uplus))
    (h_minus_compat : ∀ uminus : presheafValue (laurentMinusDatum C.base f₀),
      (bivariateOverlap_equiv_B₁₂gen (presheafValue C.base) (C.base.canonicalMap f₀))
          (τ_preBiv (restrictionMap (laurentMinusDatum C.base f₀)
              (laurentOverlapDatum C.base f₀)
              (laurentOverlap_subset_minus C.base f₀) uminus)) =
        LaurentCover.negLift (C.base.canonicalMap f₀)
          (laurentMinusBridge C.base.P C.base f₀ hnoeth_B hcont_eval_B uminus))
    (_plus_section_refined : ∀
      (fV : ∀ D : { D // D ∈ C.refinedVCovers S f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S f₀ }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_plus : presheafValue (laurentPlusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.refinedVCovers S f₀ })
          (hD_plus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T
                         (laurentPlusDatum C.base f₀).s),
          restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D })
    (_minus_section_refined : ∀
      (fV : ∀ D : { D // D ∈ C.refinedVCovers S f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S f₀ }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_minus : presheafValue (laurentMinusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.refinedVCovers S f₀ })
          (hD_minus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentMinusDatum C.base f₀).T
                         (laurentMinusDatum C.base f₀).s),
          restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D })
    (hOverlap : ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S f₀ }, presheafValue D.1)
      (_hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S f₀ })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂))
      (u_plus : presheafValue (laurentPlusDatum C.base f₀))
      (u_minus : presheafValue (laurentMinusDatum C.base f₀))
      (_huplus : ∀ (D : { D // D ∈ C.refinedVCovers S f₀ })
        (hD_plus : rationalOpen D.1.T D.1.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T
                       (laurentPlusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D)
      (_huminus : ∀ (D : { D // D ∈ C.refinedVCovers S f₀ })
        (hD_minus : rationalOpen D.1.T D.1.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T
                       (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D),
      ∀ (D₃ : RationalLocData A)
        (h₃p : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
        (h₃m : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p u_plus =
          restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m u_minus) :
    ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S f₀ }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ C.refinedVCovers S f₀ },
        restrictionMap C.base D.1
          (C.refinedVCovers_subset_base S f₀ D.1 D.2) x = fV D := by
  refine C.hV_glue_refined_from_laurent_halves S f₀ hS_cover
    _plus_section_refined _minus_section_refined ?_ hOverlap
  intro u_plus u_minus hoverlap
  simpa using laurentCover_gluing_presheaf_via_primary C.base.P C.base f₀
    hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B hnoeth_B
    hcont_forward_B hcont_eval_B τ_preBiv h_plus_compat h_minus_compat
    (laurentPlus_subset C.base f₀) (laurentMinus_subset C.base f₀)
    u_plus u_minus hoverlap

/-- Concrete Lane A supplier, reduced from the abstract direct-per-E supplier
shape to:

1. the caller-ready overlap theorem `laurentCover_gluing_presheaf_via_primary`,
2. the inner plus/minus half-section builders, and
3. the overlap compatibility transfer `hOverlap`.

The only geometric input added here beyond
`hV_glue_refined_from_laurent_halves_via_primary` is the weakening
`refines_cover_of_refines_cover_per_E`. -/
theorem RationalCoveringData.lane_A_supplier_via_primary
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (C : RationalCoveringData A) (f₀ : A)
    [IsNoetherianRing C.base.P.A₀]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (hNoeth_B : IsNoetherianRing (presheafValue C.base))
    (hLocLift_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing C.base.P C.base
      HasLocLiftPowerBounded (presheafValue C.base))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing C.base.P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete C.base.P C.base).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue C.base)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue C.base)))
    (hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing C.base.P C.base
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing C.base.P C.base
      letI : HasLocLiftPowerBounded (presheafValue C.base) := hLocLift_B
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue C.base) :=
        presheafValue_pairOfDefinition_concrete C.base.P C.base
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue C.base) (C.base.canonicalMap f₀))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue C.base) P_B (C.base.canonicalMap f₀))))
        (example638Plus_forwardHom (presheafValue C.base) P_B (C.base.canonicalMap f₀)))
    (hcont_eval_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing C.base.P C.base
      let D : RationalLocData (presheafValue C.base) :=
        iteratedMinusDatum_B C.base.P C.base f₀
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (τ_preBiv : presheafValue (laurentOverlapDatum C.base f₀) ≃+*
      (↥(TateAlgebra₂ (presheafValue C.base)) ⧸
        TateAlgebra.bivariateOverlapIdeal (C.base.canonicalMap f₀)))
    (h_plus_compat : ∀ uplus : presheafValue (laurentPlusDatum C.base f₀),
      (bivariateOverlap_equiv_B₁₂gen (presheafValue C.base) (C.base.canonicalMap f₀))
          (τ_preBiv (restrictionMap (laurentPlusDatum C.base f₀)
              (laurentOverlapDatum C.base f₀)
              (laurentOverlap_subset_plus C.base f₀) uplus)) =
        LaurentCover.posLift (C.base.canonicalMap f₀)
          (laurentPlusBridge C.base.P C.base f₀ hNoeth_B hLocLift_B hA₀Noeth_B
            hA_complete_B hnoeth_B hcont_forward_B uplus))
    (h_minus_compat : ∀ uminus : presheafValue (laurentMinusDatum C.base f₀),
      (bivariateOverlap_equiv_B₁₂gen (presheafValue C.base) (C.base.canonicalMap f₀))
          (τ_preBiv (restrictionMap (laurentMinusDatum C.base f₀)
              (laurentOverlapDatum C.base f₀)
              (laurentOverlap_subset_minus C.base f₀) uminus)) =
        LaurentCover.negLift (C.base.canonicalMap f₀)
          (laurentMinusBridge C.base.P C.base f₀ hnoeth_B hcont_eval_B uminus))
    (S' : StandardCover A)
    (hS'_per_E : refines_cover_per_E C S'.elts)
    (_hS'_contain : refines_contain C S'.elts)
    (_plus_section_refined : ∀
      (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_plus : presheafValue (laurentPlusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.refinedVCovers S'.elts f₀ })
          (hD_plus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T
                         (laurentPlusDatum C.base f₀).s),
          restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D })
    (_minus_section_refined : ∀
      (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_minus : presheafValue (laurentMinusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.refinedVCovers S'.elts f₀ })
          (hD_minus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentMinusDatum C.base f₀).T
                         (laurentMinusDatum C.base f₀).s),
          restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D })
    (hOverlap : ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1)
      (_hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂))
      (u_plus : presheafValue (laurentPlusDatum C.base f₀))
      (u_minus : presheafValue (laurentMinusDatum C.base f₀))
      (_huplus : ∀ (D : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (hD_plus : rationalOpen D.1.T D.1.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T
                       (laurentPlusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D)
      (_huminus : ∀ (D : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (hD_minus : rationalOpen D.1.T D.1.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T
                       (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D),
      ∀ (D₃ : RationalLocData A)
        (h₃p : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
        (h₃m : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p u_plus =
          restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m u_minus) :
    ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ },
        restrictionMap C.base D.1
          (C.refinedVCovers_subset_base S'.elts f₀ D.1 D.2) x = fV D :=
  C.hV_glue_refined_from_laurent_halves_via_primary S'.elts f₀
    (refines_cover_of_refines_cover_per_E C S'.elts hS'_per_E)
    hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B hnoeth_B
    hcont_forward_B hcont_eval_B τ_preBiv h_plus_compat h_minus_compat
    _plus_section_refined _minus_section_refined hOverlap

omit [HasLocLiftPowerBounded A] in
/-- Canonical completeness proof for the completed presheaf value, in the
right-uniformity shape expected by the Example 6.38 bridge API. -/
theorem RationalCoveringData.canonical_complete_presheafValue
    (C : RationalCoveringData A) :
    @CompleteSpace (presheafValue C.base)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue C.base)) := by
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

omit [HasLocLiftPowerBounded A] in
/-- Canonical continuity proof for the minus-side Tate quotient map over
`B = presheafValue C.base`.

This is the geometric-reduction-layer analogue of the final-assembly helper:
the target datum is the iterated minus rational localization of the completed
base, so the continuity follows from the Tate-case topology comparison theorem. -/
theorem RationalCoveringData.canonical_hcont_eval
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (C : RationalCoveringData A) [IsNoetherianRing C.base.P.A₀]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)] (f₀ : A) :
    letI : IsTateRing (presheafValue C.base) :=
      presheafValue_isTateRing C.base.P C.base
    let D : RationalLocData (presheafValue C.base) :=
      iteratedMinusDatum_B C.base.P C.base f₀
    ∀ hb : TopologicalRing.IsPowerBounded (invS D),
      @Continuous _ _
        (TateAlgebra.quotientOneSubfXIdealTopology D.s)
        (inferInstance : TopologicalSpace (presheafValue D))
        (tateQuotientToPresheafHom D hb) := by
  dsimp
  intro hb
  letI : IsTateRing (presheafValue C.base) := presheafValue_isTateRing C.base.P C.base
  exact tateQuotientToPresheafHom_continuous_of_tate
    (iteratedMinusDatum_B C.base.P C.base f₀) hb

/-- Canonical-completion variant of `lane_A_supplier_via_primary`.

This keeps the theorem at the geometric-reduction layer while removing two
non-mathematical proof arguments from the caller boundary:

* completeness of `presheafValue C.base`;
* continuity of the minus-side quotient map over `presheafValue C.base`.

The remaining hypotheses are the genuine Lane A data, including the plus-side
continuity proof, overlap bridge, and half-cover section suppliers. -/
theorem RationalCoveringData.lane_A_supplier_via_primary_canonical
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (C : RationalCoveringData A) (f₀ : A)
    [IsNoetherianRing C.base.P.A₀]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (hNoeth_B : IsNoetherianRing (presheafValue C.base))
    (hLocLift_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing C.base.P C.base
      HasLocLiftPowerBounded (presheafValue C.base))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing C.base.P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete C.base.P C.base).A₀))
    (hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing C.base.P C.base
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing C.base.P C.base
      letI : HasLocLiftPowerBounded (presheafValue C.base) := hLocLift_B
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue C.base) :=
        presheafValue_pairOfDefinition_concrete C.base.P C.base
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue C.base) (C.base.canonicalMap f₀))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue C.base) P_B (C.base.canonicalMap f₀))))
        (example638Plus_forwardHom (presheafValue C.base) P_B (C.base.canonicalMap f₀)))
    (τ_preBiv : presheafValue (laurentOverlapDatum C.base f₀) ≃+*
      (↥(TateAlgebra₂ (presheafValue C.base)) ⧸
        TateAlgebra.bivariateOverlapIdeal (C.base.canonicalMap f₀)))
    (h_plus_compat : ∀ uplus : presheafValue (laurentPlusDatum C.base f₀),
      (bivariateOverlap_equiv_B₁₂gen (presheafValue C.base) (C.base.canonicalMap f₀))
          (τ_preBiv (restrictionMap (laurentPlusDatum C.base f₀)
              (laurentOverlapDatum C.base f₀)
              (laurentOverlap_subset_plus C.base f₀) uplus)) =
        LaurentCover.posLift (C.base.canonicalMap f₀)
          (laurentPlusBridge C.base.P C.base f₀ hNoeth_B hLocLift_B hA₀Noeth_B
            (RationalCoveringData.canonical_complete_presheafValue C)
            hnoeth_B hcont_forward_B uplus))
    (h_minus_compat : ∀ uminus : presheafValue (laurentMinusDatum C.base f₀),
      (bivariateOverlap_equiv_B₁₂gen (presheafValue C.base) (C.base.canonicalMap f₀))
          (τ_preBiv (restrictionMap (laurentMinusDatum C.base f₀)
              (laurentOverlapDatum C.base f₀)
              (laurentOverlap_subset_minus C.base f₀) uminus)) =
        LaurentCover.negLift (C.base.canonicalMap f₀)
          (laurentMinusBridge C.base.P C.base f₀ hnoeth_B
            (RationalCoveringData.canonical_hcont_eval C f₀) uminus))
    (S' : StandardCover A)
    (hS'_per_E : refines_cover_per_E C S'.elts)
    (_hS'_contain : refines_contain C S'.elts)
    (_plus_section_refined : ∀
      (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_plus : presheafValue (laurentPlusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.refinedVCovers S'.elts f₀ })
          (hD_plus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T
                         (laurentPlusDatum C.base f₀).s),
          restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D })
    (_minus_section_refined : ∀
      (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_minus : presheafValue (laurentMinusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.refinedVCovers S'.elts f₀ })
          (hD_minus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentMinusDatum C.base f₀).T
                         (laurentMinusDatum C.base f₀).s),
          restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D })
    (hOverlap : ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1)
      (_hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂))
      (u_plus : presheafValue (laurentPlusDatum C.base f₀))
      (u_minus : presheafValue (laurentMinusDatum C.base f₀))
      (_huplus : ∀ (D : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (hD_plus : rationalOpen D.1.T D.1.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T
                       (laurentPlusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D)
      (_huminus : ∀ (D : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (hD_minus : rationalOpen D.1.T D.1.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T
                       (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D),
      ∀ (D₃ : RationalLocData A)
        (h₃p : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
        (h₃m : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p u_plus =
          restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m u_minus) :
    ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ },
        restrictionMap C.base D.1
          (C.refinedVCovers_subset_base S'.elts f₀ D.1 D.2) x = fV D :=
  RationalCoveringData.lane_A_supplier_via_primary C f₀
    hNoeth_B hLocLift_B hA₀Noeth_B (RationalCoveringData.canonical_complete_presheafValue C)
    hnoeth_B hcont_forward_B (RationalCoveringData.canonical_hcont_eval C f₀)
    τ_preBiv h_plus_compat h_minus_compat S' hS'_per_E _hS'_contain
    _plus_section_refined _minus_section_refined hOverlap

/-! ### S-GEOM-ASM final assembly: refined V-cover Part-2 closure

The assembly theorem below composes the entire geometric reduction
chain into a single Part-2 wrapper, exposing the ATOMIC external
dependencies as a small named set of explicit hypotheses. The chain:

```
tateAcyclicity Part 2 (LaurentRefinement.lean:3737)
  ← tateAcyclicity_Part2_assembly                                ◆ this
       ← tateAcyclicity_Part2_via_refined_geometric_reduction    ◆ axiom-clean
            ← gluing_of_finer_rational                           ◆ Mathlib-style
            + hV_glue_refined                                  ← hV_glue_refined_from_laurent_halves
                ← refinedVCovers_plusMinus_dichotomy             ◆ axiom-clean
                + plus_section_refined  (S-GEOM-IND step on plus half)
                + minus_section_refined (S-GEOM-IND step on minus half)
                + hLaurentGlue          (Lane A: T-OV-1)
                + hOverlapFromCompat    (Lane A complement)
            + hE_sep_refined            (Lane B: T-IDEAL-2 / Cor 8.32)
            + hC_compat                 (caller's sheaf compat)
```

This puts all the cards on the table: the geometric lane delivers a
Part-2 closure as soon as Lane A (T-OV-1) and Lane B (T-IDEAL-2)
discharge — modulo the inner section builders, which are themselves
S-GEOM-IND output (recursion on `S.erase f₀` via the Wedhorn-redundancy
sub-cover transfer; this remains the third independent dependency).

We do NOT take `hZavyalov` directly here: the standard cover `S` is
supplied by the caller (typically obtained from
`RationalCoveringData.refines_by_standard_cover` with `hZavyalov`).
Caller-side composition is straightforward: invoke
`refines_by_standard_cover`, destructure to get `S` + `refines_cover` +
`refines_contain` + `refines_span_top`, then call this assembly. -/

/-- **Part-2 final assembly via refined V-cover** (S-GEOM-ASM, τ-route;
**superseded** by `tateAcyclicity_Part2_direct_per_E` for new code).
The geometric-reduction lane's terminal theorem via the τ-route:
assembles the entire chain from V-cover refinement through Laurent
gluing into the Part-2 shape required at `LaurentRefinement.lean:3737`.

**Prefer `tateAcyclicity_Part2_direct_per_E`** or its caller wrapper
`tateAcyclicity_Part2_via_hZavyalov_per_E_direct` for new downstream
code; the direct route consumes the canonical
`StandardCover.refines_cover_per_E` predicate and bypasses the
τ/Classical.choose bridge entirely.

External dependencies remaining at this entry point:
* `plus_section_refined` / `minus_section_refined` — inner `hV_glue` on
  each Laurent half. **S-GEOM-IND output** (recursion + Wedhorn-redundancy
  sub-cover transfer for `S.erase f₀`).
* `hLaurentGlue` — Lane A: discharged by `laurentCover_gluing_presheaf`
  post-T-OV-1 (`LaurentRefinement.lean:3173`).
* `hOverlap` — overlap-from-compat. Discharged by combining
  `laurentCover_gluing_presheaf` with the section-correctness
  hypotheses (post-T-OV-1).
* `hE_sep_refined` — Lane B: discharged by
  `productRestriction_injective_tate_via_prime_extension_closed`
  (`Cor832.lean:1581`) per-`E` post-T-IDEAL-2.
* `hC_compat` — caller's sheaf condition (always external).
* `hS_cover` / `hS_contain` — from the caller's
  `refines_by_standard_cover` invocation (with `hZavyalov`). -/
theorem RationalCoveringData.tateAcyclicity_Part2_assembly
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hS_cover : refines_cover C S)
    (hS_contain : refines_contain C S)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    -- S-GEOM-IND output on plus half (inner recursion):
    (plus_section_refined : ∀
      (fV : ∀ D : { D // D ∈ C.refinedVCovers S f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S f₀ }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_plus : presheafValue (laurentPlusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.refinedVCovers S f₀ })
          (hD_plus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T
                         (laurentPlusDatum C.base f₀).s),
          restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D })
    -- S-GEOM-IND output on minus half (inner recursion):
    (minus_section_refined : ∀
      (fV : ∀ D : { D // D ∈ C.refinedVCovers S f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S f₀ }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_minus : presheafValue (laurentMinusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.refinedVCovers S f₀ })
          (hD_minus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentMinusDatum C.base f₀).T
                         (laurentMinusDatum C.base f₀).s),
          restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D })
    -- Lane A: Laurent-cover gluing at f₀ on C.base (T-OV-1 content):
    (hLaurentGlue : ∀ (u_plus : presheafValue (laurentPlusDatum C.base f₀))
      (u_minus : presheafValue (laurentMinusDatum C.base f₀))
      (_hoverlap : ∀ (D₃ : RationalLocData A)
        (h₃p : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
        (h₃m : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p u_plus =
          restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m u_minus),
      ∃ x : presheafValue C.base,
        restrictionMap C.base (laurentPlusDatum C.base f₀)
          (laurentPlus_subset C.base f₀) x = u_plus ∧
        restrictionMap C.base (laurentMinusDatum C.base f₀)
          (laurentMinus_subset C.base f₀) x = u_minus)
    -- Lane A complement: overlap-from-compat (derivable post-T-OV-1):
    (hOverlap : ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S f₀ }, presheafValue D.1)
      (_hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S f₀ })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂))
      (u_plus : presheafValue (laurentPlusDatum C.base f₀))
      (u_minus : presheafValue (laurentMinusDatum C.base f₀))
      (_huplus : ∀ (D : { D // D ∈ C.refinedVCovers S f₀ })
        (hD_plus : rationalOpen D.1.T D.1.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T
                       (laurentPlusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D)
      (_huminus : ∀ (D : { D // D ∈ C.refinedVCovers S f₀ })
        (hD_minus : rationalOpen D.1.T D.1.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T
                       (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D),
      ∀ (D₃ : RationalLocData A)
        (h₃p : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
        (h₃m : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p u_plus =
          restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m u_minus)
    -- Lane B: cover-level separation (T-IDEAL-2 / Cor 8.32 content):
    (hE_sep_refined : ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (d : { D // D ∈ C.refinedVCovers S f₀ })
         (hd : C.standardCoverTau S hS_contain
                (C.refinedVCoversTau S f₀ d) = E),
        restrictionMap E.1 d.1
            (hd ▸ ((C.refinedVCoversTau_subset S f₀ d).trans
              (C.standardCoverTau_subset S hS_contain
                (C.refinedVCoversTau S f₀ d)))) a =
          restrictionMap E.1 d.1
            (hd ▸ ((C.refinedVCoversTau_subset S f₀ d).trans
              (C.standardCoverTau_subset S hS_contain
                (C.refinedVCoversTau S f₀ d)))) b) →
        a = b) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  C.tateAcyclicity_Part2_via_refined_geometric_reduction S f₀ hS_cover hS_contain
    fC hC_compat
    (C.hV_glue_refined_from_laurent_halves S f₀ hS_cover
      plus_section_refined minus_section_refined hLaurentGlue hOverlap)
    hE_sep_refined

/-! ### Lane B: per-piece separation wrapping

The `hE_sep_refined` hypothesis of `tateAcyclicity_Part2_assembly`
asks: for each `E ∈ C.covers`, if `a, b ∈ presheafValue E.1` agree on
every refined V-piece mapping to `E` (via `τ_full = standardCoverTau ∘
refinedVCoversTau`), then `a = b`.

This is equivalent to per-`E` injectivity of the product-restriction
from `presheafValue E.1` to `∏_d presheafValue d.1` (ranging over `d`
with `τ_full d = E`). The caller can discharge via
`productRestriction_injective_tate_via_prime_extension_closed`
(`Cor832.lean:1581`) applied at each `E` once a local `RationalCoveringData`
with `base = E.1` is produced.

Below we expose the MECHANICAL reduction `hE_sep ↔ per-E injectivity`
via `RingHom.map_sub`. This peels off the additive-group shift so the
caller only has to supply per-E injectivity, not the coincidence-form
`a = b if restrictions agree`. -/

/-- **Lane B Step 1**: mechanical reduction from the `hE_sep`-shape to
a per-`E` injectivity statement. The LHS hypothesis says each `E` has
injective product-restriction to its τ-preimage d's (= 0 in →
`x = 0`); the RHS conclusion is the `a = b` form used by
`tateAcyclicity_Part2_assembly`. Proof: shift `x := a - b`, use
`map_sub` on `restrictionMapHom` + `sub_eq_zero`. -/
theorem RationalCoveringData.hE_sep_refined_of_per_E_injectivity
    [DecidableEq A]
    (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hS_contain : refines_contain C S)
    (per_E_inj : ∀ (E : { E // E ∈ C.covers }) (x : presheafValue E.1),
      (∀ (d : { D // D ∈ C.refinedVCovers S f₀ })
         (hd : C.standardCoverTau S hS_contain
                (C.refinedVCoversTau S f₀ d) = E),
        restrictionMap E.1 d.1
            (hd ▸ ((C.refinedVCoversTau_subset S f₀ d).trans
              (C.standardCoverTau_subset S hS_contain
                (C.refinedVCoversTau S f₀ d)))) x = 0) →
      x = 0) :
    ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (d : { D // D ∈ C.refinedVCovers S f₀ })
         (hd : C.standardCoverTau S hS_contain
                (C.refinedVCoversTau S f₀ d) = E),
        restrictionMap E.1 d.1
            (hd ▸ ((C.refinedVCoversTau_subset S f₀ d).trans
              (C.standardCoverTau_subset S hS_contain
                (C.refinedVCoversTau S f₀ d)))) a =
          restrictionMap E.1 d.1
            (hd ▸ ((C.refinedVCoversTau_subset S f₀ d).trans
              (C.standardCoverTau_subset S hS_contain
                (C.refinedVCoversTau S f₀ d)))) b) →
        a = b := by
  intro E a b hab
  -- `a - b` restricts to zero on every `d` (via `map_sub` + `sub_eq_zero`).
  have h_sub : a - b = 0 := by
    apply per_E_inj E (a - b)
    intro d hd
    have eq := hab d hd
    -- Normalize the goal to `restrictionMapHom` form (function coercion of
    -- `restrictionMap = restrictionMapHom`), then apply `RingHom.map_sub`
    -- and `sub_eq_zero`.
    change (restrictionMapHom E.1 d.1
        (hd ▸ ((C.refinedVCoversTau_subset S f₀ d).trans
          (C.standardCoverTau_subset S hS_contain
            (C.refinedVCoversTau S f₀ d))))) (a - b) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr eq
  exact sub_eq_zero.mp h_sub

/-! ### Lane B Step 2 (documentation): per-E injectivity via Cor 8.32

The `per_E_inj` hypothesis of
`hE_sep_refined_of_per_E_injectivity` is discharged per-E by
`productRestriction_injective_tate_via_prime_extension_closed`
(`Cor832.lean:1581`) applied to a `RationalCoveringData A` with `base = E.1`
whose `covers` include (at minimum) the d's mapping to E.

**Data required** per-E (to invoke Cor832 at E):
* `PairOfDefinition A` (the ambient pair of definition, reused).
* `[IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]`
  — all inherited from the outer theorem's typeclass bundle.
* `[IsNoetherianRing P.A₀]` — outer-level.
* `[IsNoetherianRing (locSubring E.1.P E.1.T E.1.s)]` — per-E Noetherian,
  usually via `E.1.P` = `C.base.P` (same `PairOfDefinition`).
* `hAplus_le_A₀ : (A⁺ : Set A) ⊆ E.1.P.A₀` — per-E.
* `hcanonicalMap_cont : Continuous E.1.canonicalMap` — per-E.
* `h_closed_nonOpen : prime-extension closedness at `E.1` — per-E.
* `hcover_at_E : ∀ v ∈ rationalOpen E.1.T E.1.s, ∃ d ∈ refinedVCovers S f₀,
  τ_full d = E ∧ v ∈ rationalOpen d.1.T d.1.s` — this is the geometric
  condition that E is actually covered by its τ-preimages in the refined
  V-cover. In the Wedhorn standard-cover construction, this holds via
  the `refines_by_standard_cover` invariants + `refinedVCovers_covers`;
  stated as an explicit hypothesis here.

We DO NOT package Step 2 as a single theorem here because the per-E
`RationalCoveringData` construction requires filtering `refinedVCovers` to
the d's mapping to E, which needs a `Classical.decEq (RationalLocData A)`
setup and `Finset.filter` plumbing that's cleaner to leave at the
caller-site. See the documentation block below the T-ACYC-PART2 wrapper
for a compositional sketch. -/

/-! ### Lane B Step 2: per-E local covering construction and Cor832 wrapper

Given the refined V-cover and `refines_contain`-backed τ chain, each
`E ∈ C.covers` has a collection of "its" refined V-pieces: those
`d ∈ refinedVCovers S f₀` with `τ_full d = E` (where `τ_full =
standardCoverTau ∘ refinedVCoversTau`). Packaged as a `Finset`
(`refinedVCovers_at`), these form the candidate covers of a per-E
`RationalCoveringData A` with `base = E.1`.

The per-E `RationalCoveringData` is a valid one iff its covers
geometrically cover `E.1`'s rational open. This `hcover_at_E`
property is an **explicit hypothesis** at this level; in the Wedhorn
standard-cover construction (`refines_by_standard_cover` +
`refinedVCovers_covers`) it holds via the choice of `S`, but we don't
bake that derivation into Step 2 itself since it involves a
Finset-choice argument specific to the caller's S-provenance.

With the per-E `RationalCoveringData` in hand, invoking
`productRestriction_injective_tate_via_prime_extension_closed`
(`Cor832.lean:1581`) at each `E` yields per-E separation, which Step 1
converts to the `hE_sep_refined`-shape expected by the Part-2 assembly. -/

/-- **Per-E filter of refined V-pieces**. Selects from `refinedVCovers
S f₀` only those pieces `d` whose τ-image
`standardCoverTau (refinedVCoversTau d)` equals the given `E ∈ C.covers`.

Implementation: `attach` + `filter` (using `Classical` decidability)
+ `image` back to `RationalLocData A`. Used as the covers field of the
per-E `RationalCoveringData` below. -/
noncomputable def RationalCoveringData.refinedVCovers_at
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hS_contain : refines_contain C S)
    (E : { E // E ∈ C.covers }) : Finset (RationalLocData A) :=
  letI : DecidableEq (RationalLocData A) := Classical.decEq _
  letI : DecidableEq { E' // E' ∈ C.covers } := Classical.decEq _
  (C.refinedVCovers S f₀).attach
    |>.filter (fun d =>
      C.standardCoverTau S hS_contain (C.refinedVCoversTau S f₀ d) = E)
    |>.image Subtype.val

/-- Membership in `refinedVCovers_at E`: a `RationalLocData A` is in
the per-E filter iff it lies in `refinedVCovers S f₀` AND its
τ-image equals `E`. -/
theorem RationalCoveringData.mem_refinedVCovers_at
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hS_contain : refines_contain C S)
    (E : { E // E ∈ C.covers }) (D : RationalLocData A) :
    D ∈ C.refinedVCovers_at S f₀ hS_contain E ↔
      ∃ hD : D ∈ C.refinedVCovers S f₀,
        C.standardCoverTau S hS_contain
          (C.refinedVCoversTau S f₀ ⟨D, hD⟩) = E := by
  letI : DecidableEq (RationalLocData A) := Classical.decEq _
  letI : DecidableEq { E' // E' ∈ C.covers } := Classical.decEq _
  unfold RationalCoveringData.refinedVCovers_at
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨d, hd_eq, rfl⟩
    exact ⟨d.2, hd_eq⟩
  · rintro ⟨hD, hτ⟩
    exact ⟨⟨D, hD⟩, hτ, rfl⟩

/-- **Per-E subset-to-base**. Each refined V-piece mapping to `E`
has its rational open contained in `E.1`'s rational open, via the τ
composition `refinedVCoversTau_subset` + `standardCoverTau_subset`. -/
theorem RationalCoveringData.refinedVCovers_at_subset_base
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hS_contain : refines_contain C S)
    (E : { E // E ∈ C.covers })
    (D : RationalLocData A) (hD : D ∈ C.refinedVCovers_at S f₀ hS_contain E) :
    rationalOpen D.T D.s ⊆ rationalOpen E.1.T E.1.s := by
  obtain ⟨hD_refined, hτ⟩ := (C.mem_refinedVCovers_at S f₀ hS_contain E D).mp hD
  -- Chain: D ⊆ refinedVCoversTau(⟨D,hD_refined⟩) ⊆ standardCoverTau(...) = E.
  have h1 : rationalOpen D.T D.s ⊆
      rationalOpen (C.refinedVCoversTau S f₀ ⟨D, hD_refined⟩).1.T
                   (C.refinedVCoversTau S f₀ ⟨D, hD_refined⟩).1.s :=
    C.refinedVCoversTau_subset S f₀ ⟨D, hD_refined⟩
  have h2 : rationalOpen (C.refinedVCoversTau S f₀ ⟨D, hD_refined⟩).1.T
                         (C.refinedVCoversTau S f₀ ⟨D, hD_refined⟩).1.s ⊆
            rationalOpen (C.standardCoverTau S hS_contain
                            (C.refinedVCoversTau S f₀ ⟨D, hD_refined⟩)).1.T
                         (C.standardCoverTau S hS_contain
                            (C.refinedVCoversTau S f₀ ⟨D, hD_refined⟩)).1.s :=
    C.standardCoverTau_subset S hS_contain _
  have h3 : rationalOpen (C.standardCoverTau S hS_contain
                            (C.refinedVCoversTau S f₀ ⟨D, hD_refined⟩)).1.T
                         (C.standardCoverTau S hS_contain
                            (C.refinedVCoversTau S f₀ ⟨D, hD_refined⟩)).1.s =
            rationalOpen E.1.T E.1.s := by rw [hτ]
  exact h1.trans (h2.trans h3.le)

/-- **Per-E local `RationalCoveringData`**. Given `hcover_at_E` (the
covering property that `E.1`'s rational open is covered by its τ-preimage
refined V-pieces), builds a `RationalCoveringData A` with `base = E.1` and
covers = `refinedVCovers_at S f₀ hS_contain E`.

Used as the per-E target of
`productRestriction_injective_tate_via_prime_extension_closed`
(`Cor832.lean:1581`). -/
noncomputable def RationalCoveringData.refinedVCovers_at_asRationalCoveringData
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hS_contain : refines_contain C S)
    (E : { E // E ∈ C.covers })
    (hcover_at_E : ∀ v ∈ rationalOpen E.1.T E.1.s,
      ∃ D ∈ C.refinedVCovers_at S f₀ hS_contain E,
        v ∈ rationalOpen D.T D.s) :
    RationalCoveringData A where
  base := E.1
  covers := C.refinedVCovers_at S f₀ hS_contain E
  hsubset D hD := C.refinedVCovers_at_subset_base S f₀ hS_contain E D hD
  hcover := hcover_at_E

/-- **Lane B Step 2**: reduction from `per_E_inj` (the Lane B Step 1
hypothesis) to a per-E Cor832-shaped separation hypothesis on the
local `RationalCoveringData`.

Given `hcover_at_E` per-E and the per-E Cor832 output, produces the
`per_E_inj` statement consumed by `hE_sep_refined_of_per_E_injectivity`.

Composition with Step 1 gives the full Lane B: `hE_sep_refined` reduces
to `hcover_at_E` (explicit hypothesis, derivable from the
Wedhorn-refinement provenance) + per-E Cor832 output (discharged via
`productRestriction_injective_tate_via_prime_extension_closed` at each
`refinedVCovers_at_asRationalCoveringData E hcover_at_E`). -/
theorem RationalCoveringData.per_E_inj_of_per_E_cor832
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hS_contain : refines_contain C S)
    (hcover_at_E : ∀ (E : { E // E ∈ C.covers }),
      ∀ v ∈ rationalOpen E.1.T E.1.s,
        ∃ D ∈ C.refinedVCovers_at S f₀ hS_contain E,
          v ∈ rationalOpen D.T D.s)
    (hCor832_at_E : ∀ (E : { E // E ∈ C.covers })
      (x : presheafValue (C.refinedVCovers_at_asRationalCoveringData S f₀
              hS_contain E (hcover_at_E E)).base),
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.refinedVCovers_at_asRationalCoveringData S f₀
                      hS_contain E (hcover_at_E E)).covers),
        restrictionMap (C.refinedVCovers_at_asRationalCoveringData S f₀
                          hS_contain E (hcover_at_E E)).base D
            ((C.refinedVCovers_at_asRationalCoveringData S f₀
                hS_contain E (hcover_at_E E)).hsubset D hD) x = 0) →
      x = 0) :
    ∀ (E : { E // E ∈ C.covers }) (x : presheafValue E.1),
      (∀ (d : { D // D ∈ C.refinedVCovers S f₀ })
         (hd : C.standardCoverTau S hS_contain
                (C.refinedVCoversTau S f₀ d) = E),
        restrictionMap E.1 d.1
            (hd ▸ ((C.refinedVCoversTau_subset S f₀ d).trans
              (C.standardCoverTau_subset S hS_contain
                (C.refinedVCoversTau S f₀ d)))) x = 0) →
      x = 0 := by
  intro E x hx
  -- Transfer `x : presheafValue E.1` to the per-E RationalCoveringData's base
  -- (which is also E.1 by construction).
  have h_base_eq :
      (C.refinedVCovers_at_asRationalCoveringData S f₀ hS_contain E
         (hcover_at_E E)).base = E.1 := rfl
  -- Apply hCor832_at_E: x = 0 if restriction to each D ∈ per_E covers is 0.
  apply hCor832_at_E E x
  intro D hD
  -- Unpack hD to get the membership in `refinedVCovers` and the τ-equation.
  obtain ⟨hD_refined, hτ⟩ := (C.mem_refinedVCovers_at S f₀ hS_contain E D).mp hD
  -- Apply hx at ⟨D, hD_refined⟩ with hτ. The restrictionMap subset-proof
  -- differs between `hx` (τ-path) and the target (per-E path), but
  -- `restrictionMap`'s subset argument is Prop-valued, so proof
  -- irrelevance identifies the two restrictionMap values.
  exact hx ⟨D, hD_refined⟩ hτ

/-! ### Lane B Step 3: direct per-E covering from canonical `refines_cover_per_E`

The canonical per-E precise-covering predicate `refines_cover_per_E` is
defined in `StandardCover.lean` (alongside `refines_cover`,
`refines_contain`, `refines_span_top`). It is the natural per-E
strengthening that the Wedhorn/Hübner standard-cover construction
produces, tracking the per-`f`-to-per-`E` assignment.

The `hcover_at_E` hypothesis of Lane B Step 2
(`per_E_inj_of_per_E_cor832`) asserts per-E geometric coverage by
τ-preimage refined pieces. The τ-preimage membership goes through two
`Classical.choose` layers (`refinedVCoversTau` and `standardCoverTau`),
which makes directly deriving `hcover_at_E` from simpler hypotheses
(like `refines_cover` + `refines_contain`) awkward.

We therefore provide an alternative route that **bypasses the
Classical.choose τ chain**: given the canonical `refines_cover_per_E`
predicate from `StandardCover.lean`, we build a direct per-E
`RationalCoveringData` `per_E_local_covering`. The construction uses
`Finset.filter` on `S` to select f's with `plus-piece-at-f ⊆ E`, then
takes plus- and minus-refined-at-f for those f's.

The caller obtains `refines_cover_per_E` from
`StandardCover.RationalCoveringData.refines_by_standard_cover_per_E` (the
strengthened Wedhorn/Hübner refinement theorem), which consumes a
strengthened existence hypothesis `hZavyalov_per_E`.

The downstream wiring — showing that `per_E_local_covering`'s separation
via Cor 8.32 implies the τ-based `per_E_inj` consumed by Step 2 — is
the remaining Lane B gap; it requires Classical.choose reasoning to
identify the τ-image of plus/minus-refined-at-f with the user-specified
E. We isolate this gap as a named bridge hypothesis / documented future
work so the direct per-E `RationalCoveringData` construction itself is
usable by callers who have their own Cor832-at-E discharge. -/

/-- **Direct per-E local `RationalCoveringData`** (no τ-indirection).
Given `refines_cover_per_E`, builds a per-E `RationalCoveringData A` with
`base = E.1` and covers = plus/minus-refined-at-f for f ∈ S whose
plus-piece is contained in E. The filter on `S` uses `Classical.dec`
for the subset-predicate.

This `RationalCoveringData` is directly suitable for Cor 8.32 per-E
application; the caller invokes
`productRestriction_injective_tate_via_prime_extension_closed` at
this covering to get `presheafValue E.1`-level separation. -/
noncomputable def RationalCoveringData.per_E_local_covering
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (E : { E // E ∈ C.covers })
    (hprecise : refines_cover_per_E C S) :
    RationalCoveringData A :=
  letI : DecidableEq (RationalLocData A) := Classical.decEq _
  letI : DecidablePred (fun f : A =>
    rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen E.1.T E.1.s) :=
    fun _ => Classical.propDecidable _
  { base := E.1
    covers := (S.filter (fun f =>
                rationalOpen (insert f C.base.T) C.base.s ⊆
                  rationalOpen E.1.T E.1.s)).image
                (fun f => laurentPlusDatum (C.plusDatum f) f₀) ∪
              (S.filter (fun f =>
                rationalOpen (insert f C.base.T) C.base.s ⊆
                  rationalOpen E.1.T E.1.s)).image
                (fun f => laurentMinusDatum (C.plusDatum f) f₀)
    hsubset := by
      intro D hD
      rw [Finset.mem_union] at hD
      rcases hD with hD | hD
      all_goals
        (rw [Finset.mem_image] at hD
         obtain ⟨f, hf_in_filter, rfl⟩ := hD
         simp only [Finset.mem_filter] at hf_in_filter
         have h_plus_in_E : rationalOpen (insert f C.base.T) C.base.s ⊆
                            rationalOpen E.1.T E.1.s := hf_in_filter.2
         have h_plus_piece_eq : rationalOpen (C.plusDatum f).T (C.plusDatum f).s =
                                rationalOpen (insert f C.base.T) C.base.s :=
           C.rationalOpen_plusDatum_eq_insert f)
      · exact (laurentPlus_subset (C.plusDatum f) f₀).trans
          (h_plus_piece_eq ▸ h_plus_in_E)
      · exact (laurentMinus_subset (C.plusDatum f) f₀).trans
          (h_plus_piece_eq ▸ h_plus_in_E)
    hcover := by
      intro v hv
      -- Apply the canonical predicate at E: `hprecise E.1 E.2 v hv` gives the f.
      obtain ⟨f, hf, hv_in_plus, h_plus_in_E⟩ := hprecise E.1 E.2 v hv
      have hv_pd : v ∈ rationalOpen (C.plusDatum f).T (C.plusDatum f).s :=
        (C.rationalOpen_plusDatum_eq_insert f).symm ▸ hv_in_plus
      rcases laurentCover_covers (C.plusDatum f) f₀ v hv_pd with hv_plus | hv_minus
      · refine ⟨laurentPlusDatum (C.plusDatum f) f₀, ?_, hv_plus⟩
        rw [Finset.mem_union]; left
        rw [Finset.mem_image]
        refine ⟨f, ?_, rfl⟩
        simp only [Finset.mem_filter]
        exact ⟨hf, h_plus_in_E⟩
      · refine ⟨laurentMinusDatum (C.plusDatum f) f₀, ?_, hv_minus⟩
        rw [Finset.mem_union]; right
        rw [Finset.mem_image]
        refine ⟨f, ?_, rfl⟩
        simp only [Finset.mem_filter]
        exact ⟨hf, h_plus_in_E⟩ }

/-- Membership in the direct per-E local covering: a `RationalLocData A`
is in `(per_E_local_covering E hprecise).covers` iff it is plus- or
minus-refined-at-f for some f ∈ S with plus-piece-at-f ⊆ E. -/
theorem RationalCoveringData.mem_per_E_local_covering_covers
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (E : { E // E ∈ C.covers })
    (hprecise : refines_cover_per_E C S)
    (D : RationalLocData A) :
    D ∈ (C.per_E_local_covering S f₀ E hprecise).covers ↔
      (∃ f ∈ S, rationalOpen (insert f C.base.T) C.base.s ⊆
          rationalOpen E.1.T E.1.s ∧
        (laurentPlusDatum (C.plusDatum f) f₀ = D ∨
         laurentMinusDatum (C.plusDatum f) f₀ = D)) := by
  letI : DecidableEq (RationalLocData A) := Classical.decEq _
  letI : DecidablePred (fun f : A =>
    rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen E.1.T E.1.s) :=
    fun _ => Classical.propDecidable _
  unfold RationalCoveringData.per_E_local_covering
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro (⟨f, ⟨hf, h_in_E⟩, rfl⟩ | ⟨f, ⟨hf, h_in_E⟩, rfl⟩)
    · exact ⟨f, hf, h_in_E, Or.inl rfl⟩
    · exact ⟨f, hf, h_in_E, Or.inr rfl⟩
  · rintro ⟨f, hf, h_in_E, hD | hD⟩
    · exact Or.inl ⟨f, ⟨hf, h_in_E⟩, hD⟩
    · exact Or.inr ⟨f, ⟨hf, h_in_E⟩, hD⟩

/-- The direct per-E local covering is nonempty whenever the cover piece
`E` itself has a point.

This is the exact side condition needed to apply Cor 8.32-style
nonempty-cover separation to `per_E_local_covering`: choose a point of
`E`, use `refines_cover_per_E` to find a standard-cover generator whose
plus-piece targets `E`, then use the two-piece Laurent cover of that
plus-piece. -/
theorem RationalCoveringData.per_E_local_covering_nonempty_of_rationalOpen_nonempty
    [DecidableEq A] (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (E : { E // E ∈ C.covers })
    (hprecise : refines_cover_per_E C S)
    (hE_nonempty : (rationalOpen E.1.T E.1.s).Nonempty) :
    (C.per_E_local_covering S f₀ E hprecise).covers.Nonempty := by
  obtain ⟨v, hvE⟩ := hE_nonempty
  obtain ⟨f, hf, hv_in_plus, h_plus_in_E⟩ := hprecise E.1 E.2 v hvE
  have hv_pd : v ∈ rationalOpen (C.plusDatum f).T (C.plusDatum f).s :=
    (C.rationalOpen_plusDatum_eq_insert f).symm ▸ hv_in_plus
  rcases laurentCover_covers (C.plusDatum f) f₀ v hv_pd with hv_plus | hv_minus
  · refine ⟨laurentPlusDatum (C.plusDatum f) f₀, ?_⟩
    rw [(C.mem_per_E_local_covering_covers S f₀ E hprecise
      (laurentPlusDatum (C.plusDatum f) f₀))]
    exact ⟨f, hf, h_plus_in_E, Or.inl rfl⟩
  · refine ⟨laurentMinusDatum (C.plusDatum f) f₀, ?_⟩
    rw [(C.mem_per_E_local_covering_covers S f₀ E hprecise
      (laurentMinusDatum (C.plusDatum f) f₀))]
    exact ⟨f, hf, h_plus_in_E, Or.inr rfl⟩

/-! ### Lane B Step 3 documentation: wiring the direct per-E covering

The `per_E_local_covering` above produces a `RationalCoveringData A` with
`base = E.1` and a concrete `covers` field (no `Classical.choose τ`).
Callers invoke
`productRestriction_injective_tate_via_prime_extension_closed`
(`Cor832.lean:1581`) on this per-E covering to obtain:

```
per_E_inj_direct : ∀ E : { E // E ∈ C.covers }, ∀ x : presheafValue E.1,
  (∀ (D : RationalLocData A) (hD : D ∈ (per_E_local_covering C S f₀ E _).covers),
    restrictionMap E.1 D ((per_E_local_covering ...).hsubset D hD) x = 0) →
  x = 0
```

**Gap to the τ-based `per_E_inj`** (consumed by
`hE_sep_refined_of_per_E_injectivity`): the τ-based form uses
`refinedVCovers_at`-membership, which goes through Classical.choose
layers that `per_E_local_covering` bypasses. The bridge would show:
every `d` with `τ_full d = E` (= refinedVCovers_at E member) lies in
`per_E_local_covering`'s covers (or vice versa). Since both are
subsets of `refinedVCovers S f₀`, the bridge turns on whether the
Classical.choose τ-image of a plus/minus-refined-at-f coincides with
the `refines_cover_per_E`-assigned E.

For callers who construct their standard cover S via
`refines_by_standard_cover` with the Wedhorn 8.34 / Hübner 3.8
explicit per-f→per-E assignment (tracked internally), the bridge holds
structurally, but formalising it requires either (i) an injectivity
argument for the `f ↦ plus-refined-at-f` map (to pin down
`refinedVCoversTau`'s Classical.choose), or (ii) reformulating the
Part-2 assembly to use the direct per-E covering instead of the
τ-based one. Both are possible but deferred.

**Current lane status**:
* Direct per-E `RationalCoveringData` construction: ◆ AVAILABLE (axiom-clean).
* Bridge to τ-based Lane B Step 2: **GAP**, documented.
* Callers with an independent Cor832-at-E source (e.g., from an
  alternative refinement API) can use `per_E_local_covering` directly
  without going through `refinedVCovers_at`.

The predicate `refines_cover_per_E` is exposed here as a reusable
statement in the geometric-reduction lane. A downstream ticket in
`StandardCover.lean` can strengthen `refines_by_standard_cover`'s
output to produce `refines_cover_per_E`, closing the geometric half
of Lane B (modulo the Cor832-at-E per-piece discharge, which is the
T-IDEAL-2 content). -/

/-! ### Lane B complete — direct per-E Part-2 assembly (no τ/Classical.choose bridge)

A Part-2 wrapper that **directly consumes** the `refines_cover_per_E`
predicate and its companion `per_E_local_covering` / `hE_sep_direct`
stack, bypassing the τ/Classical.choose bridge required by the existing
`tateAcyclicity_Part2_assembly`'s τ-based hE_sep.

**Fallback inside**: the proof still uses `Classical.choose` on
`refines_contain` to pick a canonical target `E_D ∈ C.covers` for each
refined V-piece `D`, but the choice is **entirely internal** and
reconciled at the Part-2 output via `hC_compat`. No external
`refinedVCoversTau`/`standardCoverTau` compatibility hypotheses needed.

**Inputs vs. `tateAcyclicity_Part2_assembly`**:
* Direct variant takes `refines_cover_per_E` + `refines_contain`
  (both from `StandardCover.refines_by_standard_cover_per_E`).
* Direct variant takes `hE_sep_direct` (per_E_local_covering-based,
  matches Cor 8.32 at E output shape, no τ).
* Direct variant takes `hV_glue_refined` as before (Lane A content).
* Direct variant takes `hC_compat` as before.
* **No** τ-based `hE_sep_refined` (the τ/Classical.choose bridge).

**Proof structure**:
1. For each refined V-piece `D`, Classical.choose a target
   `E_D ∈ C.covers` containing `D`'s plus-piece-at-f_D (via
   `refines_contain`). Define `fV D := restrictionMap E_D D (fC E_D)`.
2. `fV` is compat via `hC_compat` (restrictions of `fC` at different E's
   agree on overlaps).
3. `hV_glue_refined` applied to `fV` gives `x : presheafValue C.base`.
4. For each `E ∈ C.covers`, invoke `hE_sep_direct E` on
   `a = restrictionMap C.base E x` and `b = fC E`. For each
   `D ∈ per_E_local_covering E.covers`, show agreement:
   - LHS (via `restrictionMap_comp`) = `restrictionMap C.base D x`
     = `fV D` (by `hV_glue_refined` correctness).
   - `fV D = restrictionMap E_D D (fC E_D)`; by `hC_compat` at
     `(E_D, E, D)` = `restrictionMap E D (fC E)` = RHS. ✓

No τ compatibility is required because each step closes via
`hC_compat` or `restrictionMap_comp`, both Prop-irrelevant on their
subset-proof arguments. -/

/-- **`tateAcyclicity` Part 2 via direct per-E covering** — the Lane B
closure consuming the canonical `refines_cover_per_E` predicate from
`StandardCover.lean` (via `refines_by_standard_cover_per_E`) without any
τ/Classical.choose bridge to the existing τ-based assembly.

Internal `Classical.choose` on `refines_contain` is used to define the
fV-building target per refined piece; reconciled at the Part-2 output
via `hC_compat`. -/
theorem RationalCoveringData.tateAcyclicity_Part2_direct_per_E
    [HasLocLiftPowerBounded A]
    [DecidableEq A]
    (C : RationalCoveringData A) (S : Finset A) (f₀ : A)
    (hS_per_E : refines_cover_per_E C S)
    (hS_contain : refines_contain C S)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (hV_glue_refined : ∀
      (fV : ∀ D : { D // D ∈ C.refinedVCovers S f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S f₀ }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ C.refinedVCovers S f₀ },
        restrictionMap C.base D.1
          (C.refinedVCovers_subset_base S f₀ D.1 D.2) x = fV D)
    (hE_sep_direct : ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S f₀ E hS_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S f₀ E hS_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S f₀ E hS_per_E).hsubset D hD) b) →
        a = b) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  classical
  -- Step 1: Extract f per refined V-piece D via Classical.choose on
  -- `mem_refinedVCovers`, then pick target E_D via Classical.choose on
  -- `refines_contain` at f.
  have D_f_exists : ∀ D : { D // D ∈ C.refinedVCovers S f₀ },
      ∃ f, f ∈ S ∧
        (laurentPlusDatum (C.plusDatum f) f₀ = D.1 ∨
         laurentMinusDatum (C.plusDatum f) f₀ = D.1) := fun D => by
    rcases (C.mem_refinedVCovers S f₀).mp D.2 with ⟨f, hf, hf_eq⟩ | ⟨f, hf, hf_eq⟩
    · exact ⟨f, hf, Or.inl hf_eq⟩
    · exact ⟨f, hf, Or.inr hf_eq⟩
  let D_f : ∀ D : { D // D ∈ C.refinedVCovers S f₀ }, A := fun D =>
    Classical.choose (D_f_exists D)
  have D_f_mem_S : ∀ D, D_f D ∈ S := fun D => (Classical.choose_spec (D_f_exists D)).1
  have D_f_eq : ∀ D, laurentPlusDatum (C.plusDatum (D_f D)) f₀ = D.1 ∨
      laurentMinusDatum (C.plusDatum (D_f D)) f₀ = D.1 :=
    fun D => (Classical.choose_spec (D_f_exists D)).2
  -- D.1's rational open is contained in plus-piece-at-(D_f D).
  have D_sub_plusPiece : ∀ D : { D // D ∈ C.refinedVCovers S f₀ },
      rationalOpen D.1.T D.1.s ⊆
        rationalOpen (C.plusDatum (D_f D)).T (C.plusDatum (D_f D)).s := fun D => by
    rcases D_f_eq D with heq | heq
    · rw [← heq]; exact laurentPlus_subset (C.plusDatum (D_f D)) f₀
    · rw [← heq]; exact laurentMinus_subset (C.plusDatum (D_f D)) f₀
  have D_sub_plusPiece_insert : ∀ D : { D // D ∈ C.refinedVCovers S f₀ },
      rationalOpen D.1.T D.1.s ⊆
        rationalOpen (insert (D_f D) C.base.T) C.base.s := fun D =>
    (D_sub_plusPiece D).trans (C.rationalOpen_plusDatum_eq_insert (D_f D)).le
  -- Classical.choose target E via refines_contain.
  let D_E : ∀ D : { D // D ∈ C.refinedVCovers S f₀ }, RationalLocData A := fun D =>
    Classical.choose (hS_contain (D_f D) (D_f_mem_S D))
  have D_E_mem : ∀ D, D_E D ∈ C.covers := fun D =>
    (Classical.choose_spec (hS_contain (D_f D) (D_f_mem_S D))).1
  have D_E_sub : ∀ D,
      rationalOpen (insert (D_f D) C.base.T) C.base.s ⊆
        rationalOpen (D_E D).T (D_E D).s := fun D =>
    (Classical.choose_spec (hS_contain (D_f D) (D_f_mem_S D))).2
  -- Composite: D ⊆ D_E D.
  have D_sub_DE : ∀ D, rationalOpen D.1.T D.1.s ⊆ rationalOpen (D_E D).T (D_E D).s :=
    fun D => (D_sub_plusPiece_insert D).trans (D_E_sub D)
  -- Step 2: Build fV.
  let fV : ∀ D : { D // D ∈ C.refinedVCovers S f₀ }, presheafValue D.1 := fun D =>
    restrictionMap (D_E D) D.1 (D_sub_DE D) (fC ⟨D_E D, D_E_mem D⟩)
  -- Step 3: fV is compat via hC_compat.
  have fV_compat : ∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S f₀ })
      (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂) := by
    intro D₁ D₂ D₃ h₃₁ h₃₂
    -- Unfold fV D₁, fV D₂, use restrictionMap_comp to peel off, apply hC_compat.
    have hcomp1 := restrictionMap_comp (D_E D₁) D₁.1 D₃ (D_sub_DE D₁) h₃₁
    have hcomp2 := restrictionMap_comp (D_E D₂) D₂.1 D₃ (D_sub_DE D₂) h₃₂
    have step1 : restrictionMap D₁.1 D₃ h₃₁ (fV D₁) =
        restrictionMap (D_E D₁) D₃ (h₃₁.trans (D_sub_DE D₁)) (fC ⟨D_E D₁, D_E_mem D₁⟩) :=
      congr_fun hcomp1 _
    have step2 : restrictionMap D₂.1 D₃ h₃₂ (fV D₂) =
        restrictionMap (D_E D₂) D₃ (h₃₂.trans (D_sub_DE D₂)) (fC ⟨D_E D₂, D_E_mem D₂⟩) :=
      congr_fun hcomp2 _
    rw [step1, step2]
    exact hC_compat ⟨D_E D₁, D_E_mem D₁⟩ ⟨D_E D₂, D_E_mem D₂⟩ D₃ _ _
  -- Step 4: Apply hV_glue_refined to get x.
  obtain ⟨x, hx⟩ := hV_glue_refined fV fV_compat
  refine ⟨x, fun E => ?_⟩
  -- Step 5: Apply hE_sep_direct at E to conclude
  -- `restrictionMap C.base E x = fC E`.
  apply hE_sep_direct E
  intro D hD
  -- D ∈ per_E_local_covering E.covers. Also D ∈ refinedVCovers (per_E ⊆ refined).
  have D_in_refined : D ∈ C.refinedVCovers S f₀ := by
    rw [(C.mem_per_E_local_covering_covers S f₀ E hS_per_E D)] at hD
    obtain ⟨f, hf, _h_in_E, h_eq⟩ := hD
    rw [C.mem_refinedVCovers S f₀]
    rcases h_eq with heq | heq
    · exact Or.inl ⟨f, hf, heq⟩
    · exact Or.inr ⟨f, hf, heq⟩
  -- LHS via restrictionMap_comp: restrictionMap E D ∘ restrictionMap C.base E
  -- = restrictionMap C.base D (composed subset).
  have hcomp_LHS := restrictionMap_comp C.base E.1 D (C.hsubset E.1 E.2)
    ((C.per_E_local_covering S f₀ E hS_per_E).hsubset D hD)
  have hLHS_step : restrictionMap E.1 D
        ((C.per_E_local_covering S f₀ E hS_per_E).hsubset D hD)
        (restrictionMap C.base E.1 (C.hsubset E.1 E.2) x) =
      restrictionMap C.base D
        (((C.per_E_local_covering S f₀ E hS_per_E).hsubset D hD).trans
          (C.hsubset E.1 E.2)) x :=
    congr_fun hcomp_LHS x
  rw [hLHS_step]
  -- Apply hx at ⟨D, D_in_refined⟩ to replace restrictionMap C.base D x with fV.
  have hxD := hx ⟨D, D_in_refined⟩
  -- Proof irrelevance: two subset proofs of
  -- `rationalOpen D.T D.s ⊆ rationalOpen C.base.T C.base.s`.
  rw [show ((C.per_E_local_covering S f₀ E hS_per_E).hsubset D hD).trans
        (C.hsubset E.1 E.2) =
      C.refinedVCovers_subset_base S f₀ D D_in_refined from
    Subsingleton.elim _ _]
  rw [hxD]
  -- fV ⟨D, D_in_refined⟩ = restrictionMap (D_E ⟨D,_⟩) D _ (fC ⟨D_E ⟨D,_⟩,_⟩).
  -- By hC_compat at (⟨D_E ⟨D,_⟩,_⟩, E, D), this equals restrictionMap E D _ (fC E).
  change restrictionMap (D_E ⟨D, D_in_refined⟩) D (D_sub_DE ⟨D, D_in_refined⟩)
      (fC ⟨D_E ⟨D, D_in_refined⟩, D_E_mem ⟨D, D_in_refined⟩⟩) =
    restrictionMap E.1 D
      ((C.per_E_local_covering S f₀ E hS_per_E).hsubset D hD) (fC E)
  exact hC_compat ⟨D_E ⟨D, D_in_refined⟩, D_E_mem ⟨D, D_in_refined⟩⟩ E D _ _

/-! ### Caller-side `hZavyalov_per_E` consumption (direct per-E route)

The clean caller API for S-GEOM-ASM: consumes the strengthened
`hZavyalov_per_E` existence hypothesis (matching the output shape of
`StandardCover.RationalCoveringData.refines_by_standard_cover_per_E`),
destructures internally to obtain the `StandardCover A` and its
`refines_cover_per_E` / `refines_contain` witnesses, then applies
`tateAcyclicity_Part2_direct_per_E`.

**Lane A (`hV_glue_refined`) and Lane B (`hE_sep_direct`)** are taken
as **universal suppliers** parameterised over any valid standard cover
`S'`: they produce the respective lane outputs for any `S'`
satisfying the refinement predicates. This decouples the lane content
from the specific `S` chosen by `refines_by_standard_cover_per_E`
(which is classically chosen and thus not directly controllable by
the caller).

The universal-supplier shape is the **natural caller API**: the Lane A
proof (via `laurentCover_gluing_presheaf` post-T-OV-1) and Lane B
proof (via `productRestriction_injective_tate_via_prime_extension_closed`
at each E post-T-IDEAL-2) are statements that hold for ANY standard
cover, so supplying them as `∀ S', ...` is honest to the mathematics.

**Design note**: because `hZavyalov_per_E` is existential, the specific
`S` inside the wrapper is determined by `Classical.choose` via
`refines_by_standard_cover_per_E`'s proof. The universal-supplier shape
on Lane A/B makes the wrapper's Part-2 output independent of the
`Classical.choose` ambiguity — the output ∃ x is a concrete existence
statement on `C.base`, unambiguous once the inputs are fixed. -/

/-- **Caller wrapper**: `tateAcyclicity` Part 2 via the direct per-E
route, consuming `hZavyalov_per_E` + universal Lane A/B suppliers.

Extracts the standard cover `S` via
`RationalCoveringData.refines_by_standard_cover_per_E` and applies
`tateAcyclicity_Part2_direct_per_E` with the chosen S plus the lane
outputs for THAT S (supplied by the universal lane suppliers).

This is the **downstream-callable API** that `LaurentRefinement.lean`
(or any Part-2 closure caller) can invoke with:
* `hZavyalov_per_E` — from the Wedhorn/Hübner construction.
* `f₀ : A` — a Laurent split point (caller's choice).
* `fC`, `hC_compat` — caller's compatible section family.
* `lane_A_supplier` — Lane A discharge (Laurent-overlap gluing on
  refined V-cover, post-T-OV-1).
* `lane_B_supplier` — Lane B discharge (Cor 8.32 at each E's per-E
  local covering, post-T-IDEAL-2).

Both lane suppliers are universally quantified over `StandardCover A`
and its refinement properties, matching the mathematical shape of
Lanes A/B which hold uniformly across all standard covers. -/
theorem RationalCoveringData.tateAcyclicity_Part2_via_hZavyalov_per_E_direct
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (f₀ : A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    -- Lane A universal supplier: for any valid standard cover S',
    -- Laurent-overlap gluing produces hV_glue on `refinedVCovers S'.elts f₀`.
    (lane_A_supplier : ∀ (S' : StandardCover A)
      (_hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ },
        restrictionMap C.base D.1
          (C.refinedVCovers_subset_base S'.elts f₀ D.1 D.2) x = fV D)
    -- Lane B universal supplier: for any valid standard cover S',
    -- Cor 8.32 at each E gives hE_sep_direct on per_E_local_covering.
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  -- Extract S via `refines_by_standard_cover_per_E`.
  obtain ⟨S, hS_per_E, hS_contain⟩ :=
    C.refines_by_standard_cover_per_E hne hZavyalov_per_E
  -- Apply direct per-E Part-2 assembly with this S plus the lane outputs.
  exact C.tateAcyclicity_Part2_direct_per_E S.elts f₀ hS_per_E hS_contain
    fC hC_compat
    (lane_A_supplier S hS_per_E hS_contain)
    (lane_B_supplier S hS_per_E hS_contain)

end ValuationSpectrum

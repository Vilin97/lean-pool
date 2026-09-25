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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.LaurentRefinement

/-!
# Depth-N Wedhorn 2.13: relative rational locale data

For any pair of rational locales `E, D : RationalLocData A` with
`rationalOpen D.T D.s ⊆ rationalOpen E.T E.s`, this file constructs:

* `relativeRationalLocData E D hsub : RationalLocData (presheafValue E)` —
  D viewed as a rational locale over the intermediate ring `presheafValue E`.
  The data: `T = D.T.image E.canonicalMap`, `s = E.canonicalMap D.s`,
  `P = presheafValue_pairOfDefinition_concrete _ E`.

* `presheafValue_relative_equiv : presheafValue D ≃+*
  presheafValue (relativeRationalLocData E D hsub)` — the depth-N
  Wedhorn 2.13 identification, intertwining the restriction map with the
  canonical map at the E-level.

This is the structural piece that closes `T-RATIONAL-FLAT-GENERAL`. The
hypothesis-parameterised general flatness theorem
(`restrictionMap_flat_of_rational_subset_via_relative` in
`RestrictionFlatness.lean`) consumes the relative equiv produced here to
discharge flatness of `O(E) → O(D)` for arbitrary `D ⊆ E`.

## Architecture

Parallel to the existing depth-1 minus infrastructure
(`iteratedMinusDatum_B`, `iteratedMinus_forwardLocHom`,
`iteratedMinus_forwardHom`, `iteratedMinus_backward*`,
`presheafValue_iteratedMinus_equiv`, etc.) but generalised from
`T = {1}, s = D₀.canonicalMap f` to arbitrary `T = D.T.image E.canonicalMap`
and `s = E.canonicalMap D.s` coming from any rational sub-locale D ⊆ E.

## References

* [Wedhorn 2019] T. Wedhorn, *Adic spaces*. Lemma 2.13 (transitivity of
  rational localizations).
-/

@[expose] public section

open ValuationSpectrum CompletionLocalization

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsHuberRing A] [HasLocLiftPowerBounded A]

/-! ### `relativeRationalLocData`: depth-N pull-back of D along E.canonicalMap

Given `E, D : RationalLocData A` with `rationalOpen D ⊆ rationalOpen E`,
build a rational locale data over `presheafValue E` carrying:
* T = `D.T.image E.canonicalMap` (the image of D's T-elements in presheafValue E).
* s = `E.canonicalMap D.s` (the image of D's denominator).
* P inherited from E via `presheafValue_pairOfDefinition_concrete`.

The `hopen` condition is the key piece: openness in the relative locSubring. -/

/-- **Residual obstruction (Wedhorn Lemma 2.13, non-LaurentNormalized case).**

The single algebraic claim isolating the obstruction for
`relativeRationalLocData_hopen_proof`: the unit fraction `1 / s_at_E` lies in
the relative locSubring `locSubring P_at_E T_at_E s_at_E` over
`presheafValue E`, where `s_at_E = E.canonicalMap D.s` and
`T_at_E = D.T.image E.canonicalMap`.

**Status (2026-05-23).** Decomposed-out from `relativeRationalLocData_hopen_proof`.
The full `hopen` for the relative datum reduces to this one membership via the
multiplicative identity
`divByS b s_at_E = algebraMap b · divByS 1 s_at_E` together with
`algebraMap b ∈ locSubring` (for `b ∈ P_at_E.A₀`, by
`algebraMap_mem_locSubring`). See the docstring of
`relativeRationalLocData_hopen_proof` for the three closure routes that have
been ruled out (N = 0 collapse, pull-through of D's hopen via locLift,
closure-aware Lemma 8.5 argument).

**Mathematical content.** Wedhorn Lemma 2.13: for `D ⊆ E` rational, the datum
on `presheafValue E` describing D is again rational. The non-trivial piece is
exactly that `1/s_at_E` admits a polynomial expression in the generators of
`locSubring P_at_E T_at_E s_at_E`, which is the explicit algebraic identity of
Lemma 2.13.

For `LaurentNormalized D` this is closed sorry-free by
`relativeRationalLocData_hopen_proof_of_laurentNormalized` (the `1 ∈ D.T`
hypothesis gives `1 ∈ T_at_E`, hence `divByS 1 s_at_E ∈ locSubring` via
`divByS_mem_locSubring`). -/
private theorem relativeRationalLocData_divByS_one_mem_locSubring
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A)
    (_hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
    letI : DecidableEq (presheafValue E) := Classical.decEq _
    letI P_at_E : PairOfDefinition (presheafValue E) :=
      presheafValue_concretePair E
    divByS (1 : presheafValue E) (E.canonicalMap D.s) ∈
      locSubring P_at_E (D.T.image E.canonicalMap) (E.canonicalMap D.s) := by
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  sorry

/-- `hopen` for the relative rational locale data: openness of the relative
locSubring's image of `(P_at_E.I)^N` in `Localization.Away (E.canonicalMap D.s)`.

**Mathematical content.** We need
```
∃ N : ℕ, ∀ b ∈ P_at_E.I ^ N,
  divByS (b : presheafValue E) (E.canonicalMap D.s) ∈
    locSubring P_at_E (D.T.image E.canonicalMap) (E.canonicalMap D.s)
```
where `P_at_E = presheafValue_concretePair E` (so
`P_at_E.A₀ = presheafValue_ringOfDef E` is the topological closure of the
`E.coeRingHom`-image of `locSubring E.P E.T E.s` in `presheafValue E`, and
`P_at_E.I = presheafValue_idealOfDef E = Ideal.map (locSubringToRingOfDef E)
(locIdeal E.P E.T E.s)` uses `E.P` and `E`'s data).

**Why the standard templates do not close this.**

* `iteratedMinusDatum_B` (LaurentRefinement.lean:476) closes the analogous
  `hopen` with `N = 0` by exploiting `T = {1}` so that
  `divByS 1 s ∈ locSubring` directly via `divByS_mem_locSubring` together with
  `1 ∈ {1}`. Here `T_at_E = D.T.image E.canonicalMap` does NOT in general
  contain `1`, so the `divByS 1 s = b/s` decomposition factor `divByS 1 s`
  cannot be discharged by membership in `T_at_E`.

* The `IsLocalization.Away.lift` approach (used in `laurentMinusDatum` /
  `divByS_mul_f_mem'`) pushes a `hopen` witness through a map between
  `Localization.Away`-rings of the SAME base ring `A`. Here we would need to
  push D's `hopen` (which lives in `Localization.Away D.s` at the A-level)
  through `E.canonicalMap : A →+* presheafValue E` to land in
  `Localization.Away (E.canonicalMap D.s)`. The obstruction: a generic
  `b ∈ P_at_E.A₀` is NOT of the form `algebraMap (E.canonicalMap a)` for
  `a ∈ D.P.A₀` — `P_at_E.A₀` is the topological closure of the
  `E.coeRingHom`-image of `locSubring E.P E.T E.s` (using E.P, not D.P).
  So D's A-level `hopen` (which uses D.P) does not transfer pointwise.

* The radical relation `rad_relation_of_rational_subset` (PresheafTateStructure.lean)
  gives `∃ N e, e * E.s = D.s ^ N` in `A`. Pushed through `E.canonicalMap`:
  `E.canonicalMap e * E.canonicalMap E.s = (E.canonicalMap D.s) ^ N` in
  `presheafValue E`. This shows `E.canonicalMap E.s` is a unit times
  `(E.canonicalMap D.s) ^ N` modulo `E.canonicalMap e`, but `E.canonicalMap e`
  is not generally in `P_at_E.A₀`, so this also does not directly give
  `divByS b s_at_E ∈ locSubring` for arbitrary `b ∈ P_at_E.A₀`.

**Substantial missing piece.** A clean proof requires either:

1. A "lifted-hopen" infrastructure lemma: given the localization-level
   `hopen` for D at the A-level and the radical relation, construct a
   `hopen` witness for `(P_at_E, D.T.image E.canonicalMap, E.canonicalMap D.s)`
   via the `locLift` map at the level of `Localization.Away` followed by
   pushing through `E.coeRingHom`. The image of `locSubring D.P D.T D.s`
   under the appropriate composite needs to land in the relative locSubring,
   which requires `D.P.A₀.image canonicalMap ⊆ P_at_E.A₀`-style containments
   that are NOT automatic because D.P and E.P may differ.

2. A "closure-aware" hopen proof: the structure of `P_at_E.A₀` as a
   topological closure of `coeRingHom`-image of `locSubring E.P E.T E.s`
   means elements `b ∈ P_at_E.I ^ N` are LIMITS of finite-sum products of
   `coeRingHom`-images of elements in `locIdeal E.P E.T E.s ^ N`. The
   relative locSubring is closed under continuous operations, so a limit
   argument plus the algebraic identity at the dense (uncompleted) level
   would close it — but this needs Wedhorn Lemma 8.5 (the closed-locSubring
   completion identification) which is not yet supplied at this level of
   generality for the relative datum.

3. A direct algebraic identity exploiting `(E.canonicalMap D.s)^N =
   E.canonicalMap (e * E.s)` (rad-relation pushforward) combined with
   `E.canonicalMap E.s` being a unit. This would express `divByS 1 s_at_E`
   as a polynomial in `divByS (E.canonicalMap t) s_at_E` (for `t ∈ D.T`)
   plus `algebraMap (E.canonicalMap a)` factors (for `a ∈ E.P.A₀`), which is
   precisely the claim. The missing ingredient is the explicit polynomial
   form, which is the content of Wedhorn Lemma 2.13.

**Current status.** This sorry is the central piece blocking
`T-WEDHORN-213-DATUM` → `relativeRationalLocData`. The downstream consumer
(`restrictionMap_flat_of_rational_subset_via_relative`) currently takes
`D_at_E` as a PARAMETER, so an explicit construction here would close
the loop on `T-RATIONAL-FLAT-GENERAL`. -/
private theorem relativeRationalLocData_hopen_proof
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A)
    (_hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
    letI : DecidableEq (presheafValue E) := Classical.decEq _
    letI P_at_E : PairOfDefinition (presheafValue E) :=
      presheafValue_concretePair E
    ∃ N : ℕ, ∀ b : P_at_E.A₀, b ∈ P_at_E.I ^ N →
      divByS (b : presheafValue E) (E.canonicalMap D.s) ∈
        locSubring P_at_E (D.T.image E.canonicalMap) (E.canonicalMap D.s) := by
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  -- See the theorem docstring for the full obstruction analysis.
  --
  -- Summary of what's been ruled out:
  --
  -- (a) `N = 0` does NOT work: the goal becomes `divByS b s_at_E ∈ locSubring`
  --     for arbitrary `b ∈ P_at_E.A₀`. Decomposing as
  --     `divByS b s_at_E = algebraMap b * divByS 1 s_at_E` reduces to showing
  --     `divByS 1 s_at_E ∈ locSubring`, i.e., `s_at_E` is a unit in the
  --     locSubring. This holds iff some `t ∈ T_at_E = D.T.image E.canonicalMap`
  --     and `algebraMap t⁻¹ ∈ algebraMap '' P_at_E.A₀`, which is NOT automatic.
  --
  -- (b) Pulling D's `hopen` (∃ N₀, ∀ b ∈ D.P.I^N₀, divByS b D.s ∈
  --     locSubring D.P D.T D.s) through `E.canonicalMap`: the natural map
  --     `Localization.Away D.s →+* Localization.Away (E.canonicalMap D.s)`
  --     (via `IsLocalization.Away.lift`) does NOT necessarily send
  --     `locSubring D.P D.T D.s` into `locSubring P_at_E T_at_E s_at_E`,
  --     because `D.P.A₀.image algebraMap` (the generators of D's locSubring)
  --     does NOT land in `P_at_E.A₀.image algebraMap` (the generators on
  --     the target). The pairs `D.P` and `P_at_E` (which uses `E.P`) are
  --     independent.
  --
  -- (c) Closure argument: `P_at_E.A₀` is the topological closure of
  --     `E.coeRingHom '' locSubring E.P E.T E.s` in `presheafValue E`. An
  --     element `b ∈ P_at_E.I^N` is a finite sum of products from
  --     `Ideal.map (locSubringToRingOfDef E) (locIdeal E.P E.T E.s)^N`,
  --     which lives in the closure. To show `divByS b s_at_E ∈ locSubring`,
  --     we would need the relative locSubring to also be closed under
  --     limits AND to contain the `divByS s_at_E`-images of the dense
  --     subset — both of which are missing infrastructure.
  --
  -- INTENTIONAL STUB: the witness `N` requires new infrastructure
  -- bridging Wedhorn Lemma 2.13 with the explicit algebraic identity at
  -- the localization-and-completion level. The downstream consumer
  -- (`restrictionMap_flat_of_rational_subset_via_relative` in
  -- `Adic spaces/RestrictionFlatness.lean`) takes `D_at_E` as a
  -- parameter, so this `sorry` does not block any working downstream
  -- proof; it blocks only the closed-form constructor for `D_at_E`.
  --
  -- TODO(T-WEDHORN-213-DATUM): supply the explicit `N` via the
  -- Wedhorn Lemma 2.13 algebraic identity. Likely needs:
  -- * A bridge lemma `D.P.A₀ ∩ (something) → P_at_E.A₀` mapping
  --   D-level elements into the relative ring of definition, possibly
  --   via a refinement step that enlarges either D.P or E.P.
  -- * Use of `rad_relation_of_rational_subset` to obtain `e, N` with
  --   `e * E.s = D.s ^ N` in `A`, hence
  --   `E.canonicalMap e * E.canonicalMap E.s = (E.canonicalMap D.s) ^ N`
  --   in `presheafValue E` (gives that `E.canonicalMap e` is a unit in
  --   `Localization.Away (E.canonicalMap D.s)`).
  -- * Wedhorn Lemma 8.5 (closed-locSubring completion identification)
  --   to handle the topological-closure structure of `P_at_E.A₀`.
  --
  -- DECOMPOSITION (2026-05-23): the goal reduces — for ANY choice of `N`
  -- — to the single membership claim
  --   `divByS 1 s_at_E ∈ locSubring P_at_E T_at_E s_at_E`,
  -- via the factorization `divByS b s_at_E = algebraMap b · divByS 1 s_at_E`.
  -- The sub-lemma `relativeRationalLocData_divByS_one_mem_locSubring` carries
  -- the residual obstruction (Wedhorn 2.13 / Lemma 8.5); the main hopen
  -- witness is now `N = 0` plus the standard mul-decomposition argument.
  letI P_at_E : PairOfDefinition (presheafValue E) :=
    presheafValue_concretePair E
  refine ⟨0, fun b _ => ?_⟩
  have hdivByS_1 :
      divByS (1 : presheafValue E) (E.canonicalMap D.s) ∈
        locSubring P_at_E (D.T.image E.canonicalMap) (E.canonicalMap D.s) :=
    relativeRationalLocData_divByS_one_mem_locSubring E D _hsub
  have hmul : algebraMap (presheafValue E) _ (b : presheafValue E) *
      divByS (1 : presheafValue E) (E.canonicalMap D.s) =
      divByS (b : presheafValue E) (E.canonicalMap D.s) := by
    unfold divByS
    rw [← IsLocalization.mk'_one
          (M := Submonoid.powers (E.canonicalMap D.s))
          (S := Localization.Away (E.canonicalMap D.s)) (b : presheafValue E),
        ← IsLocalization.mk'_mul, one_mul, mul_one]
  rw [← hmul]
  exact (locSubring _ _ _).mul_mem
    (algebraMap_mem_locSubring _ _ _ b.2) hdivByS_1

/-- The relative rational locale data: D viewed as a rational locale over
`presheafValue E`. Generalises the depth-1 `iteratedMinusDatum_B` /
`iteratedPlusDatum_B` (which specialise to T = {1} or T = {f}).

This is the central object of T-WEDHORN-213-DATUM. -/
noncomputable def relativeRationalLocData
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A)
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    RationalLocData (presheafValue E) :=
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  { P := presheafValue_concretePair E
    T := D.T.image E.canonicalMap
    s := E.canonicalMap D.s
    hopen := relativeRationalLocData_hopen_proof E D hsub }

/-- The `.T` projection of `relativeRationalLocData` unfolds to
`D.T.image E.canonicalMap`. -/
theorem relativeRationalLocData_T
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A)
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    letI : DecidableEq (presheafValue E) := Classical.decEq _
    (relativeRationalLocData E D hsub).T = D.T.image E.canonicalMap := by
  rfl

/-- The `.s` projection of `relativeRationalLocData` unfolds to
`E.canonicalMap D.s`. -/
theorem relativeRationalLocData_s
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A)
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    (relativeRationalLocData E D hsub).s = E.canonicalMap D.s := by
  rfl

/-! ### `hopen` for the LaurentNormalized special case

**Breakthrough (2026-05-12)**: when `D` carries `[LaurentNormalized D]` (i.e.,
`1 ∈ D.T`), the `hopen` proof for the relative datum goes through with `N = 0`
via the standard `iteratedMinusDatum_B`-style trick:

* `1 ∈ D.T` ⟹ `E.canonicalMap 1 = 1 ∈ T_at_E = D.T.image E.canonicalMap`.
* By `divByS_mem_locSubring` with `1 ∈ T_at_E`: `divByS 1 s_at_E ∈ locSubring`.
* For any `b ∈ P_at_E.A₀`: `algebraMap b ∈ locSubring` (`algebraMap_mem_locSubring`).
* Decomposition: `divByS b s_at_E = algebraMap b * divByS 1 s_at_E`.
* Both factors in `locSubring`, which is closed under multiplication. ✓

This eliminates the need for Wedhorn 2.13's full algebraic identity in the
common case where D is LaurentNormalized — which covers ALL Laurent-cover
pieces (`laurentMinusDatum`, `laurentPlusDatum`, and their iterations).

This special-case `hopen` proof is what unblocks the chain decomposition route:
every step in a Wedhorn-style chain is a basic Laurent operation, hence
LaurentNormalized, so the relative datum exists with explicit `hopen`.

The general case (D not LaurentNormalized) still requires the full Wedhorn 2.13
algebraic identity (`relativeRationalLocData_hopen_proof` above with its
`sorry`). -/
theorem relativeRationalLocData_hopen_proof_of_laurentNormalized
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (_hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
    letI : DecidableEq (presheafValue E) := Classical.decEq _
    letI P_at_E : PairOfDefinition (presheafValue E) :=
      presheafValue_concretePair E
    ∃ N : ℕ, ∀ b : P_at_E.A₀, b ∈ P_at_E.I ^ N →
      divByS (b : presheafValue E) (E.canonicalMap D.s) ∈
        locSubring P_at_E (D.T.image E.canonicalMap) (E.canonicalMap D.s) := by
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  letI P_at_E : PairOfDefinition (presheafValue E) :=
    presheafValue_concretePair E
  -- Use N = 0: every b in P_at_E.A₀ qualifies.
  refine ⟨0, fun b _ => ?_⟩
  -- Step 1: 1 ∈ D.T (from LaurentNormalized D)
  have h1_in_DT : (1 : A) ∈ D.T := LaurentNormalized.one_mem_T
  -- Step 2: E.canonicalMap 1 = 1 ∈ T_at_E.
  have h1_in_TatE : (1 : presheafValue E) ∈ D.T.image E.canonicalMap :=
    Finset.mem_image.mpr ⟨1, h1_in_DT, map_one _⟩
  -- Step 3: divByS 1 s_at_E ∈ locSubring.
  have hdivByS_1 : divByS (1 : presheafValue E) (E.canonicalMap D.s) ∈
      locSubring P_at_E (D.T.image E.canonicalMap) (E.canonicalMap D.s) :=
    divByS_mem_locSubring P_at_E (D.T.image E.canonicalMap) (E.canonicalMap D.s)
      h1_in_TatE
  -- Step 4: divByS b s_at_E = algebraMap b * divByS 1 s_at_E.
  have hmul : algebraMap (presheafValue E) _ (b : presheafValue E) *
      divByS (1 : presheafValue E) (E.canonicalMap D.s) =
      divByS (b : presheafValue E) (E.canonicalMap D.s) := by
    unfold divByS
    rw [← IsLocalization.mk'_one
          (M := Submonoid.powers (E.canonicalMap D.s))
          (S := Localization.Away (E.canonicalMap D.s)) (b : presheafValue E),
        ← IsLocalization.mk'_mul, one_mul, mul_one]
  -- Step 5: combine — both factors in locSubring; multiplication closure.
  rw [← hmul]
  exact (locSubring _ _ _).mul_mem
    (algebraMap_mem_locSubring _ _ _ b.2)
    hdivByS_1

/-! ### `relativeRationalLocData` for LaurentNormalized D

Sorry-free variant of `relativeRationalLocData` available when `D` is
LaurentNormalized. The hopen is discharged by
`relativeRationalLocData_hopen_proof_of_laurentNormalized`. -/
noncomputable def relativeRationalLocData_laurentNormalized
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    RationalLocData (presheafValue E) :=
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  { P := presheafValue_concretePair E
    T := D.T.image E.canonicalMap
    s := E.canonicalMap D.s
    hopen := relativeRationalLocData_hopen_proof_of_laurentNormalized E D hsub }

/-- `.T` of `relativeRationalLocData_laurentNormalized` unfolds to
`D.T.image E.canonicalMap`. -/
theorem relativeRationalLocData_laurentNormalized_T
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    letI : DecidableEq (presheafValue E) := Classical.decEq _
    (relativeRationalLocData_laurentNormalized E D hsub).T =
      D.T.image E.canonicalMap := by
  rfl

/-- `.s` of `relativeRationalLocData_laurentNormalized` unfolds to
`E.canonicalMap D.s`. -/
theorem relativeRationalLocData_laurentNormalized_s
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    (relativeRationalLocData_laurentNormalized E D hsub).s = E.canonicalMap D.s := by
  rfl

/-! ### Forward uncompleted locHom (LaurentNormalized case)

For LaurentNormalized D ⊆ E rationally, construct the forward localization-level
hom `Localization.Away D.s →+* presheafValue D_at_E` where
`D_at_E = relativeRationalLocData_laurentNormalized E D hsub`.

The witness: D.s, viewed under A → presheafValue E → presheafValue D_at_E,
becomes a unit (since D_at_E.s = E.canonicalMap D.s and D_at_E.canonicalMap
sends D_at_E.s to a unit in presheafValue D_at_E).

This is the LaurentNormalized analog of `iteratedMinus_forwardLocHom`. -/

/-- The composite A → presheafValue E → presheafValue D_at_E sending
D.s to a unit. -/
private noncomputable def relativeLaurentNormalized_baseHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    A →+* presheafValue (relativeRationalLocData_laurentNormalized E D hsub) :=
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  (relativeRationalLocData_laurentNormalized E D hsub).canonicalMap.comp E.canonicalMap

/-- D.s is a unit under the base hom: A → presheafValue E → presheafValue D_at_E. -/
private theorem relativeLaurentNormalized_Ds_isUnit
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    IsUnit (relativeLaurentNormalized_baseHom E D hsub D.s) := by
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  -- Unfold: baseHom D.s = D_at_E.canonicalMap (E.canonicalMap D.s)
  --                    = D_at_E.canonicalMap D_at_E.s
  -- which is a unit by `isUnit_s_in_presheafValue D_at_E`.
  change IsUnit ((relativeRationalLocData_laurentNormalized E D hsub).canonicalMap
    (E.canonicalMap D.s))
  -- E.canonicalMap D.s = D_at_E.s by relativeRationalLocData_laurentNormalized_s.
  rw [show E.canonicalMap D.s =
    (relativeRationalLocData_laurentNormalized E D hsub).s from rfl]
  exact isUnit_s_in_presheafValue _

/-- Forward uncompleted hom `Loc_A(D.s) →+* presheafValue D_at_E`. -/
noncomputable def relativeLaurentNormalized_forwardLocHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    Localization.Away D.s →+*
      presheafValue (relativeRationalLocData_laurentNormalized E D hsub) :=
  IsLocalization.Away.lift (S := Localization.Away D.s) (R := A) D.s
    (relativeLaurentNormalized_Ds_isUnit E D hsub)

/-- `relativeLaurentNormalized_forwardLocHom` on `algebraMap a` equals the
base hom on `a`. -/
theorem relativeLaurentNormalized_forwardLocHom_algebraMap
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) (a : A) :
    relativeLaurentNormalized_forwardLocHom E D hsub
      (algebraMap A (Localization.Away D.s) a) =
      relativeLaurentNormalized_baseHom E D hsub a :=
  IsLocalization.Away.lift_eq D.s (relativeLaurentNormalized_Ds_isUnit E D hsub) a

/-! ### Backward uncompleted locHom (LaurentNormalized case)

The backward direction: `Localization.Away (E.canonicalMap D.s) →+* presheafValue D`.

The witness: `restrictionMapHom E D hsub : presheafValue E → presheafValue D`
sends `E.canonicalMap D.s` to `D.canonicalMap D.s` (by
`restrictionMapHom_canonicalMap`), which is a unit in `presheafValue D`
(by `isUnit_s_in_presheafValue D`). By `IsLocalization.Away.lift`, this
extends to a hom from `Localization.Away (E.canonicalMap D.s)`. -/

/-- `E.canonicalMap D.s`, viewed in presheafValue D via restriction, is a unit:
`restrictionMapHom E D hsub (E.canonicalMap D.s) = D.canonicalMap D.s`, which
is a unit by `isUnit_s_in_presheafValue D`. -/
theorem restrictionMapHom_E_canonicalMap_Ds_isUnit_in_D
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A) (D : RationalLocData A)
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    IsUnit (restrictionMapHom E D hsub (E.canonicalMap D.s)) := by
  rw [restrictionMapHom_canonicalMap]
  exact isUnit_s_in_presheafValue D

/-- Backward uncompleted hom `Loc(E.canonicalMap D.s) →+* presheafValue D`
via `IsLocalization.Away.lift` with `E.canonicalMap D.s` sent to a unit in
the target through `restrictionMapHom E D hsub`. -/
noncomputable def relativeLaurentNormalized_backwardLocHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    Localization.Away (E.canonicalMap D.s) →+* presheafValue D :=
  IsLocalization.Away.lift (S := Localization.Away (E.canonicalMap D.s))
    (R := presheafValue E) (E.canonicalMap D.s)
    (g := restrictionMapHom E D hsub)
    (restrictionMapHom_E_canonicalMap_Ds_isUnit_in_D E D hsub)

/-- Backward loc hom on `algebraMap`: equals `restrictionMapHom E D hsub`. -/
theorem relativeLaurentNormalized_backwardLocHom_algebraMap
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s)
    (b : presheafValue E) :
    relativeLaurentNormalized_backwardLocHom E D hsub
      (algebraMap (presheafValue E) (Localization.Away (E.canonicalMap D.s)) b) =
      restrictionMapHom E D hsub b :=
  IsLocalization.Away.lift_eq (E.canonicalMap D.s)
    (restrictionMapHom_E_canonicalMap_Ds_isUnit_in_D E D hsub) b

/-! ### Inner forward locHom (LaurentNormalized case)

To prove continuity of `relativeLaurentNormalized_forwardLocHom`, factor it
through the intermediate `Localization.Away (E.canonicalMap D.s)` (over
`presheafValue E`):

  `Loc_A(D.s) → Loc_{presheafValue E}(E.canonicalMap D.s) → presheafValue D_at_E`

The right factor is `D_at_E.coeRingHom` (continuous, completion embedding).
The left factor is the algebraic inner forward hom, defined below.
Continuity of the inner is by `locTopology_continuous_lift`. -/

/-- D.s is a unit (via algebraMap A) in `Loc_{presheafValue E}(E.canonicalMap D.s)`:
the natural map A → presheafValue E → Loc sends D.s to E.canonicalMap D.s, which
equals `D_at_E.s` and is the localization's unit-element. -/
private theorem relativeLaurentNormalized_Ds_isUnit_in_Loc
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (_hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
    IsUnit ((algebraMap (presheafValue E)
      (Localization.Away (E.canonicalMap D.s))).comp E.canonicalMap D.s) := by
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  change IsUnit (algebraMap (presheafValue E) _ (E.canonicalMap D.s))
  exact IsLocalization.Away.algebraMap_isUnit _

/-- Inner forward uncompleted hom
`Loc_A(D.s) →+* Loc_{presheafValue E}(E.canonicalMap D.s)`. -/
noncomputable def relativeLaurentNormalized_forwardInnerLocHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
    Localization.Away D.s →+* Localization.Away (E.canonicalMap D.s) :=
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  IsLocalization.Away.lift (S := Localization.Away D.s) (R := A) D.s
    (relativeLaurentNormalized_Ds_isUnit_in_Loc E D hsub)

/-- forwardInnerLocHom on algebraMap A image equals algebraMap (presheafValue E)
of E.canonicalMap. -/
theorem relativeLaurentNormalized_forwardInnerLocHom_algebraMap
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) (a : A) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
    relativeLaurentNormalized_forwardInnerLocHom E D hsub
        (algebraMap A (Localization.Away D.s) a) =
      algebraMap (presheafValue E) (Localization.Away (E.canonicalMap D.s))
        (E.canonicalMap a) := by
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  exact IsLocalization.Away.lift_eq D.s
    (relativeLaurentNormalized_Ds_isUnit_in_Loc E D hsub) a

/-- Factorization: forwardLocHom = D_at_E.coeRingHom ∘ forwardInnerLocHom.
Both sides equal the unique IsLocalization.Away.lift extension of
`D_at_E.canonicalMap ∘ E.canonicalMap : A → presheafValue D_at_E`. -/
theorem relativeLaurentNormalized_forwardLocHom_factor
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
    relativeLaurentNormalized_forwardLocHom E D hsub =
      (relativeRationalLocData_laurentNormalized E D hsub).coeRingHom.comp
        (relativeLaurentNormalized_forwardInnerLocHom E D hsub) := by
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  -- Both sides agree on `algebraMap A _` by uniqueness of IsLocalization.Away.lift.
  apply IsLocalization.ringHom_ext (Submonoid.powers D.s)
  ext a
  -- LHS: forwardLocHom (algebraMap A _ a) = baseHom a = D_at_E.canonicalMap (E.canonicalMap a).
  -- RHS: coeRingHom ∘ forwardInnerLocHom (algebraMap A _ a)
  --    = coeRingHom (algebraMap (presheafValue E) _ (E.canonicalMap a))
  --    = D_at_E.coeRingHom (algebraMap _ (E.canonicalMap a))
  --    = D_at_E.canonicalMap (E.canonicalMap a)  (by definition of canonicalMap).
  simp only [RingHom.comp_apply]
  rw [relativeLaurentNormalized_forwardLocHom_algebraMap]
  -- Inner: forwardInnerLocHom (algebraMap A _ a)
  -- = algebraMap (presheafValue E) _ (E.canonicalMap a).
  change (relativeRationalLocData_laurentNormalized E D hsub).canonicalMap
      (E.canonicalMap a) =
    (relativeRationalLocData_laurentNormalized E D hsub).coeRingHom
      (relativeLaurentNormalized_forwardInnerLocHom E D hsub
        (algebraMap A (Localization.Away D.s) a))
  change relativeLaurentNormalized_baseHom E D hsub a =
    (relativeRationalLocData_laurentNormalized E D hsub).coeRingHom
      (relativeLaurentNormalized_forwardInnerLocHom E D hsub
        (algebraMap A (Localization.Away D.s) a))
  -- Compute forwardInnerLocHom on algebraMap a:
  have hinner : relativeLaurentNormalized_forwardInnerLocHom E D hsub
      (algebraMap A (Localization.Away D.s) a) =
      algebraMap (presheafValue E) (Localization.Away (E.canonicalMap D.s))
        (E.canonicalMap a) :=
    IsLocalization.Away.lift_eq D.s
      (relativeLaurentNormalized_Ds_isUnit_in_Loc E D hsub) a
  rw [hinner]
  -- Goal: baseHom a = coeRingHom (algebraMap presheafValue E _ (E.canonicalMap a))
  -- baseHom a = D_at_E.canonicalMap (E.canonicalMap a)
  -- = D_at_E.coeRingHom (algebraMap _ (E.canonicalMap a))
  -- by definition of canonicalMap.
  rfl

/-- `relativeLaurentNormalized_forwardInnerLocHom` sends `divByS t D.s` to
`divByS (E.canonicalMap t) (E.canonicalMap D.s)`. Used in continuity. -/
theorem relativeLaurentNormalized_forwardInnerLocHom_divByS
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) (t : A) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
    relativeLaurentNormalized_forwardInnerLocHom E D hsub (divByS t D.s) =
      divByS (E.canonicalMap t) (E.canonicalMap D.s) := by
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  -- Unfold divByS to mk' form, then use lift_mk'_spec.
  change relativeLaurentNormalized_forwardInnerLocHom E D hsub
      (IsLocalization.mk' (Localization.Away D.s) t
        (⟨D.s, ⟨1, pow_one _⟩⟩ : Submonoid.powers D.s)) =
    divByS (E.canonicalMap t) (E.canonicalMap D.s)
  -- forwardInnerLocHom is IsLocalization.lift on the source localization.
  change IsLocalization.lift _ _ = _
  rw [IsLocalization.lift_mk'_spec]
  -- Goal: g t = g D.s * divByS (E.canonicalMap t) (E.canonicalMap D.s).
  -- g = (algebraMap (presheafValue E) _).comp E.canonicalMap.
  -- g t = algebraMap _ (E.canonicalMap t), g D.s = algebraMap _ (E.canonicalMap D.s).
  -- divByS (E.canonicalMap t) (E.canonicalMap D.s)
  -- = mk' (E.canonicalMap t) ⟨E.canonicalMap D.s, _⟩.
  -- By mk'_spec': algebraMap _ (E.canonicalMap D.s) * mk' (E.canonicalMap t) _
  --               = algebraMap _ (E.canonicalMap t).
  change (algebraMap (presheafValue E)
        (Localization.Away (E.canonicalMap D.s))).comp E.canonicalMap t = _
  simp only [RingHom.comp_apply]
  show algebraMap (presheafValue E) (Localization.Away (E.canonicalMap D.s))
      (E.canonicalMap t) = _
  unfold divByS
  exact (IsLocalization.mk'_spec' (Localization.Away (E.canonicalMap D.s))
    (E.canonicalMap t)
    (⟨E.canonicalMap D.s, ⟨1, pow_one _⟩⟩ : Submonoid.powers (E.canonicalMap D.s))).symm

/-! ### Continuity of `relativeLaurentNormalized_forwardInnerLocHom`

By `locTopology_continuous_lift`, decomposing the proof into:
* `hf_alg`: continuity of forwardInner ∘ algebraMap A from A to target.
  Composite equals `algebraMap_{presheafValue E → Loc} ∘ E.canonicalMap`,
  both continuous (`canonicalMap_continuous E`, `algebraMap_continuous_loc D_at_E`).
* `hpow`: forwardInner(divByS t D.s) = divByS (E.canonicalMap t) (E.canonicalMap D.s)
  ∈ locSubring of D_at_E (since E.canonicalMap t ∈ D_at_E.T), hence power-bounded
  in D_at_E.topology by `isPowerBounded_of_mem_locSubring`. -/

/-- Continuity of `relativeLaurentNormalized_forwardInnerLocHom`. -/
theorem relativeLaurentNormalized_forwardInnerLocHom_continuous
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
    letI : DecidableEq (presheafValue E) := Classical.decEq _
    @Continuous _ _ D.topology
      (relativeRationalLocData_laurentNormalized E D hsub).topology
      (relativeLaurentNormalized_forwardInnerLocHom E D hsub) := by
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  letI D_at_E_data : RationalLocData (presheafValue E) :=
    relativeRationalLocData_laurentNormalized E D hsub
  -- Set up target topology, ring, etc. (D_at_E_data.s = E.canonicalMap D.s by rfl)
  letI tgtTop : TopologicalSpace (Localization.Away D_at_E_data.s) := D_at_E_data.topology
  letI : TopologicalSpace (Localization.Away (E.canonicalMap D.s)) := tgtTop
  letI : IsTopologicalRing (Localization.Away D_at_E_data.s) := D_at_E_data.isTopologicalRing
  letI : IsTopologicalRing (Localization.Away (E.canonicalMap D.s)) :=
    D_at_E_data.isTopologicalRing
  letI : IsTopologicalAddGroup (Localization.Away D_at_E_data.s) :=
    D_at_E_data.isTopologicalAddGroup
  letI : IsTopologicalAddGroup (Localization.Away (E.canonicalMap D.s)) :=
    D_at_E_data.isTopologicalAddGroup
  -- Target is nonarchimedean ring (needed by locTopology_continuous_lift).
  haveI naTgt : @NonarchimedeanRing (Localization.Away D_at_E_data.s) _ tgtTop :=
    (locBasis D_at_E_data.P D_at_E_data.T D_at_E_data.s D_at_E_data.hopen).nonarchimedean
  haveI : @NonarchimedeanRing (Localization.Away (E.canonicalMap D.s)) _
      D_at_E_data.topology := naTgt
  -- hf_alg: continuity of forwardInner ∘ algebraMap A from A to target.
  have hf_alg : @Continuous A _ _ D_at_E_data.topology
      ((relativeLaurentNormalized_forwardInnerLocHom E D hsub).comp
        (algebraMap A (Localization.Away D.s))) := by
    -- forwardInner ∘ algebraMap A = algebraMap (presheafValue E) _ ∘ E.canonicalMap.
    have heq : (relativeLaurentNormalized_forwardInnerLocHom E D hsub).comp
        (algebraMap A (Localization.Away D.s)) =
        (algebraMap (presheafValue E) (Localization.Away (E.canonicalMap D.s))).comp
          E.canonicalMap := by
      ext a
      simp only [RingHom.comp_apply]
      exact IsLocalization.Away.lift_eq D.s
        (relativeLaurentNormalized_Ds_isUnit_in_Loc E D hsub) a
    rw [heq]
    exact (algebraMap_continuous_loc D_at_E_data).comp (canonicalMap_continuous E)
  -- hpow: forwardInner(divByS t D.s) is power-bounded for t ∈ D.T.
  have hpow : ∀ t ∈ D.T, @TopologicalRing.IsPowerBounded _ _ D_at_E_data.topology
      (relativeLaurentNormalized_forwardInnerLocHom E D hsub (divByS t D.s)) := by
    intro t ht
    -- Compute the image.
    rw [relativeLaurentNormalized_forwardInnerLocHom_divByS]
    -- divByS (E.canonicalMap t) (E.canonicalMap D.s) ∈ locSubring of D_at_E_data.
    apply isPowerBounded_of_mem_locSubring D_at_E_data
    -- D_at_E_data.T = D.T.image E.canonicalMap, so E.canonicalMap t ∈ T.
    exact divByS_mem_locSubring D_at_E_data.P D_at_E_data.T D_at_E_data.s
      (Finset.mem_image.mpr ⟨t, ht, rfl⟩)
  -- Apply locTopology_continuous_lift.
  exact locTopology_continuous_lift D.P D.T D.s D.hopen
    (relativeLaurentNormalized_forwardInnerLocHom E D hsub) hf_alg hpow

/-! ### Forward completion hom (LaurentNormalized case)

`forwardToCompletion := D_at_E.coeRingHom ∘ forwardInnerLocHom` is a continuous
hom from `Loc_A(D.s)` (with D.topology) to `presheafValue D_at_E`. Extend it via
`UniformSpace.Completion.extensionHom` to `presheafValue D → presheafValue D_at_E`. -/

/-- Composite forwardToCompletion: `Loc_A(D.s) →+* presheafValue D_at_E`. -/
noncomputable def relativeLaurentNormalized_forwardToCompletion
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
    letI : DecidableEq (presheafValue E) := Classical.decEq _
    Localization.Away D.s →+*
      presheafValue (relativeRationalLocData_laurentNormalized E D hsub) :=
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  (relativeRationalLocData_laurentNormalized E D hsub).coeRingHom.comp
    (relativeLaurentNormalized_forwardInnerLocHom E D hsub)

/-- forwardToCompletion is continuous (D.topology → presheafValue D_at_E's topology). -/
theorem relativeLaurentNormalized_forwardToCompletion_continuous
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    @Continuous _ _ D.topology _
      (relativeLaurentNormalized_forwardToCompletion E D hsub) := by
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  letI D_at_E_data : RationalLocData (presheafValue E) :=
    relativeRationalLocData_laurentNormalized E D hsub
  -- Source topology setup.
  letI : TopologicalSpace (Localization.Away D.s) := D.topology
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  -- Target topology setup (intermediate Loc, before completion).
  letI tgtTop : TopologicalSpace (Localization.Away D_at_E_data.s) := D_at_E_data.topology
  letI : TopologicalSpace (Localization.Away (E.canonicalMap D.s)) := tgtTop
  letI : IsTopologicalRing (Localization.Away D_at_E_data.s) :=
    D_at_E_data.isTopologicalRing
  letI : IsTopologicalRing (Localization.Away (E.canonicalMap D.s)) :=
    D_at_E_data.isTopologicalRing
  letI : UniformSpace (Localization.Away D_at_E_data.s) := D_at_E_data.uniformSpace
  letI : UniformSpace (Localization.Away (E.canonicalMap D.s)) := D_at_E_data.uniformSpace
  letI : IsUniformAddGroup (Localization.Away D_at_E_data.s) :=
    D_at_E_data.isUniformAddGroup
  letI : IsUniformAddGroup (Localization.Away (E.canonicalMap D.s)) :=
    D_at_E_data.isUniformAddGroup
  -- Decompose: forwardToCompletion = D_at_E.coeRingHom ∘ forwardInner.
  -- coeRingHom is continuous (uniform completion coercion).
  have hcoe : @Continuous _ _ D_at_E_data.topology
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D_at_E_data.uniformSpace))
      D_at_E_data.coeRingHom :=
    @UniformSpace.Completion.continuous_coe _ D_at_E_data.uniformSpace
  -- forwardInner is continuous by our prior theorem.
  have hinner : @Continuous _ _ D.topology D_at_E_data.topology
      (relativeLaurentNormalized_forwardInnerLocHom E D hsub) :=
    relativeLaurentNormalized_forwardInnerLocHom_continuous E D hsub
  -- Composition is continuous.
  change @Continuous _ _ D.topology _
    (D_at_E_data.coeRingHom.comp
      (relativeLaurentNormalized_forwardInnerLocHom E D hsub))
  exact hcoe.comp hinner

/-- The forward completion hom: presheafValue D →+* presheafValue D_at_E. -/
noncomputable def relativeLaurentNormalized_forwardHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
    letI : DecidableEq (presheafValue E) := Classical.decEq _
    presheafValue D →+*
      presheafValue (relativeRationalLocData_laurentNormalized E D hsub) :=
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  UniformSpace.Completion.extensionHom
    (relativeLaurentNormalized_forwardToCompletion E D hsub)
    (relativeLaurentNormalized_forwardToCompletion_continuous E D hsub)

/-! ### Backward completion direction (LaurentNormalized case)

backwardLocHom : `Loc_{presheafValue E}(E.canonicalMap D.s) → presheafValue D`
is already in place (defined above). We:
1. Prove its continuity (D_at_E.topology → presheafValue D topology) via
   `locTopology_continuous_lift` at the presheafValue E level.
2. Build backwardHom by extending through the completion of the source. -/

/-- `backwardLocHom` sends `divByS (E.canonicalMap t) (E.canonicalMap D.s)` to
`D.coeRingHom (divByS t D.s)` for `t : A`. -/
theorem relativeLaurentNormalized_backwardLocHom_divByS
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) (t : A) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
    relativeLaurentNormalized_backwardLocHom E D hsub
      (divByS (E.canonicalMap t) (E.canonicalMap D.s)) =
      D.coeRingHom (divByS t D.s) := by
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  -- Unfold divByS in source.
  change relativeLaurentNormalized_backwardLocHom E D hsub
      (IsLocalization.mk' (Localization.Away (E.canonicalMap D.s))
        (E.canonicalMap t)
        (⟨E.canonicalMap D.s, ⟨1, pow_one _⟩⟩ : Submonoid.powers (E.canonicalMap D.s))) =
    D.coeRingHom (divByS t D.s)
  change IsLocalization.lift _ _ = _
  rw [IsLocalization.lift_mk'_spec]
  -- Goal: g (E.canonicalMap t) = g (E.canonicalMap D.s) * D.coeRingHom (divByS t D.s)
  -- where g = restrictionMapHom E D hsub.
  -- restrictionMapHom E D hsub (E.canonicalMap a) = D.canonicalMap a
  -- by restrictionMapHom_canonicalMap.
  change restrictionMapHom E D hsub (E.canonicalMap t) =
    restrictionMapHom E D hsub (E.canonicalMap D.s) * _
  rw [restrictionMapHom_canonicalMap, restrictionMapHom_canonicalMap]
  -- Goal: D.canonicalMap t = D.canonicalMap D.s * D.coeRingHom (divByS t D.s)
  change D.canonicalMap t =
    D.coeRingHom (algebraMap A (Localization.Away D.s) D.s) *
    D.coeRingHom (divByS t D.s)
  -- D.canonicalMap t = D.coeRingHom (algebraMap A _ t)
  --                   = D.coeRingHom (algebraMap A _ D.s * divByS t D.s) [by mk'_spec']
  --                   = D.coeRingHom (algebraMap A _ D.s) · D.coeRingHom (divByS t D.s).
  rw [← D.coeRingHom.map_mul,
    show algebraMap A (Localization.Away D.s) D.s * divByS t D.s =
      algebraMap A (Localization.Away D.s) t from
      IsLocalization.mk'_spec' (Localization.Away D.s) t
        (⟨D.s, ⟨1, pow_one _⟩⟩ : Submonoid.powers D.s)]
  rfl

/-- backwardLocHom is continuous (D_at_E.topology → presheafValue D topology). -/
theorem relativeLaurentNormalized_backwardLocHom_continuous
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
    letI : DecidableEq (presheafValue E) := Classical.decEq _
    @Continuous _ _ (relativeRationalLocData_laurentNormalized E D hsub).topology
      _ (relativeLaurentNormalized_backwardLocHom E D hsub) := by
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  letI D_at_E_data : RationalLocData (presheafValue E) :=
    relativeRationalLocData_laurentNormalized E D hsub
  -- Source topology setup.
  letI srcTop : TopologicalSpace (Localization.Away D_at_E_data.s) :=
    D_at_E_data.topology
  letI : TopologicalSpace (Localization.Away (E.canonicalMap D.s)) := srcTop
  letI : IsTopologicalRing (Localization.Away D_at_E_data.s) :=
    D_at_E_data.isTopologicalRing
  letI : IsTopologicalRing (Localization.Away (E.canonicalMap D.s)) :=
    D_at_E_data.isTopologicalRing
  -- Target is nonarchimedean ring (needed by locTopology_continuous_lift).
  haveI : NonarchimedeanRing (presheafValue D) := presheafValueNonarchimedeanRing D
  -- hf_alg: continuity of backwardLocHom ∘ algebraMap (presheafValue E).
  -- The composite equals `restrictionMapHom E D hsub` by backwardLocHom_algebraMap.
  -- restrictionMapHom is continuous by restrictionMapHom_continuous.
  have hf_alg :
      @Continuous _ _ _ _
        ((relativeLaurentNormalized_backwardLocHom E D hsub).comp
          (algebraMap (presheafValue E) (Localization.Away D_at_E_data.s))) := by
    have heq : (relativeLaurentNormalized_backwardLocHom E D hsub).comp
        (algebraMap (presheafValue E) (Localization.Away D_at_E_data.s)) =
        restrictionMapHom E D hsub := by
      ext b
      simp only [RingHom.comp_apply]
      exact relativeLaurentNormalized_backwardLocHom_algebraMap E D hsub b
    rw [heq]
    exact restrictionMapHom_continuous E D hsub
  -- hpow: backwardLocHom(divByS t' s_at_E) is power-bounded for t' ∈ D_at_E_data.T.
  have hpow : ∀ t' ∈ D_at_E_data.T,
      TopologicalRing.IsPowerBounded
        (relativeLaurentNormalized_backwardLocHom E D hsub (divByS t' D_at_E_data.s)) := by
    intro t' ht'
    -- T_at_E = D.T.image E.canonicalMap; so t' = E.canonicalMap t for some t ∈ D.T.
    obtain ⟨t, ht, ht'_eq⟩ := Finset.mem_image.mp ht'
    subst ht'_eq
    -- D_at_E_data.s = E.canonicalMap D.s definitionally.
    -- Compute the image: backwardLocHom (divByS (E.canonicalMap t) (E.canonicalMap D.s))
    --                  = D.coeRingHom (divByS t D.s).
    change TopologicalRing.IsPowerBounded
      ((relativeLaurentNormalized_backwardLocHom E D hsub)
        (divByS (E.canonicalMap t) (E.canonicalMap D.s)))
    rw [relativeLaurentNormalized_backwardLocHom_divByS]
    -- D.coeRingHom (divByS t D.s) is in D.coeRingHom '' locSubring D, which is bounded.
    apply (CompletionLocalization.coeRingHom_image_locSubring_isBounded D).subset
    rintro _ ⟨n, rfl⟩
    -- Powers of D.coeRingHom (divByS t D.s) stay in coeRingHom-image of locSubring D.
    change D.coeRingHom (divByS t D.s) ^ n ∈ _
    rw [← map_pow]
    exact ⟨(divByS t D.s) ^ n,
      (locSubring _ _ _).pow_mem (divByS_mem_locSubring D.P D.T D.s ht) n, rfl⟩
  -- Apply locTopology_continuous_lift.
  exact locTopology_continuous_lift D_at_E_data.P D_at_E_data.T D_at_E_data.s
    D_at_E_data.hopen (relativeLaurentNormalized_backwardLocHom E D hsub)
    hf_alg hpow

/-- The backward completion hom: presheafValue D_at_E →+* presheafValue D. -/
noncomputable def relativeLaurentNormalized_backwardHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
    letI : DecidableEq (presheafValue E) := Classical.decEq _
    presheafValue (relativeRationalLocData_laurentNormalized E D hsub) →+*
      presheafValue D :=
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  letI D_at_E_data : RationalLocData (presheafValue E) :=
    relativeRationalLocData_laurentNormalized E D hsub
  letI : UniformSpace (Localization.Away D_at_E_data.s) := D_at_E_data.uniformSpace
  letI : IsUniformAddGroup (Localization.Away D_at_E_data.s) :=
    D_at_E_data.isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away D_at_E_data.s) :=
    D_at_E_data.isTopologicalRing
  UniformSpace.Completion.extensionHom
    (relativeLaurentNormalized_backwardLocHom E D hsub)
    (relativeLaurentNormalized_backwardLocHom_continuous E D hsub)

/-! ### Coe identifications for completion extension -/

/-- Forward completion hom on `D.coeRingHom a` equals `forwardToCompletion a`. -/
theorem relativeLaurentNormalized_forwardHom_coeRingHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s)
    (a : Localization.Away D.s) :
    relativeLaurentNormalized_forwardHom E D hsub (D.coeRingHom a) =
      relativeLaurentNormalized_forwardToCompletion E D hsub a := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  exact UniformSpace.Completion.extensionHom_coe _ _ a

/-- Backward completion hom on `D_at_E.coeRingHom b` equals `backwardLocHom b`. -/
theorem relativeLaurentNormalized_backwardHom_coeRingHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s)
    (b : Localization.Away (E.canonicalMap D.s)) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
    letI : DecidableEq (presheafValue E) := Classical.decEq _
    letI D_at_E_data : RationalLocData (presheafValue E) :=
      relativeRationalLocData_laurentNormalized E D hsub
    relativeLaurentNormalized_backwardHom E D hsub (D_at_E_data.coeRingHom b) =
      relativeLaurentNormalized_backwardLocHom E D hsub b := by
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  letI D_at_E_data : RationalLocData (presheafValue E) :=
    relativeRationalLocData_laurentNormalized E D hsub
  letI : UniformSpace (Localization.Away D_at_E_data.s) := D_at_E_data.uniformSpace
  letI : UniformSpace (Localization.Away (E.canonicalMap D.s)) := D_at_E_data.uniformSpace
  letI : IsUniformAddGroup (Localization.Away D_at_E_data.s) :=
    D_at_E_data.isUniformAddGroup
  letI : IsUniformAddGroup (Localization.Away (E.canonicalMap D.s)) :=
    D_at_E_data.isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away D_at_E_data.s) :=
    D_at_E_data.isTopologicalRing
  letI : IsTopologicalRing (Localization.Away (E.canonicalMap D.s)) :=
    D_at_E_data.isTopologicalRing
  exact UniformSpace.Completion.extensionHom_coe _ _ b

/-! ### Round-trip identity at the locHom level (backward ∘ forwardInner)

`backwardLocHom ∘ forwardInnerLocHom = D.coeRingHom` as ring homs
`Loc_A(D.s) →+* presheafValue D`. Both extend `D.canonicalMap : A →+* presheafValue D`
to the localization, and by `IsLocalization.ringHom_ext` they're equal. -/
theorem relativeLaurentNormalized_backward_forward_locHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    (relativeLaurentNormalized_backwardLocHom E D hsub).comp
      (relativeLaurentNormalized_forwardInnerLocHom E D hsub) =
      D.coeRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers D.s)
  ext a
  simp only [RingHom.comp_apply]
  -- LHS = backwardLocHom (forwardInner (algebraMap A _ a))
  --     = backwardLocHom (algebraMap (presheafValue E) _ (E.canonicalMap a))
  --     = restrictionMapHom E D hsub (E.canonicalMap a)
  --     = D.canonicalMap a = D.coeRingHom (algebraMap A _ a).
  rw [relativeLaurentNormalized_forwardInnerLocHom_algebraMap,
    relativeLaurentNormalized_backwardLocHom_algebraMap,
    restrictionMapHom_canonicalMap]
  rfl

/-- Round-trip identity at the completion level: `backwardHom ∘ forwardHom = id`
on `presheafValue D`. -/
theorem relativeLaurentNormalized_backwardHom_comp_forwardHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
    letI : DecidableEq (presheafValue E) := Classical.decEq _
    (relativeLaurentNormalized_backwardHom E D hsub).comp
      (relativeLaurentNormalized_forwardHom E D hsub) = RingHom.id _ := by
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  letI D_at_E_data : RationalLocData (presheafValue E) :=
    relativeRationalLocData_laurentNormalized E D hsub
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : UniformSpace (Localization.Away D_at_E_data.s) := D_at_E_data.uniformSpace
  letI : UniformSpace (Localization.Away (E.canonicalMap D.s)) := D_at_E_data.uniformSpace
  letI : IsUniformAddGroup (Localization.Away D_at_E_data.s) :=
    D_at_E_data.isUniformAddGroup
  letI : IsUniformAddGroup (Localization.Away (E.canonicalMap D.s)) :=
    D_at_E_data.isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away D_at_E_data.s) :=
    D_at_E_data.isTopologicalRing
  letI : IsTopologicalRing (Localization.Away (E.canonicalMap D.s)) :=
    D_at_E_data.isTopologicalRing
  apply RingHom.ext
  intro x
  change relativeLaurentNormalized_backwardHom E D hsub
      (relativeLaurentNormalized_forwardHom E D hsub x) = x
  refine @UniformSpace.Completion.ext' _ _ _ _ _ _ _
    ((UniformSpace.Completion.continuous_extension).comp
      UniformSpace.Completion.continuous_extension)
    continuous_id ?_ x
  intro a
  -- On dense subring D.coeRingHom a:
  --   forwardHom (D.coeRingHom a) = forwardToCompletion a
  --                                = D_at_E.coeRingHom (forwardInnerLocHom a)
  --   backwardHom (D_at_E.coeRingHom (forwardInnerLocHom a))
  --     = backwardLocHom (forwardInnerLocHom a)
  --     = D.coeRingHom a (by locHom round-trip)
  change relativeLaurentNormalized_backwardHom E D hsub
      (relativeLaurentNormalized_forwardHom E D hsub (D.coeRingHom a)) =
    D.coeRingHom a
  rw [relativeLaurentNormalized_forwardHom_coeRingHom]
  change relativeLaurentNormalized_backwardHom E D hsub
      ((relativeRationalLocData_laurentNormalized E D hsub).coeRingHom
        (relativeLaurentNormalized_forwardInnerLocHom E D hsub a)) =
    D.coeRingHom a
  rw [relativeLaurentNormalized_backwardHom_coeRingHom]
  -- Now: backwardLocHom (forwardInnerLocHom a) = D.coeRingHom a (locHom round-trip).
  exact DFunLike.congr_fun
    (relativeLaurentNormalized_backward_forward_locHom E D hsub) a

/-- Intertwining at A: `forwardHom (D.canonicalMap a) = D_at_E.canonicalMap (E.canonicalMap a)`
for `a : A`. -/
theorem relativeLaurentNormalized_forwardHom_canonicalMap
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) (a : A) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
    letI : DecidableEq (presheafValue E) := Classical.decEq _
    letI D_at_E_data : RationalLocData (presheafValue E) :=
      relativeRationalLocData_laurentNormalized E D hsub
    relativeLaurentNormalized_forwardHom E D hsub (D.canonicalMap a) =
      D_at_E_data.canonicalMap (E.canonicalMap a) := by
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  letI D_at_E_data : RationalLocData (presheafValue E) :=
    relativeRationalLocData_laurentNormalized E D hsub
  -- D.canonicalMap a = D.coeRingHom (algebraMap A _ a).
  change relativeLaurentNormalized_forwardHom E D hsub
      (D.coeRingHom (algebraMap A (Localization.Away D.s) a)) =
    D_at_E_data.coeRingHom
      (algebraMap (presheafValue E) (Localization.Away D_at_E_data.s) (E.canonicalMap a))
  rw [relativeLaurentNormalized_forwardHom_coeRingHom]
  change D_at_E_data.coeRingHom
      (relativeLaurentNormalized_forwardInnerLocHom E D hsub
        (algebraMap A (Localization.Away D.s) a)) =
    D_at_E_data.coeRingHom
      (algebraMap (presheafValue E) (Localization.Away D_at_E_data.s) (E.canonicalMap a))
  rw [relativeLaurentNormalized_forwardInnerLocHom_algebraMap]
  rfl

/-- Intertwining at presheafValue E: `forwardHom (restrictionMapHom E D hsub b)
= D_at_E.canonicalMap b` for `b : presheafValue E`. Extends the A-level
intertwining by `Completion.ext'` density. -/
theorem relativeLaurentNormalized_forwardHom_restrictionMapHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) (b : presheafValue E) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
    letI : DecidableEq (presheafValue E) := Classical.decEq _
    letI D_at_E_data : RationalLocData (presheafValue E) :=
      relativeRationalLocData_laurentNormalized E D hsub
    relativeLaurentNormalized_forwardHom E D hsub
      (restrictionMapHom E D hsub b) = D_at_E_data.canonicalMap b := by
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  letI D_at_E_data : RationalLocData (presheafValue E) :=
    relativeRationalLocData_laurentNormalized E D hsub
  letI : UniformSpace (Localization.Away E.s) := E.uniformSpace
  letI : IsUniformAddGroup (Localization.Away E.s) := E.isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away E.s) := E.isTopologicalRing
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  haveI : T2Space (presheafValue D_at_E_data) := presheafValueT2Space _
  set f : presheafValue E → presheafValue D_at_E_data := fun b =>
    relativeLaurentNormalized_forwardHom E D hsub (restrictionMapHom E D hsub b)
  set g : presheafValue E → presheafValue D_at_E_data := fun b =>
    D_at_E_data.canonicalMap b
  change f b = g b
  refine UniformSpace.Completion.ext' (f := f) (g := g) ?_ ?_ ?_ b
  · exact (UniformSpace.Completion.continuous_extension).comp
      (restrictionMapHom_continuous E D hsub)
  · exact canonicalMap_continuous _
  intro y
  -- On E.coeRingHom y for y ∈ Loc_A(E.s):
  -- Reduce by IsLocalization.ringHom_ext on (powers E.s) to A-level intertwining.
  change f (E.coeRingHom y) = g (E.coeRingHom y)
  simp only [f, g]
  -- The composition `f ∘ E.coeRingHom = g ∘ E.coeRingHom` as ring homs
  -- Loc_A(E.s) → presheafValue D_at_E.
  -- Both are ring homs; apply IsLocalization.ringHom_ext.
  let h1 : Localization.Away E.s →+* presheafValue D_at_E_data :=
    ((relativeLaurentNormalized_forwardHom E D hsub).comp
      (restrictionMapHom E D hsub)).comp E.coeRingHom
  let h2 : Localization.Away E.s →+* presheafValue D_at_E_data :=
    D_at_E_data.canonicalMap.comp E.coeRingHom
  change h1 y = h2 y
  have heq : h1 = h2 := by
    apply IsLocalization.ringHom_ext (Submonoid.powers E.s)
    ext a
    simp only [h1, h2, RingHom.comp_apply]
    change relativeLaurentNormalized_forwardHom E D hsub
        (restrictionMapHom E D hsub (E.canonicalMap a)) =
      D_at_E_data.canonicalMap (E.canonicalMap a)
    rw [restrictionMapHom_canonicalMap]
    exact relativeLaurentNormalized_forwardHom_canonicalMap E D hsub a
  exact DFunLike.congr_fun heq y

/-- Forward round-trip identity: `forwardHom ∘ backwardHom = id` on
`presheafValue D_at_E`. Proved by reducing via `Completion.ext'` to the
locHom-level identity that combines the full intertwining (for algebraMap-image)
with the divByS-image computation. -/
theorem relativeLaurentNormalized_forwardHom_comp_backwardHom
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
    letI : DecidableEq (presheafValue E) := Classical.decEq _
    (relativeLaurentNormalized_forwardHom E D hsub).comp
      (relativeLaurentNormalized_backwardHom E D hsub) = RingHom.id _ := by
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  letI D_at_E_data : RationalLocData (presheafValue E) :=
    relativeRationalLocData_laurentNormalized E D hsub
  letI : UniformSpace (Localization.Away D_at_E_data.s) := D_at_E_data.uniformSpace
  letI : UniformSpace (Localization.Away (E.canonicalMap D.s)) := D_at_E_data.uniformSpace
  letI : IsUniformAddGroup (Localization.Away D_at_E_data.s) :=
    D_at_E_data.isUniformAddGroup
  letI : IsUniformAddGroup (Localization.Away (E.canonicalMap D.s)) :=
    D_at_E_data.isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away D_at_E_data.s) :=
    D_at_E_data.isTopologicalRing
  letI : IsTopologicalRing (Localization.Away (E.canonicalMap D.s)) :=
    D_at_E_data.isTopologicalRing
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  apply RingHom.ext
  intro y
  change relativeLaurentNormalized_forwardHom E D hsub
      (relativeLaurentNormalized_backwardHom E D hsub y) = y
  refine @UniformSpace.Completion.ext' _ _ _ _ _ _ _
    ((UniformSpace.Completion.continuous_extension).comp
      UniformSpace.Completion.continuous_extension)
    continuous_id ?_ y
  intro b
  -- On D_at_E.coeRingHom b for b ∈ Loc_{presheafValue E}(E.canonicalMap D.s):
  --   backwardHom (D_at_E.coeRingHom b) = backwardLocHom b
  --   forwardHom (backwardLocHom b) = ? — need to compute.
  -- Both sides are ring homs Loc_{presheafValue E}(E.canonicalMap D.s) → presheafValue D_at_E.
  -- Apply IsLocalization.ringHom_ext on (Submonoid.powers (E.canonicalMap D.s)).
  change relativeLaurentNormalized_forwardHom E D hsub
      (relativeLaurentNormalized_backwardHom E D hsub (D_at_E_data.coeRingHom b)) =
    D_at_E_data.coeRingHom b
  rw [relativeLaurentNormalized_backwardHom_coeRingHom]
  -- Now: forwardHom (backwardLocHom b) = D_at_E.coeRingHom b.
  -- Both ring homs Loc → presheafValue D_at_E. Apply IsLocalization.ringHom_ext.
  let h1 : Localization.Away (E.canonicalMap D.s) →+* presheafValue D_at_E_data :=
    (relativeLaurentNormalized_forwardHom E D hsub).comp
      (relativeLaurentNormalized_backwardLocHom E D hsub)
  let h2 : Localization.Away (E.canonicalMap D.s) →+* presheafValue D_at_E_data :=
    D_at_E_data.coeRingHom
  change h1 b = h2 b
  have heq : h1 = h2 := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (E.canonicalMap D.s))
    ext b'
    simp only [h1, h2, RingHom.comp_apply]
    -- For algebraMap (presheafValue E) _ b' (b' ∈ presheafValue E):
    --   LHS = forwardHom (backwardLocHom (algebraMap b'))
    --       = forwardHom (restrictionMapHom E D hsub b')  [backwardLocHom_algebraMap]
    --       = D_at_E.canonicalMap b'                      [forwardHom_restrictionMapHom]
    -- RHS = D_at_E.coeRingHom (algebraMap b') = D_at_E.canonicalMap b' (by definition)
    change relativeLaurentNormalized_forwardHom E D hsub
        (relativeLaurentNormalized_backwardLocHom E D hsub
          (algebraMap (presheafValue E) _ b')) =
      D_at_E_data.coeRingHom (algebraMap (presheafValue E) _ b')
    rw [relativeLaurentNormalized_backwardLocHom_algebraMap,
      relativeLaurentNormalized_forwardHom_restrictionMapHom]
    rfl
  exact DFunLike.congr_fun heq b

/-! ### Final relative equivalence (LaurentNormalized case)

Package forward and backward homs as a RingEquiv. -/

/-- The relative equivalence: `presheafValue D ≃+* presheafValue D_at_E`
for LaurentNormalized D ⊆ E rationally. -/
noncomputable def relativeLaurentNormalized_equiv
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
    letI : DecidableEq (presheafValue E) := Classical.decEq _
    presheafValue D ≃+*
      presheafValue (relativeRationalLocData_laurentNormalized E D hsub) :=
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  { toFun := relativeLaurentNormalized_forwardHom E D hsub
    invFun := relativeLaurentNormalized_backwardHom E D hsub
    left_inv := fun x => DFunLike.congr_fun
      (relativeLaurentNormalized_backwardHom_comp_forwardHom E D hsub) x
    right_inv := fun y => DFunLike.congr_fun
      (relativeLaurentNormalized_forwardHom_comp_backwardHom E D hsub) y
    map_mul' := map_mul _
    map_add' := map_add _ }

/-- The relative equiv intertwines `restrictionMapHom E D hsub` with `D_at_E.canonicalMap`. -/
theorem relativeLaurentNormalized_equiv_intertwine
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (E : RationalLocData A)
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) (b : presheafValue E) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
    letI : DecidableEq (presheafValue E) := Classical.decEq _
    letI D_at_E_data : RationalLocData (presheafValue E) :=
      relativeRationalLocData_laurentNormalized E D hsub
    (relativeLaurentNormalized_equiv E D hsub) (restrictionMapHom E D hsub b) =
      D_at_E_data.canonicalMap b :=
  relativeLaurentNormalized_forwardHom_restrictionMapHom E D hsub b

end ValuationSpectrum

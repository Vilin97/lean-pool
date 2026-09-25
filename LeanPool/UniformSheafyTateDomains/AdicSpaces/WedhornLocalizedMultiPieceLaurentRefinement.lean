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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornMultiPieceLaurentRefinement
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalCompatFromTestFamily
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalArithmeticPerTChain

/-!
# Wedhorn 8.34(ii) — Localized multi-piece Laurent cover refinement (T171)

T054 (`WedhornMultiPieceLaurentRefinement.lean`) accepted the
**generic** per-piece Laurent cover refinement output
`MultiPieceLaurentCoverRefinementOutput`: at every `w ∈ Spa A A⁺` there
exists `τ ∈ T_test` with `w` in the σ-rescaled Laurent piece
`V_τ := rationalOpen ({(1 : A)}) (σ⁻¹ * τ)` and a per-piece
**singleton** residual on `V_τ`. T054 explicitly documents that the
**universal-over-`T_test`** lower-bound form
`∀ τ ∈ T_test, w.vle 1 (σ⁻¹ * τ)` is **mathematically false** at a
single `w` (T035 counter-example).

T170 (`WedhornLocalCompatFromTestFamily.lean`, commit `7cbf2d8`)
exposed the same obstruction in the **localized** setting: the
`h_per_piece_multi_lower` hypothesis of T169
(`h_T_D_multi_and_lower_bound_via_laurent_cover_refinement`, commit
`9d990df`) consumes `∀ t' ∈ T_D.image (algebraMap), w.vle 1 t'` per
`w` under f-membership, which is the **same false universal-over-`T_D`
lower-bound shape** at the localized level.

This file lands the **localized analogue** of T054's per-piece output
plus a **consumer reroute boundary** identifying the precise
cover-level assembly content needed to close the T168 α_T_D branch
honestly. The localized object specialises T054 at
`A := Localization.Away s` with the localized topology and plus-subring
instances, using `localizedTestFamily s T_D s_D` as the test family.

## What this file provides

* `LocalizedMultiPieceLaurentCoverRefinementOutput` — localized
  predicate naming T054's per-piece output at the localized level:
  at every `w ∈ Spa(Localization.Away s, ⁺)`, there exists
  `τ ∈ localizedTestFamily s T_D s_D` such that `w` lies in the
  σ_loc-rescaled Laurent piece together with a per-piece **singleton**
  lower-bound residual on that piece.

* `localizedMultiPieceLaurentCoverRefinementOutput_via_cor732` —
  bridge from localized Cor 7.32 σ-strict-domination to the localized
  per-piece output. Direct specialization of T054's
  `multiPieceLaurentCoverRefinementOutput_via_cor732` at
  `A := Localization.Away s` with the localized instances.

* `LocalizedAlphaTDBranchCoverLevelAssemblyResidual` — the **named
  cover-level assembly residual**: the precise compiled boundary
  identifying what additional content is needed beyond the per-piece
  singleton output to recover T168's α_T_D-branch conclusion. This
  isolates the missing Wedhorn Lemma 8.33 cover-level assembly content
  exactly.

* `h_T_test_compat_loc_branch_α_T_D_via_localized_multi_piece` — the
  **caller reroute**: composes the localized per-piece output with the
  cover-level assembly residual to produce T168's α_T_D-branch
  conclusion. Reduces the current T168/T169/T170 chain to the named
  cover-level assembly residual without invoking the false
  universal-over-`T_D` lower-bound clause.

## Why a separate file (not edits to T168/T169/T170 leaves)

* T168/T169/T170's existing chain consumes a hypothesis shape that is
  not achievable from generic Cor 7.32 + cover-refinement data (per
  T054). The reroute needs a different consumer interface — namely the
  per-piece singleton output — which is best presented in a fresh
  leaf file rather than threaded through the existing chain.

* The new declarations are purely additive; they do not modify
  T168/T169/T170 leaves, root imports, or final theorem signatures.

## Notes

* No root import (file is leaf-level relative to `Adic spaces.lean`;
  callers explicitly import as needed).
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* No `locSubring` integral-closedness, no T001/T004/T015/final/root/C1
  edits.
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

omit [IsTopologicalRing A] in
/-- **T171 localized version of T054's
`MultiPieceLaurentCoverRefinementOutput`**.

For `Localization.Away s` with `localizedTestFamily s T_D s_D` as test
family: at every `w ∈ Spa(Localization.Away s, ⁺)`, there exists
`τ ∈ localizedTestFamily s T_D s_D` such that:

* `w ∈ rationalOpen ({(1 : Localization.Away s)}) (σ_loc⁻¹ · τ)` —
  Laurent piece membership.
* `MultiElementLowerBoundResidualOnPiece V_τ ({σ_loc⁻¹ · τ})` —
  per-piece **singleton** lower-bound residual at the σ-rescaled
  element of the piece.

Defined as the specialisation of T054's
`MultiPieceLaurentCoverRefinementOutput` at `A := Localization.Away s`
with the localized topology + plus-subring instances and
`T_test := localizedTestFamily s T_D s_D`. -/
def LocalizedMultiPieceLaurentCoverRefinementOutput
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  MultiPieceLaurentCoverRefinementOutput
    (σ := σ_loc) (localizedTestFamily s T_D s_D)

omit [PlusSubring A] in
/-- **T171 bridge from localized Cor 7.32 σ-strict-domination to the
localized per-piece output**.

Direct specialization of T054's
`multiPieceLaurentCoverRefinementOutput_via_cor732` at
`A := Localization.Away s` with the localized topology + plus-subring
instances and `T_test := localizedTestFamily s T_D s_D`. The
σ-strict-domination hypothesis is the standard
`exists_dominating_unit_in_localization` output (also consumed by T169's
`h_T_D_multi_and_lower_bound_via_laurent_cover_refinement`, commit
`9d990df`). -/
theorem localizedMultiPieceLaurentCoverRefinementOutput_via_cor732
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
            ¬ w.vle τ (σ_loc : Localization.Away s)) :
    LocalizedMultiPieceLaurentCoverRefinementOutput
      P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  exact multiPieceLaurentCoverRefinementOutput_via_cor732 hσ_loc_dom

omit [PlusSubring A] in
/-- **T171 named cover-level assembly residual** for the localized
α_T_D branch.

This Prop precisely identifies what additional content is needed beyond
T171's per-piece singleton output (and beyond T170's multi-element
bound) to recover T168's α_T_D-branch conclusion via Wedhorn Lemma 8.33
cover-level assembly.

Specifically: from the localized per-piece output (per `w` an `τ` plus
the singleton residual on V_τ) plus the multi-element bound `w.vle (∏)
(algebraMap s_D)` from T170, the α_T_D-branch conclusion `∀ t' ∈
T_D.image (algebraMap), w.vle t' (algebraMap s_D)` plus `¬ w.vle
(algebraMap s_D) 0` requires a Wedhorn Lemma 8.33-style **cover-level
assembly** of per-piece per-`t'` upper bounds into a global per-`t'`
upper bound.

The honest residual content per `w` (case-split on the localized test-
family branch by `mem_localizedTestFamily_iff`):

* **`τ = algebraMap s_D` case** (V_{algebraMap s_D}): per-piece
  per-`t'` upper bound `∀ t' ∈ T_D.image (algebraMap), w.vle t'
  (algebraMap s_D)` on V_{algebraMap s_D}, derivable from
  `w.vle σ_loc (algebraMap s_D)` + per-element integrality.

* **`τ = algebraMap t` case** for `t ∈ T_D` (V_{algebraMap t}):
  per-piece per-`t'` upper bound on V_{algebraMap t}, derivable from
  `w.vle σ_loc (algebraMap t)` + the σ-strict-dom witness +
  case-specific arithmetic.

The named residual asks for the **conjunction** of these two
case-conditional bounds, which together cover Spa via T171's per-piece
output. T168's α_T_D-branch conclusion follows by case-split on the
piece membership τ + applying the per-piece bound. -/
def LocalizedAlphaTDBranchCoverLevelAssemblyResidual
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
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    w.vle ((σ_loc : Localization.Away s) *
        (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
      (algebraMap A (Localization.Away s) s) →
    ∀ τ ∈ localizedTestFamily s T_D s_D,
      w ∈ rationalOpen
          ({(1 : Localization.Away s)} : Finset (Localization.Away s))
          (((σ_loc⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) *
            τ) →
      (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle t' (algebraMap A (Localization.Away s) s_D)) ∧
      ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0

omit [PlusSubring A] in
/-- **T171 caller reroute**: from the localized per-piece output +
cover-level assembly residual, produce the T168 α_T_D-branch
conclusion.

This is the **honest reroute** of the T168 α_T_D branch route through
the corrected per-piece data, replacing the false universal-over-`T_D`
lower-bound clause with the named cover-level assembly residual that
exactly captures the genuine remaining content.

**Proof**: at each `w ∈ Spa` under f-membership, dispatch via the
localized per-piece output to obtain `τ ∈ localizedTestFamily` with
`w ∈ V_τ`, then apply the cover-level assembly residual at this τ. The
output is the per-`t'` upper bound + `s_D` non-vanishing — the exact
shape of T168's α_T_D-branch single-branch compatibility output.

**The cover-level assembly residual is the
strictly-stronger-than-pass-through compiled boundary** identified by
T171: it asks only for per-piece per-`t'` bounds (not the false
universal-over-`T_D` lower-bound clause), and its discharge is the
genuine remaining Wedhorn Lemma 8.33 / 8.34(ii) cover-level
arithmetic content. -/
theorem h_T_test_compat_loc_branch_α_T_D_via_localized_multi_piece
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_multi_piece :
      LocalizedMultiPieceLaurentCoverRefinementOutput
        P T s hopen T_D s_D σ_loc)
    (h_assembly :
      LocalizedAlphaTDBranchCoverLevelAssemblyResidual
        P T s hopen T_D s_D σ_loc) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
          (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle t' (algebraMap A (Localization.Away s) s_D)) ∧
            ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro _τ_strict _hτ_strict_mem w hw_spa hw_f _hστ_strict
  -- Dispatch via the localized per-piece output to find a piece-`τ`
  -- containing `w`, then apply the cover-level assembly at that piece.
  obtain ⟨τ, hτ_mem, hw_piece, _h_singleton_residual⟩ :=
    h_multi_piece w hw_spa
  exact h_assembly w hw_spa hw_f τ hτ_mem hw_piece

omit [PlusSubring A] in
/-- **T171 end-to-end caller**: composes the localized per-piece bridge
(from σ-strict-domination via T054 specialisation) with the cover-level
assembly residual to produce the α_T_D-branch conclusion.

Demonstrates the corrected route from the natural Cor 7.32
σ-strict-domination input + the named cover-level assembly residual,
through T171's localized multi-piece output, to the α_T_D-branch
single-branch compatibility output. -/
theorem h_T_test_compat_loc_branch_α_T_D_via_cor732_loc_and_assembly
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
    (h_assembly :
      LocalizedAlphaTDBranchCoverLevelAssemblyResidual
        P T s hopen T_D s_D σ_loc) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
          (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle t' (algebraMap A (Localization.Away s) s_D)) ∧
            ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 :=
  h_T_test_compat_loc_branch_α_T_D_via_localized_multi_piece
    P T s hopen T_D s_D σ_loc
    (localizedMultiPieceLaurentCoverRefinementOutput_via_cor732
      P T s hopen T_D s_D σ_loc hσ_loc_dom)
    h_assembly

omit [PlusSubring A] in
/-- **T171 (continued): full discharge of
`LocalizedAlphaTDBranchCoverLevelAssemblyResidual` via cover-refinement
factorization, per-element integrality, and product non-vanishing**.

Closes both branches of the cover-level assembly residual (`τ =
algebraMap s_D` and `τ = algebraMap t` for `t ∈ T_D`) **uniformly** —
the proof does not need to case-split on `τ`. The same arithmetic
chain works regardless of which Laurent piece `w` lies in.

Hypotheses (T170-style cover-refinement factorization data):

1. **Cover-refinement element factorization**:
   ```
   algebraMap A (Localization.Away s) s =
     (σ_loc : Localization.Away s) *
       algebraMap A (Localization.Away s) s_D *
       ∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t
   ```

2. **Per-element integrality of `T_D.image` at every `w`**:
   ```
   ∀ w ∈ Spa, ∀ t' ∈ T_D.image (algebraMap), w.vle t' 1
   ```

3. **Product non-vanishing at every `w` under f-membership**: from the
   cover-refinement element `f` non-degeneracy (the localized lift of
   the per-call hypothesis `¬ v.vle f 0` from
   `WedhornC1PerCallSupplyPerWCoverPiece`):
   ```
   ∀ w ∈ Spa, w.vle (σ_loc · ∏ T_D.image) (algebraMap s) →
     ¬ w.vle (∏ T_D.image) 0
   ```

Conclusion: `LocalizedAlphaTDBranchCoverLevelAssemblyResidual`.

**Proof** (τ-uniform):

* Step 1. Substitute factorization in f-membership and cancel `σ_loc`
  on the left via `vle_iff_mul_unit_left`:
  `w.vle (∏) (algebraMap s_D · ∏)`.

* Step 2. Apply `ValuativeRel.vle_mul_cancel` with product
  non-vanishing: `w.vle 1 (algebraMap s_D)`.

* Step 3. Per-`t'` upper bound: per-element integrality
  `w.vle t' 1` + step 2 + `w.vle_trans` →
  `w.vle t' (algebraMap s_D)`.

* Step 4. `s_D` non-vanishing: assume `w.vle (algebraMap s_D) 0`;
  combined with step 2 via `w.vle_trans`, derive `w.vle 1 0`, which
  contradicts `w.not_vle_one_zero`.

**Why τ-uniform**: the cover-level assembly residual's `τ` and piece
membership `hw_piece` enter the conclusion only as data; the proof
relies on f-membership + factorization + integrality + ∏ non-vanishing,
all of which are `τ`-independent. The residual was originally stated
case-conditional because Wedhorn 8.34(ii) PDF page 84's Laurent cover
refinement is naturally piece-conditional, but at the level of the
α_T_D-branch conclusion, the per-`t'` upper bound and `s_D`
non-vanishing factor through the global multi-bound chain that does
not require case analysis.

**Strictly stronger than a wrapper**: the per-`t'` upper bound and
`s_D` non-vanishing are **derived** from concrete factorization +
integrality + product non-vanishing, not assumed. The factorization is
the natural Wedhorn cover-refinement element relation; integrality is
the Tate condition on `T_D`; product non-vanishing is the
cover-refinement element `f` non-degeneracy. -/
theorem alphaTDBranchAssembly_via_factorization_integrality_prod_ne
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_factorization :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      algebraMap A (Localization.Away s) s =
        (σ_loc : Localization.Away s) *
          algebraMap A (Localization.Away s) s_D *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
    (h_T_D_image_int :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle t' (1 : Localization.Away s))
    (h_prod_ne :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        ¬ w.vle (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
          (0 : Localization.Away s)) :
    LocalizedAlphaTDBranchCoverLevelAssemblyResidual
      P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_f _τ _hτ _hw_piece
  letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
  set P_im := ∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t
    with hP_im_def
  -- Step 1: substitute factorization, then cancel σ_loc on the left.
  have hf_substituted : w.vle ((σ_loc : Localization.Away s) * P_im)
      ((σ_loc : Localization.Away s) *
        (algebraMap A (Localization.Away s) s_D * P_im)) := by
    rw [show (σ_loc : Localization.Away s) *
            (algebraMap A (Localization.Away s) s_D * P_im) =
          (σ_loc : Localization.Away s) *
            algebraMap A (Localization.Away s) s_D * P_im from by ring,
      ← h_factorization]
    exact hw_f
  have h_chain : w.vle P_im
      (algebraMap A (Localization.Away s) s_D * P_im) :=
    (vle_iff_mul_unit_left w σ_loc P_im
      (algebraMap A (Localization.Away s) s_D * P_im)).mp hf_substituted
  -- Step 2: cancel P_im via vle_mul_cancel using product non-vanishing.
  have hP_im_ne : ¬ w.vle P_im (0 : Localization.Away s) :=
    h_prod_ne w hw_spa hw_f
  have h_one_le_s_D : w.vle (1 : Localization.Away s)
      (algebraMap A (Localization.Away s) s_D) := by
    have h_chain' : w.vle ((1 : Localization.Away s) * P_im)
        (algebraMap A (Localization.Away s) s_D * P_im) := by
      rw [one_mul]; exact h_chain
    exact w.vle_mul_cancel hP_im_ne h_chain'
  -- Step 3: per-`t'` upper bound via integrality + transitivity.
  refine ⟨?_, ?_⟩
  · intro t' ht'
    have h_t'_int : w.vle t' (1 : Localization.Away s) :=
      h_T_D_image_int w hw_spa t' ht'
    exact w.vle_trans h_t'_int h_one_le_s_D
  · -- Step 4: `s_D` non-vanishing from `w.vle 1 (algebraMap s_D)`.
    intro h_s_D_zero
    exact w.not_vle_one_zero (w.vle_trans h_one_le_s_D h_s_D_zero)

omit [PlusSubring A] in
/-- **T171 (continued): full α_T_D-branch closer from concrete
factorization data**.

Composes the cover-level assembly discharge
(`alphaTDBranchAssembly_via_factorization_integrality_prod_ne`) with
T171's caller reroute `h_T_test_compat_loc_branch_α_T_D_via_cor732_loc_and_assembly`
to produce the α_T_D-branch's full single-branch compatibility output
**directly from**:

* localized Cor 7.32 σ-strict-domination over `localizedTestFamily`,
* cover-refinement element factorization
  `algebraMap s = σ_loc · algebraMap s_D · ∏ T_D.image`,
* per-element integrality of `T_D.image`,
* product non-vanishing under f-membership.

No `LocalizedAlphaTDBranchCoverLevelAssemblyResidual` hypothesis
required — this closer **fully discharges** the residual through the
arithmetic chain.

This is the **fully composed end-to-end caller** for T171's reroute,
demonstrating that the localized α_T_D-branch route is honestly
closeable from cover-refinement structural data alone (no false
universal-over-`T_D` lower bound, no σ-power-decay, no
`locSubring` integral-closedness). -/
theorem h_T_test_compat_loc_branch_α_T_D_via_factorization_integrality_prod_ne
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
    (h_factorization :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      algebraMap A (Localization.Away s) s =
        (σ_loc : Localization.Away s) *
          algebraMap A (Localization.Away s) s_D *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
    (h_T_D_image_int :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle t' (1 : Localization.Away s))
    (h_prod_ne :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        ¬ w.vle (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
          (0 : Localization.Away s)) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
          (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle t' (algebraMap A (Localization.Away s) s_D)) ∧
            ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 :=
  h_T_test_compat_loc_branch_α_T_D_via_cor732_loc_and_assembly
    P T s hopen T_D s_D σ_loc hσ_loc_dom
    (alphaTDBranchAssembly_via_factorization_integrality_prod_ne
      P T s hopen T_D s_D σ_loc h_factorization h_T_D_image_int h_prod_ne)

/-! ### T172: concrete producers for two of T171's three structural inputs

This section provides concrete producers for two of the three structural
inputs to `h_T_test_compat_loc_branch_α_T_D_via_factorization_integrality_prod_ne`
above:

* **`h_T_D_image_int_via_locSubring_membership`** — discharges the
  per-element integrality input `h_T_D_image_int` from the natural
  Tate-style hypothesis `∀ t ∈ T_D, algebraMap A (Loc s) t ∈ locSubring P T s`
  via `vle_one_of_mem_spa`. Uses the canonical
  `localizationLocSubringPlusSubring` plus-subring instance: each element
  of `locSubring P T s` is `(Loc s)⁺` by definition, hence `w.vle t' 1`
  at every `w ∈ Spa(Loc s, ⁺)`.

* **`h_prod_ne_via_factorization`** — discharges the product non-vanishing
  input `h_prod_ne` from `h_factorization` alone (no extra hypothesis).
  Uses the unit-ness of `algebraMap A (Loc s) s` (always true via
  `IsLocalization.Away.algebraMap_isUnit`): if the product `∏ T_D.image`
  vanished at `w`, then by `mul_vle_mul_right` the entire RHS of
  `h_factorization` would vanish, so `algebraMap s` would vanish — but
  it is a unit, contradiction.

After these producers, the only remaining structural input for
`h_T_test_compat_loc_branch_α_T_D_via_factorization_integrality_prod_ne`
is the cover-refinement element factorization `h_factorization`
(supplied as `s = σ_loc · s_D · ∏ pre_T_D` from the Wedhorn cover-piece
construction) plus the per-element locSubring membership of `T_D.image`
(naturally available when `T_D ⊆ P.A₀` via `algebraMap_mem_locSubring`,
or supplied directly by the cover-refinement caller).

The composed top-level caller
`h_T_test_compat_loc_branch_α_T_D_via_factorization_locSubring_membership`
exposes only these two remaining inputs (plus the standard Cor 7.32
σ-strict-domination output). -/

omit [PlusSubring A] in
/-- **T172: `h_T_D_image_int` supplier from per-element locSubring
membership of `T_D.image`**.

Discharges the per-element integrality input `h_T_D_image_int` of
`alphaTDBranchAssembly_via_factorization_integrality_prod_ne` from the
natural hypothesis that each `t ∈ T_D` has its `algebraMap` image inside
`locSubring P T s`.

**Proof**: at each `w ∈ Spa(Loc s, ⁺)` and `t' ∈ T_D.image (algebraMap)`,
extract a preimage `t ∈ T_D` with `algebraMap t = t'`. The hypothesis
gives `algebraMap t ∈ locSubring P T s = (Loc s)⁺`; `vle_one_of_mem_spa`
upgrades this to `w.vle (algebraMap t) 1`, which is `w.vle t' 1` after
substitution.

The hypothesis `∀ t ∈ T_D, algebraMap t ∈ locSubring P T s` is the
natural Tate-style integrality of `T_D`'s `algebraMap`-image — naturally
available when `T_D ⊆ P.A₀` (via `algebraMap_mem_locSubring`), or
supplied directly by the cover-refinement caller. -/
theorem h_T_D_image_int_via_locSubring_membership
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A)
    (h_T_D_in_locSubring :
      ∀ t ∈ T_D,
        algebraMap A (Localization.Away s) t ∈ locSubring P T s) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle t' (1 : Localization.Away s) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa t' ht'
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht'
  exact vle_one_of_mem_spa hw_spa (h_T_D_in_locSubring t ht)

omit [PlusSubring A] in
/-- **T172: `h_prod_ne` supplier from `h_factorization` + α s being a unit**.

Discharges the product non-vanishing input `h_prod_ne` of
`alphaTDBranchAssembly_via_factorization_integrality_prod_ne` from
`h_factorization` alone, using the always-available
`IsLocalization.Away.algebraMap_isUnit` (since `s` is inverted in
`Localization.Away s`, `algebraMap s` is a unit).

**Proof**: assume `w.vle (∏ T_D.image) 0` (the product vanishes at
`w`). Multiply by `(σ_loc : Loc s) * algebraMap s_D` on the left via
`ValuativeRel.mul_vle_mul_right` to get
`w.vle ((σ_loc : Loc s) * algebraMap s_D * ∏ T_D.image)
       ((σ_loc : Loc s) * algebraMap s_D * 0)`; simplify the right side
to `0`. By `h_factorization`, the left side equals `algebraMap s`, so
`w.vle (algebraMap s) 0`. But `algebraMap s` is a unit in `Loc s`
(`IsLocalization.Away.algebraMap_isUnit`), so
`not_vle_zero_of_isUnit` gives the contradiction.

This producer requires neither f-membership nor the σ-strict-domination
hypothesis — `h_factorization` alone forces product non-vanishing
through the unit structure of `algebraMap s` in `Loc s`. -/
theorem h_prod_ne_via_factorization
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_factorization :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      algebraMap A (Localization.Away s) s =
        (σ_loc : Localization.Away s) *
          algebraMap A (Localization.Away s) s_D *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s) →
      ¬ w.vle (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
        (0 : Localization.Away s) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w _hw_spa _hw_f h_prod_zero
  letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
  -- α s is a unit in Loc s by IsLocalization.Away.
  have h_α_s_unit :
      IsUnit (algebraMap A (Localization.Away s) s) :=
    IsLocalization.Away.algebraMap_isUnit (S := Localization.Away s) s
  have h_α_s_ne :
      ¬ w.vle (algebraMap A (Localization.Away s) s) 0 :=
    not_vle_zero_of_isUnit h_α_s_unit w
  apply h_α_s_ne
  -- Goal: w.vle (algebraMap s) 0. Substitute via h_factorization.
  rw [h_factorization]
  -- Goal: w.vle (σ_loc · algebraMap s_D · ∏ T_D.image) 0.
  -- Multiply h_prod_zero by (σ_loc · algebraMap s_D) on the left
  -- (`mul_vle_mul_right` puts the multiplier on the LEFT in the result).
  have h_step :
      w.vle ((σ_loc : Localization.Away s) *
          algebraMap A (Localization.Away s) s_D *
          ∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
        ((σ_loc : Localization.Away s) *
          algebraMap A (Localization.Away s) s_D *
          (0 : Localization.Away s)) :=
    ValuativeRel.mul_vle_mul_right h_prod_zero
      ((σ_loc : Localization.Away s) *
        algebraMap A (Localization.Away s) s_D)
  rw [mul_zero] at h_step
  exact h_step

omit [PlusSubring A] in
/-- **T172: composed top-level caller** for the α_T_D-branch closer
through T172's two concrete producers.

Composes:
* T172's `h_T_D_image_int_via_locSubring_membership` producer for the
  per-element integrality input `h_T_D_image_int`,
* T172's `h_prod_ne_via_factorization` producer for the product
  non-vanishing input `h_prod_ne`,
* T171's `h_T_test_compat_loc_branch_α_T_D_via_factorization_integrality_prod_ne`
  closer.

Produces the α_T_D-branch single-branch compatibility output directly
from:

* localized Cor 7.32 σ-strict-domination over `localizedTestFamily`
  (`hσ_loc_dom`, the standard
  `exists_dominating_unit_in_localization` output);
* cover-refinement element factorization `h_factorization`;
* per-element locSubring membership `h_T_D_in_locSubring` (the natural
  Tate-style integrality of `T_D`'s `algebraMap`-image, available when
  `T_D ⊆ P.A₀`).

No `h_T_D_image_int` hypothesis or `h_prod_ne` hypothesis required —
both are dispatched through T172's producers. The remaining structural
input is the cover-refinement element factorization, supplied by the
Wedhorn cover-piece construction at the localized level. -/
theorem h_T_test_compat_loc_branch_α_T_D_via_factorization_locSubring_membership
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
    (h_factorization :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      algebraMap A (Localization.Away s) s =
        (σ_loc : Localization.Away s) *
          algebraMap A (Localization.Away s) s_D *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
    (h_T_D_in_locSubring :
      ∀ t ∈ T_D,
        algebraMap A (Localization.Away s) t ∈ locSubring P T s) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
          (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle t' (algebraMap A (Localization.Away s) s_D)) ∧
            ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 :=
  h_T_test_compat_loc_branch_α_T_D_via_factorization_integrality_prod_ne
    P T s hopen T_D s_D σ_loc hσ_loc_dom h_factorization
    (h_T_D_image_int_via_locSubring_membership P T s hopen T_D
      h_T_D_in_locSubring)
    (h_prod_ne_via_factorization P T s hopen T_D s_D σ_loc h_factorization)

/-! ### T173: concrete suppliers for T172's two remaining structural inputs

This section discharges T172's remaining structural inputs to
`h_T_test_compat_loc_branch_α_T_D_via_factorization_locSubring_membership`:

* `h_T_D_in_locSubring`: from the natural Wedhorn / cover-refinement
  hypothesis `T_D ⊆ P.A₀`, produced via `algebraMap_mem_locSubring`.

* `h_factorization`: from T170/T171's existing cover-refinement element
  identity `h_alg : algebraMap f = σ_loc · ∏ T_D.image` (the Cor 7.32
  σ-strict-domination's cover-refinement output) plus the cover-base
  factorization `s = s_D · f` in `A` (the natural Wedhorn 8.34(ii)
  factorization at the cover-base level).

The composed end-to-end caller
`h_T_test_compat_loc_branch_α_T_D_via_h_alg_and_subset_A₀` exposes
only the standard Cor 7.32 σ-strict-domination output, the existing
cover-refinement element identity `h_alg`, and the natural cover-base
factorization `s = s_D · f` and `T_D ⊆ P.A₀` hypotheses — both directly
expressible from the localized Wedhorn cover-piece pipeline. -/

omit [IsTopologicalRing A] [PlusSubring A] in
/-- **T173: `h_T_D_in_locSubring` supplier from `T_D ⊆ P.A₀`**.

Discharges T172's `h_T_D_in_locSubring` input from the natural
Wedhorn/cover-refinement hypothesis `T_D ⊆ P.A₀`. Each `t ∈ T_D` then
has its `algebraMap`-image in `locSubring P T s` via the existing
`algebraMap_mem_locSubring` API (in `LocalizationTopology.lean:72`). -/
theorem h_T_D_in_locSubring_of_subset_A₀
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (T_D : Finset A)
    (hT_D_le_A₀ : ∀ t ∈ T_D, t ∈ P.A₀) :
    ∀ t ∈ T_D,
      algebraMap A (Localization.Away s) t ∈ locSubring P T s :=
  fun t ht ↦ algebraMap_mem_locSubring P T s (hT_D_le_A₀ t ht)

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] in
/-- **T173: `h_factorization` supplier from `h_alg` + `s = s_D · f`**.

Discharges T172's `h_factorization` input from T170/T171's existing
cover-refinement element identity
`h_alg : algebraMap f = σ_loc · ∏ T_D.image` (the Cor 7.32 σ-strict-
domination's cover-refinement output, see e.g.
`rationalOpen_subset_base_via_M_power_decay`'s `h_alg` parameter in
`Adic spaces/WedhornLocalCor732ToFactoredChain.lean:174–178`) plus the
natural Wedhorn cover-base factorization `s = s_D · f` in `A`.

**Proof**: substitute `s = s_D · f` into `algebraMap s`:
```
algebraMap s = algebraMap (s_D · f) = algebraMap s_D · algebraMap f
             = algebraMap s_D · (σ_loc · ∏ T_D.image)        -- by h_alg
             = σ_loc · algebraMap s_D · ∏ T_D.image           -- commutativity
```

The cover-base factorization `s = s_D · f` is the Wedhorn 8.34(ii) /
Lemma 8.33 algebraic identity: the cover base denominator `s` factors
as the cover-piece denominator `s_D` times the cover-refinement element
`f`. This is the natural cover-refinement structural relation; for the
Cor 7.32 / `exists_dominating_unit_in_localization` output, `f` is
constructed precisely so that `algebraMap f` factorizes through `σ_loc`. -/
theorem h_factorization_via_h_alg_and_s_factor_eq
    (s : A)
    (T_D : Finset A) (s_D : A) (f : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_alg :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      algebraMap A (Localization.Away s) f =
        (σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
    (h_s_factor : s = s_D * f) :
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    algebraMap A (Localization.Away s) s =
      (σ_loc : Localization.Away s) *
        algebraMap A (Localization.Away s) s_D *
        (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t) := by
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  -- Avoid `rw [h_s_factor]` (motive failure: `s` appears in `Localization.Away s`).
  have h_α_s_eq :
      algebraMap A (Localization.Away s) s =
        algebraMap A (Localization.Away s) (s_D * f) :=
    congr_arg (algebraMap A (Localization.Away s)) h_s_factor
  rw [h_α_s_eq, map_mul, h_alg]
  ring

omit [PlusSubring A] in
/-- **T173: end-to-end α_T_D-branch caller from `h_alg` + `s = s_D · f`
+ `T_D ⊆ P.A₀`**.

Composes T173's two suppliers (`h_factorization_via_h_alg_and_s_factor_eq`
and `h_T_D_in_locSubring_of_subset_A₀`) with T172's caller
(`h_T_test_compat_loc_branch_α_T_D_via_factorization_locSubring_membership`)
to produce the α_T_D-branch's full single-branch compatibility output
directly from the **natural Wedhorn cover-piece structural data** at
the localized level:

* `hσ_loc_dom`: standard Cor 7.32 σ-strict-domination over
  `localizedTestFamily` (the
  `exists_dominating_unit_in_localization` output);
* `h_alg`: cover-refinement element identity
  `algebraMap f = σ_loc · ∏ T_D.image` (the existing T170/T171 input
  shape);
* `h_s_factor : s = s_D · f`: cover-base factorization in `A` (Wedhorn
  8.34(ii) / Lemma 8.33 cover-refinement structural relation);
* `hT_D_le_A₀ : T_D ⊆ P.A₀`: per-element membership in the ring of
  definition (the natural Wedhorn `T_D ⊆ A°°` Tate condition).

No `h_factorization`, `h_T_D_in_locSubring`, `h_T_D_image_int`, or
`h_prod_ne` hypotheses required — all four are dispatched through
T172/T173 producers. The α_T_D branch is now closed from the natural
cover-piece structural data alone. -/
theorem h_T_test_compat_loc_branch_α_T_D_via_h_alg_and_subset_A₀
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A) (f : A)
    (σ_loc : (Localization.Away s)ˣ)
    (hσ_loc_dom :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s))
    (h_alg :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      algebraMap A (Localization.Away s) f =
        (σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
    (h_s_factor : s = s_D * f)
    (hT_D_le_A₀ : ∀ t ∈ T_D, t ∈ P.A₀) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
          (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle t' (algebraMap A (Localization.Away s) s_D)) ∧
            ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 :=
  h_T_test_compat_loc_branch_α_T_D_via_factorization_locSubring_membership
    P T s hopen T_D s_D σ_loc hσ_loc_dom
    (h_factorization_via_h_alg_and_s_factor_eq s T_D s_D f σ_loc
      h_alg h_s_factor)
    (h_T_D_in_locSubring_of_subset_A₀ P T s T_D hT_D_le_A₀)

/-! ### T174: integration into the canonical localized test-family chain

This section integrates T173's α_T_D-branch closure into the canonical
localized test-family chain consumed by
`rationalOpen_subset_base_via_local_Cor732_chain`. The α_s_D branch is
left as an explicit hypothesis; the α_T_D branches are dispatched via
T173's combined per-t' upper bound + s_D non-vanishing closer, split
into the per-t' supplier (`.1`) and the s_D non-vanishing supplier
(`.2`).

Provided:

* `h_T_test_compat_loc_canonical_via_h_alg_subset_A₀_and_alpha_s_D` —
  canonical compatibility theorem feeding `h_T_test_compat_loc_canonical`
  with T173's α_T_D branch on the α_T_D side, and an explicit
  `h_α_s_D_per_t` hypothesis on the α_s_D side.

* `rationalOpen_subset_base_via_h_alg_subset_A₀_and_alpha_s_D` —
  caller-facing base inclusion theorem composing the canonical
  compatibility above with `rationalOpen_subset_base_via_local_Cor732_chain`,
  producing `rationalOpen (insert f T_base) s ⊆ rationalOpen T_D s_D`
  from the natural Wedhorn cover-piece structural data plus the
  explicit α_s_D per-t' supplier. -/

omit [PlusSubring A] in
/-- **T174: canonical localized compatibility from T173's α_T_D-branch
closure + explicit α_s_D per-t' supplier**.

Feeds `h_T_test_compat_loc_canonical` with:
* T173's
  `h_T_test_compat_loc_branch_α_T_D_via_h_alg_and_subset_A₀`
  on the α_T_D branches (split via `.1` for per-t' upper bound, `.2`
  for s_D non-vanishing);
* an explicit `h_α_s_D_per_t` hypothesis on the α_s_D branch.

The α_s_D branch's per-t' supplier is left as an explicit hypothesis
in this theorem; the σ-factored variant of this supplier is one
σ-cancellation step away via the existing bridge
`h_α_s_D_per_t_via_factored_chain` (in
`Adic spaces/WedhornLocalArithmeticPerTChain.lean`), which T175's
wrapper `h_T_test_compat_loc_canonical_via_h_alg_subset_A₀_and_alpha_s_D_factored`
(below) plumbs through. The deeper open input is the σ-factored
α_s_D supplier matching that bridge's input shape; everything above
this layer is dispatched through T172/T173/T175 producers. -/
theorem h_T_test_compat_loc_canonical_via_h_alg_subset_A₀_and_alpha_s_D
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A) (f : A)
    (σ_loc : (Localization.Away s)ˣ)
    (hσ_loc_dom :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s))
    (h_alg :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      algebraMap A (Localization.Away s) f =
        (σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
    (h_s_factor : s = s_D * f)
    (hT_D_le_A₀ : ∀ t ∈ T_D, t ∈ P.A₀)
    (h_α_s_D_per_t :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s)
            (algebraMap A (Localization.Away s) s_D) ∧
          ¬ w.vle (algebraMap A (Localization.Away s) s_D)
            (σ_loc : Localization.Away s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle t' (algebraMap A (Localization.Away s) s_D)) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ τ ∈ localizedTestFamily s T_D s_D,
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
          (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle t' (algebraMap A (Localization.Away s) s_D)) ∧
            ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  -- T173's α_T_D-branch closure.
  have h_α_T_D_branch :=
    h_T_test_compat_loc_branch_α_T_D_via_h_alg_and_subset_A₀
      P T s hopen T_D s_D f σ_loc hσ_loc_dom h_alg h_s_factor hT_D_le_A₀
  -- Feed into h_T_test_compat_loc_canonical, splitting α_T_D output via .1/.2.
  exact h_T_test_compat_loc_canonical
    P T s hopen T_D s_D σ_loc
    h_α_s_D_per_t
    (fun τ hτ w hw_spa hw_f hστ ↦
      (h_α_T_D_branch τ hτ w hw_spa hw_f hστ).1)
    (fun τ hτ w hw_spa hw_f hστ ↦
      (h_α_T_D_branch τ hτ w hw_spa hw_f hστ).2)

/-- **T174: caller-facing base inclusion from T173's α_T_D-branch
closure + explicit α_s_D per-t' supplier**.

Composes T174's canonical compatibility theorem with
`rationalOpen_subset_base_via_local_Cor732_chain` to produce the base
rational-open inclusion `rationalOpen (insert f T_base) s ⊆ rationalOpen T_D s_D`
from natural cover-piece structural data plus the explicit α_s_D
per-t' supplier.

This is the **caller-facing end-to-end theorem** for T173/T174's
corrected branch-clearing route: the cover-piece subset clause consumed
downstream is produced from:
* `hA₀_le`: `P.A₀ ≤ A⁺` (standard Tate hypothesis);
* `T_base`, `h_T_le_T_base : T ⊆ T_base`: cover-base structural data;
* `f, σ_loc, h_alg`: cover-refinement element + Cor 7.32 σ-strict-dom output;
* `hσ_loc_dom`: standard Cor 7.32 σ-strict-domination over
  `localizedTestFamily`;
* `h_s_factor : s = s_D · f`: cover-base factorization in `A`;
* `hT_D_le_A₀ : T_D ⊆ P.A₀`: per-element ring-of-definition membership;
* `h_α_s_D_per_t`: explicit α_s_D per-t' supplier (the one input
  not yet dispatched through any clean existing API). -/
theorem rationalOpen_subset_base_via_h_alg_subset_A₀_and_alpha_s_D
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (hA₀_le : P.A₀ ≤ A⁺)
    (T_base T_D : Finset A) (s_D : A) (f : A)
    (h_T_le_T_base : T ⊆ T_base)
    (σ_loc : (Localization.Away s)ˣ)
    (hσ_loc_dom :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s))
    (h_alg :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      algebraMap A (Localization.Away s) f =
        (σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
    (h_s_factor : s = s_D * f)
    (hT_D_le_A₀ : ∀ t ∈ T_D, t ∈ P.A₀)
    (h_α_s_D_per_t :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s)
            (algebraMap A (Localization.Away s) s_D) ∧
          ¬ w.vle (algebraMap A (Localization.Away s) s_D)
            (σ_loc : Localization.Away s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle t' (algebraMap A (Localization.Away s) s_D)) :
    rationalOpen (insert f T_base) s ⊆ rationalOpen T_D s_D :=
  rationalOpen_subset_base_via_local_Cor732_chain
    P T s hopen hA₀_le T_base T_D s_D h_T_le_T_base f σ_loc h_alg
    (localizedTestFamily s T_D s_D) hσ_loc_dom
    (h_T_test_compat_loc_canonical_via_h_alg_subset_A₀_and_alpha_s_D
      P T s hopen T_D s_D f σ_loc hσ_loc_dom h_alg h_s_factor hT_D_le_A₀
      h_α_s_D_per_t)

/-! ### T175: lower the α_s_D explicit input to its σ-factored form

T174's canonical compatibility and base inclusion theorems take an
explicit unfactored `h_α_s_D_per_t` hypothesis on the α_s_D branch.
This section adds wrappers that take instead the **σ-factored**
α_s_D supplier matching the input shape of the existing cancellation
bridge `h_α_s_D_per_t_via_factored_chain` (in
`Adic spaces/WedhornLocalArithmeticPerTChain.lean:88`), then call
that bridge to recover the unfactored form and feed it into T174.

The σ-factored α_s_D supplier shape (input to
`h_α_s_D_per_t_via_factored_chain`) is:

```
∀ w ∈ Spa(Loc s, ⁺), f-membership → α_s_D σ-strict-dom →
  ∀ t' ∈ T_D.image, w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)
```

The σ-cancellation bridge converts this to the canonical un-factored
shape `w.vle t' (algebraMap s_D)` consumed by T174.

Provided:

* `h_T_test_compat_loc_canonical_via_h_alg_subset_A₀_and_alpha_s_D_factored`
  — canonical compatibility wrapper, taking the σ-factored α_s_D
  supplier in place of T174's unfactored one.

* `rationalOpen_subset_base_via_h_alg_subset_A₀_and_alpha_s_D_factored`
  — caller-facing base-inclusion wrapper, also taking the σ-factored
  α_s_D supplier. -/

omit [PlusSubring A] in
/-- **T175: canonical localized compatibility from σ-factored α_s_D
supplier**.

Wraps T174's
`h_T_test_compat_loc_canonical_via_h_alg_subset_A₀_and_alpha_s_D` by
lowering its explicit unfactored α_s_D per-t' supplier to the
σ-factored form via the existing bridge
`h_α_s_D_per_t_via_factored_chain`.

This drops the layer of σ-cancellation manual bookkeeping at the
caller side: the caller now supplies only the σ-factored α_s_D
chain `w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)`, which is the
natural Wedhorn 8.34(ii) σ-rescaled per-t' chain shape on the
α_s_D Laurent piece, matching e.g.
`laurent_piece_α_s_D_per_t_factored_chain`'s output. -/
theorem h_T_test_compat_loc_canonical_via_h_alg_subset_A₀_and_alpha_s_D_factored
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A) (f : A)
    (σ_loc : (Localization.Away s)ˣ)
    (hσ_loc_dom :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s))
    (h_alg :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      algebraMap A (Localization.Away s) f =
        (σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
    (h_s_factor : s = s_D * f)
    (hT_D_le_A₀ : ∀ t ∈ T_D, t ∈ P.A₀)
    (h_α_s_D_factored :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s)
            (algebraMap A (Localization.Away s) s_D) ∧
          ¬ w.vle (algebraMap A (Localization.Away s) s_D)
            (σ_loc : Localization.Away s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle (t' * (σ_loc : Localization.Away s))
            ((algebraMap A (Localization.Away s) s_D) *
              (σ_loc : Localization.Away s))) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ τ ∈ localizedTestFamily s T_D s_D,
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
          (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle t' (algebraMap A (Localization.Away s) s_D)) ∧
            ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 :=
  h_T_test_compat_loc_canonical_via_h_alg_subset_A₀_and_alpha_s_D
    P T s hopen T_D s_D f σ_loc hσ_loc_dom h_alg h_s_factor hT_D_le_A₀
    (h_α_s_D_per_t_via_factored_chain P T s hopen T_D s_D σ_loc
      h_α_s_D_factored)

/-- **T175: caller-facing base inclusion from σ-factored α_s_D
supplier**.

Wraps T174's
`rationalOpen_subset_base_via_h_alg_subset_A₀_and_alpha_s_D` by
lowering its explicit unfactored α_s_D per-t' supplier to the
σ-factored form via the existing bridge
`h_α_s_D_per_t_via_factored_chain`.

Equivalent to calling T175's canonical-compatibility wrapper above
and feeding it into `rationalOpen_subset_base_via_local_Cor732_chain`;
realised here as a direct call to T174's base-inclusion theorem with
the σ-cancellation bridge inlined. -/
theorem rationalOpen_subset_base_via_h_alg_subset_A₀_and_alpha_s_D_factored
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (hA₀_le : P.A₀ ≤ A⁺)
    (T_base T_D : Finset A) (s_D : A) (f : A)
    (h_T_le_T_base : T ⊆ T_base)
    (σ_loc : (Localization.Away s)ˣ)
    (hσ_loc_dom :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s))
    (h_alg :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      algebraMap A (Localization.Away s) f =
        (σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
    (h_s_factor : s = s_D * f)
    (hT_D_le_A₀ : ∀ t ∈ T_D, t ∈ P.A₀)
    (h_α_s_D_factored :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s)
            (algebraMap A (Localization.Away s) s_D) ∧
          ¬ w.vle (algebraMap A (Localization.Away s) s_D)
            (σ_loc : Localization.Away s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle (t' * (σ_loc : Localization.Away s))
            ((algebraMap A (Localization.Away s) s_D) *
              (σ_loc : Localization.Away s))) :
    rationalOpen (insert f T_base) s ⊆ rationalOpen T_D s_D :=
  rationalOpen_subset_base_via_h_alg_subset_A₀_and_alpha_s_D
    P T s hopen hA₀_le T_base T_D s_D f h_T_le_T_base σ_loc hσ_loc_dom
    h_alg h_s_factor hT_D_le_A₀
    (h_α_s_D_per_t_via_factored_chain P T s hopen T_D s_D σ_loc
      h_α_s_D_factored)

/-! ### T176: discharge the σ-factored α_s_D supplier

Discharges T175's remaining open input — the σ-factored α_s_D supplier
— directly from the natural Wedhorn cover-piece structural data
(`h_alg`, `h_s_factor : s = s_D · f`, `hT_D_le_A₀ : T_D ⊆ P.A₀`).

The proof reuses T173's machinery
(`alphaTDBranchAssembly_via_factorization_integrality_prod_ne` fed by
T172's producers) to produce an unfactored per-t' upper bound at each
`w` under f-membership, then σ-factors via `vle_iff_mul_unit_right`.

The α_s_D-strict-domination hypothesis is consumed solely to construct
a localized Laurent-piece membership `w ∈ rationalOpen ({1}) (σ_loc⁻¹ * α s_D)`
at the specific `w`, which is required by the assembly residual's type
even though its proof body does not depend on the choice of Laurent
piece.

Provided:

* `h_α_s_D_factored_via_h_alg_subset_A₀` — σ-factored α_s_D supplier
  matching the input shape of T175's wrapper.

* `rationalOpen_subset_base_via_h_alg_subset_A₀` — caller-facing
  base-inclusion theorem with **no explicit α_s_D supplier**;
  produces `rationalOpen (insert f T_base) s ⊆ rationalOpen T_D s_D`
  from the natural Wedhorn cover-piece structural data alone. -/

omit [PlusSubring A] in
/-- **T176: σ-factored α_s_D supplier from natural cover-piece data**.

Discharges T175's σ-factored α_s_D supplier shape from the same
natural cover-piece structural data as T173's α_T_D-branch closer.

**Proof outline**:

1. Build T172's `h_T_D_image_int` and `h_prod_ne` and T173's
   `h_factorization` via the natural cover-piece data
   (`h_alg`, `h_s_factor`, `hT_D_le_A₀`).

2. Build T171's
   `LocalizedAlphaTDBranchCoverLevelAssemblyResidual` via
   `alphaTDBranchAssembly_via_factorization_integrality_prod_ne`.

3. At each `w` under f-membership and α_s_D-strict-domination:
   construct the Laurent-piece membership
   `w ∈ rationalOpen ({1}) (σ_loc⁻¹ * α s_D)` from the
   α_s_D-strict-domination data; apply the assembly residual at
   `τ := α s_D` to obtain the unfactored per-t' upper bound
   `∀ t' ∈ T_D.image, w.vle t' (α s_D)`.

4. σ-factor via `vle_iff_mul_unit_right`. -/
theorem h_α_s_D_factored_via_h_alg_subset_A₀
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A) (f : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_alg :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      algebraMap A (Localization.Away s) f =
        (σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
    (h_s_factor : s = s_D * f)
    (hT_D_le_A₀ : ∀ t ∈ T_D, t ∈ P.A₀) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s) →
      w.vle (σ_loc : Localization.Away s)
          (algebraMap A (Localization.Away s) s_D) ∧
        ¬ w.vle (algebraMap A (Localization.Away s) s_D)
          (σ_loc : Localization.Away s) →
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle (t' * (σ_loc : Localization.Away s))
          ((algebraMap A (Localization.Away s) s_D) *
            (σ_loc : Localization.Away s)) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  -- Build the assembly residual once.
  have h_factor :=
    h_factorization_via_h_alg_and_s_factor_eq s T_D s_D f σ_loc
      h_alg h_s_factor
  have h_int :=
    h_T_D_image_int_via_locSubring_membership P T s hopen T_D
      (h_T_D_in_locSubring_of_subset_A₀ P T s T_D hT_D_le_A₀)
  have h_pne :=
    h_prod_ne_via_factorization P T s hopen T_D s_D σ_loc h_factor
  have h_assembly :=
    alphaTDBranchAssembly_via_factorization_integrality_prod_ne
      P T s hopen T_D s_D σ_loc h_factor h_int h_pne
  intro w hw_spa hw_f h_α_s_D_strict_dom t' ht'
  letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
  obtain ⟨h_σ_le, h_α_s_D_not_le_σ⟩ := h_α_s_D_strict_dom
  -- Construct Laurent-piece membership at α_s_D from α_s_D-strict-dom.
  have h_α_s_D_ne :
      ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 :=
    not_vle_zero_of_strict_dominator h_α_s_D_not_le_σ
  have hw_one_le_inv :
      w.vle (1 : Localization.Away s)
        (((σ_loc⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) *
          algebraMap A (Localization.Away s) s_D) := by
    have h_step := ValuativeRel.mul_vle_mul_right h_σ_le
        (((σ_loc⁻¹ : (Localization.Away s)ˣ) : Localization.Away s))
    rwa [Units.inv_mul] at h_step
  have hw_inv_ne :
      ¬ w.vle (((σ_loc⁻¹ : (Localization.Away s)ˣ) :
          Localization.Away s) *
          algebraMap A (Localization.Away s) s_D) 0 := by
    intro h_zero
    apply h_α_s_D_ne
    have h_step := ValuativeRel.mul_vle_mul_right h_zero
        ((σ_loc : Localization.Away s))
    rw [mul_zero, ← mul_assoc, Units.mul_inv, one_mul] at h_step
    exact h_step
  have hw_piece :
      w ∈ rationalOpen
        ({(1 : Localization.Away s)} : Finset (Localization.Away s))
        (((σ_loc⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) *
          algebraMap A (Localization.Away s) s_D) := by
    refine ⟨hw_spa, ?_, hw_inv_ne⟩
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact hw_one_le_inv
  -- Apply assembly residual at τ := α s_D.
  have h_α_s_D_in_family :
      algebraMap A (Localization.Away s) s_D ∈
        localizedTestFamily s T_D s_D :=
    Finset.mem_insert_self _ _
  obtain ⟨h_per_t', _⟩ :=
    h_assembly w hw_spa hw_f
      (algebraMap A (Localization.Away s) s_D)
      h_α_s_D_in_family hw_piece
  -- σ-factor the unfactored per-t' upper bound.
  exact (vle_iff_mul_unit_right w σ_loc t'
    (algebraMap A (Localization.Away s) s_D)).mpr (h_per_t' t' ht')

/-- **T176: caller-facing base inclusion with no explicit α_s_D
supplier**.

Composes T175's
`rationalOpen_subset_base_via_h_alg_subset_A₀_and_alpha_s_D_factored`
with T176's `h_α_s_D_factored_via_h_alg_subset_A₀` to produce the
base rational-open inclusion `rationalOpen (insert f T_base) s ⊆
rationalOpen T_D s_D` from the natural Wedhorn cover-piece structural
data alone — no explicit α_s_D per-t' supplier required.

This is the **fully end-to-end caller** for T173/T174/T175/T176's
corrected branch-clearing route: every supplier in the chain is
discharged from the natural cover-piece data
(`hσ_loc_dom`, `h_alg`, `h_s_factor`, `hT_D_le_A₀`). -/
theorem rationalOpen_subset_base_via_h_alg_subset_A₀
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (hA₀_le : P.A₀ ≤ A⁺)
    (T_base T_D : Finset A) (s_D : A) (f : A)
    (h_T_le_T_base : T ⊆ T_base)
    (σ_loc : (Localization.Away s)ˣ)
    (hσ_loc_dom :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s))
    (h_alg :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      algebraMap A (Localization.Away s) f =
        (σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
    (h_s_factor : s = s_D * f)
    (hT_D_le_A₀ : ∀ t ∈ T_D, t ∈ P.A₀) :
    rationalOpen (insert f T_base) s ⊆ rationalOpen T_D s_D :=
  rationalOpen_subset_base_via_h_alg_subset_A₀_and_alpha_s_D_factored
    P T s hopen hA₀_le T_base T_D s_D f h_T_le_T_base σ_loc hσ_loc_dom
    h_alg h_s_factor hT_D_le_A₀
    (h_α_s_D_factored_via_h_alg_subset_A₀ P T s hopen T_D s_D f σ_loc
      h_alg h_s_factor hT_D_le_A₀)

/-! ### T186: power-cleared clause-2 boundary

T185 verified that standard `exists_away_denominator_cleared` only
produces a **power-cleared** identity for `(σ_loc : Loc s) * ∏ τ`:

```
algebraMap f = ((σ_loc : Loc s) * ∏ τ) * (algebraMap s) ^ n
```

The exact `h_alg` consumed by T176's
`rationalOpen_subset_base_via_h_alg_subset_A₀` is the `n = 0`
specialisation. This section provides the corresponding power-cleared
clause-2 theorem, **explicitly exposing `n = 0` as the first missing
structural condition** in the API.

**Mathematical analysis (the real obstruction for `n > 0`)**:

T176's downstream chain (T172/T173/T175/T176 internally) consumes
`h_alg` via T173's `h_factorization_via_h_alg_and_s_factor_eq` to
derive

```
algebraMap s = σ_loc * algebraMap s_D * ∏ τ        -- exact case
```

For the power-cleared `h_alg` (with general `n`), substituting
`h_s_factor : s = s_D * f` and `map_mul` gives

```
algebraMap s = σ_loc * algebraMap s_D * ∏ τ * (algebraMap s) ^ n
```

i.e., dividing both sides by `algebraMap s` (a unit in `Loc s`) :

```
1 = σ_loc * algebraMap s_D * ∏ τ * (algebraMap s) ^ (n - 1)   -- in Loc s
```

This is a **structurally different identity** from the `n = 0` case
(which gives `algebraMap s = σ_loc * algebraMap s_D * ∏ τ`). The
σ-strict-domination branch-clearing arguments downstream
(T172/T173) do not handle this extra `(algebraMap s) ^ (n - 1)`
factor without substantive reformulation.

**Issue type**: MATHEMATICAL, not API-level. The `n = 0` case is a
genuine structural condition on the specific `(σ_loc, ∏ τ)` pair —
it asks that the chosen pair lifts to `algebraMap` of an `A`-element
without requiring power-clearing. For `n > 0`, the entire downstream
chain (T172/T173/T175/T176) would need re-derivation handling the
extra factor — a substantial proof refactor.

**The first missing Lean type** (per T186's directive):
`(n : ℕ) → n = 0`, where `n` is the exponent in the power-cleared
identity. Formalised below as the `h_n_zero : n = 0` parameter of
`rationalOpen_subset_base_via_power_cleared_h_alg_subset_A₀_at_zero_power`.

Provided:

* `rationalOpen_subset_base_via_power_cleared_h_alg_subset_A₀_at_zero_power`
  — the power-cleared clause-2 theorem with `h_n_zero : n = 0` as the
  explicit structural gap. For `n = 0`, reduces (via `pow_zero` +
  `mul_one`) to the exact `h_alg` form consumed by T176; the
  reduction is then T176 itself. -/

/-- **T186 power-cleared clause-2 boundary** (n = 0 specialisation).

Takes power-cleared `h_alg` of the form

```
algebraMap f = ((σ_loc : Loc s) * ∏ τ) * (algebraMap s) ^ n
```

(produced by T185's `wedhorn_834_power_cleared_h_alg_for_unit_product`)
together with the **explicit gap hypothesis** `h_n_zero : n = 0`.

For `n = 0`, the power-cleared form reduces (via `pow_zero` +
`mul_one`) to the exact `h_alg` form `algebraMap f = (σ_loc : Loc s) * ∏ τ`
required by T176's `rationalOpen_subset_base_via_h_alg_subset_A₀`.
The downstream chain T172/T173/T175/T176 then drives clause 2
unchanged.

For `n > 0`, the structural identity downstream
(`algebraMap s = σ_loc * algebraMap s_D * ∏ τ * (algebraMap s) ^ n`)
breaks T176's chain — see the section docstring above for the
mathematical analysis.

**The `n = 0` hypothesis is the first missing structural Lean type**:
discharging it requires the structural condition that the chosen
`(σ_loc, ∏ τ)` pair has `n = 0` denominator-clearing exponent —
equivalently, the existence of an exact lift in T185's
`wedhorn_834_exact_h_alg_target` shape, not merely the power-cleared
form. -/
theorem rationalOpen_subset_base_via_power_cleared_h_alg_subset_A₀_at_zero_power
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (hA₀_le : P.A₀ ≤ A⁺)
    (T_base T_D : Finset A) (s_D : A) (f : A)
    (h_T_le_T_base : T ⊆ T_base)
    (σ_loc : (Localization.Away s)ˣ)
    (hσ_loc_dom :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s))
    (n : ℕ)
    (h_alg_power_cleared :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      algebraMap A (Localization.Away s) f =
        ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)) *
          (algebraMap A (Localization.Away s) s) ^ n)
    (h_n_zero : n = 0)
    (h_s_factor : s = s_D * f)
    (hT_D_le_A₀ : ∀ t ∈ T_D, t ∈ P.A₀) :
    rationalOpen (insert f T_base) s ⊆ rationalOpen T_D s_D := by
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  -- Substitute n = 0 to recover the exact h_alg shape.
  subst h_n_zero
  rw [pow_zero, mul_one] at h_alg_power_cleared
  -- Apply T176 with the recovered exact h_alg.
  exact rationalOpen_subset_base_via_h_alg_subset_A₀
    P T s hopen hA₀_le T_base T_D s_D f h_T_le_T_base σ_loc
    hσ_loc_dom h_alg_power_cleared h_s_factor hT_D_le_A₀

/-! ### T177: C1 supplier wired through the T176 localized multi-piece route

This section provides a C1 supplier wrapper that consumes T176's
`rationalOpen_subset_base_via_h_alg_subset_A₀` directly for clause 2 of
`C1SupplierStrong_local`, **without** invoking the M_power_decay /
σ-power-decay / source-restricted residual / locSubring-integrally-
closed routes.

The natural placement would be `Adic spaces/WedhornC1PerWCoverPieceSupplier.lean`,
but that file is upstream of this file in the existing import graph
(via the multi-piece Laurent / VK / cover-piece chain), so adding the
T177 wrapper there would create an import cycle. Hosting it here, in
the same file as T176's `rationalOpen_subset_base_via_h_alg_subset_A₀`,
is the cycle-free placement.

Provided:

* `WedhornC1PerCallSupplyLocalizedMultiPiece` — per-call supply
  predicate packaging exactly the natural Wedhorn cover-piece data
  consumed by T176's `rationalOpen_subset_base_via_h_alg_subset_A₀`,
  plus the source-side `v ∈ rationalOpen (insert f C.base.T) C.base.s`
  and `¬ v.vle f 0` clauses required by `C1SupplierStrong_local`.

* `C1SupplierStrong_local_via_localized_multi_piece_data` — top-level
  C1 supplier theorem composing the per-call supply with T176's
  localized multi-piece route. Clause 2 of `C1SupplierStrong_local`
  is discharged by `rationalOpen_subset_base_via_h_alg_subset_A₀`;
  clauses 1 and 3 are read directly from the per-call supply. -/

/-- **T177: per-call supply predicate via T176 localized multi-piece data**.

Per-call data packaging the natural Wedhorn cover-piece structural
inputs consumed by `rationalOpen_subset_base_via_h_alg_subset_A₀`,
plus the source-side `v`/`f` clauses for `C1SupplierStrong_local`:

* (1) `σ_loc : (Localization.Away C.base.s)ˣ` — Cor 7.32 dominating unit.
* (2) `f : A` — cover-refinement element.
* (3) `hσ_loc_dom` — σ-strict-domination over
  `localizedTestFamily C.base.s D.T D.s` (standard
  `exists_dominating_unit_in_localization` output).
* (4) `h_alg` — cover-refinement element identity:
  `algebraMap f = σ_loc · ∏ D.T.image (algebraMap)`.
* (5) `h_s_factor` — cover-base factorization in `A`:
  `C.base.s = D.s · f`.
* (6) `hT_D_le_A₀` — per-element ring-of-definition membership:
  `∀ t ∈ D.T, t ∈ P.A₀`.
* (7a) `hv_in_plus` — clause 1 of `C1SupplierStrong_local`:
  `v ∈ rationalOpen (insert f C.base.T) C.base.s`.
* (7b) `hvf_nz` — clause 3 of `C1SupplierStrong_local`: `¬ v.vle f 0`.

This is the **direct per-call interface** for the T176 corrected
branch-clearing route at the C1 layer. -/
def WedhornC1PerCallSupplyLocalizedMultiPiece
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
    -- (3) σ-strict-domination over localizedTestFamily.
    (∀ w ∈ Spa (Localization.Away C.base.s) (Localization.Away C.base.s)⁺,
        ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
          w.vle (σ_loc : Localization.Away C.base.s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away C.base.s)) ∧
    -- (4) Cover-refinement element identity h_alg.
    (algebraMap A (Localization.Away C.base.s) f =
      (σ_loc : Localization.Away C.base.s) *
        (∏ τ ∈ D.T.image (algebraMap A (Localization.Away C.base.s)), τ)) ∧
    -- (5) Cover-base factorization h_s_factor.
    C.base.s = D.s * f ∧
    -- (6) Per-element ring-of-definition membership hT_D_le_A₀.
    (∀ t ∈ D.T, t ∈ P.A₀) ∧
    -- (7a) Clause 1 of C1: v ∈ R(insert f C.base.T, C.base.s).
    v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
    -- (7b) Clause 3 of C1: ¬ v.vle f 0.
    ¬ v.vle f 0

/-- **T177: top-level C1 supplier via T176 localized multi-piece route**.

Produces `C1SupplierStrong_local C` from per-call delivery of
`WedhornC1PerCallSupplyLocalizedMultiPiece`. Clause 2 of
`C1SupplierStrong_local` is discharged by T176's
`rationalOpen_subset_base_via_h_alg_subset_A₀` applied with
`T_base := C.base.T` and `h_T_le_T_base := Finset.Subset.refl _`;
clauses 1 (`v ∈ rationalOpen (insert f C.base.T) C.base.s`) and 3
(`¬ v.vle f 0`) are read directly from the per-call supply.

This is the **fully end-to-end C1 caller** for the corrected
branch-clearing route: every supplier in the chain — including the
α_s_D branch, the α_T_D branches, the per-element integrality, the
product non-vanishing, and the cover-base factorization — is dispatched
through T172/T173/T175/T176 producers from the natural cover-piece
structural data. No M_power_decay, no σ-power-decay, no
source-restricted residual, no locSubring-integrally-closed route. -/
theorem C1SupplierStrong_local_via_localized_multi_piece_data
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (h_per_call_supply :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        WedhornC1PerCallSupplyLocalizedMultiPiece P C hopen_base D v) :
    C1SupplierStrong_local C := by
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨σ_loc, f, hσ_loc_dom, h_alg, h_s_factor, hT_D_le_A₀,
    hv_in_plus, hvf_nz⟩ :=
    h_per_call_supply D hD v hv t ht hvt hvD_s
  refine ⟨f, hv_in_plus, ?_, hvf_nz⟩
  -- Clause 2: rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s.
  exact rationalOpen_subset_base_via_h_alg_subset_A₀
    P C.base.T C.base.s hopen_base hA₀_le C.base.T D.T D.s f
    (Finset.Subset.refl _) σ_loc hσ_loc_dom h_alg h_s_factor hT_D_le_A₀

end ValuationSpectrum

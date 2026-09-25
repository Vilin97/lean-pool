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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.RationalRefinement
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.RationalSubsets
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.TopologyComparison
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.PresheafTateStructure
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.LaurentCoverExact
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.LaurentCoverTopology
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.LaurentBaireSupport
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.CompletionLocalization
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Example638
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.IteratedRational
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.LaurentRefinementCore
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.LaurentRefinementAcyclic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.Topology.MetricSpace.Completion

/-!
# Laurent Covers and Tate Acyclicity Infrastructure

Infrastructure for proving IsSheafy (Wedhorn Theorem 8.28) via the
faithful flatness route (Corollary 8.31).

## Key facts (from reviewer):
- `1-sX` is NOT prime in `A⟨X⟩` in general (it can be a unit when s is
  topologically nilpotent). So `presheafValue D₀` is NOT a domain in general.
- The correct route: `1-sX` is a NON-ZERO-DIVISOR (regular) on `M⟨X⟩`
  for any module M. This gives flatness of `A⟨X⟩/(1-sX)` over A
  (Wedhorn Lemma 8.30, proved in `flat_quotient_oneSubfX_general`).
- IsSheafy follows from: Prop 8.15 (localization principle) + Cor 8.31
  (product restriction is faithfully flat) + Laurent cover exactness.

## Main results

* `rationalOpen_eq_iInter_singleton` : Lemma 7.54 (rational decomposition)
* `laurentCovering` : 2-element Laurent cover construction
* `rationalCovering_hasSeparation` : separation via faithful flatness
* `rationalCovering_hasGluing` : gluing via Laurent exactness

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 7.54, 8.30, 8.31,
  Corollary 8.31, Proposition 8.15, Theorem 8.28
-/

@[expose] public section

open Classical

noncomputable section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-! **`rationalOpen_eq_iInter_singleton` (Lemma 7.54) was migrated to
`LaurentRefinementCore.lean` (F12 file split, 2026-05-23 take 2).** -/

/-! ### Laurent cover construction -/

variable [IsHuberRing A] [HasLocLiftPowerBounded A]

/-! **`LaurentNormalized` class was migrated to
`LaurentRefinementCore.lean` (F12 file split, 2026-05-23 take 2,
migration 2).** -/

/-! **`laurentPlusDatum` was migrated to `LaurentRefinementCore.lean`
(F12 file split, 2026-05-23 take 2, migration 3).** -/

/-! **`divByS_factor'`, `divByS_factor2'`, `divByS_add'` were migrated to
`LaurentRefinementCore.lean` (F12 file split, 2026-05-23 take 2,
migration 4).** -/

/-! **`lift_divByS_eq'` and `divByS_mul_f_mem'` were migrated to
`LaurentRefinementCore.lean` (F12 take 2, migration 5).** -/

/-! ### Ratio Laurent datum (T-LAURENT-TREE-RELATIVE-LABELS) — head-on hopen

For Wedhorn 8.34's second-stage ratio splits at `f · g⁻¹`, we need an
absolute `RationalLocData A` representing the rational subset
`rationalOpen D₀ ∩ {v(f) ≤ v(g)}`. By `rationalOpen_inter`, this equals
`rationalOpen ((insert D₀.s D₀.T) * {f, g}) (D₀.s * g)`.

The hopen condition: `∃ N, ∀ b ∈ I^N, divByS b (D₀.s * g) ∈ locSubring`.
Substantively, this requires `g_inv ∈ A₀` where `g · g_inv = 1`: then
`divByS b (D₀.s * g) = algebraMap g_inv · divByS (b * g) (D₀.s * g)`,
and the second factor is in the new locSubring by the same `Subring.closure_induction`
argument as `divByS_mul_f_mem'`, while `algebraMap g_inv` is in the new
locSubring via `algebraMap_mem_locSubring`. -/

/-! **`divByS_mul_g_mem_T_ratio`, `ratioPlusDatum`, `ratioPlus_rationalOpen`,
`ratioMinusDatum`, `ratioMinus_rationalOpen` were migrated to
`LaurentRefinementCore.lean` (F12 take 2, migration 8).** -/

/-! **`ratioPlus_subset`, `ratioMinus_subset`, `ratioCover_covers`,
`ratioCovering`, `ratioCovering_base/_covers`, `ratioPlus_ne_ratioMinus`
were migrated to `LaurentRefinementCore.lean` (F12 take 2, migration 9).** -/

/-! **`laurentMinusDatum` was migrated to `LaurentRefinementCore.lean`
(F12 take 2, migration 6).** -/

/-! **`laurentPlus_subset`, `laurentMinus_subset`, `laurentCover_covers`,
`laurentCovering` were migrated to `LaurentRefinementCore.lean`
(F12 take 2, migration 7).** -/

/-! ### T277: Distinctness of the Laurent plus and minus data

For the 2-element Laurent cover at `f` of `D₀`, the plus and minus data
are **distinct** whenever `f` is not a unit (in `presheafValue D₀`) and
`D₀.s ≠ 0`. The distinctness is required by the subtype-indexed Π
homeomorphism in `EmbeddingTopo.lean`'s T275.

Proof: the `s` fields differ (`D₀.s` vs `D₀.s * f`); structural equality
of the data would force `D₀.s = D₀.s * f`, hence `D₀.s * (1 - f) = 0`,
and in a domain either `D₀.s = 0` (excluded by hypothesis) or `f = 1`
(making `D₀.canonicalMap f = 1` a unit, excluded by hypothesis). -/

/-! **`laurentPlus_ne_laurentMinus_of_nonunit` was migrated to
`LaurentRefinementCore.lean` (F12 take 2, migration 10).** -/

/-! ### IsSheafy via faithful flatness (Wedhorn Corollary 8.31)

The correct proof route (per reviewer):
1. `1-sX` is regular on `M⟨X⟩` (Wedhorn Lemma 8.30) — gives flatness
2. Prop 8.15: presheafValue D = rational localization of presheafValue D₀
3. Cor 8.31: product restriction is faithfully flat for finite rational covers
4. Faithfully flat → injective → embedding (field 1 of IsSheafy)
5. Laurent cover Čech exactness → gluing (field 2 of IsSheafy)

Key existing results:
- `flat_quotient_oneSubfX_general` : A⟨X⟩/(1-sX) flat over A (0 sorry)
- `presheafValue_flat_of_tateQuotient` : presheafValue D flat over A (0 sorry)
- `epsilonHom_gen_injective` : Laurent separation (0 sorry)
- `laurentCover_exact` : full Laurent exactness (discrete, 0 sorry)

NOTE: `1-sX` is NOT prime in general (can be a unit when s is top. nilpotent).
So presheafValue D₀ is NOT necessarily a domain. The proof uses flatness
and faithful flatness, NOT the domain/localization argument. -/

/-! ### Defect-correction gluing — DELETED (2026-04-08)

The defect-correction approach (`density_approximation`, `defect_correction_exists`,
`compatible_sections_in_image`) was abandoned in favor of Wedhorn's flatness
route. It tried to prove a TOPOLOGICAL embedding for the product restriction via
Banach open mapping, but our `IsSheafy` class only requires sheaf-of-sets (no
topological embedding). Wedhorn's proof of Theorem 8.28(b) gives sheaf-of-
abelian-groups directly via Lemma 8.31 (flatness) + Lemma 8.33 (3×3 diagram
chase) + Lemma 8.34 (refinement transfer), with no topology.

See `docs/plans/2026-04-08-wedhorn-vs-zavyalov.md`. -/

/-! ### Laurent cover gluing via `row3_exact` (Wedhorn Lemma 8.33)

For a 2-element Laurent cover of `Spa(A)` at element `f`, the presheaf gluing
condition follows from the algebraic exact sequence

  `0 → A →ε B₁ × B₂ →δ B₁₂ → 0`

proved in `LaurentCoverExact.row3_exact`. The bridge between the algebraic
quotients (`B₁_gen f`, `B₂_gen f`) and the presheaf values (`presheafValue D`)
goes through `presheafValueCanonicalQuotientEquiv` from `TopologyComparison.lean`.

**Type identifications:**
- `B₁_gen f = A⟨X⟩/(f-X)`: evaluation at `X = f` gives `B₁_gen f ≅ A`
  (proved as `quotientFSubXEquiv` for discrete A; general case via
  `presheafValueCanonicalQuotientEquiv` applied to the plus-piece datum
  with `s = D₀.s`).
- `B₂_gen f = A⟨X⟩/(1-fX)`: this is definitionally `TateAlgebra A ⧸ oneSubfXIdeal f`,
  identified with `presheafValue (laurentMinusDatum D₀ f)` via
  `presheafValueCanonicalQuotientEquiv` (with `s = D₀.s * f`).
- `presheafValue D₀ ≅ A` when `D₀` is the trivial datum and `A` is complete.

**Restriction map correspondence:**
- `restrictionMap D₀ (laurentPlusDatum D₀ f)` corresponds to `π₁ ∘ ε` (first
  projection of the diagonal).
- `restrictionMap D₀ (laurentMinusDatum D₀ f)` corresponds to `π₂ ∘ ε` (second
  projection).
- Compatibility on the overlap (delta = 0) corresponds to the two sections
  agreeing in `B₁₂_gen f = A⟨ζ, ζ⁻¹⟩/(f-ζ)`. -/

/-! ### Helper lemmas for Laurent cover gluing (infrastructure gaps)

**Proof strategy** (updated from the original `row3_exact` transport plan):

The transport through `row3_exact` requires bridge lemmas identifying
`presheafValue (laurentPlusDatum D₀ f) ≃+* B₁_gen f` and similarly for the
minus piece. These bridges depend on nontrivial infrastructure (Phase 2 of the
Wedhorn plan: Example 6.38 as topological ring iso, Prop 6.17 on closed ideals).

Instead, the proof uses the partition-of-unity approach from `discrete_gluing`:
1. Find an algebraic preimage `x' : Localization.Away D₀.s` via the partition
   of unity for the 2-element Laurent cover.
2. Lift to `presheafValue D₀` via `D₀.coeRingHom` (the completion embedding).
3. Verify via `extensionHom_coe` (restriction maps commute with completion).

The proof of `laurentCover_gluing_presheaf` uses the 2-element Laurent covering
`{R(T ∪ {f} / s), R(T' / s·f)}` of the base `R(T/s)`.

**Architecture**: The partition-of-unity approach (as in `discrete_gluing` from
`TateAcyclicity.lean`) works at the localization level and lifts to completions.
For a 2-element cover `{D₊, D₋}`, the proof requires:
1. Finding `x' : Localization.Away D₀.s` with `restrictionMapAlg D₀ D± _ x' = f±`.
2. Lifting `x'` to `presheafValue D₀` via `D₀.coeRingHom`.

Step 1 reduces to the partition-of-unity argument: the elements `D₊.s` and `D₋.s`
generate the unit ideal in `Localization.Away D₀.s` (from the covering condition
on the spectrum), so `∑ c_i * s_i^N = 1` gives the global section `x' = ∑ c_i * r_i`.

The key infrastructure gaps are:
- `span_top_of_laurentCover`: the images of `D₊.s` and `D₋.s` generate `⊤` in
  `Localization.Away D₀.s`.
- `laurentCover_numerator_compat`: cross-compatibility of numerators after
  absorbing powers.
- `laurentCover_restrictionMapAlg_dense_surj`: every element of `presheafValue D±`
  is in the range of `restrictionMapAlg D₀ D± _` (the algebraic restriction is
  surjective onto the dense image, then extends).

**Note**: the plus datum has `(laurentPlusDatum D₀ f).s = D₀.s` (SAME generator),
so `Localization.Away (laurentPlusDatum D₀ f).s = Localization.Away D₀.s`. Only
the topology (determined by `T`) differs. The minus datum has
`(laurentMinusDatum D₀ f).s = D₀.s * f`, a genuinely different localization. -/

/-! **`span_top_of_laurentCover` was migrated to `LaurentRefinementCore.lean`
(F12 take 2, migration 11).** -/

/-! ### Laurent cover gluing — Route A (`Localization.Away` preimage)

Removed 2026-04-14. The theorem `laurentCover_algebraic_gluing` asked for a
pre-completion element `x' : Localization.Away D₀.s` restricting to the given
completed sections `u±`. This is strictly stronger than the presheaf-level
gluing (which allows `x : presheafValue D₀`) and requires the Baire-category
surjection `restrictionMapHom_surj` (PresheafTateStructure.lean:1226) — itself
a substantial sorry. Route B (below) avoids this entirely via `row3_exact` at
`presheafValue D₀` and five explicit type-bridge stubs. -/

/-! ### Route B: Laurent cover gluing via `row3_exact` at `presheafValue D₀`

The frozen 2026-04-14 investigation established that `LaurentCover.row3_exact`
instantiates cleanly at `A := presheafValue D₀`: the completion has the
required `[UniformSpace]`, `[IsUniformAddGroup]`, `[T2Space]`, `[CompleteSpace]`,
and `[NonarchimedeanRing]` instances. The theorem statement uses
`[CommRing]`/`[TopologicalSpace]`/`[NonarchimedeanRing]` plus the four uniform
properties — it does NOT require `[IsNoetherianRing]` or `[IsDomain]` on the
instantiated base.

This gives an alternative route to `laurentCover_gluing_presheaf` that avoids
`restrictionMapHom_surj` (the Baire blocker). The remaining work is the type
bridge: building `RingEquiv`s from `presheafValue (laurent±Datum D₀ f)` to the
algebraic quotients `B_gen (D₀.canonicalMap f)` in `TateAlgebra (presheafValue D₀)`,
with restriction maps factoring through them. Cf. `presheafValueTateQuotientEquiv`
(TopologyComparison.lean:831), which gives the base-level analogue over `A`.

The statement below captures the target. -/

/-! #### Iterated rational data over `B := presheafValue D₀`

Per the 2026-04-14 reviewer addendum, the Laurent bridges are recovered
from a single generic identification: `presheafValue_A(laurent±Datum D₀ f)`
matches a rational localization of `B = presheafValue D₀` at `canonicalMap f`
(Wedhorn Lemma 2.13 / Prop 8.7 — iterated rational localizations collapse
to rational localizations of the new base).

The data below packages the target rational datum on `B`. The plus branch
uses `T = {canonicalMap f}`, `s = 1`; the minus branch uses `T = {1}`,
`s = canonicalMap f`. In both cases the `hopen` condition is discharged by
`hopen_away_one` (the plus branch directly; the minus branch via the
standard "localization-at-1 identity"). -/

/-! **`iteratedPlusDatum_B` and `iteratedMinusDatum_B` were migrated to
`LaurentRefinementCore.lean` (F12 take 2, migration 12).** -/

/-! #### Uncompleted forward / backward infrastructure for Wedhorn Lemma 2.13

The iterated identifications `presheafValue (laurent±Datum D₀ f) ≃+*
presheafValue (iterated±Datum_B P D₀ f)` are built in three stages:

1. **Uncompleted maps** (below) — forward and backward ring homs at the
   `Localization.Away` level, fully proved via `IsLocalization.Away.lift`.
2. **Continuity** — the Wedhorn Prop 8.2 analogue across the base change
   `A → B = presheafValue D₀`. Currently expected as an explicit hypothesis
   in any closed-form proof of the equivs; this is what blocks a full
   closure of `presheafValue_iteratedPlus_equiv` / `presheafValue_iteratedMinus_equiv`
   without further infrastructure.
3. **Extension to completions + round-trip** via `UniformSpace.Completion.extensionHom`
   + `Completion.ext'`, using the backward-forward identity proved below.

This block provides the stage-1 infrastructure: it is fully proved (no sorries)
and is structural preparation for any future closure of the two equivs. -/

/-! **iteratedPlus uncompleted forward/backward hom infrastructure
(`iteratedPlus_D₀s_isUnit_in_Loc_B_one`, `iteratedPlus_forwardLocHom`,
`iteratedPlus_forwardLocHom_algebraMap`, `iteratedPlus_forwardToCompletion`,
`iteratedPlus_backwardLocHom`, `iteratedPlus_backwardLocHom_algebraMap`,
`iteratedPlus_backward_forward_locHom`) was migrated to
`LaurentRefinementCore.lean` (F12 take 2, migration 13).** -/

/-! #### Minus branch: uncompleted forward / backward infrastructure -/

/-! **iteratedMinus uncompleted forward/backward hom infrastructure
(`iteratedMinus_baseHom`, `iteratedMinus_D₀s_mul_f_isUnit`,
`iteratedMinus_forwardLocHom`, `iteratedMinus_forwardLocHom_algebraMap`,
`iteratedMinus_forwardToCompletion`, `algebraMap_f_isUnit_in_laurentMinus`,
`canonicalMap_f_isUnit_in_laurentMinus`,
`restrictionMap_canonicalMap_f_isUnit_laurentMinus`,
`iteratedMinus_backwardLocHom`, `iteratedMinus_backwardLocHom_algebraMap`,
`iteratedMinus_backward_forward_locHom`) was migrated to
`LaurentRefinementCore.lean` (F12 take 2, migration 14).** -/

/-! #### Plus-branch continuity residuals (Wedhorn Prop 8.2 analogues)

Structure (mirroring the minus branch): the forward / backward homs are
extracted as named `noncomputable def`s depending on named continuity
theorems (Wedhorn Prop 8.2 analogues, recorded as sorries). The equiv
`presheafValue_iteratedPlus_equiv` (below) is assembled from these
ingredients plus two round-trip theorems — round-trip 1 is proved via
`Completion.ext'`; round-trip 2 is recorded as a named sorry pending the
density-of-canonicalMap argument. -/

/-! #### Power-boundedness helpers for the plus-branch forward map

The forward uncompleted map `iteratedPlus_forwardLocHom D₀ : Loc_A(D₀.s) →
Loc_B(1)` sends each generator `divByS t D₀.s` (for `t ∈ insert f D₀.T`,
the `T` of `laurentPlusDatum`) to an element which must be power-bounded
in `Loc_B(1)` with `(iteratedPlusDatum_B P D₀ f).topology`.

We package this as a single helper lemma `iteratedPlus_forwardLocHom_generators_powerBounded`
(Wedhorn Prop 8.2 / Lemma 2.13 content, deferred). -/

/-! **`iteratedPlus_forwardLocHom_divByS`,
`iteratedPlus_forwardLocHom_generators_powerBounded`, and
`iteratedPlus_forwardToCompletion_continuous` were migrated to
`LaurentRefinementCore.lean` (F12 take 2, migration 15). -/

/-! #### Backward (plus branch): power-boundedness sub-sorry

The backward uncompleted map
`iteratedPlus_backwardLocHom D₀ f hsub : Loc_B(1) →+*
presheafValue (laurentPlusDatum D₀ f)` sends the single generator
`divByS (canonicalMap f) 1` of `(iteratedPlusDatum_B P D₀ f).T = {canonicalMap f}`
to `(laurentPlusDatum D₀ f).canonicalMap f`, which must be power-bounded
in `presheafValue (laurentPlusDatum D₀ f)`.

We package this as `iteratedPlus_backwardLocHom_generator_powerBounded`
(parallels `iteratedMinus_backwardLocHom_generator_powerBounded` in the
minus direction). -/

/-! **`iteratedPlus_backwardLocHom_generator_powerBounded` and
`iteratedPlus_backwardLocHom_continuous` were migrated to
`LaurentRefinementCore.lean` (F12 take 2, migration 16). -/

/-! **iteratedPlus completion-level forward/backward Hom + coeRingHom +
round-trip 1 (backward∘forward = id) were migrated to
`LaurentRefinementCore.lean` (F12 take 2, migration 17a). -/

/-! **`iteratedPlus_forwardHom_comp_restrictionMapHom` was migrated to
`LaurentRefinementCore.lean` (F12 take 2, migration 17b). -/

/-! **`iteratedPlus_forwardHom_comp_backwardHom` was migrated to
`LaurentRefinementCore.lean` (F12 take 2, migration 17c). -/

/-! **`presheafValue_iteratedPlus_equiv` + `_apply` + `_coeRingHom` were
migrated to `LaurentRefinementCore.lean` (F12 take 2, migration 17d). -/

/-! #### Continuity and inducing topology of `presheafValue_iteratedPlus_equiv` (T146)

The forward / backward completion homs `iteratedPlus_forwardHom` and
`iteratedPlus_backwardHom` are both `UniformSpace.Completion.extensionHom`
of (uncompleted) continuous ring homs, hence continuous via
`UniformSpace.Completion.continuous_extension`. Combined with the fact
that they are mutual inverses, they assemble into a `Homeomorph`, and the
ring equiv `presheafValue_iteratedPlus_equiv` is `Topology.IsInducing`
in both directions. -/

/-! **`iteratedPlus_forwardHom_continuous`, `iteratedPlus_backwardHom_continuous`,
`presheafValue_iteratedPlus_equiv_homeomorph`,
`presheafValue_iteratedPlus_equiv_isInducing`,
`presheafValue_iteratedPlus_equiv_symm_isInducing` were migrated to
`LaurentRefinementCore.lean` (F12 take 2, migration 17e). -/

/-! #### Minus-branch continuity residuals (Wedhorn Prop 8.2 analogues)

The two continuity facts needed to extend the uncompleted forward / backward
maps to the completion level. Both are Wedhorn Prop 8.2 analogues across the
base change `A → B = presheafValue D₀`; see the Phase-2 plan for the full
structural proofs. Recorded here as named sorries so the downstream
`presheafValue_iteratedMinus_equiv` can refer to them as concrete theorems
(enabling the `_restrictionMap_canonicalMap` sub-sorry to be reduced). -/

/-! #### Power-boundedness helpers for the minus-branch forward map

The forward uncompleted map `iteratedMinus_forwardLocHom D₀ f :
Loc_A(D₀.s · f) → Loc_B(canonicalMap f)` sends each generator
`divByS t (D₀.s · f)` (for `t ∈ (laurentMinusDatum D₀ f).T`, the product
`(insert D₀.s D₀.T) × {D₀.s, f}` under `(·.1 * ·.2)`) to an element which
must be power-bounded in `Loc_B(canonicalMap f)` with
`(iteratedMinusDatum_B P D₀ f).topology`.

We package this as a single helper lemma
`iteratedMinus_forwardLocHom_generators_powerBounded`
(Wedhorn Prop 8.2 / Lemma 2.13 content, deferred). Parallels
`iteratedPlus_forwardLocHom_generators_powerBounded`. -/

/-! **Full minus-branch completion-level cluster (lines 458-1363, ~900
lines) was migrated to LaurentRefinementCore.lean (F12 take 2, migration 18).
Includes iteratedMinus_forwardLocHom_generators_powerBounded,
iteratedMinus_forwardToCompletion_continuous,
iteratedMinus_backwardLocHom_generator_powerBounded,
iteratedMinus_backwardLocHom_continuous, iteratedMinus_forwardHom,
iteratedMinus_backwardHom, *_coeRingHom, *_comp_*, presheafValue_iteratedMinus_equiv,
*_apply, *_coeRingHom, *_continuous, *_homeomorph, *_isInducing, *_symm_isInducing. -/


/-! **CompleteSpace + Baire + sigmaCompactSpace suppliers (lines 416-579)
migrated to LaurentRefinementCore.lean (F12 take 2, migration 19).** -/


/-! ### T152 route-decision documentation: SigmaCompactSpace blocker scope

The two `quotient*_sigmaCompactSpace_of_source` suppliers above transport
the SigmaCompactSpace hypothesis through the quotient map, but the
**source** hypothesis `SigmaCompactSpace (TateAlgebra A)` (with the
canonical Tate topology) cannot be discharged generically over an
arbitrary strongly noetherian Tate ring `A`.

**Mathematical reason.** `TateAlgebra A` has a "ring of definition"
`pairSubring P : Subring (TateAlgebra A)` with the `pairIdeal P`-adic
topology. With a topologically nilpotent unit `π ∈ A`, every element of
`TateAlgebra A` lies in `π^(-n) · pairSubring P` for some `n`, giving the
covering decomposition
`TateAlgebra A = ⋃_{n : ℕ} π^(-n) · pairSubring P`.
Each piece `π^(-n) · pairSubring P` is compact iff `pairSubring P` is
compact, iff `pairSubring P` is profinite-with-finite-residue-quotients,
which holds iff `A` is a *local field* setting (`A₀ = ℤ_p`, `𝔽_p[[t]]`,
or similar). For a generic noetherian Tate ring (e.g.,
`A = ℂ((t))` with `A₀ = ℂ[[t]]`), `pairSubring P = ℂ[[t]]⟨X⟩` is **not**
compact, and `TateAlgebra A` is **not** sigma compact.

**Consequence for the OMT chain.** Mathlib's only Banach OMT for
topological groups, `MonoidHom.isOpenMap_of_sigmaCompact`
(`Mathlib/Topology/Algebra/Group/OpenMapping.lean:113`), explicitly
requires SigmaCompactSpace on the source and notes "Note that a
sigma-compactness assumption is necessary"
(`Mathlib/Topology/Algebra/Group/OpenMapping.lean:19`,
counterexample: discrete-real → usual-real). The normed-space variant
`ContinuousLinearMap.isOpenMap` does not need sigma compactness but
requires `NormedSpace`, which `TateAlgebra` does not have.

**Replacement options for an OMT-based consumer:**

1. **Scope restriction `[CompactSpace ↥(TateAlgebra.pairSubring P)]`**
   (where `P` is the canonical principal pair). This gives compactness
   of `pairSubring P` and then `SigmaCompactSpace (TateAlgebra A)` via
   the `π^(-n) · pairSubring P` decomposition (currently not on disk;
   would require Wedhorn-style Tate-algebra structure infrastructure).
   Concrete and clean, but applies only to the local-field setting.

2. **Scope restriction `[LocallyCompactSpace A]`**. By the structure
   theory of Tate rings, this implies `A₀` has a compact open subgroup,
   from which `CompactSpace ↥(TateAlgebra.pairSubring P)` follows.
   Equivalent to (1) but stated at the base level.

3. **Direct construction of the inducing map** without OMT. For Tate
   algebras, the inverse of the relevant restriction map could be
   constructed explicitly (e.g., via "evaluate at a topologically
   nilpotent unit"). Substantial new infrastructure.

4. **Bypass the OMT chain entirely.** As noted in the docstring of
   `tateAcyclicity` (this file, line 5422 sequence), the final Tate
   acyclicity theorem (`tateAcyclicity`) uses Wedhorn's flatness route
   and does **not** depend on the OMT-derived strict embedding lemmas.
   The OMT chain (T134–T149, plus the present file's
   `laurentCover_isEmbedding_presheaf_*` family) is parameterized
   infrastructure for *future* consumers that want strict-embedding
   properties beyond the sheaf-of-sets statement.

**Replacement theorem statement** (the SigmaCompact source hypothesis
that would unblock the consumer chain, leaving open only the question
of *when* it is supplied):
```
theorem tateAlgebra_sigmaCompactSpace [scope_restriction] :
    SigmaCompactSpace ↥(TateAlgebra A)
```
where `[scope_restriction]` is one of (1)–(2) above, depending on the
desired generality.

This T152 ticket therefore lands the two `quotient_*_sigmaCompactSpace_of_source`
transport suppliers above (axiom-clean, no scope assumption beyond
`[SigmaCompactSpace ↥(TateAlgebra A)]`) but does **not** ship a generic
`SigmaCompactSpace (TateAlgebra A)` supplier, because none exists at
the level of generality this project's strongly-noetherian Tate setup
operates at. -/

/-! **F12 take 2 migration markers (2026-05-23, 27 migrations total).**

The following content blocks were extracted to sister files:

* `LaurentRefinementCore.lean` (migrations 20-25):
  - Bridge cluster (trivialPlus_fSubX_equiv + laurentPlus/MinusBridge)
  - Bridge restrictionMap + isInducing cluster
  - Laurent overlap infrastructure + delta-vanishing
  - Laurent cover gluing viaRow3 + viaBridges
  - Laurent isEmbedding cluster (6 theorems)
  - Lane-C consumer cluster (5 theorems)

* `LaurentRefinementAcyclic.lean` (migration 26):
  - tateAcyclicity_gluing_* family + tateAcyclicity headline (Wedhorn 8.28(b))

See commit 5cef63d (F12 take 2 split) and Adic spaces.lean import order. -/

/-! **presheafValue_subsingleton_of_s_eq_zero + rationalCovering_hasSeparation
+ rationalCovering_hasGluing (lines 510-584) migrated to
LaurentRefinementAcyclic.lean (F12 take 2, migration 27).** -/


-- The embedding theorem (Topology.IsEmbedding) is stated in StructureSheaf.lean
-- since it uses `productRestrictionSub` defined there.

end ValuationSpectrum

end

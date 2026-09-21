/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornVKNonemptyRationalBoundDischarge

/-!
# Wedhorn 8.34(ii) — Source-restricted comap-lift C1 supplier (T043)

T042 (commit `4a96e77`) accepted the max-element factoring of the
V_K-nonempty residual and exposed an irreducible counter-example: the
universal-over-`Spa(Localization.Away s, ⁺)` per-`w` upper-bound
quantifier in T039's component 5 / T040's predicate / T041's V_K
residual / T042's α_T_D max-element residual is **mathematically false
in general** (T035 / T042 docstring counter-examples), so attempting to
discharge those predicates uniformly is doomed without forbidden
power-decay arithmetic or upstream signature changes.

This ticket lands the **honest source-restricted route**: instead of
the false universal-over-`Spa` quantifier, the per-call C1 supplier
provides the per-`w` per-`t` upper bound **only at `w` satisfying the
source-side LHS rationalOpen conditions** — equivalently, at `w` whose
comap-image at the base lies in `rationalOpen (insert f C.base.T)
C.base.s`. This is the actual context where the bound is needed by
the existing localized-transfer machinery (`rationalOpen_subset_via_
localization_locSubring`), and it is mathematically TRUE under the
cover refinement (which is the C1 supplier's eventual output).

## Source-restricted predicate

The new predicate `WedhornCoverPieceCovPlusPieceLiftPerTBound` matches
the `h_local`-shape consumed by
`rationalOpen_subset_via_localization_locSubring`: at every
`w ∈ Spa(Localization.Away s, ⁺)` satisfying `∀ c ∈ insert f T_base,
w.vle (algebraMap c) (algebraMap s)` and `¬ w.vle (algebraMap s) 0`
(i.e., the LHS conditions corresponding to `comap w ∈ rationalOpen
(insert f T_base) s`), the per-`t` upper bound `∀ t ∈ T_D, w.vle
(algebraMap t) (algebraMap s_D)` and non-vanishing
`¬ w.vle (algebraMap s_D) 0` hold.

Mathematically, the predicate's source restriction makes the residual
**vacuously trivial** at `w` outside the cover plus-piece (where the
LHS premises fail). This is exactly the structural correction needed:
**T035's counter-example** at `A = ℚ_p, T_D = {1}, s_D = p, v_p`
fails the LHS conditions at `v_p` (since `v_p(1) > v_p(p)`), so the
predicate is vacuously true at `v_p` regardless of whether the per-`t`
bound at `algebraMap s_D` holds there.

## What this file provides

* `WedhornCoverPieceCovPlusPieceLiftPerTBound P T s hopen T_base T_D
  s_D f` — the source-restricted predicate. Quantifies over
  `w ∈ Spa(Localization.Away s, ⁺)` satisfying the LHS rationalOpen
  conditions (per-`c` bound at `algebraMap s` for `c ∈ insert f
  T_base` AND non-vanishing of `algebraMap s`); concludes per-`t` bound
  at `algebraMap s_D` AND non-vanishing of `algebraMap s_D`.

* `rationalOpen_subset_base_via_cov_plus_piece_lift_predicate` — the
  main bridge: composes the predicate directly with
  `rationalOpen_subset_via_localization_locSubring` to produce the
  base cover refinement `rationalOpen (insert f T_base) s ⊆
  rationalOpen T_D s_D` on `Spa(A, A⁺)`.

* `WedhornC1PerCallSupplyCovPlusPieceLift` — per-call supply predicate
  for the source-restricted C1 route. Consumes `f` plus the
  source-restricted predicate plus `v ∈ rationalOpen (insert f
  C.base.T) C.base.s` plus `¬ v.vle f 0`. **No σ_loc, no
  denominator-clearing identity, no σ-strict-domination** — these
  algebraic data are absorbed into the proof of the predicate (where
  the σ-construction lives) but do not appear at the per-call C1
  layer.

* `C1SupplierStrong_local_via_cov_plus_piece_lift_supplier` — top-level
  C1 supplier theorem composing the per-call source-restricted supply
  with the base subset bridge. Produces `C1SupplierStrong_local C`
  directly without invoking T039's universal-over-`Spa` per-`w`
  upper-bound supplier residual or T040–T042's universal predicates.

## Why this avoids the false global Spa bound

T039's `WedhornC1PerCallSupplyPerWCoverPiece` component 5 has the
universal premise `∀ w ∈ Spa(Localization.Away s, ⁺)` followed by
implications. The per-`t` bound conclusion is mathematically false at
`w` outside the cover plus-piece (T035 / T042 counter-examples).

This file's predicate has the same universal `∀ w ∈ Spa(...)` premise
but adds the **explicit LHS rationalOpen conditions on `w`** as
implication antecedents. At `w` failing these conditions, the
implication is vacuously true. The predicate is therefore
mathematically TRUE under the cover refinement (which is the C1
supplier's output), with no false universal claim.

The cost: the per-call C1 supplier no longer factors through the σ-
construction's σ_loc / denominator-clearing / σ-strict-dom data at the
per-call interface; those data are absorbed into the proof of the
predicate. This is a **C1 layer interface change** but stays inside
the leaf and does not edit T037–T042.

## Relationship to T037–T042

* **T037–T042 layer**: false universal-over-`Spa` predicates remain
  in T037–T042; this file does not edit those, but provides a parallel
  honest source-restricted route bypassing them.
* **Upstream changes needed for full removal**: removing T037–T042's
  false universal predicates from the project requires definition-
  level edits to `WedhornCoverPieceStructuralData` (T037's Prop) to
  add LHS source restriction explicitly, plus coordinated updates in
  T038–T042's bridges. Out of T043's scope; documented in the file's
  "remaining dependency" section.

## Notes

* No root import; leaf-level.
* Imports only `WedhornVKNonemptyRationalBoundDischarge` (T042, commit
  `4a96e77`), which transitively brings in
  `rationalOpen_subset_via_localization_locSubring` (the existing
  base-side transfer machinery via T037 → T036 → T028 →
  `WedhornLocalPerBranchChain` → `WedhornRationalOpenLocalizationTransfer`).
* No edits to T027–T042 accepted files, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* The source-restricted predicate's discharge — proving that for the
  `(σ_loc, f)` chosen by the σ-construction, the per-`t` bound at
  `algebraMap s_D` holds at every `w` satisfying LHS rationalOpen
  conditions — IS the genuine remaining mathematical content. With
  source restriction, the predicate is provably TRUE for the cover
  refinement; without it, the unrestricted version is false. The
  remaining work is the honest σ-construction-style proof, restricted
  to LHS-satisfying `w`.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Source-restricted comap-lift cover-plus-piece per-`t` bound
predicate** (T043 honest source-restricted form).

At every `w ∈ Spa(Localization.Away s, ⁺)` satisfying:

* `∀ c ∈ insert f T_base, w.vle (algebraMap c) (algebraMap s)` (the
  LHS per-`c` rationalOpen condition for the cover plus-piece
  `R(insert f T_base, s)` at the localized side), AND
* `¬ w.vle (algebraMap s) 0` (LHS non-vanishing condition),

the per-`t` upper bound `∀ t ∈ T_D, w.vle (algebraMap t)
(algebraMap s_D)` AND non-vanishing `¬ w.vle (algebraMap s_D) 0`
hold.

This is the **honest source-restricted form** of the per-`w` per-`t`
upper-bound supplier: the LHS source conditions on `w` correspond to
`comap (algebraMap A (Localization.Away s)) w ∈ rationalOpen
(insert f T_base) s` at the base side via `comap_vle`. The predicate
is vacuously trivial at `w` violating these LHS conditions — exactly
where T035 / T042's counter-examples to the unrestricted form live —
and is provably TRUE for the cover refinement at LHS-satisfying `w`.

Matches the `h_local` parameter shape of
`rationalOpen_subset_via_localization_locSubring` exactly, so it
composes directly with the existing localized-transfer machinery to
produce the base cover refinement `rationalOpen (insert f T_base) s ⊆
rationalOpen T_D s_D` on `Spa(A, A⁺)`. -/
def WedhornCoverPieceCovPlusPieceLiftPerTBound
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_base T_D : Finset A) (s_D : A) (f : A) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  ∀ w : Spv (Localization.Away s),
    w ∈ @Spa (Localization.Away s) _ (locTopology P T s hopen)
      (locSubring P T s) →
    (∀ c ∈ insert f T_base,
        w.vle (algebraMap A (Localization.Away s) c)
          (algebraMap A (Localization.Away s) s)) →
    ¬ w.vle (algebraMap A (Localization.Away s) s) 0 →
    (∀ t ∈ T_D, w.vle (algebraMap A (Localization.Away s) t)
        (algebraMap A (Localization.Away s) s_D)) ∧
    ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0

/-- **Bridge: base cover refinement from the source-restricted
comap-lift predicate** (T043 main bridge).

From `WedhornCoverPieceCovPlusPieceLiftPerTBound P T s hopen T_base
T_D s_D f`, derive the base rational-open inclusion `rationalOpen
(insert f T_base) s ⊆ rationalOpen T_D s_D` on `Spa(A, A⁺)`.

Direct application of `rationalOpen_subset_via_localization_locSubring`:
the predicate IS exactly the `h_local` hypothesis of that transfer
theorem (modulo `T1 := insert f T_base`, `T2 := T_D`, `s2 := s_D`),
so the bridge is mechanical.

The transfer's universal `∀ w` quantifier is internally only applied
at `w` arising as comap-lifts of base points in `rationalOpen
(insert f T_base) s` (constructed via
`valuationLocalizationLift_of_spa_rationalOpen_locSubring`). At
those `w`, the LHS rationalOpen conditions are automatic by
`comap_vle`; outside such `w`, the predicate is vacuously trivial. -/
theorem rationalOpen_subset_base_via_cov_plus_piece_lift_predicate
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (hA₀_le : P.A₀ ≤ A⁺)
    (T_base T_D : Finset A) (s_D : A) (f : A)
    (h_T_le_insert_f : T ⊆ insert f T_base)
    (h_pred :
      WedhornCoverPieceCovPlusPieceLiftPerTBound P T s hopen
        T_base T_D s_D f) :
    rationalOpen (insert f T_base) s ⊆ rationalOpen T_D s_D :=
  rationalOpen_subset_via_localization_locSubring P T (insert f T_base)
    T_D s s_D hopen hA₀_le h_T_le_insert_f h_pred

/-- **Per-call C1 supply predicate (source-restricted comap-lift
form)** (T043 cover-plus-piece per-call interface).

At each per-call input `(D, v, t, ...)` for the C1 caller, supply:

* `f : A` — the cover-plus-piece denominator candidate.
* `WedhornCoverPieceCovPlusPieceLiftPerTBound` — the **honest source-
  restricted residual**: per-`t` bound at `algebraMap s_D` AND
  non-vanishing of `algebraMap s_D` at every `w ∈ Spa(Loc s, ⁺)`
  satisfying the LHS rationalOpen conditions for `(insert f T_base, s)`.
* `v ∈ rationalOpen (insert f C.base.T) C.base.s` — base-side
  rationalOpen membership of `v` (clause 1 of `C1SupplierStrong_local`).
* `¬ v.vle f 0` — non-degeneracy of `f` at `v` (clause 3 of
  `C1SupplierStrong_local`).

**No σ_loc, no denominator-clearing identity, no σ-strict-domination
data** at this layer — those are internal to the σ-construction-style
proof of the predicate, not exposed at the per-call C1 interface. This
is the cleanest C1 supplier shape that avoids the false universal-
over-`Spa(Loc s, ⁺)` per-`w` upper-bound from T039–T042. -/
def WedhornC1PerCallSupplyCovPlusPieceLift
    [DecidableEq A]
    (P : PairOfDefinition A) (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (D : RationalLocData A) (v : Spv A) : Prop :=
  ∃ (f : A),
    WedhornCoverPieceCovPlusPieceLiftPerTBound P C.base.T C.base.s
      hopen_base C.base.T D.T D.s f ∧
    v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
    ¬ v.vle f 0

/-- **Top-level: `C1SupplierStrong_local C` via source-restricted
comap-lift supplier** (T043 final deliverable).

Identical caller signature to T039's
`C1SupplierStrong_local_via_per_w_cover_piece_supplier`, modulo the
per-call supply: each per-call delivery provides
`WedhornC1PerCallSupplyCovPlusPieceLift` (the honest source-restricted
form) in place of T039's `WedhornC1PerCallSupplyPerWCoverPiece` (which
contains the false universal-over-`Spa(Loc s, ⁺)` per-`w` per-`t`
upper-bound supplier).

Proof: at each per-call input, unpack the supply (`f`, predicate,
`v ∈ rationalOpen (insert f C.base.T) C.base.s`, `¬ v.vle f 0`) and
apply `rationalOpen_subset_base_via_cov_plus_piece_lift_predicate`
for the cover refinement clause. The other two clauses of the C1
supplier output read directly from the supply.

This route AVOIDS the universal-over-`Spa(Loc s, ⁺)` per-`w` quantifier
of T039 component 5 entirely. The remaining mathematical content is
the source-restricted predicate `WedhornCoverPieceCovPlusPieceLiftPerTBound`,
which is the natural localized analog of Wedhorn 7.45's cover-
refinement deduction restricted to `w` actually arising as cover-plus-
piece lifts. -/
theorem C1SupplierStrong_local_via_cov_plus_piece_lift_supplier
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (h_per_call_supply :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        WedhornC1PerCallSupplyCovPlusPieceLift P C hopen_base D v) :
    C1SupplierStrong_local C := by
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨f, h_pred, hv_in_plus, hvf_nz⟩ :=
    h_per_call_supply D hD v hv t ht hvt hvD_s
  refine ⟨f, hv_in_plus, ?_, hvf_nz⟩
  exact rationalOpen_subset_base_via_cov_plus_piece_lift_predicate
    P C.base.T C.base.s hopen_base hA₀_le C.base.T D.T D.s f
    (Finset.subset_insert _ _) h_pred

end ValuationSpectrum

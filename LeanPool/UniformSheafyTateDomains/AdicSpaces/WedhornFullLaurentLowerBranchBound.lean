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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLaurentPieceFactoredChain

/-!
# Wedhorn 8.34(ii) full Laurent lower-branch σ_loc-bound supplier (T030)

Bridges the **lower-half full Laurent branch rational-open membership**
into the branch-local σ_loc-upper-bound consumed by T029's
`laurent_piece_α_s_D_per_t_factored_chain`. At a fixed
`w ∈ Spa(Localization.Away s, locSubring P T s)` plus localized data
`(T_D, s_D, σ_loc)` from the localized Cor 7.32 supplier (T027), the
lower-branch hypothesis takes the form

`w ∈ rationalOpen (T_D.image (algebraMap A (Localization.Away s)))
       (σ_loc : Localization.Away s)`

which is exactly the **V_∅ piece** of the full binary Laurent refinement
at the σ_loc-rescaled `T_D.image` elements (the piece where every
`σ_loc⁻¹ * t'` lies in the "≤ 1" half-space). This rational-open
membership unfolds to the per-`t'` upper bound `w.vle t' σ_loc` at the
underlying valuation level.

Composing with T029's α_s_D-branch arithmetic
(`laurent_piece_α_s_D_per_t_factored_chain`) yields the per-`t'`
σ-factored conclusion `w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)`
from two natural rational-open hypotheses:

1. α_s_D-branch Laurent piece: `w ∈ rationalOpen {(1 : Loc s)}
   (σ_loc⁻¹ * algebraMap s_D)` (T027's localized Laurent-piece membership
   at the α_s_D specialisation).
2. Lower-half full Laurent branch:
   `w ∈ rationalOpen (T_D.image (algebraMap)) σ_loc` (the V_∅ piece of
   the σ_loc-rescaled T_D.image refinement).

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson /
  T001 / faithful-flatness / Zavyalov / bivariate-overlap content.
* No σ-power-decay revival.
* Imports only T029's committed `WedhornLaurentPieceFactoredChain`,
  which transitively brings in T027's localized Laurent-piece membership
  supplier and the rational-open / σ-cancellation API.
* Does NOT edit T028's `WedhornMPowerStructuralDataHonestFromLaurentPiece.lean`
  or any other accepted file.
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

omit [PlusSubring A] in
/-- **σ_loc-upper-bound on `T_D.image` from lower-half rational-open
membership**.

From the rational-open membership
`w ∈ rationalOpen (T_D.image (algebraMap A (Localization.Away s)))
(σ_loc : Localization.Away s)` (the V_∅ piece of the σ_loc-rescaled
full Laurent refinement at `T_D.image`), extract the per-`t'` upper
bound `∀ t' ∈ T_D.image, w.vle t' σ_loc` consumed by T029's
`laurent_piece_α_s_D_per_t_factored_chain`.

This is the **direct unfolding** of the rational-open membership's
per-element-bound conjunct, packaged as a labeled API for downstream
composition. The non-vanishing conjunct `¬ w.vle σ_loc 0` is
auto-discharged by `not_vle_zero_of_isUnit` since `σ_loc` is a unit;
this lemma does NOT require it as an output. -/
theorem sigma_loc_upper_bound_of_lower_branch_at
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (σ_loc : (Localization.Away s)ˣ)
    (w : Spv (Localization.Away s))
    (h_lower_branch :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      w ∈ rationalOpen
        (T_D.image (algebraMap A (Localization.Away s)))
        (σ_loc : Localization.Away s)) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle t' (σ_loc : Localization.Away s) :=
  h_lower_branch.2.1

omit [PlusSubring A] in
/-- **α_s_D per-`t'` σ-factored chain from two rational-open
hypotheses (T030 main composed deliverable)**.

Composed consumer: from the α_s_D-branch Laurent-piece membership
(`w ∈ rationalOpen {(1 : Loc s)} (σ_loc⁻¹ * algebraMap s_D)`,
supplied by T027) plus the lower-half full Laurent branch membership
(`w ∈ rationalOpen (T_D.image (algebraMap)) σ_loc`, the V_∅ piece of
the σ_loc-rescaled T_D.image refinement), derive the per-`t'`
σ-factored conclusion
`w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)` consumed by T021's
honest structural supplier.

**Proof structure**:
1. Apply `sigma_loc_upper_bound_of_lower_branch_at` to the lower-half
   branch hypothesis to extract `∀ t' ∈ T_D.image, w.vle t' σ_loc`.
2. Apply T029's `laurent_piece_α_s_D_per_t_factored_chain` with the
   α_s_D-branch Laurent-piece membership and the extracted bound.

This composed theorem captures the **canonical chain** from full
Laurent cover refinement to T021's per-`t'` σ-factored conclusion at
a single Spa point `w` in the α_s_D branch. -/
theorem alpha_s_D_per_t_factored_chain_via_lower_branch
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (w : Spv (Localization.Away s))
    (h_laurent_α_s_D :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      w ∈ rationalOpen
        ({(1 : Localization.Away s)} : Finset (Localization.Away s))
        (((σ_loc⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) *
          algebraMap A (Localization.Away s) s_D))
    (h_lower_branch :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      w ∈ rationalOpen
        (T_D.image (algebraMap A (Localization.Away s)))
        (σ_loc : Localization.Away s)) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle (t' * (σ_loc : Localization.Away s))
        ((algebraMap A (Localization.Away s) s_D) *
          (σ_loc : Localization.Away s)) :=
  laurent_piece_α_s_D_per_t_factored_chain P T s hopen T_D s_D σ_loc w
    h_laurent_α_s_D
    (sigma_loc_upper_bound_of_lower_branch_at P T s hopen T_D σ_loc w h_lower_branch)

end ValuationSpectrum

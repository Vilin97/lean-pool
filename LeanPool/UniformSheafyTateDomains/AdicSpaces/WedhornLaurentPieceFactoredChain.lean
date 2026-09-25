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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalCor732ToFactoredChain

/-!
# Wedhorn 8.34(ii) per-Laurent-piece factored chain arithmetic (T029)

Per-`w` arithmetic bridge for the localized Wedhorn 8.34(ii) supplier
chain: at a fixed `w ∈ Spa(Localization.Away s, locSubring P T s)`,
given Laurent-piece membership at the α_s_D specialisation
(`τ = algebraMap A (Localization.Away s) s_D`, supplied by T027's
`localized_cor732_laurent_piece_membership_at`) plus an explicit
**branch-local σ_loc-upper-bound** on each
`t' ∈ T_D.image (algebraMap A (Localization.Away s))`, derive the
per-`t'` σ-factored conclusion
`w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)` consumed by T021's
honest structural supplier.

## Algebraic chain at `w` (α_s_D branch)

1. Laurent-piece membership unwraps to:
   * `w.vle 1 (σ_loc⁻¹ * algebraMap s_D)` (the only inequality in the
     singleton-`{1}` rational-open) which left-multiplies by `σ_loc` to
     `w.vle σ_loc (algebraMap s_D)`;
   * `¬ w.vle (σ_loc⁻¹ * algebraMap s_D) 0` (denominator
     non-vanishing).

2. Branch-local hypothesis: `∀ t' ∈ T_D.image (algebraMap), w.vle t' σ_loc`.

3. Transitivity: `w.vle t' σ_loc ≤ algebraMap s_D` for each `t'`.

4. σ-cancellation lift (`vle_iff_mul_unit_right`):
   `w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)`.

## Why the branch-local σ_loc-upper-bound is needed

The σ-power-decay route (T023) and direct multi-element-bound route
(T024) were shown false or under-specified for arbitrary `T_D`. The
Laurent-piece membership at α_s_D supplies `σ_loc ≤ algebraMap s_D`
(a single comparison), but **does NOT** supply per-`t'` ordering of
`T_D.image` elements relative to `σ_loc` or `algebraMap s_D`. The
per-`t'` σ_loc-upper-bound `w.vle t' σ_loc` is the **explicit
additional input** required by T021's honest structural supplier,
corresponding to Wedhorn's full Laurent cover refinement at every
`σ_loc`-rescaled element of `T_D.image`. (At `w` in a specific
Laurent piece V_K of the full refinement, each `t' ∈ T_D.image` is
either in `σ_loc`'s "≤ 1" half or its "≥ 1" half; the α_s_D-only
branch where ALL `t'` are in `σ_loc`'s "≤ 1" half corresponds to
V_∅ of that full refinement.)

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson /
  T001 / faithful-flatness / Zavyalov / bivariate-overlap content.
* No σ-power-decay revival.
* Imports only T027's committed `WedhornLocalCor732ToFactoredChain`,
  which transitively brings in T024's algebraic decomposition lemmas
  (`WedhornDominatingUnitInequality`) and σ-cancellation primitives
  (`WedhornMultiBranchSubsetInequality`).
* Does NOT import or edit Secondary-owned T028 files.
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

omit [PlusSubring A] in
/-- **Per-Laurent-piece α_s_D branch σ-le extraction**.

From Laurent-piece membership at the α_s_D specialisation
(`τ = algebraMap s_D`) — namely
`w ∈ rationalOpen ({(1 : Localization.Away s)} : Finset _)
((σ_loc⁻¹ : (Loc s)ˣ) * algebraMap s_D)` — extract:

* `w.vle (σ_loc : Loc s) (algebraMap s_D)` — σ_loc is bounded above by
  `algebraMap s_D` at `w`;
* `¬ w.vle (algebraMap s_D) 0` — `algebraMap s_D` is non-vanishing at
  `w`.

Both pieces are derived by left-multiplying the rational-open's
internal inequalities by `(σ_loc : Loc s)` (a unit), using
`Units.mul_inv` to simplify `σ_loc * σ_loc⁻¹ = 1`.

These are the **branch-data extractions** consumed by the per-`t'`
factored chain theorem below; they correspond to the α_s_D-branch
slice of T021's honest structural supplier hypotheses. -/
theorem laurent_piece_α_s_D_extract
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (s_D : A) (σ_loc : (Localization.Away s)ˣ)
    (w : Spv (Localization.Away s))
    (h_laurent :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      w ∈ rationalOpen
        ({(1 : Localization.Away s)} : Finset (Localization.Away s))
        (((σ_loc⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) *
          algebraMap A (Localization.Away s) s_D)) :
    w.vle (σ_loc : Localization.Away s)
      (algebraMap A (Localization.Away s) s_D) ∧
    ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
  obtain ⟨_hw_spa, hw_one_le, hw_ne⟩ := h_laurent
  have h_one_le_inv :
      w.vle (1 : Localization.Away s)
        (((σ_loc⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) *
          algebraMap A (Localization.Away s) s_D) :=
    hw_one_le 1 (Finset.mem_singleton.mpr rfl)
  refine ⟨?_, ?_⟩
  · have h_mul :
        w.vle ((σ_loc : Localization.Away s) * (1 : Localization.Away s))
          ((σ_loc : Localization.Away s) *
            (((σ_loc⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) *
              algebraMap A (Localization.Away s) s_D)) :=
      ValuativeRel.mul_vle_mul_right h_one_le_inv (σ_loc : Localization.Away s)
    rw [mul_one, ← mul_assoc, Units.mul_inv, one_mul] at h_mul
    exact h_mul
  · intro h_s_D_zero
    apply hw_ne
    have h_mul :
        w.vle (((σ_loc⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) *
            algebraMap A (Localization.Away s) s_D)
          (((σ_loc⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) * 0) :=
      ValuativeRel.mul_vle_mul_right h_s_D_zero
        (((σ_loc⁻¹ : (Localization.Away s)ˣ) : Localization.Away s))
    rw [mul_zero] at h_mul
    exact h_mul

omit [PlusSubring A] in
/-- **Per-Laurent-piece α_s_D branch factored chain theorem (main T029
deliverable)**.

From Laurent-piece membership at the α_s_D specialisation plus the
**branch-local σ_loc-upper-bound** `∀ t' ∈ T_D.image, w.vle t' σ_loc`,
derive the per-`t'` σ-factored conclusion
`w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)` consumed by T021's
honest structural supplier.

**Proof structure**:
1. Apply `laurent_piece_α_s_D_extract` to get
   `w.vle σ_loc (algebraMap s_D)` from the Laurent-piece hypothesis.
2. Compose with the branch-local σ_loc-upper-bound via `vle_trans` to
   get `w.vle t' (algebraMap s_D)` for each `t' ∈ T_D.image`.
3. Lift via `vle_iff_mul_unit_right` (σ-cancellation lift): the
   per-`t'` upper bound `w.vle t' (algebraMap s_D)` is equivalent to
   the σ-factored form `w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)`.

This is the **narrowest true** per-Laurent-piece arithmetic bridge for
the α_s_D branch of T021's honest structural supplier; the analogous
α_T_D branch (with `τ ∈ T_D.image (algebraMap)` as the σ-strict-dom
witness) requires a different intermediate (typically a τ-versus-
algebraMap-s_D comparison) and is not in this theorem's scope. -/
theorem laurent_piece_α_s_D_per_t_factored_chain
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (w : Spv (Localization.Away s))
    (h_laurent :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      w ∈ rationalOpen
        ({(1 : Localization.Away s)} : Finset (Localization.Away s))
        (((σ_loc⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) *
          algebraMap A (Localization.Away s) s_D))
    (h_t_le_σ_loc :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle t' (σ_loc : Localization.Away s)) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle (t' * (σ_loc : Localization.Away s))
        ((algebraMap A (Localization.Away s) s_D) *
          (σ_loc : Localization.Away s)) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro t' ht'
  obtain ⟨h_σ_le_s_D, _h_s_D_ne⟩ :=
    laurent_piece_α_s_D_extract P T s hopen s_D σ_loc w h_laurent
  have h_t_le_s_D :
      w.vle t' (algebraMap A (Localization.Away s) s_D) :=
    w.vle_trans (h_t_le_σ_loc t' ht') h_σ_le_s_D
  exact (vle_iff_mul_unit_right w σ_loc t'
    (algebraMap A (Localization.Away s) s_D)).mpr h_t_le_s_D

end ValuationSpectrum

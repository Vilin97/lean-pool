/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornRationalOpenLocalizationTransfer
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalizedCor732Application
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornCor732BranchTransfer

/-!
# Wedhorn local per-branch chain — base subset inclusion via localization

Composes the localized strict-domination data (Cor 7.32 inside
`Spa(Localization.Away s, locSubring P T s)`) with the local
rational-open transfer to discharge the base-side subset inclusion
needed by Wedhorn 8.34(ii):

`rationalOpen (insert f T_base) s ⊆ rationalOpen T_D s_D`

at the base ring `A`, where `f ∈ A` is a denominator-cleared candidate
whose algebraMap-image equals `σ_loc · (∏ algebraMap T_D)` for the
localized dominating unit `σ_loc ∈ (Localization.Away s)ˣ`.

## Strategy

1. Use a **freestanding local reducer** (no `RationalCoveringData` wrapper)
   at the localization to convert localized σ-strict-domination data
   plus the local per-branch chain (`hT_test_compat_loc`) into a local
   rational-open subset inclusion on
   `Spa(Localization.Away s, locSubring P T s)`.

2. Use the algebraic identity
   `algebraMap f = (σ_loc) · (∏ algebraMap T_D)` (denominator-cleared
   candidate) to rewrite the source rational-open as
   `R_loc(insert (algebraMap f) (T_base.image algebraMap)) (algebraMap s)`.

3. Apply the previously-committed
   `rationalOpen_subset_via_localization_locSubring` (commit `78961d8`)
   to pull back the local inclusion to the base.

The localized Cor 7.32 hypotheses (`hLin`, `π_loc`, `hI_loc`, etc.) are
NOT internalised here — `exists_dominating_unit_in_localization` is the
supplier and is called by the consumer when assembling the data; this
file consumes the σ-strict-domination output directly.

## What this file provides

* `rationalOpen_subset_via_strict_sigma_domination_freestanding` —
  freestanding analog of
  `WedhornMultiDominatingUnit.rationalOpen_subset_via_strict_sigma_domination`
  with no `RationalCoveringData` wrapper. Direct proof; reusable at the
  localization side.

* `rationalOpen_subset_base_via_local_Cor732_chain` — the **caller-shaped
  composed theorem**: given a denominator-cleared base candidate `f`
  with the algebraic identity, plus the localized strict-domination
  data and the local per-branch chain, produce the base subset inclusion
  `R(insert f T_base) s ⊆ R(T_D, s_D)`. Composes (1), the algebraic
  identity, and the locSubring pullback.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness content.
* Does not edit Tertiary's wrapper/lift files, Primary's files, or
  any in-flight file.
* Reuses `exists_dominating_unit_in_localization`
  (`WedhornLocalizedCor732Application.lean:84`) and
  `rationalOpen_subset_via_localization_locSubring`
  (committed `78961d8`).
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

omit [IsTopologicalRing A] in
/-- **Freestanding strict-σ-domination rationalOpen subset reducer**
(no `RationalCoveringData` wrapper). Same shape and proof as
`WedhornMultiDominatingUnit.rationalOpen_subset_via_strict_sigma_domination`,
but parameterised directly by `(T_base, s_base, T_D, s_D)` rather than
through `RationalCoveringData`/`RationalLocData` field accesses; reusable
at any base ring including `Localization.Away s` with the `locSubring`
plus-subring. -/
theorem rationalOpen_subset_via_strict_sigma_domination_freestanding
    [DecidableEq A]
    (T_base : Finset A) (s_base : A) (T_D : Finset A) (s_D : A)
    (σ : Aˣ) (T_test : Finset A)
    (hσ : ∀ w ∈ Spa A A⁺, ∃ τ ∈ T_test,
      w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A))
    (hT_test_compat : ∀ τ ∈ T_test, ∀ w ∈ Spa A A⁺,
      w.vle ((σ : A) * (∏ t ∈ T_D, t)) s_base →
      w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A) →
        (∀ t' ∈ T_D, w.vle t' s_D) ∧ ¬ w.vle s_D 0) :
    rationalOpen (insert ((σ : A) * (∏ t ∈ T_D, t)) T_base) s_base ⊆
      rationalOpen T_D s_D := by
  intro w hw
  obtain ⟨hw_spa, hwIns, _⟩ := hw
  have hw_f : w.vle ((σ : A) * (∏ t ∈ T_D, t)) s_base :=
    hwIns _ (Finset.mem_insert_self _ _)
  obtain ⟨τ, hτ_mem, hστ⟩ := hσ w hw_spa
  obtain ⟨hwD, hwDs⟩ := hT_test_compat τ hτ_mem w hw_spa hw_f hστ
  exact ⟨hw_spa, hwD, hwDs⟩

/-- **Caller-shaped composed theorem**: from localized strict-σ-domination
data and the local per-branch chain on
`Spa(Localization.Away s, locSubring P T s)`, plus the algebraic
denominator-clearing identity `algebraMap f = σ_loc · (∏ algebraMap T_D)`,
derive the base subset inclusion
`R(insert f T_base) s ⊆ R(T_D, s_D)` on `Spa(A, A⁺)`.

**Composition steps**:
1. `rationalOpen_subset_via_strict_sigma_domination_freestanding` at
   the localization side (with `B := Localization.Away s` and the local
   plus-subring `locSubring P T s`) → local rational-open subset
   inclusion.
2. Rewrite via `h_alg` to express the source as `insert (algebraMap f)
   (T_base.image algebraMap)`.
3. Convert the set-level local inclusion into the conditional
   `h_local` form consumed by
   `rationalOpen_subset_via_localization_locSubring`.
4. Apply `rationalOpen_subset_via_localization_locSubring` to pull back
   to the base.

The localized Cor 7.32 supplier (`exists_dominating_unit_in_localization`)
is the natural source of `(σ_loc, T_test_loc, hσ_loc)`; the per-branch
chain `h_T_test_compat_loc` is the explicit Wedhorn-content input. -/
theorem rationalOpen_subset_base_via_local_Cor732_chain
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (hA₀_le : P.A₀ ≤ A⁺)
    (T_base T_D : Finset A) (s_D : A)
    (h_T_le_T_base : T ⊆ T_base)
    (f : A) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ (σ_loc : (Localization.Away s)ˣ)
      (_h_alg : algebraMap A (Localization.Away s) f =
         (σ_loc : Localization.Away s) *
           (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
      (T_test_loc : Finset (Localization.Away s))
      (_hσ_loc : ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ T_test_loc,
          w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s))
      (_h_T_test_compat_loc : ∀ τ ∈ T_test_loc,
        ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
          w.vle ((σ_loc : Localization.Away s) *
              (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
            (algebraMap A (Localization.Away s) s) →
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s) →
            (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
                w.vle t' (algebraMap A (Localization.Away s) s_D)) ∧
              ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0),
      rationalOpen (insert f T_base) s ⊆ rationalOpen T_D s_D := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro σ_loc h_alg T_test_loc hσ_loc h_T_test_compat_loc
  -- Step 1: freestanding reducer at the localization side.
  have h_local_inclusion :
      rationalOpen
        (insert ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (T_base.image (algebraMap A (Localization.Away s))))
        (algebraMap A (Localization.Away s) s) ⊆
      rationalOpen
        (T_D.image (algebraMap A (Localization.Away s)))
        (algebraMap A (Localization.Away s) s_D) :=
    rationalOpen_subset_via_strict_sigma_domination_freestanding
      (T_base.image (algebraMap A (Localization.Away s)))
      (algebraMap A (Localization.Away s) s)
      (T_D.image (algebraMap A (Localization.Away s)))
      (algebraMap A (Localization.Away s) s_D)
      σ_loc T_test_loc hσ_loc h_T_test_compat_loc
  -- Step 2 + 3: convert to h_local form for rationalOpen_subset_via_localization_locSubring.
  have h_local :
      ∀ w : Spv (Localization.Away s),
        w ∈ Spa (Localization.Away s) (Localization.Away s)⁺ →
        (∀ t ∈ insert f T_base,
          w.vle (algebraMap A (Localization.Away s) t)
            (algebraMap A (Localization.Away s) s)) →
        ¬ w.vle (algebraMap A (Localization.Away s) s) 0 →
        (∀ t ∈ T_D, w.vle (algebraMap A (Localization.Away s) t)
            (algebraMap A (Localization.Away s) s_D)) ∧
        ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 := by
    intro w hw_spa hw_T1 hw_s_ne
    -- Show w lies in the local source rational-open.
    have hw_loc_source : w ∈ rationalOpen
        (insert ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (T_base.image (algebraMap A (Localization.Away s))))
        (algebraMap A (Localization.Away s) s) := by
      refine ⟨hw_spa, ?_, hw_s_ne⟩
      intro t ht
      rw [Finset.mem_insert] at ht
      rcases ht with rfl | ht
      · -- t = (σ_loc) * (∏ T_D image), use h_alg.symm and hw_T1 at f.
        rw [← h_alg]
        exact hw_T1 f (Finset.mem_insert_self _ _)
      · -- t ∈ T_base.image algebraMap; pull back to t' ∈ T_base.
        obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
        exact hw_T1 t' (Finset.mem_insert_of_mem ht')
    -- Apply local inclusion to deduce w in local target rational-open.
    obtain ⟨_, hw_T_D_loc, hw_s_D_ne⟩ := h_local_inclusion hw_loc_source
    refine ⟨fun t ht ↦ ?_, hw_s_D_ne⟩
    exact hw_T_D_loc (algebraMap A (Localization.Away s) t)
      (Finset.mem_image.mpr ⟨t, ht, rfl⟩)
  -- Step 4: pull back via rationalOpen_subset_via_localization_locSubring.
  exact rationalOpen_subset_via_localization_locSubring P T (insert f T_base) T_D s s_D
    hopen hA₀_le
    (Finset.Subset.trans h_T_le_T_base (Finset.subset_insert f T_base))
    h_local

end ValuationSpectrum

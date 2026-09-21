/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornSourceSigmaDecayFromLocalizedChain

/-!
# Wedhorn 8.34(ii) — Source Laurent membership in localization base API (T088)

T086 (`WedhornSourceSigmaDecayFromLocalizedChain`) introduces the
named precondition
`SourceLaurentMembershipInLocalizationBase T s T_D s_base f`,
the per-`(w, t')` claim that source-restricted Laurent piece witnesses
sit inside the localization base rational open `R(T, s)`. T086 leaves
this precondition unstructured: it must be supplied by callers.

T088 lands the **structural API** around this precondition: producers
that let downstream callers discharge it from natural rational-open
data, plus a trivial-localization auto-discharger and an end-to-end
consumer composing T088's API with T086's main theorem.

## Predicate decomposition

`SourceLaurentMembershipInLocalizationBase T s T_D s_base f` requires,
at every per-`(t', w)` source-restricted Laurent-piece witness, that
`w ∈ rationalOpen T s`. Unfolding the rational-open definition, the
membership at `w` reduces to three conjuncts:

* `w ∈ Spa A A⁺` — already part of the per-`(t', w)` source-restricted
  hypothesis pack; passes through directly.
* `∀ t ∈ T, w.vle t s` — the per-`t ∈ T` upper bound by `s` at `w`.
* `¬ w.vle s 0` — non-vanishing of `s` at `w`.

T088's main producer is the **per-t + s-non-vanishing splitter**: from
two suppliers covering the per-`t` bound and the s-non-vanishing
conjuncts (each quantified over the same per-`(t', w)` source-
restricted set), the predicate follows by direct unfolding.

## Trivial localization auto-discharger

When `T = ∅` and `s = 1`, `rationalOpen ∅ 1 = Spa A A⁺` (the per-t
conjunct is vacuous and the s-non-vanishing conjunct is the universal
Spv axiom `not_vle_one_zero`). The predicate is thus automatic without
any further suppliers, witnessing that T086's composition theorem is
non-vacuously instantiable at the degenerate localization
`Localization.Away 1 ≅ A`.

## What this file provides

* `source_laurent_membership_in_localization_base_id` — typed identity
  producer (boundary primitive).

* `source_laurent_membership_in_localization_base_of_per_t_and_s_nonvan`
  — substantive splitter: produce the predicate from a per-`t ∈ T`
  bound supplier and an s-non-vanishing supplier. Real unfolding of
  `rationalOpen` membership.

* `source_laurent_membership_in_localization_base_of_subset_at_w` —
  produce from a per-`(t', w)` direct rationalOpen-membership supplier
  (alternative typed boundary).

* `source_laurent_membership_in_localization_base_empty_T_one_s` —
  trivial-localization auto-discharger: the predicate at `(T = ∅,
  s = 1)` is automatic via `Spv.not_vle_one_zero`.

* `localized_cor732_sigma_decay_chain_supplier_from_per_t_and_s_nonvan`
  — end-to-end consumer composing T088's per-t + s-non-vanishing
  splitter with T086's
  `localized_cor732_sigma_decay_chain_supplier_from_denominator_chain`
  to deliver T083's `LocalizedCor732SigmaDecayChainSupplier` directly
  from per-t + s-non-vanishing data plus T084's localized chain
  identity at the algebra-map-image source data.

* `localized_cor732_sigma_decay_chain_supplier_at_trivial_localization`
  — end-to-end consumer at the `(T = ∅, s = 1)` localization base:
  T083's residual follows automatically from T084's chain identity
  plus `hA₀_le`. No per-t / s-non-vanishing supplier required.

## Notes

* No root import; leaf-level.
* Imports T086 (`WedhornSourceSigmaDecayFromLocalizedChain`) for the
  named predicate `SourceLaurentMembershipInLocalizationBase`, the
  `Cor732SigmaDenominatorClearingChainIdentity` predicate (via T086's
  T084 transitive import), and the composition theorem
  `localized_cor732_sigma_decay_chain_supplier_from_denominator_chain`.
* No edits to T031–T087 accepted leaves, root imports, or final
  theorem signatures.
* No edits to Primary's T087 file
  (`WedhornCor732PerTauUpperBoundResidual.lean`) or Secondary's T062
  file.
* No revival of T001 / Lane-B / Jacobson / bivariate / Zavyalov /
  global universal Spa bound / σ-power-decay / M-power-decay detours.
* No final `ValuationSpectrum.tateAcyclicity` hypothesis additions.
* All declarations are fully proven, depend only on the standard Lean
  kernel postulates, and avoid native compilation and unchecked
  tactics.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-! ## Direct typed-boundary producers -/

omit [IsTopologicalRing A] in
/-- **Typed identity producer for `SourceLaurentMembershipInLocalizationBase`**.

Trivially produces the predicate from a hypothesis matching its exact
shape. Useful as the typed boundary primitive for downstream callers
who already have a per-`(t', w)` rationalOpen-membership theorem with
matching quantifier structure. -/
theorem source_laurent_membership_in_localization_base_id
    (T : Finset A) (s : A) (T_D : Finset A) (s_base f : A)
    (h : ∀ t' ∈ T_D, ∀ w ∈ Spa A A⁺,
      w.vle f s_base → w.vle (1 : A) t' → ¬ w.vle t' 0 →
      w ∈ rationalOpen T s) :
    SourceLaurentMembershipInLocalizationBase T s T_D s_base f := h

omit [IsTopologicalRing A] in
/-- **Direct rationalOpen-supplier producer**.

Alternative typed-boundary producer: bundles the source-restricted
hypotheses into a single per-`(t', w)` rationalOpen-membership
supplier, which is then forwarded as the predicate. Identical to the
identity producer but useful when the supplier is already named in
the caller's context. -/
theorem source_laurent_membership_in_localization_base_of_subset_at_w
    (T : Finset A) (s : A) (T_D : Finset A) (s_base f : A)
    (h_supplier : ∀ t' ∈ T_D, ∀ w ∈ Spa A A⁺,
      w.vle f s_base → w.vle (1 : A) t' → ¬ w.vle t' 0 →
      w ∈ rationalOpen T s) :
    SourceLaurentMembershipInLocalizationBase T s T_D s_base f :=
  h_supplier

/-! ## Substantive splitter: per-t + s-non-vanishing -/

omit [IsTopologicalRing A] in
/-- **Per-t + s-non-vanishing splitter**: produce the predicate from a
per-`t ∈ T` upper-bound supplier and an s-non-vanishing supplier
(T088 main substantive producer).

The two suppliers are quantified over the same per-`(t', w)`
source-restricted set as the predicate. The proof unfolds
`rationalOpen T s = { w ∈ Spa A A⁺ | (∀ t ∈ T, w.vle t s) ∧ ¬ w.vle s 0 }`
and discharges the three conjuncts:
* `w ∈ Spa A A⁺` — directly from the predicate's source-restricted
  hypothesis;
* `∀ t ∈ T, w.vle t s` — from `h_per_t`;
* `¬ w.vle s 0` — from `h_s_nonvan`.

**Substantive consumption**: both suppliers are genuinely used — the
per-t supplier is consumed at every `t ∈ T`, and the s-non-vanishing
supplier is consumed at every `(t', w)` source-restricted witness. -/
theorem source_laurent_membership_in_localization_base_of_per_t_and_s_nonvan
    (T : Finset A) (s : A) (T_D : Finset A) (s_base f : A)
    (h_per_t : ∀ t ∈ T, ∀ t' ∈ T_D, ∀ w ∈ Spa A A⁺,
      w.vle f s_base → w.vle (1 : A) t' → ¬ w.vle t' 0 →
      w.vle t s)
    (h_s_nonvan : ∀ t' ∈ T_D, ∀ w ∈ Spa A A⁺,
      w.vle f s_base → w.vle (1 : A) t' → ¬ w.vle t' 0 →
      ¬ w.vle s 0) :
    SourceLaurentMembershipInLocalizationBase T s T_D s_base f := by
  intro t' ht' w hw_spa hw_f hw_one_t hw_t_ne
  exact ⟨hw_spa, fun t ht => h_per_t t ht t' ht' w hw_spa hw_f hw_one_t hw_t_ne,
    h_s_nonvan t' ht' w hw_spa hw_f hw_one_t hw_t_ne⟩

/-! ## Trivial localization auto-discharger -/

omit [IsTopologicalRing A] in
/-- **Trivial-localization auto-discharger**: the predicate at the
degenerate localization base `(T = ∅, s = 1)` is automatic.

`rationalOpen ∅ 1 = Spa A A⁺ ∩ {w | (∀ t ∈ ∅, w.vle t 1) ∧ ¬ w.vle 1 0}`,
where the per-`t` conjunct is vacuous and the s-non-vanishing
conjunct is the universal Spv axiom `Spv.not_vle_one_zero` (every
`w : Spv A` satisfies `¬ w.vle 1 0`). The predicate's conclusion
`w ∈ rationalOpen ∅ 1` thus reduces to the given `w ∈ Spa A A⁺`,
needing no further suppliers.

**Why this is non-vacuous**: T086's composition theorem
`localized_cor732_sigma_decay_chain_supplier_from_denominator_chain`
takes `SourceLaurentMembershipInLocalizationBase` as a precondition;
this auto-discharger witnesses that the composition theorem is
non-vacuously instantiable at `(T, s) = (∅, 1)`, giving an unconditional
end-to-end consumer at the trivial localization base (see
`localized_cor732_sigma_decay_chain_supplier_at_trivial_localization`
below). -/
theorem source_laurent_membership_in_localization_base_empty_T_one_s
    (T_D : Finset A) (s_base f : A) :
    SourceLaurentMembershipInLocalizationBase (∅ : Finset A) (1 : A)
      T_D s_base f := by
  intro t' _ht' w hw_spa _hw_f _hw_one_t _hw_t_ne
  exact ⟨hw_spa, fun t ht => absurd ht (Finset.notMem_empty _), w.not_vle_one_zero⟩

/-! ## End-to-end consumers -/

/-- **End-to-end T088 deliverable via per-t + s-non-vanishing**:
produce T083's source σ-decay chain residual
`LocalizedCor732SigmaDecayChainSupplier` directly from per-t bound +
s-non-vanishing data plus T084's localized chain identity at the
algebra-map-image source data, via T088's splitter and T086's
composition theorem.

Closes the chain:
per-`t` + s-non-vanishing data (T088) →
`SourceLaurentMembershipInLocalizationBase` (T088 splitter) →
`LocalizedCor732SigmaDecayChainSupplier` (T086 composition).

**Substantive consumption**: every input is genuinely used —
`h_chain_at_images` is fed to T086's composition theorem;
`h_per_t`, `h_s_nonvan` are consumed by the splitter to produce
the named predicate; `hA₀_le` is consumed by T086's lift in the
composition. -/
theorem localized_cor732_sigma_decay_chain_supplier_from_per_t_and_s_nonvan
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (hA₀_le : P.A₀ ≤ A⁺)
    (T_D : Finset A) (s_D s_base f : A)
    (h_chain_at_images :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      Cor732SigmaDenominatorClearingChainIdentity P T s hopen T_D s_D
        (localizedTestFamily s T_D s_D)
        (algebraMap A (Localization.Away s) s_base)
        (algebraMap A (Localization.Away s) s_D)
        (algebraMap A (Localization.Away s) f))
    (h_per_t : ∀ t ∈ T, ∀ t' ∈ T_D, ∀ w ∈ Spa A A⁺,
      w.vle f s_base → w.vle (1 : A) t' → ¬ w.vle t' 0 →
      w.vle t s)
    (h_s_nonvan : ∀ t' ∈ T_D, ∀ w ∈ Spa A A⁺,
      w.vle f s_base → w.vle (1 : A) t' → ¬ w.vle t' 0 →
      ¬ w.vle s 0) :
    LocalizedCor732SigmaDecayChainSupplier P T s hopen T_D s_D s_base f :=
  localized_cor732_sigma_decay_chain_supplier_from_denominator_chain
    P T s hopen hA₀_le T_D s_D s_base f h_chain_at_images
    (source_laurent_membership_in_localization_base_of_per_t_and_s_nonvan
      T s T_D s_base f h_per_t h_s_nonvan)

/-- **End-to-end T088 deliverable at the trivial localization base**
`(T, s) = (∅, 1)`: produce T083's
`LocalizedCor732SigmaDecayChainSupplier` automatically from T084's
chain identity at the algebra-map-image source data plus `hA₀_le`,
with no per-t / s-non-vanishing supplier needed.

The trivial localization base auto-dischargers the
`SourceLaurentMembershipInLocalizationBase` precondition via
`Spv.not_vle_one_zero`. The remaining inputs are exactly T084's
chain identity and the standard `hA₀_le : P.A₀ ≤ A⁺` (consumed by
T086's lift internally).

**Why this is non-trivial**: it shows T086's composition theorem
yields T083's σ-decay chain residual unconditionally on the
`SourceLaurentMembershipInLocalizationBase` precondition at the
trivial localization base, demonstrating the composition route is
non-vacuous at this canonical instantiation. -/
theorem localized_cor732_sigma_decay_chain_supplier_at_trivial_localization
    (P : PairOfDefinition A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) 1 ∈ locSubring P (∅ : Finset A) 1)
    (hA₀_le : P.A₀ ≤ A⁺)
    (T_D : Finset A) (s_D s_base f : A)
    (h_chain_at_images :
      letI : TopologicalSpace (Localization.Away (1 : A)) :=
        locTopology P (∅ : Finset A) 1 hopen
      letI : PlusSubring (Localization.Away (1 : A)) :=
        localizationLocSubringPlusSubring P (∅ : Finset A) 1
      Cor732SigmaDenominatorClearingChainIdentity P (∅ : Finset A) 1 hopen
        T_D s_D
        (localizedTestFamily 1 T_D s_D)
        (algebraMap A (Localization.Away (1 : A)) s_base)
        (algebraMap A (Localization.Away (1 : A)) s_D)
        (algebraMap A (Localization.Away (1 : A)) f)) :
    LocalizedCor732SigmaDecayChainSupplier P (∅ : Finset A) 1 hopen
      T_D s_D s_base f :=
  localized_cor732_sigma_decay_chain_supplier_from_denominator_chain
    P (∅ : Finset A) 1 hopen hA₀_le T_D s_D s_base f h_chain_at_images
    (source_laurent_membership_in_localization_base_empty_T_one_s
      T_D s_base f)

end ValuationSpectrum

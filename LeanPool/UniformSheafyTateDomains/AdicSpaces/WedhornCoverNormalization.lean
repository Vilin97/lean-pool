/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Presheaf
import LeanPool.UniformSheafyTateDomains.AdicSpaces.RationalSubsets

/-!
# Wedhorn Cover Normalization (insert-denominator transform)

Wedhorn Remark 7.30(3) at the rational-localization-data level: adding the
denominator `D.s` to the generating set `D.T` of a rational localization
datum produces the *same* rational open. This file lifts that observation
to a cover-level normalization, so that downstream consumers (notably the
C1/C2 Wedhorn-standard-cover assembly) can assume `D.s ∈ D.T` without
making it a final-theorem hypothesis.

## What this file gives

* `locSubring_mono_T` — `T₁ ⊆ T₂ → locSubring P T₁ s ≤ locSubring P T₂ s`.
* `RationalLocData.insertDenom` — the rational-locale-data transform that
  adds `D.s` to `D.T` while keeping `P, s` unchanged; `hopen` upgrades via
  `locSubring_mono_T`.
* `RationalLocData.insertDenom_s_mem` — `D.s ∈ D.insertDenom.T`.
* `RationalLocData.rationalOpen_insertDenom` — `rationalOpen` is unchanged.
* `RationalCoveringData.insertDenom` — the cover-level normalization, applying
  `RationalLocData.insertDenom` to base and each piece.
* `RationalCoveringData.insertDenom_normalized` — every piece satisfies
  `D.s ∈ D.T`.
* `RationalCoveringData.insertDenom_base_open` — the base rational open is
  unchanged as a set of valuations.

The transform is purely combinatorial / set-theoretic; no Lane B / Cor 8.32 /
Jacobson / faithful-flatness / T001 / final-acyclicity content. The single
analytic ingredient is `locSubring_mono_T`, which is a one-line monotonicity
on `Subring.closure`.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [DecidableEq A]

omit [IsTopologicalRing A] [DecidableEq A] in
/-- **Localization-subring monotonicity in `T`**. Adding more elements to
the generating set `T` enlarges (does not shrink) the ring of definition
`locSubring P T s`. Pure `Subring.closure` monotonicity. -/
theorem locSubring_mono_T {T₁ T₂ : Finset A} (h : T₁ ⊆ T₂)
    (P : PairOfDefinition A) (s : A) :
    locSubring P T₁ s ≤ locSubring P T₂ s := by
  unfold locSubring
  apply Subring.closure_mono
  apply Set.union_subset_union_right
  rintro _ ⟨⟨t, ht⟩, rfl⟩
  exact ⟨⟨t, h ht⟩, rfl⟩

/-- **Rational-locale-data insert-denominator transform** (Wedhorn Remark
7.30(3) at the data level). Adds the denominator `D.s` to `D.T`; `P, s`
are unchanged, and `hopen` upgrades via `locSubring_mono_T`. -/
def RationalLocData.insertDenom (D : RationalLocData A) : RationalLocData A where
  P := D.P
  T := insert D.s D.T
  s := D.s
  hopen := by
    obtain ⟨N, hN⟩ := D.hopen
    refine ⟨N, fun b hb => ?_⟩
    exact locSubring_mono_T (Finset.subset_insert _ _) D.P D.s (hN b hb)

@[simp]
theorem RationalLocData.insertDenom_s (D : RationalLocData A) :
    D.insertDenom.s = D.s := rfl

@[simp]
theorem RationalLocData.insertDenom_T (D : RationalLocData A) :
    D.insertDenom.T = insert D.s D.T := rfl

@[simp]
theorem RationalLocData.insertDenom_P (D : RationalLocData A) :
    D.insertDenom.P = D.P := rfl

/-- The denominator `D.s` is in the generating set after `insertDenom`. -/
theorem RationalLocData.insertDenom_s_mem (D : RationalLocData A) :
    D.s ∈ D.insertDenom.T :=
  Finset.mem_insert_self _ _

section RationalCoveringDataSection

variable [PlusSubring A]

/-- **Wedhorn Remark 7.30(3) at the data level**: the rational open is
preserved by `insertDenom`. Direct corollary of
`RationalSubsets.rationalOpen_insert_s`. The `[PlusSubring A]` instance
is needed because `rationalOpen` is defined relative to `Spa A A⁺`. -/
theorem RationalLocData.rationalOpen_insertDenom
    (D : RationalLocData A) :
    rationalOpen D.insertDenom.T D.insertDenom.s = rationalOpen D.T D.s :=
  rationalOpen_insert_s D.T D.s

/-- **Rational-cover insert-denominator transform**. Applies
`RationalLocData.insertDenom` to the base and to each piece; both base and
pieces satisfy `D.s ∈ D.T` after the transform. The rational-open structure
is unchanged on every piece because `rationalOpen_insert_s` is a set
equality, so `hsubset`/`hcover` carry over from `C`. -/
noncomputable def RationalCoveringData.insertDenom
    (C : RationalCoveringData A) : RationalCoveringData A :=
  letI : DecidableEq (RationalLocData A) := Classical.decEq _
  { base := C.base.insertDenom
    covers := C.covers.image RationalLocData.insertDenom
    hsubset := by
      intro D' hD'
      obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hD'
      rw [RationalLocData.rationalOpen_insertDenom D,
        RationalLocData.rationalOpen_insertDenom C.base]
      exact C.hsubset D hD
    hcover := by
      intro v hv
      rw [RationalLocData.rationalOpen_insertDenom C.base] at hv
      obtain ⟨D, hD, hvD⟩ := C.hcover v hv
      refine ⟨D.insertDenom, Finset.mem_image.mpr ⟨D, hD, rfl⟩, ?_⟩
      rw [RationalLocData.rationalOpen_insertDenom D]
      exact hvD }

/-- After `RationalCoveringData.insertDenom`, every piece is normalized:
`D.s ∈ D.T`. -/
theorem RationalCoveringData.insertDenom_normalized
    (C : RationalCoveringData A) :
    ∀ D ∈ C.insertDenom.covers, D.s ∈ D.T := by
  letI : DecidableEq (RationalLocData A) := Classical.decEq _
  intro D hD
  obtain ⟨D₀, _, rfl⟩ := Finset.mem_image.mp hD
  exact D₀.insertDenom_s_mem

/-- After `RationalCoveringData.insertDenom`, the base rational open is
unchanged as a set of valuations. -/
theorem RationalCoveringData.insertDenom_base_open
    (C : RationalCoveringData A) :
    rationalOpen C.insertDenom.base.T C.insertDenom.base.s =
      rationalOpen C.base.T C.base.s :=
  RationalLocData.rationalOpen_insertDenom C.base

end RationalCoveringDataSection

/-! ## Integrality and pair-pinning support API (T118)

Reusable `Prop` wrappers for the integrality / shared-pair side conditions
that the corrected T089 locNhd-form witness residual chain requires when
operating on arbitrary `RationalLocData`. After T117's blocker audit, the
private chain `locLift_preimage_target_witness_existence` →
`restrictionMapHom_ker_isTorsion` is provable only with three local
hypotheses on the rational data:

* `D.s ∈ D.P.A₀` and `∀ t ∈ D.T, t ∈ D.P.A₀` — packaged here as
  `RationalLocData.IntegralInPair`.
* `D.P = D₀.P` — packaged as `RationalLocData.SamePair`.
* (Cover-level): all pieces of a `RationalCoveringData` carry the same pair as
  the base — packaged as `RationalCoveringData.PinnedTo`.

Together with the existing `PairOfDefinition.mem_powerBoundedSubring`
(`HuberRings.lean:188`), the integrality assumption gives A-level
`TopologicalRing.IsPowerBounded` for `D.s` and elements of `D.T`, which is
exactly what `PairOfDefinition.adjoin` needs (Wedhorn 6.1 ring-of-definition
enlargement).

This API is non-overlapping with Secondary's `WedhornAwayMapSaturation`
denominator-clearing lane (T114): it concerns the *side-condition packaging*
that any ultimate discharge route must consume, not the algebraic core.

## Construction lemmas

* `globalLocData_integralInPair` — the global rational datum (`T = {1}, s = 1`)
  is integral in any pair.
* `RationalLocData.IntegralInPair.insertDenom` — the `insertDenom` transform
  preserves `IntegralInPair` (since `D.insertDenom.P = D.P` and
  `D.insertDenom.T = insert D.s D.T`).
* `RationalLocData.SamePair.insertDenom` — the transform preserves `SamePair`.
* `RationalCoveringData.PinnedTo.insertDenom` — the cover-level transform preserves
  `PinnedTo`.
* `RationalCoveringData.insertDenom_integralInPair_each` — preservation of
  per-piece `IntegralInPair` under the cover-level transform.
-/

/-- A rational localization datum is **integral in its pair** if the
denominator `D.s` and every tray element `t ∈ D.T` lie in the ring of
definition `D.P.A₀`.

This is the local side condition needed by the corrected T089 saturation
chain (T117 blocker B1) so that the structural extraction `γ ∈ D.P.I^m`
of T114 step 3 lands in `D.P.A₀` and integer powers `D.s^k` of the
denominator stay in `D.P.A₀` (needed for common-denominator collection
inside the natural extraction route). -/
structure RationalLocData.IntegralInPair (D : RationalLocData A) : Prop where
  /-- The denominator `D.s` lies in the ring of definition `D.P.A₀`. -/
  s_in_A₀ : D.s ∈ D.P.A₀
  /-- Every tray element lies in the ring of definition `D.P.A₀`. -/
  T_in_A₀ : ∀ t ∈ D.T, t ∈ D.P.A₀

omit [DecidableEq A] in
/-- The denominator of an integral rational datum is power-bounded in `A`.
Direct combination of `IntegralInPair.s_in_A₀` and
`PairOfDefinition.mem_powerBoundedSubring`. -/
theorem RationalLocData.IntegralInPair.isPowerBounded_s
    {D : RationalLocData A} (hD : D.IntegralInPair) :
    TopologicalRing.IsPowerBounded D.s :=
  D.P.mem_powerBoundedSubring hD.s_in_A₀

omit [DecidableEq A] in
/-- Every tray element of an integral rational datum is power-bounded in `A`. -/
theorem RationalLocData.IntegralInPair.isPowerBounded_T
    {D : RationalLocData A} (hD : D.IntegralInPair)
    {t : A} (ht : t ∈ D.T) :
    TopologicalRing.IsPowerBounded t :=
  D.P.mem_powerBoundedSubring (hD.T_in_A₀ t ht)

/-- Two rational localization data **share the same pair of definition**.

This is the local side condition needed by the corrected T089 saturation
chain (T117 blocker B2) so that source `D₀.P.I^?` and target `D.P.I^m`
data live in a common `D.P.A₀ = D₀.P.A₀` and become directly comparable
as ideals of the same subring. The trivial proof when the relation holds
is `rfl`. -/
def RationalLocData.SamePair (D₀ D : RationalLocData A) : Prop := D.P = D₀.P

omit [DecidableEq A] in
/-- `SamePair` is reflexive. -/
theorem RationalLocData.SamePair.refl (D : RationalLocData A) : D.SamePair D := rfl

omit [DecidableEq A] in
/-- `SamePair` is symmetric. -/
theorem RationalLocData.SamePair.symm {D₀ D : RationalLocData A}
    (h : D₀.SamePair D) : D.SamePair D₀ := Eq.symm h

omit [DecidableEq A] in
/-- `SamePair` is transitive. -/
theorem RationalLocData.SamePair.trans {D₀ D₁ D₂ : RationalLocData A}
    (h₁ : D₀.SamePair D₁) (h₂ : D₁.SamePair D₂) : D₀.SamePair D₂ :=
  Eq.trans h₂ h₁

omit [DecidableEq A] in
/-- The global rational localization datum (`T = {1}, s = 1`) is integral
in any pair `P`. Direct: `1 ∈ P.A₀` for any subring `P.A₀`. -/
theorem globalLocData_integralInPair (P : PairOfDefinition A) :
    (globalLocData P).IntegralInPair where
  s_in_A₀ := P.A₀.one_mem
  T_in_A₀ := by
    intro t ht
    rw [show (globalLocData P).T = {(1 : A)} from rfl, Finset.mem_singleton] at ht
    exact ht ▸ P.A₀.one_mem

/-- The `insertDenom` transform preserves `IntegralInPair`: since
`D.insertDenom.s = D.s`, `D.insertDenom.T = insert D.s D.T`, and
`D.insertDenom.P = D.P`, integrality of the new tray follows from
integrality of `D.T ∪ {D.s}` in `D.P.A₀`. -/
theorem RationalLocData.IntegralInPair.insertDenom
    {D : RationalLocData A} (hD : D.IntegralInPair) :
    D.insertDenom.IntegralInPair where
  s_in_A₀ := by simpa using hD.s_in_A₀
  T_in_A₀ := by
    simp only [RationalLocData.insertDenom_T, RationalLocData.insertDenom_P,
      Finset.forall_mem_insert]
    exact ⟨hD.s_in_A₀, hD.T_in_A₀⟩

/-- The `insertDenom` transform preserves `SamePair` (in either argument). -/
theorem RationalLocData.SamePair.insertDenom
    {D₀ D : RationalLocData A} (h : D₀.SamePair D) :
    D₀.insertDenom.SamePair D.insertDenom := by
  simpa [RationalLocData.SamePair] using h

section RationalCoveringDataSection2

variable [PlusSubring A]

/-- A rational covering is **pinned to an ambient pair** `P` if both its
base and every cover piece carry that pair as their pair of definition.

This is the cover-level analogue of `SamePair`: it globally discharges
the `D.P = base.P = P` side condition for every restriction map within
the covering, so the corrected T089 chain can run uniformly. -/
structure RationalCoveringData.PinnedTo (P : PairOfDefinition A)
    (C : RationalCoveringData A) : Prop where
  /-- The base carries the ambient pair. -/
  base_pair : C.base.P = P
  /-- Every cover piece carries the ambient pair. -/
  covers_pair : ∀ D ∈ C.covers, D.P = P

omit [DecidableEq A] in
/-- If a cover is pinned to a pair, every cover piece is `SamePair` to
the base. Direct from transitivity through the ambient pair. -/
theorem RationalCoveringData.PinnedTo.samePair_base
    {P : PairOfDefinition A} {C : RationalCoveringData A} (hC : C.PinnedTo P)
    {D : RationalLocData A} (hD : D ∈ C.covers) :
    C.base.SamePair D := by
  change D.P = C.base.P
  rw [hC.covers_pair D hD, hC.base_pair]

/-- The cover-level `insertDenom` transform preserves `PinnedTo`: the
piece-level `insertDenom` keeps `P` unchanged. -/
theorem RationalCoveringData.PinnedTo.insertDenom
    {P : PairOfDefinition A} {C : RationalCoveringData A} (hC : C.PinnedTo P) :
    C.insertDenom.PinnedTo P where
  base_pair := hC.base_pair
  covers_pair := by
    classical
    intro D hD
    obtain ⟨D', hD', rfl⟩ := Finset.mem_image.mp hD
    exact hC.covers_pair D' hD'

/-- The cover-level `insertDenom` transform preserves per-piece (and
base-level) `IntegralInPair`. -/
theorem RationalCoveringData.insertDenom_integralInPair_each
    {C : RationalCoveringData A}
    (h_base : C.base.IntegralInPair)
    (h_covers : ∀ D ∈ C.covers, D.IntegralInPair) :
    C.insertDenom.base.IntegralInPair ∧
    ∀ D ∈ C.insertDenom.covers, D.IntegralInPair := by
  classical
  refine ⟨RationalLocData.IntegralInPair.insertDenom h_base, ?_⟩
  intro D hD
  obtain ⟨D', hD', rfl⟩ := Finset.mem_image.mp hD
  exact RationalLocData.IntegralInPair.insertDenom (h_covers D' hD')

end RationalCoveringDataSection2

end ValuationSpectrum

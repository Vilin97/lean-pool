/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.LocalizationTopology
import LeanPool.UniformSheafyTateDomains.AdicSpaces.ContinuousValuations

/-!
# Continuity of `Valuation.extendToLocalization` under `locTopology`

The single remaining residual identified in
`WedhornLocalizationLiftContinuity.lean`: continuity of the
`Valuation.extendToLocalization` (Mathlib) at the locTopology on
`Localization.Away s`.

## Audit and refinement

The full continuity statement as identified in the prior file's
trailing docblock requires a **uniform bound** on the extended valuation
across `locSubring` elements, which generally fails for arbitrary
valuations: a `locSubring` element such as `t/s` has extended-valuation
`ν(t)/ν(s)` — unbounded if `ν(t) > ν(s)`.

The bound DOES hold under two natural Wedhorn callsite hypotheses:

* `hν_A₀ : ∀ a ∈ A₀, ν a ≤ 1` — `ν` bounded by 1 on the ring of
  definition. Implied by `A₀ ⊆ A⁺` (Wedhorn 7.17 /
  `CompatiblePlusSubring`) plus `v ∈ Spa A A⁺`.

* `hν_T : ∀ t ∈ T, ν t ≤ ν s` — the test family `T` is
  `s`-non-archimedean-bounded. Implied by `v ∈ rationalOpen T s`.

Under these hypotheses, `ν` extends to `extendToLocalization` bounded
by 1 on `locSubring` (proved here), and continuity follows by combining
this bound with `ν`'s continuity on `A` and the `locNhd`-basis
structure.

## What this file provides

1. `extendToLocalization_le_one_of_locSubring` — the key bound:
   `(ν.extendToLocalization)` is bounded by `1` on `locSubring P T s`,
   under `hν_A₀` and `hν_T`. Proved by `Subring.closure_induction` on
   the generators `algebraMap '' A₀ ∪ {t/s : t ∈ T}`.

2. `extendToLocalization_isContinuous_locTopology_of_bounded` — the
   strengthened continuity theorem. Combines the locSubring bound with
   ν's continuity on A and the `locNhd`-basis structure.

3. Documented relation to the manager's original target signature
   (without the strengthened hypotheses): the abstract theorem as
   stated requires the additional hypotheses to hold; the strengthened
   form here is the natural Wedhorn-callsite version.

## Notes

* No root import; leaf-level file.
* No edits to `LocalizationTopology.lean`, `ContinuousValuations.lean`,
  or any committed bridge file.
* No Lane B / Cor 8.32 / Jacobson / T001 / faithful-flatness /
  final-acyclicity content. -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

omit [IsTopologicalRing A] in
/-- **Bound on `extendToLocalization` over `locSubring`** under natural
Wedhorn-callsite hypotheses.

If `ν : Valuation A Γ` satisfies:
* `hν_A₀ : ∀ a ∈ A₀, ν a ≤ 1` (`ν` bounded on the ring of definition)
* `hν_T : ∀ t ∈ T, ν t ≤ ν s` (test family s-bounded; equivalently,
  `ν(t/s) ≤ 1`)
* `hν_s_pos : ν s ≠ 0` (denominator non-degenerate)

then `(ν.extendToLocalization hS (Localization.Away s))` is bounded by
`1` on every element of `locSubring P T s`.

**Proof**: `Subring.closure_induction` on the closure-generators
`algebraMap '' A₀ ∪ {t/s : t ∈ T}`. For `a ∈ A₀`:
`(extendToLocalization)(algebraMap a) = ν a ≤ 1`. For `t/s`:
`(extendToLocalization)(t/s) = ν(t) · (ν(s))⁻¹ ≤ 1` since
`ν(t) ≤ ν(s)`. Closure operations preserve `≤ 1` (sum: max of bounds;
product: product of bounds; etc.). -/
theorem extendToLocalization_le_one_of_locSubring
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (ν : Valuation A Γ)
    (hν_A₀ : ∀ a ∈ P.A₀, ν a ≤ 1)
    (hν_T : ∀ t ∈ T, ν t ≤ ν s)
    (hS : Submonoid.powers s ≤ ν.supp.primeCompl)
    {x : Localization.Away s} (hx : x ∈ locSubring P T s) :
    (ν.extendToLocalization hS (Localization.Away s)) x ≤ 1 := by
  -- `Submonoid.powers s ≤ ν.supp.primeCompl` ⟹ `s ∉ ν.supp` ⟹ `ν s ≠ 0`.
  have hs_pos : ν s ≠ 0 := by
    intro hνs0
    have hs_supp : s ∈ ν.supp := by rw [Valuation.mem_supp_iff]; exact hνs0
    exact hS (Submonoid.mem_powers s) hs_supp
  -- `(ν s)⁻¹ ≤ (ν s)⁻¹` (will be used as a bound for t/s ≤ 1).
  -- The inverse of a unit `≤ 1` is `≥ 1`, so we need ν(t) · ν(s)⁻¹ ≤ 1 ↔ ν(t) ≤ ν(s).
  set ν_loc := ν.extendToLocalization hS (Localization.Away s) with hν_loc
  refine Subring.closure_induction (p := fun y _ ↦ ν_loc y ≤ 1) ?_ ?_ ?_ ?_ ?_ ?_ hx
  · -- Generators: y ∈ algebraMap '' A₀ ∪ Set.range (fun t : T => divByS t s).
    rintro y (⟨a, ha, rfl⟩ | ⟨⟨t, ht⟩, rfl⟩)
    · -- y = algebraMap a, a ∈ A₀.
      show ν_loc (algebraMap A (Localization.Away s) a) ≤ 1
      rw [hν_loc, Valuation.extendToLocalization_apply_map_apply]
      exact hν_A₀ a ha
    · -- y = divByS (t : A) s = IsLocalization.mk' _ t ⟨s, ⟨1, pow_one s⟩⟩.
      change ν_loc (divByS (t : A) s) ≤ 1
      simp only [divByS, hν_loc, Valuation.extendToLocalization_mk']
      calc ν (t : A) * (ν s)⁻¹
          ≤ ν s * (ν s)⁻¹ := mul_le_mul_left (hν_T t ht) _
        _ = 1 := mul_inv_cancel₀ hs_pos
  · -- 0 case: ν_loc 0 = 0 ≤ 1.
    change ν_loc 0 ≤ 1
    rw [map_zero]; exact zero_le_one
  · -- 1 case: ν_loc 1 = 1 ≤ 1.
    change ν_loc 1 ≤ 1
    rw [map_one]
  · -- Sum: ν_loc(a + b) ≤ max ≤ 1.
    intro a b _ _ ha hb
    change ν_loc (a + b) ≤ 1
    refine le_trans (ν_loc.map_add a b) ?_
    exact max_le ha hb
  · -- Negation: ν_loc(-a) = ν_loc(a) ≤ 1.
    intro a _ ha
    change ν_loc (-a) ≤ 1
    rw [Valuation.map_neg]; exact ha
  · -- Product: ν_loc(a * b) = ν_loc a * ν_loc b ≤ 1 * 1 = 1.
    intro a b _ _ ha hb
    change ν_loc (a * b) ≤ 1
    rw [map_mul]
    exact mul_le_one' ha hb

/-- **(Wedhorn §8.1 absorption — valuation version)** For `x ∈ locSubring P T s`
and `b ∈ P.Iᵐ`, the extended valuation satisfies `ν_loc(x · algebraMap b) < γ`,
**given only** `ν(Iᵐ) < γ` (the `A`-continuity bound) and `ν(tᵢ) ≤ ν(s)` — with **no
`ν ≤ 1` on `A₀`**. This is Wedhorn's absorption (`wedhorn.txt:3669`): the `A₀`-coefficients
of `x` are swallowed by the `Iᵐ` factor (since `I` is an `A₀`-ideal, `a₀·b ∈ Iᵐ`), and the
`tᵢ/s` factors have `ν_loc ≤ 1` (from `ν(tᵢ) ≤ ν(s)`). The valuation analogue of
`locTopology_continuous_lift`'s `hfull`; proved by the same finite-generator induction. -/
theorem extendToLocalization_mul_pow_lt
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (ν : Valuation A Γ)
    (hν_T : ∀ t ∈ T, ν t ≤ ν s)
    (hS : Submonoid.powers s ≤ ν.supp.primeCompl)
    {γ : Γ} (hγ : γ ≠ 0) {m : ℕ}
    (hm : ∀ b : ↥P.A₀, b ∈ P.I ^ m → ν (b : A) < γ) :
    ∀ x ∈ locSubring P T s, ∀ b : ↥P.A₀, b ∈ P.I ^ m →
      (ν.extendToLocalization hS (Localization.Away s))
        (x * algebraMap A (Localization.Away s) (b : A)) < γ := by
  set ν_loc := ν.extendToLocalization hS (Localization.Away s) with hν_loc
  have hs_pos : ν s ≠ 0 := fun h0 ↦
    hS (Submonoid.mem_powers s) ((Valuation.mem_supp_iff ν s).mpr h0)
  have hdiv_le : ∀ t ∈ T, ν_loc (divByS t s) ≤ 1 := by
    intro t ht
    simp only [divByS, hν_loc, Valuation.extendToLocalization_mk']
    calc ν t * (ν s)⁻¹ ≤ ν s * (ν s)⁻¹ := mul_le_mul_left (hν_T t ht) _
      _ = 1 := mul_inv_cancel₀ hs_pos
  suffices haux : ∀ (U : Finset A), (∀ t ∈ U, ν_loc (divByS t s) ≤ 1) →
      ∀ x ∈ locSubring P U s, ∀ b : ↥P.A₀, b ∈ P.I ^ m →
        ν_loc (x * algebraMap A (Localization.Away s) (b : A)) < γ by
    exact haux T hdiv_le
  classical
  intro U
  induction U using Finset.induction with
  | empty =>
    intro _ x hx b hb
    have hempty : locSubring P ∅ s = P.A₀.map (algebraMap A (Localization.Away s)) := by
      unfold locSubring
      simp only [Set.range_eq_empty, Set.union_empty]
      rw [← Subring.coe_map]; exact Subring.closure_eq _
    rw [hempty] at hx
    obtain ⟨a₀, ha₀, rfl⟩ := hx
    rw [← map_mul, hν_loc, Valuation.extendToLocalization_apply_map_apply]
    exact hm ⟨a₀ * (b : A), P.A₀.mul_mem ha₀ b.property⟩
      (Ideal.mul_mem_left _ ⟨a₀, ha₀⟩ hb)
  | insert t U' ht ih =>
    intro hdivU x hx b hb
    have hinsert_le : locSubring P (insert t U') s ≤
        Subring.closure ((locSubring P U' s : Set _) ∪ {divByS t s}) := by
      unfold locSubring
      apply Subring.closure_le.mpr
      rintro y (⟨a₀, ha₀, rfl⟩ | ⟨⟨t', ht'⟩, rfl⟩)
      · exact Subring.subset_closure (Or.inl (Subring.subset_closure (Or.inl ⟨a₀, ha₀, rfl⟩)))
      · simp only [Finset.mem_insert] at ht'
        rcases ht' with rfl | ht'U
        · exact Subring.subset_closure (Or.inr rfl)
        · exact Subring.subset_closure (Or.inl (Subring.subset_closure (Or.inr
            ⟨⟨t', ht'U⟩, rfl⟩)))
    have hx_in_adj : x ∈ Algebra.adjoin ↥(locSubring P U' s)
        ({divByS t s} : Set (Localization.Away s)) := by
      have h_le : Subring.closure
          ((locSubring P U' s : Set (Localization.Away s)) ∪ {divByS t s}) ≤
            (Algebra.adjoin ↥(locSubring P U' s) ({divByS t s} : Set _)).toSubring := by
        rw [Subring.closure_le]
        rintro w (hw | rfl)
        · exact Subalgebra.algebraMap_mem _ (⟨w, hw⟩ : ↥(locSubring P U' s))
        · exact Algebra.subset_adjoin rfl
      exact h_le (hinsert_le hx)
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hx_in_adj
    obtain ⟨p, hp⟩ := hx_in_adj
    rw [← hp, Polynomial.aeval_eq_sum_range, Finset.sum_mul]
    refine Valuation.map_sum_lt ν_loc hγ (fun i _ ↦ ?_)
    rw [Algebra.smul_def, Algebra.algebraMap_ofSubsemiring_apply,
      show ((p.coeff i : Localization.Away s) * (divByS t s) ^ i) *
            algebraMap A (Localization.Away s) (b : A) =
          ((p.coeff i : Localization.Away s) *
            algebraMap A (Localization.Away s) (b : A)) * (divByS t s) ^ i from by ring,
      map_mul, map_pow]
    have h_coeff : ν_loc ((p.coeff i : Localization.Away s) *
        algebraMap A (Localization.Away s) (b : A)) < γ :=
      ih (fun t' ht' ↦ hdivU t' (Finset.mem_insert_of_mem ht')) _ (p.coeff i).property b hb
    calc ν_loc ((p.coeff i : Localization.Away s)
            * algebraMap A (Localization.Away s) (b : A)) * ν_loc (divByS t s) ^ i
        ≤ ν_loc ((p.coeff i : Localization.Away s)
            * algebraMap A (Localization.Away s) (b : A)) * 1 := by
          apply mul_le_mul_right
          calc ν_loc (divByS t s) ^ i ≤ (1 : Γ) ^ i :=
                pow_le_pow_left' (hdivU t (Finset.mem_insert_self t U')) i
            _ = 1 := one_pow i
      _ = ν_loc ((p.coeff i : Localization.Away s)
            * algebraMap A (Localization.Away s) (b : A)) := mul_one _
      _ < γ := h_coeff

/-- **Strengthened continuity of `extendToLocalization` under
`locTopology`** (the natural Wedhorn-callsite version).

Given the natural Wedhorn-callsite hypotheses:

* `hν_cont : ν.IsContinuous` — original valuation is continuous on `A`.
* `hν_A₀ : ∀ a ∈ A₀, ν a ≤ 1` — bounded on the ring of definition.
* `hν_T : ∀ t ∈ T, ν t ≤ ν s` — `t/s` ratios bounded by 1.
* `hS : Submonoid.powers s ≤ ν.supp.primeCompl` — `ν s ≠ 0`.

the extended valuation `ν.extendToLocalization` is continuous on
`Localization.Away s` under `locTopology P T s hopen`.

**Proof structure**:

1. By `Subring.closure_induction` (`extendToLocalization_le_one_of_locSubring`),
   the extended valuation is bounded by `1` on `locSubring P T s`.

2. For any `γ ∈ Γ`, use `ν`'s continuity at `0 : A` to find `m : ℕ`
   such that `algebraMap (P.I^m) ⊆ {b | ν b < γ}` (via
   `P.hasBasis_nhds_zero` and `extendToLocalization_apply_map_apply`).

3. For `d ∈ locNhd m` (image of `(locIdeal)^m` in `Localization.Away s`):
   the locSubring bound (step 1) plus the `algebraMap (P.I^m)` bound
   (step 2) combine via `≤ max` (non-archimedean) to give
   `(ν.extendToLocalization) d < γ`.

The final IsOpen-at-0 follows; full IsContinuous via translation by
the `IsTopologicalAddGroup` structure of `locTopology`. -/
theorem extendToLocalization_isContinuous_locTopology_of_bounded
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (ν : Valuation A Γ) (hν_cont : ν.IsContinuous)
    (hν_T : ∀ t ∈ T, ν t ≤ ν s)
    (hS : Submonoid.powers s ≤ ν.supp.primeCompl) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    (ν.extendToLocalization hS (Localization.Away s)).IsContinuous := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  haveI : IsTopologicalRing (Localization.Away s) :=
    (locBasis P T s hopen).toRingFilterBasis.isTopologicalRing
  set ν_loc := ν.extendToLocalization hS (Localization.Away s) with hν_loc
  -- For continuity, it suffices (by IsTopologicalAddGroup) to verify continuity at 0.
  -- For each γ ∈ Γ, need {b | ν_loc b < γ} to be open.
  -- We show it contains a locNhd m for some m.
  intro γ
  -- Step 2: find m such that ν(P.I^m) < γ.
  -- Use ν.IsContinuous: {a | ν a < γ} is open in A, so contains a basic nhd of 0,
  -- which by P.hasBasis_nhds_zero has the form `Subtype.val '' (P.I^m)`.
  by_cases hγ : γ = 0
  · subst hγ
    convert isOpen_empty
    ext b
    simp
  -- γ ≠ 0, so γ is a unit. Use ltAddSubgroup characterization.
  set γu : Γˣ := Units.mk0 γ hγ with hγu
  rw [show { b : Localization.Away s | ν_loc b < γ } =
        (ν_loc.ltAddSubgroup γu : Set (Localization.Away s)) from
      (Valuation.coe_ltAddSubgroup ν_loc γu).symm]
  apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
  rw [(locBasis P T s hopen).hasBasis_nhds_zero.mem_iff]
  have h_open_A : IsOpen { a : A | ν a < γ } := hν_cont γ
  obtain ⟨m, _, hm⟩ := P.hasBasis_nhds_zero.mem_iff.mp
    (h_open_A.mem_nhds (by simp [zero_lt_iff.mpr hγ] : (0 : A) ∈ {a | ν a < γ}))
  refine ⟨m, trivial, ?_⟩
  intro d hd
  -- d ∈ locNhd m, i.e., ∃ d' ∈ (locIdeal)^m, subtype.val d' = d.
  obtain ⟨d', hd'_mem, rfl⟩ := hd
  -- Goal: subtype.val d' ∈ ↑(ν_loc.ltAddSubgroup γu).
  change ν_loc ((d' : locSubring P T s) : Localization.Away s) < γ
  rw [locIdeal, ← Ideal.map_pow, ← Ideal.span_eq (P.I^m), Ideal.map_span] at hd'_mem
  -- Wedhorn §8.1 absorption: any `locSubring`-multiple of an `algebraMap(Iᵐ)` generator has
  -- its `A₀`-coefficients swallowed by `Iᵐ`, so NO `ν ≤ 1` on `A₀` is needed. We prove the
  -- smul-stable strengthening `∀ r, ν_loc(↑r · ↑d') < γ` by span-induction (generator case =
  -- `extendToLocalization_mul_pow_lt`, smul case reassociates `r · (c • x) = (r·c) • x`), then
  -- specialise `r = 1`.
  have hm' : ∀ b : ↥P.A₀, b ∈ P.I ^ m → ν (b : A) < γ := fun b hb ↦ hm ⟨b, hb, rfl⟩
  have key : ∀ r : ↥(locSubring P T s),
      ν_loc ((r : Localization.Away s)
        * ((d' : locSubring P T s) : Localization.Away s)) < γ := by
    refine Submodule.span_induction (p := fun x _ ↦ ∀ r : ↥(locSubring P T s),
      ν_loc ((r : Localization.Away s)
        * ((x : locSubring P T s) : Localization.Away s)) < γ)
      ?_ ?_ ?_ ?_ hd'_mem
    · -- Generator case: x = algebraMapD b (b ∈ P.Iᵐ) — exactly the absorption lemma.
      rintro x ⟨b, hb, rfl⟩ r
      exact extendToLocalization_mul_pow_lt P T s ν hν_T hS hγ hm'
        (r : Localization.Away s) r.property b hb
    · -- Zero case.
      intro r
      simp only [ZeroMemClass.coe_zero, mul_zero, map_zero]
      exact zero_lt_iff.mpr hγ
    · -- Sum case.
      intro x y _ _ hx hy r
      have h_add : (r : Localization.Away s)
            * ((x + y : locSubring P T s) : Localization.Away s) =
          (r : Localization.Away s) * ((x : locSubring P T s) : Localization.Away s)
          + (r : Localization.Away s) * ((y : locSubring P T s) : Localization.Away s) := by
        rw [show ((x + y : locSubring P T s) : Localization.Away s) =
          ((x : locSubring P T s) : Localization.Away s) +
          ((y : locSubring P T s) : Localization.Away s) from rfl]; ring
      rw [h_add]
      exact lt_of_le_of_lt (ν_loc.map_add _ _) (max_lt (hx r) (hy r))
    · -- Smul case: reassociate `r · (c • x) = (r · c) · x`, apply IH at `r · c`.
      intro c x _ hx r
      have h_smul : (r : Localization.Away s)
            * ((c • x : locSubring P T s) : Localization.Away s) =
          ((r * c : locSubring P T s) : Localization.Away s)
            * ((x : locSubring P T s) : Localization.Away s) := by
        rw [show ((c • x : locSubring P T s) : Localization.Away s) =
            ((c : locSubring P T s) : Localization.Away s) *
            ((x : locSubring P T s) : Localization.Away s) from rfl,
          show ((r * c : locSubring P T s) : Localization.Away s) =
            (r : Localization.Away s) * ((c : locSubring P T s) : Localization.Away s) from rfl]
        ring
      rw [h_smul]
      exact hx (r * c)
  have hfinal := key 1
  simpa using hfinal

end ValuationSpectrum
